use crate::{
	build_executor, ensure_matching_spec_name, extract_code, full_extensions, local_spec_name,
	parse, state_machine_call, SharedParams, LOG_TARGET,
};
use jsonrpsee_ws_client::{
	types::{traits::SubscriptionClient, v2::params::JsonRpcParams, Subscription},
	WsClientBuilder,
};
use parity_scale_codec::Decode;
use remote_externalities::{rpc_api, Builder, Mode, OnlineConfig};
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use sp_core::H256;
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{fmt::Debug, str::FromStr};

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct FollowChainCmd {
	/// The url to connect to
	#[structopt(
			short,
			long,
			parse(try_from_str = parse::url),
		)]
	uri: String,
}

pub async fn follow_chain<Block, ExecDispatch>(
	shared: SharedParams,
	command: FollowChainCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT<Hash = H256> + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: serde::de::DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let mut maybe_state_ext = None;

	let sub = "chain_subscribeFinalizedHeads";
	let unsub = "chain_unsubscribeFinalizedHeads";

	let client = WsClientBuilder::default()
		.connection_timeout(std::time::Duration::new(20, 0))
		.max_request_body_size(u32::MAX)
		.build(&command.uri)
		.await
		.unwrap();

	log::info!(target: LOG_TARGET, "subscribing to {:?} / {:?}", sub, unsub);
	let mut subscription: Subscription<Block::Header> =
		client.subscribe(&sub, JsonRpcParams::NoParams, &unsub).await.unwrap();

	let (code_key, code) = extract_code(&config.chain_spec)?;
	let executor = build_executor::<ExecDispatch>(&shared, &config);
	let execution = shared.execution;

	while let Some(header) = subscription.next().await.unwrap() {
		let hash = header.hash();
		let number = header.number();
		let parent = header.parent_hash();

		let block = rpc_api::get_block::<Block, _>(&command.uri, hash).await.unwrap();

		log::debug!(
			target: LOG_TARGET,
			"new block event: {:?} => {:?}, extrinsics: {}",
			hash,
			number,
			block.extrinsics().len()
		);

		// create an ext at the state of this block, whatever is the first subscription event.
		if maybe_state_ext.is_none() {
			let builder = Builder::<Block>::new().mode(Mode::Online(OnlineConfig {
				transport: command.uri.clone().into(),
				at: Some(header.parent_hash().clone()),
				..Default::default()
			}));

			let new_ext =
				builder.inject_key_value(&[(code_key.clone(), code.clone())]).build().await?;
			log::info!(
				target: LOG_TARGET,
				"initialized state externalities at {:?}, storage root {:?}",
				number,
				new_ext.as_backend().root()
			);

			let expected_spec_name = local_spec_name::<Block, ExecDispatch>(&new_ext, &executor);
			ensure_matching_spec_name::<Block>(command.uri.clone(), expected_spec_name).await;

			maybe_state_ext = Some(new_ext);
		}

		let state_ext =
			maybe_state_ext.as_mut().expect("state_ext either existed or was just created");

		let (mut changes, encoded_result) = state_machine_call::<Block, ExecDispatch>(
			&state_ext,
			&executor,
			execution,
			"TryRuntime_execute_block_no_state_root_check",
			block.encode().as_ref(),
			full_extensions(),
		)?;
		// .set_parent_hash(*parent)

		let consumed_weight = <u64 as Decode>::decode(&mut &*encoded_result)
			.map_err(|e| format!("failed to decode output: {:?}", e))?;

		let storage_changes = changes
			.drain_storage_changes::<_, _, NumberFor<Block>>(
				&state_ext.backend,
				None,
				Default::default(),
				&mut Default::default(),
			)
			.unwrap();
		state_ext.backend.apply_transaction(
			storage_changes.transaction_storage_root,
			storage_changes.transaction,
		);

		log::info!(
			target: LOG_TARGET,
			"executed block {}, consumed weight {}, new storage root {:?}",
			number,
			consumed_weight,
			state_ext.as_backend().root(),
		);
	}

	log::error!(target: LOG_TARGET, "ws subscription must have terminated.");
	Ok(())
}
