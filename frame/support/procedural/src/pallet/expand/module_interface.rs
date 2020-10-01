// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::pallet::Def;
use syn::spanned::Spanned;

/// * implement the individual traits using the ModuleInterface trait
pub fn expand_module_interface(def: &mut Def) -> proc_macro2::TokenStream {
	let frame_support = &def.frame_support;
	let type_impl_gen = &def.type_impl_generics();
	let type_use_gen = &def.type_use_generics();
	let module_ident = &def.module.module;
	let where_clause = &def.module_interface.where_clause;
	let frame_system = &def.frame_system;

	let module_interface_item_span = def.item.content.as_mut()
		.expect("Checked by def parser").1[def.module_interface.index].span();

	quote::quote_spanned!(module_interface_item_span =>
		impl<#type_impl_gen>
			#frame_support::traits::OnFinalize<<T as #frame_system::Trait>::BlockNumber>
			for #module_ident<#type_use_gen> #where_clause
		{
			fn on_finalize(n: <T as #frame_system::Trait>::BlockNumber) {
				<
					Self as #frame_support::traits::ModuleInterface<
						<T as #frame_system::Trait>::BlockNumber
					>
				>::on_finalize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnInitialize<<T as #frame_system::Trait>::BlockNumber>
			for #module_ident<#type_use_gen> #where_clause
		{
			fn on_initialize(
				n: <T as #frame_system::Trait>::BlockNumber
			) -> #frame_support::weights::Weight {
				<
					Self as #frame_support::traits::ModuleInterface<
						<T as #frame_system::Trait>::BlockNumber
					>
				>::on_initialize(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OnRuntimeUpgrade
			for #module_ident<#type_use_gen> #where_clause
		{
			fn on_runtime_upgrade() -> #frame_support::weights::Weight {
				<
					Self as #frame_support::traits::ModuleInterface<
						<T as #frame_system::Trait>::BlockNumber
					>
				>::on_runtime_upgrade()
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::OffchainWorker<<T as #frame_system::Trait>::BlockNumber>
			for #module_ident<#type_use_gen> #where_clause
		{
			fn offchain_worker(n: <T as #frame_system::Trait>::BlockNumber) {
				<
					Self as #frame_support::traits::ModuleInterface<
						<T as #frame_system::Trait>::BlockNumber
					>
				>::offchain_worker(n)
			}
		}

		impl<#type_impl_gen>
			#frame_support::traits::IntegrityTest
			for #module_ident<#type_use_gen> #where_clause
		{
			fn integrity_test() {
				<
					Self as #frame_support::traits::ModuleInterface<
						<T as #frame_system::Trait>::BlockNumber
					>
				>::integrity_test()
			}
		}
	)
}
