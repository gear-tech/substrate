// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! This module defines `HostState` and `HostContext` structs which provide logic and state
//! required for execution of host.

use wasmtime::Caller;

use sp_wasm_interface::{Pointer, WordSize};
pub use sp_wasm_interface::HostState;

use crate::{runtime::StoreData, util};

/// A `HostContext` implements `FunctionContext` for making host calls from a Wasmtime
/// runtime. The `HostContext` exists only for the lifetime of the call and borrows state from
/// a longer-living `HostState`.
pub(crate) struct HostContext<'a> {
	pub(crate) caller: Caller<'a, StoreData>,
}

impl<'a> HostContext<'a> {
	fn host_state_mut(&mut self) -> &mut HostState {
		self.caller
			.data_mut()
			.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
	}
}

impl<'a> sp_wasm_interface::FunctionContext for HostContext<'a> {
	fn read_memory_into(
		&self,
		address: Pointer<u8>,
		dest: &mut [u8],
	) -> sp_wasm_interface::Result<()> {
		util::read_memory_into(&self.caller, address, dest).map_err(|e| e.to_string())
	}

	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> sp_wasm_interface::Result<()> {
		util::write_memory_from(&mut self.caller, address, data).map_err(|e| e.to_string())
	}

	fn allocate_memory(&mut self, size: WordSize) -> sp_wasm_interface::Result<Pointer<u8>> {
		let memory = self.caller.data().memory();
		let (memory, data) = memory.data_and_store_mut(&mut self.caller);
		data.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
			.allocator
			.allocate(memory, size)
			.map_err(|e| e.to_string())
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> sp_wasm_interface::Result<()> {
		let memory = self.caller.data().memory();
		let (memory, data) = memory.data_and_store_mut(&mut self.caller);
		data.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
			.allocator
			.deallocate(memory, ptr)
			.map_err(|e| e.to_string())
	}

	fn register_panic_error_message(&mut self, message: &str) {
		self.host_state_mut().panic_message = Some(message.to_owned());
	}
}
