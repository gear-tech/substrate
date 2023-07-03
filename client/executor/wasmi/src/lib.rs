// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! This crate provides an implementation of `WasmModule` that is baked by wasmi.

use std::{cell::RefCell, rc::Rc, str, sync::Arc};

use log::{error, trace};
use wasmi::{
	memory_units::Pages,
	FuncInstance, ImportsBuilder, MemoryRef, Module, ModuleInstance, ModuleRef,
	RuntimeValue::{self, I32, I64},
	TableRef,
};

use sc_allocator::AllocationStats;
use sc_executor_common::{
	error::{Error, MessageWithBacktrace, WasmError},
	runtime_blob::{DataSegmentsSnapshot, RuntimeBlob},
	sandbox::{self, SandboxInstance},
	util::MemoryTransfer,
	wasm_runtime::{HeapAllocStrategy, InvokeMethod, WasmInstance, WasmModule},
};
use sp_runtime_interface::unpack_ptr_and_len;
use sp_sandbox::env as sandbox_env;
use sp_wasm_interface::{
	Function, FunctionContext, MemoryId, Pointer, Result as WResult, Sandbox, WordSize, HostPointer,
};
use codec::{Decode, Encode};

/// Wrapper around [`MemorRef`] that implements [`sc_allocator::Memory`].
struct MemoryWrapper<'a>(&'a MemoryRef);

impl sc_allocator::Memory for MemoryWrapper<'_> {
	fn with_access_mut<R>(&mut self, run: impl FnOnce(&mut [u8]) -> R) -> R {
		self.0.with_direct_access_mut(run)
	}

	fn with_access<R>(&self, run: impl FnOnce(&[u8]) -> R) -> R {
		self.0.with_direct_access(run)
	}

	fn pages(&self) -> u32 {
		self.0.current_size().0 as _
	}

	fn max_pages(&self) -> Option<u32> {
		self.0.maximum().map(|p| p.0 as _)
	}

	fn grow(&mut self, additional: u32) -> Result<(), ()> {
		self.0
			.grow(Pages(additional as _))
			.map_err(|e| {
				log::error!(
					target: "wasm-executor",
					"Failed to grow memory by {} pages: {}",
					additional,
					e,
				)
			})
			.map(drop)
	}
}

struct FunctionExecutor {
	sandbox_store: Rc<RefCell<sandbox::Store<wasmi::FuncRef>>>,
	heap: RefCell<sc_allocator::FreeingBumpHeapAllocator>,
	memory: MemoryRef,
	table: Option<TableRef>,
	host_functions: Arc<Vec<&'static dyn Function>>,
	allow_missing_func_imports: bool,
	missing_functions: Arc<Vec<String>>,
	panic_message: Option<String>,
}

impl FunctionExecutor {
	fn new(
		m: MemoryRef,
		heap_base: u32,
		t: Option<TableRef>,
		host_functions: Arc<Vec<&'static dyn Function>>,
		allow_missing_func_imports: bool,
		missing_functions: Arc<Vec<String>>,
	) -> Result<Self, Error> {
		Ok(FunctionExecutor {
			sandbox_store: Rc::new(RefCell::new(sandbox::Store::new(
				sandbox::SandboxBackend::Wasmi,
			))),
			heap: RefCell::new(sc_allocator::FreeingBumpHeapAllocator::new(heap_base)),
			memory: m,
			table: t,
			host_functions,
			allow_missing_func_imports,
			missing_functions,
			panic_message: None,
		})
	}
}

struct SandboxContext<'a> {
	executor: &'a mut FunctionExecutor,
	dispatch_thunk: wasmi::FuncRef,
	/// Custom data to propagate it in supervisor export functions
	state: u32,
}

impl<'a> sandbox::SandboxContext for SandboxContext<'a> {
	fn invoke(
		&mut self,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		func_idx: sandbox::SupervisorFuncIndex,
	) -> Result<i64, Error> {
		let result = wasmi::FuncInstance::invoke(
			&self.dispatch_thunk,
			&[
				RuntimeValue::I32(u32::from(invoke_args_ptr) as i32),
				RuntimeValue::I32(invoke_args_len as i32),
				RuntimeValue::I32(self.state as i32),
				RuntimeValue::I32(usize::from(func_idx) as i32),
			],
			self.executor,
		);

		match result {
			Ok(Some(RuntimeValue::I64(val))) => Ok(val),
			Ok(_) => Err("Supervisor function returned unexpected result!".into()),
			Err(err) => Err(Error::Sandbox(err.to_string())),
		}
	}

	fn supervisor_context(&mut self) -> &mut dyn FunctionContext {
		self.executor
	}
}

impl FunctionContext for FunctionExecutor {
	fn read_memory_into(&self, address: Pointer<u8>, dest: &mut [u8]) -> WResult<()> {
		self.memory.get_into(address.into(), dest).map_err(|e| e.to_string())
	}

	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> WResult<()> {
		self.memory.set(address.into(), data).map_err(|e| e.to_string())
	}

	fn allocate_memory(&mut self, size: WordSize) -> WResult<Pointer<u8>> {
		self.heap
			.borrow_mut()
			.allocate(&mut MemoryWrapper(&self.memory), size)
			.map_err(|e| e.to_string())
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> WResult<()> {
		self.heap
			.borrow_mut()
			.deallocate(&mut MemoryWrapper(&self.memory), ptr)
			.map_err(|e| e.to_string())
	}

	fn sandbox(&mut self) -> &mut dyn Sandbox {
		self
	}

	fn register_panic_error_message(&mut self, message: &str) {
		self.panic_message = Some(message.to_owned());
	}
}

impl Sandbox for FunctionExecutor {
	fn memory_get(
		&mut self,
		memory_id: MemoryId,
		offset: WordSize,
		buf_ptr: Pointer<u8>,
		buf_len: WordSize,
	) -> WResult<u32> {
		let sandboxed_memory =
			self.sandbox_store.borrow().memory(memory_id).map_err(|e| e.to_string())?;

		let len = buf_len as usize;

		let buffer = match sandboxed_memory.read(Pointer::new(offset as u32), len) {
			Err(_) => return Ok(sandbox_env::ERR_OUT_OF_BOUNDS),
			Ok(buffer) => buffer,
		};

		if self.memory.set(buf_ptr.into(), &buffer).is_err() {
			return Ok(sandbox_env::ERR_OUT_OF_BOUNDS)
		}

		Ok(sandbox_env::ERR_OK)
	}

	fn memory_set(
		&mut self,
		memory_id: MemoryId,
		offset: WordSize,
		val_ptr: Pointer<u8>,
		val_len: WordSize,
	) -> WResult<u32> {
		let sandboxed_memory =
			self.sandbox_store.borrow().memory(memory_id).map_err(|e| e.to_string())?;

		let len = val_len as usize;

		#[allow(deprecated)]
		let buffer = match self.memory.get(val_ptr.into(), len) {
			Err(_) => return Ok(sandbox_env::ERR_OUT_OF_BOUNDS),
			Ok(buffer) => buffer,
		};

		if sandboxed_memory.write_from(Pointer::new(offset as u32), &buffer).is_err() {
			return Ok(sandbox_env::ERR_OUT_OF_BOUNDS)
		}

		Ok(sandbox_env::ERR_OK)
	}

	fn memory_teardown(&mut self, memory_id: MemoryId) -> WResult<()> {
		self.sandbox_store
			.borrow_mut()
			.memory_teardown(memory_id)
			.map_err(|e| e.to_string())
	}

	fn memory_new(&mut self, initial: u32, maximum: u32) -> WResult<MemoryId> {
		self.sandbox_store
			.borrow_mut()
			.new_memory(initial, maximum)
			.map_err(|e| e.to_string())
	}

	fn invoke(
		&mut self,
		instance_id: u32,
		export_name: &str,
		mut args: &[u8],
		return_val: Pointer<u8>,
		return_val_len: WordSize,
		state: u32,
	) -> WResult<u32> {
		trace!(target: "sp-sandbox", "invoke, instance_idx={}", instance_id);

		// Deserialize arguments and convert them into wasmi types.
		let args = Vec::<sp_wasm_interface::Value>::decode(&mut args)
			.map_err(|_| "Can't decode serialized arguments for the invocation")?
			.into_iter()
			.collect::<Vec<_>>();

		let instance =
			self.sandbox_store.borrow().instance(instance_id).map_err(|e| e.to_string())?;

		let dispatch_thunk = self
			.sandbox_store
			.borrow()
			.dispatch_thunk(instance_id)
			.map_err(|e| e.to_string())?;

		match instance.invoke(
			export_name,
			&args,
			&mut SandboxContext { dispatch_thunk, executor: self, state },
		) {
			Ok(None) => Ok(sandbox_env::ERR_OK),
			Ok(Some(val)) => {
				// Serialize return value and write it back into the memory.
				sp_wasm_interface::ReturnValue::Value(val).using_encoded(|val| {
					if val.len() > return_val_len as usize {
						return Err("Return value buffer is too small".into())
					}
					self.write_memory(return_val, val).map_err(|_| "Return value buffer is OOB")?;
					Ok(sandbox_env::ERR_OK)
				})
			},
			Err(_) => Ok(sandbox_env::ERR_EXECUTION),
		}
	}

	fn instance_teardown(&mut self, instance_id: u32) -> WResult<()> {
		self.sandbox_store
			.borrow_mut()
			.instance_teardown(instance_id)
			.map_err(|e| e.to_string())
	}

	fn instance_new(
		&mut self,
		dispatch_thunk_id: u32,
		wasm: &[u8],
		raw_env_def: &[u8],
		state: u32,
	) -> WResult<u32> {
		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = self
				.table
				.as_ref()
				.ok_or("Runtime doesn't have a table; sandbox is unavailable")?;
			table
				.get(dispatch_thunk_id)
				.map_err(|_| "dispatch_thunk_idx is out of the table bounds")?
				.ok_or("dispatch_thunk_idx points on an empty table entry")?
		};

		let guest_env =
			match sandbox::GuestEnvironment::decode(&*self.sandbox_store.borrow(), raw_env_def) {
				Ok(guest_env) => guest_env,
				Err(_) => return Ok(sandbox_env::ERR_MODULE as u32),
			};

		let store = self.sandbox_store.clone();
		let result = store.borrow_mut().instantiate(
			wasm,
			guest_env,
			&mut SandboxContext { executor: self, dispatch_thunk: dispatch_thunk.clone(), state },
		);

		let instance_idx_or_err_code =
			match result.map(|i| i.register(&mut store.borrow_mut(), dispatch_thunk)) {
				Ok(instance_idx) => instance_idx,
				Err(sandbox::InstantiationError::StartTrapped) => sandbox_env::ERR_EXECUTION,
				Err(_) => sandbox_env::ERR_MODULE,
			};

		Ok(instance_idx_or_err_code)
	}

	fn get_global_val(
		&self,
		instance_idx: u32,
		name: &str,
	) -> WResult<Option<sp_wasm_interface::Value>> {
		self.sandbox_store
			.borrow()
			.instance(instance_idx)
			.map(|i| i.get_global_val(name))
			.map_err(|e| e.to_string())
	}

	fn get_global_i32(&self, instance_idx: u32, name: &str) -> WResult<Option<i32>> {
		self.sandbox_store
			.borrow()
			.instance(instance_idx)
			.map(|i| i.get_global_i32(name))
			.map_err(|e| e.to_string())
	}

	fn get_global_i64(&self, instance_idx: u32, name: &str) -> WResult<Option<i64>> {
		self.sandbox_store
			.borrow()
			.instance(instance_idx)
			.map(|i| i.get_global_i64(name))
			.map_err(|e| e.to_string())
	}

	fn set_global_i64(&self, instance_idx: u32, name: &str, value: i64) -> WResult<u32> {
		trace!(target: "sp-sandbox", "set_global_i64, instance_idx={}", instance_idx);

		let instance =
			self.sandbox_store.borrow().instance(instance_idx).map_err(|e| e.to_string())?;

		let result = instance.set_global_i64(name, value);

		trace!(target: "sp-sandbox", "set_global_i64, name={name}, value={value:?}, result={result:?}");
		match result {
			Ok(None) => Ok(sandbox_env::ERROR_GLOBALS_NOT_FOUND),
			Ok(Some(_)) => Ok(sandbox_env::ERROR_GLOBALS_OK),
			Err(_) => Ok(sandbox_env::ERROR_GLOBALS_OTHER),
		}
	}

	fn memory_grow(&mut self, memory_id: MemoryId, pages: u32) -> WResult<u32> {
		let mut m = self
			.sandbox_store
			.borrow_mut()
			.memory(memory_id)
			.map_err(|e| format!("Cannot get wasmi memory: {}", e))?;
		m.memory_grow(pages).map_err(|e| format!("{}", e))
	}

	fn memory_size(&mut self, memory_id: MemoryId) -> WResult<u32> {
		let mut m = self
			.sandbox_store
			.borrow_mut()
			.memory(memory_id)
			.map_err(|e| format!("Cannot get wasmi memory: {}", e))?;
		Ok(m.memory_size())
	}

	fn get_buff(&mut self, memory_id: MemoryId) -> WResult<HostPointer> {
		let mut m = self
			.sandbox_store
			.borrow_mut()
			.memory(memory_id)
			.map_err(|e| format!("Cannot get wasmi memory: {}", e))?;
		Ok(m.get_buff() as HostPointer)
	}

	fn get_instance_ptr(&mut self, instance_id: u32) -> WResult<HostPointer> {
		let instance = self.sandbox_store
			.borrow()
			.instance(instance_id)
			.map_err(|e| e.to_string())?;

		Ok(instance.as_ref().get_ref() as *const SandboxInstance as HostPointer)
	}
}

/// Will be used on initialization of a module to resolve function and memory imports.
struct Resolver<'a> {
	/// All the hot functions that we export for the WASM blob.
	host_functions: &'a [&'static dyn Function],
	/// Should we allow missing function imports?
	///
	/// If `true`, we return a stub that will return an error when being called.
	allow_missing_func_imports: bool,
	/// All the names of functions for that we did not provide a host function.
	missing_functions: RefCell<Vec<String>>,
}

impl<'a> Resolver<'a> {
	fn new(
		host_functions: &'a [&'static dyn Function],
		allow_missing_func_imports: bool,
	) -> Resolver<'a> {
		Resolver {
			host_functions,
			allow_missing_func_imports,
			missing_functions: RefCell::new(Vec::new()),
		}
	}
}

impl<'a> wasmi::ModuleImportResolver for Resolver<'a> {
	fn resolve_func(
		&self,
		name: &str,
		signature: &wasmi::Signature,
	) -> std::result::Result<wasmi::FuncRef, wasmi::Error> {
		let signature = sp_wasm_interface::Signature::from(signature);
		for (function_index, function) in self.host_functions.iter().enumerate() {
			if name == function.name() {
				if signature == function.signature() {
					return Ok(wasmi::FuncInstance::alloc_host(signature.into(), function_index))
				} else {
					return Err(wasmi::Error::Instantiation(format!(
						"Invalid signature for function `{}` expected `{:?}`, got `{:?}`",
						function.name(),
						signature,
						function.signature(),
					)))
				}
			}
		}

		if self.allow_missing_func_imports {
			trace!(
				target: "wasm-executor",
				"Could not find function `{}`, a stub will be provided instead.",
				name,
			);
			let id = self.missing_functions.borrow().len() + self.host_functions.len();
			self.missing_functions.borrow_mut().push(name.to_string());

			Ok(wasmi::FuncInstance::alloc_host(signature.into(), id))
		} else {
			Err(wasmi::Error::Instantiation(format!("Export {} not found", name)))
		}
	}

	fn resolve_memory(
		&self,
		_: &str,
		_: &wasmi::MemoryDescriptor,
	) -> Result<MemoryRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(
			"Internal error, wasmi expects that the wasm blob exports memory.".into(),
		))
	}
}

impl wasmi::Externals for FunctionExecutor {
	fn invoke_index(
		&mut self,
		index: usize,
		args: wasmi::RuntimeArgs,
	) -> Result<Option<wasmi::RuntimeValue>, wasmi::Trap> {
		let mut args = args.as_ref().iter().copied().map(Into::into);

		if let Some(function) = self.host_functions.clone().get(index) {
			function
				.execute(self, &mut args)
				.map_err(|msg| Error::FunctionExecution(function.name().to_string(), msg))
				.map_err(wasmi::Trap::from)
				.map(|v| v.map(Into::into))
		} else if self.allow_missing_func_imports &&
			index >= self.host_functions.len() &&
			index < self.host_functions.len() + self.missing_functions.len()
		{
			Err(Error::from(format!(
				"Function `{}` is only a stub. Calling a stub is not allowed.",
				self.missing_functions[index - self.host_functions.len()],
			))
			.into())
		} else {
			Err(Error::from(format!("Could not find host function with index: {}", index)).into())
		}
	}
}

fn get_mem_instance(module: &ModuleRef) -> Result<MemoryRef, Error> {
	Ok(module
		.export_by_name("memory")
		.ok_or(Error::InvalidMemoryReference)?
		.as_memory()
		.ok_or(Error::InvalidMemoryReference)?
		.clone())
}

/// Find the global named `__heap_base` in the given wasm module instance and
/// tries to get its value.
fn get_heap_base(module: &ModuleRef) -> Result<u32, Error> {
	let heap_base_val = module
		.export_by_name("__heap_base")
		.ok_or(Error::HeapBaseNotFoundOrInvalid)?
		.as_global()
		.ok_or(Error::HeapBaseNotFoundOrInvalid)?
		.get();

	match heap_base_val {
		wasmi::RuntimeValue::I32(v) => Ok(v as u32),
		_ => Err(Error::HeapBaseNotFoundOrInvalid),
	}
}

/// Call a given method in the given wasm-module runtime.
fn call_in_wasm_module(
	module_instance: &ModuleRef,
	memory: &MemoryRef,
	method: InvokeMethod,
	data: &[u8],
	host_functions: Arc<Vec<&'static dyn Function>>,
	allow_missing_func_imports: bool,
	missing_functions: Arc<Vec<String>>,
	allocation_stats: &mut Option<AllocationStats>,
) -> Result<Vec<u8>, Error> {
	// Initialize FunctionExecutor.
	let table: Option<TableRef> = module_instance
		.export_by_name("__indirect_function_table")
		.and_then(|e| e.as_table().cloned());
	let heap_base = get_heap_base(module_instance)?;

	let mut function_executor = FunctionExecutor::new(
		memory.clone(),
		heap_base,
		table.clone(),
		host_functions,
		allow_missing_func_imports,
		missing_functions,
	)?;

	// Write the call data
	let offset = function_executor.allocate_memory(data.len() as u32)?;
	function_executor.write_memory(offset, data)?;

	fn convert_trap(executor: &mut FunctionExecutor, trap: wasmi::Trap) -> Error {
		if let Some(message) = executor.panic_message.take() {
			Error::AbortedDueToPanic(MessageWithBacktrace { message, backtrace: None })
		} else {
			Error::AbortedDueToTrap(MessageWithBacktrace {
				message: trap.to_string(),
				backtrace: None,
			})
		}
	}

	let result = match method {
		InvokeMethod::Export(method) => module_instance
			.invoke_export(
				method,
				&[I32(u32::from(offset) as i32), I32(data.len() as i32)],
				&mut function_executor,
			)
			.map_err(|error| {
				if let wasmi::Error::Trap(trap) = error {
					convert_trap(&mut function_executor, trap)
				} else {
					error.into()
				}
			}),
		InvokeMethod::Table(func_ref) => {
			let func = table
				.ok_or(Error::NoTable)?
				.get(func_ref)?
				.ok_or(Error::NoTableEntryWithIndex(func_ref))?;
			FuncInstance::invoke(
				&func,
				&[I32(u32::from(offset) as i32), I32(data.len() as i32)],
				&mut function_executor,
			)
			.map_err(|trap| convert_trap(&mut function_executor, trap))
		},
		InvokeMethod::TableWithWrapper { dispatcher_ref, func } => {
			let dispatcher = table
				.ok_or(Error::NoTable)?
				.get(dispatcher_ref)?
				.ok_or(Error::NoTableEntryWithIndex(dispatcher_ref))?;

			FuncInstance::invoke(
				&dispatcher,
				&[I32(func as _), I32(u32::from(offset) as i32), I32(data.len() as i32)],
				&mut function_executor,
			)
			.map_err(|trap| convert_trap(&mut function_executor, trap))
		},
	};

	*allocation_stats = Some(function_executor.heap.borrow().stats());

	match result {
		Ok(Some(I64(r))) => {
			let (ptr, length) = unpack_ptr_and_len(r as u64);
			#[allow(deprecated)]
			memory.get(ptr, length as usize).map_err(|_| Error::Runtime)
		},
		Err(e) => {
			trace!(
				target: "wasm-executor",
				"Failed to execute code with {} pages",
				memory.current_size().0,
			);
			Err(e)
		},
		_ => Err(Error::InvalidReturn),
	}
}

/// Prepare module instance
fn instantiate_module(
	module: &Module,
	host_functions: &[&'static dyn Function],
	allow_missing_func_imports: bool,
) -> Result<(ModuleRef, Vec<String>, MemoryRef), Error> {
	let resolver = Resolver::new(host_functions, allow_missing_func_imports);
	// start module instantiation. Don't run 'start' function yet.
	let intermediate_instance =
		ModuleInstance::new(module, &ImportsBuilder::new().with_resolver("env", &resolver))?;

	// Verify that the module has the heap base global variable.
	let _ = get_heap_base(intermediate_instance.not_started_instance())?;

	// The `module` should export the memory with the correct properties (min, max).
	//
	// This is ensured by modifying the `RuntimeBlob` before initializing the `Module`.
	let memory = get_mem_instance(intermediate_instance.not_started_instance())?;

	if intermediate_instance.has_start() {
		// Runtime is not allowed to have the `start` function.
		Err(Error::RuntimeHasStartFn)
	} else {
		Ok((
			intermediate_instance.assert_no_start(),
			resolver.missing_functions.into_inner(),
			memory,
		))
	}
}

/// A state snapshot of an instance taken just after instantiation.
///
/// It is used for restoring the state of the module after execution.
#[derive(Clone)]
struct GlobalValsSnapshot {
	/// The list of all global mutable variables of the module in their sequential order.
	global_mut_values: Vec<RuntimeValue>,
}

impl GlobalValsSnapshot {
	// Returns `None` if instance is not valid.
	fn take(module_instance: &ModuleRef) -> Self {
		// Collect all values of mutable globals.
		let global_mut_values = module_instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.map(|g| g.get())
			.collect();
		Self { global_mut_values }
	}

	/// Reset the runtime instance to the initial version by restoring
	/// the preserved memory and globals.
	///
	/// Returns `Err` if applying the snapshot is failed.
	fn apply(&self, instance: &ModuleRef) -> Result<(), WasmError> {
		for (global_ref, global_val) in instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.zip(self.global_mut_values.iter())
		{
			// the instance should be the same as used for preserving and
			// we iterate the same way it as we do it for preserving values that means that the
			// types should be the same and all the values are mutable. So no error is expected/
			global_ref.set(*global_val).map_err(|_| WasmError::ApplySnapshotFailed)?;
		}
		Ok(())
	}
}

/// A runtime along with initial copy of data segments.
pub struct WasmiRuntime {
	/// A wasm module.
	module: Module,
	/// The host functions registered for this instance.
	host_functions: Arc<Vec<&'static dyn Function>>,
	/// Enable stub generation for functions that are not available in `host_functions`.
	/// These stubs will error when the wasm blob tries to call them.
	allow_missing_func_imports: bool,

	global_vals_snapshot: GlobalValsSnapshot,
	data_segments_snapshot: DataSegmentsSnapshot,
}

impl WasmModule for WasmiRuntime {
	fn new_instance(&self) -> Result<Box<dyn WasmInstance>, Error> {
		// Instantiate this module.
		let (instance, missing_functions, memory) =
			instantiate_module(&self.module, &self.host_functions, self.allow_missing_func_imports)
				.map_err(|e| WasmError::Instantiation(e.to_string()))?;

		Ok(Box::new(WasmiInstance {
			instance,
			memory,
			global_vals_snapshot: self.global_vals_snapshot.clone(),
			data_segments_snapshot: self.data_segments_snapshot.clone(),
			host_functions: self.host_functions.clone(),
			allow_missing_func_imports: self.allow_missing_func_imports,
			missing_functions: Arc::new(missing_functions),
			memory_zeroed: true,
		}))
	}
}

/// Create a new `WasmiRuntime` given the code. This function loads the module and
/// stores it in the instance.
pub fn create_runtime(
	mut blob: RuntimeBlob,
	heap_alloc_strategy: HeapAllocStrategy,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> Result<WasmiRuntime, WasmError> {
	let data_segments_snapshot =
		DataSegmentsSnapshot::take(&blob).map_err(|e| WasmError::Other(e.to_string()))?;

	// Make sure we only have exported memory to simplify the code of the wasmi executor.
	blob.convert_memory_import_into_export()?;
	// Ensure that the memory uses the correct heap pages.
	blob.setup_memory_according_to_heap_alloc_strategy(heap_alloc_strategy)?;

	let module =
		Module::from_parity_wasm_module(blob.into_inner()).map_err(|_| WasmError::InvalidModule)?;

	let global_vals_snapshot = {
		let (instance, _, _) =
			instantiate_module(&module, &host_functions, allow_missing_func_imports)
				.map_err(|e| WasmError::Instantiation(e.to_string()))?;
		GlobalValsSnapshot::take(&instance)
	};

	Ok(WasmiRuntime {
		module,
		data_segments_snapshot,
		global_vals_snapshot,
		host_functions: Arc::new(host_functions),
		allow_missing_func_imports,
	})
}

/// Wasmi instance wrapper along with the state snapshot.
pub struct WasmiInstance {
	/// A wasm module instance.
	instance: ModuleRef,
	/// The memory instance of used by the wasm module.
	memory: MemoryRef,
	/// Is the memory zeroed?
	memory_zeroed: bool,
	/// The snapshot of global variable values just after instantiation.
	global_vals_snapshot: GlobalValsSnapshot,
	/// The snapshot of data segments.
	data_segments_snapshot: DataSegmentsSnapshot,
	/// The host functions registered for this instance.
	host_functions: Arc<Vec<&'static dyn Function>>,
	/// Enable stub generation for functions that are not available in `host_functions`.
	/// These stubs will error when the wasm blob trie to call them.
	allow_missing_func_imports: bool,
	/// List of missing functions detected during function resolution
	missing_functions: Arc<Vec<String>>,
}

// This is safe because `WasmiInstance` does not leak any references to `self.memory` and
// `self.instance`
unsafe impl Send for WasmiInstance {}

impl WasmiInstance {
	fn call_impl(
		&mut self,
		method: InvokeMethod,
		data: &[u8],
		allocation_stats: &mut Option<AllocationStats>,
	) -> Result<Vec<u8>, Error> {
		// We reuse a single wasm instance for multiple calls and a previous call (if any)
		// altered the state. Therefore, we need to restore the instance to original state.

		if !self.memory_zeroed {
			// First, zero initialize the linear memory.
			self.memory.erase().map_err(|e| {
				// Snapshot restoration failed. This is pretty unexpected since this can happen
				// if some invariant is broken or if the system is under extreme memory pressure
				// (so erasing fails).
				error!(target: "wasm-executor", "snapshot restoration failed: {}", e);
				WasmError::ErasingFailed(e.to_string())
			})?;
		}

		// Second, reapply data segments into the linear memory.
		self.data_segments_snapshot
			.apply(|offset, contents| self.memory.set(offset, contents))?;

		// Third, restore the global variables to their initial values.
		self.global_vals_snapshot.apply(&self.instance)?;

		let res = call_in_wasm_module(
			&self.instance,
			&self.memory,
			method,
			data,
			self.host_functions.clone(),
			self.allow_missing_func_imports,
			self.missing_functions.clone(),
			allocation_stats,
		);

		// If we couldn't unmap it, erase the memory.
		self.memory_zeroed = self.memory.erase().is_ok();

		res
	}
}

impl WasmInstance for WasmiInstance {
	fn call_with_allocation_stats(
		&mut self,
		method: InvokeMethod,
		data: &[u8],
	) -> (Result<Vec<u8>, Error>, Option<AllocationStats>) {
		let mut allocation_stats = None;
		let result = self.call_impl(method, data, &mut allocation_stats);
		(result, allocation_stats)
	}

	fn get_global_const(&mut self, name: &str) -> Result<Option<sp_wasm_interface::Value>, Error> {
		match self.instance.export_by_name(name) {
			Some(global) => Ok(Some(
				global
					.as_global()
					.ok_or_else(|| format!("`{}` is not a global", name))?
					.get()
					.into(),
			)),
			None => Ok(None),
		}
	}

	fn linear_memory_base_ptr(&self) -> Option<*const u8> {
		Some(self.memory.direct_access().as_ref().as_ptr())
	}
}
