// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Implementation of conversions between Substrate and wasmi types.

use crate::{Signature, Value, ValueType};
use sp_std::vec::Vec;

pub fn from_value(value: Value) -> wasmi::RuntimeValue {
	match value {
		Value::I32(val) => wasmi::RuntimeValue::I32(val),
		Value::I64(val) => wasmi::RuntimeValue::I64(val),
		Value::F32(val) => wasmi::RuntimeValue::F32(val.into()),
		Value::F64(val) => wasmi::RuntimeValue::F64(val.into()),
	}
}

pub fn into_value(value: wasmi::RuntimeValue) -> Value {
	match value {
		wasmi::RuntimeValue::I32(val) => Value::I32(val),
		wasmi::RuntimeValue::I64(val) => Value::I64(val),
		wasmi::RuntimeValue::F32(val) => Value::F32(val.into()),
		wasmi::RuntimeValue::F64(val) => Value::F64(val.into()),
	}
}

pub fn from_value_type(value: ValueType) -> wasmi::ValueType {
	match value {
		ValueType::I32 => wasmi::ValueType::I32,
		ValueType::I64 => wasmi::ValueType::I64,
		ValueType::F32 => wasmi::ValueType::F32,
		ValueType::F64 => wasmi::ValueType::F64,
	}
}

pub fn into_value_type(value: wasmi::ValueType) -> ValueType {
	match value {
		wasmi::ValueType::I32 => ValueType::I32,
		wasmi::ValueType::I64 => ValueType::I64,
		wasmi::ValueType::F32 => ValueType::F32,
		wasmi::ValueType::F64 => ValueType::F64,
	}
}

impl From<Signature> for wasmi::Signature {
	fn from(sig: Signature) -> Self {
		let args = sig.args.iter().copied().map(from_value_type).collect::<Vec<_>>();
		wasmi::Signature::new(args, sig.return_value.map(from_value_type))
	}
}

impl From<&wasmi::Signature> for Signature {
	fn from(sig: &wasmi::Signature) -> Self {
		Signature::new(
			sig.params().iter().copied().map(into_value_type).collect::<Vec<_>>(),
			sig.return_type().map(into_value_type),
		)
	}
}
