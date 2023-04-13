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

use super::common::wasmi::{MemoryRef, memory_units::Pages};

/// Wrapper around [`MemorRef`] that implements [`sp_allocator::Memory`].
pub struct MemoryWrapper<'a>(&'a MemoryRef);

impl<'a> From<&'a MemoryRef> for MemoryWrapper<'a> {
    fn from(value: &'a MemoryRef) -> Self {
        Self(value)
    }
}

impl sp_allocator::Memory for MemoryWrapper<'_> {
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
					"Failed to grow memory by {} pages: {}",
					additional,
					e,
				)
			})
			.map(drop)
	}
}
