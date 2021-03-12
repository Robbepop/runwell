// Copyright 2021 Robin Freyler
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::primitive::Edge;

/// Allows to immutably visit all edges in an instruction.
///
/// Implemented by all Runwell IR instructions.
pub trait VisitEdges {
    /// Visits every edge in the instruction by the given visitor.
    ///
    /// # Note
    ///
    /// The visitor returns `true` if it wants to continue visiting more values.
    fn visit_edges<V>(&self, visitor: V)
    where
        V: FnMut(Edge) -> bool;
}

/// Allows to visit all edges in an instruction by mutable reference.
///
/// Implemented by all Runwell IR instructions.
pub trait VisitEdgesMut {
    /// Visits every edge in the instruction by mutable reference by the given visitor.
    ///
    /// # Note
    ///
    /// The visitor returns `true` if it wants to continue visiting more values.
    fn visit_edges_mut<V>(&mut self, visitor: V)
    where
        V: FnMut(&mut Edge) -> bool;
}
