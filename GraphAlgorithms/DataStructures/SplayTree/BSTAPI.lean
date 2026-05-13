/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

import GraphAlgorithms.DataStructures.SplayTree.Correctness
import GraphAlgorithms.DataStructures.SplayTree.Complexity

/-!
# Bundled BST API for Splay Trees

This module provides a clean, user-facing API for splay trees operating strictly
on bundled `BST` types. By leveraging the correctness and complexity theorems
proven in the core modules, we automatically maintain the binary search tree
invariant and size metrics without burdening the end-user with proof obligations.
-/

variable {α : Type} [LinearOrder α]


open BinaryTree
open SplayTree


/-! ### Bundled Splay Operation -/
section BundledSplay

/-- Splay a key `q` in a bundled `BST`. Automatically proves that the resulting
tree maintains the `IsBST` invariant and preserves its exact node count. -/
def BST.splay {n : ℕ} (T : BST n α) (q : α) : BST n α :=
  { tree := SplayTree.splay T.tree q
    hBST := IsBST_splay T.tree q T.hBST
    h_size := by rw [num_nodes_splay, T.h_size] }

end BundledSplay


/-! ### Correctness Guarantees -/
section Correctness

/-- If the tree contains `q`, splaying it guarantees that `q` becomes the root.
We extract this directly from the unbundled proof. -/
theorem BST.splay_root_of_contains {n : ℕ} (T : BST n α) (q : α)
    (hc : T.tree.contains q) : ∃ l r, (T.splay q).tree = .node l q r :=
  SplayTree.splay_root_of_contains T.tree q hc

end Correctness


/-! ### Amortized Complexity Bounds -/
section Complexity

/-- The amortized cost of a single splay operation is bounded by 3 \log_2 n + 1.
Because `T` is a bundled `BST n α`, we can swap the tree's internal size for `n`. -/
theorem BST.splay_amortized_bound {n : ℕ} (T : BST n α) (q : α) :
    φ (T.splay q).tree - φ T.tree + splay.cost T.tree q ≤
      3 * Real.logb 2 n + 1 := by
  have h := SplayTree.splay_amortized_bound T.tree q
  rw [T.h_size] at h
  exact h

/-- The total cost of a sequence of m splay operations is bounded by
m(3 \log_2 n + 1) + n \log_2 n. -/
theorem BST.nlogn_cost {n m : ℕ} (T : BST n α) (X : Fin m → α) :
    splay.sequence_cost T.tree X ≤ m * (3 * Real.logb 2 n + 1) + n * Real.logb 2 n :=
  SplayTree.nlogn_cost n m X T.tree T.h_size

end Complexity
