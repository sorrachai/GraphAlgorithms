/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche, Sorrachai Yingchareonthawornchai
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-!
# Binary Tree

  In this file we introduce the `BinaryTree` data structure and its basic operations.
-/

variable {α : Type}

inductive BinaryTree (α) where
| empty
| node (left : BinaryTree α) (key : α) (right : BinaryTree α)
deriving DecidableEq

def BinaryTree.left : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node l _ _ => l

def BinaryTree.right : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node _ _ r => r

theorem non_empty_exist (s : BinaryTree α) (h : s ≠ BinaryTree.empty) :
∃ A k B, s = .node A k B :=
  by induction s <;> grind

def BinaryTree.num_nodes (α) : BinaryTree α → ℕ
| .empty => 0
| .node left _ right => 1 + (num_nodes α left) + (num_nodes α right)

@[simp] lemma BinaryTree.num_nodes_empty : BinaryTree.empty.num_nodes α = 0 := rfl

@[simp] lemma BinaryTree.num_nodes_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    (BinaryTree.node l k r).num_nodes α = 1 + l.num_nodes α + r.num_nodes α := rfl

/-- In-order traversal as a list of keys. -/
def BinaryTree.toKeyList (α) : BinaryTree α → List α
  | .empty => []
  | .node l k r => l.toKeyList α ++ [k] ++ r.toKeyList α


@[simp] lemma BinaryTree.toKeyList_empty : BinaryTree.empty.toKeyList α = [] := rfl

@[simp] lemma BinaryTree.toKeyList_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    (BinaryTree.node l k r).toKeyList α = l.toKeyList α ++ [k] ++ r.toKeyList α := rfl

/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def BinaryTree.search_path_len [LinearOrder α] (t : BinaryTree α) (q : α) : ℕ :=
  match t with
  | .empty => 0
  | .node left key right =>
    if q < key then
      1 + left.search_path_len q
    else if key < q then
      1 + right.search_path_len q
    else
      1

/-
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If BinaryTree.contains t q is true, then q is in t; but
the converse need not necessarily hold true. The
converse is true for a binary search tree.
-/
def BinaryTree.contains [LinearOrder α] (t : BinaryTree α) (q : α) : Prop :=
  match t with
  | .empty => False
  | .node left key right =>
    if q < key then
      left.contains q
    else if key < q then
      right.contains q
    else
      True

-- ============================================================
-- Simp lemmas for contains
-- ============================================================

@[simp] lemma BinaryTree.not_contains_empty [LinearOrder α] (q : α) :
    ¬ BinaryTree.empty.contains q := nofun

@[simp] lemma BinaryTree.contains_node_lt [LinearOrder α] {l : BinaryTree α} {k q : α}
    {r : BinaryTree α} (h : q < k) :
    (BinaryTree.node l k r).contains q ↔ l.contains q := by
  simp [BinaryTree.contains, h]

@[simp] lemma BinaryTree.contains_node_gt [LinearOrder α] {l : BinaryTree α} {k q : α}
    {r : BinaryTree α} (h : k < q) :
    (BinaryTree.node l k r).contains q ↔ r.contains q := by
  simp [BinaryTree.contains, h, not_lt_of_gt h]

@[simp] lemma BinaryTree.contains_node_not_eq_not_lt [LinearOrder α]
    {l : BinaryTree α} {k q : α} {r : BinaryTree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (BinaryTree.node l k r).contains q ↔ r.contains q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [BinaryTree.contains, hgt, not_lt_of_gt hgt]

inductive ForallTree (p : α → Prop) : BinaryTree α → Prop
  | left : ForallTree p .empty
  | node left key right :
     ForallTree p left →
     p key  →
     ForallTree p right →
     ForallTree p (.node left key right)

inductive IsBST [LinearOrder α] : BinaryTree α → Prop
  | left : IsBST .empty
  | node key left right:
     ForallTree (fun k  => k < key) left →
     ForallTree (fun k  => key < k) right →
     IsBST left → IsBST right →
     IsBST (.node left key right)

-- ============================================================
-- Accessor lemmas for ForallTree
-- ============================================================
@[simp] lemma ForallTree.left_sub {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : ForallTree p l := by
  cases h with | node _ _ _ hl _ _ => exact hl

@[simp] lemma ForallTree.root {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : p k := by
  cases h with | node _ _ _ _ hk _ => exact hk

@[simp] lemma ForallTree.right_sub {p : α → Prop} {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : ForallTree p (.node l k r)) : ForallTree p r := by
  cases h with | node _ _ _ _ _ hr => exact hr

-- ============================================================
-- Accessor lemmas for IsBST
-- ============================================================

@[simp] lemma IsBST.forallTree_left [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : ForallTree (· < k) l := by
  cases h with | node _ _ _ hl _ _ _ => exact hl

@[simp] lemma IsBST.forallTree_right [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : ForallTree (k < ·) r := by
  cases h with | node _ _ _ _ hr _ _ => exact hr

@[simp] lemma IsBST.left_bst [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : IsBST l := by
  cases h with | node _ _ _ _ _ hl _ => exact hl

@[simp] lemma IsBST.right_bst [LinearOrder α] {l : BinaryTree α} {k : α} {r : BinaryTree α}
    (h : IsBST (.node l k r)) : IsBST r := by
  cases h with | node _ _ _ _ _ _ hr => exact hr

structure BST (n : ℕ) (α : Type) [LinearOrder α] where
  tree : BinaryTree α
  hBST : IsBST tree
  h_size : tree.num_nodes = n
