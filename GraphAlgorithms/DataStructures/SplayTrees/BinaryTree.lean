import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric


set_option autoImplicit false
set_option tactic.hygienic false

inductive BinaryTree where
| empty
| node (left : BinaryTree) (key : ℕ) (right : BinaryTree)
deriving Repr, BEq, DecidableEq

def BinaryTree.left : BinaryTree → BinaryTree
  | .empty => .empty
  | .node l _ _ => l

def BinaryTree.right : BinaryTree → BinaryTree
  | .empty => .empty
  | .node _ _ r => r

theorem non_empty_exist (s : BinaryTree) (h : s ≠ BinaryTree.empty) : ∃ A k B, s = .node A k B :=
  by induction s <;> grind

def BinaryTree.num_nodes : BinaryTree → ℕ
| .empty => 0
| .node left _ right => 1 + (num_nodes left) + (num_nodes right)

/-- In-order traversal as a list of keys. -/
def BinaryTree.toKeyList : BinaryTree → List ℕ
  | .empty => []
  | .node l k r => l.toKeyList ++ [k] ++ r.toKeyList

/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def BinaryTree.search_path_len (t : BinaryTree) (q : ℕ) : ℕ :=
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
because a binary tree could have q >/< key and be in
the left/right subtree of key respectively. Obviously,
if BinaryTree.contains t q is true, then q is in t; but
the converse need not necessarily hold true. The
converse is true for a binary search tree.
-/
def BinaryTree.contains (t : BinaryTree) (q : Nat) : Prop :=
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

@[simp] lemma BinaryTree.not_contains_empty (q : ℕ) :
    ¬ BinaryTree.empty.contains q := nofun

@[simp] lemma BinaryTree.contains_node_lt {l : BinaryTree} {k q : ℕ}
    {r : BinaryTree} (h : q < k) :
    (BinaryTree.node l k r).contains q ↔ l.contains q := by
  simp [BinaryTree.contains, h]

@[simp] lemma BinaryTree.contains_node_gt {l : BinaryTree} {k q : ℕ}
    {r : BinaryTree} (h : k < q) :
    (BinaryTree.node l k r).contains q ↔ r.contains q := by
  simp [BinaryTree.contains, h, Nat.not_lt_of_gt h]

@[simp] lemma BinaryTree.contains_node_not_eq_not_lt
    {l : BinaryTree} {k q : ℕ} {r : BinaryTree}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (BinaryTree.node l k r).contains q ↔ r.contains q := by
  have hgt : k < q := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h2) (Ne.symm (Ne.intro h1))
  simp [BinaryTree.contains, hgt, Nat.not_lt_of_gt hgt]

inductive ForallTree (p : Nat → Prop) : BinaryTree → Prop
  | left : ForallTree p .empty
  | node left key right :
     ForallTree p left →
     p key  →
     ForallTree p right →
     ForallTree p (.node left key  right)

inductive IsBST : BinaryTree → Prop
  | left : IsBST .empty
  | node key left right:
     ForallTree (fun k  => k < key) left →
     ForallTree (fun k  => key < k) right →
     IsBST left → IsBST right →
     IsBST (.node left key right)

-- ============================================================
-- Accessor lemmas for ForallTree
-- ============================================================

lemma ForallTree.left_sub {p : ℕ → Prop} {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : ForallTree p (.node l k r)) : ForallTree p l := by
  cases h with | node _ _ _ hl _ _ => exact hl

lemma ForallTree.root {p : ℕ → Prop} {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : ForallTree p (.node l k r)) : p k := by
  cases h with | node _ _ _ _ hk _ => exact hk

lemma ForallTree.right_sub {p : ℕ → Prop} {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : ForallTree p (.node l k r)) : ForallTree p r := by
  cases h with | node _ _ _ _ _ hr => exact hr

-- ============================================================
-- Accessor lemmas for IsBST
-- ============================================================

lemma IsBST.forallTree_left {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : IsBST (.node l k r)) : ForallTree (· < k) l := by
  cases h with | node _ _ _ hl _ _ _ => exact hl

lemma IsBST.forallTree_right {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : IsBST (.node l k r)) : ForallTree (k < ·) r := by
  cases h with | node _ _ _ _ hr _ _ => exact hr

lemma IsBST.left_bst {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : IsBST (.node l k r)) : IsBST l := by
  cases h with | node _ _ _ _ _ hl _ => exact hl

lemma IsBST.right_bst {l : BinaryTree} {k : ℕ} {r : BinaryTree}
    (h : IsBST (.node l k r)) : IsBST r := by
  cases h with | node _ _ _ _ _ _ hr => exact hr

structure BST (n : ℕ) where
  tree : BinaryTree
  hBST : IsBST tree
  h_size : tree.num_nodes = n
