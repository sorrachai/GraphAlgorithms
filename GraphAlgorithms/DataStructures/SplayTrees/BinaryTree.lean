import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric


set_option autoImplicit false
set_option tactic.hygienic false

inductive BinaryTree where
| empty
| node (left : BinaryTree) (key : ℕ) (right : BinaryTree)
deriving Repr, BEq


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

structure BST (n : ℕ) where
  tree : BinaryTree
  hBST : IsBST tree
  h_size : tree.num_nodes = n
