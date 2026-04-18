/-
The goal of this file is to show correctness of splay trees,
i.e. that they maintain the binary search tree property and
that the splay operation correctly moves the accessed node to the root.

Two main theorems are established:
  1. splay_preserves_BST  : IsBST t → IsBST (splay t q)
  2. splay_root_of_contains : t.contains q → ∃ l r, splay t q = .node l q r
-/

import GraphAlgorithms.DataStructures.SplayTrees.Basic

set_option autoImplicit false

-- ============================================================
-- SECTION 1: FORALL-TREE HELPER LEMMAS
-- These lemmas say that ForallTree (a predicate holding on every
-- node key) is closed under tree rearrangements (rotations, splay).
-- ============================================================

/-- ForallTree is monotone: a weaker predicate follows from a stronger one. -/
lemma forallTree_mono {p q : ℕ → Prop} {t : BinaryTree}
    (hmono : ∀ x, p x → q x) (h : ForallTree p t) : ForallTree q t := by
  induction h with
  | left => exact .left
  | node l k r _ hk _ ihl ihr => exact .node l k r ihl (hmono k hk) ihr

/-- ForallTree is preserved by a right rotation,
because the same keys appear; only structure changes. -/
lemma forallTree_rotateRight {p : ℕ → Prop} {t : BinaryTree}
    (h : ForallTree p t) : ForallTree p (rotateRight t) := by
  unfold rotateRight
  match t with
  | .empty => exact h
  | .node .empty k r => exact h
  | .node (.node a x b) y c =>
    exact .node a x (.node b y c)
      h.left_sub.left_sub h.left_sub.root
      (.node b y c h.left_sub.right_sub h.root h.right_sub)

/-- ForallTree is preserved by a left rotation.
because the same keys appear; only structure changes. -/
lemma forallTree_rotateLeft {p : ℕ → Prop} {t : BinaryTree}
    (h : ForallTree p t) : ForallTree p (rotateLeft t) := by
  unfold rotateLeft
  match t with
  | .empty => exact h
  | .node l k .empty => exact h
  | .node a y (.node b x c) =>
    exact .node (.node a y b) x c
      (.node a y b h.left_sub h.root h.right_sub.left_sub)
      h.right_sub.root h.right_sub.right_sub

/-- ForallTree is thus preserved by any rotation strategy. -/
lemma forallTree_rotate {p : ℕ → Prop} (rt : Rot) {t : BinaryTree}
    (h : ForallTree p t) : ForallTree p (rotate t rt) := by
  unfold rotate
  match rt with
  | .zigZig => exact forallTree_rotateRight (forallTree_rotateRight h)
  | .zigZag =>
    match t with
    | .empty => exact h
    | .node l k r =>
      exact forallTree_rotateRight
        (.node _ _ _ (forallTree_rotateLeft h.left_sub) h.root h.right_sub)
  | .zagZag => exact forallTree_rotateLeft (forallTree_rotateLeft h)
  | .zagZig =>
    match t with
    | .empty => exact h
    | .node l k r =>
      exact forallTree_rotateLeft
        (.node _ _ _ h.left_sub h.root (forallTree_rotateRight h.right_sub))
  | .zig => exact forallTree_rotateRight h
  | .zag => exact forallTree_rotateLeft h

/-- ForallTree is preserved by splay: every key satisfying p before still satisfies p after. -/
lemma forallTree_splay {p : ℕ → Prop} (t : BinaryTree) (q : ℕ)
    (h : ForallTree p t) : ForallTree p (splay t q) := by
  fun_induction splay
  -- Case: empty tree
  · exact h
  -- Case: q equals the root key — tree is unchanged
  · exact h
  -- Case: q < k, left child is empty — tree is unchanged
  · exact h
  -- Case: q < k, left = .node, q < lk, ll = .empty — single zig rotation
  · apply forallTree_rotate; exact h
  -- Case: ZigZig — recurse into ll, then double-rotate
  · rename_i k r c1 c2 ll lk lr c3 h_ll_ne ih
    apply forallTree_rotate
    exact .node _ _ _ (.node _ _ _ (ih h.left_sub.left_sub) h.left_sub.root h.left_sub.right_sub)
      h.root h.right_sub
  -- Case: q < k, left = .node, lk < q, lr = .empty — single zig rotation
  · apply forallTree_rotate; exact h
  -- Case: ZigZag — recurse into lr, then zig-zag rotate
  · rename_i k r _ _ ll lk lr _ _ _ ih
    apply forallTree_rotate
    exact .node _ _ _ (.node _ _ _ h.left_sub.left_sub h.left_sub.root (ih h.left_sub.right_sub))
      h.root h.right_sub
  -- Case: q = lk (found at left child) — single zig rotation
  · apply forallTree_rotate; exact h
  -- Case: q > k, right child empty — tree is unchanged
  · exact h
  -- Case: q > k, right = .node, q < rk, rl = .empty — single zag rotation
  · apply forallTree_rotate; exact h
  -- Case: ZagZig — recurse into rl, then zag-zig rotate
  · rename_i _ _ _ _ rl rk rr _ _ ih
    apply forallTree_rotate
    exact .node _ _ _ h.left_sub h.root
      (.node _ _ _ (ih h.right_sub.left_sub) h.right_sub.root h.right_sub.right_sub)
  -- Case: q > k, right = .node, rk < q, rr = .empty — single zag rotation
  · apply forallTree_rotate; exact h
  -- Case: ZagZag — recurse into rr, then double left-rotate
  · rename_i _ _ _ _ rl rk rr _ _ _ ih
    apply forallTree_rotate
    exact .node _ _ _ h.left_sub h.root
      (.node _ _ _ h.right_sub.left_sub h.right_sub.root (ih h.right_sub.right_sub))
  -- Case: q = rk (found at right child) — single zag rotation
  · apply forallTree_rotate; exact h

-- ============================================================
-- SECTION 2: BST INVARIANT PRESERVATION UNDER ROTATIONS
-- Each rotation only reshuffles the tree; BST order is maintained.
-- ============================================================

/-- Right rotation preserves the BST invariant. -/
lemma rotateRight_preserves_BST {t : BinaryTree} (h : IsBST t) :
    IsBST (rotateRight t) := by
  unfold rotateRight
  match t with
  | .empty => exact h
  | .node .empty k r => exact h
  | .node (.node a x b) y c =>
    have hFL := h.forallTree_left; have hBL := h.left_bst
    -- Goal: IsBST (.node a x (.node b y c))
    exact .node _ _ _
      hBL.forallTree_left
      (.node b y c hBL.forallTree_right hFL.root
        (forallTree_mono (fun k hk => Nat.lt_trans hFL.root hk) h.forallTree_right))
      hBL.left_bst
      (.node y b c hFL.right_sub h.forallTree_right hBL.right_bst h.right_bst)

/-- Left rotation preserves the BST invariant. Symmetric to rotateRight. -/
lemma rotateLeft_preserves_BST {t : BinaryTree} (h : IsBST t) :
    IsBST (rotateLeft t) := by
  unfold rotateLeft
  match t with
  | .empty => exact h
  | .node l k .empty => exact h
  | .node a y (.node b x c) =>
    have hFR := h.forallTree_right; have hBR := h.right_bst
    -- Goal: IsBST (.node (.node a y b) x c)
    exact .node _ _ _
      (.node a y b
        (forallTree_mono (fun k hk => Nat.lt_trans hk hFR.root) h.forallTree_left)
        hFR.root hBR.forallTree_left)
      hBR.forallTree_right
      (.node y a b h.forallTree_left hFR.left_sub h.left_bst hBR.left_bst)
      hBR.right_bst

/-- Any rotation strategy preserves the BST invariant. -/
lemma rotate_preserves_BST (rt : Rot) {t : BinaryTree} (h : IsBST t) :
    IsBST (rotate t rt) := by
  unfold rotate
  match rt with
  | .zigZig => exact rotateRight_preserves_BST (rotateRight_preserves_BST h)
  | .zigZag =>
    match t with
    | .empty => exact h
    | .node l k r =>
      exact rotateRight_preserves_BST
        (.node _ _ _ (forallTree_rotateLeft h.forallTree_left) h.forallTree_right
          (rotateLeft_preserves_BST h.left_bst) h.right_bst)
  | .zagZag => exact rotateLeft_preserves_BST (rotateLeft_preserves_BST h)
  | .zagZig =>
    match t with
    | .empty => exact h
    | .node l k r =>
      exact rotateLeft_preserves_BST
        (.node _ _ _ h.forallTree_left (forallTree_rotateRight h.forallTree_right)
          h.left_bst (rotateRight_preserves_BST h.right_bst))
  | .zig => exact rotateRight_preserves_BST h
  | .zag => exact rotateLeft_preserves_BST h

-- ============================================================
-- SECTION 3: SPLAY PRESERVES THE BST INVARIANT
-- This is the central correctness theorem. We proceed by
-- fun_induction following the recursive structure of splay.
-- In each case we either return an unchanged subtree, apply a
-- single rotation, or (for the double-rotation cases) first
-- recursively splay a grandchild and then rotate.
-- ============================================================

/-- The splay operation preserves the BST invariant. -/
theorem splay_preserves_BST (t : BinaryTree) (q : ℕ) (h : IsBST t) :
    IsBST (splay t q) := by
  fun_induction splay
  -- Case: empty tree
  · exact h
  -- Case: q equals the root — tree returned unchanged
  · exact h
  -- Case: q < k, left child empty — tree returned unchanged
  · exact h
  -- Case: q < k, left = .node, q < lk, ll = .empty — single zig (no recursion)
  · exact rotate_preserves_BST .zig h
  -- Case: ZigZig — recursively splay ll, then double right-rotate
  · rename_i k r _ _ ll lk lr _ _ ih
    apply rotate_preserves_BST
    have hFL := h.forallTree_left; have hBL := h.left_bst
    exact .node _ _ _
      (.node _ _ _ (forallTree_splay ll q hFL.left_sub) hFL.root hFL.right_sub)
      h.forallTree_right
      (.node _ _ _ (forallTree_splay ll q hBL.forallTree_left) hBL.forallTree_right
        (ih hBL.left_bst) hBL.right_bst)
      h.right_bst
  -- Case: q < k, left = .node, lk < q, lr = .empty — single zig (no recursion)
  · exact rotate_preserves_BST .zig h
  -- Case: ZigZag — recursively splay lr, then zig-zag rotate
  · rename_i k r _ _ ll lk lr _ _ _ ih
    apply rotate_preserves_BST
    have hFL := h.forallTree_left; have hBL := h.left_bst
    exact .node _ _ _
      (.node _ _ _ hFL.left_sub hFL.root (forallTree_splay lr q hFL.right_sub))
      h.forallTree_right
      (.node _ _ _ hBL.forallTree_left (forallTree_splay lr q hBL.forallTree_right)
        hBL.left_bst (ih hBL.right_bst))
      h.right_bst
  -- Case: q = lk (found at left child) — single zig
  · exact rotate_preserves_BST .zig h
  -- Case: q > k, right child empty — tree unchanged
  · exact h
  -- Case: q > k, right = .node, q < rk, rl = .empty — single zag (no recursion)
  · exact rotate_preserves_BST .zag h
  -- Case: ZagZig — recursively splay rl, then zag-zig rotate
  · rename_i _ _ _ _ rl rk rr _ _ ih
    apply rotate_preserves_BST
    have hFR := h.forallTree_right; have hBR := h.right_bst
    exact .node _ _ _
      h.forallTree_left
      (.node _ _ _ (forallTree_splay rl q hFR.left_sub) hFR.root hFR.right_sub)
      h.left_bst
      (.node _ _ _ (forallTree_splay rl q hBR.forallTree_left) hBR.forallTree_right
        (ih hBR.left_bst) hBR.right_bst)
  -- Case: q > k, right = .node, rk < q, rr = .empty — single zag (no recursion)
  · exact rotate_preserves_BST .zag h
  -- Case: ZagZag — recursively splay rr, then double left-rotate
  · rename_i _ _ _ _ rl rk rr _ _ _ ih
    apply rotate_preserves_BST
    have hFR := h.forallTree_right; have hBR := h.right_bst
    exact .node _ _ _
      h.forallTree_left
      (.node _ _ _ hFR.left_sub hFR.root (forallTree_splay rr q hFR.right_sub))
      h.left_bst
      (.node _ _ _ hBR.forallTree_left (forallTree_splay rr q hBR.forallTree_right)
        hBR.left_bst (ih hBR.right_bst))
  -- Case: q = rk (found at right child) — single zag
  · exact rotate_preserves_BST .zag h

-- ============================================================
-- SECTION 4: SPLAY MOVES THE TARGET KEY TO THE ROOT
-- If `q` is found by `BinaryTree.contains`, then `splay t q`
-- has `q` at the root. The proof follows the recursive shape
-- of `splay`, case-by-case.
-- Remark: This theorem does not require `IsBST t`. It only
-- relies on the operational meaning of `BinaryTree.contains`
-- used in this file: at each node, the search follows one
-- branch using key comparisons.
-- ============================================================

/-- The root of the splayed tree is the target key if it is present. -/
theorem splay_root_of_contains (t : BinaryTree) (q : ℕ)
    (hc : t.contains q) : ∃ l r, splay t q = .node l q r := by
  /-
    Each `splay` branch is either a contradiction (the `contains` hypothesis
    is impossible for that control-flow path, discharged by `simp_all`) or
    a constructive branch (recursive IH + rotation shape gives root `q`).
    The `@[simp]` lemmas `contains_node_lt`, `contains_node_gt`,
    `contains_node_not_eq_not_lt`, and `not_contains_empty` let `simp_all`
    chase `contains` through the tree and close contradiction branches
    automatically.
  -/
  fun_induction splay
  · -- empty tree
    contradiction
  · -- q = k: found at root
    rename_i l r; exact ⟨l, r, rfl⟩
  · -- q < k, l = .empty
    simp_all
  · -- q < lk, ll = .empty
    simp_all
  · -- ZigZig: recurse on ll, then double right-rotate
    rename_i k r _ _ ll lk lr _ _ ih
    obtain ⟨A, B, hsplay⟩ := ih (by simp_all)
    exact ⟨A, .node B lk (.node lr k r), by simp [hsplay, rotate, rotateRight]⟩
  · -- lk < q, lr = .empty
    simp_all
  · -- ZigZag: recurse on lr, then zig-zag rotate
    rename_i k r _ _ ll lk lr _ _ _ ih
    obtain ⟨A, B, hsplay⟩ := ih (by simp_all)
    exact ⟨.node ll lk A, .node B k r,
      by simp [hsplay, rotate, rotateLeft, rotateRight]⟩
  · -- q = lk: found at left child, single zig
    rename_i l k r _ ll lk lr _ _
    have heq : q = lk := by omega
    subst heq; exact ⟨ll, .node lr l k, by simp [rotate, rotateRight]⟩
  · -- q > k, r = .empty
    simp_all
  · -- q < rk, rl = .empty
    simp_all
  · -- ZagZig: recurse on rl, then zag-zig rotate
    rename_i ll lk _ _ rl rk rr _ _ ih
    obtain ⟨A, B, hsplay⟩ := ih (by simp_all)
    exact ⟨.node ll lk A, .node B rk rr,
      by simp [hsplay, rotate, rotateRight, rotateLeft]⟩
  · -- rk < q, rr = .empty
    simp_all
  · -- ZagZag: recurse on rr, then double left-rotate
    rename_i ll lk _ _ rl rk rr _ _ _ ih
    obtain ⟨A, B, hsplay⟩ := ih (by simp_all)
    exact ⟨.node (.node ll lk rl) rk A, B,
      by simp [hsplay, rotate, rotateLeft]⟩
  · -- q = rk: found at right child, single zag
    rename_i ll lk _ _ rl rk rr _ _
    have heq : q = rk := by omega
    subst heq; exact ⟨.node ll lk rl, rr, by simp [rotate, rotateLeft]⟩
