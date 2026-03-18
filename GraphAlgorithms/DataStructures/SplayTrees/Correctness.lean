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
  | .empty => exact h -- no keys, so trivially preserved
  | .node .empty k r => exact h -- left child empty, so no change
  | .node (.node a x b) y c =>
    -- h : ForallTree p (.node (.node a x b) y c), we now deconstruct the ForallTree to
    -- rebuild the rotated tree
    cases h with
    | node _ _ _ hl hy hr =>
      cases hl with
      | node _ _ _ ha hx hb =>
        -- Rebuild: .node a x (.node b y c)
        exact .node a x (.node b y c) ha hx (.node b y c hb hy hr)

/-- ForallTree is preserved by a left rotation.
because the same keys appear; only structure changes. -/
lemma forallTree_rotateLeft {p : ℕ → Prop} {t : BinaryTree}
    (h : ForallTree p t) : ForallTree p (rotateLeft t) := by
  unfold rotateLeft
  match t with
  | .empty => exact h -- no keys, so trivially preserved
  | .node l k .empty => exact h -- right child empty, so no change
  | .node a y (.node b x c) =>
    -- h : ForallTree p (.node a y (.node b x c)), we now deconstruct the ForallTree to
    -- rebuild the rotated tree
    cases h with
    | node _ _ _ ha hy hbc =>
      cases hbc with
      | node _ _ _ hb hx hc =>
        -- Rebuild: .node (.node a y b) x c
        exact .node (.node a y b) x c (.node a y b ha hy hb) hx hc

/-- ForallTree is thus preserved by any rotation strategy. -/
lemma forallTree_rotate {p : ℕ → Prop} (rt : Rot) {t : BinaryTree}
    (h : ForallTree p t) : ForallTree p (rotate t rt) := by
  unfold rotate
  match rt with
  | .zigZig =>
    -- Two right rotations preserve ForallTree.
    exact forallTree_rotateRight (forallTree_rotateRight h)
  | .zigZag =>
    -- The left subtree after the first left rotation still satisfies ForallTree,
    -- so the second left right also preserves it.
    match t with
    | .empty => exact h -- no keys, so trivially preserved
    | .node l k r =>
      apply forallTree_rotateRight
      cases h with
      | node _ _ _ hl hk hr =>
        exact .node _ _ _ (forallTree_rotateLeft hl) hk hr
  | .zagZag =>
    -- Two left rotations preserve ForallTree.
    exact forallTree_rotateLeft (forallTree_rotateLeft h)
  | .zagZig =>
    -- The right subtree after the first right rotation still satisfies ForallTree,
    -- so the second left rotation also preserves it.
    match t with
    | .empty => exact h -- no keys, so trivially preserved
    | .node l k r =>
      apply forallTree_rotateLeft
      cases h with
      | node _ _ _ hl hk hr =>
        exact .node _ _ _ hl hk (forallTree_rotateRight hr)
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
    cases h with
    | node _ _ _ hl hk hr =>
      cases hl with
      | node _ _ _ hll hlk hlr =>
        exact .node _ _ _ (.node _ _ _ (ih hll) hlk hlr) hk hr
  -- Case: q < k, left = .node, lk < q, lr = .empty — single zig rotation
  · apply forallTree_rotate; exact h
  -- Case: ZigZag — recurse into lr, then double-rotate
  · rename_i k r c1 c2 ll lk lr c3 c4 h_lr_ne ih
    apply forallTree_rotate
    cases h with
    | node _ _ _ hl hk hr =>
      cases hl with
      | node _ _ _ hll hlk hlr =>
        exact .node _ _ _ (.node _ _ _ hll hlk (ih hlr)) hk hr
  -- Case: q = lk (found at left child) — single zig rotation
  · apply forallTree_rotate; exact h
  -- Case: q > k, right child is empty — tree is unchanged
  · exact h
  -- Case: q > k, right = .node, q < rk, rl = .empty — single zag rotation
  · apply forallTree_rotate; exact h
  -- Case: ZagZig — recurse into rl, then double-rotate
  · rename_i ll lk h h_1 rl rk rr h_2 h_rl_ne ih
    apply forallTree_rotate
    cases h with
    | node _ _ _ hl hk hr =>
      cases hr with
      | node _ _ _ hrl hrk hrr =>
        exact .node _ _ _ hl hk (.node _ _ _ (ih hrl) hrk hrr)
  -- Case: q > k, right = .node, rk < q, rr = .empty — single zag rotation
  · apply forallTree_rotate; exact h
  -- Case: ZagZag — recurse into rr, then double-rotate
  · rename_i ll lk h h_1 rl rk rr h_2 h_3 h_rr_ne ih
    apply forallTree_rotate
    cases h with
    | node _ _ _ hl hk hr =>
      cases hr with
      | node _ _ _ hrl hrk hrr =>
        exact .node _ _ _ hl hk (.node _ _ _ hrl hrk (ih hrr))
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
    -- Deconstruct outer BST node
    cases h with
    | node _ _ _ hfall_l hfall_r hbst_l hbst_r =>
      -- hfall_l : ForallTree (· < y) (.node a x b)
      -- hfall_r : ForallTree (y < ·) c
      -- hbst_l  : IsBST (.node a x b)
      -- hbst_r  : IsBST c
      cases hbst_l with
      | node _ _ _ ha_lt_x hx_lt_b hbst_a hbst_b =>
        -- ha_lt_x : ForallTree (· < x) a,  hx_lt_b : ForallTree (x < ·) b
        -- Deconstruct the ForallTree for the left subtree
        cases hfall_l with
        | node _ _ _ ha_lt_y hxy hb_lt_y =>
          -- ha_lt_y : ForallTree (· < y) a,  hxy : x < y,  hb_lt_y : ForallTree (· < y) b
          -- Goal: IsBST (.node a x (.node b y c))
          apply IsBST.node
          · -- ForallTree (· < x) a  (unchanged from inner BST)
            exact ha_lt_x
          · -- ForallTree (x < ·) (.node b y c):
            --   all of b satisfy x < · (from inner BST),
            --   x < y (from outer ForallTree),
            --   all of c satisfy y < · ≥ x < · (by transitivity)
            exact .node b y c hx_lt_b hxy
              (forallTree_mono (fun k hk => Nat.lt_trans hxy hk) hfall_r)
          · exact hbst_a
          · -- IsBST (.node b y c):  b < y (from outer ForallTree), y < c (unchanged)
            exact IsBST.node y b c hb_lt_y hfall_r hbst_b hbst_r

/-- Left rotation preserves the BST invariant. Symmetric to rotateRight. -/
lemma rotateLeft_preserves_BST {t : BinaryTree} (h : IsBST t) :
    IsBST (rotateLeft t) := by
  unfold rotateLeft
  match t with
  | .empty => exact h
  | .node l k .empty  => exact h
  | .node a y (.node b x c) =>
    -- Deconstruct outer BST node
    cases h with
    | node _ _ _ hfall_l hfall_r hbst_l hbst_r =>
      -- hfall_l : ForallTree (· < y) a
      -- hfall_r : ForallTree (y < ·) (.node b x c)
      -- hbst_l  : IsBST a
      -- hbst_r  : IsBST (.node b x c)
      cases hbst_r with
      | node _ _ _ hb_lt_x hx_lt_c hbst_b hbst_c =>
        -- hb_lt_x : ForallTree (· < x) b,  hx_lt_c : ForallTree (x < ·) c
        -- Deconstruct the ForallTree for the right subtree
        cases hfall_r with
        | node _ _ _ hb_gt_y hyx hc_gt_y =>
          -- hb_gt_y : ForallTree (y < ·) b,  hyx : y < x,  hc_gt_y : ForallTree (y < ·) c
          -- Goal: IsBST (.node (.node a y b) x c)
          apply IsBST.node
          · -- ForallTree (· < x) (.node a y b):
            --   all of a satisfy · < y ≤ · < x (by transitivity),
            --   y < x (from outer ForallTree),
            --   all of b satisfy · < x (from inner BST)
            exact .node a y b
              (forallTree_mono (fun k hk => Nat.lt_trans hk hyx) hfall_l)
              hyx hb_lt_x
          · exact hx_lt_c
          · -- IsBST (.node a y b): a < y (from outer ForallTree), y < b (unchanged)
            exact IsBST.node y a b hfall_l hb_gt_y hbst_l hbst_b
          · exact hbst_c

/-- Any rotation strategy preserves the BST invariant. -/
lemma rotate_preserves_BST (rt : Rot) {t : BinaryTree} (h : IsBST t) :
    IsBST (rotate t rt) := by
  unfold rotate
  match rt with
  | .zigZig =>
    exact rotateRight_preserves_BST (rotateRight_preserves_BST h)
  | .zigZag =>
    match t with
    | .empty => exact h
    | .node l k r =>
      apply rotateRight_preserves_BST
      cases h with
      | node _ _ _ hfall_l hfall_r hbst_l hbst_r =>
        apply IsBST.node
        · -- ForallTree (· < k) (rotateLeft l):
          -- all keys of l satisfy · < k, and rotateLeft is a permutation
          exact forallTree_rotateLeft hfall_l
        · exact hfall_r
        · exact rotateLeft_preserves_BST hbst_l
        · exact hbst_r
  | .zagZag =>
    exact rotateLeft_preserves_BST (rotateLeft_preserves_BST h)
  | .zagZig =>
    match t with
    | .empty => exact h
    | .node l k r =>
      apply rotateLeft_preserves_BST
      cases h with
      | node _ _ _ hfall_l hfall_r hbst_l hbst_r =>
        apply IsBST.node
        · exact hfall_l
        · -- ForallTree (k < ·) (rotateRight r)
          -- all keys of r satisfy k < ·, and rotateRight is a permutation
          exact forallTree_rotateRight hfall_r
        · exact hbst_l
        · exact rotateRight_preserves_BST hbst_r
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
  · rename_i k r c1 c2 ll lk lr c3 h_ll_ne ih
    -- h   : IsBST (.node (.node ll lk lr) k r)
    -- ih  : IsBST ll → IsBST (splay ll q)
    -- Goal: IsBST (rotate (.node (.node (splay ll q) lk lr) k r) .zigZig)
    apply rotate_preserves_BST
    -- Peel off the outer BST node
    cases h with
    | node _ _ _ hfall_outer hfall_r hbst_inner hbst_r =>
      -- hfall_outer : ForallTree (· < k) (.node ll lk lr)
      -- hbst_inner  : IsBST (.node ll lk lr)
      cases hbst_inner with
      | node _ _ _ hfall_ll hfall_lr hbst_ll hbst_lr =>
        -- hfall_ll : ForallTree (· < lk) ll
        -- hfall_lr : ForallTree (lk < ·) lr
        -- hbst_ll  : IsBST ll  →  by ih  →  IsBST (splay ll q)
        cases hfall_outer with
        | node _ _ _ hll_lt_k hlk_lt_k hlr_lt_k =>
          -- Build IsBST (.node (.node (splay ll q) lk lr) k r)
          apply IsBST.node
          · -- ForallTree (· < k) (.node (splay ll q) lk lr):
            --   keys of splay ll q are keys of ll (permutation), all < k
            exact .node _ _ _ (forallTree_splay ll q hll_lt_k) hlk_lt_k hlr_lt_k
          · exact hfall_r
          · -- IsBST (.node (splay ll q) lk lr)
            apply IsBST.node
            · -- ForallTree (· < lk) (splay ll q): permutation of ll, all < lk
              exact forallTree_splay ll q hfall_ll
            · exact hfall_lr
            · exact ih hbst_ll
            · exact hbst_lr
          · exact hbst_r
  -- Case: q < k, left = .node, lk < q, lr = .empty — single zig (no recursion)
  · exact rotate_preserves_BST .zig h
  -- Case: ZigZag — recursively splay lr, then zig-zag rotate
  · rename_i k r c1 c2 ll lk lr c3 c4 h_lr_ne ih
    apply rotate_preserves_BST
    cases h with
    | node _ _ _ hfall_outer hfall_r hbst_inner hbst_r =>
      cases hbst_inner with
      | node _ _ _ hfall_ll hfall_lr hbst_ll hbst_lr =>
        cases hfall_outer with
        | node _ _ _ hll_lt_k hlk_lt_k hlr_lt_k =>
          apply IsBST.node
          · exact .node _ _ _ hll_lt_k hlk_lt_k (forallTree_splay lr q hlr_lt_k)
          · exact hfall_r
          · apply IsBST.node
            · exact hfall_ll
            · -- ForallTree (lk < ·) (splay lr q): permutation of lr, all > lk
              exact forallTree_splay lr q hfall_lr
            · exact hbst_ll
            · exact ih hbst_lr
          · exact hbst_r
  -- Case: q = lk (found at left child) — single zig
  · exact rotate_preserves_BST .zig h
  -- Case: q > k, right child empty — tree unchanged
  · exact h
  -- Case: q > k, right = .node, q < rk, rl = .empty — single zag (no recursion)
  · exact rotate_preserves_BST .zag h
  -- Case: ZagZig — recursively splay rl, then zag-zig rotate
  · rename_i ll lk h_neq h_gt rl rk rr h_lt h_rl_ne ih
    apply rotate_preserves_BST
    cases h with
    | node _ _ _ hfall_l hfall_outer hbst_l hbst_inner =>
      cases hbst_inner with
      | node _ _ _ hfall_rl hfall_rr hbst_rl hbst_rr =>
        cases hfall_outer with
        | node _ _ _ hrl_gt_k hrk_gt_k hrr_gt_k =>
          apply IsBST.node
          · exact hfall_l
          · exact .node _ _ _ (forallTree_splay rl q hrl_gt_k) hrk_gt_k hrr_gt_k
          · exact hbst_l
          · apply IsBST.node
            · exact forallTree_splay rl q hfall_rl
            · exact hfall_rr
            · exact ih hbst_rl
            · exact hbst_rr
  -- Case: q > k, right = .node, rk < q, rr = .empty — single zag (no recursion)
  · exact rotate_preserves_BST .zag h
  -- Case: ZagZag — recursively splay rr, then double left-rotate
  · rename_i ll lk h_neq h_gt rl rk rr h_nlt h_rk_lt h_rr_ne ih
    apply rotate_preserves_BST
    cases h with
    | node _ _ _ hfall_l hfall_outer hbst_l hbst_inner =>
      cases hbst_inner with
      | node _ _ _ hfall_rl hfall_rr hbst_rl hbst_rr =>
        cases hfall_outer with
        | node _ _ _ hrl_gt_k hrk_gt_k hrr_gt_k =>
          apply IsBST.node
          · exact hfall_l
          · exact .node _ _ _ hrl_gt_k hrk_gt_k (forallTree_splay rr q hrr_gt_k)
          · exact hbst_l
          · apply IsBST.node
            · exact hfall_rl
            · exact forallTree_splay rr q hfall_rr
            · exact hbst_rl
            · exact ih hbst_rr
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

/-- Helper: unfold contains for the left branch. -/
private lemma contains_left {l : BinaryTree} {k q : ℕ} {r : BinaryTree}
    (hlt : q < k) (hc : (BinaryTree.node l k r).contains q) : l.contains q := by
  simp only [BinaryTree.contains] at hc
  simp_all

/-- Helper: unfold contains for the right branch. -/
private lemma contains_right {l : BinaryTree} {k q : ℕ} {r : BinaryTree}
    (hgt : k < q) (hc : (BinaryTree.node l k r).contains q) : r.contains q := by
  simp only [BinaryTree.contains] at hc
  have hlt : ¬ q < k := Nat.not_lt.mpr (Nat.le_of_lt hgt)
  simp_all

/-- Helper: after a ZigZig rotation, the root is the original left-left grandchild. -/
private lemma root_after_zigZig (q k lk : ℕ)
    (A B lr r : BinaryTree) :
    rotate (.node (.node (.node A q B) lk lr) k r) .zigZig
      = .node A q (.node B lk (.node lr k r)) := by
  simp only [rotate, rotateRight]

/-- Helper: after a ZigZag rotation, the root is the original left-right grandchild. -/
private lemma root_after_zigZag (q k lk : ℕ)
    (ll A B r : BinaryTree) :
    rotate (.node (.node ll lk (.node A q B)) k r) .zigZag
      = .node (.node ll lk A) q (.node B k r) := by
  simp only [rotate, rotateLeft, rotateRight]

/-- Helper: after a ZagZig rotation, the root is the original right-left grandchild. -/
private lemma root_after_zagZig (q lk rk : ℕ)
    (ll A B rr : BinaryTree) :
    rotate (.node ll lk (.node (.node A q B) rk rr)) .zagZig
      = .node (.node ll lk A) q (.node B rk rr) := by
  simp only [rotate, rotateRight, rotateLeft]

/-- Helper: after a ZagZag rotation, the root is the original right-right grandchild. -/
private lemma root_after_zagZag (q lk rk : ℕ)
    (ll rl A B : BinaryTree) :
    rotate (.node ll lk (.node rl rk (.node A q B))) .zagZag
      = .node (.node (.node ll lk rl) rk A) q B := by
  simp only [rotate, rotateLeft]


/-- The root of the splayed tree is the target key if it is present. -/
theorem splay_root_of_contains_v3 (t : BinaryTree) (q : ℕ)
    (hc : t.contains q) : ∃ l r, splay t q = .node l q r := by
  -- Reading guide for this proof:
  -- each `splay` branch is either
  -- (1) a contradiction branch: `contains q` is impossible for that control-flow path,
  -- or
  -- (2) a constructive branch: recursive IH + one rotation helper gives root `q`.
  /-
    The only nontrivial shape step in constructive branches is the final rotation outcome.
    There are exactly four double-rotation patterns in `splay` (`zigZig`, `zigZag`, `zagZig`,
    `zagZag`), and each helper lemma states that after this rotation, the root is `q` when
    the recursively splayed subtree already has root `q`. Once those four shape facts are
    available, the rest is just extracting the right `contains` hypothesis for the recursive call.
  -/
  fun_induction splay
  · -- Contradiction branch: empty tree cannot contain any key.
    contradiction
  · -- Constructive branch: found at root, so splay returns unchanged.
    rename_i l r
    exact ⟨l, r, rfl⟩
  · -- Contradiction branch: we are in the `q < k` path with `l = .empty`.
    rename_i l k r c1
    simp only [BinaryTree.contains, c1] at hc
    exact False.elim hc
  · -- Contradiction branch: left-left case with `ll = .empty`.
    rename_i l k r c1 lk lr c3
    have h1 : (BinaryTree.node .empty lk lr).contains q := contains_left c1 hc
    simp only [BinaryTree.contains, c3] at h1
    simp at h1
  · -- Constructive branch: Zig-Zig, recurse on `ll`, then apply rotation shape.
    rename_i k r c1 c2 ll lk lr c3 h_ll_ne ih
    have h1 : (BinaryTree.node ll lk lr).contains q := contains_left c2 hc
    have h2 : ll.contains q := by
      simp only [BinaryTree.contains, c3] at h1
      exact h1
    obtain ⟨A, B, hsplay⟩ := ih h2
    refine ⟨A, .node B lk (.node lr k r), ?_⟩
    simp only [hsplay]
    exact root_after_zigZig q k lk A B lr r
  · -- Contradiction branch: left-right case with `lr = .empty`.
    rename_i l k r c1 ll lk c3 c4
    have h1 : (BinaryTree.node ll lk .empty).contains q := contains_left c1 hc
    simp only [BinaryTree.contains, c3, c4] at h1
    simp at h1
  · -- Constructive branch: Zig-Zag, recurse on `lr`, then apply rotation shape.
    rename_i k r c1 c2 ll lk lr c3 c4 h_lr_ne ih
    have h1 : (BinaryTree.node ll lk lr).contains q := contains_left c2 hc
    have h2 : lr.contains q := by
      have hlt : ¬ q < lk := Nat.not_lt.mpr (Nat.le_of_lt c4)
      simp only [BinaryTree.contains, hlt, c4] at h1
      exact h1
    obtain ⟨A, B, hsplay⟩ := ih h2
    refine ⟨.node ll lk A, .node B k r, ?_⟩
    simp only [hsplay]
    exact root_after_zigZag q k lk ll A B r
  · -- Constructive branch: found at left child, so single zig rotation puts `q` at root.
    rename_i l k r c1 ll lk lr c3 c4
    have heq : q = lk := Nat.le_antisymm (Nat.not_lt.mp c4) (Nat.not_lt.mp c3)
    subst heq
    simp only [rotate, rotateRight]
    exact ⟨ll, .node lr l k, rfl⟩
  · -- Contradiction branch: we are in the `q > k` path with `r = .empty`.
    rename_i l k r c1
    have hgt : k < q := lt_of_le_of_ne (Nat.le_of_not_lt c1) (Ne.symm r)
    have h1 : BinaryTree.empty.contains q := contains_right hgt hc
    simp only [BinaryTree.contains] at h1
  · -- Contradiction branch: right-left case with `rl = .empty`.
    rename_i ll lk c1 c2 rk rr c3
    have hgt : lk < q := lt_of_le_of_ne (Nat.le_of_not_lt c2) (Ne.symm c1)
    have h1 : (BinaryTree.node .empty rk rr).contains q := contains_right hgt hc
    simp only [BinaryTree.contains, c3] at h1
    simp at h1
  · -- Constructive branch: Zag-Zig, recurse on `rl`, then apply rotation shape.
    rename_i ll lk c1 c2 rl rk rr c3 h_rl_ne ih
    have hgt : lk < q := lt_of_le_of_ne (Nat.le_of_not_lt c2) (Ne.symm c1)
    have h1 : (BinaryTree.node rl rk rr).contains q := contains_right hgt hc
    have h2 : rl.contains q := by
      simp only [BinaryTree.contains, c3] at h1
      exact h1
    obtain ⟨A, B, hsplay⟩ := ih h2
    refine ⟨.node ll lk A, .node B rk rr, ?_⟩
    simp only [hsplay]
    exact root_after_zagZig q lk rk ll A B rr
  · -- Contradiction branch: right-right case with `rr = .empty`.
    rename_i ll lk c1 c2 rl rk c3 c4
    have hgt : lk < q := lt_of_le_of_ne (Nat.le_of_not_lt c2) (Ne.symm c1)
    have h1 : (BinaryTree.node rl rk .empty).contains q := contains_right hgt hc
    simp only [BinaryTree.contains] at h1
    have hlt : ¬ q < rk := Nat.not_lt.mpr (Nat.le_of_lt c4)
    simp only [hlt] at h1
    grind
  · -- Constructive branch: Zag-Zag, recurse on `rr`, then apply rotation shape.
    rename_i ll lk c1 c2 rl rk rr c3 c4 h_rr_ne ih
    have hgt : lk < q := lt_of_le_of_ne (Nat.le_of_not_lt c2) (Ne.symm c1)
    have h1 : (BinaryTree.node rl rk rr).contains q := contains_right hgt hc
    have h2 : rr.contains q := by
      have hlt : ¬ q < rk := Nat.not_lt.mpr (Nat.le_of_lt c4)
      simp only [BinaryTree.contains, hlt, c4] at h1
      exact h1
    obtain ⟨A, B, hsplay⟩ := ih h2
    refine ⟨.node (.node ll lk rl) rk A, B, ?_⟩
    simp only [hsplay]
    exact root_after_zagZag q lk rk ll rl A B
  · -- Constructive branch: found at right child, so single zag rotation puts `q` at root.
    rename_i ll lk c1 c2 rl rk rr c3 c4
    have heq : q = rk := Nat.le_antisymm (Nat.not_lt.mp c4) (Nat.not_lt.mp c3)
    subst heq
    simp only [rotate, rotateLeft]
    exact ⟨.node ll lk rl, rr, rfl⟩
