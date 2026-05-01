/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche, Sorrachai Yingchareonthawornchai

The goal of this file is to prove correctness of bottom-up splay trees.
Key theorems:
  1. splayBU_preserves_BST : IsBST t → IsBST (splayBU t q)
  2. splayBU_root_of_contains : t.contains q → ∃ l r, splayBU t q = .node l q r
-/

import GraphAlgorithms.DataStructures.SplayTrees.bottom_up_definition_splay_tree

set_option autoImplicit false

-- ============================================================
-- SECTION 1: HELPER LEMMAS FOR FRAME OPERATIONS
-- ============================================================

/-- ForallTree is monotone: a weaker predicate follows from a stronger one. -/
lemma forallTree_mono {α : Type} {p q : α → Prop} {t : BinaryTree α}
    (hmono : ∀ x, p x → q x) (h : ForallTree p t) : ForallTree q t := by
  induction h with
  | left => exact .left
  | node l k r _ hk _ ihl ihr => exact .node l k r ihl (hmono k hk) ihr

/-- ForallTree is preserved when a subtree c is attached via a frame. -/
lemma forallTree_frame_attach {α : Type} {p : α → Prop}
    (c : BinaryTree α) (f : Frame α)
    (hc : ForallTree p c) (hp : p f.key) (hs : ForallTree p f.sibling) :
    ForallTree p (f.attach c) := by
  unfold Frame.attach
  match f.dir with
  | .L => exact .node c f.key f.sibling hc hp hs
  | .R => exact .node f.sibling f.key c hs hp hc

/-- ForallTree is preserved through the entire splayUp recursion. -/
lemma forallTree_splayUp {α : Type} {p : α → Prop} (c : BinaryTree α) (path : List (Frame α))
    (hc : ForallTree p c) (hpath : ∀ f ∈ path, p f.key ∧ ForallTree p f.sibling) :
    ForallTree p (splayUp c path) := by
  induction path generalizing c with
  | nil => exact hc
  | cons f rest ih =>
    unfold splayUp
    match rest with
    | [] =>
      have ⟨hp, hs⟩ := hpath f (List.mem_cons_self f [])
      simp [Dir.bringUp, rotateRight, rotateLeft]
      exact forallTree_frame_attach c f hc hp hs
    | f2 :: rest' =>
      have ⟨hp1, hs1⟩ := hpath f (List.mem_cons_self f (f2 :: rest'))
      have hpath_rest : ∀ f ∈ f2 :: rest', p f.key ∧ ForallTree p f.sibling := by
        intros f' hf'; exact hpath f' (List.mem_cons_of_mem f hf')
      have ⟨hp2, hs2⟩ := hpath f2 (List.mem_cons_self f2 rest')
      let s := f2.attach (f.attach c)
      have hs : ForallTree p s := forallTree_frame_attach (f.attach c) f2
        (forallTree_frame_attach c f hc hp1 hs1) hp2 hs2
      apply ih hs hpath_rest

-- ============================================================
-- SECTION 2: BST INVARIANT PRESERVATION LEMMAS
-- ============================================================

/-- Right rotation preserves the BST invariant. -/
lemma rotateRight_preserves_BST {α : Type} [LinearOrder α] {t : BinaryTree α} (h : IsBST α t) :
    IsBST α (rotateRight t) := by
  unfold rotateRight
  match t with
  | .empty => exact h
  | .node .empty k r => exact h
  | .node (.node a x b) y c =>
    have hFL := h.forallTree_left; have hBL := h.left_bst
    exact .node _ _ _ hBL.forallTree_left
      (.node b y c hBL.forallTree_right hFL.root
        (forallTree_mono (fun k hk => Nat.lt_trans hFL.root hk) h.forallTree_right))
      hBL.left_bst
      (.node y b c hFL.right_sub h.forallTree_right hBL.right_bst h.right_bst)

/-- Left rotation preserves the BST invariant. -/
lemma rotateLeft_preserves_BST {α : Type} [LinearOrder α] {t : BinaryTree α} (h : IsBST α t) :
    IsBST α (rotateLeft t) := by
  unfold rotateLeft
  match t with
  | .empty => exact h
  | .node l k .empty => exact hs
  | .node a y (.node b x c) =>
    have hFR := h.forallTree_right; have hBR := h.right_bst
    exact .node _ _ _
      (.node a y b
        (forallTree_mono (fun k hk => Nat.lt_trans hk hFR.root) h.forallTree_left)
        hFR.root hBR.forallTree_left)
      hBR.forallTree_right
      (.node y a b h.forallTree_left hFR.left_sub h.left_bst hBR.left_bst)
      hBR.right_bst

/-- Rotating according to direction preserves BST. -/
lemma dir_bringUp_preserves_BST {α : Type} [LinearOrder α] (d : Dir) {t : BinaryTree α} (h : IsBST α t) :
    IsBST α (d.bringUp t) := by
  match d with
  | .L => exact rotateRight_preserves_BST h
  | .R => exact rotateLeft_preserves_BST h

/-- IsBST is preserved when attaching a subtree via a frame (requires BST properties). -/
lemma isBST_frame_attach {α : Type} [LinearOrder α]
    (c : BinaryTree α) (f : Frame α)
    (hc : IsBST α c) (hs : IsBST α f.sibling)
    (hc_lt : ForallTree (· < f.key) c) (hs_gt : ForallTree (f.key < ·) f.sibling) :
    IsBST α (f.attach c) := by
  unfold Frame.attach
  match f.dir with
  | .L => exact .node c f.key f.sibling hc_lt hs_gt hc hs
  | .R => exact .node f.sibling f.key c hs_gt hc_lt hs hc

/-- IsBST is preserved through splayUp when the reassembled tree is a BST. -/
lemma isBST_splayUp {α : Type} [LinearOrder α]
    (c : BinaryTree α) (path : List (Frame α)) (h : IsBST α (reassemble c path)) :
    IsBST α (splayUp c path) := by
  exact IsBST_splayUp c path h

/-- The splayBU operation preserves the BST invariant. -/
theorem splayBU_preserves_BST {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α) (h : IsBST α t) :
    IsBST α (splayBU t q) := by
  -- Delegate to the splay-up BST lemma via the in-order/list characterization
  exact IsBST_splayBU t q h

/-- If splayBU finds the target, it becomes the root of the result. -/
theorem splayBU_root_of_contains {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α)
    (hc : t.contains q) : ∃ l r, splayBU t q = .node l q r := by
  -- Use the descend result to obtain the reached node, then splay it up.
  rcases descend_of_contains t q hc with ⟨l, r, path, heq⟩
  unfold splayBU
  rw [heq]
  exact splayUp_root_key_of_node path l q r

-- ============================================================
-- SECTION 3: DESCEND PROPERTIES
-- ============================================================

/-- If descend returns a non-empty subtree, that subtree is a node with the target key. -/
lemma descend_found_structure {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α) :
    match descend t q with
    | (.node _ k _, _) => k = q
    | _ => True := by
  induction t with
  | empty => simp [descend]; trivial
  | node l k r ihl ihr =>
    by_cases hq : q = k
    · subst hq
      simp [descend_node_eq]; rfl
    · by_cases hlt : q < k
      · rw [descend_node_lt hlt]
        exact ihl q
      · have hgt : k < q := by omega
        rw [descend_node_gt hgt]
        exact ihr q

/-- Extract ForallTree facts for every frame produced by descend. -/
lemma forallTree_of_descend {α : Type} {p : α → Prop} [LinearOrder α] (t : BinaryTree α) (q : α)
    (h : ForallTree p t) : ∀ f ∈ (descend t q).2, p f.key ∧ ForallTree p f.sibling := by
  induction t with
  | empty => simp [descend]; intro f hf; cases hf
  | node l k r ihl ihr =>
    dsimp [descend]
    by_cases hq : q = k
    · simp [descend_node_eq]; intro f hf; cases hf
    · by_cases hlt : q < k
      · rw [descend_node_lt hlt]
        have hl := h.left_sub; have hr := h.right_sub
        intro f hf; cases List.mem_append.1 hf with
        | inl hf' => exact ihl q hl f hf'
        | inr hf' => exact ⟨h.root, hr⟩
      · have hgt : k < q := by omega
        rw [descend_node_gt hgt]
        have hl := h.left_sub; have hr := h.right_sub
        intro f hf; cases List.mem_append.1 hf with
        | inl hf' => exact ⟨h.root, hl⟩
        | inr hf' => exact ihr q hr f hf'

-- ============================================================
-- SECTION 4: CONTAINS AND DESCEND RELATIONSHIP
-- ============================================================

/-- If contains finds q, then descend returns a non-empty result at the head. -/
lemma descend_of_contains {α : Type} [LinearOrder α] (t : BinaryTree α) (q : α) (hc : t.contains q) :
    ∃ l r path, descend t q = (.node l q r, path) := by
  induction t with
  | empty => simp [BinaryTree.contains] at hc; contradiction
  | node l k r ihl ihr =>
    dsimp [BinaryTree.contains] at hc
    by_cases hq : q = k
    · subst hq
      use l, r, []
      simp [descend_node_eq]
    · by_cases hlt : q < k
      · simp [hlt] at hc
        rcases ihl q hc with ⟨ll, rr, path, heq⟩
        use ll, rr, path ++ [{ dir := .L, key := k, sibling := r }]
        rw [descend_node_lt hlt, heq]; rfl
      · have hgt : k < q := by omega
        simp [hgt] at hc
        rcases ihr q hc with ⟨ll, rr, path, heq⟩
        use ll, rr, path ++ [{ dir := .R, key := k, sibling := l }]
        rw [descend_node_gt hgt, heq]; rfl

-- ============================================================
-- SECTION 5: MAIN CORRECTNESS THEOREMS
-- ============================================================

/-- ForallTree is preserved by splayBU: every key satisfying p before still satisfies p after. -/
lemma splayBU_preserves_forallTree {α : Type} {p : α → Prop} (t : BinaryTree α) (q : α)
    (h : ForallTree p t) : ForallTree p (splayBU t q) := by
  unfold splayBU
  let hframes := forallTree_of_descend t q h
  match hpath : descend t q with
  | (.empty, []) => exact .left
  | (.empty, f :: rest) =>
    have ⟨hp, hs⟩ := hframes f (List.mem_cons_self f rest)
    apply forallTree_splayUp
    · exact forallTree_frame_attach .empty f .left hp hs
    · intros f' hf'; exact hframes f' (List.mem_cons_of_mem f hf')
  | (node l k r, path) =>
    apply forallTree_splayUp
    · exact h
    · intros f' hf'; exact hframes f' hf'

