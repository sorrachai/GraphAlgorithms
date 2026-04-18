import GraphAlgorithms.DataStructures.SplayTrees.Basic
import Mathlib.Data.List.Sort

set_option autoImplicit false

-- BOTTOM-UP SPLAY (Sleator–Tarjan 1985 formulation)
-- Descend to the target collecting a zipper-style path, then splay upward
-- consuming frames two at a time (zig-zig / zig-zag) and a final single
-- frame as a plain zig/zag when the path length is odd. This is the
-- formulation analysed in Tarjan 1985 ("Sequential Access ..."), Sundar 1989,
-- and Elmasry 2004.

inductive Dir
  | L -- target descended into the left subtree from this parent
  | R -- target descended into the right subtree from this parent
  deriving DecidableEq, Repr

/-- Single primitive rotation that brings the `d`-child of the root up one
level. `L` ↦ `rotateRight`, `R` ↦ `rotateLeft`. -/
def Dir.bringUp : Dir → BinaryTree → BinaryTree
  | .L => rotateRight
  | .R => rotateLeft

/-- Apply `op` to the `d`-child of the root, leaving everything else fixed. -/
def applyChild (d : Dir) (op : BinaryTree → BinaryTree) : BinaryTree → BinaryTree
  | .node l k r =>
    match d with
    | .L => .node (op l) k r
    | .R => .node l k (op r)
  | .empty => .empty

/-- One frame of the search path: the direction we took from this ancestor,
its key, and the subtree we did *not* descend into. -/
structure Frame where
  dir : Dir
  key : ℕ
  sibling : BinaryTree

/-- Re-attach a subtree `c` below the ancestor described by `f`. -/
def Frame.attach (c : BinaryTree) (f : Frame) : BinaryTree :=
  match f.dir with
  | .L => .node c f.key f.sibling
  | .R => .node f.sibling f.key c

/-- Descend from `t` toward `q`, returning the subtree reached (either the
matching node or `.empty` if `q` is absent) and the path above it. The head
of the returned list is the deepest frame (parent of the returned subtree). -/
def descend (t : BinaryTree) (q : ℕ) : BinaryTree × List Frame :=
  go t []
where
  go : BinaryTree → List Frame → BinaryTree × List Frame
  | .empty, acc => (.empty, acc)
  | .node l k r, acc =>
    if q = k then (.node l k r, acc)
    else if q < k then go l ({ dir := .L, key := k, sibling := r } :: acc)
    else go r ({ dir := .R, key := k, sibling := l } :: acc)

/-- Splay the subtree `c` upward along `path`, pairing frames from the bottom
up. Each double step (parent `f1`, grandparent `f2`) is:
* **same-direction** (`zig-zig` / `zag-zag`): two outer rotations in direction
  `f2.dir`;
* **opposite-direction** (`zig-zag` / `zag-zig`): one inner rotation at the
  `f2.dir`-child (in direction `f1.dir`), then one outer rotation (in
  direction `f2.dir`).
A leftover single frame is a plain zig/zag. -/
def splayUp : BinaryTree → List Frame → BinaryTree
  | c, [] => c
  | c, [f] => f.dir.bringUp (f.attach c)
  | c, f1 :: f2 :: rest =>
    let s := f2.attach (f1.attach c)
    let s' :=
      if f1.dir = f2.dir then
        f2.dir.bringUp (f2.dir.bringUp s)
      else
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    splayUp s' rest

/-- Bottom-up splay: the "textbook" splay analysed by Tarjan, Sundar, and
Elmasry. If `q` is absent the last visited ancestor is splayed to the root. -/
def splayBU (t : BinaryTree) (q : ℕ) : BinaryTree :=
  match descend t q with
  | (.empty, []) => .empty
  | (.empty, f :: rest) => splayUp (f.attach .empty) rest
  | (x@(.node _ _ _), path) => splayUp x path

/-- Cost of a bottom-up splay: one unit per rotation, i.e. the length of the
search path. -/
def splayBU.cost (t : BinaryTree) (q : ℕ) : ℝ :=
  match descend t q with
  | (.empty, path) => path.length
  | (.node _ _ _, path) => path.length

-- =========================================================================
-- Phase 0.2 — unfolding lemmas for `splayUp`
-- =========================================================================

@[simp] theorem splayUp_nil (c : BinaryTree) : splayUp c [] = c := rfl

@[simp] theorem splayUp_singleton (c : BinaryTree) (f : Frame) :
    splayUp c [f] = f.dir.bringUp (f.attach c) := rfl

theorem splayUp_cons_cons (c : BinaryTree) (f1 f2 : Frame) (rest : List Frame) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp
        (if f1.dir = f2.dir then
          f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))
        else
          f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp
            (f2.attach (f1.attach c))))
        rest := rfl

theorem splayUp_cons_cons_same (c : BinaryTree) (f1 f2 : Frame)
    (rest : List Frame) (h : f1.dir = f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

theorem splayUp_cons_cons_opp (c : BinaryTree) (f1 f2 : Frame)
    (rest : List Frame) (h : f1.dir ≠ f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp
        (applyChild f2.dir f1.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

/-- Two-step induction principle specialised to `splayUp`: base (empty path),
singleton frame, and the general pair-cons step. The tree `c` is
generalised automatically. -/
theorem splayUp_induction
    {motive : BinaryTree → List Frame → Prop}
    (nil : ∀ c, motive c [])
    (single : ∀ c f, motive c [f])
    (step : ∀ c f1 f2 rest,
      (∀ c', motive c' rest) → motive c (f1 :: f2 :: rest))
    (c : BinaryTree) (path : List Frame) : motive c path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => exact nil c
  | singleton f => exact single c f
  | cons_cons f1 f2 rest ih _ => exact step c f1 f2 rest (fun c' => ih c')

-- =========================================================================
-- Phase 0.1 — node-count invariants
-- =========================================================================

/-- Number of nodes a single frame contributes when re-attached: the
ancestor itself plus its sibling subtree. -/
def Frame.nodes (f : Frame) : ℕ := 1 + f.sibling.num_nodes

/-- Total number of nodes contributed by a path above a subtree. -/
def pathNodes : List Frame → ℕ
  | [] => 0
  | f :: rest => f.nodes + pathNodes rest

@[simp] lemma pathNodes_nil : pathNodes [] = 0 := rfl

@[simp] lemma pathNodes_cons (f : Frame) (rest : List Frame) :
    pathNodes (f :: rest) = f.nodes + pathNodes rest := rfl

@[simp, grind =]
theorem num_nodes_Frame_attach (c : BinaryTree) (f : Frame) :
    (f.attach c).num_nodes = c.num_nodes + f.nodes := by
  unfold Frame.attach Frame.nodes
  cases f.dir <;> simp [BinaryTree.num_nodes] <;> ring

@[simp, grind =]
theorem num_nodes_bringUp (d : Dir) (t : BinaryTree) :
    (d.bringUp t).num_nodes = t.num_nodes := by
  cases d <;> simp [Dir.bringUp]

@[simp, grind =]
theorem num_nodes_applyChild (d : Dir) (op : BinaryTree → BinaryTree)
    (hop : ∀ s, (op s).num_nodes = s.num_nodes) (t : BinaryTree) :
    (applyChild d op t).num_nodes = t.num_nodes := by
  cases t with
  | empty => rfl
  | node l k r =>
    cases d <;> simp [applyChild, BinaryTree.num_nodes, hop]

@[simp]
theorem num_nodes_splayUp (c : BinaryTree) (path : List Frame) :
    (splayUp c path).num_nodes = c.num_nodes + pathNodes path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => simp [splayUp]
  | singleton f => simp [splayUp, Frame.nodes, pathNodes]
  | cons_cons f1 f2 rest ih _ =>
    have hac : ∀ s,
        (applyChild f2.dir f1.dir.bringUp s).num_nodes = s.num_nodes := by
      intro s; exact num_nodes_applyChild _ _ (num_nodes_bringUp _) _
    unfold splayUp
    split_ifs with h
    · rw [ih]
      simp [Frame.nodes, pathNodes_cons]; ring
    · rw [ih]
      simp [Frame.nodes, pathNodes_cons, hac]; ring

theorem num_nodes_descend_go (t : BinaryTree) (q : ℕ) (acc : List Frame) :
    let r := descend.go q t acc
    r.1.num_nodes + pathNodes r.2 = t.num_nodes + pathNodes acc := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp [BinaryTree.num_nodes]
    · have := ihl (acc := { dir := .L, key := k, sibling := r } :: acc)
      simp [Frame.nodes, BinaryTree.num_nodes] at this ⊢
      linarith
    · have := ihr (acc := { dir := .R, key := k, sibling := l } :: acc)
      simp [Frame.nodes, BinaryTree.num_nodes] at this ⊢
      linarith

theorem num_nodes_descend (t : BinaryTree) (q : ℕ) :
    (descend t q).1.num_nodes + pathNodes (descend t q).2 = t.num_nodes := by
  have := num_nodes_descend_go t q []
  simpa [descend] using this

@[simp]
theorem num_nodes_splayBU (t : BinaryTree) (q : ℕ) :
    (splayBU t q).num_nodes = t.num_nodes := by
  unfold splayBU
  have hd := num_nodes_descend t q
  match h : descend t q with
  | (.empty, []) =>
      rw [h] at hd
      simp [BinaryTree.num_nodes] at hd
      simp [BinaryTree.num_nodes, hd]
  | (.empty, f :: rest) =>
      rw [h] at hd
      simp only [num_nodes_splayUp, num_nodes_Frame_attach, BinaryTree.num_nodes,
        pathNodes_cons] at hd ⊢
      linarith
  | (.node l k r, path) =>
      rw [h] at hd
      simp only [num_nodes_splayUp]
      linarith

-- =========================================================================
-- Phase 0.3 — `descend` characterisations
-- =========================================================================

/-- Reassemble a subtree `c` with its ancestral path `path` (deepest frame
first) back into the original tree. -/
def reassemble (c : BinaryTree) (path : List Frame) : BinaryTree :=
  path.foldl (fun c' f => f.attach c') c

@[simp] lemma reassemble_nil (c : BinaryTree) : reassemble c [] = c := rfl

@[simp] lemma reassemble_cons (c : BinaryTree) (f : Frame) (rest : List Frame) :
    reassemble c (f :: rest) = reassemble (f.attach c) rest := rfl

@[simp] lemma descend_empty (q : ℕ) : descend .empty q = (.empty, []) := rfl

lemma descend_go_append (q : ℕ) (t : BinaryTree) (acc : List Frame) :
    descend.go q t acc =
      ((descend.go q t []).1, (descend.go q t []).2 ++ acc) := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · rw [ihl (acc := { dir := .L, key := k, sibling := r } :: acc)]
      rw [ihl (acc := [{ dir := .L, key := k, sibling := r }])]
      simp
    · rw [ihr (acc := { dir := .R, key := k, sibling := l } :: acc)]
      rw [ihr (acc := [{ dir := .R, key := k, sibling := l }])]
      simp

lemma descend_node_eq (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    descend (.node l k r) k = (.node l k r, []) := by
  simp [descend, descend.go]

lemma descend_eq_descend_go (t : BinaryTree) (q : ℕ) :
    descend t q = descend.go q t [] := rfl

lemma descend_node_lt {l : BinaryTree} {k : ℕ} {r : BinaryTree} {q : ℕ}
    (h : q < k) :
    descend (.node l k r) q =
      ((descend l q).1,
       (descend l q).2 ++ [{ dir := .L, key := k, sibling := r }]) := by
  have hne : q ≠ k := by omega
  change descend.go q (.node l k r) [] = _
  unfold descend.go
  rw [if_neg hne, if_pos h,
      descend_go_append q l [{ dir := .L, key := k, sibling := r }]]
  rfl

lemma descend_node_gt {l : BinaryTree} {k : ℕ} {r : BinaryTree} {q : ℕ}
    (h : k < q) :
    descend (.node l k r) q =
      ((descend r q).1,
       (descend r q).2 ++ [{ dir := .R, key := k, sibling := l }]) := by
  have hne : q ≠ k := by omega
  have hnlt : ¬ q < k := by omega
  change descend.go q (.node l k r) [] = _
  unfold descend.go
  rw [if_neg hne, if_neg hnlt,
      descend_go_append q r [{ dir := .R, key := k, sibling := l }]]
  rfl

lemma reassemble_append (c : BinaryTree) (p1 p2 : List Frame) :
    reassemble c (p1 ++ p2) = reassemble (reassemble c p1) p2 := by
  simp [reassemble, List.foldl_append]

theorem descend_go_preserves_tree (t : BinaryTree) (q : ℕ) (acc : List Frame) :
    reassemble (descend.go q t acc).1 (descend.go q t acc).2 =
      reassemble t acc := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · exact ihl (acc := { dir := .L, key := k, sibling := r } :: acc)
    · exact ihr (acc := { dir := .R, key := k, sibling := l } :: acc)

theorem descend_preserves_tree (t : BinaryTree) (q : ℕ) :
    reassemble (descend t q).1 (descend t q).2 = t := by
  have := descend_go_preserves_tree t q []
  simpa [descend] using this

lemma descend_go_length_le (q : ℕ) (t : BinaryTree) (acc : List Frame) :
    acc.length ≤ (descend.go q t acc).2.length := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · exact Nat.le_of_lt
        (Nat.lt_of_lt_of_le (by simp)
          (ihl (acc := { dir := .L, key := k, sibling := r } :: acc)))
    · exact Nat.le_of_lt
        (Nat.lt_of_lt_of_le (by simp)
          (ihr (acc := { dir := .R, key := k, sibling := l } :: acc)))

-- =========================================================================
-- Phase 0.4 / 0.5 — cost and search-path length in terms of `descend`
-- =========================================================================

/-- Subtrees have positive search path length. -/
lemma search_path_len_node_pos (l : BinaryTree) (k : ℕ) (r : BinaryTree)
    (q : ℕ) : 1 ≤ (BinaryTree.node l k r).search_path_len q := by
  unfold BinaryTree.search_path_len; split_ifs <;> omega

/-- Relation between `search_path_len` and the length of the path produced by
`descend`. When `descend` reaches a node, the search path is one link longer;
when it reaches `.empty`, the two are equal. -/
theorem search_path_len_eq_descend_length (t : BinaryTree) (q : ℕ) :
    t.search_path_len q =
      (descend t q).2.length +
        (match (descend t q).1 with | .empty => 0 | .node _ _ _ => 1) := by
  induction t with
  | empty => simp [BinaryTree.search_path_len, descend, descend.go]
  | node l k r ihl ihr =>
    by_cases hqk : q = k
    · subst hqk
      simp [BinaryTree.search_path_len, descend_node_eq]
    · by_cases hlt : q < k
      · rw [descend_node_lt hlt]
        unfold BinaryTree.search_path_len
        simp only [hlt, if_true, List.length_append, List.length_singleton]
        rw [ihl]; omega
      · have hgt : k < q := by omega
        rw [descend_node_gt hgt]
        unfold BinaryTree.search_path_len
        simp only [hlt, hgt, if_false, if_true, List.length_append,
          List.length_singleton]
        rw [ihr]; omega

/-- The bottom-up splay cost equals the length of the descended path
(equivalently, the number of rotations performed). -/
theorem splayBU_cost_eq_length (t : BinaryTree) (q : ℕ) :
    splayBU.cost t q = ((descend t q).2.length : ℝ) := by
  unfold splayBU.cost
  match h : descend t q with
  | (.empty, path) => rfl
  | (.node _ _ _, path) => rfl

theorem splayBU_cost_nonneg (t : BinaryTree) (q : ℕ) :
    0 ≤ splayBU.cost t q := by
  rw [splayBU_cost_eq_length]; positivity

-- =========================================================================
-- Phase 0.6 — toKeyList preservation (as equality; rotations preserve order)
-- =========================================================================

open BinaryTree (toKeyList)

@[simp] theorem toKeyList_rotateRight (t : BinaryTree) :
    (rotateRight t).toKeyList = t.toKeyList := by
  unfold rotateRight
  cases t with
  | empty => rfl
  | node l k r =>
    cases l with
    | empty => rfl
    | node ll lk lr => simp [toKeyList]
@[simp] theorem toKeyList_rotateLeft (t : BinaryTree) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  unfold rotateLeft
  cases t with
  | empty => rfl
  | node l k r =>
    cases r with
    | empty => rfl
    | node rl rk rr => simp [toKeyList]

@[simp] theorem toKeyList_bringUp (d : Dir) (t : BinaryTree) :
    (d.bringUp t).toKeyList = t.toKeyList := by
  cases d <;> simp [Dir.bringUp]

@[simp] theorem toKeyList_applyChild (d : Dir) (op : BinaryTree → BinaryTree)
    (hop : ∀ s, (op s).toKeyList = s.toKeyList) (t : BinaryTree) :
    (applyChild d op t).toKeyList = t.toKeyList := by
  cases t with
  | empty => rfl
  | node l k r => cases d <;> simp [applyChild, toKeyList, hop]

@[simp] theorem toKeyList_Frame_attach (c : BinaryTree) (f : Frame) :
    (f.attach c).toKeyList =
      (match f.dir with
        | .L => c.toKeyList ++ [f.key] ++ f.sibling.toKeyList
        | .R => f.sibling.toKeyList ++ [f.key] ++ c.toKeyList) := by
  unfold Frame.attach
  cases f.dir <;> simp [toKeyList]

lemma reassemble_toKeyList_congr {c1 c2 : BinaryTree} (path : List Frame)
    (h : c1.toKeyList = c2.toKeyList) :
    (reassemble c1 path).toKeyList = (reassemble c2 path).toKeyList := by
  induction path generalizing c1 c2 with
  | nil => simp [h]
  | cons f rest ih =>
    apply ih
    simp [h]

theorem toKeyList_splayUp (c : BinaryTree) (path : List Frame) :
    (splayUp c path).toKeyList = (reassemble c path).toKeyList := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp [splayUp, reassemble]
  | step c f1 f2 rest ih =>
    unfold splayUp
    split_ifs with h
    · rw [ih]
      apply reassemble_toKeyList_congr
      simp
    · rw [ih]
      apply reassemble_toKeyList_congr
      have hac : ∀ s,
          (applyChild f2.dir f1.dir.bringUp s).toKeyList = s.toKeyList :=
        fun s => toKeyList_applyChild _ _ (toKeyList_bringUp _) _
      simp [hac]

theorem toKeyList_splayBU (t : BinaryTree) (q : ℕ) :
    (splayBU t q).toKeyList = t.toKeyList := by
  unfold splayBU
  have hpres := descend_preserves_tree t q
  match h : descend t q with
  | (.empty, []) =>
      rw [h] at hpres
      simp at hpres
      simp [← hpres, toKeyList]
  | (.empty, f :: rest) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]
      simp [reassemble]
  | (.node l k r, path) =>
      rw [h] at hpres
      rw [toKeyList_splayUp, ← hpres]

theorem splayBU_empty_iff (t : BinaryTree) (q : ℕ) :
    splayBU t q = .empty ↔ t = .empty := by
  constructor
  · intro h
    have hn := num_nodes_splayBU t q
    rw [h] at hn
    cases t with
    | empty => rfl
    | node l k r => simp [BinaryTree.num_nodes] at hn; omega
  · rintro rfl
    simp [splayBU, descend, descend.go]

-- =========================================================================
-- Phase 0.8 — root of `splayBU` on a contained key
-- =========================================================================

/-- If `t.contains q`, the subtree reached by `descend` is a node whose key
equals `q`. Mirrors how `descend` and `BinaryTree.contains` follow the same
comparison path. -/
theorem descend_contains (t : BinaryTree) (q : ℕ) (h : t.contains q) :
    ∃ l r, (descend t q).1 = .node l q r := by
  induction t with
  | empty => simp [BinaryTree.contains] at h
  | node lt k rt ihl ihr =>
    unfold BinaryTree.contains at h
    by_cases hlt : q < k
    · rw [if_pos hlt] at h
      obtain ⟨l', r', hd⟩ := ihl h
      refine ⟨l', r', ?_⟩
      rw [descend_node_lt hlt]; exact hd
    · rw [if_neg hlt] at h
      by_cases hgt : k < q
      · rw [if_pos hgt] at h
        obtain ⟨l', r', hd⟩ := ihr h
        refine ⟨l', r', ?_⟩
        rw [descend_node_gt hgt]; exact hd
      · have hqk : q = k := by omega
        subst hqk
        refine ⟨lt, rt, ?_⟩
        rw [descend_node_eq]

/-- Splaying a node `c = .node l k r` upward along any path yields a tree
whose root key is still `k`. Each rotation step (`bringUp`, `applyChild
bringUp`) brings `c` one level higher without changing its root key. -/
theorem splayUp_root_key_of_node :
    ∀ (path : List Frame) (l : BinaryTree) (k : ℕ) (r : BinaryTree),
      ∃ l' r', splayUp (.node l k r) path = .node l' k r' := by
  intro path
  induction path using List.twoStepInduction with
  | nil => intro l k r; exact ⟨l, r, rfl⟩
  | singleton f =>
      intro l k r
      simp only [splayUp_singleton]
      cases hd : f.dir
      · exact ⟨l, .node r f.key f.sibling, by
          simp [Frame.attach, Dir.bringUp, hd, rotateRight]⟩
      · exact ⟨.node f.sibling f.key l, r, by
          simp [Frame.attach, Dir.bringUp, hd, rotateLeft]⟩
  | cons_cons f1 f2 rest ih _ =>
      intro l k r
      rw [splayUp_cons_cons]
      obtain ⟨d1, k1, s1⟩ := f1
      obtain ⟨d2, k2, s2⟩ := f2
      -- Show the inner expression is a node with root key `k`, then apply IH.
      suffices hstep :
          ∃ l' r',
            (if d1 = d2 then
                d2.bringUp (d2.bringUp
                  (Frame.attach (Frame.attach (.node l k r) ⟨d1, k1, s1⟩)
                    ⟨d2, k2, s2⟩))
              else
                d2.bringUp (applyChild d2 d1.bringUp
                  (Frame.attach (Frame.attach (.node l k r) ⟨d1, k1, s1⟩)
                    ⟨d2, k2, s2⟩))) = .node l' k r' by
        obtain ⟨l', r', hkey⟩ := hstep
        simp only [hkey]
        exact ih l' k r'
      cases d1 <;> cases d2 <;>
        simp [Frame.attach, Dir.bringUp, applyChild, rotateRight, rotateLeft]

-- =========================================================================
-- Phase 0.7 — BST preservation
-- =========================================================================

/-- `ForallTree p t` is equivalent to "every key in the in-order traversal
of `t` satisfies `p`". Reduces tree-quantifier reasoning to list-membership. -/
lemma ForallTree_iff_toKeyList (p : ℕ → Prop) (t : BinaryTree) :
    ForallTree p t ↔ ∀ k ∈ t.toKeyList, p k := by
  induction t with
  | empty =>
    constructor
    · intro _ k hk; simp [BinaryTree.toKeyList] at hk
    · intro _; exact .left
  | node l k r ihl ihr =>
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
    constructor
    · intro h
      cases h with
      | node _ _ _ hl hk hr =>
        intro k' hk'
        rcases hk' with (hk' | rfl) | hk'
        · exact (ihl.mp hl) k' hk'
        · exact hk
        · exact (ihr.mp hr) k' hk'
    · intro h
      refine .node _ _ _
        (ihl.mpr fun k' hk' => h _ (Or.inl (Or.inl hk')))
        (h _ (Or.inl (Or.inr rfl)))
        (ihr.mpr fun k' hk' => h _ (Or.inr hk'))

/-- A tree is a BST iff its in-order traversal is strictly sorted (pairwise
`<`). Reduces every BST-preservation question to "does the operation
preserve `toKeyList`?". -/
theorem IsBST_iff_toKeyList_sorted (t : BinaryTree) :
    IsBST t ↔ t.toKeyList.Pairwise (· < ·) := by
  induction t with
  | empty =>
    refine ⟨fun _ => by simp [BinaryTree.toKeyList], fun _ => .left⟩
  | node l k r ihl ihr =>
    constructor
    · intro h
      cases h with
      | node _ _ _ hfl hfr hBl hBr =>
        have hl := ihl.mp hBl
        have hr := ihr.mp hBr
        have hlk : ∀ k' ∈ l.toKeyList, k' < k :=
          (ForallTree_iff_toKeyList _ _).mp hfl
        have hkr : ∀ k' ∈ r.toKeyList, k < k' :=
          (ForallTree_iff_toKeyList _ _).mp hfr
        simp only [BinaryTree.toKeyList, List.pairwise_append,
          List.pairwise_cons, List.Pairwise.nil, List.mem_singleton,
          List.mem_append, List.not_mem_nil, false_implies, implies_true,
          and_true, true_and]
        refine ⟨⟨hl, ?_⟩, hr, ?_⟩
        · intro a ha b hb; subst hb; exact hlk a ha
        · rintro a (ha | rfl) b hb
          · exact lt_trans (hlk a ha) (hkr b hb)
          · exact hkr b hb
    · intro h
      simp only [BinaryTree.toKeyList, List.pairwise_append,
        List.pairwise_cons, List.Pairwise.nil, List.mem_singleton,
        List.mem_append, List.not_mem_nil, false_implies, implies_true,
        and_true, true_and] at h
      obtain ⟨⟨hl, hlk_raw⟩, hr, hcross⟩ := h
      have hlk : ∀ k' ∈ l.toKeyList, k' < k :=
        fun k' hk' => hlk_raw k' hk' k rfl
      have hkr : ∀ k' ∈ r.toKeyList, k < k' :=
        fun k' hk' => hcross k (Or.inr rfl) k' hk'
      refine .node _ _ _ ?_ ?_ (ihl.mpr hl) (ihr.mpr hr)
      · exact (ForallTree_iff_toKeyList _ _).mpr hlk
      · exact (ForallTree_iff_toKeyList _ _).mpr hkr

/-- Bottom-up splay preserves the BST invariant. Follows from
`toKeyList_splayBU` combined with `IsBST_iff_toKeyList_sorted`. -/
theorem IsBST_splayBU (t : BinaryTree) (q : ℕ) (h : IsBST t) :
    IsBST (splayBU t q) := by
  rw [IsBST_iff_toKeyList_sorted] at h ⊢
  rwa [toKeyList_splayBU]

/-- Each primitive rotation preserves the BST invariant (key-list sort is
preserved because `toKeyList` is invariant under rotation). -/
theorem IsBST_bringUp (d : Dir) (t : BinaryTree) (h : IsBST t) :
    IsBST (d.bringUp t) := by
  rw [IsBST_iff_toKeyList_sorted] at h ⊢
  rwa [toKeyList_bringUp]

theorem IsBST_applyChild (d : Dir) (op : BinaryTree → BinaryTree)
    (hop_keys : ∀ s, (op s).toKeyList = s.toKeyList)
    (t : BinaryTree) (h : IsBST t) :
    IsBST (applyChild d op t) := by
  rw [IsBST_iff_toKeyList_sorted] at h ⊢
  rwa [toKeyList_applyChild _ _ hop_keys]

/-- Any frame-wise splay-up preserves BST-ness of the reassembled tree. -/
theorem IsBST_splayUp (c : BinaryTree) (path : List Frame)
    (h : IsBST (reassemble c path)) : IsBST (splayUp c path) := by
  rw [IsBST_iff_toKeyList_sorted] at h ⊢
  rwa [toKeyList_splayUp]

/-- If `t.contains q`, the bottom-up splay of `t` at `q` has `q` at the root.
Replaces `Correctness.splay_root_of_contains` for `splayBU`. -/
theorem splayBU_root_of_contains (t : BinaryTree) (q : ℕ)
    (hc : t.contains q) : ∃ l r, splayBU t q = .node l q r := by
  obtain ⟨lr, rr, hd⟩ := descend_contains t q hc
  unfold splayBU
  rcases hdecomp : descend t q with ⟨reached, path⟩
  rw [hdecomp] at hd
  subst hd
  exact splayUp_root_key_of_node path lr q rr
