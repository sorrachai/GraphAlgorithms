import GraphAlgorithms.DataStructures.SplayTrees.BinaryTree
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false


-- =========================================================================
-- §1  Definitions
-- =========================================================================
-- Rotation primitives, direction / frame types, descend, splayUp, splayBU.


def rotateRight : BinaryTree → BinaryTree
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree → BinaryTree
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t


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
  (descend t q).2.length


/-- Reassemble a subtree `c` with its ancestral path `path` (deepest frame
first) back into the original tree. -/
def reassemble (c : BinaryTree) (path : List Frame) : BinaryTree :=
  path.foldl (fun c' f => f.attach c') c

@[simp] lemma reassemble_nil (c : BinaryTree) : reassemble c [] = c := rfl

@[simp] lemma reassemble_cons (c : BinaryTree) (f : Frame) (rest : List Frame) :
    reassemble c (f :: rest) = reassemble (f.attach c) rest := rfl


/-- Number of nodes a single frame contributes when re-attached: the
ancestor itself plus its sibling subtree. -/
def Frame.nodes (f : Frame) : ℕ := 1 + f.sibling.num_nodes

/-- Total number of nodes contributed by a path above a subtree. -/
def pathNodes : List Frame → ℕ
  | [] => 0
  | f :: rest => f.nodes + pathNodes rest


-- =========================================================================
-- §2  Unfolding / induction lemmas for `splayUp`
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
-- §3  Node-count invariants
-- =========================================================================

@[simp, grind =]
theorem num_nodes_rotateRight (t : BinaryTree) :
    (rotateRight t).num_nodes = t.num_nodes := by
  unfold rotateRight
  cases t with
  | empty => rfl
  | node l k r =>
    cases l with
    | empty => rfl
    | node ll lk lr => simp; omega

@[simp, grind =]
theorem num_nodes_rotateLeft (t : BinaryTree) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  unfold rotateLeft
  cases t with
  | empty => rfl
  | node l k r =>
    cases r with
    | empty => rfl
    | node rl rk rr => simp; omega


@[simp] lemma pathNodes_nil : pathNodes [] = 0 := rfl

@[simp] lemma pathNodes_cons (f : Frame) (rest : List Frame) :
    pathNodes (f :: rest) = f.nodes + pathNodes rest := rfl

@[simp, grind =]
theorem num_nodes_Frame_attach (c : BinaryTree) (f : Frame) :
    (f.attach c).num_nodes = c.num_nodes + f.nodes := by
  unfold Frame.attach Frame.nodes
  cases f.dir <;> simp <;> omega

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
    cases d <;> simp [applyChild, hop]

@[simp, grind =]
theorem num_nodes_applyChild_bringUp (d₁ d₂ : Dir) (t : BinaryTree) :
    (applyChild d₁ d₂.bringUp t).num_nodes = t.num_nodes :=
  num_nodes_applyChild _ _ (num_nodes_bringUp _) _

@[simp]
theorem num_nodes_splayUp (c : BinaryTree) (path : List Frame) :
    (splayUp c path).num_nodes = c.num_nodes + pathNodes path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => simp [splayUp]
  | singleton f => simp [splayUp, Frame.nodes, pathNodes]
  | cons_cons f1 f2 rest ih _ =>
    unfold splayUp
    split_ifs with h
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega

theorem num_nodes_descend_go (t : BinaryTree) (q : ℕ) (acc : List Frame) :
    let r := descend.go q t acc
    r.1.num_nodes + pathNodes r.2 = t.num_nodes + pathNodes acc := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · have := ihl (acc := { dir := .L, key := k, sibling := r } :: acc)
      simp [Frame.nodes] at this ⊢
      omega
    · have := ihr (acc := { dir := .R, key := k, sibling := l } :: acc)
      simp [Frame.nodes] at this ⊢
      omega

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
      simp at hd
      simp [hd]
  | (.empty, f :: rest) =>
      rw [h] at hd
      simp only [num_nodes_splayUp, num_nodes_Frame_attach,
        BinaryTree.num_nodes_empty, pathNodes_cons] at hd ⊢
      omega
  | (.node l k r, path) =>
      rw [h] at hd
      simp only [num_nodes_splayUp]
      omega


-- =========================================================================
-- §4  `descend` characterisations
-- =========================================================================

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
-- §5  Cost and search-path length
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
    splayBU.cost t q = ((descend t q).2.length : ℝ) := rfl

theorem splayBU_cost_nonneg (t : BinaryTree) (q : ℕ) :
    0 ≤ splayBU.cost t q := by
  unfold splayBU.cost; exact Nat.cast_nonneg _


-- =========================================================================
-- §6  `toKeyList` preservation
-- =========================================================================


open BinaryTree (toKeyList)

@[simp, grind =] theorem toKeyList_rotateRight (t : BinaryTree) :
    (rotateRight t).toKeyList = t.toKeyList := by
  unfold rotateRight
  cases t with
  | empty => rfl
  | node l k r =>
    cases l with
    | empty => rfl
    | node ll lk lr => simp [toKeyList]
@[simp, grind =] theorem toKeyList_rotateLeft (t : BinaryTree) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  unfold rotateLeft
  cases t with
  | empty => rfl
  | node l k r =>
    cases r with
    | empty => rfl
    | node rl rk rr => simp [toKeyList]

@[simp, grind =] theorem toKeyList_bringUp (d : Dir) (t : BinaryTree) :
    (d.bringUp t).toKeyList = t.toKeyList := by
  cases d <;> simp [Dir.bringUp]

@[simp, grind =] theorem toKeyList_applyChild (d : Dir) (op : BinaryTree → BinaryTree)
    (hop : ∀ s, (op s).toKeyList = s.toKeyList) (t : BinaryTree) :
    (applyChild d op t).toKeyList = t.toKeyList := by
  cases t with
  | empty => rfl
  | node l k r => cases d <;> simp [applyChild, toKeyList, hop]

@[simp, grind =]
theorem toKeyList_applyChild_bringUp (d₁ d₂ : Dir) (t : BinaryTree) :
    (applyChild d₁ d₂.bringUp t).toKeyList = t.toKeyList :=
  toKeyList_applyChild _ _ (toKeyList_bringUp _) _

@[simp, grind =] theorem toKeyList_Frame_attach (c : BinaryTree) (f : Frame) :
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

@[simp, grind =]
theorem toKeyList_splayUp (c : BinaryTree) (path : List Frame) :
    (splayUp c path).toKeyList = (reassemble c path).toKeyList := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp [splayUp, reassemble]
  | step c f1 f2 rest ih =>
    unfold splayUp
    split_ifs with h
    · rw [ih]; apply reassemble_toKeyList_congr; simp
    · rw [ih]; apply reassemble_toKeyList_congr; simp

@[simp, grind =]
theorem toKeyList_splayBU (t : BinaryTree) (q : ℕ) :
    (splayBU t q).toKeyList = t.toKeyList := by
  unfold splayBU
  have hpres := descend_preserves_tree t q
  match h : descend t q with
  | (.empty, []) =>
      rw [h] at hpres
      simp at hpres
      simp [← hpres]
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
    | node l k r => simp at hn; omega
  · rintro rfl
    simp [splayBU, descend, descend.go]


-- =========================================================================
-- §7  BST preservation
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

/-- Transfer BST-ness between trees with the same in-order traversal. -/
lemma IsBST_of_toKeyList_eq {t t' : BinaryTree}
    (h : t'.toKeyList = t.toKeyList) (hbst : IsBST t) : IsBST t' := by
  rw [IsBST_iff_toKeyList_sorted] at hbst ⊢; rwa [h]

/-- Bottom-up splay preserves the BST invariant. -/
theorem IsBST_splayBU (t : BinaryTree) (q : ℕ) (h : IsBST t) :
    IsBST (splayBU t q) :=
  IsBST_of_toKeyList_eq (toKeyList_splayBU t q) h

/-- Each primitive rotation preserves the BST invariant. -/
theorem IsBST_bringUp (d : Dir) (t : BinaryTree) (h : IsBST t) :
    IsBST (d.bringUp t) :=
  IsBST_of_toKeyList_eq (toKeyList_bringUp d t) h

theorem IsBST_applyChild (d : Dir) (op : BinaryTree → BinaryTree)
    (hop_keys : ∀ s, (op s).toKeyList = s.toKeyList)
    (t : BinaryTree) (h : IsBST t) :
    IsBST (applyChild d op t) :=
  IsBST_of_toKeyList_eq (toKeyList_applyChild d op hop_keys t) h

/-- Any frame-wise splay-up preserves BST-ness of the reassembled tree. -/
theorem IsBST_splayUp (c : BinaryTree) (path : List Frame)
    (h : IsBST (reassemble c path)) : IsBST (splayUp c path) :=
  IsBST_of_toKeyList_eq (toKeyList_splayUp c path) h


-- =========================================================================
-- §8  Root of `splayBU` on a contained key
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



-- =========================================================================
-- §9  Amortized complexity (potential method)
-- =========================================================================
-- We follow Sleator–Tarjan's potential method.  The rank of a tree is
-- `log₂(num_nodes)`, the potential `φ` is the sum of ranks over all
-- subtrees.  Each splay step (zig, zig-zig, zig-zag) satisfies a
-- per-step potential inequality, and these telescope along the frame
-- path to give the O(log n) amortized bound.

noncomputable section

/-- Rank of a tree: `log₂(num_nodes)`, or 0 for the empty tree. -/
def rank (t : BinaryTree) : ℝ :=
  if t.num_nodes = 0 then 0 else Real.logb 2 t.num_nodes

/-- Potential of a tree: sum of ranks over all subtrees (including itself). -/
def φ : BinaryTree → ℝ
  | .empty => 0
  | s@(.node l _ r) => rank s + φ l + φ r

-- -------------------------------------------------------------------------
--  Basic rank / potential lemmas
-- -------------------------------------------------------------------------

@[simp] lemma rank_empty : rank .empty = 0 := by simp [rank]

lemma rank_nonneg (t : BinaryTree) : 0 ≤ rank t := by
  simp only [rank]; split_ifs with h
  · rfl
  · exact Real.logb_nonneg (by grind)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

@[simp] lemma φ_empty : φ .empty = 0 := rfl

@[simp] lemma φ_node (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    φ (.node l k r) = rank (.node l k r) + φ l + φ r := rfl

lemma φ_nonneg : ∀ t : BinaryTree, 0 ≤ φ t
  | .empty => le_refl _
  | .node l k r => by
      simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg l, φ_nonneg r]

lemma rank_le_of_num_nodes_le {s t : BinaryTree}
    (h : s.num_nodes ≤ t.num_nodes) : rank s ≤ rank t := by
  simp only [rank]
  split_ifs with hs ht ht
  · exact le_refl _
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht)
  · omega
  · apply Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs)
      (by simp_all only [Nat.cast_le])

lemma rank_eq_of_num_nodes_eq {s t : BinaryTree}
    (h : s.num_nodes = t.num_nodes) : rank s = rank t := by
  exact le_antisymm (rank_le_of_num_nodes_le (le_of_eq h))
    (rank_le_of_num_nodes_le (le_of_eq h.symm))

@[simp] lemma rank_splayBU (t : BinaryTree) (q : ℕ) :
    rank (splayBU t q) = rank t :=
  rank_eq_of_num_nodes_eq (num_nodes_splayBU t q)

-- -------------------------------------------------------------------------
--  The key logarithmic inequality (AM-GM for logs)
-- -------------------------------------------------------------------------
-- Proof follows Basic.lean.

theorem log_sum_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 := by
  have h1 : Real.logb 2 a = Real.log a / Real.log (2 : ℝ) := rfl
  have h2 : Real.logb 2 b = Real.log b / Real.log (2 : ℝ) := rfl
  have h3 : Real.logb 2 c = Real.log c / Real.log (2 : ℝ) := rfl
  rw [h1, h2, h3]
  have h5 : Real.log (2 : ℝ) > 0 := by apply Real.log_pos; linarith
  have h6 : Real.log a + Real.log b ≤ 2 * Real.log c - 2 * Real.log (2 : ℝ) := by
    have h8 : a * b ≤ (c ^ 2) / 4 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c),
        mul_pos ha hb, sq_nonneg (c - (a + b)),
        mul_nonneg (show 0 ≤ c - (a + b) by nlinarith) (show 0 ≤ (a + b) by nlinarith)]
    have h9 : Real.log a + Real.log b = Real.log (a * b) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have hc_pos : c > 0 := by nlinarith
    have h10 : 2 * Real.log c - 2 * Real.log (2 : ℝ) = Real.log (c ^ 2 / 4) := by
      have h11 : Real.log (c ^ 2 / 4) = Real.log (c ^ 2) - Real.log (4 : ℝ) :=
        Real.log_div (by positivity) (by positivity)
      rw [h11, Real.log_pow,
        show Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) from by
          calc Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
            _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]]
      simp_all only [gt_iff_lt, Real.log_pow, Nat.cast_ofNat]
    have h14 : Real.log (a * b) ≤ Real.log (c ^ 2 / 4) := by
      apply Real.log_le_log (by positivity); linarith
    nlinarith [h9, h10, h14]
  have h11 : Real.log a / Real.log (2 : ℝ) + Real.log b / Real.log (2 : ℝ) =
      (Real.log a + Real.log b) / Real.log (2 : ℝ) := by ring_nf
  have h12 : 2 * (Real.log c / Real.log (2 : ℝ)) - 2 =
      (2 * Real.log c - 2 * Real.log (2 : ℝ)) / Real.log (2 : ℝ) := by
    field_simp;
  rw [h11, h12]
  exact (div_le_div_iff_of_pos_right h5).mpr h6

-- -------------------------------------------------------------------------
--  Potential of subtrees versus the whole tree
-- -------------------------------------------------------------------------

theorem φ_subtree_le_left (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    φ l ≤ φ (.node l k r) := by
  simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg r]

theorem φ_subtree_le_right (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    φ r ≤ φ (.node l k r) := by
  simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg l]

theorem φ_le_attach (c : BinaryTree) (f : Frame) : φ c ≤ φ (f.attach c) := by
  cases f.dir <;> simp [Frame.attach, φ] <;>
  split
  next x heq =>
    simp_all only [φ_node]
    sorry
  next x heq =>
    simp_all only [φ_node, le_add_iff_nonneg_left]
    sorry

theorem φ_le_reassemble (c : BinaryTree) (path : List Frame) :
    φ c ≤ φ (reassemble c path) := by
  induction path generalizing c with
  | nil => simp
  | cons f rest ih => simp only [reassemble_cons]; exact le_trans (φ_le_attach c f) (ih _)

theorem reassemble_descend_eq (t : BinaryTree) (q : ℕ) :
    reassemble (descend t q).1 (descend t q).2 = t := by
  suffices ∀ acc, reassemble (descend.go q t acc).1 (descend.go q t acc).2 =
      reassemble t acc from by
    have := this []; simp only [reassemble_nil] at this; exact this
  intro acc
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go; split_ifs with h1 h2
    · rfl
    · simp_all only [reassemble_cons]
      rfl
    · simp_all only [not_lt, reassemble_cons]
      rfl

theorem φ_descend_subtree_le (t : BinaryTree) (q : ℕ) :
    φ (descend t q).1 ≤ φ t := by
  have h := reassemble_descend_eq t q
  calc φ (descend t q).1
      ≤ φ (reassemble (descend t q).1 (descend t q).2) :=
        φ_le_reassemble _ _
    _ = φ t := by rw [h]

theorem φ_attach_base_le (t : BinaryTree) (q : ℕ) (f : Frame) (rest : List Frame)
    (hd : descend t q = (.empty, f :: rest)) :
    φ (f.attach .empty) ≤ φ t := by
  have h := reassemble_descend_eq t q
  rw [hd] at h; simp only at h; rw [← h]
  exact φ_le_reassemble (f.attach .empty) rest

theorem φ_descend_node_le (t : BinaryTree) (q : ℕ) (l : BinaryTree) (k : ℕ)
    (r : BinaryTree) (path : List Frame) (hd : descend t q = (.node l k r, path)) :
    φ (.node l k r) ≤ φ t := by
  have h := reassemble_descend_eq t q
  rw [hd] at h; simp_all only [φ_node, ge_iff_le]; rw [← h]
  exact φ_le_reassemble (.node l k r) path

-- -------------------------------------------------------------------------
--  Per-step potential bounds
-- -------------------------------------------------------------------------
-- Each splay step transforms a subtree c (the node being splayed) into a
-- larger tree that includes the frame nodes.
-- The key invariant: φ(step result) − φ(c) + cost ≤ 3·(rank(result) − rank(c)).
-- For a zig (single frame):    cost = 1, bound = 3·Δrank  (no −2 needed)
-- For zig-zig (same dir pair):  cost = 2, bound = 3·Δrank  (log_sum_le gives −2)
-- For zig-zag (opp dir pair):   cost = 2, bound = 3·Δrank  (log_sum_le gives −2)

/-- Zig step. -/
theorem φ_zig (c : BinaryTree) (f : Frame) :
    φ (f.dir.bringUp (f.attach c)) - φ c ≤
      3 * (rank (f.dir.bringUp (f.attach c)) - rank c) := by
  cases hd : f.dir <;> simp only [hd, Dir.bringUp, Frame.attach]
  · -- L: rotateRight (.node c f.key f.sibling)
    unfold rotateRight; cases c with
    | empty =>
      simp [φ, rank]
      linarith [rank_nonneg (BinaryTree.node .empty f.key f.sibling)]
    | node A x B =>
      simp only [φ_node, φ_empty]
      have hrs : rank (BinaryTree.node A x (BinaryTree.node B f.key f.sibling)) =
          rank (BinaryTree.node (BinaryTree.node A x B) f.key f.sibling) :=
        rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)
      have h1 : rank (BinaryTree.node B f.key f.sibling) ≤
          rank (BinaryTree.node A x (BinaryTree.node B f.key f.sibling)) :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h2 : rank (BinaryTree.node A x B) ≤
          rank (BinaryTree.node A x (BinaryTree.node B f.key f.sibling)) :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      linarith
  · -- R: rotateLeft (.node f.sibling f.key c)
    unfold rotateLeft; cases c with
    | empty =>
      simp [φ, rank]
      linarith [rank_nonneg (BinaryTree.node f.sibling f.key .empty)]
    | node A x B =>
      simp only [φ_node, φ_empty]
      have hrs : rank (BinaryTree.node (BinaryTree.node f.sibling f.key A) x B) =
          rank (BinaryTree.node f.sibling f.key (BinaryTree.node A x B)) :=
        rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)
      have h1 : rank (BinaryTree.node f.sibling f.key A) ≤
          rank (BinaryTree.node (BinaryTree.node f.sibling f.key A) x B) :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h2 : rank (BinaryTree.node A x B) ≤
          rank (BinaryTree.node (BinaryTree.node f.sibling f.key A) x B) :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      linarith

/-- Zig-zig step (same-direction double rotation). -/
theorem φ_zigzig (c : BinaryTree) (f1 f2 : Frame) (heq : f1.dir = f2.dir) :
    let step := f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))
    φ step - φ c + 2 ≤ 3 * (rank step - rank c) := by
  intro step
  cases hd : f2.dir <;> (have hd1 : f1.dir = _ := by rw [heq, hd]; rfl)
  all_goals simp only [hd, hd1, Dir.bringUp, Frame.attach] at step ⊢
  · -- Both L: step = rotateRight (rotateRight (.node (.node c f1.key f1.sibling) f2.key f2.sibling))
    -- First rotation gives: .node c f1.key (.node f1.sibling f2.key f2.sibling)
    -- Then case split on c for second rotation
    cases c with
    | empty =>
      simp [rotateRight, φ, rank]
      linarith [rank_nonneg (BinaryTree.node f1.sibling f2.key f2.sibling),
                rank_nonneg (BinaryTree.node .empty f1.key
                  (BinaryTree.node f1.sibling f2.key f2.sibling))]
    | node A x B =>
      -- first rot: rotateRight (.node (.node (.node A x B) f1.key f1.sibling) f2.key f2.sibling)
      --   = .node (.node A x B) f1.key (.node f1.sibling f2.key f2.sibling)
      -- second rot: rotateRight (.node (.node A x B) f1.key (.node f1.sibling f2.key f2.sibling))
      --   = .node A x (.node B f1.key (.node f1.sibling f2.key f2.sibling))
      -- We need to show these unfold correctly
      change φ (rotateRight (rotateRight (BinaryTree.node
        (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling) f2.key f2.sibling)))
        - φ (BinaryTree.node A x B) + 2 ≤
        3 * (rank (rotateRight (rotateRight (BinaryTree.node
        (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling) f2.key f2.sibling)))
        - rank (BinaryTree.node A x B))
      -- Unfold both rotations
      have hrot : rotateRight (rotateRight (BinaryTree.node
          (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling)
          f2.key f2.sibling)) =
          BinaryTree.node A x (BinaryTree.node B f1.key
          (BinaryTree.node f1.sibling f2.key f2.sibling)) := by
        unfold rotateRight; rfl
      rw [hrot]; clear hrot
      simp only [φ_node, φ_empty]
      -- Named rank variables (following Basic.lean's style)
      set rx  := rank (BinaryTree.node A x B) with hrx_def
      set r'x := rank (BinaryTree.node A x (BinaryTree.node B f1.key
          (BinaryTree.node f1.sibling f2.key f2.sibling))) with hr'x_def
      set r'p := rank (BinaryTree.node B f1.key
          (BinaryTree.node f1.sibling f2.key f2.sibling)) with hr'p_def
      set r'g := rank (BinaryTree.node f1.sibling f2.key f2.sibling) with hr'g_def
      set rp  := rank (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling) with hrp_def
      -- Key AM-GM inequality
      have hlog : rx + r'g ≤ 2 * r'x - 2 := by
        simp only [hrx_def, hr'g_def, hr'x_def, rank, BinaryTree.num_nodes]
        apply log_sum_le <;> (simp [BinaryTree.num_nodes]; omega)
      -- Monotonicity bounds
      have h_r'p : r'p ≤ r'x :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rx_rp : rx ≤ rp :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rp : rp ≤ r'x := by
        calc rp ≤ rank (BinaryTree.node (BinaryTree.node (BinaryTree.node A x B) f1.key
            f1.sibling) f2.key f2.sibling) :=
              rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
          _ = r'x := (rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)).symm
      -- Goal: (r'x + r'p + r'g) − rx + 2 ≤ 3*(r'x − rx)
      -- i.e. r'p + r'g + 2 ≤ 2*r'x
      -- From hlog: rx + r'g ≤ 2*r'x − 2, so r'g ≤ 2*r'x − rx − 2
      -- Also r'p − rp ≤ r'x − rx (from monotonicity)
      nlinarith
  · -- Both R: symmetric
    cases c with
    | empty =>
      simp [rotateLeft, φ, rank]
      linarith [rank_nonneg (BinaryTree.node f2.sibling f2.key f1.sibling),
                rank_nonneg (BinaryTree.node
                  (BinaryTree.node f2.sibling f2.key f1.sibling) f1.key .empty)]
    | node A x B =>
      have hrot : rotateLeft (rotateLeft (BinaryTree.node f2.sibling f2.key
          (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B)))) =
          BinaryTree.node (BinaryTree.node
          (BinaryTree.node f2.sibling f2.key f1.sibling) f1.key A) x B := by
        unfold rotateLeft; rfl
      change φ (rotateLeft (rotateLeft (BinaryTree.node f2.sibling f2.key
          (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B)))))
          - φ (BinaryTree.node A x B) + 2 ≤
          3 * (rank (rotateLeft (rotateLeft (BinaryTree.node f2.sibling f2.key
          (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B)))))
          - rank (BinaryTree.node A x B))
      rw [hrot]; clear hrot
      simp only [φ_node, φ_empty]
      set rx  := rank (BinaryTree.node A x B)
      set r'x := rank (BinaryTree.node (BinaryTree.node
          (BinaryTree.node f2.sibling f2.key f1.sibling) f1.key A) x B)
      set r'p := rank (BinaryTree.node
          (BinaryTree.node f2.sibling f2.key f1.sibling) f1.key A)
      set r'g := rank (BinaryTree.node f2.sibling f2.key f1.sibling)
      set rp  := rank (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B))
      have hlog : rx + r'g ≤ 2 * r'x - 2 := by
        simp only [rx, r'g, r'x, rank, BinaryTree.num_nodes]
        apply log_sum_le <;> (simp [BinaryTree.num_nodes]; omega)
      have h_r'p : r'p ≤ r'x :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rx_rp : rx ≤ rp :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rp : rp ≤ r'x := by
        calc rp ≤ rank (BinaryTree.node f2.sibling f2.key (BinaryTree.node f1.sibling f1.key
            (BinaryTree.node A x B))) :=
              rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
          _ = r'x := (rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)).symm
      nlinarith

/-- Zig-zag step (opposite-direction double rotation). -/
theorem φ_zigzag (c : BinaryTree) (f1 f2 : Frame) (hne : f1.dir ≠ f2.dir) :
    let step := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp (f2.attach (f1.attach c)))
    φ step - φ c + 2 ≤ 3 * (rank step - rank c) := by
  intro step
  cases hd2 : f2.dir
  · -- f2 = L, so f1 = R
    have hd1 : f1.dir = .R := by cases f1.dir with | L => simp [hd2] at hne | R => rfl
    simp only [hd2, hd1, Dir.bringUp, Frame.attach, applyChild] at step ⊢
    -- step = rotateRight (.node (rotateLeft (.node f1.sibling f1.key c)) f2.key f2.sibling)
    cases c with
    | empty =>
      simp [rotateLeft, rotateRight, φ, rank]
      linarith [rank_nonneg (BinaryTree.node f1.sibling f1.key .empty),
                rank_nonneg (BinaryTree.node
                  (BinaryTree.node f1.sibling f1.key .empty) f2.key f2.sibling)]
    | node A x B =>
      -- rotateLeft (.node f1.sibling f1.key (.node A x B))
      --   = .node (.node f1.sibling f1.key A) x B
      -- So the inner tree becomes: .node (.node (.node f1.sibling f1.key A) x B) f2.key f2.sibling
      -- rotateRight of that = .node (.node f1.sibling f1.key A) x (.node B f2.key f2.sibling)
      have hstep : rotateRight (BinaryTree.node (rotateLeft
          (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B)))
          f2.key f2.sibling) =
          BinaryTree.node (BinaryTree.node f1.sibling f1.key A) x
          (BinaryTree.node B f2.key f2.sibling) := by
        unfold rotateLeft rotateRight; rfl
      change φ (rotateRight (BinaryTree.node (rotateLeft (BinaryTree.node f1.sibling
          f1.key (BinaryTree.node A x B))) f2.key f2.sibling))
          - φ (BinaryTree.node A x B) + 2 ≤
          3 * (rank (rotateRight (BinaryTree.node (rotateLeft (BinaryTree.node
          f1.sibling f1.key (BinaryTree.node A x B))) f2.key f2.sibling))
          - rank (BinaryTree.node A x B))
      rw [hstep]; clear hstep
      simp only [φ_node, φ_empty]
      set rx  := rank (BinaryTree.node A x B)
      set r'x := rank (BinaryTree.node (BinaryTree.node f1.sibling f1.key A) x
          (BinaryTree.node B f2.key f2.sibling))
      set r'l := rank (BinaryTree.node f1.sibling f1.key A)
      set r'r := rank (BinaryTree.node B f2.key f2.sibling)
      set rp  := rank (BinaryTree.node f1.sibling f1.key (BinaryTree.node A x B))
      have hlog : r'l + r'r ≤ 2 * r'x - 2 := by
        simp only [r'l, r'r, r'x, rank, BinaryTree.num_nodes]
        apply log_sum_le <;> (simp [BinaryTree.num_nodes]; omega)
      have h_rx : rx ≤ r'x :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rx_rp : rx ≤ rp :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rp : rp ≤ r'x := by
        calc rp ≤ rank (BinaryTree.node (BinaryTree.node f1.sibling f1.key
            (BinaryTree.node A x B)) f2.key f2.sibling) :=
              rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
          _ = r'x := (rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)).symm
      nlinarith
  · -- f2 = R, so f1 = L
    have hd1 : f1.dir = .L := by cases f1.dir with | R => simp [hd2] at hne | L => rfl
    simp only [hd2, hd1, Dir.bringUp, Frame.attach, applyChild] at step ⊢
    cases c with
    | empty =>
      simp [rotateRight, rotateLeft, φ, rank]
      linarith [rank_nonneg (BinaryTree.node .empty f1.key f1.sibling),
                rank_nonneg (BinaryTree.node f2.sibling f2.key
                  (BinaryTree.node .empty f1.key f1.sibling))]
    | node A x B =>
      have hstep : rotateLeft (BinaryTree.node f2.sibling f2.key (rotateRight
          (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling))) =
          BinaryTree.node (BinaryTree.node f2.sibling f2.key A) x
          (BinaryTree.node B f1.key f1.sibling) := by
        unfold rotateRight rotateLeft; rfl
      change φ (rotateLeft (BinaryTree.node f2.sibling f2.key (rotateRight
          (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling))))
          - φ (BinaryTree.node A x B) + 2 ≤
          3 * (rank (rotateLeft (BinaryTree.node f2.sibling f2.key (rotateRight
          (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling))))
          - rank (BinaryTree.node A x B))
      rw [hstep]; clear hstep
      simp only [φ_node, φ_empty]
      set rx  := rank (BinaryTree.node A x B)
      set r'x := rank (BinaryTree.node (BinaryTree.node f2.sibling f2.key A) x
          (BinaryTree.node B f1.key f1.sibling))
      set r'l := rank (BinaryTree.node f2.sibling f2.key A)
      set r'r := rank (BinaryTree.node B f1.key f1.sibling)
      set rp  := rank (BinaryTree.node (BinaryTree.node A x B) f1.key f1.sibling)
      have hlog : r'l + r'r ≤ 2 * r'x - 2 := by
        simp only [r'l, r'r, r'x, rank, BinaryTree.num_nodes]
        apply log_sum_le <;> (simp [BinaryTree.num_nodes]; omega)
      have h_rx : rx ≤ r'x :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rx_rp : rx ≤ rp :=
        rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
      have h_rp : rp ≤ r'x := by
        calc rp ≤ rank (BinaryTree.node f2.sibling f2.key (BinaryTree.node
            (BinaryTree.node A x B) f1.key f1.sibling)) :=
              rank_le_of_num_nodes_le (by simp [BinaryTree.num_nodes]; omega)
          _ = r'x := (rank_eq_of_num_nodes_eq (by simp [BinaryTree.num_nodes]; omega)).symm
      nlinarith

-- -------------------------------------------------------------------------
--  Telescoping: potential change along the full splayUp
-- -------------------------------------------------------------------------

theorem φ_splayUp (c : BinaryTree) (path : List Frame) :
    φ (splayUp c path) - φ c + path.length ≤
      3 * (rank (splayUp c path) - rank c) + 1 := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp only [splayUp_singleton, List.length_singleton, Nat.cast_one]
    linarith [φ_zig c f]
  | step c f1 f2 rest ih =>
    rw [splayUp_cons_cons]
    simp only [List.length_cons]
    split_ifs with hdir
    · -- same direction (zig-zig)
      set s := f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))
      have hstep := φ_zigzig c f1 f2 hdir
      specialize ih s
      push_cast; nlinarith
    · -- opposite direction (zig-zag)
      set s := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp
          (f2.attach (f1.attach c)))
      have hstep := φ_zigzag c f1 f2 hdir
      specialize ih s
      push_cast; nlinarith

-- -------------------------------------------------------------------------
--  The main amortized bound
-- -------------------------------------------------------------------------

theorem splayBU_amortized_bound (t : BinaryTree) (q : ℕ) :
    φ (splayBU t q) - φ t + splayBU.cost t q ≤
      3 * Real.logb 2 t.num_nodes + 1 := by
  unfold splayBU.cost splayBU
  match hd : descend t q with
  | (.empty, []) =>
    have ht : t = .empty := by
      have := num_nodes_descend t q; rw [hd] at this; simp at this
      cases t with | empty => rfl | node l k r => simp at this; omega
    subst ht; simp [φ]
  | (.empty, f :: rest) =>
    have hplen : (descend t q).2.length = (f :: rest).length := by rw [hd]
    simp only
    set base := f.attach BinaryTree.empty
    have hsize : (splayUp base rest).num_nodes = t.num_nodes := by
      have h1 := num_nodes_descend t q; rw [hd] at h1
      simp [Frame.nodes, base, num_nodes_Frame_attach] at h1 ⊢; omega
    have hφ_base_le : φ base ≤ φ t := φ_attach_base_le t q f rest hd
    have htel := φ_splayUp base rest
    calc φ (splayUp base rest) - φ t + ↑(List.length (f :: rest))
        = (φ (splayUp base rest) - φ base + ↑rest.length) +
          (φ base - φ t) + 1 := by push_cast; ring
      _ ≤ (3 * (rank (splayUp base rest) - rank base) + 1) +
          (φ base - φ t) + 1 := by linarith
      _ ≤ 3 * rank (splayUp base rest) + 1 := by
          linarith [rank_nonneg base]
      _ ≤ 3 * rank t + 1 := by
          linarith [rank_le_of_num_nodes_le (le_of_eq hsize)]
      _ ≤ 3 * Real.logb 2 ↑t.num_nodes + 1 := by
          simp only [rank]; split_ifs with hn <;> linarith [φ_nonneg (splayUp base rest)]
  | (.node l k r, path) =>
    have hplen : (descend t q).2.length = path.length := by rw [hd]
    simp only [hplen]
    have hsize : (splayUp (.node l k r) path).num_nodes = t.num_nodes := by
      have h1 := num_nodes_descend t q; rw [hd] at h1; simp at h1; omega
    have hφ_sub_le : φ (.node l k r) ≤ φ t := φ_descend_node_le t q l k r path hd
    have htel := φ_splayUp (.node l k r) path
    calc φ (splayUp (.node l k r) path) - φ t + ↑path.length
        = (φ (splayUp (.node l k r) path) - φ (.node l k r) + ↑path.length) +
          (φ (.node l k r) - φ t) := by ring
      _ ≤ (3 * (rank (splayUp (.node l k r) path) - rank (.node l k r)) + 1) +
          (φ (.node l k r) - φ t) := by linarith
      _ ≤ 3 * rank (splayUp (.node l k r) path) + 1 := by
          linarith [rank_nonneg (.node l k r)]
      _ ≤ 3 * rank t + 1 := by
          linarith [rank_le_of_num_nodes_le (le_of_eq hsize)]
      _ ≤ 3 * Real.logb 2 ↑t.num_nodes + 1 := by
          simp only [rank]; split_ifs with hn <;>
            linarith [φ_nonneg (splayUp (.node l k r) path)]

end
