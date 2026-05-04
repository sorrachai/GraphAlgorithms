/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche, Sorrachai Yingchareonthawornchai
-/


import GraphAlgorithms.DataStructures.SplayTrees.BinaryTree
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

variable {α : Type}


-- =========================================================================
-- §1  Definitions
-- =========================================================================
-- Rotation primitives, direction / frame types, descend, splayUp, splayBU.


def rotateRight : BinaryTree α → BinaryTree α
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : BinaryTree α → BinaryTree α
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t


inductive Dir
  | L -- target descended into the left subtree from this parent
  | R -- target descended into the right subtree from this parent
  deriving DecidableEq, Repr

/-- Flip a direction: `L ↔ R`. -/
def Dir.flip : Dir → Dir
  | .L => .R
  | .R => .L

@[simp] lemma Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl
@[simp] lemma Dir.flip_ne (d : Dir) : d.flip ≠ d := by cases d <;> simp [flip]
@[simp] lemma Dir.ne_flip (d : Dir) : d ≠ d.flip := by cases d <;> simp [flip]

/-- Single primitive rotation that brings the `d`-child of the root up one
level. `L` ↦ `rotateRight`, `R` ↦ `rotateLeft`. -/
def Dir.bringUp : Dir → BinaryTree α → BinaryTree α
  | .L => rotateRight
  | .R => rotateLeft

/-- Apply `op` to the `d`-child of the root, leaving everything else fixed. -/
def applyChild (d : Dir) (op : BinaryTree α → BinaryTree α) : BinaryTree α → BinaryTree α
  | .node l k r =>
    match d with
    | .L => .node (op l) k r
    | .R => .node l k (op r)
  | .empty => .empty

/-- One frame of the search path: the direction we took from this ancestor,
its key, and the subtree we did *not* descend into. -/
structure Frame α where
  dir : Dir
  key : α
  sibling : BinaryTree α

/-- Re-attach a subtree `c` below the ancestor described by `f`. -/
def Frame.attach (c : BinaryTree α) (f : Frame α) : BinaryTree α :=
  match f.dir with
  | .L => .node c f.key f.sibling
  | .R => .node f.sibling f.key c

-- -------------------------------------------------------------------------
-- Mirror symmetry
-- ------------------------------------------------------------------------
/-
L–L / R–R (resp. L–R / R–L) splay steps are related by mirroring.
We define `BinaryTree.mirror` and `Frame.flip`, and prove the
commutativity lemmas needed to reduce one direction case to the other.
-/

/-- Mirror a binary tree: swap every left and right subtree. -/
def BinaryTree.mirror : BinaryTree α → BinaryTree α
  | .empty => .empty
  | .node l k r => .node r.mirror k l.mirror

@[simp] lemma BinaryTree.mirror_empty :
    (BinaryTree.empty : BinaryTree α).mirror = .empty := rfl
@[simp] lemma BinaryTree.mirror_node (l : BinaryTree α) (k : α)
    (r : BinaryTree α) :
    (BinaryTree.node l k r).mirror = .node r.mirror k l.mirror :=
  rfl
@[simp] lemma BinaryTree.mirror_mirror (t : BinaryTree α) :
    t.mirror.mirror = t := by induction t <;> simp_all

@[simp] lemma BinaryTree.num_nodes_mirror (t : BinaryTree α) :
    t.mirror.num_nodes = t.num_nodes := by
  induction t <;> simp_all [BinaryTree.num_nodes]; omega

@[simp] lemma mirror_rotateRight (t : BinaryTree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  rcases t with _ | ⟨l, k, r⟩ <;> simp only [rotateRight, BinaryTree.mirror_empty, rotateLeft]
  rcases l with _ | ⟨ll, lk, lr⟩ <;> simp only [BinaryTree.mirror_node, BinaryTree.mirror_empty]

@[simp] lemma mirror_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  rcases t with _ | ⟨l, k, r⟩ <;> simp only [rotateLeft, BinaryTree.mirror_empty, rotateRight]
  rcases r with _ | ⟨rl, rk, rr⟩ <;> simp only [BinaryTree.mirror_node, BinaryTree.mirror_empty]

@[simp] lemma mirror_bringUp (d : Dir) (t : BinaryTree α) :
    (d.bringUp t).mirror = d.flip.bringUp t.mirror := by
  cases d <;> simp [Dir.bringUp, Dir.flip]

/-- Flip a frame: reverse the direction and mirror the sibling. -/
def Frame.flip (f : Frame α) : Frame α :=
  { dir := f.dir.flip, key := f.key, sibling := f.sibling.mirror }

@[simp] lemma mirror_attach (c : BinaryTree α) (f : Frame α) :
    (f.attach c).mirror = f.flip.attach c.mirror := by
  cases f with | mk d k s =>
    cases d <;> simp [Frame.attach, Frame.flip, Dir.flip]

@[simp] lemma mirror_applyChild_bringUp (d₁ d₂ : Dir)
    (t : BinaryTree α) :
    (applyChild d₁ d₂.bringUp t).mirror =
      applyChild d₁.flip d₂.flip.bringUp t.mirror := by
  rcases t with _ | ⟨l, k, r⟩
  · cases d₁ <;> cases d₂ <;> simp [applyChild]
  · cases d₁ <;> cases d₂ <;>
      simp only [applyChild, Dir.flip, Dir.bringUp,
        BinaryTree.mirror_node] <;> congr 1 <;>
      first | exact mirror_rotateRight _ | exact mirror_rotateLeft _

/-- Descend from `t` toward `q`, returning the subtree reached (either the
matching node or `.empty` if `q` is absent) and the path above it. The head
of the returned list is the deepest frame (parent of the returned subtree). -/
def descend [LinearOrder α] (t : BinaryTree α) (q : α) : BinaryTree α × List (Frame α) :=
  go t []
where
  go : BinaryTree α → List (Frame α) → BinaryTree α × List (Frame α)
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
def splayUp : BinaryTree α → List (Frame α) → BinaryTree α
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
def splayBU [LinearOrder α] (t : BinaryTree α) (q : α) : BinaryTree α :=
  match descend t q with
  | (.empty, []) => .empty
  | (.empty, f :: rest) => splayUp (f.attach .empty) rest
  | (x@(.node _ _ _), path) => splayUp x path

/-- Cost of a bottom-up splay: one unit per rotation, i.e. the length of the
search path. -/
def splayBU.cost [LinearOrder α] (t : BinaryTree α) (q : α) : ℝ :=
  (descend t q).2.length

/-- Reassemble a subtree `c` with its ancestral path `path` (deepest frame
first) back into the original tree. -/
def reassemble (c : BinaryTree α) (path : List (Frame α)) : BinaryTree α :=
  path.foldl (fun c' f => f.attach c') c

@[simp] lemma reassemble_nil (c : BinaryTree α) : reassemble c [] = c := rfl

@[simp] lemma reassemble_cons (c : BinaryTree α) (f : Frame α) (rest : List (Frame α)) :
    reassemble c (f :: rest) = reassemble (f.attach c) rest := rfl

/-- Number of nodes a single frame contributes when re-attached: the
ancestor itself plus its sibling subtree. -/
def Frame.nodes (f : Frame α) : ℕ := 1 + f.sibling.num_nodes

/-- Total number of nodes contributed by a path above a subtree. -/
def pathNodes : List (Frame α) → ℕ
  | [] => 0
  | f :: rest => f.nodes + pathNodes rest


-- =========================================================================
-- §2  Unfolding / induction lemmas for `splayUp`
-- =========================================================================


@[simp] theorem splayUp_nil (c : BinaryTree α) : splayUp c [] = c := rfl

@[simp] theorem splayUp_singleton (c : BinaryTree α) (f : Frame α) :
    splayUp c [f] = f.dir.bringUp (f.attach c) := rfl

theorem splayUp_cons_cons (c : BinaryTree α) (f1 f2 : Frame α) (rest : List (Frame α)) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp
        (if f1.dir = f2.dir then
          f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))
        else
          f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp
            (f2.attach (f1.attach c))))
        rest := rfl

theorem splayUp_cons_cons_same (c : BinaryTree α) (f1 f2 : Frame α)
    (rest : List (Frame α)) (h : f1.dir = f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp (f2.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

theorem splayUp_cons_cons_opp (c : BinaryTree α) (f1 f2 : Frame α)
    (rest : List (Frame α)) (h : f1.dir ≠ f2.dir) :
    splayUp c (f1 :: f2 :: rest) =
      splayUp (f2.dir.bringUp
        (applyChild f2.dir f1.dir.bringUp (f2.attach (f1.attach c)))) rest := by
  rw [splayUp_cons_cons]; simp [h]

/-- Two-step induction principle specialised to `splayUp`: base (empty path),
singleton frame, and the general pair-cons step. The tree `c` is
generalised automatically. -/
theorem splayUp_induction
    {motive : BinaryTree α → List (Frame α) → Prop}
    (nil : ∀ c, motive c [])
    (single : ∀ c f, motive c [f])
    (step : ∀ c f1 f2 rest,
      (∀ c', motive c' rest) → motive c (f1 :: f2 :: rest))
    (c : BinaryTree α) (path : List (Frame α)) : motive c path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => exact nil c
  | singleton f => exact single c f
  | cons_cons f1 f2 rest ih _ => exact step c f1 f2 rest (fun c' => ih c')


-- =========================================================================
-- §3  Node-count invariants
-- =========================================================================


@[simp, grind =]
theorem num_nodes_rotateRight (t : BinaryTree α) :
    (rotateRight t).num_nodes = t.num_nodes := by
  rcases t with _ | ⟨(_ | ⟨ll, lk, lr⟩), k, r⟩ <;>
    simp [rotateRight]; omega

@[simp, grind =]
theorem num_nodes_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  have h := num_nodes_rotateRight t.mirror
  simp only [← mirror_rotateLeft, BinaryTree.num_nodes_mirror] at h; exact h


@[simp] lemma pathNodes_nil : pathNodes ([] : List (Frame α)) = 0 := rfl

@[simp] lemma pathNodes_cons (f : Frame α) (rest : List (Frame α)) :
    pathNodes (f :: rest) = f.nodes + pathNodes rest := rfl

@[simp, grind =]
theorem num_nodes_Frame_attach (c : BinaryTree α) (f : Frame α) :
    (f.attach c).num_nodes = c.num_nodes + f.nodes := by
  unfold Frame.attach Frame.nodes
  cases f.dir <;> simp <;> omega

@[simp, grind =]
theorem num_nodes_bringUp (d : Dir) (t : BinaryTree α) :
    (d.bringUp t).num_nodes = t.num_nodes := by
  cases d <;> simp [Dir.bringUp]

@[simp, grind =]
theorem num_nodes_applyChild (d : Dir) (op : BinaryTree α → BinaryTree α)
    (hop : ∀ s, (op s).num_nodes = s.num_nodes) (t : BinaryTree α) :
    (applyChild d op t).num_nodes = t.num_nodes := by
  cases t with
  | empty => rfl
  | node l k r =>
    cases d <;> simp [applyChild, hop]

@[simp, grind =]
theorem num_nodes_applyChild_bringUp (d₁ d₂ : Dir) (t : BinaryTree α) :
    (applyChild d₁ d₂.bringUp t).num_nodes = t.num_nodes :=
  num_nodes_applyChild _ _ (num_nodes_bringUp _) _

@[simp]
theorem num_nodes_splayUp (c : BinaryTree α) (path : List (Frame α)) :
    (splayUp c path).num_nodes = c.num_nodes + pathNodes path := by
  induction path using List.twoStepInduction generalizing c with
  | nil => simp [splayUp]
  | singleton f => simp [splayUp, Frame.nodes, pathNodes]
  | cons_cons f1 f2 rest ih _ =>
    unfold splayUp
    split_ifs with h
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega
    · rw [ih]; simp [Frame.nodes, pathNodes_cons]; omega

theorem num_nodes_descend_go [LinearOrder α] (t : BinaryTree α) (q : α) (acc : List (Frame α)) :
    let r := descend.go q t acc
    r.1.num_nodes + pathNodes r.2 = t.num_nodes + pathNodes acc := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · have := ihl (acc := ⟨.L, k, r⟩ :: acc)
      simp [Frame.nodes] at this ⊢; omega
    · have := ihr (acc := ⟨.R, k, l⟩ :: acc)
      simp [Frame.nodes] at this ⊢; omega

theorem num_nodes_descend [LinearOrder α] (t : BinaryTree α) (q : α) :
    (descend t q).1.num_nodes + pathNodes (descend t q).2 = t.num_nodes := by
  have := num_nodes_descend_go t q []
  simpa [descend] using this

@[simp]
theorem num_nodes_splayBU [LinearOrder α] (t : BinaryTree α) (q : α) :
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


@[simp] lemma descend_empty [LinearOrder α] (q : α) : descend .empty q = (.empty, []) := rfl

lemma descend_go_append [LinearOrder α] (q : α) (t : BinaryTree α) (acc : List (Frame α)) :
    descend.go q t acc =
      ((descend.go q t []).1, (descend.go q t []).2 ++ acc) := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · rw [ihl (acc := ⟨.L, k, r⟩ :: acc),
        ihl (acc := [⟨.L, k, r⟩])]; simp
    · rw [ihr (acc := ⟨.R, k, l⟩ :: acc),
        ihr (acc := [⟨.R, k, l⟩])]; simp

lemma descend_node_eq [LinearOrder α] (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    descend (.node l k r) k = (.node l k r, []) := by
  simp [descend, descend.go]

lemma descend_eq_descend_go [LinearOrder α] (t : BinaryTree α) (q : α) :
    descend t q = descend.go q t [] := rfl

lemma descend_node_lt [LinearOrder α] {l : BinaryTree α} {k : α}
    {r : BinaryTree α} {q : α} (h : q < k) :
    descend (.node l k r) q =
      ((descend l q).1,
       (descend l q).2 ++ [⟨.L, k, r⟩]) := by
  have hne : q ≠ k := ne_of_lt h
  change descend.go q (.node l k r) [] = _
  unfold descend.go
  rw [if_neg hne, if_pos h, descend_go_append q l [⟨.L, k, r⟩]]; rfl

lemma descend_node_gt [LinearOrder α] {l : BinaryTree α} {k : α}
    {r : BinaryTree α} {q : α} (h : k < q) :
    descend (.node l k r) q =
      ((descend r q).1,
       (descend r q).2 ++ [⟨.R, k, l⟩]) := by
  have hne : q ≠ k := ne_of_gt h
  change descend.go q (.node l k r) [] = _
  unfold descend.go
  rw [if_neg hne, if_neg (not_lt.mpr h.le),
      descend_go_append q r [⟨.R, k, l⟩]]; rfl

lemma reassemble_append (c : BinaryTree α) (p1 p2 : List (Frame α)) :
    reassemble c (p1 ++ p2) = reassemble (reassemble c p1) p2 := by
  simp [reassemble, List.foldl_append]

theorem descend_go_preserves_tree [LinearOrder α] (t : BinaryTree α)
  (q : α) (acc : List (Frame α)) :
    reassemble (descend.go q t acc).1 (descend.go q t acc).2 =
      reassemble t acc := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · exact ihl (acc := ⟨.L, k, r⟩ :: acc)
    · exact ihr (acc := ⟨.R, k, l⟩ :: acc)

theorem descend_preserves_tree [LinearOrder α] (t : BinaryTree α) (q : α) :
    reassemble (descend t q).1 (descend t q).2 = t := by
  have := descend_go_preserves_tree t q []
  simpa [descend] using this

lemma descend_go_length_le [LinearOrder α] (q : α) (t : BinaryTree α) (acc : List (Frame α)) :
    acc.length ≤ (descend.go q t acc).2.length := by
  induction t generalizing acc with
  | empty => simp [descend.go]
  | node l k r ihl ihr =>
    unfold descend.go
    split_ifs with h1 h2
    · simp
    · exact le_of_lt (lt_of_lt_of_le (by simp)
        (ihl (acc := ⟨.L, k, r⟩ :: acc)))
    · exact le_of_lt (lt_of_lt_of_le (by simp)
        (ihr (acc := ⟨.R, k, l⟩ :: acc)))


-- =========================================================================
-- §5  Cost and search-path length
-- =========================================================================


/-- Subtrees have positive search path length. -/
lemma search_path_len_node_pos [LinearOrder α] (l : BinaryTree α) (k : α) (r : BinaryTree α)
    (q : α) : 1 ≤ (BinaryTree.node l k r).search_path_len q := by
  unfold BinaryTree.search_path_len
  ; split_ifs <;> omega

/-- Relation between `search_path_len` and the length of the path produced by
`descend`. When `descend` reaches a node, the search path is one link longer;
when it reaches `.empty`, the two are equal. -/
theorem search_path_len_eq_descend_length [LinearOrder α] (t : BinaryTree α) (q : α) :
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
      · have hgt : k < q := by grind only
        rw [descend_node_gt hgt]
        unfold BinaryTree.search_path_len
        simp only [hlt, hgt, if_false, if_true, List.length_append,
          List.length_singleton]
        rw [ihr]; omega

/-- The bottom-up splay cost equals the length of the descended path
(equivalently, the number of rotations performed). -/
theorem splayBU_cost_eq_length [LinearOrder α] (t : BinaryTree α) (q : α) :
    splayBU.cost t q = ((descend t q).2.length : ℝ) := rfl

theorem splayBU_cost_nonneg [LinearOrder α] (t : BinaryTree α) (q : α) :
    0 ≤ splayBU.cost t q := by
  unfold splayBU.cost; exact Nat.cast_nonneg _


-- =========================================================================
-- §6  `toKeyList` preservation
-- =========================================================================


open BinaryTree (toKeyList)

@[simp, grind =] theorem toKeyList_rotateRight (t : BinaryTree α) :
    (rotateRight t).toKeyList = t.toKeyList := by
  rcases t with _ | ⟨(_ | ⟨ll, lk, lr⟩), k, r⟩ <;>
    simp [rotateRight, toKeyList]

@[simp, grind =] theorem toKeyList_rotateLeft (t : BinaryTree α) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  rcases t with _ | ⟨l, k, (_ | ⟨rl, rk, rr⟩)⟩ <;>
    simp [rotateLeft, toKeyList]

@[simp, grind =] theorem toKeyList_bringUp (d : Dir) (t : BinaryTree α) :
    (d.bringUp t).toKeyList = t.toKeyList := by
  cases d <;> simp [Dir.bringUp]

@[simp, grind =] theorem toKeyList_applyChild (d : Dir) (op : BinaryTree α → BinaryTree α)
    (hop : ∀ s, (op s).toKeyList = s.toKeyList) (t : BinaryTree α) :
    (applyChild d op t).toKeyList = t.toKeyList := by
  cases t with
  | empty => rfl
  | node l k r => cases d <;> simp [applyChild, toKeyList, hop]

@[simp, grind =]
theorem toKeyList_applyChild_bringUp (d₁ d₂ : Dir) (t : BinaryTree α) :
    (applyChild d₁ d₂.bringUp t).toKeyList = t.toKeyList :=
  toKeyList_applyChild _ _ (toKeyList_bringUp _) _

@[simp, grind =] theorem toKeyList_Frame_attach (c : BinaryTree α) (f : Frame α) :
    (f.attach c).toKeyList =
      (match f.dir with
        | .L => c.toKeyList ++ [f.key] ++ f.sibling.toKeyList
        | .R => f.sibling.toKeyList ++ [f.key] ++ c.toKeyList) := by
  unfold Frame.attach
  cases f.dir <;> simp [toKeyList]

lemma reassemble_toKeyList_congr {c1 c2 : BinaryTree α} (path : List (Frame α))
    (h : c1.toKeyList = c2.toKeyList) :
    (reassemble c1 path).toKeyList = (reassemble c2 path).toKeyList := by
  induction path generalizing c1 c2 with
  | nil => simp [h]
  | cons f rest ih =>
    apply ih
    simp [h]

@[simp, grind =]
theorem toKeyList_splayUp (c : BinaryTree α) (path : List (Frame α)) :
    (splayUp c path).toKeyList = (reassemble c path).toKeyList := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp [splayUp, reassemble]
  | step c f1 f2 rest ih =>
    unfold splayUp; split_ifs <;>
      (rw [ih]; apply reassemble_toKeyList_congr; simp)

@[simp, grind =]
theorem toKeyList_splayBU [LinearOrder α] (t : BinaryTree α) (q : α) :
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

theorem splayBU_empty_iff [LinearOrder α] (t : BinaryTree α) (q : α) :
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
lemma ForallTree_iff_toKeyList (p : α → Prop) (t : BinaryTree α) :
    ForallTree p t ↔ ∀ k ∈ t.toKeyList, p k := by
  induction t with
  | empty => exact ⟨fun _ _ hk => by simp at hk, fun _ => .left⟩
  | node l k r ihl ihr =>
    simp only [BinaryTree.toKeyList_node, List.mem_append,
      List.mem_singleton]
    constructor
    · intro h; cases h with | node _ _ _ hl hk hr =>
      rintro k' ((hk' | rfl) | hk')
      · exact ihl.mp hl k' hk'
      · exact hk
      · exact ihr.mp hr k' hk'
    · intro h
      exact .node _ _ _
        (ihl.mpr fun k' hk' => h _ (.inl (.inl hk')))
        (h _ (.inl (.inr rfl)))
        (ihr.mpr fun k' hk' => h _ (.inr hk'))

/-- A tree is a BST iff its in-order traversal is strictly sorted (pairwise
`<`). Reduces every BST-preservation question to "does the operation
preserve `toKeyList`?". -/
theorem IsBST_iff_toKeyList_sorted [LinearOrder α] (t : BinaryTree α) :
    IsBST t ↔ t.toKeyList.Pairwise (· < ·) := by
  induction t with
  | empty => exact ⟨fun _ => by simp, fun _ => .left⟩
  | node l k r ihl ihr =>
    simp only [BinaryTree.toKeyList_node, List.pairwise_append,
      List.pairwise_cons, List.Pairwise.nil, List.mem_singleton,
      List.mem_append, List.not_mem_nil, false_implies,
      implies_true, and_true, true_and]
    constructor
    · intro h; cases h with | node _ _ _ hfl hfr hBl hBr =>
      have hlk := (ForallTree_iff_toKeyList _ _).mp hfl
      have hkr := (ForallTree_iff_toKeyList _ _).mp hfr
      exact ⟨⟨ihl.mp hBl, fun a ha b hb => hb ▸ hlk a ha⟩,
        ihr.mp hBr,
        fun a ha b hb => ha.elim
          (fun h => lt_trans (hlk a h) (hkr b hb))
          (fun h => h ▸ hkr b hb)⟩
    · intro ⟨⟨hl, hlk⟩, hr, hcross⟩
      exact .node _ _ _
        ((ForallTree_iff_toKeyList _ _).mpr
          fun k' hk' => hlk k' hk' k rfl)
        ((ForallTree_iff_toKeyList _ _).mpr
          fun k' hk' => hcross k (.inr rfl) k' hk')
        (ihl.mpr hl) (ihr.mpr hr)

/-- Transfer BST-ness between trees with the same in-order traversal. -/
lemma IsBST_of_toKeyList_eq [LinearOrder α] {t t' : BinaryTree α}
    (h : t'.toKeyList = t.toKeyList) (hbst : IsBST t) : IsBST t' := by
  rw [IsBST_iff_toKeyList_sorted] at hbst ⊢; rwa [h]

/-- Bottom-up splay preserves the BST invariant. -/
theorem IsBST_splayBU [LinearOrder α] (t : BinaryTree α) (q : α) (h : IsBST t) :
    IsBST (splayBU t q) :=
  IsBST_of_toKeyList_eq (toKeyList_splayBU t q) h

/-- Each primitive rotation preserves the BST invariant. -/
theorem IsBST_bringUp [LinearOrder α] (d : Dir) (t : BinaryTree α) (h : IsBST t) :
    IsBST (d.bringUp t) :=
  IsBST_of_toKeyList_eq (toKeyList_bringUp d t) h

theorem IsBST_applyChild [LinearOrder α] (d : Dir) (op : BinaryTree α → BinaryTree α)
    (hop_keys : ∀ s, (op s).toKeyList = s.toKeyList)
    (t : BinaryTree α) (h : IsBST t) :
    IsBST (applyChild d op t) :=
  IsBST_of_toKeyList_eq (toKeyList_applyChild d op hop_keys t) h

/-- Any frame-wise splay-up preserves BST-ness of the reassembled tree. -/
theorem IsBST_splayUp [LinearOrder α] (c : BinaryTree α) (path : List (Frame α))
    (h : IsBST (reassemble c path)) : IsBST (splayUp c path) :=
  IsBST_of_toKeyList_eq (toKeyList_splayUp c path) h


-- =========================================================================
-- §8  Root of `splayBU` on a contained key
-- =========================================================================


/-- If `t.contains q`, the subtree reached by `descend` is a node whose key
equals `q`. Mirrors how `descend` and `BinaryTree.contains` follow the same
comparison path. -/
theorem descend_contains [LinearOrder α] (t : BinaryTree α) (q : α) (h : t.contains q) :
    ∃ l r, (descend t q).1 = .node l q r := by
  induction t with
  | empty => simp [BinaryTree.contains] at h
  | node lt k rt ihl ihr =>
    simp only [BinaryTree.contains] at h
    by_cases hlt : q < k
    · simp only [hlt, ite_true] at h
      obtain ⟨l', r', hd⟩ := ihl h
      exact ⟨l', r', by rw [descend_node_lt hlt]; exact hd⟩
    · simp only [hlt, ite_false] at h
      by_cases hgt : k < q
      · simp only [hgt, ite_true] at h
        obtain ⟨l', r', hd⟩ := ihr h
        exact ⟨l', r', by rw [descend_node_gt hgt]; exact hd⟩
      · have hqk : q = k := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
        subst hqk; exact ⟨lt, rt, by rw [descend_node_eq]⟩

/-- Splaying a node `c = .node l k r` upward along any path yields a tree
whose root key is still `k`. Each rotation step (`bringUp`, `applyChild
bringUp`) brings `c` one level higher without changing its root key. -/
theorem splayUp_root_key_of_node :
    ∀ (path : List (Frame α)) (l : BinaryTree α) (k : α) (r : BinaryTree α),
      ∃ l' r', splayUp (.node l k r) path = .node l' k r' := by
  intro path
  induction path using List.twoStepInduction with
  | nil => intro l k r; exact ⟨l, r, rfl⟩
  | singleton f =>
    intro l k r; obtain ⟨d, kf, s⟩ := f
    cases d <;> simp [splayUp, Dir.bringUp, Frame.attach,
      rotateRight, rotateLeft]
  | cons_cons f1 f2 rest ih _ =>
    intro l k r; simp only [splayUp]
    obtain ⟨d1, k1, s1⟩ := f1; obtain ⟨d2, k2, s2⟩ := f2
    suffices ∃ l' r', (if d1 = d2 then _ else _) =
        BinaryTree.node l' k r' by
      obtain ⟨l', r', heq⟩ := this; rw [heq]; exact ih l' k r'
    cases d1 <;> cases d2 <;>
      simp [Frame.attach, Dir.bringUp, applyChild,
        rotateRight, rotateLeft]


/-- If `t.contains q`, the bottom-up splay of `t` at `q` has `q` at the root.
Replaces `Correctness.splay_root_of_contains` for `splayBU`. -/
theorem splayBU_root_of_contains [LinearOrder α] (t : BinaryTree α) (q : α)
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
def rank (t : BinaryTree α) : ℝ :=
  if t.num_nodes = 0 then 0 else Real.logb 2 t.num_nodes

/-- Potential of a tree: sum of ranks over all subtrees (including itself). -/
def φ : BinaryTree α → ℝ
  | .empty => 0
  | s@(.node l _ r) => rank s + φ l + φ r

-- -------------------------------------------------------------------------
--  The key logarithmic inequality (AM-GM for logs)
-- -------------------------------------------------------------------------

theorem log_sum_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 := by
  have hc : 0 < c := by linarith
  have hab_le : a * b ≤ c ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  have hln2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  suffices h : Real.log a + Real.log b ≤
      2 * Real.log c - 2 * Real.log 2 by
    simp only [Real.logb]
    rw [show Real.log a / Real.log 2 + Real.log b / Real.log 2 =
      (Real.log a + Real.log b) / Real.log 2 from by ring]
    rw [show 2 * (Real.log c / Real.log 2) - 2 =
      (2 * Real.log c - 2 * Real.log 2) / Real.log 2 from by
        field_simp]
    exact div_le_div_of_nonneg_right h hln2.le
  calc Real.log a + Real.log b
      = Real.log (a * b) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ ≤ Real.log (c ^ 2 / 4) :=
        Real.log_le_log (by positivity) hab_le
    _ = Real.log (c ^ 2) - Real.log 4 :=
        Real.log_div (by positivity) (by positivity)
    _ = 2 * Real.log c - 2 * Real.log 2 := by
        rw [Real.log_pow, show (4:ℝ) = 2^2 from by norm_num,
          Real.log_pow]; push_cast; ring

-- -------------------------------------------------------------------------
--  Basic rank / potential lemmas
-- -------------------------------------------------------------------------

@[simp] lemma rank_empty : rank (.empty : BinaryTree α) = 0 := by simp [rank]

lemma rank_nonneg (t : BinaryTree α) : 0 ≤ rank t := by
  simp only [rank]; split_ifs with h
  · rfl
  · exact Real.logb_nonneg (by grind)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

@[simp] lemma φ_empty : φ (.empty : BinaryTree α) = 0 := rfl

@[simp] lemma φ_node (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    φ (.node l k r) = rank (.node l k r) + φ l + φ r := rfl

lemma φ_nonneg : ∀ t : BinaryTree α, 0 ≤ φ t
  | .empty => le_refl _
  | .node l k r => by
      simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg l, φ_nonneg r]

lemma rank_le_of_num_nodes_le {s t : BinaryTree α}
    (h : s.num_nodes ≤ t.num_nodes) : rank s ≤ rank t := by
  simp only [rank]
  split_ifs with hs ht ht
  · exact le_refl _
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht)
  · omega
  · apply Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs)
      (by simp_all only [Nat.cast_le])

lemma rank_eq_of_num_nodes_eq {s t : BinaryTree α}
    (h : s.num_nodes = t.num_nodes) : rank s = rank t := by
  exact le_antisymm (rank_le_of_num_nodes_le (le_of_eq h))
    (rank_le_of_num_nodes_le (le_of_eq h.symm))

@[simp] lemma rank_splayBU [LinearOrder α] (t : BinaryTree α) (q : α) :
    rank (splayBU t q) = rank t :=
  rank_eq_of_num_nodes_eq (num_nodes_splayBU t q)

-- -------------------------------------------------------------------------
--  Mirror preserves rank and potential
-- -------------------------------------------------------------------------

lemma rank_mirror (t : BinaryTree α) : rank t.mirror = rank t := by
  simp [rank]

lemma φ_mirror : ∀ t : BinaryTree α, φ t.mirror = φ t
  | .empty => rfl
  | .node l k r => by
    change rank (.node r.mirror k l.mirror) + φ r.mirror + φ l.mirror =
      rank (.node l k r) + φ l + φ r
    rw [φ_mirror l, φ_mirror r]
    linarith [rank_eq_of_num_nodes_eq
      (show (BinaryTree.node r.mirror k l.mirror).num_nodes =
        (BinaryTree.node l k r).num_nodes by simp [BinaryTree.num_nodes]; omega)]

/-- Transfer a potential-step inequality from mirrored trees to the
originals. Given that `step.mirror = step'` and `s.mirror = s'`,
the bound `φ step' - φ s' + 2 ≤ 3*(rank step' - rank c.mirror)`
implies `φ step - φ s + 2 ≤ 3*(rank step - rank c)`. -/
private lemma φ_transfer_mirror
    {step s c step' s' : BinaryTree α}
    (hstep : step.mirror = step')
    (hs : s.mirror = s')
    (h : φ step' - φ s' + 2 ≤
      3 * (rank step' - rank c.mirror)) :
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rw [← hstep, φ_mirror, rank_mirror] at h
  rw [← hs, φ_mirror] at h
  linarith [rank_mirror c]

-- -------------------------------------------------------------------------
--  Short‐hands for `logb 2` arithmetic (used in zig‐zig / zig‐zag)
-- -------------------------------------------------------------------------

/-- Monotonicity of `logb 2`. -/
private lemma logb_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.logb 2 a ≤ Real.logb 2 b :=
  Real.logb_le_logb_of_le (by norm_num) ha hab

/-- Non‐negativity of `logb 2 x` when `x ≥ 1`. -/
private lemma logb_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.logb 2 x :=
  Real.logb_nonneg (by norm_num) hx

/-- `logb 2 x ≥ 1` when `x ≥ 2`. -/
private lemma one_le_logb {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ Real.logb 2 x := by
  rwa [Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by linarith),
    show (2 : ℝ) ^ (1 : ℝ) = 2 from by norm_num]

-- -------------------------------------------------------------------------
--  Potential of subtrees versus the whole tree
-- -------------------------------------------------------------------------

theorem φ_subtree_le_left (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    φ l ≤ φ (.node l k r) := by
  simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg r]

theorem φ_subtree_le_right (l : BinaryTree α) (k : α) (r : BinaryTree α) :
    φ r ≤ φ (.node l k r) := by
  simp [φ]; linarith [rank_nonneg (.node l k r), φ_nonneg l]

theorem φ_le_attach (c : BinaryTree α) (f : Frame α) :
    φ c ≤ φ (f.attach c) := by
  cases f with | mk d k s =>
  cases d <;> simp [Frame.attach, φ_node] <;>
    linarith [rank_nonneg (c.node k s), rank_nonneg (s.node k c),
      φ_nonneg c, φ_nonneg s]

theorem φ_le_reassemble (c : BinaryTree α) (path : List (Frame α)) :
    φ c ≤ φ (reassemble c path) := by
  induction path generalizing c with
  | nil => simp
  | cons f rest ih => simp only [reassemble_cons]; exact le_trans (φ_le_attach c f) (ih _)

theorem φ_descend_subtree_le [LinearOrder α] (t : BinaryTree α) (q : α) :
    φ (descend t q).1 ≤ φ t := by
  have h := descend_preserves_tree t q
  calc φ (descend t q).1
      ≤ φ (reassemble (descend t q).1 (descend t q).2) :=
        φ_le_reassemble _ _
    _ = φ t := by rw [h]

theorem φ_attach_base_le [LinearOrder α] (t : BinaryTree α) (q : α)
  (f : Frame α) (rest : List (Frame α))
  (hd : descend t q = (.empty, f :: rest)) : φ (f.attach .empty) ≤ φ t := by
  have h := descend_preserves_tree t q
  rw [hd] at h; simp only at h; rw [← h]
  exact φ_le_reassemble (f.attach .empty) rest

theorem φ_descend_node_le [LinearOrder α] (t : BinaryTree α) (q : α)
  (l : BinaryTree α) (k : α) (r : BinaryTree α) (path : List (Frame α))
  (hd : descend t q = (.node l k r, path)) : φ (.node l k r) ≤ φ t := by
  have h := descend_preserves_tree t q
  rw [hd] at h; simp_all only [φ_node, ge_iff_le]; rw [← h]
  exact φ_le_reassemble (.node l k r) path

-- -----------------------------------------------------------------------
-- φ step potential bounds
-- -----------------------------------------------------------------------

/-
Zig step (single rotation): the potential of the rotated tree minus the
    potential of the assembled tree is at most the rank increase of the
    splayed node.
-/
theorem φ_zig (c : BinaryTree α) (f : Frame α) :
    φ (f.dir.bringUp (f.attach c)) - φ (f.attach c) ≤
      rank (f.dir.bringUp (f.attach c)) - rank c := by
  rcases f with ⟨d, key, sib⟩
  rcases c with _ | ⟨l, k, r⟩ <;> cases d <;>
    all_goals simp only [Dir.bringUp, rotateLeft, rotateRight,
    Frame.attach, φ_node, φ_empty, add_zero, sub_self, rank_empty, sub_zero]
  -- empty: 0 ≤ rank t; node: rank(child) ≤ rank(parent)
  · exact rank_nonneg _
  · exact rank_nonneg _
  · linarith [rank_le_of_num_nodes_le (show
      (BinaryTree.node r key sib).num_nodes ≤
      (BinaryTree.node (BinaryTree.node l k r) key sib).num_nodes
      by simp)]
  · linarith [rank_le_of_num_nodes_le (show
      (BinaryTree.node sib key l).num_nodes ≤
      (BinaryTree.node sib key (BinaryTree.node l k r)).num_nodes
      by simp; omega)]

/-
Zig-zig step (same-direction double rotation): the potential change
    (relative to the assembled tree) plus the actual cost (2 rotations)
    is at most 3 times the rank increase of the splayed node.

By mirror symmetry it suffices to prove the `L`-`L` case;
the `R`-`R` case follows from `φ_mirror` / `rank_mirror`.
-/

/-- Zig-zig, left–left direction only. -/
private theorem φ_zigzig_left (c : BinaryTree α)
    (k1 : α) (n1 : BinaryTree α) (k2 : α) (n2 : BinaryTree α) :
    let s := (Frame.mk .L k2 n2).attach ((Frame.mk .L k1 n1).attach c)
    let step := rotateRight (rotateRight s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  -- Abbreviations for the key natural‐number sizes
  set nn1 := (n1.num_nodes : ℝ); set nn2 := (n2.num_nodes : ℝ)
  have h1 : (0 : ℝ) ≤ nn1 := by positivity
  have h2 : (0 : ℝ) ≤ nn2 := by positivity
  rcases c with _ | ⟨l, k, r⟩ <;>
    simp +decide only [Frame.attach, rotateRight,
      φ_node, φ_empty, rank, add_zero, sub_zero,
      BinaryTree.num_nodes_node, BinaryTree.num_nodes_empty,
      Nat.add_eq_zero_iff, false_and, and_self,
      ↓reduceIte, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf
  -- c = .empty : 2 ≤ 3 * logb 2 (2 + nn1 + nn2)
  · nlinarith [
      logb_mono (show (0 : ℝ) < 1 + nn1 + nn2 by linarith)
        (show 1 + nn1 + nn2 ≤ 2 + nn1 + nn2 by linarith),
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn1 by linarith),
      one_le_logb (show (2 : ℝ) ≤ 2 + nn1 + nn2 by linarith)]
  -- c = node l k r : use log_sum_le + monotonicity
  · set a := (l.num_nodes α : ℝ); set b := (r.num_nodes α : ℝ)
    have ha : (0 : ℝ) ≤ a := by positivity
    have hb : (0 : ℝ) ≤ b := by positivity
    have hls := log_sum_le
        (show (0 : ℝ) < 1 + a + b by linarith)
        (show (0 : ℝ) < 1 + nn1 + nn2 by linarith)
        (show 1 + a + b + (1 + nn1 + nn2) ≤
          3 + a + b + nn1 + nn2 by linarith)
    nlinarith [
      logb_mono (show (0 : ℝ) < 2 + b + nn1 + nn2 by linarith)
        (show 2 + b + nn1 + nn2 ≤
          3 + a + b + nn1 + nn2 by linarith),
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 2 + a + b + nn1 by linarith)]

theorem φ_zigzig (c : BinaryTree α) (f1 f2 : Frame α)
    (heq : f1.dir = f2.dir) :
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (f2.dir.bringUp s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rcases f1 with ⟨d, k1, n1⟩; rcases f2 with ⟨_, k2, n2⟩; subst heq
  cases d
  · -- L-L: direct
    exact φ_zigzig_left c k1 n1 k2 n2
  · -- R-R → L-L via mirror
    have h := φ_zigzig_left c.mirror k1 n1.mirror k2 n2.mirror
    simp only [Frame.attach, Dir.bringUp] at h ⊢
    exact φ_transfer_mirror (by simp [mirror_rotateLeft]) (by simp) h

/-
Zig-zag step (opposite-direction double rotation): same bound.

By mirror symmetry it suffices to prove the `L`-`R` case;
`R`-`L` follows from `φ_mirror` / `rank_mirror`.
-/

/-- Zig-zag, left–right direction only. -/
private theorem φ_zigzag_left (c : BinaryTree α)
    (k1 : α) (n1 : BinaryTree α) (k2 : α) (n2 : BinaryTree α) :
    let f1 : Frame α := ⟨.L, k1, n1⟩
    let f2 : Frame α := ⟨.R, k2, n2⟩
    let s := f2.attach (f1.attach c)
    let step := rotateLeft (applyChild .R rotateRight s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  -- Abbreviations for the key natural‐number sizes
  set nn1 := (n1.num_nodes : ℝ); set nn2 := (n2.num_nodes : ℝ)
  have h1 : (0 : ℝ) ≤ nn1 := by positivity
  have h2 : (0 : ℝ) ≤ nn2 := by positivity
  rcases c with _ | ⟨l, k, r⟩ <;>
    simp +decide only [Frame.attach, applyChild,
      rotateRight, rotateLeft,
      φ_node, φ_empty, rank, add_zero, sub_zero,
      BinaryTree.num_nodes_node, BinaryTree.num_nodes_empty,
      Nat.add_eq_zero_iff, false_and, and_self,
      ↓reduceIte, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf
  -- c = .empty
  · have hls := log_sum_le
        (show (0 : ℝ) < nn1 + 1 by linarith)
        (show (0 : ℝ) < nn2 + 1 by linarith)
        (show nn1 + 1 + (nn2 + 1) ≤ nn1 + nn2 + 2 by linarith)
    simp only [show nn1 + 1 = 1 + nn1 by ring,
      show nn2 + 1 = 1 + nn2 by ring,
      show nn1 + nn2 + 2 = 2 + nn2 + nn1 by ring] at hls
    linarith [
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn1 by linarith),
      logb_nonneg (show (1 : ℝ) ≤ 1 + nn2 by linarith)]
  -- c = node l k r
  · set a := (l.num_nodes : ℝ); set b := (r.num_nodes : ℝ)
    have ha : (0 : ℝ) ≤ a := by positivity
    have hb : (0 : ℝ) ≤ b := by positivity
    have hls := log_sum_le
        (show (0 : ℝ) < 1 + nn2 + a by linarith)
        (show (0 : ℝ) < 1 + b + nn1 by linarith)
        (show 1 + nn2 + a + (1 + b + nn1) ≤
          3 + nn2 + a + b + nn1 by linarith)
    nlinarith [
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 2 + a + b + nn1 by linarith),
      logb_mono (show (0 : ℝ) < 1 + a + b by linarith)
        (show 1 + a + b ≤ 3 + nn2 + a + b + nn1 by linarith)]

theorem φ_zigzag (c : BinaryTree α) (f1 f2 : Frame α)
    (hne : f1.dir ≠ f2.dir) :
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    φ step - φ s + 2 ≤ 3 * (rank step - rank c) := by
  rcases f1 with ⟨d1, k1, n1⟩; rcases f2 with ⟨d2, k2, n2⟩
  cases d1 <;> cases d2 <;> simp_all +decide only [ne_eq]
  · -- L-R: direct
    exact φ_zigzag_left c k1 n1 k2 n2
  · -- R-L → L-R via mirror
    have h := φ_zigzag_left c.mirror k1 n1.mirror k2 n2.mirror
    simp only [Frame.attach, Dir.bringUp, applyChild] at h ⊢
    exact φ_transfer_mirror
      (by simp [mirror_rotateRight, mirror_rotateLeft]) (by simp) h

-- -------------------------------------------------------------------------
--  Telescoping: potential change along the full splayUp
-- -------------------------------------------------------------------------

/-- The key congruence lemma: if two trees have the same number of nodes,
    then the potential change from attaching them to the same frame is
    the same. -/
lemma φ_attach_congr {s s' : BinaryTree α} (f : Frame α)
    (h : s.num_nodes = s'.num_nodes) :
    φ (f.attach s') - φ (f.attach s) = φ s' - φ s := by
  cases f with | mk d k sib =>
  cases d <;> simp only [Frame.attach, φ_node, add_sub_add_right_eq_sub] <;>
    (unfold rank; simp [h])

/-- Extending the congr lemma to full paths. -/
lemma φ_reassemble_congr {s s' : BinaryTree α} (path : List (Frame α))
    (h : s.num_nodes = s'.num_nodes) :
    φ (reassemble s' path) - φ (reassemble s path) = φ s' - φ s := by
  induction path generalizing s s' with
  | nil => simp
  | cons f rest ih =>
    simp only [reassemble_cons]
    rw [ih (by simp [num_nodes_Frame_attach, h])]
    exact φ_attach_congr f h

/-- The total potential change of splayUp plus the path length is at
    most 3 × the rank increase + 1. -/
theorem φ_splayUp (c : BinaryTree α) (path : List (Frame α)) :
    φ (splayUp c path) - φ (reassemble c path) + path.length ≤
      3 * (rank (splayUp c path) - rank c) + 1 := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp only [splayUp_singleton, reassemble_cons,
      reassemble_nil, List.length_singleton, Nat.cast_one]
    linarith [φ_zig c f,
      rank_le_of_num_nodes_le (α := α)
        (show c.num_nodes ≤
          (f.dir.bringUp (f.attach c)).num_nodes from by simp)]
  | step c f1 f2 rest ih =>
    rw [splayUp_cons_cons]; simp only [List.length_cons]
    split_ifs with hdir
    · set s := f2.attach (f1.attach c)
      set step_tree := f2.dir.bringUp (f2.dir.bringUp s)
      have hnn : step_tree.num_nodes = s.num_nodes := by
        simp [step_tree]
      simp only [reassemble_cons]; push_cast
      nlinarith [ih step_tree,
        φ_reassemble_congr rest hnn.symm, φ_zigzig c f1 f2 hdir]
    · set s := f2.attach (f1.attach c)
      set step_tree :=
        f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
      have hnn : step_tree.num_nodes = s.num_nodes := by
        simp [step_tree]
      simp only [reassemble_cons]; push_cast
      nlinarith [ih step_tree,
        φ_reassemble_congr rest hnn.symm, φ_zigzag c f1 f2 hdir]

-- -------------------------------------------------------------------------
--  The main amortized bound
-- -------------------------------------------------------------------------

private lemma rank_eq_logb {t : BinaryTree α}
    (h : t.num_nodes ≠ 0) :
    rank t = Real.logb 2 t.num_nodes := by
  simp [rank, h]

private lemma num_nodes_pos_of_descend_nonempty_path
    [LinearOrder α] {t : BinaryTree α} {q : α}
    {reached : BinaryTree α} {path : List (Frame α)}
    (hdecomp : descend t q = (reached, path))
    (hpath : path ≠ []) : t.num_nodes ≠ 0 := by
  intro h0
  have hd := num_nodes_descend t q
  rw [hdecomp] at hd; simp at hd
  rcases path with _ | ⟨f, rest⟩
  · exact hpath rfl
  · simp [pathNodes, Frame.nodes] at hd; omega

theorem splayBU_amortized_bound [LinearOrder α]
    (t : BinaryTree α) (q : α) :
    φ (splayBU t q) - φ t + splayBU.cost t q ≤
      3 * Real.logb 2 t.num_nodes + 2 := by
  rcases hdecomp : descend t q with ⟨reached, path⟩
  have hpres := descend_preserves_tree t q
  rw [hdecomp] at hpres; simp only at hpres
  -- Express splayBU and cost in terms of descend result
  have h_splay : splayBU t q = splayUp reached path ∨
      (∃ f rest, reached = .empty ∧
        path = f :: rest ∧
        splayBU t q = splayUp (f.attach .empty) rest) := by
    simp only [splayBU, hdecomp]
    rcases reached with _ | ⟨l, k, r⟩
    · rcases path with _ | ⟨f, rest⟩
      · left; rfl
      · right; exact ⟨f, rest, rfl, rfl, rfl⟩
    · left; rfl
  have h_cost : splayBU.cost t q = path.length := by
    simp [splayBU.cost, hdecomp]
  rw [h_cost]
  rcases reached with _ | ⟨l, k, r⟩
  · -- reached = .empty
    rcases path with _ | ⟨f, rest⟩
    · -- empty tree, empty path → t is empty
      simp only [reassemble, List.foldl_nil] at hpres
      subst hpres
      simp [splayBU, hdecomp, φ]
    · -- empty reached, non-empty path
      have h_eq : splayBU t q =
          splayUp (f.attach .empty) rest := by
        simp [splayBU, hdecomp]
      rw [h_eq]
      set base := f.attach (.empty : BinaryTree α)
      have hpres' : reassemble base rest = t := by
        rw [← hpres]; simp [reassemble, base]
      have hφ := φ_splayUp base rest
      rw [hpres'] at hφ
      have hrank_eq : rank (splayUp base rest) =
          rank t := by
        have h := rank_splayBU t q
        simp only [splayBU, hdecomp] at h; exact h
      have hnn : t.num_nodes ≠ 0 :=
        num_nodes_pos_of_descend_nonempty_path
          hdecomp (List.cons_ne_nil f rest)
      simp only [List.length_cons, Nat.cast_add,
        Nat.cast_one]
      calc φ (splayUp base rest) - φ t +
              (↑rest.length + 1)
          = 1 + (φ (splayUp base rest) - φ t +
              ↑rest.length) := by ring
        _ ≤ 1 + (3 * (rank (splayUp base rest) -
              rank base) + 1) := by linarith
        _ = 3 * (rank (splayUp base rest) -
              rank base) + 2 := by ring
        _ ≤ 3 * rank (splayUp base rest) + 2 := by
            linarith [rank_nonneg base]
        _ = 3 * Real.logb 2 t.num_nodes + 2 := by
            rw [hrank_eq, rank_eq_logb hnn]
  · -- reached = .node l k r
    have h_eq : splayBU t q =
        splayUp (.node l k r) path := by
      simp [splayBU, hdecomp]
    rw [h_eq]
    have hφ := φ_splayUp (.node l k r) path
    rw [hpres] at hφ
    have hrank_eq :
        rank (splayUp (.node l k r) path) = rank t := by
      have h := rank_splayBU t q
      simp only [splayBU, hdecomp] at h; exact h
    have hnn : t.num_nodes ≠ 0 := by
      have hd := num_nodes_descend t q
      rw [hdecomp] at hd
      simp at hd; omega
    calc φ (splayUp (.node l k r) path) - φ t +
            ↑path.length
        ≤ 3 * (rank (splayUp (.node l k r) path) -
            rank (.node l k r)) + 1 := by
          exact_mod_cast hφ
      _ ≤ 3 * rank (splayUp (.node l k r) path) +
            1 := by linarith [rank_nonneg (.node l k r)]
      _ ≤ 3 * Real.logb 2 t.num_nodes + 2 := by
          rw [hrank_eq, rank_eq_logb hnn]; linarith

/-!
# General Amortized Analysis and Splay Tree Corollary
## General Framework
Given a sequence of `m` operations on states with a potential
function `Φ` such that each step satisfies
  `Φ(s_{i+1}) - Φ(s_i) + cost_i ≤ B`
the total actual cost telescopes to at most `m * B + Φ(s₀)`.
## Splay Tree Corollary
Applying this to bottom-up splay with `Φ = φ` and
`B = 3 * log₂(n) + 2`, the total cost of `m` splay
operations on trees of at most `n` nodes is bounded by
`m * (3 * log₂(n) + 2) + φ(t₀)`.
-/

-- ---------------------------------------------------------
-- General amortized analysis
-- ---------------------------------------------------------

/-- General amortized analysis telescope. If each step
satisfies `Φ(s_{i+1}) - Φ(s_i) + cost_i ≤ B`, then the
total cost is at most `m * B + Φ(s₀) - Φ(sₘ)`. -/
theorem amortized_cost_bound {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B) :
    ∑ i : Fin m, cost i ≤
      m * B + Φ (s 0) - Φ (s (Fin.last m)) := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    hamort i
  simp_all +decide only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
  Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
  ge_iff_le]
  linarith! [Fin.sum_univ_castSucc fun i => Φ (s i),
    Fin.sum_univ_succ fun i => Φ (s i)]

/-- Simplified amortized bound when the potential is
nonnegative: total cost ≤ `m * B + Φ(s₀)`. -/
theorem amortized_cost_bound' {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) :
    ∑ i : Fin m, cost i ≤ m * B + Φ (s 0) := by
  linarith [amortized_cost_bound m s cost Φ B hamort,
    hΦ_nonneg (s (Fin.last m))]

-- ---------------------------------------------------------
-- Splay tree amortized corollary
-- ---------------------------------------------------------

/-- The total cost of `m` bottom-up splay operations is at
most `m * (3 * log₂ n + 2) + φ(t₀)`, provided every tree
has at most `n` nodes and each step satisfies
`t(i+1) = splayBU (t i) (q i)`. -/
theorem splayBU_total_cost [LinearOrder α] (m : ℕ)
    (t : Fin (m + 1) → BinaryTree α)
    (q : Fin m → α) (n : ℕ)
    (hseq : ∀ i : Fin m,
      t i.succ = splayBU (t i.castSucc) (q i))
    (hsize : ∀ i : Fin (m + 1),
      (t i).num_nodes ≤ n) :
    ∑ i : Fin m,
      splayBU.cost (t i.castSucc) (q i) ≤
      m * (3 * Real.logb 2 n + 2) + φ (t 0) := by
  apply amortized_cost_bound' m t
    (fun i => splayBU.cost (t i.castSucc) (q i))
    φ (3 * Real.logb 2 n + 2)
  · intro i
    rw [hseq i]
    have hb := splayBU_amortized_bound
      (t i.castSucc) (q i)
    by_cases h : (t (Fin.castSucc i)).num_nodes = 0
    · simp_all +decide [Real.logb]
      have : (0 : ℝ) ≤ Real.log n / Real.log 2 :=
        by positivity
      linarith
    · calc φ (splayBU (t i.castSucc) (q i)) -
              φ (t i.castSucc) +
              splayBU.cost (t i.castSucc) (q i)
          ≤ 3 * Real.logb 2
              (t i.castSucc).num_nodes + 2 := hb
        _ ≤ 3 * Real.logb 2 n + 2 := by
            gcongr <;> [norm_num; exact hsize _]
  · exact fun x => φ_nonneg x

end
