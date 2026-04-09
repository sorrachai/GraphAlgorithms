import Mathlib.Data.Sym.Sym2
-- Authors: Sorrachai Yingchareonthawornchai
-- This definition of walk are well-defined for both directed and undirected simple graphs.

set_option tactic.hygienic false
variable {α : Type*}

/- VertexSeq as a non-empty seq -/
inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

namespace VertexSeq

/-! ## Basic accessors -/

/-- The list of vertices visited by the walk, in order. -/
def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons p v => p.toList ++ [v]

/-- The first node does not count in the sequence. -/
@[simp] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => head w

def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

@[simp] lemma con_head_eq (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

@[simp] lemma con_tail_eq (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

/-! ## dropHead, dropTail -/

def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => .cons (dropHead w) v

def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-! ## append, reverse, and their laws -/

def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons w2 v => .cons (append w w2) v

def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

@[simp] lemma tail_on_tail (p q : VertexSeq α) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

@[simp] lemma head_on_head (p q : VertexSeq α) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

@[simp] lemma tail_on_tail_singleton (p : VertexSeq α) (x : α) :
    (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> aesop

@[simp] lemma head_on_head_singleton (p : VertexSeq α) (x : α) :
  ((VertexSeq.singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

@[simp] lemma append_assoc (p q r : VertexSeq α) :
    (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

@[simp] lemma reverse_append (p q : VertexSeq α) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]

@[simp] lemma reverse_reverse (p : VertexSeq α) : (p.reverse).reverse = p := by
  fun_induction reverse p <;> aesop

@[simp] lemma head_reverse (p : VertexSeq α) : (p.reverse).head = p.tail := by
  fun_induction reverse p <;> aesop

@[simp] lemma tail_reverse (p : VertexSeq α) : (p.reverse).tail = p.head := by
  fun_induction reverse p <;> aesop

@[simp] lemma dropTail_head (p : VertexSeq α) : p.dropTail.head = p.head := by
  fun_induction reverse p <;> aesop

/-! ## takeUntil, dropUntil, loopErase -/

/-- Take vertices until the first occurrence of `v` (including `v`). -/
def takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

/-- Drop vertices until the last occurrence of `v` (not including `v`). -/
def dropUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

@[simp] lemma takeUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind [length]

@[simp] lemma dropUntil_length_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind [length]

@[simp] lemma head_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (takeUntil w v h).head = w.head := by
  induction w with
  | singleton x => grind [takeUntil]
  | cons w x ih => grind [takeUntil, head, toList]

@[simp] lemma tail_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (takeUntil w v h).tail = v := by
  induction w with
  | singleton x => grind [takeUntil, tail, toList]
  | cons w x ih => grind [takeUntil, tail, toList]

@[simp] lemma mem_takeUntil [DecidableEq α] (w : VertexSeq α) (v x : α) (h : v ∈ w.toList) :
    x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v with
  | singleton y => simp [takeUntil]
  | cons w y ih => grind [takeUntil, toList]

def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if h : v ∈ w.toList then
        loopErase (takeUntil w v h)
      else
        .cons (loopErase w) v
  termination_by p => p.length
  decreasing_by
  · simp; grind [takeUntil_length_le]
  · simp

lemma mem_loopErase [DecidableEq α] (w : VertexSeq α) :
    ∀ {x : α}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

theorem loopErase_nodup [DecidableEq α] (w : VertexSeq α) : w.loopErase.toList.Nodup := by
  fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

@[simp] lemma head_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.head = w.head := by
  fun_induction loopErase w <;> simp_all

@[simp] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) : w.loopErase.tail = w.tail := by
  fun_induction loopErase w <;> simp_all

end VertexSeq

/-! ## IsWalk, Walk core data -/

inductive IsWalk : VertexSeq α → Prop
  | singleton (v : α) : IsWalk (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)
    : IsWalk (.cons w u)

structure Walk (α : Type*) where
  seq : VertexSeq α
  valid : IsWalk seq

namespace Walk
open VertexSeq

/-! ## Basic IsWalk helper lemmas -/

@[simp] lemma iswalk_prefix (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : IsWalk w2 := by
  cases valid
  grind

@[simp] lemma tail_neq_of_iswalk (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by
  cases valid
  grind

lemma nodup_iswalk (w : VertexSeq α) (h : w.toList.Nodup) : IsWalk w := by
  induction w with
  | singleton v => simp [IsWalk.singleton]
  | cons w v ih => grind [IsWalk.cons, toList, tail, VertexSeq]

lemma prepend_iswalk (w2 : VertexSeq α) (v : α)
    (valid : IsWalk w2) (hneq : v ≠ w2.head) :
  IsWalk ((VertexSeq.singleton v).append w2) := by
  induction valid generalizing v with
  | singleton x => grind [head, tail, append, IsWalk.singleton, IsWalk.cons]
  | cons w u hw htail ih => grind [head, append, IsWalk.cons, tail_on_tail]

lemma takeUntil_iswalk [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
  (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v with
  | singleton x => grind [takeUntil, IsWalk.singleton]
  | cons w u hw hneq ih => grind [takeUntil, IsWalk.cons]

lemma loopErase_iswalk [DecidableEq α] (w : VertexSeq α) : IsWalk w.loopErase := by
  grind [nodup_iswalk, loopErase_nodup]

/-! ## support, head, tail, length, dropTail for Walk -/

/-- The list of vertices visited by the walk, in order. -/
def support (w : Walk α) : List α := w.seq.toList

abbrev head (w : Walk α) : α := w.seq.head
abbrev tail (w : Walk α) : α := w.seq.tail
abbrev length (w : Walk α) : ℕ := w.seq.length

abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail
    valid := by
      have : IsWalk w.seq := by exact w.valid
      generalize h_eq1 : w.seq = p
      have : IsWalk p := by grind
      cases this
      · aesop
      · simpa [VertexSeq.dropTail] }

def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.valid (by aesop)⟩

lemma dropTail_head (w : Walk α) : w.dropTail.head = w.head := by
  cases w with
  | mk seq valid =>
      cases seq <;> simp [Walk.head, VertexSeq.dropTail, VertexSeq.head]

lemma len_zero_of_drop_tail_eq_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
    w.length = 0 := by
  cases w
  induction valid
  · exact Nat.eq_zero_of_add_eq_zero_left rfl
  · exact Nat.eq_zero_of_not_pos fun a ↦ hneq h

lemma head_eq_tail_of_length_zero (w : Walk α) (h : w.length = 0) : w.head = w.tail := by
  cases w with
  | mk seq valid =>
      cases valid <;> simp_all [Walk.length, Walk.head, Walk.tail, VertexSeq.head, VertexSeq.tail]

/-! ## Walk append, reverse and related lemmas -/

lemma two_seqs_append_of (w1 w2 : Walk α) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.seq.append w2.seq) := by
  cases w1
  cases w2
  simp_all only [Walk.tail, Walk.head, ne_eq]
  fun_induction seq.append seq_1
  · exact IsWalk.cons w v valid hneq
  · refine IsWalk.cons (w.append w2) v ?_ ?_
    apply ih1 <;> simp_all only [forall_const, con_head_eq, not_false_eq_true]
    · exact iswalk_prefix w2 v valid_1
    · simp_all only [forall_const, con_head_eq, tail_on_tail, ne_eq,
        tail_neq_of_iswalk, not_false_eq_true]

def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
  if h1 : w1.length = 0 then w2
  else
    { seq := w1.dropTail.seq.append w2.seq
      valid := by
        apply two_seqs_append_of
        rw [← h]
        by_contra!
        absurd h1
        apply len_zero_of_drop_tail_eq_tail
        exact this }

def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse
    valid := by
      cases w
      induction valid
      · grind [VertexSeq.reverse, IsWalk]
      · simp_all only [VertexSeq.reverse]
        have h : IsWalk (VertexSeq.singleton u) := by exact IsWalk.singleton u
        apply two_seqs_append_of (⟨VertexSeq.singleton u, h⟩ : Walk α) (⟨w.reverse, hw_ih⟩ : Walk α)
        simp_all only [Walk.head, Walk.tail]
        unfold VertexSeq.tail
        aesop }

@[simp] lemma head_reverse (w : Walk α) : (w.reverse).head = w.tail := by
  simp [reverse, head]

@[simp] lemma tail_reverse (w : Walk α) : (w.reverse).tail = w.head := by
  simp [reverse, tail]

@[simp] lemma head_on_head (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  unfold Walk.append
  split
  · grind [head_eq_tail_of_length_zero]
  · simp [Walk.head]

@[simp] lemma tail_on_tail (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by
  unfold Walk.append
  split <;> simp [Walk.tail]

/-! ## path, cycle -/

def IsPath (w : Walk α) : Prop := w.support.Nodup

abbrev toPath [DecidableEq α] (w : Walk α) : Walk α :=
  { seq := w.seq.loopErase
    valid := loopErase_iswalk w.seq }

theorem toPath_isPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by
  unfold IsPath toPath support
  simpa using loopErase_nodup w.seq

lemma tail_toPath [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind [tail_loopErase]

lemma head_toPath [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind [head_loopErase]

def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail

end Walk
