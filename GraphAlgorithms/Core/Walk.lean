import Mathlib.Data.Sym.Sym2
-- Authors: Sorrachai Yingchareonthawornchai
-- This definition of walk are well-defined for both directed and undirected simple graphs.

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

/- VertexSeq as a non-empty seq -/
inductive VertexSeq (V : Type*)
  | singleton (v : V) : VertexSeq V
  | cons (w : VertexSeq V) (v : V) : VertexSeq V

namespace VertexSeq

/-- The list of vertices visited by the walk, in order. -/
def toList : VertexSeq α →  List α
  | .singleton v => [v]
  | .cons p v => p.toList ++ [v]

/-- The first node does not count in the sequence. -/
@[simp] def length {V : Type*} : VertexSeq V → ℕ
  | singleton _ => 0
  | cons w _   => 1 + w.length

def tail {V : Type*} : VertexSeq V → V
  | singleton v => v
  | cons _ v   => v

@[simp] lemma con_tail_eq {V : Type*} (w : VertexSeq V) (u : V) :
  (w.cons u).tail = u := rfl

def head {V : Type*} : VertexSeq V → V
  | singleton v => v
  | cons w _   => head w

@[simp] lemma con_head_eq {V : Type*} (w : VertexSeq V) (u : V) :
  (w.cons u).head = w.head := rfl


def dropTail {V : Type*} : VertexSeq V → VertexSeq V
  | singleton v => .singleton v -- singleton remains singleton
  | cons w _   => w

def dropHead {V : Type*} : VertexSeq V → VertexSeq V
  | singleton v => .singleton v -- singleton remains singleton
  | cons (singleton _) v => .singleton v
  | cons w v   => cons (dropHead w) v

def append {V : Type*} : VertexSeq V →  VertexSeq V → VertexSeq V
  | w, .singleton v => .cons w v
  | w, .cons w2 v   => .cons (append w w2) v

def reverse {V : Type*} : VertexSeq V → VertexSeq V
  | singleton v => .singleton v
  | cons w v   => append (.singleton v) (reverse w)


@[simp] lemma tail_on_tail {V : Type*} (p q : VertexSeq V) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

@[simp] lemma head_on_head {V : Type*} (p q : VertexSeq V) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

@[simp] lemma tail_on_tail_singleton {V : Type*} (p : VertexSeq V) (x : V) :
  (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> aesop

@[simp] lemma head_on_head_singleton {V : Type*} (p : VertexSeq V) (x : V) :
  ((singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

@[simp] lemma append_assoc {V : Type*} (p q r : VertexSeq V) :
  (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

@[simp] lemma reverse_append {V : Type*} (p q : VertexSeq V) :
  (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]

@[simp] lemma reverse_reverse {V : Type*} (p : VertexSeq V) : (p.reverse).reverse = p := by
  fun_induction reverse p <;> aesop

@[simp] lemma head_reverse {V : Type*} (p : VertexSeq V) : (p.reverse).head = p.tail := by
  fun_induction reverse p <;> aesop

@[simp] lemma tail_reverse {V : Type*} (p : VertexSeq V) : (p.reverse).tail = p.head := by
  fun_induction reverse p <;> aesop

@[simp] lemma dropTail_head {V : Type*} (p : VertexSeq V) : p.dropTail.head = p.head := by
  fun_induction reverse p <;> aesop


/-
takeUntil, dropUntil, and related lemmas
-/
-- Take vertices until the first occurrence of v (including v)
def takeUntil {V : Type*} [DecidableEq V] (w : VertexSeq V) (v : V)
  (h : v ∈ w.toList) : VertexSeq V :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

-- Drop vertices until the last occurrence of v (not including v)
def dropUntil {V : Type*} [DecidableEq V] (w : VertexSeq V) (v : V)
  (h : v ∈ w.toList) : VertexSeq V :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

@[simp] lemma takeUntil_length_le {V : Type*} [DecidableEq V] (w : VertexSeq V) (v : V)
(h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind [length]

@[simp] lemma dropUntil_length_le {V : Type*} [DecidableEq V] (w : VertexSeq V) (v : V)
(h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind [length]

@[simp] lemma head_takeUntil {V : Type*} [DecidableEq V]
    (w : VertexSeq V) (v : V) (h : v ∈ w.toList) :
    (takeUntil w v h).head = w.head := by
  induction w with
  | singleton x => grind [takeUntil]
  | cons w x ih => grind [takeUntil, head, toList]

@[simp] lemma tail_takeUntil {V : Type*} [DecidableEq V]
    (w : VertexSeq V) (v : V) (h : v ∈ w.toList) :
    (takeUntil w v h).tail = v := by
  induction w with
  | singleton x => grind [takeUntil, tail, toList]
  | cons w x ih => grind [takeUntil, tail, toList]

@[simp] lemma mem_takeUntil {V : Type*} [DecidableEq V]
    (w : VertexSeq V) (v x : V) (h : v ∈ w.toList) :
    x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v with
  | singleton y => simp [takeUntil]
  | cons w y ih => grind [takeUntil, toList]


def loopErase {V : Type*} [DecidableEq V] : VertexSeq V → VertexSeq V
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



lemma mem_loopErase {V : Type*} [DecidableEq V] (w : VertexSeq V) :
    ∀ {x : V}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

theorem loopErase_nodup {V : Type*} [DecidableEq V] (w : VertexSeq V) :
    w.loopErase.toList.Nodup := by
  fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

@[simp] lemma head_loopErase {V : Type*} [DecidableEq V] (w : VertexSeq V) :
    w.loopErase.head = w.head := by
  fun_induction loopErase w <;> simp_all

@[simp] lemma tail_loopErase {V : Type*} [DecidableEq V] (w : VertexSeq V) :
    w.loopErase.tail = w.tail := by
  fun_induction loopErase w <;> simp_all

end VertexSeq



inductive IsWalk {V : Type*} : VertexSeq V → Prop
  | singleton (v : V) : IsWalk (VertexSeq.singleton v)
  | cons  (w : VertexSeq V) (u : V)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)   -- non-stuttering
    : IsWalk (VertexSeq.cons w u)

structure Walk (V : Type*) where
  seq : VertexSeq V
  valid : IsWalk seq




namespace Walk
open VertexSeq

@[simp] theorem iswalk_prefix {V : Type*} (w2 : VertexSeq V) (v : V)
(valid : IsWalk (w2.cons v)) : IsWalk w2 := by cases valid; grind

@[simp] theorem tail_neq_of_iswalk {V : Type*} (w2 : VertexSeq V) (v : V)
(valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by cases valid; grind


lemma nodup_iswalk {V : Type*} (w : VertexSeq V) (h : w.toList.Nodup) : IsWalk w := by
  induction w with
  | singleton v => simp [IsWalk.singleton]
  | cons w v ih => grind [IsWalk.cons, toList, tail, VertexSeq]

lemma prepend_iswalk {V : Type*} (w2 : VertexSeq V) (v : V)
(valid : IsWalk w2) (hneq : v ≠ w2.head) : IsWalk ((VertexSeq.singleton v).append w2) := by
induction valid generalizing v with
| singleton x => grind [head, tail, append, IsWalk.singleton, IsWalk.cons]
| cons w u hw htail ih => grind [head, append, IsWalk.cons, tail_on_tail]

lemma takeUntil_iswalk {V : Type*} [DecidableEq V]
    (w : VertexSeq V) (v : V) (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v with
  | singleton x => grind [takeUntil, IsWalk.singleton]
  | cons w u hw hneq ih => grind [takeUntil, IsWalk.cons]

lemma loopErase_iswalk {V : Type*} [DecidableEq V] (w : VertexSeq V) :
    IsWalk w.loopErase := by grind[nodup_iswalk, loopErase_nodup]

/-- The list of vertices visited by the walk, in order. -/
def support (w : Walk α) : List α := w.seq.toList

abbrev head (w : Walk α) : α := w.seq.head
abbrev tail (w : Walk α) : α := w.seq.tail
abbrev length (w : Walk α) : ℕ := w.seq.length


def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.valid (by aesop)⟩

abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail, valid := by {
    have: IsWalk w.seq := by exact w.valid
    generalize h_eq1: w.seq  = p
    have: IsWalk p := by grind
    cases this
    · aesop
    · simpa [VertexSeq.dropTail]
    }
  }

lemma two_seqs_append_of {V : Type*} (w1 w2 : Walk V) (hneq : w1.tail ≠ w2.head) :
  IsWalk (w1.seq.append w2.seq) := by
  cases w1; cases w2
  simp_all only [Walk.tail, Walk.head, ne_eq]
  fun_induction seq.append seq_1
  · exact IsWalk.cons w v valid hneq
  · refine IsWalk.cons (w.append w2) v ?_ ?_
    apply ih1 <;> simp_all only [forall_const, con_head_eq, not_false_eq_true]
    · exact iswalk_prefix w2 v valid_1
    · simp_all only [forall_const, con_head_eq, tail_on_tail, ne_eq, tail_neq_of_iswalk,
      not_false_eq_true]

lemma dropTail_head {V : Type*} (w : Walk V) :
    w.dropTail.head = w.head := by
  cases w with
  | mk seq valid =>
      cases seq <;> simp [Walk.head, VertexSeq.dropTail, VertexSeq.head]


omit [DecidableEq α]
lemma len_zero_of_drop_tail_eq_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
  w.length = 0 := by
  cases w
  induction valid
  · exact Nat.eq_zero_of_add_eq_zero_left rfl
  · exact Nat.eq_zero_of_not_pos fun a ↦ hneq h

lemma head_eq_tail_of_length_zero (w : Walk α)
    (h : w.length = 0) : w.head = w.tail := by
  cases w with
  | mk seq valid =>
    cases valid <;> simp_all [Walk.length, Walk.head, Walk.tail, VertexSeq.head,VertexSeq.tail]

/-
Convert a walk to path by removing all loops
-/
def IsPath (w : Walk α) : Prop := w.support.Nodup

abbrev toPath (w : Walk α) : Walk α :=
  {seq := w.seq.loopErase, valid := loopErase_iswalk w.seq}

theorem toPath_isPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by
  unfold IsPath toPath support
  simpa using loopErase_nodup w.seq

lemma tail_toPath [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind [tail_loopErase]

lemma head_toPath [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind [head_loopErase]

def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail

def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
    if      h1: w1.length = 0 then w2
    else { seq := w1.dropTail.seq.append w2.seq, valid := by
    { apply two_seqs_append_of
      rw [← h]
      by_contra!
      absurd h1
      apply len_zero_of_drop_tail_eq_tail
      exact this
    } }

def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse, valid := by{
    cases w
    induction valid
    · grind [VertexSeq.reverse, IsWalk]
    · simp_all only [VertexSeq.reverse]
      have h: IsWalk (VertexSeq.singleton u) := by exact IsWalk.singleton u
      apply two_seqs_append_of (⟨VertexSeq.singleton u, h⟩ : Walk α) (⟨w.reverse, hw_ih⟩ : Walk α)
      simp_all only [Walk.head, Walk.tail]
      unfold VertexSeq.tail
      aesop
  }
  }

@[simp] lemma head_reverse (w : Walk α) : (w.reverse).head = w.tail := by
  simp [reverse, head]

@[simp] lemma tail_reverse (w : Walk α) : (w.reverse).tail = w.head := by
  simp [reverse, tail]

@[simp] theorem head_on_head {V : Type*} (w1 w2 : Walk V)
    (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  unfold Walk.append
  split
  · grind [head_eq_tail_of_length_zero]
  · simp [Walk.head]

@[simp] theorem tail_on_tail (w1 w2 : Walk α)
    (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by
  unfold Walk.append
  split <;> simp [Walk.tail]

end Walk
