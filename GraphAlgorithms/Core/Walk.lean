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
  | cons w _   => VertexSeq.head w

@[simp] lemma con_heqad_eq {V : Type*} (w : VertexSeq V) (u : V) :
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

@[simp] lemma tail_on_tail {V : Type*} (p q : VertexSeq V) : (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [VertexSeq.tail]

@[simp] lemma head_on_head {V : Type*} (p q : VertexSeq V) : (p.append q).head = p.head := by
  fun_induction append <;> simp_all

@[simp] lemma tail_on_tail_singleton {V : Type*} (p : VertexSeq V) (x : V) :
  (p.append (.singleton x)).tail = x := by
  unfold append
  unfold tail
  split <;> grind

@[simp] lemma head_on_head_singleton {V : Type*} (p : VertexSeq V) (x : V) :
  ((VertexSeq.singleton x).append p).head = x := by
  unfold append
  unfold head
  split <;> aesop

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

@[simp] theorem iswalk_prefix {V : Type*} (w2 : VertexSeq V) (v : V)
(valid : IsWalk (w2.cons v)) : IsWalk w2 := by cases valid; grind

@[simp] theorem tail_neq_of_iswalk {V : Type*} (w2 : VertexSeq V) (v : V)
(valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by cases valid; grind

open VertexSeq
/-- The list of vertices visited by the walk, in order. -/
def support (w : Walk α) : List α := w.seq.toList

abbrev head (w : Walk α) : α := w.seq.head
abbrev tail (w : Walk α) : α := w.seq.tail
abbrev length (w : Walk α) : ℕ := w.seq.length

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
    apply ih1 <;> simp_all only [forall_const, con_heqad_eq, not_false_eq_true]
    · exact iswalk_prefix w2 v valid_1
    · simp_all only [forall_const, con_heqad_eq, tail_on_tail, ne_eq, tail_neq_of_iswalk,
      not_false_eq_true]

omit [DecidableEq α]
lemma len_zero_of_drop_tail_eq_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
  w.length = 0 := by
  cases w
  induction valid
  · exact Nat.eq_zero_of_add_eq_zero_left rfl
  · exact Nat.eq_zero_of_not_pos fun a ↦ hneq h

def IsPath (w : Walk α) : Prop := w.support.Nodup

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

def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  ⟨w.seq.cons u, .cons w.seq u w.valid (by aesop)⟩

end Walk
