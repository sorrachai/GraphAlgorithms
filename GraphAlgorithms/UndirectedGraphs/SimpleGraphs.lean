import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

-- Undirected Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

abbrev Edge := Sym2

structure SimpleGraph (α : Type*) where
  vertexSet : Finset α
  edgeSet   : Finset (Edge α)
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  loopless :  ∀ e ∈ edgeSet, ¬ e.IsDiag

open Finset

namespace SimpleGraphs

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => SimpleGraph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => SimpleGraph.edgeSet G

abbrev IncidentEdgeSet (G : SimpleGraph α) (s : α) :
  Finset (Edge α) := {e ∈ E(G) | s ∈ e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/

scoped notation "δ(" G "," v ")" => SimpleGraph.IncidentEdgeSet G v

abbrev Neighbors (G : SimpleGraph α) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e ∧ u ∈ e ∧ u ≠ s}

/-- `N(G,v)` denotes the `neighbors` of a graph `G`. -/
scoped notation "N(" G "," v ")" => SimpleGraph.Neighbors G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)

abbrev subgraphOf (H G : SimpleGraph α) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => SimpleGraph.subgraphOf

/- VertexSeq as a non-empty seq -/
inductive VertexSeq (V : Type*)
  | singleton (v : V) : VertexSeq V
  | cons (w : VertexSeq V) (v : V) : VertexSeq V

/-- The list of vertices visited by the walk, in order. -/
def VertexSeq.toList : VertexSeq α →  List α
  | .singleton v => [v]
  | .cons p v => p.toList ++ [v]

/-- The first node does not count in the sequence. -/
@[simp] def VertexSeq.length {V : Type*} : VertexSeq V → ℕ
  | singleton _ => 0
  | cons w _   => 1 + w.length

def VertexSeq.tail {V : Type*} : VertexSeq V → V
  | singleton v => v
  | cons _ v   => v

@[simp] lemma VertexSeq.con_tail_eq {V: Type*} (w : VertexSeq V) (u : V) :
  (w.cons u).tail = u := rfl


def VertexSeq.head {V : Type*} : VertexSeq V → V
  | singleton v => v
  | cons w _   => VertexSeq.head w

@[simp] lemma VertexSeq.con_heqad_eq {V: Type*} (w : VertexSeq V) (u : V) :
  (w.cons u).head = w.head := rfl


def VertexSeq.dropTail {V : Type*} : VertexSeq V → VertexSeq V
  | singleton v => .singleton v -- singleton remains singleton
  | cons w _   => w

def VertexSeq.dropHead {V : Type*} : VertexSeq V → VertexSeq V
  | singleton v => .singleton v -- singleton remains singleton
  | cons (singleton _) v => .singleton v
  | cons w v   => VertexSeq.cons (VertexSeq.dropHead w) v

def VertexSeq.append {V : Type*} : VertexSeq V →  VertexSeq V → VertexSeq V
  | w, .singleton v => .cons w v
  | w, .cons w2 v   => .cons (append w w2) v

@[simp] lemma tail_on_tail {V : Type*} (p q : VertexSeq V): (p.append q).tail = q.tail := by
  fun_induction VertexSeq.append <;> simp_all [VertexSeq.tail]

@[simp] lemma head_on_head {V : Type*} (p q : VertexSeq V): (p.append q).head = p.head := by
  fun_induction VertexSeq.append <;> simp_all

@[simp] lemma tail_on_tail_singleton {V : Type*} (p : VertexSeq V) (x : V): (p.append (.singleton x)).tail = x := by
  unfold VertexSeq.append
  unfold VertexSeq.tail
  split <;> aesop

@[simp] lemma head_on_head_singleton {V : Type*} (p : VertexSeq V) (x : V): ((VertexSeq.singleton x).append p).head = x := by
  unfold VertexSeq.append
  unfold VertexSeq.head
  split <;> aesop


inductive IsWalk {V : Type*} : VertexSeq V → Prop
  | singleton (v : V) : IsWalk (VertexSeq.singleton v)
  | cons  (w : VertexSeq V) (u : V)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u)   -- non-stuttering
    : IsWalk (VertexSeq.cons w u)

structure Walk (V : Type*) where
  seq : VertexSeq V
  valid : IsWalk seq

open VertexSeq
/-- The list of vertices visited by the walk, in order. -/
def Walk.support (w : Walk α) : List α := w.seq.toList

abbrev Walk.head (w : Walk α) : α := w.seq.head
abbrev Walk.tail (w : Walk α) : α := w.seq.tail
abbrev Walk.length (w : Walk α) : ℕ := w.seq.length

abbrev Walk.dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail, valid := by {
    have: IsWalk w.seq := by exact w.valid
    generalize h_eq1: w.seq  = p
    have: IsWalk p := by grind
    cases this
    · aesop
    · simpa [VertexSeq.dropTail]
    }
  }

private lemma two_seqs_append_of {V : Type*} (w1 w2 : Walk V) (hneq : w1.tail ≠ w2.head):
  IsWalk (w1.seq.append w2.seq) := by
  cases w1
  cases w2
  simp_all [Walk.tail,Walk.head]
  fun_induction seq.append seq_1
  · exact IsWalk.cons w v valid hneq
  · have: IsWalk w2 := by
        cases valid_1
        assumption
    have: w2.tail ≠ v := by
        cases valid_1
        assumption
    simp [VertexSeq.head] at hneq
    simp_all [forall_const]
    refine IsWalk.cons (w.append w2) v ih1 ?_
    simpa only [tail_on_tail, ne_eq]

lemma drop_tail_eq_tail_len_zero (w : Walk α) (h : w.dropTail.tail = w.tail):
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
      apply drop_tail_eq_tail_len_zero
      exact this
    } }

end SimpleGraphs
