import GraphAlgorithms.Core.Walk
import GraphAlgorithms.UndirectedGraphs.SimpleGraphs


-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
variable {α : Type*} [DecidableEq α]

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


open scoped SimpleGraph

@[grind] inductive VertexSeq.IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : s(w.tail, u) ∈ E(G)) :
      IsVertexSeqIn G (.cons w u)

grind_pattern VertexSeq.IsVertexSeqIn.singleton => VertexSeq.IsVertexSeqIn G (.singleton v)
grind_pattern VertexSeq.IsVertexSeqIn.cons => VertexSeq.IsVertexSeqIn G (.cons w u)

abbrev VertexSeq.vertex_seq_in (w : VertexSeq α) (G : SimpleGraph α) := IsVertexSeqIn G w
abbrev VertexSeq.edgeSet (w : VertexSeq α) : Finset (Edge α) :=
  match w with
  | .singleton _ => ∅
  | .cons w u => w.edgeSet ∪ {s(w.tail, u)}

@[simp] lemma VertexSeq.is_vertex_seq_in_iff (G : SimpleGraph α) (p : VertexSeq α) :
  IsVertexSeqIn G p ↔ p.head ∈ V(G) ∧ p.edgeSet ⊆ E(G) := by
  induction p <;> grind


namespace Walk
open VertexSeq

abbrev edgeSet (w : Walk α) : Finset (Edge α) := w.seq.edgeSet

lemma iswalk_in_iff (G : SimpleGraph α) (w : Walk α) :
  IsVertexSeqIn G w.seq ↔ w.head ∈ V(G) ∧ w.edgeSet ⊆ E(G) := by
  grind [VertexSeq.is_vertex_seq_in_iff]

@[grind →]
lemma prepend_vertex_seq_in (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) (u : α)
    (hedg : s(u, w.head) ∈ G.edgeSet) :
    IsVertexSeqIn G
      ((VertexSeq.singleton u).append w) := by
    induction hw
    · refine IsVertexSeqIn.cons (VertexSeq.singleton u) v ?_ hedg
      refine IsVertexSeqIn.singleton u ?_
      have:= G.incidence; aesop
    · simp_all only [VertexSeq.con_head_eq, forall_const]
      refine IsVertexSeqIn.cons ((VertexSeq.singleton u).append w_1) u_1 hw_ih ?_
      aesop

lemma prepend_walk_valid (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) (u : α)
    (hedg : s(u, w.head) ∈ G.edgeSet) :
    let w' := (VertexSeq.singleton u).append w
    IsVertexSeqIn G w' ∧ IsWalk w' := by grind

@[grind →]
lemma reverse_iswalk_in (G : SimpleGraph α) (w : VertexSeq α) (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.reverse := by
    induction hw <;> grind [VertexSeq.is_vertex_seq_in_iff]

lemma reverse_walk_valid (G : SimpleGraph α) (w : VertexSeq α)
  (hw : (w.vertex_seq_in G) ∧ IsWalk w) :
    (w.reverse.vertex_seq_in G) ∧ IsWalk w.reverse := by grind

@[grind →]
lemma dropTail_iswalk_in (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.dropTail := by induction hw <;> grind

lemma dropTail_walk_valid (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) :
    IsVertexSeqIn G w.dropTail ∧ IsWalk w.dropTail := by grind

@[grind →]
lemma takeUntil_iswalk_in (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw_in : IsVertexSeqIn G w) (hw : IsWalk w) :
    IsVertexSeqIn G (w.takeUntil v h) := by
  induction hw_in generalizing v with
  | singleton u hu => grind
  | cons w u hw_in he ih => by_cases h2 : v ∈ w.toList <;> grind

lemma takeUntil_walk_valid (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) :
    IsVertexSeqIn G (w.takeUntil v h) ∧ IsWalk (w.takeUntil v h) := by grind

@[grind →]
lemma iswalk_in_subgraph (H G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn H w) (hsub : SimpleGraph.subgraphOf H G) :
    IsVertexSeqIn G w := by
  induction hw <;> grind

lemma iswalk_valid_in_subgraph (H G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn H w ∧ IsWalk w) (hsub : SimpleGraph.subgraphOf H G) :
    IsVertexSeqIn G w ∧ IsWalk w := by exact ⟨iswalk_in_subgraph H G w hw.1 hsub, hw.2⟩

lemma two_seqs_append_iswalk_in (G : SimpleGraph α)
    (w1 w2 : VertexSeq α)
    (h1 : IsVertexSeqIn G w1) (h2 : IsVertexSeqIn G w2)
    (hedg : s(w1.tail, w2.head) ∈ G.edgeSet) :
    IsVertexSeqIn G (w1.append w2) := by
  induction h2 generalizing w1 h1 <;> grind

lemma append_iswalk_in (G : SimpleGraph α)
    (w1 w2 : Walk α)
    (h1 : IsVertexSeqIn G w1.seq) (h2 : IsVertexSeqIn G w2.seq)
    (h : w1.tail = w2.head) :
    IsVertexSeqIn G (Walk.append w1 w2 h).seq := by
    unfold append
    by_cases h1 : w1.length = 0
    · grind
    · split_ifs; apply two_seqs_append_iswalk_in <;> grind

lemma toPath_iswalk_in (G : SimpleGraph α) (w : Walk α)
    (hw : IsVertexSeqIn G w.seq) :
    IsVertexSeqIn G w.toPath.seq := by
  suffices h : ∀ n : ℕ, ∀ w : Walk α, w.length = n →
      IsVertexSeqIn G w.seq → IsVertexSeqIn G w.toPath.seq by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen hw; cases w; cases valid with
    | singleton v => grind
    | cons w0 u hw0 hneq =>
        have hw0_in : IsVertexSeqIn G w0 := by grind
        have hedg : s(w0.tail, u) ∈ G.edgeSet := by grind
        have hw0lt : (⟨w0, hw0⟩ : Walk α).length < n := by grind
        by_cases hmem : u ∈ w0.toList
        · let p : Walk α := ⟨w0.takeUntil u hmem, takeUntil_iswalk w0 u hmem hw0⟩
          have hp_in : IsVertexSeqIn G p.seq := by grind
          have hplt : p.length < n := by grind [VertexSeq.takeUntil_length_le]
          simpa [Walk.toPath, VertexSeq.loopErase, hmem, p] using
            ih p.length hplt p rfl hp_in
        · have hw0P : IsVertexSeqIn G (⟨w0, hw0⟩ : Walk α).toPath.seq := by
            exact ih _ hw0lt (⟨w0, hw0⟩ : Walk α) rfl hw0_in
          have hcons : IsVertexSeqIn G ((⟨w0, hw0⟩ : Walk α).toPath.seq.cons u) := by
            refine IsVertexSeqIn.cons _ _ hw0P ?_
            simpa [Walk.tail_toPath] using hedg
          grind


end Walk
