import GraphAlgorithms.UndirectedGraphs.Walk.EdgeSet

-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
variable {α : Type*} [DecidableEq α]

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open scoped SimpleGraph

namespace VertexSeq

/-! ### Vertex sequences in an undirected graph -/

/-- A vertex sequence is realized in `G` if its start vertex is in `G` and each step is an edge. -/
@[grind] inductive IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : s(w.tail, u) ∈ E(G)) :
      IsVertexSeqIn G (.cons w u)

namespace IsVertexSeqIn

/-- Characterize graph-realized vertex sequences by head membership and edge-set inclusion. -/
@[simp, grind =] lemma iff (G : SimpleGraph α) (p : VertexSeq α) :
    IsVertexSeqIn G p ↔ p.head ∈ V(G) ∧ p.edgeSet ⊆ E(G) := by
  induction p <;> grind

/-- Prepending a vertex along an edge preserves graph realization. -/
@[grind →]
lemma prepend (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) (u : α)
    (hedg : s(u, w.head) ∈ G.edgeSet) :
    IsVertexSeqIn G ((VertexSeq.singleton u).append w) := by
  induction hw
  · refine IsVertexSeqIn.cons (VertexSeq.singleton u) v ?_ hedg
    refine IsVertexSeqIn.singleton u ?_
    have:= G.incidence; aesop
  · grind

/-- Reversing an undirected graph-realized sequence preserves graph realization. -/
@[grind →]
lemma reverse (G : SimpleGraph α) (w : VertexSeq α) (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.reverse := by induction hw <;> grind

/-- Dropping the tail preserves graph realization. -/
@[grind →]
lemma dropTail (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.dropTail := by induction hw <;> grind

/-- Taking a prefix at a vertex preserves graph realization. -/
@[grind →]
lemma takeUntil (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw_in : IsVertexSeqIn G w) (hw : IsWalk w) :
    IsVertexSeqIn G (w.takeUntil v h) := by induction hw <;> grind

/-- Dropping to a suffix at a vertex preserves graph realization. -/
@[grind →]
lemma dropUntil (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw_in : IsVertexSeqIn G w) (hw : IsWalk w) :
    IsVertexSeqIn G (w.dropUntil v h) := by
  induction hw_in generalizing v with
  | singleton u hu => grind
  | cons w u hw_in he ih => by_cases h2 : v ∈ w.toList <;> grind

/-- Graph realization is monotone under passing to a supergraph. -/
@[grind →]
lemma mono (H G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn H w) (hsub : SimpleGraph.subgraphOf H G) :
    IsVertexSeqIn G w := by induction hw <;> grind

/-- Appending two graph-realized sequences along an edge preserves graph realization. -/
lemma append (G : SimpleGraph α)
    (w1 w2 : VertexSeq α)
    (h1 : IsVertexSeqIn G w1) (h2 : IsVertexSeqIn G w2)
    (hedg : s(w1.tail, w2.head) ∈ G.edgeSet) :
    IsVertexSeqIn G (w1.append w2) := by
  induction h2 generalizing w1 h1 <;> grind

/-- The tail of a graph-realized vertex sequence lies in the graph's vertex set. -/
lemma tail_mem {G : SimpleGraph α} {w : VertexSeq α}
    (hw : IsVertexSeqIn G w) :
    w.tail ∈ G.vertexSet := by induction hw <;> grind

/-- If the graph has no edges, every graph-realized vertex sequence has length zero. -/
lemma length_eq_zero_of_no_edges
    {G : SimpleGraph α} (hE : G.edgeSet = ∅) {w : VertexSeq α}
    (hw : IsVertexSeqIn G w) :
    w.length = 0 := by induction hw <;> grind

end IsVertexSeqIn

end VertexSeq
