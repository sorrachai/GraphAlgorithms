import GraphAlgorithms.UndirectedGraphs.Walk.IsVertexSeqIn

-- Authors: Sorrachai Yingchareonthawornchai and Weixuan Yuan
variable {α : Type*} [DecidableEq α]

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open scoped SimpleGraph

namespace SimpleGraph

/-! ### Walks in an undirected graph -/

/-- A `Walk` is in a simple graph when its underlying vertex sequence is realized in the graph. -/
abbrev IsWalkIn (G : SimpleGraph α) (w : Walk α) : Prop :=
  VertexSeq.IsVertexSeqIn G w.seq

namespace IsWalkIn

/-- Characterize graph-realized walks by head membership and edge-set inclusion. -/
@[grind =] lemma iff (G : SimpleGraph α) (w : Walk α) :
    IsWalkIn G w ↔ w.head ∈ V(G) ∧ w.edgeSet ⊆ E(G) := by grind

/-- A walk is in `G` with edge `e` deleted iff it is in `G` and does not use `e`. -/
@[grind =] lemma deleteEdge_iff (G : SimpleGraph α) (e : Edge α) (w : Walk α) :
    IsWalkIn (SimpleGraph.deleteEdge G e) w ↔
      IsWalkIn G w ∧ e ∉ w.edgeSet := by grind

/-- Reversing an undirected graph-realized walk preserves graph realization. -/
@[grind →] lemma reverse (G : SimpleGraph α) (w : Walk α) (hw : IsWalkIn G w) :
    IsWalkIn G w.reverse := by grind

/-- Dropping the tail preserves graph realization. -/
@[grind →] lemma dropTail (G : SimpleGraph α) (w : Walk α) (hw : IsWalkIn G w) :
    IsWalkIn G w.dropTail := by grind

/-- Taking a walk prefix at a support vertex preserves graph realization. -/
@[grind →] lemma takeUntil (G : SimpleGraph α)
    (w : Walk α) (hw : IsWalkIn G w) (v : α) (h : v ∈ w.support) :
    IsWalkIn G (w.takeUntil v h) := by grind

/-- Dropping to a walk suffix at a support vertex preserves graph realization. -/
@[grind →] lemma dropUntil (G : SimpleGraph α)
    (w : Walk α) (hw : IsWalkIn G w) (v : α) (h : v ∈ w.support) :
    IsWalkIn G (w.dropUntil v h) := by grind

/-- Appending graph-realized walks with matching endpoints preserves graph realization. -/
@[grind ←] lemma append (G : SimpleGraph α)
    (w1 w2 : Walk α)
    (h1 : IsWalkIn G w1) (h2 : IsWalkIn G w2)
    (h : w1.tail = w2.head) :
    IsWalkIn G (Walk.append w1 w2 h) := by
  unfold Walk.append; by_cases hlen : w1.length = 0
  · grind
  · have happ := VertexSeq.IsVertexSeqIn.append G w1.dropTail.seq w2.seq
      (dropTail G w1 h1) h2 (by grind[Walk.dropTail_edges])
    grind

/-- Converting a graph-realized walk to a path preserves graph realization. -/
lemma toPath (G : SimpleGraph α) (w : Walk α)
    (hw : IsWalkIn G w) :
    IsWalkIn G w.toPath := by
  suffices h : ∀ n : ℕ, ∀ w : Walk α, w.length = n →
      IsWalkIn G w → IsWalkIn G w.toPath by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen hw; cases w; cases valid with
    | singleton v => grind
    | cons w0 u hw0 hneq =>
        have hw0_in : VertexSeq.IsVertexSeqIn G w0 := by grind
        have hedg : s(w0.tail, u) ∈ G.edgeSet := by grind
        have hw0lt : (⟨w0, hw0⟩ : Walk α).length < n := by grind
        by_cases hmem : u ∈ w0.toList
        · let p : Walk α := ⟨w0.takeUntil u hmem, Walk.valid_takeUntil w0 u hmem hw0⟩
          have hp_in : IsWalkIn G p := by
            simpa [IsWalkIn, p] using
              VertexSeq.IsVertexSeqIn.takeUntil G w0 u hmem hw0_in hw0
          have hplt : p.length < n := by grind [VertexSeq.takeUntil_length_le]
          simpa [Walk.toPath, VertexSeq.loopErase, hmem, p] using
            ih p.length hplt p rfl hp_in
        · have hw0P : IsWalkIn G (⟨w0, hw0⟩ : Walk α).toPath := by
            exact ih _ hw0lt (⟨w0, hw0⟩ : Walk α) rfl hw0_in
          grind

end IsWalkIn

end SimpleGraph
