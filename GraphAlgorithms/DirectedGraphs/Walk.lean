import GraphAlgorithms.Core.Walk
import GraphAlgorithms.DirectedGraphs.SimpleDiGraphs

-- Authors: Sorrachai Yingchareonthawornchai

namespace Walk

set_option tactic.hygienic false

/-- A walk `w` is a walk in graph `G` if every consecutive pair of vertices
    forms an edge in `G`, and the starting vertex lies in the vertex set. -/
inductive IsWalkIn {V : Type*} (G : SimpleDiGraph V) : Walk V → Prop
  | singleton (v : V) (hv : v ∈ G.vertexSet)
    : IsWalkIn G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk V) (u : V)
      (hw   : IsWalkIn G w)
      (hedg : (w.tail, u) ∈ G.edgeSet)
    : IsWalkIn G (w.append_single u (by have : ∀ e ∈ G.edgeSet, e.1 ≠ e.2 :=  G.loopless; grind))

/-- A walk of positive length in G has a first outgoing edge from its head.
    Usage:
    - Helper lemma to prove `BreadFirstSearch.bfs_complete_aux` -/
lemma isWalkIn_first_edge {V : Type*}
    (G : SimpleDiGraph V) (w : Walk V)
    (hw : Walk.IsWalkIn G w) (hlen : w.length > 0) :
    ∃ a₁ ∈ w.support, a₁ ≠ w.head ∧ (w.head, a₁) ∈ G.edgeSet := by
  induction hw with
  | singleton v hv => exact absurd hlen (by grind [VertexSeq.length])
  | cons w' u' hw_inner hedg ih =>
      by_cases h' : w'.length = 0
      · -- w' is a singleton: w'.head = w'.tail, direct edge (w.head, u')
        have heq : w'.head = w'.tail := Walk.head_eq_tail_of_length_zero w' h'
        exact ⟨u',
          by simp [Walk.support, Walk.append_single, VertexSeq.toList],
          (G.loopless _ (heq ▸ hedg)).symm,
          heq ▸ hedg⟩
      · -- w'.length > 0: IH gives first edge of w', lift membership to w
        -- ih : w'.length > 0 → ∃ a₁ ∈ w'.support, a₁ ≠ w'.head ∧ (w'.head, a₁) ∈ G.edgeSet
        obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ := ih (Nat.pos_of_ne_zero h')
        exact ⟨a₁,
          by simp only [support, append_single, VertexSeq.toList, List.mem_cons];
              exact Or.inr ha₁_supp,
          ha₁_neq,
          ha₁_edge⟩

end Walk
