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


end Walk
