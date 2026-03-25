import GraphAlgorithms.Core.Walk
import GraphAlgorithms.UndirectedGraphs.SimpleGraphs

-- Authors: Sorrachai Yingchareonthawornchai

namespace Walk

set_option tactic.hygienic false

inductive IsWalkIn {V : Type*} (G : SimpleGraph V) : Walk V → Prop
  | singleton (v : V) (hv : v ∈ G.vertexSet)
    : IsWalkIn G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk V) (u : V)
      (hw   : IsWalkIn G w)
      (hedg : s(w.tail, u) ∈ G.edgeSet)
    : IsWalkIn G (w.append_single u (by
        have : ∀ e ∈ G.edgeSet, ¬ e.IsDiag :=  G.loopless;
        by_contra!;subst this;apply this at hedg
        contradiction
      ))

end Walk
