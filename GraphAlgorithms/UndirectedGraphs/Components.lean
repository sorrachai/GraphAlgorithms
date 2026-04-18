import GraphAlgorithms.UndirectedGraphs.Walk
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Components (undirected simple)
-- Authors: Weixuan Yuan

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

namespace SimpleGraph
open scoped SimpleGraph
open scoped BigOperators
open VertexSeq

/-- Number of vertices in a finite simple graph. -/
abbrev numVertices (G : SimpleGraph α) : Nat := G.vertexSet.card
/-- Number of edges in a finite simple graph. -/
abbrev numEdges (G : SimpleGraph α) : Nat := G.edgeSet.card

/-! ## Reachability, connectivity, acyclicity -/

/-- `u` can reach `v` in `G` iff there exists a walk in `G` from `u` to `v`. -/
@[grind] def Reachable (G : SimpleGraph α) (u v : α) : Prop :=
  ∃ w : Walk α, IsVertexSeqIn G w.seq ∧ w.head = u ∧ w.tail = v

/-- `G` is connected iff every two vertices in `vertexSet` are reachable. -/
@[grind] def Connected (G : SimpleGraph α) : Prop :=
  ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet → Reachable G u v

/-- `G` is acyclic iff it contains no simple cycle. -/
@[grind] def Acyclic (G : SimpleGraph α) : Prop :=
  ¬ ∃ w : Walk α, IsVertexSeqIn G w.seq ∧ Walk.IsCycle w

/-- Reachable is an equivalence relation. -/
@[simp, grind →] theorem reachable_refl (G : SimpleGraph α) (v : α) (hv : v ∈ G.vertexSet) :
    Reachable G v v := by
  refine ⟨⟨VertexSeq.singleton v, IsWalk.singleton v⟩, ?_, rfl, rfl⟩
  exact IsVertexSeqIn.singleton v hv

@[simp, grind →] theorem reachable_symm (G : SimpleGraph α) (u v : α) (huv : Reachable G u v) :
    Reachable G v u := by
  rcases huv with ⟨w, hw, hu, hv⟩
  refine ⟨w.reverse, ?_, ?_, ?_⟩ <;> grind

@[simp, grind →] theorem reachable_trans (G : SimpleGraph α) (u v w : α)
    (huv : Reachable G u v) (hvw : Reachable G v w) : Reachable G u w := by
  rcases huv with ⟨w1, h1, hu, hv⟩; rcases hvw with ⟨w2, h2, hv', hw⟩
  have h : w1.tail = w2.head := by grind
  refine ⟨Walk.append w1 w2 h, Walk.append_iswalk_in G w1 w2 h1 h2 h, ?_, ?_⟩
  <;> grind


/-- If `H` is a subgraph of `G` and `u` is reachable from `v` in `H`,
  then `u` is reachable from `v` in `G`. -/
lemma reachable_in_subgraph {H G : SimpleGraph α}
    (hsub : SimpleGraph.subgraphOf H G) {u v : α}
    (hreach : Reachable H u v) : Reachable G u v := by
  grind [Walk.iswalk_in_subgraph, Reachable]

/-- If `H` is a subgraph of `G` and `G` is acyclic, then `H` is acyclic. -/
lemma subgraph_acyclicity {H G : SimpleGraph α}
    (hsub : SimpleGraph.subgraphOf H G)
    (hacyG : Acyclic G) : Acyclic H := by
  grind [Acyclic, Walk.iswalk_in_subgraph]

/-! ## Components as reachable classes -/

/-- Vertex type restricted to vertices of `G`. -/
abbrev Vertex (G : SimpleGraph α) := {v : α // v ∈ G.vertexSet}

/-- Reachability relation on `Vertex G`. -/
abbrev ReachableOn (G : SimpleGraph α) (u v : Vertex G) : Prop :=
  Reachable G u.1 v.1

/-- Setoid induced by graph reachability on vertices of `G`. -/
def reachableSetoid (G : SimpleGraph α) : Setoid (Vertex G) where
  r := ReachableOn G
  iseqv := by refine ⟨?refl, ?symm, ?trans⟩ <;> grind

/- `componentOf G v` is the connected component containing `v`. -/
@[simp, grind] noncomputable def componentOf (G : SimpleGraph α) (v : Vertex G) : Finset α := by
  classical
  exact G.vertexSet.filter (fun u => Reachable G v.1 u)

/- The set of all connected components of `G`. -/
@[simp, grind] noncomputable def components (G : SimpleGraph α) : Finset (Finset α) := by
  classical
  exact (G.vertexSet.attach.image (fun v => componentOf G v))

/- Number of connected components of `G`. -/
@[simp, grind] noncomputable def numComponents (G : SimpleGraph α) : Nat := by
  classical
  exact (components G).card

@[simp, grind] noncomputable def componentEdgeSetOf (G : SimpleGraph α) (C : Finset α) :
  Finset (Edge α) := by classical
  exact {e ∈ G.edgeSet | ∀ v ∈ e, v ∈ C}

/-! ## Basic component lemmas -/

@[simp, grind =] lemma mem_componentOf_iff (G : SimpleGraph α) (v : Vertex G) (u : α) :
    u ∈ componentOf G v ↔ u ∈ G.vertexSet ∧ Reachable G v u := by grind

@[simp, grind .] lemma self_mem_componentOf (G : SimpleGraph α) (v : Vertex G) :
    v.1 ∈ componentOf G v := by grind

@[simp, grind →] lemma component_subset (G : SimpleGraph α)
    {C : Finset α} (hC : C ∈ components G) :
    C ⊆ G.vertexSet := by grind

@[simp, grind →] lemma component_nonEmpty {G : SimpleGraph α}
  {C : Finset α} (hC : C ∈ components G) : C.Nonempty := by
  unfold components at hC
  simp only [componentOf, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hC
  rcases hC with ⟨a, ha, h⟩; use a
  grind [Reachable]

@[simp, grind →] lemma component_eq_componentOf_mem (G : SimpleGraph α)
    {C : Finset α} (hC : C ∈ components G) {u : α} (hu : u ∈ C) :
    C = componentOf G ⟨u, component_subset G hC hu⟩ := by grind

@[simp, grind →] lemma componentOf_eq_of_reachable (G : SimpleGraph α)
    (u v : Vertex G) (huv : Reachable G u.1 v.1) :
    componentOf G u = componentOf G v := by grind

@[simp, grind .] lemma components_pairwise_disjoint (G : SimpleGraph α) :
    ((components G : Finset (Finset α)) : Set (Finset α)).Pairwise
      (fun C D => Disjoint C D) := by intro; grind[Finset.disjoint_left]

@[simp, grind =] lemma components_union_eq_vertexSet (G : SimpleGraph α) :
    (components G).biUnion (fun C => C) = G.vertexSet := by
  ext u; constructor
  · grind
  · intro hu; have hC : componentOf G ⟨u, hu⟩ ∈ components G := by grind
    grind

@[simp, grind →] lemma reachable_of_edge (G : SimpleGraph α) {u v : α}
    (he : s(u, v) ∈ G.edgeSet) : Reachable G u v := by
  let w : Walk α :=
    ⟨VertexSeq.cons (VertexSeq.singleton u) v,
      IsWalk.cons (VertexSeq.singleton u) v
        (IsWalk.singleton u) (by grind)⟩
  refine ⟨w, ?_, rfl, rfl⟩
  have hu : u ∈ G.vertexSet := G.incidence _ he _ (by simp); grind


/-! ## Induced subgraphs and component-wise counting identities -/

@[simp, grind] noncomputable def inducedSubgraph (G : SimpleGraph α) (C : Finset α) :
  SimpleGraph α := by classical
  classical
  refine
    { vertexSet := C
      edgeSet := {e ∈ G.edgeSet | ∀ v ∈ e, v ∈ C}
      incidence := ?_
      loopless := ?_ }
  · grind
  · intro e he
    exact G.loopless e (Finset.mem_filter.mp he).1

@[local grind =] lemma sum_numVertices_components (G : SimpleGraph α) :
    (∑ C ∈ components G, numVertices (inducedSubgraph G C)) = numVertices G := by
  grind [Set.PairwiseDisjoint, Finset.card_biUnion, components_union_eq_vertexSet]

@[local grind =] lemma sum_Edges_components (G : SimpleGraph α) :
    (∑ C ∈ components G, numEdges (inducedSubgraph G C)) = numEdges G := by
  classical
  have edge_mem_some_componentEdgeSet :
      ∀ e, e ∈ G.edgeSet → ∃ C ∈ components G, e ∈ componentEdgeSetOf G C := by
    intro e
    refine Sym2.inductionOn e ?_
    intro a b he
    have haV : a ∈ G.vertexSet := G.incidence _ he _ (by simp)
    have : componentOf G ⟨a, haV⟩ ∈ components G := by grind
    grind [reachable_of_edge]
  have componentEdgeSets_pairwise_disjoint :
      ((components G : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint
        (componentEdgeSetOf G) := by
    intro C hC D hD hne; refine Finset.disjoint_left.mpr ?_; intro e heC heD
    have := Sym2.out_fst_mem e; grind [Sym2.out_fst_mem]
  have componentEdgeSets_biUnion_eq_edgeSet :
      (components G).biUnion (componentEdgeSetOf G) = G.edgeSet := by
    grind
  grind [Finset.card_biUnion]




/-! ## Lemmas for numComponents
  1. If H, G have the same vertex set and every reachable pair in G is reachable in H,
  then numComponents G ≥ numComponents H.
  2. If H, G have the same vertex set and every reachable pair in G is reachable in H, and
     numComponents G = numComponents H, then every reachable pair in H is reachable in G.
-/

lemma numComponents_mono
    {G H : SimpleGraph α}
    (hV : V(G) = V(H))
    (hReach : ∀ u v : α,
      u ∈ G.vertexSet → v ∈ G.vertexSet →
      Reachable G u v → Reachable H u v) :
    numComponents G ≥ numComponents H := by classical
  let f : Finset α → Finset α := fun C =>
    if hC : C ∈ components G then
      componentOf H ⟨Classical.choose (component_nonEmpty hC), by grind⟩
    else ∅
  have hsurj : Set.SurjOn f (components G : Set (Finset α)) (components H : Set (Finset α)) := by
    intro D hD
    rcases (component_nonEmpty hD) with ⟨y, hyD⟩
    refine ⟨componentOf G ⟨y, by grind⟩, ?_, ?_⟩ <;> grind
  grind [Finset.card_le_card_of_surjOn f hsurj]

lemma reachable_of_numComponents_eq
    {G H : SimpleGraph α}
    (hV : V(G) = V(H))
    (hReach : ∀ u v : α,
      u ∈ G.vertexSet → v ∈ G.vertexSet →
      Reachable G u v → Reachable H u v)
    (hNum : numComponents G = numComponents H):
    ∀ u v : α,
      u ∈ G.vertexSet → v ∈ G.vertexSet → Reachable H u v → Reachable G u v := by classical
  intro u v hu hv
  let f : Finset α → Finset α := fun C =>
    if hC : C ∈ components G then
      componentOf H ⟨Classical.choose (component_nonEmpty hC), by grind⟩
    else ∅
  have himg_eq : ((components G : Set (Finset α))).image f = components H := by
    ext D; constructor
    · grind
    · intro hD; rcases (component_nonEmpty hD) with ⟨y, hyD⟩
      refine ⟨componentOf G ⟨y, by grind⟩, ?_, ?_⟩ <;> grind
  have hcard_image : ((components G).image f).card = (components G).card := by
    norm_cast at himg_eq; grind
  have hinj : Set.InjOn f (components G) := Finset.injOn_of_card_image_eq hcard_image
  intro hHuv
  by_contra hnot
  let uG : Vertex G := ⟨u, hu⟩; let vG : Vertex G := ⟨v, hv⟩
  let uH : Vertex H := ⟨u, by grind⟩; let vH : Vertex H := ⟨v, by grind⟩
  have hCu : componentOf G uG ∈ components G := by grind
  have hCv : componentOf G vG ∈ components G := by grind
  have hCompNe : componentOf G uG ≠ componentOf G vG := by grind
  have hCompEq : componentOf G uG = componentOf G vG := hinj hCu hCv (by grind)
  exact hCompNe hCompEq

end SimpleGraph
