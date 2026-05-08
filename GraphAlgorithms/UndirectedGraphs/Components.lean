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

/-- Every graph vertex is reachable from itself. -/
@[simp, grind →] theorem reachable_refl (G : SimpleGraph α) (v : α) (hv : v ∈ G.vertexSet) :
    Reachable G v v := by
  refine ⟨⟨VertexSeq.singleton v, IsWalk.singleton v⟩, ?_, rfl, rfl⟩
  exact IsVertexSeqIn.singleton v hv

/-- Reachability in an undirected graph is symmetric. -/
@[simp, grind →] theorem reachable_symm (G : SimpleGraph α) (u v : α) (huv : Reachable G u v) :
    Reachable G v u := by
  rcases huv with ⟨w, hw, hu, hv⟩
  refine ⟨w.reverse, ?_, ?_, ?_⟩ <;> grind

/-- Reachability is transitive. -/
@[simp, grind →] theorem reachable_trans (G : SimpleGraph α) (u v w : α)
    (huv : Reachable G u v) (hvw : Reachable G v w) : Reachable G u w := by
  rcases huv with ⟨w1, h1, hu, hv⟩; rcases hvw with ⟨w2, h2, hv', hw⟩
  have h : w1.tail = w2.head := by grind
  refine ⟨Walk.append w1 w2 h, SimpleGraph.IsWalkIn.append G w1 w2 h1 h2 h, ?_, ?_⟩
  <;> grind

/-- The left endpoint of a reachable pair is a graph vertex. -/
@[simp, grind →] lemma mem_left_of_reachable {G : SimpleGraph α} {x y : α}
    (hxy : Reachable G x y) : x ∈ G.vertexSet := by grind

/-- The right endpoint of a reachable pair is a graph vertex. -/
@[simp, grind →] lemma mem_right_of_reachable {G : SimpleGraph α} {x y : α}
    (hxy : Reachable G x y) : y ∈ G.vertexSet := by grind

/-- If `H` is a subgraph of `G` and `u` is reachable from `v` in `H`,
  then `u` is reachable from `v` in `G`. -/
@[simp, grind →] lemma reachable_mono {H G : SimpleGraph α}
    (hsub : SimpleGraph.subgraphOf H G) {u v : α}
    (hreach : Reachable H u v) : Reachable G u v := by grind

/-- If `H` is a subgraph of `G` and `G` is acyclic, then `H` is acyclic. -/
@[simp, grind →] lemma acyclic_of_subgraph {H G : SimpleGraph α}
    (hsub : SimpleGraph.subgraphOf H G)
    (hacyG : Acyclic G) : Acyclic H := by grind

/-! ## Components as reachable classes -/

/-- Vertex type restricted to vertices of `G`. -/
abbrev Vertex (G : SimpleGraph α) := {v : α // v ∈ G.vertexSet}

/-- Reachability relation on `Vertex G`. -/
abbrev ReachableOn (G : SimpleGraph α) (u v : Vertex G) : Prop :=
  Reachable G u.1 v.1

/-- Setoid induced by graph reachability on vertices of `G`. -/
@[grind] def reachableSetoid (G : SimpleGraph α) : Setoid (Vertex G) where
  r := ReachableOn G
  iseqv := by refine ⟨?refl, ?symm, ?trans⟩ <;> grind

/-- The connected component containing `v`. -/
@[simp, grind] noncomputable def componentOf (G : SimpleGraph α) (v : Vertex G) : Finset α := by
  classical
  exact G.vertexSet.filter (fun u => Reachable G v.1 u)

/-- The finite set of all connected components of `G`. -/
@[simp, grind] noncomputable def components (G : SimpleGraph α) : Finset (Finset α) := by
  classical
  exact (G.vertexSet.attach.image (fun v => componentOf G v))

/-- The number of connected components of `G`. -/
@[simp, grind] noncomputable def numComponents (G : SimpleGraph α) : Nat := by
  classical
  exact (components G).card

/-- The edges of `G` whose endpoints both lie in `C`. -/
@[simp, grind] noncomputable def componentEdgeSetOf (G : SimpleGraph α) (C : Finset α) :
  Finset (Edge α) := by classical
  exact {e ∈ G.edgeSet | ∀ v ∈ e, v ∈ C}

/-! ## Basic component lemmas -/

/-- Membership in a component is exactly vertex membership plus reachability. -/
@[simp, grind =] lemma componentOf_mem (G : SimpleGraph α) (v : Vertex G) (u : α) :
    u ∈ componentOf G v ↔ u ∈ G.vertexSet ∧ Reachable G v u := by grind

/-- The representative vertex belongs to its own component. -/
@[simp, grind .] lemma mem_componentOf_self (G : SimpleGraph α) (v : Vertex G) :
    v.1 ∈ componentOf G v := by grind

/-- Every listed component is contained in the graph vertex set. -/
@[simp, grind →] lemma component_subset (G : SimpleGraph α)
    {C : Finset α} (hC : C ∈ components G) :
    C ⊆ G.vertexSet := by grind

/-- Every listed component is nonempty. -/
@[simp, grind →] lemma component_nonempty {G : SimpleGraph α}
  {C : Finset α} (hC : C ∈ components G) : C.Nonempty := by grind

/-- A component equals the component generated by any of its vertices. -/
@[simp, grind →] lemma component_eq_of_mem (G : SimpleGraph α)
    {C : Finset α} (hC : C ∈ components G) {u : α} (hu : u ∈ C) :
    C = componentOf G ⟨u, component_subset G hC hu⟩ := by grind

/-- Reachable vertices determine the same component. -/
@[simp, grind →] lemma componentOf_eq (G : SimpleGraph α)
    (u v : Vertex G) (huv : Reachable G u.1 v.1) :
    componentOf G u = componentOf G v := by grind

/-- Distinct components are disjoint. -/
@[simp, grind .] lemma components_disjoint (G : SimpleGraph α) :
    ((components G : Finset (Finset α)) : Set (Finset α)).Pairwise
      (fun C D => Disjoint C D) := by intro; grind[Finset.disjoint_left]

/-- The union of all components is the full vertex set. -/
@[simp, grind =] lemma components_biUnion (G : SimpleGraph α) :
    (components G).biUnion (fun C => C) = G.vertexSet := by
  ext u; constructor
  · grind
  · intro hu; have hC : componentOf G ⟨u, hu⟩ ∈ components G := by grind
    grind

/-- A graph edge gives a length-one reachability witness. -/
@[simp, grind →] lemma reachable_of_edge (G : SimpleGraph α) {u v : α}
    (he : s(u, v) ∈ G.edgeSet) : Reachable G u v := by
  let w : Walk α :=
    ⟨VertexSeq.cons (VertexSeq.singleton u) v,
      IsWalk.cons (VertexSeq.singleton u) v
        (IsWalk.singleton u) (by grind)⟩
  refine ⟨w, ?_, rfl, rfl⟩
  have hu : u ∈ G.vertexSet := G.incidence _ he _ (by simp); grind

/-- Realized vertex sequences are reachable if each traversed edge is reachable. -/
lemma reachable_of_seq {G H : SimpleGraph α}
    (hV : G.vertexSet ⊆ H.vertexSet)
    (hEdge : ∀ u v : α, s(u, v) ∈ G.edgeSet → Reachable H u v)
    (w : VertexSeq α) (hw : IsVertexSeqIn G w) :
    Reachable H w.head w.tail := by
  induction hw <;> grind


/-! ## Induced subgraphs and component-wise counting identities -/

/-- The subgraph induced by a finite vertex set. -/
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

/-- Component vertex counts sum to the graph vertex count. -/
@[local grind =] lemma sum_component_vertices (G : SimpleGraph α) :
    (∑ C ∈ components G, numVertices (inducedSubgraph G C)) = numVertices G := by
  grind [Set.PairwiseDisjoint, Finset.card_biUnion, components_biUnion]

/-- Component edge counts sum to the graph edge count. -/
@[local grind =] lemma sum_component_edges (G : SimpleGraph α) :
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

/-- Adding reachability can only merge components. -/
@[local grind →] lemma numComponents_ge {G H : SimpleGraph α} (hV : V(G) = V(H))
    (hReach : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet →
      Reachable G u v → Reachable H u v) :
    numComponents G ≥ numComponents H := by classical
  let f : Finset α → Finset α := fun C =>
    if hC : C ∈ components G then
      componentOf H ⟨Classical.choose (component_nonempty hC), by grind⟩
    else ∅
  have hsurj : Set.SurjOn f (components G : Set (Finset α)) (components H : Set (Finset α)) := by
    intro D hD; rcases (component_nonempty hD) with ⟨y, hyD⟩
    refine ⟨componentOf G ⟨y, by grind⟩, ?_, ?_⟩ <;> grind
  grind [Finset.card_le_card_of_surjOn f hsurj]

/-- If the component count does not change, no reverse reachability was lost. -/
@[local grind →] lemma reachable_of_eq_numComponents {G H : SimpleGraph α} (hV : V(G) = V(H))
    (hReach : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet →
      Reachable G u v → Reachable H u v)
    (hNum : numComponents G = numComponents H):
    ∀ u v : α,
      u ∈ G.vertexSet → v ∈ G.vertexSet → Reachable H u v → Reachable G u v := by classical
  intro u v hu hv
  let f : Finset α → Finset α := fun C =>
    if hC : C ∈ components G then
      componentOf H ⟨Classical.choose (component_nonempty hC), by grind⟩
    else ∅
  have himg_eq : ((components G : Set (Finset α))).image f = components H := by
    ext D; constructor
    · grind
    · intro hD; rcases (component_nonempty hD) with ⟨y, hyD⟩
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
  have hfCu : f (componentOf G uG) = componentOf H uH := by grind
  have hfCv : f (componentOf G vG) = componentOf H vH := by
    grind [componentOf_eq]
  have hfEq : f (componentOf G uG) = f (componentOf G vG) := by
    grind [componentOf_eq]
  grind [hinj hCu hCv hfEq]

/-- A graph with a vertex has at least one component. -/
@[local grind →] lemma numComponents_pos
    (G : SimpleGraph α) (hne : G.vertexSet.Nonempty) : 0 < numComponents G := by
  rcases hne with ⟨v, hv⟩
  have hC : componentOf G ⟨v, hv⟩ ∈ components G := by grind
  grind

/-- In a connected graph, every component is the full vertex set. -/
@[local grind =] lemma component_eq_vertexSet
    (G : SimpleGraph α) (hConn : Connected G) (v : Vertex G) :
    componentOf G v = G.vertexSet := by grind

/-- A nonempty connected graph has exactly one component. -/
lemma numComponents_one_of_connected
    (G : SimpleGraph α) (hne : G.vertexSet.Nonempty) (hConn : Connected G) :
    numComponents G = 1 := by
  rcases hne with ⟨v, hv⟩
  have : components G = {componentOf G ⟨v, hv⟩} := by
    ext C; constructor <;> grind
  grind

/-- A nonempty graph with one component is connected. -/
lemma connected_of_numComponents_one (G : SimpleGraph α)
    (hnum : numComponents G = 1) : Connected G := by
  intro u v hu hv
  have hCu : componentOf G ⟨u, hu⟩ ∈ components G := by grind
  have hCv : componentOf G ⟨v, hv⟩ ∈ components G := by grind
  have hcard : (components G).card = 1 := by grind
  rcases Finset.card_eq_one.mp hcard with ⟨C, hcomponents⟩
  grind

@[grind =] theorem connected_iff_numComponents (G : SimpleGraph α)
  (hne : G.vertexSet.Nonempty) : Connected G ↔ numComponents G = 1 := by
  grind [connected_of_numComponents_one, numComponents_one_of_connected]

/-! ## Deleting one edge -/

/-- Reachability in `G \ e`, possibly crossing the deleted edge once. -/
@[grind] def DeleteEdgeRoute (G : SimpleGraph α) (e : Edge α) (x y : α) : Prop :=
  Reachable (deleteEdge G e) x y ∨
    (Reachable (deleteEdge G e) x e.out.1 ∧ Reachable (deleteEdge G e) e.out.2 y) ∨
    (Reachable (deleteEdge G e) x e.out.2 ∧ Reachable (deleteEdge G e) e.out.1 y)

/-- `DeleteEdgeRoute` is transitive in its endpoints. -/
@[local grind .] lemma DeleteEdgeRoute.trans {G : SimpleGraph α} (e : Edge α)
    {x y z : α}
    (hxy : DeleteEdgeRoute G e x y)
    (hyz : DeleteEdgeRoute G e y z) :
    DeleteEdgeRoute G e x z := by
  unfold DeleteEdgeRoute at hxy hyz ⊢
  rcases hxy with hxy | hxy | hxy <;> grind

/-- A single edge gives a `DeleteEdgeRoute`. -/
@[local grind ←] lemma deleteRoute_of_edge {G : SimpleGraph α} (e : Edge α)
    {x y : α} (hxy : s(x, y) ∈ G.edgeSet) :
    DeleteEdgeRoute G e x y := by
  unfold DeleteEdgeRoute
  by_cases heq : s(x, y) = e
  · have hmk : s((e.out.1, e.out.2).1, (e.out.1, e.out.2).2) =
        s((x, y).1, (x, y).2) := by grind [Quot.out_eq]
    rcases Sym2.mk_eq_mk_iff.mp hmk with hpair | hpair <;> grind
  · grind

/-- A realized vertex sequence gives a `DeleteEdgeRoute`. -/
@[local grind .] lemma deleteRoute_of_seq
  {G : SimpleGraph α} (e : Edge α) (w : VertexSeq α) (hw : IsVertexSeqIn G w) :
    DeleteEdgeRoute G e w.head w.tail := by
  induction hw with
  | singleton v hv => grind
  | cons w v hw he ih => grind


/-- Reachability in `G` gives a `DeleteEdgeRoute` after deleting `e`. -/
lemma deleteRoute_of_reachable {G : SimpleGraph α} (e : Edge α)
    {x y : α} (hxy : Reachable G x y) : DeleteEdgeRoute G e x y := by
  unfold DeleteEdgeRoute
  rcases hxy with ⟨w, hwG, hx, hy⟩
  have h := deleteRoute_of_seq e w.seq hwG
  unfold DeleteEdgeRoute at h
  simpa [hx, hy] using h

/-- Components after deleting one edge inject into old components plus one extra point. -/
lemma components_deleteEdge_map
    (G : SimpleGraph α) (e : Edge α) :
    ∃ f : Finset α → (Finset α ⊕ Unit),
      Set.MapsTo f (components (deleteEdge G e))
        ((components G).disjSum {()}) ∧
      Set.InjOn f (components (deleteEdge G e)) := by
  classical
  let H : SimpleGraph α := deleteEdge G e
  let f : Finset α → (Finset α ⊕ Unit) := fun C =>
    if e.out.1 ∈ C then
      Sum.inr ()
    else
      if hC : C.Nonempty ∧ C ⊆ G.vertexSet then
        Sum.inl (componentOf G
          ⟨Classical.choose hC.1, hC.2 (Classical.choose_spec hC.1)⟩)
      else
        Sum.inl ∅
  refine ⟨f, ?_, ?_⟩
  · intro C hC; by_cases huC : e.out.1 ∈ C
    · grind [Finset.inr_mem_disjSum]
    · grind [Finset.inl_mem_disjSum]
  · intro C hC D hD hEq
    have hCG : C.Nonempty ∧ C ⊆ G.vertexSet := by grind
    have hDG : D.Nonempty ∧ D ⊆ G.vertexSet := by grind
    by_cases huC : e.out.1 ∈ C
    · grind
    · by_cases huD : e.out.1 ∈ D
      · grind
      · have hfC : f C = Sum.inl (componentOf G
            ⟨Classical.choose hCG.1, hCG.2 (Classical.choose_spec hCG.1)⟩) := by grind
        have hfD : f D = Sum.inl (componentOf G
            ⟨Classical.choose hDG.1, hDG.2 (Classical.choose_spec hDG.1)⟩) := by grind
        rw [hfC, hfD, Sum.inl.injEq] at hEq
        let x : α := Classical.choose hCG.1
        let y : α := Classical.choose hDG.1
        have hGxy : Reachable G x y := by grind [mem_componentOf_self]
        have hClass := deleteRoute_of_reachable e hGxy
        rcases hClass with hHxy | hcross | hcross <;> grind

/-- Deleting one edge increases the component count by at most one. -/
lemma numComponents_deleteEdge_le_succ
    (G : SimpleGraph α) (e : Edge α) :
    numComponents (deleteEdge G e) ≤ numComponents G + 1 := by
  rcases components_deleteEdge_map G e with ⟨f, hfmap, hfinj⟩
  have hcard := Finset.card_le_card_of_injOn f hfmap hfinj
  grind [Finset.card_disjSum]

/-! ## Induced component subgraphs -/

/-- An induced subgraph uses only edges of the original graph. -/
lemma induced_edges_subset (G : SimpleGraph α) (C : Finset α) :
    (inducedSubgraph G C).edgeSet ⊆ G.edgeSet := by grind

/-- The induced graph on a component is a subgraph of the original graph. -/
lemma induced_subgraph (G : SimpleGraph α)
    {C : Finset α} (hC : C ∈ components G) :
    SimpleGraph.subgraphOf (inducedSubgraph G C) G := by grind

/-- A walk staying inside a component is realized in the induced component graph. -/
lemma IsVertexSeqIn.induced_of_component {G : SimpleGraph α}
    {C : Finset α} (hC : C ∈ components G) {w : VertexSeq α}
    (hw : IsVertexSeqIn G w) (hhead : w.head ∈ C) :
    IsVertexSeqIn (inducedSubgraph G C) w := by
  induction hw with
  | singleton v hv => grind
  | cons w u hw he ih =>
      have hwI := ih hhead
      have huC : u ∈ C := by grind
      refine IsVertexSeqIn.cons w u hwI ?_
      show s(w.tail, u) ∈ (inducedSubgraph G C).edgeSet
      rw [inducedSubgraph]
      simp only [Finset.mem_filter]; grind

/-- Reachability inside a component lifts to the induced component graph. -/
lemma reachable_induced {G : SimpleGraph α}
    {C : Finset α} (hC : C ∈ components G) {u v : α}
    (hu : u ∈ C) (h : Reachable G u v) : Reachable (inducedSubgraph G C) u v := by
    grind [IsVertexSeqIn.induced_of_component]

/-! ## Empty-edge graphs -/

/-- A graph with no edges is acyclic. -/
lemma acyclic_of_no_edges (G : SimpleGraph α) (hE : G.edgeSet = ∅) :
    Acyclic G := by grind

/-- The identity `m + 1 = n` forces a nonempty vertex set. -/
lemma nonempty_of_count_eq
    {G : SimpleGraph α} (h : numEdges G + 1 = numVertices G) :
    G.vertexSet.Nonempty := by grind [Finset.card_pos]

/-- In an edgeless graph, reachable vertices are equal. -/
lemma eq_of_reachable_edgeless {G : SimpleGraph α} (hE : G.edgeSet = ∅)
    {u v : α} (h : Reachable G u v) :
    u = v := by rcases h with ⟨w, hw, hwu, hwv⟩; grind

/-- A nonempty connected edgeless graph has one vertex. -/
lemma one_vertex_of_connected_edgeless
    (G : SimpleGraph α) (hne : G.vertexSet.Nonempty) (hConn : Connected G)
    (hE : G.edgeSet = ∅) :
    numVertices G = 1 := by
  rcases hne with ⟨v, hv⟩
  have hV : G.vertexSet = {v} := by
    ext u; constructor
    · intro hu
      have huv : Reachable G v u := hConn v u hv hu
      exact Finset.mem_singleton.mpr (eq_of_reachable_edgeless hE huv).symm
    · grind
  grind

end SimpleGraph
