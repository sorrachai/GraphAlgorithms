import GraphAlgorithms.UndirectedGraphs.Bridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Trees (undirected simple)
-- Authors: Weixuan Yuan

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
variable {α : Type*} [DecidableEq α]

namespace SimpleGraph
open scoped SimpleGraph
open scoped BigOperators Finset
open VertexSeq


/-- A tree is a nonempty connected acyclic graph. -/
def IsTree (G : SimpleGraph α) : Prop :=
  G.vertexSet.Nonempty ∧ Connected G ∧ Acyclic G

/-- A forest is an acyclic graph. -/
def IsForest (G : SimpleGraph α) : Prop :=
  Acyclic G

namespace Tree

/-- There is a unique path-walk in `G` from `u` to `v`. -/
def UniquePath (G : SimpleGraph α) (u v : α) : Prop :=
  ∃! w : Walk α, IsWalkIn G w ∧ Walk.IsPath w ∧ w.head = u ∧ w.tail = v

/-- Deleting an edge on a cycle preserves connectedness. -/
@[local grind .] lemma connected_delete_cycle {G : SimpleGraph α}
    (hConn : Connected G) (e : Edge α) {c : Walk α} (hcG : IsWalkIn G c)
    (hcycle : Walk.IsCycle c) (hec : e ∈ c.edgeSet) : Connected (deleteEdge G e) := by
  have hneG : G.vertexSet.Nonempty := by grind [Sym2.out_fst_mem]
  have hnotBridge : ¬ IsBridge G e := by grind [Bridge.iff]
  grind [numComponents_pos, numComponents_one_of_connected]

/-- Deleting a tree edge creates exactly two components. -/
@[local grind .] lemma components_deleteEdge
    (G : SimpleGraph α) (hT : IsTree G) (e : Edge α) (he : e ∈ G.edgeSet) :
    numComponents (deleteEdge G e) = 2 := by
  grind [numComponents_one_of_connected G hT.1 hT.2.1, numComponents_one_of_connected,
  numComponents_deleteEdge_le_succ,Bridge.isBridge_of_acyclic_edge e hT.2.2 he]

/-- A component restriction is unchanged after deleting the separating tree edge. -/
@[local grind =] lemma induced_deleteEdge
    (G : SimpleGraph α) (hT : IsTree G) (e : Edge α) (he : e ∈ G.edgeSet)
    {C : Finset α} (hC : C ∈ components (deleteEdge G e)) :
    inducedSubgraph (deleteEdge G e) C = inducedSubgraph G C := by
  classical
  let H : SimpleGraph α := deleteEdge G e
  have hBridge : IsBridge G e := Bridge.isBridge_of_acyclic_edge e hT.2.2 he
  have hEndpoint_not_reachable : ¬ Reachable H e.out.1 e.out.2 := by
    intro hEndpoint
    have hReachGH : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet →
        Reachable G u v → Reachable H u v := by
      intro u v hu hv hreach
      rcases hreach with ⟨w, hwG, hwu, hwv⟩
      have hEdge : ∀ x y : α, s(x, y) ∈ G.edgeSet → Reachable H x y := by
        intro x y hxy; by_cases hxe : s(x, y) = e
        · have hmk : s((s(x, y) : Edge α).out.1, (s(x, y) : Edge α).out.2) =
              s(x, y) := by grind [Quot.out_eq]
          grind
        · grind [reachable_of_edge]
      have hwH := reachable_of_seq (G := G) (H := H)
        (by intro z hz; change z ∈ G.vertexSet; exact hz) hEdge w.seq hwG
      rcases hwH with ⟨wH, hwHin, hwh, hwt⟩
      refine ⟨wH, hwHin, ?_, ?_⟩ <;> grind [reachable_of_seq]
    have hmono := numComponents_ge (G := G) (H := H)
      (by change G.vertexSet = (deleteEdge G e).vertexSet; rfl) hReachGH
    have hgt : numComponents H > numComponents G := by grind
    grind
  have hEdge_not_in_C : e ∉ (inducedSubgraph G C).edgeSet := by
    grind [Sym2.out_fst_mem, Sym2.out_snd_mem]
  ext <;> grind

/-- Each component of an acyclic graph is a tree. -/
@[local grind .] lemma isTree_component (G : SimpleGraph α) (hacy : Acyclic G)
    {C : Finset α} (hC : C ∈ components G) : IsTree (inducedSubgraph G C) := by
    refine ⟨?_, ?_, ?_⟩ <;> grind [reachable_induced]

/-- A finite tree has one more vertex than edge. -/
@[local grind =] theorem edge_vertex_count
    (G : SimpleGraph α) (hT : IsTree G) :
    numEdges G + 1 = numVertices G := by
  suffices hmain : ∀ n : Nat, ∀ G : SimpleGraph α,
      numEdges G = n → IsTree G → numEdges G + 1 = numVertices G by
    exact hmain (numEdges G) G rfl hT
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hn hT; by_cases hE : G.edgeSet = ∅
    · grind [one_vertex_of_connected_edgeless G hT.1 hT.2.1 hE]
    · have hEnonempty : G.edgeSet.Nonempty := by grind
      rcases hEnonempty with ⟨e, he⟩
      let H : SimpleGraph α := deleteEdge G e
      have hHacy : Acyclic H :=
        acyclic_of_subgraph (by change SimpleGraph.subgraphOf (deleteEdge G e) G; exact deleteEdge_subgraph G e) hT.2.2
      have hsum :
          (∑ C ∈ components H, (numEdges (inducedSubgraph H C) + 1)) =
            (∑ C ∈ components H, numVertices (inducedSubgraph H C)) := by
        grind [Finset.sum_congr]
      grind[components_deleteEdge,Finset.card_eq_sum_ones, sum_component_vertices,
      sum_component_edges, Finset.sum_add_distrib]


/-- A connected graph has at most one more vertex than edge. -/
@[local grind .] lemma vertex_le_edge_succ
    (G : SimpleGraph α) (hConn : Connected G) :
    numVertices G ≤ numEdges G + 1 := by
  suffices hmain : ∀ n : Nat, ∀ G : SimpleGraph α,
      numEdges G = n → Connected G → numVertices G ≤ numEdges G + 1 by grind
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hn hConn; by_cases hE : G.edgeSet = ∅
    · by_cases hne : G.vertexSet.Nonempty
      · grind [one_vertex_of_connected_edgeless]
      · grind [Finset.not_nonempty_iff_eq_empty]
    · by_cases hacy : Acyclic G
      · have hne : G.vertexSet.Nonempty := by
          rcases Finset.nonempty_iff_ne_empty.mpr hE with ⟨e, he⟩
          exact ⟨e.out.1, G.incidence _ he _ (Sym2.out_fst_mem e)⟩
        have hT : IsTree G := ⟨hne, hConn, hacy⟩
        grind
      · have hex : ∃ c : Walk α, IsWalkIn G c ∧ Walk.IsCycle c := by grind
        rcases hex with ⟨c, hcG, hcycle⟩
        rcases Walk.cycle_edges_nonempty c hcycle with ⟨e, hec⟩
        grind [connected_delete_cycle hConn e hcG hcycle hec]

end Tree

/-- A finite forest satisfies `m + c = n`. -/
@[local grind .] lemma forest_count
    (G : SimpleGraph α) (hacy : Acyclic G) :
    numEdges G + numComponents G = numVertices G := by
  have hsum : (∑ C ∈ components G, (numEdges (inducedSubgraph G C) + 1)) =
    (∑ C ∈ components G, numVertices (inducedSubgraph G C)) := by
    grind [Finset.sum_congr, Tree.edge_vertex_count, Tree.isTree_component]
  grind [Finset.card_eq_sum_ones, Finset.sum_add_distrib,
    sum_component_edges, sum_component_vertices]

namespace Tree

/-- A connected graph with `m + 1 = n` is a tree. -/
@[local grind →] lemma of_connected_count
    (G : SimpleGraph α) (hnum : numEdges G + 1 = numVertices G) (hConn : Connected G) :
    IsTree G := by
  refine ⟨(nonempty_of_count_eq hnum), hConn, ?_⟩; by_contra hacy
  have hex : ∃ c : Walk α, IsWalkIn G c ∧ Walk.IsCycle c := by grind
  rcases hex with ⟨c, hcG, hcycle⟩
  rcases Walk.cycle_edges_nonempty c hcycle with ⟨e, hec⟩
  have heG : e ∈ G.edgeSet := ((SimpleGraph.IsWalkIn.iff G c).mp hcG).2 hec
  have := connected_delete_cycle hConn e hcG hcycle hec
  grind [vertex_le_edge_succ]


/-- An acyclic graph with `m + 1 = n` is a tree. -/
@[local grind →] lemma of_acyclic_count
    (G : SimpleGraph α) (hnum : numEdges G + 1 = numVertices G)
    (hacy : Acyclic G) : IsTree G := by grind


/-- A deleted bridge disconnects its endpoints. -/
@[local grind →]
lemma bridge_not_reachable {G : SimpleGraph α} {e : Edge α}
    (hBridge : IsBridge G e) :
    ¬ Reachable (deleteEdge G e) e.out.1 e.out.2 := by
  let H : SimpleGraph α := deleteEdge G e; intro hEndpoint
  have hReachGH : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet →
      Reachable G u v → Reachable H u v := by
    intro u v hu hv hreach; rcases hreach with ⟨w, hwG, hwu, hwv⟩
    have hEdge : ∀ x y : α, s(x, y) ∈ G.edgeSet → Reachable H x y := by
      intro x y hxy; by_cases hxe : s(x, y) = e
      · have hmk : s((s(x, y) : Edge α).out.1, (s(x, y) : Edge α).out.2) =
            s(x, y) := by grind [Quot.out_eq]
        grind
      · grind [reachable_of_edge]
    have hwH := reachable_of_seq (G := G) (H := H)
      (by intro z hz; change z ∈ G.vertexSet; exact hz) hEdge w.seq hwG
    rcases hwH with ⟨wH, hwHin, hwh, hwt⟩
    refine ⟨wH, hwHin, ?_, ?_⟩ <;> grind
  have hmono : numComponents G ≥ numComponents H := numComponents_ge (G := G) (H := H)
    (by change G.vertexSet = (deleteEdge G e).vertexSet; rfl) hReachGH
  grind

/-- Two distinct paths with the same endpoints produce a cycle. -/
lemma cycle_of_two_paths {G : SimpleGraph α} {p q : Walk α}
    (hpG : IsWalkIn G p) (hqG : IsWalkIn G q)
    (hpPath : Walk.IsPath p) (hqPath : Walk.IsPath q)
    (hhead : p.head = q.head) (htail : p.tail = q.tail) (hne : p ≠ q) :
    ∃ c : Walk α, IsWalkIn G c ∧ Walk.IsCycle c := by
  by_contra hacy
  have hAcy : Acyclic G := by grind
  have hEq : p = q := by
    suffices hmain : ∀ n : Nat, ∀ p q : Walk α,
        p.length = n →
        IsWalkIn G p → Walk.IsPath p →
        IsWalkIn G q → Walk.IsPath q →
        p.head = q.head → p.tail = q.tail → p = q by
      exact hmain p.length p q rfl hpG hpPath hqG hqPath hhead htail
    intro n; refine Nat.strong_induction_on n ?_
    intro n ih p q hpn hpG hpPath hqG hqPath hhead htail
    by_cases hp0 : p.length = 0
    · grind [VertexSeq.length_zero_of_nodup_head_eq_tail]
    · have hpLastG : s(p.dropTail.tail, p.tail) ∈ G.edgeSet := by
        have hpLast : s(p.dropTail.tail, p.tail) ∈ p.edgeSet := by grind [Walk.dropTail_edges]
        grind
      let e : Edge α := s(p.dropTail.tail, p.tail)
      have hpLastNotDrop : e ∉ p.dropTail.edgeSet := by grind [Walk.lastEdge_fresh]
      have hpDropG : IsWalkIn (deleteEdge G e) p.dropTail := by
        exact (SimpleGraph.IsWalkIn.deleteEdge_iff G e p.dropTail).mpr
          ⟨SimpleGraph.IsWalkIn.dropTail G p hpG, hpLastNotDrop⟩
      have hbridge := Bridge.isBridge_of_acyclic_edge e hAcy (by simpa [e] using hpLastG)
      have hqUses : e ∈ q.edgeSet := by
        by_contra hqNo
        have hqDel := (SimpleGraph.IsWalkIn.deleteEdge_iff G e q).mpr ⟨hqG, hqNo⟩
        have hreachP : Reachable (deleteEdge G e) p.dropTail.tail p.head := by
          have htmp : Reachable (deleteEdge G e) p.head p.dropTail.tail :=
            ⟨p.dropTail, hpDropG, Walk.dropTail_head p, rfl⟩
          grind
        have hreachQ : Reachable (deleteEdge G e) p.head p.tail := by grind
        have hout : e.out = (p.dropTail.tail, p.tail) ∨ e.out = (p.tail, p.dropTail.tail) := by
          have hmk' : s((e.out.1, e.out.2).1, (e.out.1, e.out.2).2) =
              s((p.dropTail.tail, p.tail).1, (p.dropTail.tail, p.tail).2) := by grind [Quot.out_eq]
          grind
        grind
      have hdropEq : p.dropTail = q.dropTail :=
        ih p.dropTail.length (by grind [Walk.dropTail_length_succ]) p.dropTail q.dropTail rfl
          (by grind) (by grind [Walk.isPath_dropTail])
          (by grind) (by grind [Walk.isPath_dropTail])
          (by grind) (by grind [Walk.tail_of_lastEdge])
      grind
  exact hne hEq

/-- A tree has a unique path between any two vertices. -/
lemma uniquePath
    (G : SimpleGraph α) (hT : IsTree G) :
    ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet → UniquePath G u v := by
  intro u v hu hv; unfold UniquePath
  rcases hT.2.1 u v hu hv with ⟨w, hwG, hwu, hwv⟩; let p : Walk α := w.toPath
  have hpG := SimpleGraph.IsWalkIn.toPath G w hwG
  have hpPath := Walk.isPath_toPath w
  have hpHead : p.head = u := by grind
  have hpTail : p.tail = v := by grind
  refine ⟨p, ⟨hpG, hpPath, hpHead, hpTail⟩, ?_⟩; intro q hq; by_contra hne
  have hCycle : ∃ c : Walk α, IsWalkIn G c ∧ Walk.IsCycle c :=
    cycle_of_two_paths hpG hq.1 hpPath hq.2.1
      (by rw [hpHead, hq.2.2.1]) (by rw [hpTail, hq.2.2.2])
      (by intro hpq; exact hne hpq.symm)
  exact hT.2.2 hCycle

/-- Unique paths between vertices characterize trees, assuming nonemptiness. -/
lemma of_uniquePath (G : SimpleGraph α) (hne : G.vertexSet.Nonempty)
    (hUnique : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet → UniquePath G u v) :
    IsTree G := by
  refine ⟨hne, ?_, ?_⟩
  · intro u v hu hv; rcases hUnique u v hu hv with ⟨w, hw, _⟩; grind
  · rintro ⟨c, hcG, hcycle⟩
    let p : Walk α := c.dropTail
    have hpos : c.length ≠ 0 := by grind
    let q : Walk α := ⟨(VertexSeq.singleton c.head).cons c.dropTail.tail,
      IsWalk.cons (VertexSeq.singleton c.head) c.dropTail.tail
        (IsWalk.singleton c.head) (by grind)⟩
    have hpG : IsWalkIn G p := SimpleGraph.IsWalkIn.dropTail G c hcG
    have hpPath : Walk.IsPath p := hcycle.2.2
    have hqG : IsWalkIn G q := by grind [Walk.dropTail_edges]
    have hqPath : Walk.IsPath q := by unfold Walk.IsPath; grind
    have htailV := VertexSeq.IsVertexSeqIn.tail_mem hpG
    have huniq := hUnique c.head c.dropTail.tail
      ((SimpleGraph.IsWalkIn.iff G c).mp hcG |>.1) htailV
    rcases huniq with ⟨r, hr, huniqr⟩
    grind [Walk.dropTail_length_succ, huniqr q]

/-! ## Tree characterizations -/

/-- Trees are exactly nonempty graphs with unique paths between vertices. -/
theorem iff1 (G : SimpleGraph α) :
    IsTree G ↔
      G.vertexSet.Nonempty ∧
        ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet → UniquePath G u v := by
  constructor
  · intro hT
    exact ⟨hT.1, uniquePath G hT⟩
  · intro h
    exact of_uniquePath G h.1 h.2

/-- Trees are exactly connected graphs with `m + 1 = n`. -/
theorem iff2 (G : SimpleGraph α) :
    IsTree G ↔ Connected G ∧ numEdges G + 1 = numVertices G := by
  constructor
  · intro hT
    exact ⟨hT.2.1, edge_vertex_count G hT⟩
  · intro h
    exact of_connected_count G h.2 h.1

/-- Trees are exactly acyclic graphs with `m + 1 = n`. -/
theorem iff3 (G : SimpleGraph α) :
    IsTree G ↔ Acyclic G ∧ numEdges G + 1 = numVertices G := by
  constructor
  · intro hT
    exact ⟨hT.2.2, edge_vertex_count G hT⟩
  · intro h
    exact of_acyclic_count G h.2 h.1

end Tree

end SimpleGraph
