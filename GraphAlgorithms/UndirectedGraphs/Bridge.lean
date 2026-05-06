import GraphAlgorithms.UndirectedGraphs.Walk
import GraphAlgorithms.UndirectedGraphs.Components
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Bridges in undirected simple graphs.
-- Authors: Weixuan Yuan

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
variable {α : Type*} [DecidableEq α]

namespace SimpleGraph
open scoped SimpleGraph
open scoped BigOperators Finset
open VertexSeq

/-! ### Bridge definition -/

/-- Bridge: deleting the edge strictly increases the number of components. -/
@[grind] def IsBridge (G : SimpleGraph α) (e : Edge α) : Prop :=
  e ∈ G.edgeSet ∧ numComponents (deleteEdge G e) > numComponents G

/-! ### Reachability after deleting cycle edges -/

/-- If `e` is the closing edge of a cycle, its endpoints remain reachable after deleting `e`. -/
lemma reachable_deleteEdge_of_cycle_closing_edge {G : SimpleGraph α} (e : Edge α)
    {c : Walk α} (hcG : IsVertexSeqIn G c.seq) (hcycle : Walk.IsCycle c)
    (hhead : c.head = e.out.1) (hec : e ∈ c.edgeSet)
    (hnot : e ∉ c.dropTail.edgeSet) :
    Reachable (deleteEdge G e) e.out.1 e.out.2 := by
  have hpos : c.length ≠ 0 := by grind
  have hcEdges := Walk.dropTail_edges c hpos
  have htail : c.tail = e.out.1 := by grind
  have hdropTail : c.dropTail.tail = e.out.2 := by
    have hmk : s((c.dropTail.tail, e.out.1).1, (c.dropTail.tail, e.out.1).2) =
        s((e.out.1, e.out.2).1, (e.out.1, e.out.2).2) := by grind[Quot.out_eq]
    rcases (Sym2.mk_eq_mk_iff.mp hmk) with hpair | hpair <;> grind
  refine ⟨c.dropTail, ?_, ?_, ?_⟩
  · exact (SimpleGraph.IsWalkIn.deleteEdge_iff G e c.dropTail).mpr
      ⟨SimpleGraph.IsWalkIn.dropTail G c hcG, hnot⟩
  · grind
  · grind

/-- Any edge on a cycle has endpoints still reachable after deleting that edge. -/
lemma reachable_deleteEdge_of_cycle_edge {G : SimpleGraph α} (e : Edge α)
    {c : Walk α} (hcG : IsVertexSeqIn G c.seq) (hcycle : Walk.IsCycle c)
    (hec : e ∈ c.edgeSet) :
    Reachable (deleteEdge G e) e.out.1 e.out.2 := by
  let u : α := e.out.1
  let v : α := e.out.2
  have hmk : s(u, v) = e := by grind[Quot.out_eq]
  have hu : u ∈ c.support := by grind [VertexSeq.left_mem_of_edge]
  let r : Walk α := c.rerootCycle hcycle u hu
  have hrCycle : Walk.IsCycle r := Walk.isCycle_reroot c hcycle u hu
  have hrG : IsVertexSeqIn G r.seq := by grind
  let a : Walk α := Walk.takeUntil c u hu
  let b : Walk α := Walk.dropUntil c u hu
  have hrEdge : r.edgeSet = b.edgeSet ∪ a.edgeSet := by grind [Walk.append_edges]
  have her : e ∈ r.edgeSet := by
    have hcsub := VertexSeq.split_edges_subset c.seq u hu hec
    grind
  by_cases hnot : e ∉ r.dropTail.edgeSet
  · grind [reachable_deleteEdge_of_cycle_closing_edge]
  · have herDrop : e ∈ r.dropTail.edgeSet := by grind
    let d : Walk α := r.dropTail
    have hvd : v ∈ d.support := by grind [VertexSeq.right_mem_of_edge]
    have heG : e ∈ G.edgeSet := by grind
    have hge := hrCycle.1
    have hrpos : r.length ≠ 0 := by grind
    have hdlen : d.length + 1 = r.length := by grind [Walk.dropTail_length_succ]
    let q0 : Walk α := Walk.dropUntil d v hvd
    have hq0G : IsVertexSeqIn G q0.seq := by grind [SimpleGraph.IsWalkIn.dropUntil]
    have hq0NoE : e ∉ q0.edgeSet := by grind[VertexSeq.not_incident_dropUntil]
    have hrtail : r.tail = u := by grind
    have hclosingG : s(d.tail, u) ∈ G.edgeSet := by
      have hlastR : s(r.dropTail.tail, r.tail) ∈ r.edgeSet := by grind [Walk.dropTail_edges]
      have hlastG := ((SimpleGraph.IsWalkIn.iff G r).mp hrG).2 hlastR
      simpa [d, hrtail] using hlastG
    have hclosingNoE : s(d.tail, u) ≠ e := by
      intro hclose
      have hmk' : s((d.tail, u).1, (d.tail, u).2) =
          s((u, v).1, (u, v).2) := by grind
      rcases Sym2.mk_eq_mk_iff.mp hmk' with hp | hp <;> grind [VertexSeq.tail_ne_of_incident]
    let q : Walk α := q0.append_single u (by grind)
    have hqH : IsVertexSeqIn (deleteEdge G e) q.seq := by
      change IsVertexSeqIn (deleteEdge G e) (q0.seq.cons u)
      grind
    have hvu : Reachable (deleteEdge G e) v u := by
      refine ⟨q, hqH, ?_, ?_⟩
      · change q.seq.head = v
        simp [q, q0, Walk.append_single, Walk.dropUntil]
      · grind [Walk.append_single]
    grind

/-! ### Bridges and cycles -/

namespace Bridge

/-- A non-bridge edge lies on a cycle. -/
lemma nonBridge_inCycle {G : SimpleGraph α} (e : Edge α) (he : e ∈ G.edgeSet) :
    ¬ IsBridge G e → ∃ w : Walk α, IsVertexSeqIn G w.seq ∧ Walk.IsCycle w ∧ e ∈ w.edgeSet := by
    intro h
    let H : SimpleGraph α := deleteEdge G e
    have hVeq : V(H) = V(G) := by grind
    have hReachHG : ∀ u v : α,
        u ∈ H.vertexSet → v ∈ H.vertexSet →
        Reachable H u v → Reachable G u v := by grind [reachable_mono]
    have hgeq := numComponents_ge hVeq hReachHG
    have heq : numComponents H = numComponents G := by grind
    have hReachGH := reachable_of_eq_numComponents hVeq hReachHG heq
    let u : α := e.out.1; let v : α := e.out.2
    have hmk : s(u, v) = e := by simp [u, v, Sym2.mk]
    have heuv : s(u, v) ∈ G.edgeSet := by rw[hmk]; exact he
    have huvH := hReachGH u v (by exact G.incidence _ heuv _ (by simp))
      (by exact G.incidence _ heuv _ (by simp)) (reachable_of_edge G heuv)
    clear * - huvH hmk heuv he; rcases huvH with ⟨w, hwH, hwu, hwv⟩
    have hnotE : e ∉ w.edgeSet := (SimpleGraph.IsWalkIn.deleteEdge_iff G e w).mp hwH |>.2
    let p : Walk α := w.toPath
    have hpG : IsVertexSeqIn G p.seq := by grind [SimpleGraph.IsWalkIn.toPath]
    have hpHead : p.head = u := by grind[Walk.toPath_head]
    have hpTail : p.tail = v := by grind[Walk.toPath_tail]
    let c : Walk α := ⟨p.seq.cons u, IsWalk.cons p.seq u p.valid (by grind)⟩
    have hcG : IsVertexSeqIn G c.seq := by grind
    refine ⟨c, hcG, ?_, (by grind)⟩
    refine ⟨?_, (by grind), (by grind [Walk.isPath_toPath])⟩
    have hnotEp : e ∉ p.edgeSet := by grind [Walk.toPath_edges_subset]
    by_contra hlt
    have hp01 : p.length = 0 ∨ p.length = 1 := by grind
    rcases hp01 with hp0 | hp1
    · grind [Walk.endpoints_eq_of_zero p hp0]
    · have hlen1_edge (r : Walk α) : r.length = 1 → s(r.head, r.tail) ∈ r.edgeSet := by
        cases r; cases valid;
        · grind
        · cases hw <;> grind
      have hsuv : s(u, v) ∈ p.edgeSet := by
        simpa [hpHead, hpTail] using hlen1_edge p hp1
      grind

/-- A bridge cannot lie on a cycle. -/
lemma bridge_not_inCycle {G : SimpleGraph α} (e : Edge α) (_he : e ∈ G.edgeSet) :
    IsBridge G e → ¬ ∃ w : Walk α, IsVertexSeqIn G w.seq ∧ Walk.IsCycle w ∧ e ∈ w.edgeSet := by
    contrapose!
    rintro ⟨c, hc, hcycle, hec⟩
    let H : SimpleGraph α := deleteEdge G e
    have hEndpoint : Reachable H e.out.1 e.out.2 := by
      simpa [H] using reachable_deleteEdge_of_cycle_edge e hc hcycle hec
    have hReachGH : ∀ u v : α, u ∈ G.vertexSet → v ∈ G.vertexSet →
        Reachable G u v → Reachable H u v := by
      intro u v hu hv hreach
      rcases hreach with ⟨w, hwG, hwu, hwv⟩
      have hEdge : ∀ x y : α, s(x, y) ∈ G.edgeSet → Reachable H x y := by
        intro x y hxy
        by_cases hxe : s(x, y) = e
        · have hout : (s(x, y) : Edge α).out = (x, y) ∨
              (s(x, y) : Edge α).out = (y, x) := by grind[Quot.out_eq]
          rcases hout with hout | hout <;> grind
        · have hxyH : s(x, y) ∈ H.edgeSet := by grind
          grind
      have hwH : Reachable H w.head w.tail :=
        reachable_of_seq (G := G) (H := H)
          (by intro z hz; change z ∈ G.vertexSet; exact hz) hEdge w.seq hwG
      rcases hwH with ⟨wH, hwHin, hwh, hwt⟩
      refine ⟨wH, hwHin, ?_, ?_⟩ <;> grind
    have := numComponents_ge (G := G) (H := H) (by rfl) hReachGH
    grind

/-- An edge is a bridge iff it lies on no cycle. -/
theorem iff {G : SimpleGraph α} (e : Edge α) (he : e ∈ G.edgeSet) :
    IsBridge G e ↔
      ¬ ∃ w : Walk α, IsVertexSeqIn G w.seq ∧ Walk.IsCycle w ∧ e ∈ w.edgeSet := by
  constructor
  · exact bridge_not_inCycle e he
  · intro hno
    by_contra hbridge
    exact hno (nonBridge_inCycle e he hbridge)


/-- In an acyclic graph, every edge is a bridge. -/
lemma isBridge_of_acyclic_edge {G : SimpleGraph α} (e : Edge α)
    (hacy : Acyclic G) (he : e ∈ G.edgeSet) :
    IsBridge G e := by
  by_contra hbridge
  have hcycle := nonBridge_inCycle e he hbridge
  exact hacy (by
    rcases hcycle with ⟨w, hwG, hwCycle, _⟩
    exact ⟨w, hwG, hwCycle⟩)

end Bridge

end SimpleGraph
