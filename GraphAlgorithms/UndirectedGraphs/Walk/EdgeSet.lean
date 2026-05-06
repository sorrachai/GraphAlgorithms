import GraphAlgorithms.Core.Walk
import GraphAlgorithms.UndirectedGraphs.SimpleGraphs

-- Authors: Weixuan Yuan
variable {α : Type*} [DecidableEq α]

set_option tactic.hygienic false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open scoped SimpleGraph

namespace VertexSeq

/-! ### Edge sets of vertex sequences -/

/-- The undirected edges traversed by a vertex sequence. -/
abbrev edgeSet (w : VertexSeq α) : Finset (Edge α) :=
  match w with
  | .singleton _ => ∅
  | .cons w u => w.edgeSet ∪ {s(w.tail, u)}

/-- Taking a prefix cannot introduce new traversed edges. -/
@[grind →, grind ←] lemma takeUntil_edges_subset (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) :
    (w.takeUntil v h).edgeSet ⊆ w.edgeSet := by
  induction w generalizing v
  · intro a ha; simp [takeUntil] at ha
  · by_cases h2 : v ∈ w_1.toList
    · grind
    · simp [takeUntil, h2]

/-- Loop erasure cannot introduce new traversed edges. -/
@[grind ←] lemma loopErase_edges_subset (w : VertexSeq α) :
    w.loopErase.edgeSet ⊆ w.edgeSet := by
  suffices h : ∀ n : ℕ, ∀ w : VertexSeq α,
      w.length = n → w.loopErase.edgeSet ⊆ w.edgeSet by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen; cases w
  · intro a ha; simp [loopErase, edgeSet] at ha
  · by_cases hmem : v ∈ w_1.toList
    · grind [takeUntil_length_le]
    · intro a ha
      have ha' : a = s(w_1.loopErase.tail, v) ∨ a ∈ w_1.loopErase.edgeSet := by
            simpa [loopErase, hmem] using ha
      grind [tail_loopErase]

/-- The left endpoint of an edge in a sequence's edge set appears in the sequence. -/
@[grind →] lemma left_mem_of_edge {u v : α} :
  ∀ w : VertexSeq α, s(u, v) ∈ w.edgeSet → u ∈ w.toList := by
  intro w; induction w <;> grind

/-- The right endpoint of an edge in a sequence's edge set appears in the sequence. -/
@[grind →] lemma right_mem_of_edge {u v : α} :
  ∀ w : VertexSeq α, s(u, v) ∈ w.edgeSet → v ∈ w.toList := by
  intro w; induction w <;> grind

/-- The edge set of an appended sequence is the union plus the connecting edge. -/
lemma append_edges (p q : VertexSeq α) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet ∪ {s(p.tail, q.head)} := by
  induction q generalizing p;
  · ext e; simp [VertexSeq.append, edgeSet]
  · ext e
    simp only [VertexSeq.append, edgeSet, w_ih, Finset.mem_union,
      Finset.mem_singleton, VertexSeq.append_tail, VertexSeq.cons_head_eq]
    grind

/-- Every original edge appears in the prefix or suffix cut at a support vertex. -/
lemma split_edges_subset
    (w : VertexSeq α) (u : α) (hu : u ∈ w.toList) :
    w.edgeSet ⊆ (w.takeUntil u hu).edgeSet ∪ (w.dropUntil u hu).edgeSet := by
  induction w generalizing u
  · grind
  · intro e he
    by_cases hmem : u ∈ w_1.toList
    · simp [hmem]; grind
    · simp [hmem]; grind

/-- In a duplicate-free sequence, dropping to `v` removes edges incident to the old head. -/
lemma not_incident_dropUntil
    (w : VertexSeq α) (u v : α) (hv : v ∈ w.toList)
    (hnd : w.toList.Nodup) (hhead : w.head = u) (hne : u ≠ v) :
    s(u, v) ∉ (w.dropUntil v hv).edgeSet := by
  induction w generalizing v <;> grind

/-- A nontrivial duplicate-free sequence using an edge from the head
does not end at its other endpoint. -/
lemma tail_ne_of_incident
    (w : VertexSeq α) (u v : α) (he : s(u, v) ∈ w.edgeSet)
    (hnd : w.toList.Nodup) (hhead : w.head = u) (hlen : w.length ≠ 1) :
    w.tail ≠ v := by cases w <;> grind

end VertexSeq

namespace Walk
open VertexSeq

/-! ### Edge sets of walks -/

/-- The undirected edges traversed by a walk. -/
abbrev edgeSet (w : Walk α) : Finset (Edge α) := w.seq.edgeSet

/-- Converting a walk to a path cannot introduce new traversed edges. -/
lemma toPath_edges_subset (w : Walk α) : w.toPath.edgeSet ⊆ w.edgeSet := by
  simpa [edgeSet] using VertexSeq.loopErase_edges_subset w.seq

/-- A length-zero walk traverses no edges. -/
lemma edges_empty_of_zero (w : Walk α) (h : w.length = 0) :
    w.edgeSet = ∅ := by
  cases w; induction valid <;> grind

/-- A positive-length walk's edge set is its dropped-tail edge set plus its last edge. -/
lemma dropTail_edges (w : Walk α) (h : w.length ≠ 0) :
    w.edgeSet = w.dropTail.edgeSet ∪ {s(w.dropTail.tail, w.tail)} := by
  cases w; induction valid <;> grind

/-- Appending walks unions their edge sets. -/
lemma append_edges (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).edgeSet = w1.edgeSet ∪ w2.edgeSet := by
  grind [edges_empty_of_zero, dropTail_edges, VertexSeq.append_edges]

/-- A walk with empty edge set has equal endpoints. -/
lemma endpoints_eq_of_no_edges (w : Walk α) (h : w.edgeSet = ∅) :
    w.head = w.tail := by
  cases w; induction valid
  · grind
  · have hmem : s(w.tail, u) ∈ (w.cons u).edgeSet := by simp [VertexSeq.edgeSet]
    grind

/-- A cycle has a nonempty edge set. -/
lemma cycle_edges_nonempty (w : Walk α) (hcycle : Walk.IsCycle w) :
    w.edgeSet.Nonempty := by
  have hpos : w.length ≠ 0 := by
    have hlen3 : 3 ≤ w.length := hcycle.1
    omega
  have hlast : s(w.dropTail.tail, w.tail) ∈ w.edgeSet := by
    rw [dropTail_edges w hpos]
    simp
  exact ⟨s(w.dropTail.tail, w.tail), hlast⟩

/-- In a path, the final edge is not already present in the dropped-tail walk. -/
lemma lastEdge_fresh
    (w : Walk α) (hPath : Walk.IsPath w) (hpos : w.length ≠ 0) :
    s(w.dropTail.tail, w.tail) ∉ w.dropTail.edgeSet := by grind

/-- If a path uses an edge ending at its tail, that edge is the final edge. -/
lemma tail_of_lastEdge
    {w : Walk α} {a b : α} (hPath : Walk.IsPath w)
    (htail : w.tail = b) (hab : a ≠ b) (he : s(a, b) ∈ w.edgeSet) :
    w.length ≠ 0 ∧ w.dropTail.tail = a := by
  cases w; cases valid
  · grind
  · have hlast : s(a, b) = s(w.tail, b) := by grind
    have hpairs : a = w.tail ∧ b = b ∨ a = b ∧ b = w.tail := by
      have hmk : s((a, b).1, (a, b).2) = s((w.tail, b).1, (w.tail, b).2) := by
        exact hlast
      rcases Sym2.mk_eq_mk_iff.mp hmk with hp | hp <;> grind
    rcases hpairs with hpairs | hpairs <;> grind

end Walk
