import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.DirectedGraphs.SimpleDiGraphs
import GraphAlgorithms.DirectedGraphs.Walk

-- Breadth-first Search
-- Authors: Huang, JiangYi

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

open SimpleDiGraph
open Walk

namespace bfsAlgorithm

/-- Core BFS traversal that computes distances from a fixed root to all vertices.
    Processes one frontier level per recursive call, accumulating distances in `dist`.

    Parameters:
    - `G`        : the directed graph being searched
    - `n`        : termination counter, initialised to `Fintype.card α`;
                   decreases by 1 each call so Lean accepts the recursion without a proof.
                   Since any shortest path visits at most `|V|` vertices,
                   `|V|` rounds always suffice.
    - `visited`  : the union of all frontier sets processed so far; prevents revisiting
    - `frontier` : the set of vertices at the current BFS level (distance `d` from root)
    - `d`        : the distance of the current frontier from the root
    - `dist`     : accumulated distance map; vertices not yet reached carry `⊤`
-/
def bfs [Fintype α] (G : SimpleDiGraph α) :
    ℕ → Finset α → Finset α → ℕ → (α → ℕ∞) → (α → ℕ∞)
  /- **Base case** (`n = 0`): counter exhausted — return accumulated `dist` as-is.
     Unreached vertices retain `⊤`. This branch is never reached when `n` is
     initialised to `Fintype.card α`. -/
  | 0,     _,       _,        _, dist => dist
  /- **Recursion case** when called with arguments
     `(n+1, visited, frontier, d, dist)`, do the following... -/
  | n + 1, visited, frontier, d, dist =>
    /- *Exhausted*: if `frontier = ∅`, no new vertices are reachable;
       all remaining vertices are unreachable and retain `⊤` in `dist`. -/
    if frontier = ∅ then dist
    else
      /- *Record*: assign distance `d` to every vertex in the current frontier. -/
      let dist' := fun v => if v ∈ frontier then (d : ℕ∞) else dist v
      /- *Expand*: compute `next`, the next frontier, as the out-neighbors of
         every vertex in `frontier`, minus all already-visited vertices:
         `next = (⋃ v ∈ frontier, N⁺(G, v)) \ visited` -/
      let next  := (Finset.biUnion frontier (fun v ↦ N⁺(G, v))) \ visited
      /- *Recurse*: advance one level — `visited` absorbs `next`,
         `frontier` becomes `next`, `d` increments by 1. -/
      bfs G n (visited ∪ next) next (d + 1) dist'

/-- BFS distance map from `v` to all vertices of `G`.
    Reachable vertices receive their shortest-path distance (as `(d : ℕ∞)`);
    unreachable vertices receive `⊤` (infinity). -/
def bfsDistances [Fintype α] (G : SimpleDiGraph α) (v : α) : α → ℕ∞ :=
  bfs G (Fintype.card α) {v} {v} 0 (fun _ => ⊤)

/-- The shortest distance from `v₁` to `v₂` in directed graph `G`.
    Returns `⊤` if `v₂` is unreachable from `v₁`. Computed via BFS. -/
def bfsDistance [Fintype α] (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  bfsDistances G v₁ v₂

end bfsAlgorithm


-- Analytical definition of `path` for bfs correctness analysis.
namespace Path

/-- A path is a walk whose support (the list of vertices from VertexSeq.toList)
    has no duplicate vertices — List.Nodup. -/
def IsPathIn [Fintype α] (G : SimpleDiGraph α) (w : Walk α) : Prop := IsWalkIn G w ∧ w.IsPath

/-- If w is a simple path (no repeated vertices) in G, and u is any vertex on that path,
    then the portion of the path from u onward is also a simple path in G. -/
lemma IsPathIn.suffix [Fintype α] (G : SimpleDiGraph α) (w : Walk α) (u : α)
    (hu : u ∈ w.support) (hw : IsPathIn G w) :
    IsPathIn G ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.valid⟩ := by
  constructor
  · -- IsWalkIn: edges of suffix are edges of w; prove by induction on IsWalkIn w
    induction hw.1 generalizing u with   -- hw.1 : IsWalkIn G w
    | singleton v hv =>
      simp only [Walk.support, VertexSeq.toList, List.mem_singleton] at hu
      subst hu
      simp only [VertexSeq.dropUntil]
      exact IsWalkIn.singleton u hv
    | cons w' u' hw' hedg ih =>
      simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hu
      by_cases hu' : u ∈ w'.seq.toList
      · -- suffix starts inside w': dropUntil goes deeper, then re-attaches u'
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_pos hu']
        expose_names; simp_all
        -- Prove the IsWalkIn for the suffix:
        -- the new walk is w'.seq.dropUntil u hu' with u' appended;
        -- the new walk is a walk in G because w' is a walk in G
        -- and the edge from w'.tail to u' is in G.
        -- #TODO: the current proof reads obsecure;
        --        can we clean it up to a few more readable lemmas?
        exact IsWalkIn.cons ⟨w'.seq.dropUntil u hu', dropUntil_iswalk w'.seq u hu' w'.valid⟩ u'
          (ih u hu' ⟨hw', by
            have hpath := hw.2
            simp only [Walk.IsPath, Walk.support,
              Walk.append_single, VertexSeq.toList, List.nodup_cons] at hpath
            exact hpath.2⟩)
          (by
            have htail :
              (
                ⟨w'.seq.dropUntil u hu', dropUntil_iswalk w'.seq u hu' w'.valid⟩ : Walk α
              ).tail = w'.tail :=
              VertexSeq.tail_dropUntil w'.seq u hu'
            exact htail ▸ hedg)
      · -- suffix starts at u': dropUntil stops immediately
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_neg hu']
        exact IsWalkIn.singleton u' (G.incidence _ hedg).2
  · -- IsPath: suffix support is duplicate-free (dropUntil preserves Nodup)
    unfold Walk.IsPath Walk.support
    exact VertexSeq.dropUntil_toList_nodup hu hw.2


/-- Shortest path - analytical definition of distance:
    the length of minimum path between two vertices `v₁` and `v₂` in graph `G` -/
noncomputable def shortestPath [Fintype α] (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  /- ⨅: the indexed infimum (greatest lower bound) operator.
     - `⨅ (x : T), f x` is `iInf f`
     - `⨅ (x : T) (_ : P x), f x` is `iInf (fun x => iInf (fun _ : P x => f x))`,
       a nested `iInf` where the inner one ranges over proofs of `P x`.
       When `P x` is False (no proof exists), `iInf` over an empty type gives `⊤`.
     Here it means the infimum (minimum) of `w.length` over all walks `w` satisfying the condition.
     When the condition is empty (no such path exists), ⨅ over an empty set
     in ℕ∞ gives ⊤ (infinity) automatically. -/
  ⨅ (w : Walk α) (_ : IsPathIn G w ∧ w.head = v₁ ∧ w.tail = v₂), (w.length : ℕ∞)

-- /-- Lemma 22.1 in CLRS: the triangle inequality for shortest paths.
--     ∀ s ∈ V(G), ∀ (u, v) ∈ E(G), shortestPath G s v ≤ shortestPath G s u + 1 -/
-- lemma shortestPath_triangle_inequality [Fintype α] (G : SimpleDiGraph α) (s u v : α)
--     (h_su : shortestPath G s u ≠ ⊤) (h_uv : (u, v) ∈ E(G)) :
--     shortestPath G s v ≤ shortestPath G s u + 1 := by
--   sorry

end Path


namespace bfsCorrectness

-- /-- Lemma 22.2 in CLRS: BFS bounds the shortest path.
--     Suppose that BFS is run on G from a given source vertex s ∈ V.
--     Then upon termination, ∀ v ∈ V, the distance computed by BFS satisfies:
--     bfsDistances G s v ≥ shortestPath G s v -/
-- lemma bfs_bounds_shortest_path [Fintype α] (G : SimpleDiGraph α) (s v : α)
--     (h_s : s ∈ G.vertexSet) :
--     bfsAlgorithm.bfsDistances G s v ≥ Path.shortestPath G s v := by
--   sorry

-- /-- Lemma 22.3 in CLRS: During the execution of BFS on a graph G,
--     the `frontier` contains the vertices {v₁, ..., vᵣ}, where v₁ is the head and vᵣ is the tail.
--     Then dist' vᵣ ≤ dist' v₁ + 1. -/
-- lemma bfs_triangle_inequality [Fintype α] (G : SimpleDiGraph α) (root : α) (v₁ v₂ : α)
--     (h_root : root ∈ G.vertexSet) :
--     bfsAlgorithm.bfsDistances G root v₂ ≤ bfsAlgorithm.bfsDistances G root v₁ + 1 := by
--   sorry

-- /-- Corollary 22.4 in CLRS: For vertices vᵢ and vⱼ are enqueued during the execution of BFS,
--     and that vᵢ is enqueued before vⱼ. Then dist' vᵢ ≤ dist' vⱼ at the time that vⱼ is enqueued.
--     * This turns out a tautology in our implementation. -/
-- lemma bfs_enqueue_order [Fintype α] (G : SimpleDiGraph α) (root : α) (vᵢ vⱼ : α)
--     (h_root : root ∈ G.vertexSet)
--     (h_enqueue : bfsAlgorithm.bfsDistances G root vᵢ ≤ bfsAlgorithm.bfsDistances G root vⱼ) :
--     bfsAlgorithm.bfsDistances G root vᵢ ≤ bfsAlgorithm.bfsDistances G root vⱼ := by
--   sorry

/-- Helper lemma to prove `bfs_complete_aux`:
    Once a vertex is in `visited` and not in the current frontier,
    BFS never changes its recorded distance. -/
lemma bfs_stable [Fintype α] (G : SimpleDiGraph α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞)
    (v : α) (hv_vis : v ∈ visited) (hv_fron : v ∉ frontier) :
    bfsAlgorithm.bfs G n visited frontier d dist v = dist v := by
  induction n generalizing visited frontier d dist with
  | zero => simp [bfsAlgorithm.bfs]
  | succ n ih =>
    simp only [bfsAlgorithm.bfs]
    split_ifs with h_empty
    · -- frontier = ∅: bfs returns dist unchanged
      rfl
    · -- frontier ≠ ∅: record dist', compute next, recurse
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      -- v ∉ next because next ⊆ complement of visited, but v ∈ visited
      have hv_not_next : v ∉ next :=
        fun h => (Finset.mem_sdiff.mp h).2 hv_vis
      -- Apply IH: v ∈ visited ∪ next (from hv_vis), v ∉ next (proved above)
      rw [ih (visited ∪ next) next (d + 1) dist' (Finset.mem_union_left _ hv_vis) hv_not_next]
      simp [dist', if_neg hv_fron]

/-- Helper lemma to prove `bfs_complete`:
    If a path of length k from root to v exists avoiding all vertices in visited,
    then after k more BFS rounds, v will appear in dist with value ≤ d + k. -/
lemma bfs_complete_aux [Fintype α] (G : SimpleDiGraph α) (root v : α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    (w : Walk α) (hw : Path.IsPathIn G w) (hw_head : w.head ∈ frontier)
    (hw_tail : w.tail = v) (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited)
    (hn : w.length < n) :
    bfsAlgorithm.bfs G n visited frontier d init_dist v ≤ d + w.length := by
  induction n generalizing visited frontier d init_dist w with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [bfsAlgorithm.bfs]
    split_ifs with h_empty
    · -- frontier = ∅: contradicts hw_head
      simp [h_empty] at hw_head
    · -- frontier ≠ ∅
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      -- Case split on walk length
      rcases Nat.eq_zero_or_pos w.length with h_len | h_len
      · -- w.length = 0, so w is a trivial walk, v = w.head ∈ frontier
        -- v gets distance d from dist', then bfs_stable keeps it
        have hv_front : v ∈ frontier :=
          hw_tail ▸ (Walk.head_eq_tail_of_length_zero w h_len ▸ hw_head)
          -- Alternatively, in tactic mode:
          -- by have h_eq := Walk.head_eq_tail_of_length_zero w h_len  -- w.head = w.tail
          -- rw [← hw_tail, ← h_eq]; exact hw_head
        have hv_vis : v ∈ visited := hfv hv_front
        have hv_not_next : v ∉ next := fun h => (Finset.mem_sdiff.mp h).2 hv_vis
        rw [bfs_stable G n (visited ∪ next) next (d + 1) dist' v
              (Finset.mem_union_left _ hv_vis) hv_not_next]
        simp only [dist', if_pos hv_front]
        simp [h_len]
      · -- w.length = k + 1, decompose walk
        -- get the second vertex in the support (index 1) and split the walk there
        have h_support_len : w.support.length = w.length + 1 := by
          simp [Walk.support, VertexSeq.toList_length_eq]
        sorry

/-- Sub Goal A for `bfs_correct`:
    If a path of length `k` exists from `root` vertex to `v` in `G`,
    then BFS returns `distance ≤ k` for `v`. -/
lemma bfs_complete [Fintype α] (G : SimpleDiGraph α) (root : α) (v : α) (k : ℕ)
    (hk : ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧ (w.length : ℕ∞) = k) :
    bfsAlgorithm.bfsDistance G root v ≤ k := by
  sorry

/-- Sub Goal B for `bfs_correct`:
    If `bfs G n visited frontier d dist v` = k,
    then there exists a valid path in `G` from `root` vertex to `v` of `length k`. -/
lemma bfs_sound [Fintype α] (G : SimpleDiGraph α) (root : α) (v : α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    -- INV-1: every distance already in `init_dist` corresponds to a real path from `root`
    (h_dist : ∀ v : α, init_dist v ≠ ⊤ →
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = init_dist v)
    -- INV-2: every `frontier` vertex has a path of length `d` whose vertices lie in `visited`
    (h_front : ∀ v ∈ frontier,
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited)
    (hv : bfsAlgorithm.bfs G n visited frontier d init_dist v ≠ ⊤) :
    ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
        (w.length : ℕ∞) = bfsAlgorithm.bfs G n visited frontier d init_dist v := by
  induction n generalizing visited frontier d init_dist with
  | zero =>
    simp only [bfsAlgorithm.bfs] at hv ⊢
    exact h_dist v hv
  | succ n ih =>
    simp only [bfsAlgorithm.bfs] at hv ⊢
    split_ifs with h_empty
    · -- frontier = ∅: bfs returns init_dist unchanged
      simp only [h_empty] at hv
      exact h_dist v hv
    · -- frontier ≠ ∅: record dist', compute next, recurse
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      apply ih (visited ∪ next) next (d + 1) dist'
      · -- h_dist': ∀ u, dist' u ≠ ⊤ → ∃ path ...
        intro u hu
        simp only [dist'] at hu
        split_ifs at hu with hu_front
        · -- u ∈ frontier: dist' u = d, path comes from h_front
          obtain ⟨w, hw_path, hw_head, hw_tail, hw_len, _⟩ := h_front u hu_front
          simp only [dist', if_pos hu_front]
          exact ⟨w, hw_path, hw_head, hw_tail, hw_len⟩
        · -- u ∉ frontier: dist' u = init_dist u, path comes from h_dist
          simp only [dist', if_neg hu_front]
          exact h_dist u hu
      · -- h_front': ∀ u ∈ next, ∃ path of length d+1 ...
        -- Save u ∈ next before destructuring (needed later for the support proof):
        intro u hu_next
        have hu_in_next : u ∈ next := hu_next
        rw [Finset.mem_sdiff, Finset.mem_biUnion] at hu_next
        obtain ⟨⟨v_src, hv_front, hv_neigh⟩, hu_not_vis⟩ := hu_next
        -- Extract the edge from N⁺:
        simp only [OutNeighbors, Finset.mem_filter] at hv_neigh
        obtain ⟨_, e, he_edge, he1, he2, _⟩ := hv_neigh
        have hedg : (v_src, u) ∈ G.edgeSet := by
          have : e = (v_src, u) := Prod.ext he1.symm he2.symm; rwa [← this]
        -- Get path to v_src:
        obtain ⟨w_v, hw_path, hw_head, hw_tail, hw_len, hw_supp⟩ := h_front v_src hv_front
        -- Prove u ≠ w_v.tail (required by append_single):
        have h_neq : u ≠ w_v.tail := hw_tail ▸ Ne.symm (G.loopless (v_src, u) hedg)
        -- Construct the extended walk and prove all fields:
        refine ⟨w_v.append_single u h_neq, ?_, ?_, ?_, ?_, ?_⟩
        · -- IsPathIn: IsWalkIn ∧ IsPath
          constructor
          · exact IsWalkIn.cons w_v u hw_path.1 (hw_tail ▸ hedg)
          · simp only [Walk.IsPath, Walk.append_single, Walk.support, VertexSeq.toList]
            exact List.nodup_cons.mpr ⟨fun h => hu_not_vis (hw_supp u h), hw_path.2⟩
        · -- head = root
          change (w_v.seq.cons u).head = root
          rw [VertexSeq.con_head_eq]
          -- Walk.head is abbrev for w.seq.head, so hw_head : w_v.seq.head = root
          change w_v.head = root; exact hw_head
        · -- tail = u
          rfl
        · -- length cast = d + 1
          have hlen : (w_v.append_single u h_neq).length = 1 + w_v.length := rfl
          rw [hlen]; push_cast
          rw [hw_len]; ring
        · -- support ⊆ visited ∪ next
          intro x hx
          simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_union_right _ hu_in_next
          · exact Finset.mem_union_left _ (hw_supp x hx)
      · simp only [h_empty] at hv; exact hv

theorem bfs_correct [Fintype α] (G : SimpleDiGraph α) (v₁ v₂ : α)
    (h₁ : v₁ ∈ G.vertexSet) :
    bfsAlgorithm.bfsDistance G v₁ v₂ = Path.shortestPath G v₁ v₂ := by
  apply le_antisymm
  · -- Goal A: Distance G v₁ v₂ ≤ shortestPath G v₁ v₂
    unfold Path.shortestPath
    apply le_iInf; intro w
    apply le_iInf; intro ⟨hw_path, hw_head, hw_tail⟩
    exact bfs_complete G v₁ v₂ w.length ⟨w, hw_path, hw_head, hw_tail, rfl⟩
  · -- Goal B: shortestPath G v₁ v₂ ≤ Distance G v₁ v₂
    unfold Path.shortestPath
    sorry

end bfsCorrectness

-- #TODOs:
-- 1. A theorem to show whether the definitions can find a shortest path in a graph
-- 2. Try replicate the `UndirectedGraphs.Walk` into the `DirectedGraphs.Walk` -/
