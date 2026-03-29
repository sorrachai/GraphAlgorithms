/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import GraphAlgorithms.UndirectedGraphs.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

/-
  **TODO**: Rename once the structure is clear.
-/
namespace Set.graphOn_nonempty

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! # Matchings -/

/-- A matching in `G` is a set of pairwise vertex-disjoint edges. -/
structure Matching (G : SimpleGraph α β) where
  edges : Finset (Edge α β)
  subset : ↑edges ⊆ E(G)
  pairwise_disjoint : ∀ e ∈ edges, ∀ f ∈ edges,
    e ≠ f → Disjoint e.endpoints.toFinset f.endpoints.toFinset

variable {G : SimpleGraph α β}

/-- The size of a matching. -/
abbrev Matching.size (M : Matching G) : ℕ := M.edges.card

/-- A matching is maximal if no edge can be added to it. -/
def IsMaximal (M : Matching G) : Prop :=
  ∀ M' : Matching G, M.edges ⊆ M'.edges → M.edges = M'.edges

/-- A matching is maximum if no matching has more edges. -/
def IsMaximum (M : Matching G) : Prop :=
  ∀ M' : Matching G, M'.size ≤ M.size

/-- `ν(G)` — the matching number is the size of a maximum matching. -/
noncomputable def matchingNr (G : SimpleGraph α β) : ℕ :=
  sSup { n : ℕ | ∃ M : Matching G, M.size = n }

scoped notation "ν(" G ")" => matchingNr G

/-- A matching is perfect if every vertex is an endpoint of an edge in the matching. -/
def IsPerfectMatching (M : Matching G) : Prop :=
  M.edges.biUnion (fun e => e.endpoints.toFinset) =
    VF((G : FinGraph α β))

/-! ## Covered vertices -/

/-- Vertex `v` is covered by `M` if it is contained in an endpoint of an edge in `M`. -/
def IsCovered (M : Matching G) (v : α) : Prop :=
  v ∈ V(G) ∧ ∃ e ∈ M.edges, v ∈ e.endpoints.toFinset

/-- The set of covered vertices as a Finset. -/
noncomputable def coveredVertices (M : Matching G) : Finset α :=
  M.edges.biUnion (fun e => e.endpoints.toFinset)

/-- Two edges in a matching are incident iff they are equal. -/
lemma eq_of_not_disjoint
    {M : Matching G}
    {e f : Edge α β}
    (he : e ∈ M.edges) (hf : f ∈ M.edges)
    (h_inter : ¬Disjoint e.endpoints.toFinset f.endpoints.toFinset) :
    e = f := by
  by_contra h_contra
  exact h_inter (M.pairwise_disjoint e he f hf h_contra)

/-- The covered vertices are a subset of V(G). -/
lemma coveredVertices_subset (M : Matching G) :
  -- **TODO**: The casting is not nice here.
    ↑(coveredVertices M) ⊆ V(G) := by
  sorry

/-- Each edge of a simple graph has exactly 2 endpoints as a Finset. -/
lemma edge_card_two {e : Edge α β} (he : e ∈ E(G)) :
    e.endpoints.toFinset.card = 2 := by
  rw [Sym2.card_toFinset]
  split_ifs with h
  · exfalso; exact G.loopless e he h
  · rfl

/-- The number of covered vertices is twice the matching size. -/
lemma coveredVertices_card (M : Matching G) :
    (coveredVertices M).card = 2 * M.size := by
  sorry

/-- A perfect matching covers an even number of vertices. -/
theorem perfect_matching_even_vertices (M : Matching G)
    (h : IsPerfectMatching M) :
    Even VF((G : FinGraph α β)).card := by
  sorry

/-- A perfect matching is maximum. -/
theorem perfect_is_maximum (M : Matching G)
    (h : IsPerfectMatching M) : IsMaximum M := by
  sorry

/-- A maximum matching is maximal. -/
theorem maximum_is_maximal (M : Matching G) (h : IsMaximum M) :
    IsMaximal M := by
  intro M' hM'
  have := h M'
  exact (Finset.subset_iff_eq_of_card_le this).mp hM'

/-! ## Alternating and augmenting paths -/

/-- A walk is alternating w.r.t. `M` if its edges alternate between `M` and `E(G) \ M`. -/
def IsAlternatingWalk (M : Matching G) {u v : α}
    (p : (u, v)-Walk-(α, β)) : Prop :=
  p.edges.Chain' (fun e1 e2 => (e1 ∈ M.edges) ↔ (e2 ∉ M.edges))

/-- An augmenting path for `M` is an alternating path whose endpoints are both uncovered by `M`. -/
def IsAugmentingPath (M : Matching G) {u v : α}
    (p : (u, v)-Walk-(α, β)) : Prop :=
  p.isPath ∧
  IsAlternatingWalk M p ∧
  ¬IsCovered M u ∧ ¬IsCovered M v ∧
  u ≠ v

/-! ## Berge's theorem -/

/-- **Berge's theorem**: a matching `M` is maximum iff there is no
    `M`-augmenting path. -/
theorem Berge (M : Matching G) :
    IsMaximum M ↔
    ¬∃ (u v : α) (p : (u, v)-Walk-(α, β)),
      p.InGraph (G : Graph α β) ∧ IsAugmentingPath M p := by
    constructor
    · intro h
      by_contra h_contra
      obtain ⟨u, v, p, h1, h2⟩ := h_contra
      -- reach a contradiction with maximality of M
      sorry
    · intro h
      unfold IsMaximum
      intro M'
      by_contra h_contra
      apply h
      simp at h_contra
      -- now XOR the graphs, there needs to be at least one augmenting path
      -- simply provide this path to conclude this proof
      sorry

/-- Corollary: an augmenting path yields a strictly larger matching. -/
theorem augmenting_path_gives_larger_matching
    {M : Matching G} {u v : α} {p : (u, v)-Walk-(α, β)}
    (hp : p.InGraph (G : Graph α β))
    (haug : IsAugmentingPath M p) :
    ∃ M' : Matching G, M'.size = M.size + 1 := sorry

/-! ## Matching algorithm helpers -/

attribute [local instance] Classical.propDecidable

/-- Symmetric difference of two edge sets. -/
noncomputable def edgeSymmDiff (S T : Finset (Edge α β)) : Finset (Edge α β) :=
  (S \ T) ∪ (T \ S)

/-- The matched partner of vertex `v` under `M`: the other endpoint of the
    unique matching edge incident to `v`, or `none` if `v` is unmatched. -/
noncomputable def Matching.partner (M : Matching G) (v : α) : Option α :=
  (M.edges.biUnion fun e =>
    if v ∈ e.endpoints.toFinset then e.endpoints.toFinset.erase v else ∅
  ).toList.head?

/-- Free (unmatched) vertices in `S` with respect to matching `M`. -/
noncomputable def freeIn (M : Matching G) (S : Finset α) : Finset α :=
  S.filter fun v => M.partner v = none

/-- Collect graph edges between consecutive vertices in a list. -/
noncomputable def consecutiveEdges (G : SimpleGraph α β) : List α → Finset (Edge α β)
  | [] | [_] => ∅
  | a :: b :: rest =>
    EF((G : FinGraph α β)).filter (fun e =>
      a ∈ e.endpoints.toFinset ∧ b ∈ e.endpoints.toFinset) ∪
    consecutiveEdges G (b :: rest)

/-! ## Hopcroft–Karp algorithm -/

section HopcroftKarp

/-- State of the Hopcroft–Karp algorithm: current matching and bipartition. -/
structure HKState (G : SimpleGraph α β) where
  matching : Matching G
  left : Finset α
  right : Finset α

/-- **BFS** from free left vertices through alternating edges.

    Computes layers of left-side vertices.  Each BFS step:
      left layer →[non-matching edge]→ right →[matching edge]→ next left layer.
    Stops when a non-matching edge reaches a free right vertex.
    Returns the layers and whether an augmenting path was found. -/
noncomputable def hkBFS (st : HKState G) : List (Finset α) × Bool :=
  let layer₀ := freeIn st.matching st.left
  bfsLoop st [layer₀] layer₀ layer₀ (VF((G : FinGraph α β)).card)
where
  bfsLoop (st : HKState G)
      (layers : List (Finset α)) (frontier visited : Finset α) :
      ℕ → List (Finset α) × Bool
  | 0 => (layers, false)
  | fuel + 1 =>
    if frontier.card = 0 then (layers, false) else
    -- Right-side vertices reachable via non-matching edges from frontier
    let rReach := st.right.filter fun v => v ∉ visited ∧
      ∃ u ∈ frontier, ∃ e ∈ EF((G : FinGraph α β)),
        e ∉ st.matching.edges ∧
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset
    -- If any free right vertex is reached, an augmenting path exists
    if (freeIn st.matching rReach).card > 0 then (layers, true)
    else
      -- Next left-side layer: matched partners of reached right vertices
      let nextLeft := st.left.filter fun w => w ∉ visited ∧
        ∃ v ∈ rReach, st.matching.partner v = some w
      bfsLoop st (layers ++ [nextLeft]) nextLeft (visited ∪ nextLeft) fuel

/-- Trace one augmenting path backwards from free right vertex `t` through
    BFS layers (given in reverse order, deepest first).  Returns the path
    edges and used vertices, or `(∅, ∅)` on failure. -/
noncomputable def hkTrace (st : HKState G) :
    List (Finset α) → α → Finset α → Finset (Edge α β) × Finset α
  | [], _, _ => (∅, ∅)
  | [layer₀], v, used =>
    -- Base: find a free left vertex in layer₀ adjacent to v
    match ((layer₀ \ used).filter fun u =>
      ∃ e ∈ EF((G : FinGraph α β)), e ∉ st.matching.edges ∧
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset).toList with
    | [] => (∅, ∅)
    | u :: _ =>
      match (EF((G : FinGraph α β)).filter fun e =>
        e ∉ st.matching.edges ∧
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset).toList with
      | [] => (∅, ∅)
      | e :: _ => ({e}, {u, v})
  | layer :: rest, v, used =>
    -- Find a left vertex in this layer adjacent to v via non-matching edge
    match ((layer \ used).filter fun u =>
      ∃ e ∈ EF((G : FinGraph α β)), e ∉ st.matching.edges ∧
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset).toList with
    | [] => (∅, ∅)
    | u :: _ =>
      -- Non-matching edge u — v
      match (EF((G : FinGraph α β)).filter fun e =>
        e ∉ st.matching.edges ∧
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset).toList with
      | [] => (∅, ∅)
      | e_uv :: _ =>
        -- Follow matching edge u — w
        match st.matching.partner u with
        | none => ({e_uv}, {u, v})
        | some w =>
          match (st.matching.edges.filter fun e =>
            u ∈ e.endpoints.toFinset ∧ w ∈ e.endpoints.toFinset).toList with
          | [] => (∅, ∅)
          | e_uw :: _ =>
            let (moreEdges, moreVerts) := hkTrace st rest w (used ∪ {u, w})
            ({e_uv, e_uw} ∪ moreEdges, {u, v, w} ∪ moreVerts)

/-- Find a maximal set of vertex-disjoint shortest augmenting paths.
    Returns the union of their edge sets. -/
noncomputable def hkFindPaths (st : HKState G) (layers : List (Finset α)) :
    Finset (Edge α β) :=
  let deepest := layers.getLast?.getD ∅
  let freeRight := (freeIn st.matching st.right).filter fun v =>
    ∃ u ∈ deepest, ∃ e ∈ EF((G : FinGraph α β)),
      e ∉ st.matching.edges ∧
      u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset
  -- Greedily collect vertex-disjoint paths
  (freeRight.toList.foldl
    (fun (acc : Finset (Edge α β) × Finset α) v =>
      let (edges, used) := acc
      let (newEdges, newVerts) := hkTrace st layers.reverse v used
      if newEdges.card > 0 then (edges ∪ newEdges, used ∪ newVerts) else acc)
    (∅, ∅)).1

/-- One **Hopcroft–Karp phase**: BFS to find layers, DFS to collect
    vertex-disjoint augmenting paths, augment along all of them. -/
noncomputable def hkPhase (st : HKState G) : HKState G :=
  let (layers, found) := hkBFS st
  if found then
    let pathEdges := hkFindPaths st layers
    { st with matching :=
        { edges := edgeSymmDiff st.matching.edges pathEdges
          subset := sorry
          pairwise_disjoint := sorry } }
  else st

/-- **Hopcroft–Karp algorithm**: iterate BFS+DFS phases until no augmenting
    path is found.  Fuel bounded by `|V|` (each phase increases the matching
    size by at least one). -/
noncomputable def hopcroftKarp
    (G : SimpleGraph α β) (left right : Finset α) (M₀ : Matching G) :
    Matching G :=
  hkLoop ⟨M₀, left, right⟩ (VF((G : FinGraph α β)).card)
where
  hkLoop (st : HKState G) : ℕ → Matching G
  | 0 => st.matching
  | fuel + 1 =>
    let (_, found) := hkBFS st
    if found then hkLoop (hkPhase st) fuel else st.matching

/-- **Hopcroft–Karp correctness**: the output is a maximum bipartite matching. -/
theorem hopcroftKarp_correct
    (G : SimpleGraph α β) (left right : Finset α) (M₀ : Matching G)
    (hBip : (left : Set α) ∪ right = V(G) ∧ Disjoint left right ∧
      ∀ e ∈ E(G), (∃ u ∈ left, u ∈ e.endpoints) ∧ (∃ v ∈ right, v ∈ e.endpoints)) :
    IsMaximum (hopcroftKarp G left right M₀) := sorry

/-- **Hopcroft–Karp phase bound**: at most `O(√|V|)` phases suffice. -/
theorem hopcroftKarp_phase_bound
    (G : SimpleGraph α β) (left right : Finset α) (M₀ : Matching G) :
    ∃ nphases : ℕ,
      nphases ≤ Nat.sqrt VF((G : FinGraph α β)).card + 1 ∧
      ∃ M : Matching G, IsMaximum M := sorry

end HopcroftKarp

/-! ## König's theorem -/

/-- A **vertex cover** is a set of vertices that touches every edge. -/
def IsVertexCover (G : SimpleGraph α β) (C : Finset α) : Prop :=
  ∀ e ∈ E(G), ∃ v ∈ C, v ∈ e.endpoints

/-- `τ(G)` — the **vertex cover number**: minimum size of a vertex cover. -/
noncomputable def vertexCoverNr (G : SimpleGraph α β) : ℕ :=
  sInf { n : ℕ | ∃ C : Finset α, IsVertexCover G C ∧ C.card = n }

scoped notation "τ(" G ")" => vertexCoverNr G

/-- In any graph, `ν(G) ≤ τ(G)`. -/
theorem matchingNr_le_vertexCoverNr (G : SimpleGraph α β) :
    ν(G) ≤ τ(G) := sorry

/-- **König's theorem**: in a bipartite graph, the maximum matching
    equals the minimum vertex cover: `ν(G) = τ(G)`. -/
theorem König (G : SimpleGraph α β) (hB : IsBipartite G) :
    ν(G) = τ(G) := sorry

/-! ## Hall's marriage theorem -/

/-- For a bipartite graph, the **neighbourhood** of `S` within `B`:
    vertices in `B` that are adjacent (via some edge) to a vertex in `S`. -/
noncomputable def bipartiteNeighbors
    (G : SimpleGraph α β) (B S : Finset α) : Finset α :=
  B.filter (fun v => (N((G : FinGraph α β), v) ∩ S).Nonempty)

/-- **Hall's condition**: for every `S ⊆ A`, `|N(S) ∩ B| ≥ |S|`. -/
def HallCondition (G : SimpleGraph α β) (A B : Finset α) : Prop :=
  ∀ S : Finset α, S ⊆ A → (bipartiteNeighbors G B S).card ≥ S.card

/-- **Hall's marriage theorem**: a bipartite graph `G` with sides `A`, `B`
    has a matching saturating `A` iff Hall's condition holds. -/
theorem Hall (G : SimpleGraph α β) (A B : Finset α)
    (hAB : (A : Set α) ∪ B = V(G)) (hDisj : Disjoint A B)
    (hBip : ∀ e ∈ E(G), (∃ u ∈ A, u ∈ e.endpoints) ∧
                          (∃ v ∈ B, v ∈ e.endpoints)) :
    (∃ M : Matching G, ∀ a ∈ A, ∃ e ∈ M.edges, a ∈ e.endpoints.toFinset)
    ↔ HallCondition G A B := sorry

/-! ## Tutte's theorem -/

/-- The number of **odd components** of `G \ S`: connected components of
    `G[V(G) \ S]` with an odd number of vertices. -/
noncomputable def oddComponents (G : SimpleGraph α β) (S : Finset α) : ℕ :=
  sorry

/-- **Tutte–Berge formula**: `ν(G) = ½ (|V(G)| - max_S (o(G-S) - |S|))`. -/
theorem TutteBerge (G : SimpleGraph α β) :
    2 * ν(G) = VF((G : FinGraph α β)).card -
      sSup { d : ℕ | ∃ S : Finset α, (S : Set α) ⊆ V(G) ∧
        d = oddComponents G S - S.card } := sorry

/-- **Tutte's theorem**: `G` has a perfect matching iff for every
    `S ⊆ V(G)`, the number of odd components of `G - S` is ≤ `|S|`. -/
theorem Tutte (G : SimpleGraph α β) :
    (∃ M : Matching G, IsPerfectMatching M) ↔
    ∀ S : Finset α, (S : Set α) ⊆ V(G) →
      oddComponents G S ≤ S.card := sorry

/-! ## Gallai identities -/

/-- An **edge cover** is a set of edges that touches every vertex. -/
def IsEdgeCover (G : SimpleGraph α β) (F : Finset (Edge α β)) : Prop :=
  (↑F : Set (Edge α β)) ⊆ E(G) ∧
  ∀ v ∈ V(G), ∃ e ∈ F, v ∈ e.endpoints

/-- `ρ(G)` — the **edge cover number**: minimum size of an edge cover
    (only meaningful when `G` has no isolated vertices). -/
noncomputable def edgeCoverNr (G : SimpleGraph α β) : ℕ :=
  sInf { n : ℕ | ∃ F : Finset (Edge α β), IsEdgeCover G F ∧ F.card = n }

/-
  I'm not sure if this is standard but I've seen it somewhere.
-/
scoped notation "ρ(" G ")" => edgeCoverNr G

/-- **Gallai's identity (vertex)**: `α(G) + τ(G) = |V(G)|`. -/
theorem Gallai_vertex (G : SimpleGraph α β)
    (hNoIso : ∀ v ∈ V(G), ∃ e ∈ E(G), v ∈ e.endpoints) :
    α(G) + τ(G) = VF((G : FinGraph α β)).card := sorry

/-- **Gallai's identity (edge)**: `ν(G) + ρ(G) = |V(G)|` for graphs
    without isolated vertices. -/
theorem Gallai_edge (G : SimpleGraph α β)
    (hNoIso : ∀ v ∈ V(G), ∃ e ∈ E(G), v ∈ e.endpoints) :
    ν(G) + ρ(G) = VF((G : FinGraph α β)).card := sorry

/-! ## Blossom algorithm (Edmonds) -/

section Blossom

/-- A **blossom** is an odd cycle `C` in `G` such that `M` matches all but
    one vertex of `C` using edges of `C`. -/
def IsBlossom (M : Matching G) (C : Finset α) : Prop :=
  ¬2 ∣ C.card ∧
  C.card ≥ 3 ∧
  (C : Set α) ⊆ V(G) ∧
  ∃ (u : α) (p : (u, u)-Walk-(α, β)),
    p.InGraph (G : Graph α β) ∧
    p.isCycle ∧
    p.support.tail.toFinset = C ∧
    -- All but one vertex of C are matched within C
    ∃ base ∈ C, ∀ v ∈ C, v ≠ base →
      ∃ e ∈ M.edges, v ∈ e.endpoints.toFinset ∧
        ∀ w ∈ e.endpoints.toFinset, w ∈ C

/-- State of the alternating forest in the blossom algorithm.
    Each tree is rooted at a free vertex. Outer (even-depth) vertices
    are potential path endpoints; inner (odd-depth) vertices are matched
    partners reached along alternating edges. -/
structure BlossomForest (G : SimpleGraph α β) where
  /-- Current matching. -/
  matching : Matching G
  /-- Outer (even-depth) vertices in the forest. -/
  outer : Finset α
  /-- Inner (odd-depth) vertices in the forest. -/
  inner : Finset α
  /-- Parent map: `parent v = some u` means `u` is the parent of `v`. -/
  parent : α → Option α
  /-- Root map: `root v = some r` means `v` is in the tree rooted at `r`. -/
  root : α → Option α

/-- Initialise the alternating forest: free vertices become outer roots. -/
noncomputable def BlossomForest.init (M : Matching G) : BlossomForest G :=
  let free := freeIn M VF((G : FinGraph α β))
  { matching := M
    outer := free
    inner := ∅
    parent := fun _ => none
    root := fun v => if v ∈ free then some v else none }

/-- Trace the path from `v` to the root of its alternating tree. -/
noncomputable def BlossomForest.pathToRoot (F : BlossomForest G) (v : α) :
    List α :=
  go v (VF((G : FinGraph α β)).card)
where
  go (v : α) : ℕ → List α
  | 0 => [v]
  | fuel + 1 =>
    match F.parent v with
    | none => [v]
    | some u => v :: go u fuel

/-- Lowest common ancestor of `u` and `v` in the forest. -/
noncomputable def BlossomForest.lca (F : BlossomForest G) (u v : α) : α :=
  let pathU := F.pathToRoot u
  let pathVSet := (F.pathToRoot v).toFinset
  match pathU.filter (· ∈ pathVSet) with
  | [] => u
  | x :: _ => x

/-- Blossom vertices: the odd cycle through outer vertices `u`, `v` that
    share the same tree, passing through their lowest common ancestor. -/
noncomputable def BlossomForest.blossomVerts (F : BlossomForest G)
    (u v : α) : Finset α :=
  let b := F.lca u v
  let pathU := (F.pathToRoot u).takeWhile (· ≠ b) ++ [b]
  let pathV := (F.pathToRoot v).takeWhile (· ≠ b)
  (pathU ++ pathV).toFinset

/-- Grow the forest: add `v` as inner child of outer vertex `u`, and
    `w = match(v)` as outer child of `v`. -/
noncomputable def BlossomForest.grow (F : BlossomForest G)
    (u v w : α) : BlossomForest G :=
  { F with
    inner := F.inner ∪ {v}
    outer := F.outer ∪ {w}
    parent := fun x =>
      if x = v then some u else if x = w then some v else F.parent x
    root := fun x =>
      if x = v ∨ x = w then F.root u else F.root x }

/-- Edges of the augmenting path `root(u) → ⋯ → u — v → ⋯ → root(v)`,
    where `u` and `v` are outer vertices in different trees. -/
noncomputable def BlossomForest.augPathEdges (F : BlossomForest G)
    (u v : α) : Finset (Edge α β) :=
  let treeEdgesU := consecutiveEdges G (F.pathToRoot u)
  let treeEdgesV := consecutiveEdges G (F.pathToRoot v)
  let bridge := EF((G : FinGraph α β)).filter fun e =>
    e ∉ F.matching.edges ∧
    u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset
  treeEdgesU ∪ bridge ∪ treeEdgesV

/-- Result of scanning non-matching edges in the forest. -/
inductive ScanResult (α : Type*) where
  /-- Augmenting path found through edge `u—v` (different trees). -/
  | augment (u v : α)
  /-- Blossom detected: odd cycle with given vertices and base. -/
  | blossom (verts : Finset α) (base : α)
  /-- Forest can be grown: add `v` (inner) and `w` (outer) via `u`. -/
  | grow (u v w : α)
  /-- No useful edge remains: matching is maximum. -/
  | done

/-- Scan non-matching edges for the next forest operation.

    For each non-matching edge with an outer endpoint `u` and other
    endpoint `v ∉ inner`:
    - `v` not in forest, `v` free  → augmenting path
    - `v` not in forest, `v` matched to `w` → grow (add `v`, `w`)
    - `v` outer, different tree from `u` → augmenting path
    - `v` outer, same tree as `u` → blossom -/
noncomputable def blossomScan (F : BlossomForest G) : ScanResult α :=
  let useful := EF((G : FinGraph α β)).filter fun e =>
    e ∉ F.matching.edges ∧
    ∃ u ∈ e.endpoints.toFinset, u ∈ F.outer ∧
      ∃ v ∈ e.endpoints.toFinset, v ≠ u ∧ v ∉ F.inner
  match useful.toList with
  | [] => .done
  | e :: _ =>
    match (e.endpoints.toFinset.filter (· ∈ F.outer)).toList with
    | [] => .done
    | u :: _ =>
      match (e.endpoints.toFinset.erase u).toList with
      | [] => .done
      | v :: _ =>
        if v ∉ F.outer ∧ v ∉ F.inner then
          -- v is not in the forest
          match F.matching.partner v with
          | none => .augment u v     -- v is free
          | some w => .grow u v w    -- extend tree through v → w
        else if v ∈ F.outer then
          -- both endpoints are outer
          if F.root u ≠ F.root v then .augment u v
          else .blossom (F.blossomVerts u v) (F.lca u v)
        else .done

/-- Contract a blossom and lift the resulting matching back.

    Given blossom vertices `bVerts` with base `base`:
    1. Construct the contracted graph by merging `bVerts` into `base`.
    2. Project the current matching onto the contracted graph.
    3. Find a maximum matching in the contracted graph (recursive call).
    4. Lift: if the contracted matching uses `base`, route through the
       blossom cycle to recover a matching in the original graph. -/
noncomputable def blossomContractAndLift (G : SimpleGraph α β)
    (M : Matching G) (bVerts : Finset α) (base : α) : Matching G :=
  sorry

/-- **Edmonds blossom algorithm**: grow the alternating forest, augment
    along discovered augmenting paths, and contract blossoms.

    Each step of the inner loop either:
    - **grows** the forest (adds two vertices → progress),
    - **augments** along a path (matching size increases → restart), or
    - **contracts** a blossom (reduces effective vertex count → progress).

    Fuel is bounded by `|V|²` (at most `|V|/2` augmentations, each needing
    at most `|V|` grow/contract steps). -/
noncomputable def blossomAlgorithm
    (G : SimpleGraph α β) (M₀ : Matching G) : Matching G :=
  go (BlossomForest.init M₀) (VF((G : FinGraph α β)).card ^ 2)
where
  go (F : BlossomForest G) : ℕ → Matching G
  | 0 => F.matching
  | fuel + 1 =>
    match blossomScan F with
    | .done => F.matching
    | .grow u v w =>
      go (F.grow u v w) fuel
    | .augment u v =>
      let pathEdges := F.augPathEdges u v
      let M' : Matching G :=
        { edges := edgeSymmDiff F.matching.edges pathEdges
          subset := sorry
          pairwise_disjoint := sorry }
      go (BlossomForest.init M') fuel
    | .blossom bVerts base =>
      let M' := blossomContractAndLift G F.matching bVerts base
      go (BlossomForest.init M') fuel

/-- **Blossom algorithm correctness**: the output is a maximum matching. -/
theorem blossomAlgorithm_correct
    (G : SimpleGraph α β) (M₀ : Matching G) :
    IsMaximum (blossomAlgorithm G M₀) := sorry

/-- **Blossom algorithm termination**: matching size ≤ ⌊|V|/2⌋. -/
theorem blossomAlgorithm_terminates
    (G : SimpleGraph α β) (M₀ : Matching G) :
    (blossomAlgorithm G M₀).size ≤ VF((G : FinGraph α β)).card / 2 := sorry

end Blossom

/-! ## Additional classical results -/

/-- Any graph satisfies `ν(G) · Δ(G) ≥ |E(G)|` where `Δ(G)` is the
    maximum degree. -/
theorem matching_lower_bound_by_maxdeg (G : SimpleGraph α β)
    (hne : (V(G)).Nonempty)
    (Δ : ℕ) (hΔ : ∀ v ∈ V(G), deg((G : FinGraph α β), v) ≤ Δ)
    (hΔpos : Δ > 0) :
    ν(G) * Δ ≥ EF((G : FinGraph α β)).card := sorry

/-- Every `k`-regular bipartite graph (`k ≥ 1`, non-empty) has a
    perfect matching. -/
theorem regular_bipartite_has_perfect_matching
    (G : SimpleGraph α β) (k : ℕ) (hk : k ≥ 1)
    (hReg : IsKRegular G k) (hBip : IsBipartite G)
    (hne : (V(G)).Nonempty) :
    ∃ M : Matching G, IsPerfectMatching M := sorry

/-- **Petersen's theorem**: every 2-edge-connected 3-regular graph has a
    perfect matching. -/
theorem Petersen (G : SimpleGraph α β)
    (h3reg : IsKRegular G 3)
    (h2ec : κ'(G) ≥ 2) :
    ∃ M : Matching G, IsPerfectMatching M := sorry

/-! ## Fractional matchings and LP duality -/

/-- A **fractional matching** assigns a weight `w(e) ∈ [0,1]` to each edge
    so that for every vertex the total weight of incident edges is ≤ 1. -/
def IsFractionalMatching (G : SimpleGraph α β) (w : Edge α β → ℝ) : Prop :=
  (∀ e, e ∈ E(G) → 0 ≤ w e ∧ w e ≤ 1) ∧
  (∀ e, e ∉ E(G) → w e = 0) ∧
  (∀ v ∈ V(G),
    (EF((G : FinGraph α β)).filter (fun e => v ∈ e.endpoints)).sum w ≤ 1)

/-- `ν*(G)` — the **fractional matching number**. -/
noncomputable def fracMatchingNr (G : SimpleGraph α β) : ℝ :=
  sSup { r : ℝ | ∃ w : Edge α β → ℝ, IsFractionalMatching G w ∧
    EF((G : FinGraph α β)).sum w = r }

/-- `ν(G) ≤ ν*(G)`: every integral matching is fractional. -/
theorem matchingNr_le_fracMatchingNr (G : SimpleGraph α β) :
    (ν(G) : ℝ) ≤ fracMatchingNr G := sorry

/-- **Birkhoff–von Neumann**: in a bipartite graph, `ν(G) = ν*(G)`. -/
theorem bipartite_integrality (G : SimpleGraph α β) (hB : IsBipartite G) :
    (ν(G) : ℝ) = fracMatchingNr G := sorry

/-- A **fractional vertex cover** assigns weights to vertices such that
    every edge has total endpoint weight ≥ 1. -/
def IsFractionalVertexCover (G : SimpleGraph α β) (w : α → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧
  (∀ v, v ∉ V(G) → w v = 0) ∧
  (∀ e ∈ E(G), ∀ u ∈ e.endpoints, ∀ v ∈ e.endpoints, u ≠ v →
    w u + w v ≥ 1)

/-- `τ*(G)` — the **fractional vertex cover number**. -/
noncomputable def fracVertexCoverNr (G : SimpleGraph α β) : ℝ :=
  sInf { r : ℝ | ∃ w : α → ℝ, IsFractionalVertexCover G w ∧
    VF((G : FinGraph α β)).sum w = r }

/-- **LP duality**: `ν*(G) = τ*(G)`. -/
theorem LP_duality_matching (G : SimpleGraph α β) :
    fracMatchingNr G = fracVertexCoverNr G := sorry

/-! ## Stable matchings -/

/-- A **stable matching instance**: bipartite graph with preference lists. -/
structure StableMatchingInstance (α β : Type*) [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β) where
  left : Finset α
  right : Finset α
  partition : (left : Set α) ∪ right = V(G)
  disjoint : Disjoint left right
  pref_left : α → List α
  pref_right : α → List α

/-- A matching is **stable** if no unmatched pair `(u, v)` mutually
    prefers each other over their current partners. -/
def IsStableMatching {G : SimpleGraph α β}
    (inst : StableMatchingInstance α β G) (M : Matching G) : Prop :=
  -- For every edge {u, v} with u on the left and v on the right,
  -- it is not the case that both u and v prefer each other to their
  -- current partners in M.
  ∀ e ∈ E(G), ∀ u ∈ e.endpoints, ∀ v ∈ e.endpoints,
    u ∈ inst.left → v ∈ inst.right → u ≠ v →
    -- At least one of u, v does not prefer the other
    ¬(-- u prefers v: v appears before current partner in pref_left u
      (∀ e' ∈ M.edges, u ∈ e'.endpoints.toFinset →
        ∀ w ∈ e'.endpoints.toFinset, w ≠ u →
          (inst.pref_left u).dropWhile (· ≠ v) ≠ []) ∧
      -- v prefers u: u appears before current partner in pref_right v
      (∀ e' ∈ M.edges, v ∈ e'.endpoints.toFinset →
        ∀ w ∈ e'.endpoints.toFinset, w ≠ v →
          (inst.pref_right v).dropWhile (· ≠ u) ≠ []))

/-- **Gale–Shapley theorem**: every stable matching instance admits a
    stable matching. -/
theorem GaleShapley {G : SimpleGraph α β}
    (inst : StableMatchingInstance α β G) :
    ∃ M : Matching G, IsStableMatching inst M := sorry

/-! ## Weighted matchings -/

/-- A **maximum-weight matching** maximises `∑_{e ∈ M} w(e)` over all
    matchings. -/
def IsMaxWeightMatching (G : SimpleGraph α β)
    (w : Edge α β → ℝ) (M : Matching G) : Prop :=
  ∀ M' : Matching G, M'.edges.sum w ≤ M.edges.sum w

/-- A **maximum-weight perfect matching** maximises the total weight
    among all perfect matchings. -/
def IsMaxWeightPerfectMatching (G : SimpleGraph α β)
    (w : Edge α β → ℝ) (M : Matching G) : Prop :=
  IsPerfectMatching M ∧
  ∀ M' : Matching G, IsPerfectMatching M' → M'.edges.sum w ≤ M.edges.sum w

/-- The **Hungarian algorithm** computes a maximum-weight perfect matching
    in a bipartite graph. -/
noncomputable def hungarian
    (G : SimpleGraph α β) (w : Edge α β → ℝ) : Option (Matching G) :=
  sorry

/-- **Hungarian algorithm correctness**. -/
theorem hungarian_correct
    (G : SimpleGraph α β) (w : Edge α β → ℝ) (hBip : IsBipartite G)
    {M : Matching G} (hM : hungarian G w = some M) :
    IsMaxWeightPerfectMatching G w M := sorry

/-! ## Deficiency and factor-critical graphs -/

/-- The **deficiency** of `G`: `def(G) = max_S (o(G-S) - |S|)`. -/
noncomputable def deficiency (G : SimpleGraph α β) : ℕ :=
  sSup { d : ℕ | ∃ S : Finset α, (S : Set α) ⊆ V(G) ∧
    d = oddComponents G S - S.card }

/-- `G` is **factor-critical** if `G - v` has a perfect matching for every
    vertex `v`. -/
def IsFactorCritical (G : SimpleGraph α β) : Prop :=
  ∀ v ∈ V(G), ∃ M : Matching (induce G (V(G) \ {v})),
    IsPerfectMatching M

/-- A factor-critical graph has an odd number of vertices. -/
theorem factor_critical_odd (G : SimpleGraph α β)
    (hFC : IsFactorCritical G) (hne : (V(G)).Nonempty) :
    ¬2 ∣ VF((G : FinGraph α β)).card := sorry

/-- **Edmonds–Gallai decomposition**: the vertex set of any graph can be
    partitioned into three sets `D`, `A`, `C` with structural properties
    that characterise the maximum matching. -/
theorem EdmondsGallai (G : SimpleGraph α β) :
    ∃ D A C : Finset α,
      -- partition of V(G)
      (D : Set α) ∪ A ∪ C = V(G) ∧
      Disjoint D A ∧ Disjoint D C ∧ Disjoint A C ∧
      -- D = set of vertices missed by some maximum matching
      (∀ v ∈ D, ∃ M : Matching G, IsMaximum M ∧ ¬IsCovered M v) ∧
      -- A = N(D)
      (∀ a ∈ A, ∃ d ∈ D, adj (G : Graph α β) a d) ∧
      -- every maximum matching matches all of A and C
      (∀ M : Matching G, IsMaximum M →
        (∀ a ∈ A, IsCovered M a) ∧ (∀ c ∈ C, IsCovered M c)) := sorry

/-! ## Micali–Vazirani algorithm

The Micali–Vazirani algorithm computes a maximum matching in a general
(not necessarily bipartite) graph in `O(|E| √|V|)` time, matching the
Hopcroft–Karp bound for bipartite graphs. (https://doi.org/10.1109/SFCS.1980.12)

**TODO**: Still wrong :c

-/

section MicaliVazirani

/-- A **bloom** (implicit blossom) encountered during the BFS phase.
    Stored as the bridge edge that detected it, the base (LCA), and
    the set of vertices in the bloom. -/
structure Bloom (α β : Type*) [DecidableEq α] [DecidableEq β] where
  bridge_u : α
  bridge_v : α
  base : α
  verts : Finset α

/-- State of one Micali–Vazirani phase. -/
structure MVPhaseState (G : SimpleGraph α β) where
  /-- Current matching. -/
  matching : Matching G
  /-- BFS distance label for each vertex (`none` = unreached). -/
  dist : α → Option ℕ
  /-- `even v = true` iff `v` is at even distance from a free vertex. -/
  even : α → Bool
  /-- Blooms discovered so far in this phase. -/
  blooms : List (Bloom α β)
  /-- Vertices used by augmenting paths found so far (for disjointness). -/
  used : Finset α

/-- Initialise a phase: BFS layer 0 consists of all free vertices, which
    are at even distance 0 from themselves. -/
noncomputable def MVPhaseState.init (M : Matching G) : MVPhaseState G :=
  let free := freeIn M VF((G : FinGraph α β))
  { matching := M
    dist := fun v => if v ∈ free then some 0 else none
    even := fun v => v ∈ free
    blooms := []
    used := ∅ }

/-- One BFS layer expansion.  From all vertices at distance `d`:
    - follow non-matching edges from even vertices (→ odd),
    - follow matching edges from odd vertices (→ even),
    handling bridges (even–even edges at equal distance) as blooms. -/
noncomputable def mvBFSStep (st : MVPhaseState G) (d : ℕ) :
    MVPhaseState G × Bool :=
  let frontier := VF((G : FinGraph α β)).filter fun v => st.dist v = some d
  -- Edges from frontier to unlabelled or same-distance-even vertices
  let newVerts := VF((G : FinGraph α β)).filter fun w =>
    st.dist w = none ∧ w ∉ st.used ∧
    ∃ v ∈ frontier, ∃ e ∈ EF((G : FinGraph α β)),
      v ∈ e.endpoints.toFinset ∧ w ∈ e.endpoints.toFinset ∧
      -- alternation: even→odd via non-matching, odd→even via matching
      ((st.even v ∧ e ∉ st.matching.edges) ∨
       (!st.even v ∧ e ∈ st.matching.edges))
  -- Bridges: non-matching edges between two even vertices at distance d
  let bridges := EF((G : FinGraph α β)).filter fun e =>
    e ∉ st.matching.edges ∧
    ∃ u ∈ e.endpoints.toFinset, ∃ v ∈ e.endpoints.toFinset,
      u ≠ v ∧ st.even u ∧ st.even v ∧ st.dist u = some d ∧ st.dist v = some d
  -- Register new blooms from bridges where both endpoints share a tree
  let newBlooms := bridges.toList.filterMap fun e =>
    match (e.endpoints.toFinset.filter (st.even ·)).toList with
    | u :: v :: _ =>
      -- Bloom with base at LCA (approximated: use the vertex with smaller dist)
      some { bridge_u := u, bridge_v := v, base := u, verts := {u, v} : Bloom α β }
    | _ => none
  -- Check if any new vertex is free (augmenting path exists)
  let reachesFree := (freeIn st.matching newVerts).card > 0
  let st' : MVPhaseState G :=
    { st with
      dist := fun w =>
        if w ∈ newVerts then some (d + 1) else st.dist w
      even := fun w =>
        if w ∈ newVerts then !st.even w  -- flip parity
        else st.even w
      blooms := st.blooms ++ newBlooms }
  (st', reachesFree)

/-- Run the full BFS phase: expand layers until free vertices are reached
    or no progress is made. -/
noncomputable def mvBFS (M : Matching G) :
    MVPhaseState G × Bool :=
  go (MVPhaseState.init M) 0 (VF((G : FinGraph α β)).card)
where
  go (st : MVPhaseState G) (d : ℕ) : ℕ → MVPhaseState G × Bool
  | 0 => (st, false)
  | fuel + 1 =>
    let (st', found) := mvBFSStep st d
    if found then (st', true)
    else
      -- Check if any new vertices were added
      let newCount := (VF((G : FinGraph α β)).filter fun v =>
        st'.dist v = some (d + 1)).card
      if newCount = 0 then (st', false)
      else go st' (d + 1) fuel

/-- Double-DFS to extract one augmenting path from the BFS layering,
    navigating through blooms.  Returns the path edges. -/
noncomputable def mvExtractPath (st : MVPhaseState G) (t : α) :
    Finset (Edge α β) :=
  -- Trace backwards from free vertex t through the BFS layers
  go t (st.dist t |>.getD 0) ∅
where
  go (v : α) : ℕ → Finset (Edge α β) → Finset (Edge α β)
  | 0, edges => edges
  | d + 1, edges =>
    -- Find a predecessor u at distance d connected to v by the right edge type
    let preds := VF((G : FinGraph α β)).filter fun u =>
      st.dist u = some d ∧ u ∉ st.used ∧
      ∃ e ∈ EF((G : FinGraph α β)),
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset ∧
        ((st.even u ∧ e ∉ st.matching.edges) ∨
         (!st.even u ∧ e ∈ st.matching.edges))
    match preds.toList with
    | [] => edges
    | u :: _ =>
      match (EF((G : FinGraph α β)).filter fun e =>
        u ∈ e.endpoints.toFinset ∧ v ∈ e.endpoints.toFinset).toList with
      | [] => edges
      | e :: _ => go u d ({e} ∪ edges)

/-- Find a maximal set of vertex-disjoint shortest augmenting paths in a
    single phase. -/
noncomputable def mvFindPaths (st : MVPhaseState G) :
    Finset (Edge α β) × Finset α :=
  let maxDist := VF((G : FinGraph α β)).card
  let freeAtMax := (freeIn st.matching VF((G : FinGraph α β))).filter fun v =>
    st.dist v ≠ none ∧ st.even v
  freeAtMax.toList.foldl
    (fun (acc : Finset (Edge α β) × Finset α) t =>
      if t ∈ acc.2 then acc  -- already used
      else
        let pathEdges := mvExtractPath { st with used := acc.2 } t
        if pathEdges.card > 0 then
          let pathVerts := pathEdges.biUnion fun e => e.endpoints.toFinset
          (acc.1 ∪ pathEdges, acc.2 ∪ pathVerts)
        else acc)
    (∅, st.used)

/-- One Micali–Vazirani phase: BFS + extract augmenting paths + augment. -/
noncomputable def mvPhase (M : Matching G) : Matching G :=
  let (st, found) := mvBFS M
  if found then
    let (pathEdges, _) := mvFindPaths st
    { edges := edgeSymmDiff M.edges pathEdges
      subset := sorry
      pairwise_disjoint := sorry }
  else M

/-- **Micali–Vazirani algorithm**: iterate phases until no augmenting path
    exists.  Each phase runs in `O(|E|)` and at most `O(√|V|)` phases are
    needed, giving `O(|E| √|V|)` total. -/
noncomputable def micaliVazirani
    (G : SimpleGraph α β) (M₀ : Matching G) : Matching G :=
  go M₀ (Nat.sqrt (VF((G : FinGraph α β)).card) + 1)
where
  go (M : Matching G) : ℕ → Matching G
  | 0 => M
  | fuel + 1 =>
    let (_, found) := mvBFS M
    if found then go (mvPhase M) fuel else M

/-- **Micali–Vazirani correctness**: the output is a maximum matching. -/
theorem micaliVazirani_correct
    (G : SimpleGraph α β) (M₀ : Matching G) :
    IsMaximum (micaliVazirani G M₀) := sorry

/-- **Micali–Vazirani phase bound**: at most `⌈√|V|⌉ + 1` phases. -/
theorem micaliVazirani_phase_bound
    (G : SimpleGraph α β) (M₀ : Matching G) :
    ∃ nphases : ℕ,
      nphases ≤ Nat.sqrt VF((G : FinGraph α β)).card + 1 ∧
      IsMaximum (micaliVazirani G M₀) := sorry

end MicaliVazirani

end Set.graphOn_nonempty
