/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import GraphAlgorithms.UndirectedGraphs.Basic
import GraphAlgorithms.DirectedGraphs.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

open UndirectedGraph
open scoped BigOperators

structure Matching (G : UndirectedGraph α β) where
  edges : Finset (Edge α β)
  subset : edges ⊆ E(G)
  pairwise_disjoint : ∀ e ∈ edges, ∀ f ∈ edges,
    e ≠ f → e.endpoints.toFinset ∩ f.endpoints.toFinset = ∅

variable {G : UndirectedGraph α β}

def IsMaximal (M : Matching G) : Prop :=
  ∀ M' : Matching G, M.edges ⊆ M'.edges → M.edges = M'.edges

def IsMaximum (M : Matching G) : Prop :=
  ∀ M' : Matching G, M'.edges.card ≤ M.edges.card

def IsPerfect (M : Matching G) : Prop :=
  M.edges.biUnion (fun e ↦ e.endpoints.toFinset) = V(G)

/-- If a vertex is covered then there is a unique edge in the matching containing it. -/
def IsCovered (M : Matching G) (v : α) : Prop :=
  v ∈ V(G) ∧ ∃ e ∈ M.edges, v ∈ e.endpoints.toFinset

/-- Instance to make IsCovered computable for Finset.filter -/
instance (M : Matching G) : DecidablePred (IsCovered M) := by
  sorry

/-- If two edges of a matching share an endpoint, they are the same edge. -/
lemma eq_of_not_disjoint
    {M : Matching G}
    {e f : Edge α β}
    (h_matching : e ∈ M.edges ∧ f ∈ M.edges)
    (h_inter : e.endpoints.toFinset ∩ f.endpoints.toFinset ≠ ∅) :
    e = f := by
  by_contra h_contra
  apply h_inter
  exact M.pairwise_disjoint e h_matching.1 f h_matching.2 h_contra

/-- The set of covered vertices is equivalent to the set of endpoints of contained edges. -/
lemma covered_eq_biUnion_endpoints (M : Matching G) :
    Finset.filter (IsCovered M) V(G) = M.edges.biUnion (fun e ↦ e.endpoints.toFinset) := by
  ext x
  constructor
  · intro hx
    simp_all [IsCovered]
  · intro hx
    simp_all [IsCovered]
    obtain ⟨a, hal, har⟩ := hx
    exact G.incidence a (M.subset hal) x har

/-- The number of covered vertices is twice the number of edges. -/
lemma num_cov_vert_twice_num_edges (M : Matching G) (h_simple : G.Simple) :
    2 * M.edges.card = (V(G).filter (IsCovered M)).card := by
  rw [covered_eq_biUnion_endpoints M, Finset.card_biUnion, Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr
  · rfl
  · intro x hx
    rw [Sym2.card_toFinset]
    split_ifs
    · simp
      apply h_simple.2 x <| M.subset hx
      assumption
    · simp
  · intro a ha b hb hab
    simp [Function.onFun]
    exact Finset.disjoint_iff_inter_eq_empty.mpr <| M.pairwise_disjoint a ha b hb hab

/-- A perfect matching has an even number of vertices. -/
lemma perfect_matching_even_vertices (M : Matching G) (h : IsPerfect M) (h_simple : G.Simple) :
    Even V(G).card := by
  unfold IsPerfect at h
  rw [← covered_eq_biUnion_endpoints M] at h
  rw [← h, ← num_cov_vert_twice_num_edges M h_simple]
  simp

/-- A perfect matching is a maximum matching. -/
lemma perfect_matching_is_maximum (M : Matching G) (h : IsPerfect M) (h_simple : G.Simple) :
    IsMaximum M := by
  unfold IsMaximum
  unfold IsPerfect at h
  -- by contradiction, assume there exists a bigger matching
  -- then the matching has more endpoints that there are vertices
  by_contra h_contra
  simp at h_contra
  obtain ⟨x, hx⟩ := h_contra
  rw [← covered_eq_biUnion_endpoints] at h
  have h1 := num_cov_vert_twice_num_edges x h_simple
  have h2 := num_cov_vert_twice_num_edges M h_simple
  rw [h] at h2
  have : 2 * M.edges.card < 2 * x.edges.card := by omega
  grw [h1, h2] at this
  have := Finset.card_filter_le V(G) (IsCovered x)
  expose_names
  grw [this] at this_1
  omega

/-- A maximum matching is a maximal matching. -/
lemma maximum_matching_is_maximal (M : Matching G) (h : IsMaximum M) :
    IsMaximal M := by
  unfold IsMaximal
  unfold IsMaximum at h
  intro M hM
  have := h M
  apply (Finset.subset_iff_eq_of_card_le this).1
  assumption

-- **Greedy Maximal Matching Algorithm**




-- **Berges Theorem & Hopcroft-Karp Algorithm**

/-- A path is alternating with respect to M if its edges alternate between M and E \ M. -/
def IsAlternatingPath (M : Matching G) {u v : α} (p : Walk α β u v) : Prop :=
  p.edges.IsChain (fun e1 e2 ↦ e1 ∈ M.edges ↔ e2 ∉ M.edges)

/-- An augmenting path is an alternating path that starts and ends at exposed vertices. -/
def IsAugmentingPath (M : Matching G) {u v : α} (p : Walk α β u v) : Prop :=
  IsAlternatingPath M p ∧ ¬IsCovered M u ∧ ¬IsCovered M v ∧ u ≠ v

lemma augmenting_path_even_length : 1 = 1 := by sorry

-- **This should really already exist in mathlib but couldnt use it.**
/-- Symmetric Difference for Finset. -/
def finsetSymmDiff (s t : Finset α) : Finset α :=
  (s \ t) ∪ (t \ s)

lemma Berge
    {M : Matching G}
    {u v : α}
    {p : Walk α β u v}
    (h_aug : IsAugmentingPath M p) :
    ∃ M' : Matching G, M'.edges.card = M.edges.card + 1 := by

  let M' := finsetSymmDiff M.edges p.edges.toFinset

  have ⟨M'', hM''⟩ : ∃ M'' : Matching G, M''.edges = M' := by
    let M'' : Matching G := {
      edges := M',
      subset := by
        simp [M', finsetSymmDiff, Finset.union_subset_iff]
        constructor
        · suffices M.edges ⊆ E(G) by
            grind
          intro x hx
          exact M.subset hx
        · suffices p.edges.toFinset ⊆ E(G) by
            grind
          sorry,
      pairwise_disjoint := by
        intro e he f hf hef
        simp [M', finsetSymmDiff] at he
        simp [M', finsetSymmDiff] at hf
        rcases he with h1 | h2
        · rcases hf with h11 | h12
          · exact M.pairwise_disjoint e h1.1 f h11.1 hef
          · sorry
        · sorry
    }
    sorry

  use M''
  have h_distr : (M.edges \ p.edges.toFinset ∪ p.edges.toFinset \ M.edges).card = (M.edges \ p.edges.toFinset).card + (p.edges.toFinset \ M.edges).card := by
    apply Finset.card_union_eq_card_add_card.2
    apply Finset.disjoint_iff_inter_eq_empty.2
    ext x
    constructor
    · simp
      intro hx1 hx2 hx3
      contradiction
    · intro x
      contradiction
  simp [hM'', M', finsetSymmDiff, h_distr]
  have h1 : (M.edges \ p.edges.toFinset).card = M.edges.card - (p.edges.toFinset ∩ M.edges).card := by
    grind
  have h2 : (p.edges.toFinset \ M.edges).card = p.edges.toFinset.card - (p.edges.toFinset ∩ M.edges).card := by
    grind
  rw [h1, h2]
  have : M.edges.card - (p.edges.toFinset ∩ M.edges).card + (p.edges.toFinset.card - (p.edges.toFinset ∩ M.edges).card) =
      M.edges.card + p.edges.toFinset.card - 2 * (p.edges.toFinset ∩ M.edges).card := by
    grind
  rw [this]
  sorry

-- **Implement Hopcroft-Karp Algorithm here**

-- **König's Lemma**

-- **Hall's Theorem** (cor of König)

-- **Tutte's Theorem**

-- **Gallai Identity**

-- **Blossom Algorithm**
