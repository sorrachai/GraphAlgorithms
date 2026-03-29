/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

import GraphAlgorithms.UndirectedGraphs.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

namespace Set.graphOn_nonempty

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ## Contraction -/

/-- Redirect an edge's endpoints: replace every occurrence of `v` with `u`. -/
private def redirectEdge (u v : α) (e : Edge α β) : Edge α β :=
  { id := e.id, endpoints := e.endpoints.map (fun x => if x = v then u else x) }

/-- **Contract** `v` into `u`: remove `v` from the vertex set, redirect every edge that
    touched `v` to `u` instead, and discard the resulting loops. -/
def contract {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α β) (u v : G.vertices) (h : u ≠ v) : SimpleGraph α β where
  vertices := V(G) \ {(v : α)}
  edges    :=
    { e' | ∃ e ∈ E(G),
        e' = redirectEdge (u : α) (v : α) e ∧
        ¬(redirectEdge (u : α) (v : α) e).endpoints.IsDiag }
  incidence := by
    intro e' he' w hw
    simp only [Set.mem_setOf_eq] at he'
    obtain ⟨e, heG, rfl, hndg⟩ := he'
    simp only [redirectEdge, Sym2.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    by_cases hxv : x = (v : α)
    · subst hxv
      simp only [if_pos rfl]
      exact ⟨u.property, fun huv => h (Subtype.ext huv)⟩
    · simp only [if_neg hxv]
      exact ⟨G.incidence e heG x hx, hxv⟩
  fin_vertices := by
    haveI : Finite ↥V(G) := G.fin_vertices
    exact Finite.of_injective (Set.inclusion Set.diff_subset) (Set.inclusion_injective _)
  fin_edges := by
    haveI : Finite ↥E(G) := G.fin_edges
    apply Set.Finite.to_subtype
    have hfin : (E(G) : Set (Edge α β)).Finite := Set.toFinite _
    have hpre : ({ e ∈ (E(G) : Set (Edge α β)) |
        ¬(redirectEdge (u : α) (v : α) e).endpoints.IsDiag }).Finite :=
      hfin.subset (Set.sep_subset _ _)
    apply Set.Finite.subset (hpre.image (redirectEdge (u : α) (v : α)))
    intro e' he'
    simp only [Set.mem_setOf_eq] at he'
    obtain ⟨e, heG, rfl, hndg⟩ := he'
    exact Set.mem_image_of_mem _ ⟨heG, hndg⟩
  loopless := by
    intro e' he'
    simp only [Set.mem_setOf_eq] at he'
    obtain ⟨e, _, rfl, hndg⟩ := he'
    exact hndg
  simple := by
    -- Contraction can create parallel edges; left as sorry.
    sorry

/-! ### Minors -/

/-- `H` is a **minor** of `G`: there exist pairwise disjoint, non-empty, connected
    branch sets `φ v ⊆ V(G)` for each `v ∈ V(H)`, with a `G`-edge between the branch
    sets of every adjacent pair in `H`. -/
def minorOf {α β γ δ : Type*} (G : SimpleGraph α β) (H : SimpleGraph γ δ) : Prop :=
  ∃ φ : γ → Set α,
    -- branch sets are subsets of V(G)
    (∀ v ∈ V(H), φ v ⊆ V(G)) ∧
    -- branch sets are pairwise disjoint
    (∀ v₁ ∈ V(H), ∀ v₂ ∈ V(H), v₁ ≠ v₂ → Disjoint (φ v₁) (φ v₂)) ∧
    -- branch sets are non-empty
    (∀ v ∈ V(H), (φ v).Nonempty) ∧
    -- branch sets are connected in G
    (∀ v ∈ V(H), IsConnected (G[φ v])) ∧
    -- adjacent vertices in H have a G-edge between their branch sets
    (∀ e ∈ E(H), ∀ v₁ ∈ e.endpoints, ∀ v₂ ∈ e.endpoints, v₁ ≠ v₂ →
      ∃ x ∈ φ v₁, ∃ y ∈ φ v₂, ∃ f ∈ E(G), x ∈ f.endpoints ∧ y ∈ f.endpoints)

/-- `H` is a **topological minor** of `G`: there is an injection of `V(H)` into `V(G)`
    (branch vertices) and, for each edge of `H`, an internally vertex-disjoint path in `G`
    whose internal vertices avoid all branch vertices. -/
def topMinorOf {α β γ δ : Type*} (G : SimpleGraph α β) (H : SimpleGraph γ δ) : Prop :=
  ∃ (φ : γ → α)
    (P : (e : Edge γ δ) → (u v : γ) → (φ u, φ v)-Walk-(α, β)),
    -- φ maps V(H) into V(G)
    (∀ v ∈ V(H), φ v ∈ V(G)) ∧
    -- φ is injective on V(H)
    (∀ v₁ ∈ V(H), ∀ v₂ ∈ V(H), v₁ ≠ v₂ → φ v₁ ≠ φ v₂) ∧
    -- for each edge, P provides a path in G whose internal vertices avoid branch vertices
    (∀ e ∈ E(H), ∀ v₁ ∈ e.endpoints, ∀ v₂ ∈ e.endpoints, v₁ ≠ v₂ →
      (P e v₁ v₂).isPath ∧ (P e v₁ v₂).InGraph G ∧
      ∀ x ∈ (P e v₁ v₂).support.tail.dropLast, ∀ w ∈ V(H), φ w ≠ x) ∧
    -- internal vertices of paths for distinct edges are disjoint
    (∀ e₁ ∈ E(H), ∀ u₁ ∈ e₁.endpoints, ∀ v₁ ∈ e₁.endpoints, u₁ ≠ v₁ →
     ∀ e₂ ∈ E(H), ∀ u₂ ∈ e₂.endpoints, ∀ v₂ ∈ e₂.endpoints, u₂ ≠ v₂ →
       e₁ ≠ e₂ →
       ∀ x, x ∈ (P e₁ u₁ v₁).support.tail.dropLast →
         x ∉ (P e₂ u₂ v₂).support.tail.dropLast)

scoped notation H " ≼ " G  => minorOf H G
scoped notation H " ≼ₜ " G => topMinorOf H G

/-! ## Clique-sum -/

/-- `G` is a **clique-sum of order ≤ `k`** of `G₁` and `G₂`: there exist
    cliques `K₁ ⊆ V(G₁)`, `K₂ ⊆ V(G₂)` of size ≤ `k` and a bijection
    between them; `G` is obtained by identifying `K₁` with `K₂` and
    possibly deleting some edges within the identified clique. -/
def IsCliqueSum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G G₁ G₂ : SimpleGraph α β) (k : ℕ) : Prop :=
  ∃ (K₁ K₂ : Finset α),
    IsClique G₁ K₁ ∧ IsClique G₂ K₂ ∧
    K₁.card ≤ k ∧ K₁.card = K₂.card ∧
    V(G) = V(G₁) ∪ V(G₂) ∧
    (∀ u v : α, u ∈ V(G₁) \ ↑K₁ → v ∈ V(G₂) \ ↑K₂ → ¬adj (G : Graph α β) u v) ∧
    (∀ u v : α, u ∈ V(G₁) → v ∈ V(G₁) → u ∉ K₁ ∨ v ∉ K₁ →
      (adj (G : Graph α β) u v ↔ adj (G₁ : Graph α β) u v)) ∧
    (∀ u v : α, u ∈ V(G₂) → v ∈ V(G₂) → u ∉ K₂ ∨ v ∉ K₂ →
      (adj (G : Graph α β) u v ↔ adj (G₂ : Graph α β) u v))

/-! ## Grid minor and flat wall -/

/-- A **`k × k` grid graph**: vertices are `Fin k × Fin k` and edges connect
    horizontally or vertically adjacent pairs.  (Construction left abstract.) -/
noncomputable def gridGraph (k : ℕ) : SimpleGraph (Fin k × Fin k) ℕ := sorry

/-- `G` contains a **grid minor** of order `k`: the `k × k` grid is a
    minor of `G`. -/
def HasGridMinor {α β : Type*} (G : SimpleGraph α β) (k : ℕ) : Prop :=
  minorOf (gridGraph k) G

/-- A **wall** of height `k` in `G`. -/
def HasWall (G : SimpleGraph α β) (k : ℕ) : Prop := sorry

/-- A wall is **flat** if it can be drawn in a disk with the boundary
    cycle on the disk boundary. -/
def HasFlatWall (G : SimpleGraph α β) (k : ℕ) : Prop := sorry

/-- **Grid minor theorem** (Robertson–Seymour V; improved by
    Chuzhoy–Tan): there is a function `f` such that `tw(G) ≥ f(k)`
    implies `G` has a `k × k` grid minor. -/
theorem grid_minor_theorem {α β : Type*} [DecidableEq α] [DecidableEq β] :
    ∃ f : ℕ → ℕ, ∀ (G : SimpleGraph α β) (k : ℕ),
      tw(G) ≥ f k → HasGridMinor G k := sorry

/-- The tree-width of the `k × k` grid is `k` (for `k ≥ 1`). -/
theorem treeWidth_grid (k : ℕ) (hk : k ≥ 1) :
    tw(gridGraph k) = k := by
  sorry

/-- Tree-width is monotone under minors. -/
theorem treeWidth_minor {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ]
    (G : SimpleGraph α β) (H : SimpleGraph γ δ)
    (hmin : minorOf H G) :
    tw(H) ≤ tw(G) := by
  sorry

end Set.graphOn_nonempty
