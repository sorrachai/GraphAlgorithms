/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

/-
    Need to read a book on topology first.
-/

import GraphAlgorithms.UndirectedGraphs.Basic
import GraphAlgorithms.Contractions.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

namespace Set.graphOn_nonempty

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! # Topological embeddings of graphs -/

/-- A **topological embedding** of `G` into the topological space `X`:
    an injective placement of vertices and edge-arcs so that arcs are
    pairwise interior-disjoint and miss all vertex images. -/
def isEmbedding {α β X : Type*} [TopologicalSpace X]
    (G : SimpleGraph α β) : Prop :=
  ∃ (φv : α → X),
    (∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → φv u ≠ φv v) ∧
    ∃ (φe : ∀ e ∈ E(G), C(Set.Icc (0 : ℝ) 1, X)),
      (∀ e (he : e ∈ E(G)) u v, e.endpoints = s(u, v) →
          (φe e he) ⟨0, by norm_num⟩ = φv u ∧
          (φe e he) ⟨1, by norm_num⟩ = φv v) ∧
      (∀ e (he : e ∈ E(G)), Function.Injective (φe e he)) ∧
      (∀ e (he : e ∈ E(G)) f (hf : f ∈ E(G)), e ≠ f →
          Disjoint ((φe e he) '' Set.Ioo 0 1)
                   ((φe f hf) '' Set.Ioo 0 1)) ∧
      (∀ e (he : e ∈ E(G)) v, v ∈ V(G) →
          φv v ∉ (φe e he) '' Set.Ioo 0 1)

/-! ## Planarity -/

/-- `G` is **planar** if it embeds into the Euclidean plane `ℝ²`. -/
def isPlanar {α β : Type*} (G : SimpleGraph α β) : Prop :=
  isEmbedding (X := ℝ × ℝ) G

/-- A planar graph on `n ≥ 3` vertices has at most `3n - 6` edges. -/
theorem planar_edge_bound (G : SimpleGraph α β) (hP : isPlanar G)
    (hn : VF((G : FinGraph α β)).card ≥ 3) :
    EF((G : FinGraph α β)).card ≤
      3 * VF((G : FinGraph α β)).card - 6 := sorry

/-- A planar **bipartite** graph on `n ≥ 4` vertices has at most
    `2n - 4` edges (no triangles ⟹ every face has degree ≥ 4). -/
theorem planar_bipartite_edge_bound (G : SimpleGraph α β)
    (hP : isPlanar G) (hB : IsBipartite G)
    (hn : VF((G : FinGraph α β)).card ≥ 4) :
    EF((G : FinGraph α β)).card ≤
      2 * VF((G : FinGraph α β)).card - 4 := sorry

/-- The complete graph `K₅` is not planar. -/
theorem K5_not_planar (G : SimpleGraph α β) (hK : IsComplete G)
    (h5 : VF((G : FinGraph α β)).card = 5) :
    ¬isPlanar G := sorry

/-- The complete bipartite graph `K₃,₃` is not planar. -/
theorem K33_not_planar (G : SimpleGraph α β) (hB : IsBipartite G)
    (hReg : IsKRegular G 3)
    (h6 : VF((G : FinGraph α β)).card = 6) :
    ¬isPlanar G := sorry

/-- **Kuratowski's theorem**: a graph is planar iff it contains no
    subdivision of `K₅` or `K₃,₃`. -/
theorem Kuratowski (G : SimpleGraph α β) :
    isPlanar G ↔
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsComplete H → VF((H : FinGraph γ δ)).card = 5 →
        ¬topMinorOf G H) ∧
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsBipartite H → IsKRegular H 3 →
        VF((H : FinGraph γ δ)).card = 6 →
        ¬topMinorOf G H) := sorry

/-- **Wagner's theorem**: a graph is planar iff it contains no `K₅` or
    `K₃,₃` as a minor. -/
theorem Wagner (G : SimpleGraph α β) :
    isPlanar G ↔
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsComplete H → VF((H : FinGraph γ δ)).card = 5 →
        ¬minorOf G H) ∧
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsBipartite H → IsKRegular H 3 →
        VF((H : FinGraph γ δ)).card = 6 →
        ¬minorOf G H) := sorry

/-- **Euler's formula** for connected planar graphs: `v - e + f = 2`. -/
theorem Euler_formula (G : SimpleGraph α β)
    (hP : isPlanar G) (hC : IsConnected G) :
    ∃ f : ℕ, -- number of faces
      VF((G : FinGraph α β)).card -
        EF((G : FinGraph α β)).card + f = 2 := sorry

/-- Every planar graph has a vertex of degree at most 5. -/
theorem planar_min_degree_le_five (G : SimpleGraph α β)
    (hP : isPlanar G) (hne : (V(G)).Nonempty) :
    ∃ v ∈ V(G), deg((G : FinGraph α β), v) ≤ 5 := sorry

/-- A planar graph is 5-degenerate: every subgraph has a vertex of
    degree at most 5. -/
theorem planar_five_degenerate (G : SimpleGraph α β)
    (hP : isPlanar G) :
    ∀ S : Set α, S ⊆ V(G) → S.Nonempty →
      ∃ v ∈ S,
        deg((induce G S : FinGraph α β), v) ≤ 5 := sorry

/-- Every planar graph is **5-choosable** (list-colourable).
    Stated without the Coloring import as a self-contained property. -/
theorem planar_five_colourable (G : SimpleGraph α β)
    (hP : isPlanar G) :
    ∃ c : α → Fin 5,
      ∀ e ∈ E(G), ¬(e.endpoints.map c).IsDiag := sorry

/-! ## Surface embeddings and genus -/

/-- `G` embeds into an orientable surface of genus `g`.
    (Genus 0 = sphere ≅ plane, genus 1 = torus, etc.) -/
def embedsInSurface {α β : Type*}
    (G : SimpleGraph α β) (g : ℕ) : Prop :=
  sorry -- requires a formalization of orientable surfaces

/-- The **genus** of `G`: the minimum `g` such that `G` embeds in the
    orientable surface of genus `g`. -/
noncomputable def genus {α β : Type*}
    (G : SimpleGraph α β) : ℕ :=
  sInf { g : ℕ | embedsInSurface G g }

/-- A planar graph has genus 0. -/
theorem planar_iff_genus_zero (G : SimpleGraph α β) :
    isPlanar G ↔ genus G = 0 := sorry

/-- `G` is **toroidal** if it embeds on the torus (genus ≤ 1). -/
def isToroidal {α β : Type*} (G : SimpleGraph α β) : Prop :=
  embedsInSurface G 1

/-- A toroidal graph has genus at most 1. -/
theorem toroidal_iff_genus_le_one (G : SimpleGraph α β) :
    isToroidal G ↔ genus G ≤ 1 := sorry

/-- `K₇` embeds on the torus but not in the plane. -/
theorem K7_toroidal (G : SimpleGraph α β) (hK : IsComplete G)
    (h7 : VF((G : FinGraph α β)).card = 7) :
    isToroidal G := sorry

/-- **Euler's formula for surfaces**: for a connected graph embedded on
    a surface of genus `g`, `v - e + f = 2 - 2g`. -/
theorem Euler_formula_surface (G : SimpleGraph α β) (g : ℕ)
    (hE : embedsInSurface G g) (hC : IsConnected G) :
    ∃ f : ℕ,
      VF((G : FinGraph α β)).card + f =
        EF((G : FinGraph α β)).card + 2 - 2 * g := sorry

/-- **Edge bound for genus `g`**: a graph embeddable on a surface of
    genus `g` with `n ≥ 3` vertices has at most `3(n - 2 + 2g)` edges. -/
theorem surface_edge_bound (G : SimpleGraph α β) (g : ℕ)
    (hE : embedsInSurface G g)
    (hn : VF((G : FinGraph α β)).card ≥ 3) :
    EF((G : FinGraph α β)).card ≤
      3 * (VF((G : FinGraph α β)).card - 2 + 2 * g) := sorry

/-- **Heawood's bound**: a graph embeddable on genus `g ≥ 1` is
    `H(g)`-colourable, where `H(g) = ⌊(7 + √(1 + 48g)) / 2⌋`. -/
theorem Heawood_bound (G : SimpleGraph α β) (g : ℕ)
    (hg : g ≥ 1) (hE : embedsInSurface G g) :
    ∃ (k : ℕ) (c : α → Fin k),
      k ≤ (7 + Nat.sqrt (1 + 48 * g)) / 2 ∧
      ∀ e ∈ E(G), ¬(e.endpoints.map c).IsDiag := sorry

/-- **Ringel–Youngs theorem** (Map Colour Theorem): the Heawood bound is
    tight for every surface of genus `g ≥ 1`. -/
theorem RingelYoungs (g : ℕ) (hg : g ≥ 1) :
    ∃ (α β : Type) (_ : DecidableEq α) (_ : DecidableEq β)
      (G : SimpleGraph α β),
      embedsInSurface G g ∧
      -- chromatic number equals the Heawood number
      ∀ (k : ℕ), k < (7 + Nat.sqrt (1 + 48 * g)) / 2 →
        ¬∃ c : α → Fin k, ∀ e ∈ E(G), ¬(e.endpoints.map c).IsDiag := sorry

/-! ## Non-orientable surfaces -/

/-- `G` embeds into a non-orientable surface of **crosscap number** `k`.
    (k = 1: projective plane, k = 2: Klein bottle, etc.) -/
def embedsInNonOrientable {α β : Type*}
    (G : SimpleGraph α β) (k : ℕ) : Prop :=
  sorry

/-- The **crosscap number** of `G`: minimum `k` for an embedding into
    the non-orientable surface with `k` crosscaps. -/
noncomputable def crosscapNr {α β : Type*}
    (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | embedsInNonOrientable G k }

/-- **Euler's formula for non-orientable surfaces**: for a connected graph
    on a surface with `k` crosscaps, `v - e + f = 2 - k`. -/
theorem Euler_formula_nonorientable (G : SimpleGraph α β) (k : ℕ)
    (hE : embedsInNonOrientable G k) (hC : IsConnected G) :
    ∃ f : ℕ,
      VF((G : FinGraph α β)).card + f =
        EF((G : FinGraph α β)).card + 2 - k := sorry

/-- `K₆` embeds on the projective plane. -/
theorem K6_projective_plane (G : SimpleGraph α β) (hK : IsComplete G)
    (h6 : VF((G : FinGraph α β)).card = 6) :
    embedsInNonOrientable G 1 := sorry

/-- **Franklin's theorem**: `K₆` is the largest complete graph embeddable
    on the projective plane. -/
theorem K7_not_projective (G : SimpleGraph α β) (hK : IsComplete G)
    (h7 : VF((G : FinGraph α β)).card ≥ 7) :
    ¬embedsInNonOrientable G 1 := sorry

/-! ## Outerplanarity -/

/-- `G` is **outerplanar** if it has a planar embedding in which every
    vertex lies on the boundary of the outer face. -/
def isOuterplanar {α β : Type*} (G : SimpleGraph α β) : Prop :=
  sorry

/-- An outerplanar graph is planar. -/
theorem outerplanar_is_planar (G : SimpleGraph α β)
    (hO : isOuterplanar G) : isPlanar G := sorry

/-- An outerplanar graph on `n ≥ 2` vertices has at most `2n - 3` edges. -/
theorem outerplanar_edge_bound (G : SimpleGraph α β)
    (hO : isOuterplanar G)
    (hn : VF((G : FinGraph α β)).card ≥ 2) :
    EF((G : FinGraph α β)).card ≤
      2 * VF((G : FinGraph α β)).card - 3 := sorry

/-- **Outerplanar characterisation**: `G` is outerplanar iff it contains
    no `K₄` minor and no `K₂,₃` minor. -/
theorem outerplanar_iff_no_K4_K23 (G : SimpleGraph α β) :
    isOuterplanar G ↔
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsComplete H → VF((H : FinGraph γ δ)).card = 4 →
        ¬minorOf G H) ∧
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      IsBipartite H → VF((H : FinGraph γ δ)).card = 5 →
        EF((H : FinGraph γ δ)).card = 6 →
        ¬minorOf G H) := sorry

/-- Every outerplanar graph is 3-colourable. -/
theorem outerplanar_three_colourable (G : SimpleGraph α β)
    (hO : isOuterplanar G) :
    ∃ c : α → Fin 3,
      ∀ e ∈ E(G), ¬(e.endpoints.map c).IsDiag := sorry

/-- Every outerplanar graph has tree-width at most 2. -/
theorem outerplanar_treewidth_le_two (G : SimpleGraph α β)
    (hO : isOuterplanar G) : tw(G) ≤ 2 := sorry

/-! ## Graph thickness and book embedding -/

/-- The **thickness** of `G`: the minimum number of planar subgraphs whose
    edges partition `E(G)`. -/
noncomputable def thickness (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | ∃ parts : Fin k → Set (Edge α β),
    (∀ i, ∃ (H : SimpleGraph α β), isPlanar H ∧ E(H) = parts i) ∧
    (∀ e ∈ E(G), ∃! i, e ∈ parts i) }

/-- A graph is planar iff its thickness is at most 1. -/
theorem planar_iff_thickness_le_one (G : SimpleGraph α β) :
    isPlanar G ↔ thickness G ≤ 1 := sorry

/-- The **book thickness** (stack number, page number) of `G`: the minimum
    number of pages in a book embedding. -/
noncomputable def bookThickness (G : SimpleGraph α β) : ℕ := sorry

/-- Every planar graph has book thickness at most 4 (Yannakakis 1989). -/
theorem planar_book_thickness_le_four (G : SimpleGraph α β)
    (hP : isPlanar G) :
    bookThickness G ≤ 4 := sorry

/-! ## Dual graph and face structure -/

/-- The **face set** of a connected planar graph (given a fixed embedding). -/
noncomputable def faces (G : SimpleGraph α β)
    (hP : isPlanar G) (hC : IsConnected G) :
    Finset (Set α) := sorry

/-- The number of faces satisfies Euler's formula. -/
theorem faces_card (G : SimpleGraph α β)
    (hP : isPlanar G) (hC : IsConnected G) :
    (faces G hP hC).card =
      EF((G : FinGraph α β)).card -
        VF((G : FinGraph α β)).card + 2 := sorry

/-- The **dual graph** of a connected planar graph: vertices are faces,
    edges connect faces sharing a boundary edge. -/
noncomputable def dualGraph (G : SimpleGraph α β)
    (hP : isPlanar G) (hC : IsConnected G) :
    SimpleGraph (Set α) ℕ := sorry

/-- The dual of a planar graph is planar. -/
theorem dual_is_planar (G : SimpleGraph α β)
    (hP : isPlanar G) (hC : IsConnected G) :
    isPlanar (dualGraph G hP hC) := sorry

/-! ## Crossing number -/

/-- The **crossing number** `cr(G)`: minimum number of edge crossings in
    any drawing of `G` in the plane. -/
noncomputable def crossingNr (G : SimpleGraph α β) : ℕ := sorry

/-- A graph is planar iff its crossing number is 0. -/
theorem planar_iff_crossing_zero (G : SimpleGraph α β) :
    isPlanar G ↔ crossingNr G = 0 := sorry

/-- **Crossing lemma** (Ajtai–Chvátal–Newborn–Szemerédi; Leighton):
    if `|E| ≥ 4|V|`, then `cr(G) ≥ |E|³ / (64 |V|²)`. -/
theorem crossing_lemma (G : SimpleGraph α β)
    (h : EF((G : FinGraph α β)).card ≥
      4 * VF((G : FinGraph α β)).card) :
    crossingNr G * (64 * VF((G : FinGraph α β)).card ^ 2) ≥
      EF((G : FinGraph α β)).card ^ 3 := sorry

/-! ## Forbidden minor characterisations -/

/-- **Robertson–Seymour for linkless embeddings**: `G` is **linklessly
    embeddable** iff it has no Petersen family minor.
    (Stated abstractly — the Petersen family has 7 graphs.) -/
def isLinklesslyEmbeddable (G : SimpleGraph α β) : Prop :=
  ∃ (φv : α → ℝ × ℝ × ℝ),
    Function.Injective φv ∧ True -- placeholder for "no two cycles link"

theorem linkless_iff_no_petersen_minor (G : SimpleGraph α β) :
    isLinklesslyEmbeddable G ↔
    (∀ (γ δ : Type*) [DecidableEq γ] [DecidableEq δ]
        (H : SimpleGraph γ δ),
      -- H is in the Petersen family
      True → ¬minorOf G H) := sorry

/-- **Robertson–Seymour for knotlessly embeddable** graphs: `G` is
    knotlessly embeddable iff it has no minor from a specific family. -/
def isKnotlesslyEmbeddable (G : SimpleGraph α β) : Prop :=
  sorry

/-- The **Colin de Verdière invariant** `μ(G)`: a spectral graph parameter
    that characterises embeddability. -/
noncomputable def colinDeVerdiere (G : SimpleGraph α β) : ℕ := sorry

/-- `μ(G) ≤ 3` iff `G` is planar (Colin de Verdière 1990). -/
theorem colinDeVerdiere_planar (G : SimpleGraph α β) :
    isPlanar G ↔ colinDeVerdiere G ≤ 3 := sorry

/-- `μ(G) ≤ 2` iff `G` is outerplanar. -/
theorem colinDeVerdiere_outerplanar (G : SimpleGraph α β) :
    isOuterplanar G ↔ colinDeVerdiere G ≤ 2 := sorry

/-- `μ(G) ≤ 4` iff `G` is linklessly embeddable. -/
theorem colinDeVerdiere_linkless (G : SimpleGraph α β) :
    isLinklesslyEmbeddable G ↔ colinDeVerdiere G ≤ 4 := sorry

/-! ## Straight-line embeddings -/

/-- **Fáry's theorem**: every planar graph has a straight-line embedding
    (i.e., an embedding where every edge is a line segment). -/
theorem Fary (G : SimpleGraph α β) (hP : isPlanar G) :
    ∃ (φ : α → ℝ × ℝ),
      (∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → φ u ≠ φ v) ∧
      -- edges are non-crossing line segments (no interiors intersect)
      (∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f →
        ∀ u₁ ∈ e.endpoints, ∀ v₁ ∈ e.endpoints,
        ∀ u₂ ∈ f.endpoints, ∀ v₂ ∈ f.endpoints,
          u₁ ≠ v₁ → u₂ ≠ v₂ → True) -- placeholder for non-crossing
      := sorry

/-- **Schnyder's theorem**: every planar graph has a straight-line
    embedding on an `(n-2) × (n-2)` grid. -/
theorem Schnyder (G : SimpleGraph α β) (hP : isPlanar G)
    (n : ℕ) (hn : VF((G : FinGraph α β)).card = n) :
    ∃ (φ : α → Fin (n - 1) × Fin (n - 1)),
      ∀ u ∈ V(G), ∀ v ∈ V(G), u ≠ v → φ u ≠ φ v := sorry

end Set.graphOn_nonempty
