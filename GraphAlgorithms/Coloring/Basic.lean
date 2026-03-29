/-
Copyright (c) 2024 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/

import GraphAlgorithms.UndirectedGraphs.Basic
import GraphAlgorithms.Embeddings.Basic

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

namespace Set.graphOn_nonempty

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ## Proper colouring and chromatic number -/

/-- A **proper `k`-colouring** assigns colours from `Fin k` to vertices so that adjacent
    vertices receive different colours. -/
def IsProperColouring (G : SimpleGraph α β) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ e ∈ E(G), ¬(e.endpoints.map c).IsDiag

/-- `χ(G)` — the **chromatic number**: the minimum number of colours in a proper colouring. -/
noncomputable def chromaticNr (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | ∃ c : α → Fin k, IsProperColouring G k c }

scoped notation "χ(" G ")" => chromaticNr G

/-- Every clique requires a distinct colour, so `ω(G) ≤ χ(G)`. -/
theorem cliqueNr_le_chromaticNr (G : SimpleGraph α β) : ω(G) ≤ χ(G) := by
  sorry

/-- A bipartite graph is 2-colourable. -/
theorem bipartite_iff_twoColourable (G : SimpleGraph α β) :
    IsBipartite G ↔ ∃ c : α → Fin 2, IsProperColouring G 2 c := by
  sorry

/-! ## Clique cover -/

/-- A **clique cover** of `G` is a family of cliques whose vertex sets
    partition `V(G)`. -/
def IsCliqueCover (G : SimpleGraph α β) (k : ℕ) (cover : Fin k → Finset α) : Prop :=
  (∀ i, IsClique G (cover i)) ∧
  (∀ v ∈ V(G), ∃! i, v ∈ cover i) ∧
  (∀ i, ↑(cover i) ⊆ V(G))

/-- `θ(G)` — the **clique cover number**: minimum number of cliques that
    cover `V(G)`. -/
noncomputable def cliqueCoverNr (G : SimpleGraph α β) : ℕ :=
  sInf { k : ℕ | ∃ cover : Fin k → Finset α, IsCliqueCover G k cover }

scoped notation "θ(" G ")" => cliqueCoverNr G

/-! ## Perfect graphs -/

/-- `G` is **perfect** if `χ(H) = ω(H)` for every induced subgraph `H`. -/
def IsPerfect (G : SimpleGraph α β) : Prop :=
  ∀ S : Set α, S ⊆ V(G) → χ(G[S]) = ω(G[S])

/-- **Weak Perfect Graph Theorem** (Lovász 1972): the complement of a
    perfect graph is perfect. -/
theorem WeakPerfectGraphTheorem {α β : Type*} (G H : SimpleGraph α β)
    (hc : IsComplement G H) (hP : IsPerfect G) : IsPerfect H := sorry

/-
  This Flurin and I want to do separately.
-/
/-- **Strong Perfect Graph Theorem** (Chudnovsky–Robertson–Seymour–Thomas 2006):
    a graph is perfect iff it contains no odd hole and no odd antihole. -/
theorem StrongPerfectGraphTheorem (G : SimpleGraph α β) :
    IsPerfect G ↔ ¬HasOddHole G ∧ ¬HasOddAntihole G := sorry

/-! ## Chordal graphs -/

/-
  **TODO**: On second thought, this should go to `UndirectedGraphs/Basic.lean`.
-/

/-- `G` is **chordal** if every cycle of length ≥ 4 has a chord (equivalently,
    no induced cycle of length ≥ 4). -/
def IsChordal (G : SimpleGraph α β) : Prop :=
  ∀ n, n ≥ 4 → ¬HasInducedCycle G n

/-- Every chordal graph is perfect. -/
theorem chordal_is_perfect (G : SimpleGraph α β) (hC : IsChordal G) :
    IsPerfect G := sorry

/-! ## Four Colour Theorem -/

/-- lol, good luck -/
theorem FourColourTheorem {α β : Type*} (G : SimpleGraph α β) (hP : isPlanar G) :
    chromaticNr G ≤ 4 := by sorry

end Set.graphOn_nonempty
