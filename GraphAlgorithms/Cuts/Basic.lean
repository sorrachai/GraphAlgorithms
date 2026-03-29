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

/-! ## Cuts -/

/-- The **cut** of `U ⊆ V(G)`: edges with one endpoint in `U` and one in `VF(G) \ U`. -/
noncomputable def Cut (G : FinGraph α β) (U : Finset α) : Finset (Edge α β) :=
  EF(G).filter (fun e => ∃ u ∈ U, u ∈ e.endpoints ∧ ∃ v ∈ VF(G) \ U, v ∈ e.endpoints)

namespace Cut

open Finset BigOperators

variable {R} [AddCommMonoid R] [CompleteLattice R] [CanonicallyOrderedAdd R]

/-- The weight of a cut under edge weight function `w`. -/
noncomputable def weight (G : FinGraph α β) (U : Finset α) (w : Edge α β → R) : R :=
  (Cut G U).sum w

/-- **Submodularity of cuts**: `w(δ(U ∩ W)) + w(δ(U ∪ W)) ≤ w(δ(U)) + w(δ(W))`. -/
lemma cut_submodular (G : FinGraph α β) (U W : Finset α) (w : Edge α β → R) :
    weight G (U ∩ W) w + weight G (U ∪ W) w ≤ weight G U w + weight G W w := by
  sorry

/-- A **`s`-`t` cut** separates `s` from `t`. -/
def isSTCut (G : FinGraph α β) (U : Finset α) (s t : α) : Prop :=
  s ∈ U ∧ t ∉ U ∧ U.Nonempty ∧ (U : Set α) ⊂ V(G)

/-- A **minimum `s`-`t` cut** minimises the cut weight. -/
def isSTMinCut (G : FinGraph α β) (U : Finset α) (s t : α)
    (w : Edge α β → R) : Prop :=
  isSTCut G U s t ∧ ∀ W : Finset α, isSTCut G W s t → weight G U w ≤ weight G W w

/-- The **minimum `s`-`t` cut value**. -/
def stMinCutValue (G : FinGraph α β) (s t : α) (w : Edge α β → R) : R :=
  sInf { c | ∃ U : Finset α, isSTCut G U s t ∧ weight G U w = c }

lemma isSTMinCut_iff {G : FinGraph α β} {U : Finset α} {s t : α}
    {w : Edge α β → R} :
    isSTMinCut G U s t w ↔
    isSTCut G U s t ∧ weight G U w = stMinCutValue G s t w := by
  constructor
  · intro ⟨hcut, hmin⟩
    exact ⟨hcut, le_antisymm
      (le_sInf (fun _ ⟨W, hW, hWc⟩ => hWc ▸ hmin W hW))
      (sInf_le ⟨U, hcut, rfl⟩)⟩
  · intro ⟨hcut, heq⟩
    exact ⟨hcut, fun W hW => heq ▸ sInf_le ⟨W, hW, rfl⟩⟩

/-- A **Gomory–Hu tree** for `G` simultaneously represents all pairwise minimum cuts. -/
def isGomoryHu
    (G : FinGraph α β) (wG : Edge α β → R)
    (T : Tree α β)    (wT : Edge α β → R) : Prop :=
  V(T.1) = V(G) ∧
  ∀ s t : α, s ∈ V(G) → t ∈ V(G) → s ≠ t →
    ∃ U : Finset α,
      isSTMinCut G   U s t wG ∧
      isSTMinCut T.1 U s t wT ∧
      weight G U wG = weight T.1 U wT

end Cut

end Set.graphOn_nonempty
