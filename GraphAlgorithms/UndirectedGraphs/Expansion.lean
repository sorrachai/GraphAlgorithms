import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.UndirectedGraphs.SimpleGraphs
import GraphAlgorithms.UndirectedGraphs.Cuts

-- Cuts and contractions (undirected simple)
-- Authors: Yuchen Zhong
-- Vibe coding assist by Gemini

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open Finset
open SimpleGraph Cuts

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

variable {α : Type*} [DecidableEq α]

noncomputable def edgeExpansion (G : SimpleGraph α) (d : ℕ) (S : Finset α) : ℝ :=
  ( (Cut G S).card : ℝ ) / ( (d * S.card) : ℝ )

noncomputable def graphExpansion (G : SimpleGraph α) (d : ℕ) : ℝ :=
  let validSubsets := (V(G).powerset).filter (fun S => S.Nonempty ∧ 2 * S.card ≤ (V(G)).card)
  if h : validSubsets.Nonempty then
    (validSubsets.image (fun S => edgeExpansion G d S)).min' (by
      -- The image of a non-empty set is non-empty.
      exact Finset.Nonempty.image h (fun S => edgeExpansion G d S)
    )
  else 0

noncomputable def rayleighQuotient (G : SimpleGraph α) (x : α → ℝ) : ℝ :=
  let numerator := E(G).sum (fun e =>
    e.lift ⟨fun u v => (x u - x v)^2, by
      intro u v
      dsimp
      ring
    ⟩
  )
  let denominator := V(G).sum (fun v => (deg(G,v) : ℝ) * (x v)^2)
  numerator / denominator

lemma rayleighQuotient_nonneg (G : SimpleGraph α) (x : α → ℝ) :
  0 ≤ rayleighQuotient G x := by
  unfold rayleighQuotient
  apply div_nonneg
  · -- Numerator: ∑ (x u - x v)² ≥ 0
    apply sum_nonneg
    intro e _
    -- Use Sym2.inductionOn to handle the unordered pair
    induction e using Sym2.inductionOn with
    | hf u v =>
      dsimp
      exact sq_nonneg (x u - x v)
  · -- Denominator: ∑ d_v * x_v² ≥ 0
    apply sum_nonneg
    intro v _
    apply mul_nonneg
    · -- Degrees are natural numbers, so their real coercion is ≥ 0
      norm_cast
      exact Nat.zero_le _
    · -- Squares are ≥ 0
      exact sq_nonneg (x v)

def orthogonalVectors (G : SimpleGraph α) : Set (α → ℝ) :=
  { x | (V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0) ∧ (∃ v ∈ V(G), x v ≠ 0) }

def R_values (G : SimpleGraph α) : Set ℝ :=
  { r | ∃ x ∈ orthogonalVectors G, r = rayleighQuotient G x }

noncomputable def lambda2 (G : SimpleGraph α) : ℝ :=
  sInf (R_values G)

-- lambda2 ≥ 0
lemma lambda2_bounded_below (G : SimpleGraph α) :
  BddBelow { r : ℝ | ∃ x : α → ℝ, (V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0) ∧
    (∃ v ∈ V(G), x v ≠ 0) ∧ r = rayleighQuotient G x } := by
  use 0
  intro r hr
  simp only [Set.mem_setOf_eq] at hr
  rcases hr with ⟨x, _, _, rfl⟩
  apply rayleighQuotient_nonneg

noncomputable def energy (G : SimpleGraph α) (x : α → ℝ) : ℝ :=
  ∑ e ∈ E(G), Sym2.lift ⟨fun u v ↦ (x u - x v) ^ 2, by
    expose_names
    intro a1 a2
    dsimp
    rw [← neg_sub]
    linarith
  ⟩ e

lemma energy_nonneg (G : SimpleGraph α) (x : α → ℝ) :
    0 ≤ energy G x := by
  unfold energy
  apply Finset.sum_nonneg
  intro e he
  induction e using Sym2.ind
  case h =>
    dsimp
    apply sq_nonneg

noncomputable def deg_norm (G : SimpleGraph α) (x : α → ℝ) : ℝ :=
  ∑ v ∈ V(G), ↑(#δ(G,v)) * x v ^ 2

lemma deg_norm_nonneg (G : SimpleGraph α) (x : α → ℝ) :
    0 ≤ deg_norm G x := by
  unfold deg_norm
  apply Finset.sum_nonneg
  intro v hv
  apply mul_nonneg
  · norm_cast
    exact Nat.zero_le _
  · exact sq_nonneg (x v)

lemma deg_norm_eq_sum_reg (G : SimpleGraph α) (x : α → ℝ) (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    deg_norm G x = ∑ v ∈ V(G), (d : ℝ) * x v ^ 2 := by
  unfold deg_norm
  apply Finset.sum_congr rfl
  intro v hv
  rw [h_reg v hv]

end SimpleGraph
