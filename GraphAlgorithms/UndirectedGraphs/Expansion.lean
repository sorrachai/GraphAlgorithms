import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.UndirectedGraphs.Cuts
import GraphAlgorithms.UndirectedGraphs.SimpleGraphs

-- Cuts and contractions (undirected simple)
-- Authors: Yuchen Zhong, Weixuan Yuan
-- LLM: Gemini, GPT-5.5 on codex

set_option tactic.hygienic false

open Finset
open Cuts

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

lemma energy_mul (G : SimpleGraph α) (x : α → ℝ) (c : ℝ) :
    G.energy (fun v => c * x v) = c ^ 2 * G.energy x := by
  classical
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u =>
    simp
    ring_nf

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

lemma deg_norm_mul (G : SimpleGraph α) (x : α → ℝ) (c : ℝ) :
    G.deg_norm (fun v => c * x v) = c ^ 2 * G.deg_norm x := by
  classical
  unfold deg_norm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma rQ_eq_energy_div_norm (G : SimpleGraph α) (x : α → ℝ) :
    G.rayleighQuotient x = G.energy x / G.deg_norm x := by
  unfold rayleighQuotient
  rfl

lemma rayleighQuotient_mul (G : SimpleGraph α) (x : α → ℝ) {c : ℝ} (hc : c ≠ 0) :
    G.rayleighQuotient (fun v => c * x v) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_mul, deg_norm_mul]
  field_simp [pow_ne_zero 2 hc]


noncomputable def restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) : α → ℝ :=
  fun v => if v ∈ V(G) then x v else 0

lemma energy_restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) :
    G.energy (restrictToVertexSet G x) = G.energy x := by
  classical
  unfold energy restrictToVertexSet
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h =>
    have huV : x_1 ∈ V(G) := G.incidence s(x_1, y) he x_1 (Sym2.mem_mk_left x_1 y)
    have hvV : y ∈ V(G) := G.incidence s(x_1, y) he y (Sym2.mem_mk_right x_1 y)
    simp [huV, hvV]

lemma deg_norm_restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) :
    G.deg_norm (restrictToVertexSet G x) = G.deg_norm x := by
  classical
  unfold deg_norm restrictToVertexSet
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv]

lemma rayleighQuotient_restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) :
    G.rayleighQuotient (restrictToVertexSet G x) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_restrictToVertexSet, deg_norm_restrictToVertexSet]

lemma orthogonalVectors_restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ)
    (horth : x ∈ orthogonalVectors G) :
    restrictToVertexSet G x ∈ orthogonalVectors G := by
  classical
  rcases horth with ⟨horth, hne⟩
  constructor
  · unfold restrictToVertexSet
    rw [show (∑ v ∈ V(G), ↑(#δ(G,v)) * (if v ∈ V(G) then x v else 0)) =
        ∑ v ∈ V(G), ↑(#δ(G,v)) * x v by
      apply Finset.sum_congr rfl
      intro v hv
      simp [hv]]
    exact horth
  · rcases hne with ⟨v, hv, hxv⟩
    exact ⟨v, hv, by simpa [restrictToVertexSet, hv] using hxv⟩


end SimpleGraph
