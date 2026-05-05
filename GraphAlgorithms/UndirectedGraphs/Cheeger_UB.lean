import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

import GraphAlgorithms.UndirectedGraphs.Cuts
import GraphAlgorithms.UndirectedGraphs.SimpleGraphs
import GraphAlgorithms.UndirectedGraphs.Expansion

namespace SimpleGraph

open Finset
open ProbabilityTheory MeasureTheory
open Cuts

variable {α : Type*} [DecidableEq α]

/--
TODO
1. Np_ne_zero
2. median property, h_m_pos
3. prove sweepCuts
4. lemma 3 -> cheeger ub
5. lemma 4
6. fact 2

Possible spin-off mini projects
1. min S <= min T  <=> ∀ x ∈ T, ∃ y ∈ S
2. probabilistic methods in lean

-/

-- Generates the set of all prefix cuts (sweep cuts) for a vector x.
noncomputable def sweepCuts (G : SimpleGraph α) (x : α → ℝ) : Finset (Finset α) :=
  let sortedV := (V(G).toList).mergeSort (fun u v => x u ≤ x v)
  let n := (V(G)).card
  let indices := List.range (n - 1)
  (indices.map (fun k => (sortedV.take (k + 1)).toFinset)).toFinset

lemma sweepCut_is_subset (G : SimpleGraph α) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S ⊆ V(G) := by
  intro S hS
  unfold sweepCuts at hS
  simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hS
  obtain ⟨k, hk, rfl⟩ := hS
  intro v hv
  -- Convert the Finset membership back to List membership
  rw [List.mem_toFinset] at hv
  have h_mem_sorted : v ∈ (V(G).toList).mergeSort (fun u v => x u ≤ x v) := by
    apply List.mem_of_mem_take hv
  rw [List.mem_mergeSort] at h_mem_sorted
  rw [← Finset.mem_toList]
  exact h_mem_sorted

lemma sweepCuts_are_nonempty (G : SimpleGraph α) (hV : 2 ≤ (V(G)).card) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S.Nonempty := by
  intro S hS
  unfold sweepCuts at hS
  simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hS
  obtain ⟨k, hk, rfl⟩ := hS
  rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]
  intro h_empty
  have h_list_len : 1 ≤ ((V(G)).toList.mergeSort (fun u v => x u ≤ x v)).length := by
    rw [List.length_mergeSort, Finset.length_toList]
    omega -- uses hV : 2 ≤ card
  simp_all only [List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
    List.length_nil, nonpos_iff_eq_zero]

lemma sweepCuts_expansion_nonempty (G : SimpleGraph α) (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (V(G)).card) :
    ((sweepCuts G x).image (fun S => edgeExpansion G d S)).Nonempty := by
  rw [Finset.image_nonempty]
  unfold sweepCuts
  rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff,
    List.map_eq_nil_iff, List.range_eq_nil]
  -- Use hV to show n - 1 ≥ 1
  omega

/-- The expansion of the best cut found by Fiedler's algorithm.
    Requires |V| ≥ 2 to ensure at least one cut exists. -/
noncomputable def fiedlerExpansion (G : SimpleGraph α) (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (V(G)).card) : ℝ :=
  let cuts := sweepCuts G x
  (cuts.image (fun S => edgeExpansion G d S)).min' (by
    exact sweepCuts_expansion_nonempty G d x hV
  )

/-- The actual set of vertices (cut) that achieves the fiedlerExpansion. -/
noncomputable def fiedlerCut (G : SimpleGraph α) (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (V(G)).card) : Finset α :=
  -- Pick a cut that attains the minimum expansion
  Classical.choose (Finset.mem_image.mp (Finset.min'_mem _ (sweepCuts_expansion_nonempty G d x hV)))


lemma fiedlerCut_mem_sweep (G : SimpleGraph α) (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (V(G)).card) :
  fiedlerCut G d x hV ∈ sweepCuts G x := by
  unfold fiedlerCut
  -- Classical.choose_spec retrieves the property:
  -- S ∈ sweepCuts ∧ edgeExpansion G d S = fiedlerExpansion G d x hV
  exact (Classical.choose_spec (Finset.mem_image.mp (
      Finset.min'_mem _ (sweepCuts_expansion_nonempty G d x hV)
    ))).1

lemma fiedlerCut_nonempty (G : SimpleGraph α) (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (V(G)).card) :
    (fiedlerCut G d x hV).Nonempty := by
  let S_f := fiedlerCut G d x hV
  have hS_mem : S_f ∈ sweepCuts G x := fiedlerCut_mem_sweep G d x hV
  apply sweepCuts_are_nonempty G hV x
  exact hS_mem

lemma fiedlerCut_is_subset (G : SimpleGraph α) (d : ℕ) (x : α → ℝ) (hV : 2 ≤ (V(G)).card) :
  fiedlerCut G d x hV ⊆ V(G) := by
  apply sweepCut_is_subset G x
  exact fiedlerCut_mem_sweep G d x hV

lemma sum_sq_pos (G : SimpleGraph α) (x : α → ℝ) (hV : 2 ≤ (V(G)).card)
    (h_x_ne : ∃ v ∈ V(G), x v ≠ 0) : 0 < ∑ i ∈ V(G), x i ^ 2 := by
  have h_nonneg : 0 ≤ ∑ i ∈ V(G), x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  apply lt_of_le_of_ne h_nonneg
  intro h_sum_zero
  have h_all_zero : ∀ i ∈ V(G), x i = 0 := by
    intro i hi
    have h_sq_zero : x i ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg _).mp h_sum_zero.symm i hi
      intro j hj
      apply sq_nonneg
    exact eq_zero_of_pow_eq_zero h_sq_zero
  grind

/-- Lemma 5: Let x be orthogonal to 1. There exists a non-negative vector y with
    at most |V|/2 non-zero entries such that R_L(y) ≤ R_L(x). -/
lemma lemma_5 (G : SimpleGraph α) (x : α → ℝ) (d : ℕ) (hV : 2 ≤ (V(G)).card)
    (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    ∃ y : α → ℝ,
      (∀ v, 0 ≤ y v) ∧
      (2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) ∧
      rayleighQuotient G y ≤ rayleighQuotient G x ∧
      (∀ t > 0, {v ∈ V(G) | y v ≥ t} ∈ sweepCuts G x) := by
  /-
    Proof Sketch[cite: 104, 107, 114]:
    1. Let m be the median of x. Let x' = x - m1.
    2. Split x' into positive part x⁺ and negative part x⁻.
    3. Show R_L(x') ≤ R_L(x)[cite: 104].
    4. Show min(R_L(x⁺), R_L(x⁻)) ≤ R_L(x')[cite: 117].
    5. Threshold cuts of x⁺ or x⁻ are sub-collections of the sweep cuts of x[cite: 110, 112].
  -/

  let n := (V(G)).card
  let sorted_vals := (V(G).toList.map x).mergeSort (· ≤ ·)
  let m := sorted_vals.get ⟨n / 2, by
    have h_len : sorted_vals.length = n := by
      simp [sorted_vals, n]
    rw [h_len]
    apply Nat.div_lt_self
    · omega
    · exact by norm_num
  ⟩

  -- 1. Shift x by the median m
  let x_sh := fun v => x v - m
  let x_pos := fun v => max (x_sh v) 0
  let x_neg := fun v => max (-x_sh v) 0

  -- 2. Orthogonality justifies the denominator bound
  have h_den : V(G).sum (fun v => (x v)^2) ≤ V(G).sum (fun v => (x_sh v)^2) := by
    simp only [sub_sq, x_sh]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- Use h_orth: sum x_i = 0 (for d-regular)
    have h_zero : V(G).sum (fun v => 2 * x v * m) = 0 := by
      rw [← Finset.sum_mul]
      simp_all only [mul_eq_zero]
      left
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum] at h_orth
      simp_all
    rw [h_zero]
    simp
    nlinarith

  -- 1. The numerators are equal
  have h_num : G.energy x_sh = G.energy x := by
    unfold SimpleGraph.energy
    simp [x_sh]

  have h_ray_sh : rayleighQuotient G x_sh ≤ rayleighQuotient G x := by
    unfold rayleighQuotient
    rw [← energy, ← energy, h_num]
    apply div_le_div_of_nonneg_left
    · exact energy_nonneg G x
    · have h_den_d : ∑ v ∈ V(G), ↑(#δ(G,v)) * x v ^ 2 = ∑ v ∈ V(G), (d : ℝ) * x v ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [h_reg v hv]
      rw [h_den_d, ← Finset.mul_sum]
      apply mul_pos
      · norm_cast
        exact Nat.pos_of_ne_zero h_d_pos
      · apply sum_sq_pos G x hV h_x_ne
    · calc
        ∑ v ∈ V(G), ↑(#δ(G,v)) * x v ^ 2 = ∑ v ∈ V(G), (d : ℝ) * x v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [h_reg v hv]
        _ = (d : ℝ) * ∑ v ∈ V(G), x v ^ 2 := by rw [Finset.mul_sum]
        _ ≤ (d : ℝ) * ∑ v ∈ V(G), x_sh v ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_den
          norm_cast
          exact Nat.zero_le d
        _ = ∑ v ∈ V(G), (d : ℝ) * x_sh v ^ 2 := by rw [Finset.mul_sum]
        _ = ∑ v ∈ V(G), ↑(#δ(G,v)) * x_sh v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [h_reg v hv]

  -- One shot by Gemini
  have h_energy_split : G.energy x_sh ≥ G.energy x_pos + G.energy x_neg := by
    unfold energy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e he
    induction e using Sym2.ind
    case h u v =>
      dsimp [x_pos, x_neg]
      -- Let A = (x_pos u - x_pos v) and B = (x_neg u - x_neg v)
      let A := max (x_sh u) 0 - max (x_sh v) 0
      let B := max (-x_sh u) 0 - max (-x_sh v) 0
      -- Using the identity: (x_sh u - x_sh v) = A - B
      have h_ident : x_sh u - x_sh v = A - B := by
        -- Expand A and B definitions
        simp only [A, B]
        -- Use the fundamental max(c, 0) - max(-c, 0) = c identity
        have h_u : x_sh u = max (x_sh u) 0 - max (-x_sh u) 0 := by
          rcases le_total 0 (x_sh u) with h | h
          · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
          · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
        have h_v : x_sh v = max (x_sh v) 0 - max (-x_sh v) 0 := by
          rcases le_total 0 (x_sh v) with h | h
          · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
          · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
        rw [h_u, h_v]
        grind
      rw [h_ident]
      -- Expand (A - B)^2 = A^2 + B^2 - 2AB
      have h_expand : (A - B)^2 = A^2 + B^2 - 2 * A * B := by ring
      rw [h_expand]
      -- Goal: A^2 + B^2 - 2AB ≥ A^2 + B^2, which reduces to AB ≤ 0
      suffices A * B ≤ 0 by linarith
      -- Case analysis on the signs of x_sh u and x_sh v
      by_cases hu : 0 ≤ x_sh u <;> by_cases hv : 0 ≤ x_sh v
      · -- Case 1: u ≥ 0, v ≥ 0
        have hB : B = 0 := by
          simp [B, hu, hv]
        simp [hB]
      · -- Case 2: u ≥ 0, v < 0
        have hA : A = x_sh u := by simp [A, hu]; linarith
        have hB : B = x_sh v := by
          simp only [Left.neg_nonpos_iff, hu, sup_of_le_right, zero_sub, B]
          have hv_lt : x_sh v < 0 := lt_of_not_ge hv
          have h_max : max (-x_sh v) 0 = -x_sh v := by
            apply max_eq_left
            linarith [hv_lt]
          rw [h_max]
          simp
        rw [hA, hB]
        apply mul_nonpos_of_nonneg_of_nonpos hu (by linarith)
      · -- Case 3: u < 0, v ≥ 0
        have hA : A = -x_sh v := by simp [A, hv]; linarith
        have hB : B = -x_sh u := by simp [B, hv]; linarith
        rw [hA, hB]
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      · -- Case 4: u < 0, v < 0
        have hA : A = 0 := by
          simp only [A]
          have hu_lt : x_sh u < 0 := lt_of_not_ge hu
          have hv_lt : x_sh v < 0 := lt_of_not_ge hv
          have h1 : max (x_sh u) 0 = 0 := max_eq_right hu_lt.le
          have h2 : max (x_sh v) 0 = 0 := max_eq_right hv_lt.le
          rw [h1, h2]
          simp
        simp [hA]

  -- One shot by Gemini
  -- have h_norm_split : ∑ v ∈ V(G), ↑d * x_sh v ^ 2 =
  --     ∑ v ∈ V(G), ↑d * x_pos v ^ 2 + ∑ v ∈ V(G), ↑d * x_neg v ^ 2 := by
  have h_norm_split : G.deg_norm x_sh = G.deg_norm x_pos + G.deg_norm x_neg := by
    unfold deg_norm
    simp_rw [x_pos, x_neg, x_sh]
    -- Use the fact that (a-m)^2 = (max(a-m, 0))^2 + (max(-(a-m), 0))^2
    -- Goal: ∑ ↑d * x_sh v ^ 2 = ∑ ↑d * x_pos v ^ 2 + ∑ ↑d * x_neg v ^ 2
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← mul_add]
    congr 1
    -- The core algebraic identity: c^2 = (max c 0)^2 + (max -c 0)^2
    let c := x v - m
    change c^2 = (max c 0)^2 + (max (-c) 0)^2
    rcases le_total 0 c with h | h
    · -- Case c ≥ 0
      rw [max_eq_left h, max_eq_right]
      · simp
      · linarith
    · -- Case c < 0
      rw [max_eq_right h, max_eq_left]
      · simp
      · linarith

  let Ep := G.energy x_pos
  let En := G.energy x_neg
  let Np := G.deg_norm x_pos
  let Nn := G.deg_norm x_neg

  have Np_ne_zero : Np ≠ 0 := by sorry

  have Nn_ne_zero : Nn ≠ 0 := by sorry

  have h_Np_pos : Np > 0 := by
    unfold Np
    have h_nonneg : G.deg_norm x_pos ≥ 0 := G.deg_norm_nonneg x_pos
    have h_ne_zero : G.deg_norm x_pos ≠ 0 := by grind
    exact lt_of_le_of_ne h_nonneg h_ne_zero.symm

  have h_Nn_pos : Nn > 0 := by
    unfold Nn
    have h_nonneg : G.deg_norm x_neg ≥ 0 := G.deg_norm_nonneg x_neg
    have h_ne_zero : G.deg_norm x_neg ≠ 0 := by grind
    exact lt_of_le_of_ne h_nonneg h_ne_zero.symm

  have h_calc : G.rayleighQuotient x_sh
      ≥ min (G.rayleighQuotient x_pos) (G.rayleighQuotient x_neg) := by
    calc
      G.rayleighQuotient x_sh = G.energy x_sh / G.deg_norm x_sh := by
        unfold rayleighQuotient
        rw [← energy, ← deg_norm]
      _ ≥ (Ep + En) / (Np + Nn) := by
        -- Use h_energy_split and h_norm_split
        rw [h_norm_split]
        apply div_le_div_of_nonneg_right
        · unfold Ep En
          simp only [h_energy_split]
        · unfold Np Nn
          rw [← h_norm_split]
          simp only [deg_norm_nonneg]
      _ = ((Ep / Np) * Np + (En / Nn) * Nn) / (Np + Nn) := by
        simp_all only [ne_eq, List.get_eq_getElem, neg_sub, ge_iff_le, isUnit_iff_ne_zero,
          not_false_eq_true, IsUnit.div_mul_cancel, x_sh, m, sorted_vals, n,
          x_pos, x_neg, Np, Nn, Ep, En]
      _ = (G.rayleighQuotient x_pos * Np + G.rayleighQuotient x_neg * Nn) / (Np + Nn) := by
        unfold Ep En Np Nn
        simp only [← rQ_eq_energy_div_norm]
      _ ≥ min (G.rayleighQuotient x_pos) (G.rayleighQuotient x_neg) := by
          rw [ge_iff_le, min_le_iff]
          by_cases h : G.rayleighQuotient x_pos ≤ G.rayleighQuotient x_neg
          · left
            rw [le_div_iff₀ (by linarith [h_Np_pos, h_Nn_pos])]
            rw [mul_add]
            simp only [add_le_add_iff_left]
            gcongr

          · right
            rw [le_div_iff₀ (by linarith [h_Np_pos, h_Nn_pos])]
            rw [mul_add]
            simp only [add_le_add_iff_right]
            have h_le : G.rayleighQuotient x_neg ≤ G.rayleighQuotient x_pos := by
              grind
            gcongr

  -- Since R(x_sh) ≥ min (R x_pos) (R x_neg), one of them must be ≤ R(x_sh)
  -- Combined with h_ray_sh (R x_sh ≤ R x), we find our candidate y
  have h_min_le : G.rayleighQuotient x_pos ≤ G.rayleighQuotient x ∨
      G.rayleighQuotient x_neg ≤ G.rayleighQuotient x := by grind

  have h_pos_set : {v ∈ V(G) | x_pos v > 0} = {v ∈ V(G) | x v > m} := by
    ext v; simp [x_pos, x_sh]

  have h_m_pos : #({v ∈ V(G) | x_pos v > 0}) ≤ #V(G) / 2 := by
    rw [h_pos_set]

    let L := sorted_vals
    let n := #V(G)
    let k := n / 2

    sorry

  have h_neg_set : {v ∈ V(G) | x_neg v > 0} = {v ∈ V(G) | x v < m} := by
    ext v; simp [x_neg, x_sh]

  have h_m_neg : #({v ∈ V(G) | x_neg v > 0}) ≤ #V(G) / 2 := by
    -- support x_neg is {v | x v < m}
    rw [h_neg_set]

    sorry


  rcases h_min_le with h_pos | h_neg
  · -- Case 1: y = x_pos
    use x_pos
    refine ⟨fun v ↦ le_max_right _ _, ?_, h_pos, ?_⟩
    · grind
    · -- Prove level sets are sweep cuts
      intro t ht
      have h_pos_set_r : {v ∈ V(G) | x_pos v ≥ t} = {v ∈ V(G) | x v ≥ m + t} := by grind
      rw [h_pos_set_r]
      unfold sweepCuts
      simp only [List.mem_toFinset, List.mem_map, List.mem_range]
      let k := (V(G).filter (fun v => x v < m + t)).card
      use (n - k - 1)

      -- 1. Let L be the list of vertices sorted by the values of x
      let sortedV := (V(G).toList).mergeSort (fun u v => x u ≤ x v)

      -- 2. Define k as the number of vertices strictly less than the threshold
      let k := (sortedV.filter (fun v => x v < m + t)).length

      -- 3. In sweepCuts, prefix cuts are defined as taking (i + 1) elements
      -- For d-regular graphs, the expansion of a set S is equal to the expansion
      -- of its complement Sᶜ[cite: 65].
      -- If {v | x v ≥ m + t} is the suffix, its complement {v | x v < m + t}
      -- is exactly the prefix (sortedV.take k).

      have h_prefix_mem : (sortedV.take k).toFinset ∈ sweepCuts G x := by
        unfold sweepCuts
        simp only [List.mem_toFinset, List.mem_map, List.mem_range]
        use k - 1
        constructor
        · -- k must be within range [1, n-1]
          sorry
        · sorry
          -- simp only [Nat.sub_add_cancel] -- results in (sortedV.take k)

      -- 4. Since edgeExpansion G d S = edgeExpansion G d Sᶜ,
      -- and fiedlerExpansion is the minimum over ALL sweep cuts[cite: 7],
      -- showing the complement is a sweep cut is sufficient for the bound.

      -- rw [← edgeExpansion_complement G d]
      -- exact h_prefix_mem
      sorry

  · -- Case 2: y = x_neg
    use x_neg
    refine ⟨fun v ↦ le_max_right _ _, ?_, h_neg, ?_⟩
    · grind
    · -- Prove level sets are sweep cuts
      intro t ht
      have h_neg_set_r : {v ∈ V(G) | x_neg v ≥ t} = {v ∈ V(G) | x v ≤ m - t} := by grind
      rw [h_neg_set_r]
      unfold sweepCuts

      sorry










/-- Lemma 4: For a non-negative vector y, there exists a threshold t such that
    the expansion of the set S_t = {v : y_v ≥ t} is at most sqrt(2 * R_L(y)). -/
lemma lemma_4 (G : SimpleGraph α) (d : ℕ) (y : α → ℝ) (hV : 2 ≤ (V(G)).card)
    (h_pos : ∀ v, 0 ≤ y v)
    (h_supp : 2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) :
    ∃ t > 0,
      let S_t := V(G).filter (fun v => y v ≥ t)
      S_t.Nonempty → edgeExpansion G d S_t ≤ Real.sqrt (2 * rayleighQuotient G y) := by
  /-
    Proof Strategy from Lecture 3:
    1. Define the expansion of S_t as ϕ(S_t) = |Cut(S_t)| / (d * |S_t|).
    2. Consider the threshold t chosen such that t² is uniform in [0, max(y²)].
    3. Show that E[|Cut(S_t)|] / E[d * |S_t|] ≤ sqrt(2 * R_L(y)).
    4. By Fact 2 (probabilistic method), there exists a threshold t satisfying the bound.
  -/
  let R_y := rayleighQuotient G y

  -- 1. Cauchy-Schwarz on the edges:
  -- (∑ |y_u^2 - y_v^2|)^2 ≤ (∑ (y_u - y_v)^2) * (∑ (y_u + y_v)^2)
  -- This relates the Cut sizes to the Rayleigh Numerator.
  have h_CS : (∑ e ∈ E(G), |y (G.source e)^2 - y (G.target e)^2|) ≤
              Real.sqrt (2 * R_y) * (∑ v ∈ V(G), d * y v^2) := by
    sorry

  -- 2. Level Set Decomposition (Discrete Expectation):
  -- Let T be the set of unique values in the range of y (sorted).
  let T := (V(G).image y).sort (· ≤ ·)

  -- We argue by contradiction: if every S_t has expansion > √2R,
  -- then the total sum of cuts would exceed the Cauchy-Schwarz bound.
  by_contra h_all_gt
  push_neg at h_all_gt

  -- Summing over intervals between sorted values of y:
  -- ∑ (y_{i+1}^2 - y_i^2) * |Cut(S_{y_{i+1}})| > ∑ (y_{i+1}^2 - y_i^2) * √2R * d|S_{y_{i+1}}|
  have h_sum_gt : (∑ e in G.edgeFinset, |y (G.source e)^2 - y (G.target e)^2|) >
                  Real.sqrt (2 * R_y) * (∑ v in V(G), d * y v^2) := by
    sorry

  -- 3. Contradiction between h_CS and h_sum_gt
  exact absurd h_sum_gt (not_lt.mpr h_CS)

/-- Fact 2 from Lecture 3:
    Let X and Y be random variables such that P[Y > 0] = 1.
    Then there exists an outcome ω such that X(ω)/Y(ω) ≤ E[X]/E[Y]. -/
lemma fact_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (hY_pos : ∀ᵐ ω ∂P, 0 < Y ω) (hEY_pos : 0 < ∫ ω, Y ω ∂P) :
    ∃ ω, X ω / Y ω ≤ (∫ ω, X ω ∂P) / (∫ ω, Y ω ∂P) := by
  let r := (∫ ω, X ω ∂P) / (∫ ω, Y ω ∂P)

  sorry










lemma lemma3 (G : SimpleGraph α) (d : ℕ) (x : α → ℝ) (h_d_pos : d ≠ 0)
    (hV : 2 ≤ (V(G)).card) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0) :
    let S_f := fiedlerCut G d x hV
    S_f.Nonempty ∧ S_f ⊆ V(G) ∧ G.edgeExpansion d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
  let S_f := fiedlerCut G d x hV
  let R_x := G.rayleighQuotient x
  -- 1. Structural Properties (Non-empty and Subset)
  have hS_ne : S_f.Nonempty := fiedlerCut_nonempty G d x hV
  have hS_sub : S_f ⊆ V(G) := fiedlerCut_is_subset G d x hV
  -- 2. Use Lemma 5 and Lemma 4 to establish the existence of a good threshold cut
  obtain ⟨y, h_pos, h_supp, h_rayleigh, h_sweep_subset⟩ :=
    lemma_5 G x d hV h_d_pos h_x_ne h_orth h_reg
  obtain ⟨t, ht_pos, h_phi_impl⟩ := lemma_4 G d y hV h_pos h_supp
  -- From lemma_5, there exists a specific S_t in sweepCuts G x
  -- that corresponds to the threshold t of y.
  let h_exists := h_sweep_subset t ht_pos
  let S_t := V(G).filter (fun v => y v ≥ t)
  have hSt_mem : S_t ∈ sweepCuts G x := h_exists
  have hSt_eq : S_t = V(G).filter (fun v => y v ≥ t) := by grind
  -- Assume y is the vector from Lemma 5 and t is from Lemma 4
  have hSt_ne : (V(G).filter (fun v => y v ≥ t)).Nonempty := by
    rw [← hSt_eq]
    apply sweepCuts_are_nonempty G hV x
    exact hSt_mem
  have h_lem_4 : G.edgeExpansion d S_t ≤ √(2 * G.rayleighQuotient y) := by
    apply h_phi_impl
    exact hSt_ne
  -- 3. Expansion Property: fiedlerCut is at least as good as S_t
  have h_exp_bound : G.edgeExpansion d S_f ≤ G.edgeExpansion d S_t := by
    unfold S_f
    let expansion_vals := (sweepCuts G x).image (fun S => edgeExpansion G d S)
    let h_nonempty := sweepCuts_expansion_nonempty G d x hV
    have h_Sf_is_min :
        edgeExpansion G d (fiedlerCut G d x hV) = expansion_vals.min' h_nonempty := by
      unfold fiedlerCut
      exact (
          Classical.choose_spec (Finset.mem_image.mp (Finset.min'_mem _ h_nonempty))
        ).2
    rw [h_Sf_is_min]
    apply Finset.min'_le
    rw [Finset.mem_image]
    use S_t
  -- 4. Algebraic Chain: ϕ(S_f)² ≤ ϕ(S_t)² ≤ 2R(y) ≤ 2R(x)
  have h_alg : G.edgeExpansion d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
    calc G.edgeExpansion d S_f
      _ ≤ G.edgeExpansion d S_t := by omega
      _ ≤ Real.sqrt (2 * G.rayleighQuotient y) := by omega
      _ ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
        have h_mul : 2 * G.rayleighQuotient y ≤ 2 * G.rayleighQuotient x := by
          apply mul_le_mul_of_nonneg_left h_rayleigh
          norm_num -- proves 2 ≥ 0
        apply Real.sqrt_le_sqrt h_mul
  exact ⟨fiedlerCut_nonempty G d x hV, fiedlerCut_is_subset G d x hV, h_alg⟩










/-- Lemma: There exists a non-zero vector x orthogonal to the constant vector
    such that its Rayleigh quotient achieves λ₂. -/
lemma exists_eigenvector_lambda2 (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) (hV : 2 ≤ #V(G)) :
    ∃ x : α → ℝ, (∃ v ∈ V(G), x v ≠ 0) ∧
      (∑ v ∈ V(G), x v = 0) ∧
      G.rayleighQuotient x = G.lambda2 := by
  -- 1. Define the subspace V' = {x : α → ℝ | ∑ x v = 0}
  let V_orth := {x : α → ℝ | ∑ v ∈ V(G), x v = 0}

  -- 2. Define the Rayleigh quotient restricted to the unit sphere in V_orth
  -- Let S = {x ∈ V_orth | ‖x‖ = 1}. This set is compact because α is finite.
  let unit_sphere_orth := {x : α → ℝ | x ∈ V_orth ∧ ∑ v ∈ V(G), (x v)^2 = 1}

  -- 3. Since the graph is finite, the unit sphere is a closed and bounded subset
  -- of a finite-dimensional Euclidean space, hence it is compact.
  have h_compact : IsCompact (unit_sphere_orth) := by
    -- Standard topology: closed and bounded in finite dimensions
    sorry

  -- 4. The Rayleigh quotient R(x) is continuous on this compact set.
  -- By the Extreme Value Theorem (IsCompact.exists_isMinOn), there exists
  -- a vector x that attains the minimum.
  have h_cont : ContinuousOn (G.rayleighQuotient) unit_sphere_orth := by
    -- R(x) is a rational function with a non-zero denominator on the sphere
    sorry

  obtain ⟨x, hx_mem, hx_min⟩ := h_compact.exists_isMinOn (by
    -- Show the sphere is non-empty given |V| ≥ 2
    sorry
  ) h_cont

  -- 5. By the variational characterization of λ₂, this minimum is exactly λ₂.
  use x
  refine ⟨?_, hx_mem.1, ?_⟩
  · -- Prove x is non-zero (since its norm is 1)
    obtain ⟨v, hv⟩ := (Finset.nonempty_iff_ne_empty.mpr (V_G_ne_empty G hV)).exists_mem
    use v, hv
    intro h_zero
    have : ∑ v ∈ V(G), (x v)^2 = 0 := by
      -- if all entries were zero, the sum of squares would be 0, not 1
      sorry
    linarith [hx_mem.2]
  · -- R(x) = λ₂
    rw [← hx_min]
    -- λ₂ is the infimum over the whole subspace; since R is scale-invariant,
    -- the infimum over the sphere is the same as the infimum over the subspace.
    sorry

/-- The Hard Direction of Cheeger's Inequality: h(G) ≤ √(2 * λ₂) -/
theorem cheeger_hard_direction (G : SimpleGraph α) [Finite α] (d : ℕ)
    (hV : 2 ≤ #V(G))
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    graphExpansion G d ≤ Real.sqrt (2 * G.lambda2) := by
  -- 1. Obtain the second eigenvector x with R(x) = λ₂
  obtain ⟨x, h_x_ne, h_orth_const, h_lambda2⟩ := G.exists_eigenvector_lambda2 d h_reg hV

  -- 2. Convert orthogonality to the degree-weighted form required by Lemma 3
  -- For d-regular graphs: ∑ d_i x_i = d * ∑ x_i = 0
  have h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0 := by
    -- simp_rw [h_reg _ (mem_V _), ← mul_sum]
    -- rw [h_orth_const, mul_zero]
    sorry

  -- 3. Handle the d = 0 case (isolated vertices)
  by_cases h_d_pos : d = 0
  · -- If d = 0, expansion is 0 and lambda2 is 0.
    simp [h_d_pos]
    sorry

  -- 4. Apply Lemma 3 (The Sweep Cut Lemma)
  -- This provides a cut S_f (the Fiedler cut) from the level sets of x
  let S_f := fiedlerCut G d x hV
  obtain ⟨hS_ne, hS_sub, hS_phi⟩ := lemma3 G d x h_d_pos hV h_reg h_x_ne h_orth

  -- 5. Relate h(G) to the expansion of this specific Fiedler cut
  -- Since h(G) = min_{|S|≤n/2} ϕ(S), and Lemma 3 guarantees S_f is valid:
  have h_cheeger_le : graphExpansion G d ≤ edgeExpansion G d S_f := by
    -- S_f is one of the sweep cuts of x, which by Lemma 5 satisfies |S| ≤ |V|/2
    -- apply graphExpansion_le_fiedlerExpansion G d x hV
    sorry

  -- 6. Final Chain of Inequalities
  calc
    graphExpansion G d ≤ edgeExpansion G d S_f := h_cheeger_le
    _ ≤ Real.sqrt (2 * G.rayleighQuotient x) := hS_phi
    _ = Real.sqrt (2 * G.lambda2) := by rw [h_lambda2]

end SimpleGraph
