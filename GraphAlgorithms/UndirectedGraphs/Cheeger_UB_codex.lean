import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

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

noncomputable def restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) : α → ℝ :=
  fun v => if v ∈ V(G) then x v else 0

lemma energy_restrictToVertexSet (G : SimpleGraph α) (x : α → ℝ) :
    G.energy (restrictToVertexSet G x) = G.energy x := by
  classical
  unfold energy restrictToVertexSet
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u v =>
    have huV : u ∈ V(G) := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
    have hvV : v ∈ V(G) := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
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

lemma energy_mul (G : SimpleGraph α) (x : α → ℝ) (c : ℝ) :
    G.energy (fun v => c * x v) = c ^ 2 * G.energy x := by
  classical
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u v =>
    simp
    ring_nf

lemma deg_norm_mul (G : SimpleGraph α) (x : α → ℝ) (c : ℝ) :
    G.deg_norm (fun v => c * x v) = c ^ 2 * G.deg_norm x := by
  classical
  unfold deg_norm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma rayleighQuotient_mul (G : SimpleGraph α) (x : α → ℝ) {c : ℝ} (hc : c ≠ 0) :
    G.rayleighQuotient (fun v => c * x v) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_mul, deg_norm_mul]
  field_simp [pow_ne_zero 2 hc]

/-
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

-- Generates the set of all prefix and suffix cuts (sweep cuts) for a vector x.
noncomputable def sweepCuts (G : SimpleGraph α) (x : α → ℝ) : Finset (Finset α) :=
  by
    classical
    let sortedV := (V(G).toList).mergeSort (fun u v => x u ≤ x v)
    let n := (V(G)).card
    let indices := List.range (n / 2)
    let prefixes := indices.map (fun k => (sortedV.take (k + 1)).toFinset)
    let suffixes := indices.map (fun k => (sortedV.reverse.take (k + 1)).toFinset)
    let lowerLevels :=
      (V(G).powerset).filter
        (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = V(G).filter (fun v => x v ≤ t))
    let upperLevels :=
      (V(G).powerset).filter
        (fun S => S.Nonempty ∧ 2 * S.card ≤ n ∧ ∃ t : ℝ, S = V(G).filter (fun v => x v ≥ t))
    exact (prefixes ++ suffixes).toFinset ∪ (lowerLevels ∪ upperLevels)

lemma sweepCut_is_subset (G : SimpleGraph α) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S ⊆ V(G) := by
  intro S hS
  unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  intro v hv
  rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
  · rw [List.mem_toFinset] at hv
    have h_mem_sorted : v ∈ (V(G).toList).mergeSort (fun u v => x u ≤ x v) := by
      apply List.mem_of_mem_take hv
    rw [List.mem_mergeSort] at h_mem_sorted
    rw [← Finset.mem_toList]
    exact h_mem_sorted
  · rw [List.mem_toFinset] at hv
    have h_mem_rev : v ∈ ((V(G).toList).mergeSort (fun u v => x u ≤ x v)).reverse := by
      apply List.mem_of_mem_take hv
    have h_mem_sorted : v ∈ (V(G).toList).mergeSort (fun u v => x u ≤ x v) := by
      simpa using List.mem_reverse.mp h_mem_rev
    rw [List.mem_mergeSort] at h_mem_sorted
    rw [← Finset.mem_toList]
    exact h_mem_sorted
  · rcases hLevels with hLower | hUpper
    · exact hLower.1 hv
    · exact hUpper.1 hv

lemma sweepCuts_are_nonempty (G : SimpleGraph α) (hV : 2 ≤ (V(G)).card) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, S.Nonempty := by
  intro S hS
  unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
  · rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]
    intro h_empty
    have h_list_len : 1 ≤ ((V(G)).toList.mergeSort (fun u v => x u ≤ x v)).length := by
      rw [List.length_mergeSort, Finset.length_toList]
      omega
    simp_all only [List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or,
      List.length_nil, nonpos_iff_eq_zero]
  · rw [Finset.nonempty_iff_ne_empty, ne_eq, List.toFinset_eq_empty_iff]
    intro h_empty
    have h_list_len : 1 ≤ (((V(G)).toList.mergeSort (fun u v => x u ≤ x v)).reverse).length := by
      rw [List.length_reverse, List.length_mergeSort, Finset.length_toList]
      omega
    simp_all only [List.take_eq_nil_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      false_or, List.length_nil, nonpos_iff_eq_zero]
  · rcases hLevels with hLower | hUpper
    · exact hLower.2.1
    · exact hUpper.2.1

lemma sweepCuts_expansion_nonempty (G : SimpleGraph α) (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (V(G)).card) :
    ((sweepCuts G x).image (fun S => edgeExpansion G d S)).Nonempty := by
  rw [Finset.image_nonempty]
  refine ⟨(List.take (0 + 1) ((V(G)).toList.mergeSort
    (fun u v => x u ≤ x v))).toFinset, ?_⟩
  unfold sweepCuts
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map]
  left
  left
  refine ⟨0, ?_, rfl⟩
  rw [List.mem_range]
  exact Nat.div_pos hV (by norm_num)

lemma sweepCut_card_le_half (G : SimpleGraph α) (x : α → ℝ) :
    ∀ S ∈ sweepCuts G x, 2 * S.card ≤ (V(G)).card := by
  intro S hS
  unfold sweepCuts at hS
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_range,
    Finset.mem_filter, Finset.mem_powerset] at hS
  rcases hS with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hLevels
  · have h_card :
        ((List.take (k + 1) ((V(G)).toList.mergeSort
          (fun u v => x u ≤ x v))).toFinset).card ≤ k + 1 := by
      calc
        ((List.take (k + 1) ((V(G)).toList.mergeSort
          (fun u v => x u ≤ x v))).toFinset).card
            ≤ (List.take (k + 1) ((V(G)).toList.mergeSort
                (fun u v => x u ≤ x v))).length := by
              exact List.toFinset_card_le _
        _ ≤ k + 1 := by simp
    have hk' : k + 1 ≤ (V(G)).card / 2 := by omega
    omega
  · have h_card :
        ((List.take (k + 1) ((V(G)).toList.mergeSort
          (fun u v => x u ≤ x v)).reverse).toFinset).card ≤ k + 1 := by
      calc
        ((List.take (k + 1) ((V(G)).toList.mergeSort
          (fun u v => x u ≤ x v)).reverse).toFinset).card
            ≤ (List.take (k + 1) ((V(G)).toList.mergeSort
                (fun u v => x u ≤ x v)).reverse).length := by
              exact List.toFinset_card_le _
        _ ≤ k + 1 := by simp
    have hk' : k + 1 ≤ (V(G)).card / 2 := by omega
    omega
  · rcases hLevels with hLower | hUpper
    · exact hLower.2.2.1
    · exact hUpper.2.2.1

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

lemma fiedlerCut_card_le_half (G : SimpleGraph α) (d : ℕ) (x : α → ℝ)
    (hV : 2 ≤ (V(G)).card) :
    2 * (fiedlerCut G d x hV).card ≤ (V(G)).card := by
  apply sweepCut_card_le_half G x
  exact fiedlerCut_mem_sweep G d x hV

lemma sum_sq_pos (G : SimpleGraph α) (x : α → ℝ)
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

/-- A median value for `x` whose strict upper and lower level sets both have
cardinality at most half of `V(G)`. -/
lemma exists_balanced_median (G : SimpleGraph α) (x : α → ℝ) (hV : 2 ≤ (V(G)).card) :
    ∃ m : ℝ,
      (V(G).filter (fun v => x v > m)).card ≤ (V(G)).card / 2 ∧
      (V(G).filter (fun v => x v < m)).card ≤ (V(G)).card / 2 := by
  classical
  let sortedV := (V(G).toList).mergeSort (fun u v => x u ≤ x v)
  let n := (V(G)).card
  let k := n / 2
  have h_len : sortedV.length = n := by
    simp [sortedV, n]
  have hk_lt : k < sortedV.length := by
    rw [h_len]
    omega
  let m := x (sortedV[k]'hk_lt)
  use m
  have h_sorted : List.Pairwise (fun u v => x u ≤ x v) sortedV := by
    simpa [sortedV] using
      (List.pairwise_mergeSort
        (le := fun u v : α => decide (x u ≤ x v))
        (fun a b c hab hbc => by
          simpa using
            (show decide (x a ≤ x c) = true from
              decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))))
        (fun a b => by
          rcases le_total (x a) (x b) with h | h
          · simp [h]
          · simp [h])
        (V(G).toList))
  have h_nodup : sortedV.Nodup := by
    simpa [sortedV] using (V(G).nodup_toList.mergeSort (le := fun u v => x u ≤ x v))
  have h_mem_sorted_iff : ∀ v, v ∈ sortedV ↔ v ∈ V(G) := by
    intro v
    simp [sortedV]
  constructor
  · let upper := V(G).filter (fun v => x v > m)
    let toTailIndex : α → ℕ := fun v => sortedV.length - 1 - sortedV.idxOf v
    have h_maps : Set.MapsTo toTailIndex upper (Finset.range k) := by
      intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Finset.mem_range]
      have hv_sorted : v ∈ sortedV := (h_mem_sorted_iff v).2 hv.1
      have hidx_lt : sortedV.idxOf v < sortedV.length := List.idxOf_lt_length_iff.2 hv_sorted
      have hget : sortedV[sortedV.idxOf v]'hidx_lt = v := by
        exact List.getElem_idxOf hidx_lt
      have hk_le_not : ¬ sortedV.idxOf v ≤ k := by
        intro hle
        have hx_le : x v ≤ m := by
          have hrel := h_sorted.rel_get_of_le
            (a := ⟨sortedV.idxOf v, hidx_lt⟩) (b := ⟨k, hk_lt⟩)
            (show (⟨sortedV.idxOf v, hidx_lt⟩ : Fin sortedV.length) ≤ ⟨k, hk_lt⟩ from hle)
          simpa [m, hget] using hrel
        linarith
      have hkidx : k < sortedV.idxOf v := Nat.lt_of_not_ge hk_le_not
      rw [h_len] at hidx_lt
      dsimp [toTailIndex]
      rw [h_len]
      omega
    have h_inj : (upper : Set α).InjOn toTailIndex := by
      intro a ha b hb h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_sorted : a ∈ sortedV := (h_mem_sorted_iff a).2 ha.1
      have hb_sorted : b ∈ sortedV := (h_mem_sorted_iff b).2 hb.1
      have hidxa : sortedV.idxOf a < sortedV.length := List.idxOf_lt_length_iff.2 ha_sorted
      have hidxb : sortedV.idxOf b < sortedV.length := List.idxOf_lt_length_iff.2 hb_sorted
      have hidx_eq : sortedV.idxOf a = sortedV.idxOf b := by
        dsimp [toTailIndex] at h_eq
        omega
      exact (List.idxOf_inj ha_sorted).1 hidx_eq
    simpa [upper, k, n] using Finset.card_le_card_of_injOn toTailIndex h_maps h_inj
  · let lower := V(G).filter (fun v => x v < m)
    have h_maps : Set.MapsTo (fun v => sortedV.idxOf v) lower (Finset.range k) := by
      intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Finset.mem_range]
      have hv_sorted : v ∈ sortedV := (h_mem_sorted_iff v).2 hv.1
      have hidx_lt : sortedV.idxOf v < sortedV.length := List.idxOf_lt_length_iff.2 hv_sorted
      have hget : sortedV[sortedV.idxOf v]'hidx_lt = v := by
        exact List.getElem_idxOf hidx_lt
      by_contra hnot
      have hk_le : k ≤ sortedV.idxOf v := Nat.le_of_not_gt hnot
      have hm_le : m ≤ x v := by
        have hrel := h_sorted.rel_get_of_le
          (a := ⟨k, hk_lt⟩) (b := ⟨sortedV.idxOf v, hidx_lt⟩)
          (show (⟨k, hk_lt⟩ : Fin sortedV.length) ≤ ⟨sortedV.idxOf v, hidx_lt⟩ from hk_le)
        simpa [m, hget] using hrel
      linarith
    have h_inj : (lower : Set α).InjOn (fun v => sortedV.idxOf v) := by
      intro a ha b hb h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_sorted : a ∈ sortedV := (h_mem_sorted_iff a).2 ha.1
      have hb_sorted : b ∈ sortedV := (h_mem_sorted_iff b).2 hb.1
      have hidxa : sortedV.idxOf a < sortedV.length := List.idxOf_lt_length_iff.2 ha_sorted
      have hidxb : sortedV.idxOf b < sortedV.length := List.idxOf_lt_length_iff.2 hb_sorted
      exact (List.idxOf_inj ha_sorted).1 h_eq
    simpa [lower, k, n] using
      Finset.card_le_card_of_injOn (fun v => sortedV.idxOf v) h_maps h_inj

/-- Shifting by a balanced median does not increase the Rayleigh quotient for a
degree-regular graph when `x` is degree-orthogonal to constants. -/
lemma median_shift_rayleigh_le (G : SimpleGraph α) (x : α → ℝ) (d : ℕ)
    (m : ℝ) (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    rayleighQuotient G (fun v => x v - m) ≤ rayleighQuotient G x := by
  have h_sum_x : V(G).sum (fun v => x v) = 0 := by
    have h_weight :
        V(G).sum (fun v => (deg(G,v) : ℝ) * x v) =
          (d : ℝ) * V(G).sum (fun v => x v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simp [h_reg v hv]
    rw [h_weight] at h_orth
    have hd_ne : (d : ℝ) ≠ 0 := by
      exact_mod_cast h_d_pos
    exact (mul_eq_zero.mp h_orth).resolve_left hd_ne
  have h_den :
      G.deg_norm x ≤ G.deg_norm (fun v => x v - m) := by
    rw [deg_norm_eq_sum_reg G x d h_reg,
      deg_norm_eq_sum_reg G (fun v => x v - m) d h_reg]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      V(G).sum (fun v => x v ^ 2)
          ≤ V(G).sum (fun v => (x v - m) ^ 2) := by
        simp only [sub_sq]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h_cross : V(G).sum (fun v => 2 * x v * m) = 0 := by
          rw [← Finset.sum_mul]
          rw [← Finset.mul_sum]
          simp [h_sum_x]
        rw [h_cross]
        simp
        positivity
      _ = V(G).sum (fun v => (x v - m) ^ 2) := rfl
  have h_num : G.energy (fun v => x v - m) = G.energy x := by
    unfold energy
    apply Finset.sum_congr rfl
    intro e he
    induction e using Sym2.ind
    case h u v =>
      simp
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm, h_num]
  apply div_le_div_of_nonneg_left
  · exact energy_nonneg G x
  · rw [deg_norm_eq_sum_reg G x d h_reg, ← Finset.mul_sum]
    apply mul_pos
    · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
    · exact sum_sq_pos G x h_x_ne
  · exact h_den

lemma pos_neg_sq_add (a : ℝ) :
    max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by
  by_cases ha : 0 ≤ a
  · simp [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
  · have ha' : a < 0 := lt_of_not_ge ha
    simp [max_eq_right ha'.le, max_eq_left (neg_nonneg.mpr ha'.le)]

lemma pos_neg_sub_sq_add_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤
      (a - b) ^ 2 := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_left ha, max_eq_left hb,
      max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
  · have hb' : b < 0 := lt_of_not_ge hb
    simp [max_eq_left ha, max_eq_right hb'.le,
      max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb'.le)]
    nlinarith [ha, hb']
  · have ha' : a < 0 := lt_of_not_ge ha
    simp [max_eq_right ha'.le, max_eq_left hb,
      max_eq_left (neg_nonneg.mpr ha'.le), max_eq_right (neg_nonpos.mpr hb)]
    nlinarith [ha', hb]
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge hb
    simp [max_eq_right ha'.le, max_eq_right hb'.le,
      max_eq_left (neg_nonneg.mpr ha'.le), max_eq_left (neg_nonneg.mpr hb'.le)]
    nlinarith

lemma deg_norm_shifted_parts_add (G : SimpleGraph α) (z : α → ℝ) :
    G.deg_norm (fun v => max (z v) 0) +
      G.deg_norm (fun v => max (-(z v)) 0) =
        G.deg_norm z := by
  unfold deg_norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← mul_add, pos_neg_sq_add]

lemma energy_shifted_parts_add_le (G : SimpleGraph α) (z : α → ℝ) :
    G.energy (fun v => max (z v) 0) +
      G.energy (fun v => max (-(z v)) 0) ≤
        G.energy z := by
  unfold energy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  induction e using Sym2.ind
  case h u v =>
    dsimp
    exact pos_neg_sub_sq_add_le (z u) (z v)

lemma exists_pos_of_deg_norm_pos (G : SimpleGraph α) (y : α → ℝ)
    (hy_nonneg : ∀ v, 0 ≤ y v) (h_norm_pos : 0 < G.deg_norm y) :
    ∃ v ∈ V(G), 0 < y v := by
  unfold deg_norm at h_norm_pos
  have h_term_nonneg :
      ∀ v ∈ V(G), 0 ≤ (↑(#δ(G,v)) : ℝ) * y v ^ 2 := by
    intro v hv
    exact mul_nonneg (by positivity) (sq_nonneg (y v))
  obtain ⟨v, hv, hv_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg h_term_nonneg).1 h_norm_pos
  have hy_sq_pos : 0 < y v ^ 2 := by
    have hdeg_nonneg : (0 : ℝ) ≤ (#δ(G,v) : ℝ) := by positivity
    nlinarith [hdeg_nonneg, sq_nonneg (y v), hv_pos]
  have hy_ne : y v ≠ 0 := by
    exact sq_pos_iff.mp hy_sq_pos
  exact ⟨v, hv, lt_of_le_of_ne (hy_nonneg v) (Ne.symm hy_ne)⟩

/-- From the positive and negative parts of a shifted vector, choose a nonzero
nonnegative side whose Rayleigh quotient is no larger than that of the shift. -/
lemma shifted_part_rayleigh_le (G : SimpleGraph α) (x : α → ℝ) (m : ℝ)
    (h_shift_norm_pos : 0 < G.deg_norm (fun v => x v - m)) :
    ∃ y : α → ℝ,
      (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
      (∀ v, 0 ≤ y v) ∧
      (∃ v ∈ V(G), 0 < y v) ∧
      rayleighQuotient G y ≤ rayleighQuotient G (fun v => x v - m) := by
  let z : α → ℝ := fun v => x v - m
  let p : α → ℝ := fun v => max (z v) 0
  let n : α → ℝ := fun v => max (-(z v)) 0
  let Ez := G.energy z
  let Ep := G.energy p
  let En := G.energy n
  let Cz := G.deg_norm z
  let Cp := G.deg_norm p
  let Cn := G.deg_norm n
  have hp_nonneg : ∀ v, 0 ≤ p v := by intro v; exact le_max_right _ _
  have hn_nonneg : ∀ v, 0 ≤ n v := by intro v; exact le_max_right _ _
  have hEp_nonneg : 0 ≤ Ep := by exact energy_nonneg G p
  have hEn_nonneg : 0 ≤ En := by exact energy_nonneg G n
  have hCp_nonneg : 0 ≤ Cp := by exact deg_norm_nonneg G p
  have hCn_nonneg : 0 ≤ Cn := by exact deg_norm_nonneg G n
  have hCz_pos : 0 < Cz := by simpa [Cz, z] using h_shift_norm_pos
  have h_norm_add : Cp + Cn = Cz := by
    simpa [Cp, Cn, Cz, p, n] using deg_norm_shifted_parts_add G z
  have h_energy_add : Ep + En ≤ Ez := by
    simpa [Ep, En, Ez, p, n] using energy_shifted_parts_add_le G z
  let Rz := Ez / Cz
  have h_sum_le : Ep + En ≤ Rz * (Cp + Cn) := by
    have h_avg : (Ep + En) / (Cp + Cn) ≤ Ez / Cz := by
      rw [h_norm_add]
      exact div_le_div_of_nonneg_right h_energy_add (le_of_lt hCz_pos)
    have hCpCn_pos : 0 < Cp + Cn := by simpa [h_norm_add] using hCz_pos
    have := (div_le_iff₀ hCpCn_pos).1 h_avg
    simpa [Rz, mul_comm] using this
  have h_choose_p (hCp_pos : 0 < Cp) (hp_le : Ep / Cp ≤ Rz) :
      ∃ y : α → ℝ,
        (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
        (∀ v, 0 ≤ y v) ∧
        (∃ v ∈ V(G), 0 < y v) ∧
        rayleighQuotient G y ≤ rayleighQuotient G (fun v => x v - m) := by
    refine ⟨p, ?_, hp_nonneg, exists_pos_of_deg_norm_pos G p hp_nonneg hCp_pos, ?_⟩
    · left
      ext v
      simp [p, z]
    · rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
      simpa [Ep, Cp, Ez, Cz, Rz, p, z] using hp_le
  have h_choose_n (hCn_pos : 0 < Cn) (hn_le : En / Cn ≤ Rz) :
      ∃ y : α → ℝ,
        (y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0)) ∧
        (∀ v, 0 ≤ y v) ∧
        (∃ v ∈ V(G), 0 < y v) ∧
        rayleighQuotient G y ≤ rayleighQuotient G (fun v => x v - m) := by
    refine ⟨n, ?_, hn_nonneg, exists_pos_of_deg_norm_pos G n hn_nonneg hCn_pos, ?_⟩
    · right
      ext v
      simp [n, z]
    · rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
      simpa [En, Cn, Ez, Cz, Rz, n, z] using hn_le
  by_cases hCp_pos : 0 < Cp
  · by_cases hp_le : Ep / Cp ≤ Rz
    · exact h_choose_p hCp_pos hp_le
    · have hp_gt : Rz < Ep / Cp := lt_of_not_ge hp_le
      have hCn_pos : 0 < Cn := by
        by_contra hCn_not
        have hCn_zero : Cn = 0 := le_antisymm (le_of_not_gt hCn_not) hCn_nonneg
        have hp_mul : Rz * Cp < Ep := (lt_div_iff₀ hCp_pos).1 hp_gt
        rw [hCn_zero, add_zero] at h_sum_le
        nlinarith [hEn_nonneg, h_sum_le, hp_mul]
      have hn_le : En / Cn ≤ Rz := by
        by_contra hn_not
        have hn_gt : Rz < En / Cn := lt_of_not_ge hn_not
        have hp_mul : Rz * Cp < Ep := by
          exact (lt_div_iff₀ hCp_pos).1 hp_gt
        have hn_mul : Rz * Cn < En := by
          exact (lt_div_iff₀ hCn_pos).1 hn_gt
        nlinarith
      exact h_choose_n hCn_pos hn_le
  · have hCp_zero : Cp = 0 := le_antisymm (le_of_not_gt hCp_pos) hCp_nonneg
    have hCn_pos : 0 < Cn := by nlinarith [h_norm_add, hCz_pos]
    have hn_le : En / Cn ≤ Rz := by
      have hEn_le : En ≤ Rz * Cn := by nlinarith
      rw [div_le_iff₀ hCn_pos]
      nlinarith
    exact h_choose_n hCn_pos hn_le

/-- A chosen positive or negative shifted part inherits the median support bound. -/
lemma shifted_part_support_le_half (G : SimpleGraph α) (x : α → ℝ) (m : ℝ)
    (y : α → ℝ)
    (hy_side : y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0))
    (h_upper : (V(G).filter (fun v => x v > m)).card ≤ (V(G)).card / 2)
    (h_lower : (V(G).filter (fun v => x v < m)).card ≤ (V(G)).card / 2) :
    2 * (V(G).filter (fun v => y v > 0)).card ≤ (V(G)).card := by
  rcases hy_side with rfl | rfl
  · have h_set :
        V(G).filter (fun v => max (x v - m) 0 > 0) =
          V(G).filter (fun v => x v > m) := by
      ext v
      constructor <;> intro hv
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by simpa [sub_pos] using hv.2⟩
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by simpa [sub_pos] using hv.2⟩
    rw [h_set]
    omega
  · have h_set :
        V(G).filter (fun v => max (m - x v) 0 > 0) =
          V(G).filter (fun v => x v < m) := by
      ext v
      constructor <;> intro hv
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by simpa [sub_pos] using hv.2⟩
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by simpa [sub_pos] using hv.2⟩
    rw [h_set]
    omega

/-- Nonempty level sets of a chosen shifted part are bounded prefix/suffix sweep cuts. -/
lemma shifted_part_level_mem_sweepCuts (G : SimpleGraph α) (x : α → ℝ) (m : ℝ)
    (y : α → ℝ)
    (hy_side : y = (fun v => max (x v - m) 0) ∨ y = (fun v => max (m - x v) 0))
    (h_support : 2 * (V(G).filter (fun v => y v > 0)).card ≤ (V(G)).card) :
    ∀ t > 0, ({v ∈ V(G) | y v ≥ t} : Finset α).Nonempty →
      {v ∈ V(G) | y v ≥ t} ∈ sweepCuts G x := by
  intro t ht h_nonempty
  have hmax_ge_iff : ∀ a : ℝ, t ≤ max a 0 ↔ t ≤ a := by
    intro a
    constructor
    · intro h
      by_contra hnot
      have ha_lt : a < t := lt_of_not_ge hnot
      have hmax_lt : max a 0 < t := max_lt ha_lt ht
      linarith
    · intro h
      exact h.trans (le_max_left a 0)
  have h_card :
      2 * ({v ∈ V(G) | y v ≥ t} : Finset α).card ≤ (V(G)).card := by
    have h_subset :
        ({v ∈ V(G) | y v ≥ t} : Finset α) ⊆
          V(G).filter (fun v => y v > 0) := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, lt_of_lt_of_le ht hv.2⟩
    have h_card_le :
        ({v ∈ V(G) | y v ≥ t} : Finset α).card ≤
          (V(G).filter (fun v => y v > 0)).card :=
      Finset.card_le_card h_subset
    omega
  rcases hy_side with rfl | rfl
  · have h_level :
        ({v ∈ V(G) | max (x v - m) 0 ≥ t} : Finset α) =
          V(G).filter (fun v => x v ≥ m + t) := by
      ext v
      constructor <;> intro hv
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by
          have ht_le : t ≤ x v - m := (hmax_ge_iff (x v - m)).1 hv.2
          linarith⟩
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by
          have ht_le : t ≤ x v - m := by linarith
          exact (hmax_ge_iff (x v - m)).2 ht_le⟩
    unfold sweepCuts
    simp only [Finset.mem_union]
    right
    right
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by
      intro v hv
      exact (Finset.mem_filter.mp hv).1, h_nonempty, h_card, ⟨m + t, h_level⟩⟩
  · have h_level :
        ({v ∈ V(G) | max (m - x v) 0 ≥ t} : Finset α) =
          V(G).filter (fun v => x v ≤ m - t) := by
      ext v
      constructor <;> intro hv
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by
          have ht_le : t ≤ m - x v := (hmax_ge_iff (m - x v)).1 hv.2
          linarith⟩
      · rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, by
          have ht_le : t ≤ m - x v := by linarith
          exact (hmax_ge_iff (m - x v)).2 ht_le⟩
    unfold sweepCuts
    simp only [Finset.mem_union]
    right
    left
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by
      intro v hv
      exact (Finset.mem_filter.mp hv).1, h_nonempty, h_card, ⟨m - t, h_level⟩⟩

/-- Package the median split into exactly the witness needed by `lemma_5`. -/
lemma exists_median_split_witness (G : SimpleGraph α) (x : α → ℝ) (d : ℕ)
    (hV : 2 ≤ (V(G)).card)
    (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    ∃ y : α → ℝ,
      (∀ v, 0 ≤ y v) ∧
      (∃ v ∈ V(G), 0 < y v) ∧
      (2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) ∧
      rayleighQuotient G y ≤ rayleighQuotient G x ∧
      (∀ t > 0, ({v ∈ V(G) | y v ≥ t} : Finset α).Nonempty →
        {v ∈ V(G) | y v ≥ t} ∈ sweepCuts G x) := by
  obtain ⟨m, h_upper, h_lower⟩ := exists_balanced_median G x hV
  have h_shift_ne : ∃ v ∈ V(G), x v - m ≠ 0 := by
    by_contra h_no
    push_neg at h_no
    have h_x_const : ∀ v ∈ V(G), x v = m := by
      intro v hv
      specialize h_no v hv
      linarith
    have h_sum_weight :
        V(G).sum (fun v => (deg(G,v) : ℝ) * x v) =
          V(G).sum (fun _ => (d : ℝ) * m) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [h_x_const v hv]
      simp [h_reg v hv]
    have h_dm_zero : (d : ℝ) * m * (V(G).card : ℝ) = 0 := by
      rw [h_sum_weight] at h_orth
      rw [Finset.sum_const] at h_orth
      simp only [nsmul_eq_mul] at h_orth
      linarith
    have hd_pos : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero h_d_pos
    have hV_pos : (0 : ℝ) < (V(G).card : ℝ) := by
      exact_mod_cast (by omega : 0 < V(G).card)
    have hm_zero : m = 0 := by
      have hV_ne : ((V(G).card : ℝ) ≠ 0) := ne_of_gt hV_pos
      have hd_ne : ((d : ℝ) ≠ 0) := ne_of_gt hd_pos
      rcases mul_eq_zero.mp h_dm_zero with hdm | hcard
      · rcases mul_eq_zero.mp hdm with hd_zero | hm_zero
        · exact (hd_ne hd_zero).elim
        · exact hm_zero
      · exact (hV_ne hcard).elim
    rcases h_x_ne with ⟨v, hv, hxv⟩
    exact hxv (by rw [h_x_const v hv, hm_zero])
  obtain ⟨y, hy_side, hy_nonneg, hy_pos, hy_ray_shift⟩ :=
    shifted_part_rayleigh_le G x m (by
      rw [deg_norm_eq_sum_reg G (fun v => x v - m) d h_reg, ← Finset.mul_sum]
      apply mul_pos
      · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
      · exact sum_sq_pos G (fun v => x v - m) h_shift_ne)
  have hy_support :
      2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card :=
    shifted_part_support_le_half G x m y hy_side h_upper h_lower
  have hy_ray_x : rayleighQuotient G y ≤ rayleighQuotient G x :=
    hy_ray_shift.trans (median_shift_rayleigh_le G x d m h_d_pos h_x_ne h_orth h_reg)
  exact ⟨y, hy_nonneg, hy_pos, hy_support, hy_ray_x,
    shifted_part_level_mem_sweepCuts G x m y hy_side hy_support⟩

/-- Median-splitting lemma used by the sweep proof.
It produces a nonzero nonnegative vector with small support, no larger Rayleigh quotient,
and level sets that are valid sweep cuts of `x`. -/
lemma lemma_5 (G : SimpleGraph α) (x : α → ℝ) (d : ℕ) (hV : 2 ≤ (V(G)).card)
    (h_d_pos : d ≠ 0) (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    ∃ y : α → ℝ,
      (∀ v, 0 ≤ y v) ∧
      (∃ v ∈ V(G), 0 < y v) ∧
      (2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) ∧
      rayleighQuotient G y ≤ rayleighQuotient G x ∧
      (∀ t > 0, ({v ∈ V(G) | y v ≥ t} : Finset α).Nonempty →
        {v ∈ V(G) | y v ≥ t} ∈ sweepCuts G x) := by
  exact exists_median_split_witness G x d hV h_d_pos h_x_ne h_orth h_reg

/-- Lemma 4: For a non-negative vector y, there exists a threshold t such that
    the expansion of the set S_t = {v : y_v ≥ t} is at most sqrt(2 * R_L(y)). -/
lemma exists_ratio_le_of_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (R : ℝ)
    (hs : s.Nonempty)
    (hb_pos : ∀ i ∈ s, 0 < b i)
    (h_sum : ∑ i ∈ s, a i ≤ R * ∑ i ∈ s, b i) :
    ∃ i ∈ s, 0 < b i ∧ a i / b i ≤ R := by
  by_contra h_no
  push Not at h_no
  have h_each_gt : ∀ i ∈ s, R * b i < a i := by
    intro i hi
    have hratio_not := h_no i hi (hb_pos i hi)
    have hratio_gt : R < a i / b i := hratio_not
    exact (lt_div_iff₀ (hb_pos i hi)).1 hratio_gt
  have h_total_gt : R * ∑ i ∈ s, b i < ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hs h_each_gt
  nlinarith

lemma sum_le_sqrt_mul_sqrt_of_le_mul {ι : Type*} (s : Finset ι)
    (w A B : ι → ℝ)
    (hw_le : ∀ i ∈ s, w i ≤ A i * B i) :
    ∑ i ∈ s, w i ≤
      Real.sqrt (∑ i ∈ s, A i ^ 2) * Real.sqrt (∑ i ∈ s, B i ^ 2) := by
  calc
    ∑ i ∈ s, w i
        ≤ ∑ i ∈ s, A i * B i := Finset.sum_le_sum hw_le
    _ ≤ Real.sqrt (∑ i ∈ s, A i ^ 2) * Real.sqrt (∑ i ∈ s, B i ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt s A B

lemma abs_sq_sub_sq_le_abs_sub_mul_add_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ 2 - b ^ 2| ≤ |a - b| * (a + b) := by
  have hab_nonneg : 0 ≤ a + b := add_nonneg ha hb
  calc
    |a ^ 2 - b ^ 2| = |(a - b) * (a + b)| := by ring_nf
    _ = |a - b| * |a + b| := abs_mul _ _
    _ ≤ |a - b| * (a + b) := by rw [abs_of_nonneg hab_nonneg]

lemma positive_value_levels_nonempty (G : SimpleGraph α) (y : α → ℝ)
    (h_y_pos : ∃ v ∈ V(G), 0 < y v) :
    ((V(G).image y).filter (fun t => 0 < t)).Nonempty := by
  rcases h_y_pos with ⟨v, hv, hv_pos⟩
  exact ⟨y v, by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hv_pos⟩⟩

lemma positive_value_level_pos (G : SimpleGraph α) (y : α → ℝ) :
    ∀ t ∈ (V(G).image y).filter (fun t => 0 < t), 0 < t := by
  intro t ht
  exact (Finset.mem_filter.mp ht).2

lemma positive_value_level_set_nonempty (G : SimpleGraph α) (y : α → ℝ) :
    ∀ t ∈ (V(G).image y).filter (fun t => 0 < t),
      (V(G).filter (fun v => y v ≥ t)).Nonempty := by
  intro t ht
  rcases Finset.mem_image.mp (Finset.mem_filter.mp ht).1 with ⟨v, hv, rfl⟩
  exact ⟨v, by simp [hv]⟩

lemma positive_value_level_mem_image {G : SimpleGraph α} {y : α → ℝ} {t : ℝ}
    (ht : t ∈ (V(G).image y).filter (fun t => 0 < t)) :
    t ∈ V(G).image y := (Finset.mem_filter.mp ht).1

noncomputable def previousLevel (levels : Finset ℝ) (t : ℝ) : ℝ :=
  if h : (levels.filter (fun s => s < t)).Nonempty then
    (levels.filter (fun s => s < t)).max' h
  else 0

noncomputable def coareaWeight (levels : Finset ℝ) (t : ℝ) : ℝ :=
  t ^ 2 - (previousLevel levels t) ^ 2

lemma previousLevel_lt_of_pos_mem {levels : Finset ℝ} {t : ℝ}
    (ht_pos : 0 < t) :
    previousLevel levels t < t := by
  unfold previousLevel
  by_cases h : (levels.filter (fun s => s < t)).Nonempty
  · rw [dif_pos h]
    exact (Finset.max'_lt_iff (levels.filter (fun s => s < t)) h).mpr (by
      intro s hs
      exact (Finset.mem_filter.mp hs).2)
  · rw [dif_neg h]
    exact ht_pos

lemma previousLevel_nonneg_of_positive_levels {levels : Finset ℝ} {t : ℝ}
    (hlevels_pos : ∀ s ∈ levels, 0 < s) :
    0 ≤ previousLevel levels t := by
  unfold previousLevel
  by_cases h : (levels.filter (fun s => s < t)).Nonempty
  · rw [dif_pos h]
    have hmem : (levels.filter (fun s => s < t)).max' h ∈
        levels.filter (fun s => s < t) := Finset.max'_mem _ _
    exact le_of_lt (hlevels_pos _ (Finset.mem_filter.mp hmem).1)
  · rw [dif_neg h]

lemma coareaWeight_pos_of_pos_mem {levels : Finset ℝ} {t : ℝ}
    (hlevels_pos : ∀ s ∈ levels, 0 < s)
    (ht_pos : 0 < t) :
    0 < coareaWeight levels t := by
  unfold coareaWeight
  have hpred_nonneg : 0 ≤ previousLevel levels t :=
    previousLevel_nonneg_of_positive_levels hlevels_pos
  have hpred_lt : previousLevel levels t < t :=
    previousLevel_lt_of_pos_mem ht_pos
  have hsq_lt : (previousLevel levels t) ^ 2 < t ^ 2 := by
    nlinarith
  nlinarith

lemma previousLevel_insert_of_lt {levels : Finset ℝ} {a t : ℝ}
    (ht_lt_a : t < a) :
    previousLevel (insert a levels) t = previousLevel levels t := by
  unfold previousLevel
  have hfilter :
      (insert a levels).filter (fun s => s < t) = levels.filter (fun s => s < t) := by
    ext s
    by_cases hsa : s = a
    · subst hsa
      simp [not_lt_of_ge (le_of_lt ht_lt_a)]
    · simp [hsa]
  rw [hfilter]

lemma previousLevel_insert_top {levels : Finset ℝ} {a : ℝ}
    (h_all_lt : ∀ s ∈ levels, s < a) :
    previousLevel (insert a levels) a = if h : levels.Nonempty then levels.max' h else 0 := by
  unfold previousLevel
  have hfilter : (insert a levels).filter (fun s => s < a) = levels := by
    ext s
    by_cases hsa : s = a
    · subst hsa
      simp only [Finset.mem_filter, Finset.mem_insert, lt_self_iff_false, and_false, false_iff]
      intro ha
      exact (lt_irrefl _) (h_all_lt _ ha)
    · constructor
      · intro hs
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp hs).1 with rfl | hs_mem
        · exact (hsa rfl).elim
        · exact hs_mem
      · intro hs
        exact Finset.mem_filter.mpr ⟨by simp [hs], h_all_lt s hs⟩
  rw [hfilter]

lemma sum_coareaWeight_eq_max_sq_or_zero (levels : Finset ℝ) :
    ∑ t ∈ levels, coareaWeight levels t =
      if h : levels.Nonempty then (levels.max' h) ^ 2 else 0 := by
  classical
  refine Finset.induction_on_max levels ?_ ?_
  · simp
  · intro a s h_all_lt ih
    have ha_not_mem : a ∉ s := by
      intro ha
      exact (lt_irrefl a) (h_all_lt a ha)
    rw [Finset.sum_insert ha_not_mem]
    have h_weight_a :
        coareaWeight (insert a s) a =
          a ^ 2 - (if h : s.Nonempty then (s.max' h) ^ 2 else 0) := by
      unfold coareaWeight
      rw [previousLevel_insert_top h_all_lt]
      by_cases hs : s.Nonempty
      · simp [hs]
      · simp [hs]
    have h_sum_s :
        ∑ x ∈ s, coareaWeight (insert a s) x = ∑ x ∈ s, coareaWeight s x := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold coareaWeight
      rw [previousLevel_insert_of_lt (h_all_lt x hx)]
    rw [h_sum_s, ih, h_weight_a]
    have h_insert_ne : (insert a s).Nonempty := Finset.insert_nonempty a s
    have h_max_insert : (insert a s).max' h_insert_ne = a := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact le_rfl
          · exact le_of_lt (h_all_lt x hx))
      · exact Finset.le_max' _ a (by simp)
    rw [dif_pos h_insert_ne, h_max_insert]
    by_cases hs : s.Nonempty
    · rw [dif_pos hs]
      ring
    · rw [dif_neg hs]
      ring

lemma sum_coareaWeight_le_value_sq {levels : Finset ℝ} {a : ℝ}
    (ha_nonneg : 0 ≤ a) :
    ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight (levels.filter (fun t => t ≤ a)) t =
      if h : (levels.filter (fun t => t ≤ a)).Nonempty then
        ((levels.filter (fun t => t ≤ a)).max' h) ^ 2
      else 0 := by
  exact sum_coareaWeight_eq_max_sq_or_zero _

lemma previousLevel_filter_le_eq {levels : Finset ℝ} {a t : ℝ}
    (ht_le : t ≤ a) :
    previousLevel (levels.filter (fun s => s ≤ a)) t = previousLevel levels t := by
  unfold previousLevel
  have hfilter :
      ((levels.filter (fun s => s ≤ a)).filter (fun s => s < t)) =
        levels.filter (fun s => s < t) := by
    ext s
    constructor
    · intro hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1,
        (Finset.mem_filter.mp hs).2⟩
    · intro hs
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hs).1, le_trans (le_of_lt (Finset.mem_filter.mp hs).2) ht_le⟩,
        (Finset.mem_filter.mp hs).2⟩
  rw [hfilter]

lemma coareaWeight_filter_le_eq {levels : Finset ℝ} {a t : ℝ}
    (ht_le : t ≤ a) :
    coareaWeight (levels.filter (fun s => s ≤ a)) t = coareaWeight levels t := by
  unfold coareaWeight
  rw [previousLevel_filter_le_eq ht_le]

lemma sum_coareaWeight_initial_segment_eq_max_sq {levels : Finset ℝ} {a : ℝ}
    (ha_mem : a ∈ levels) :
    ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight levels t = a ^ 2 := by
  classical
  have hsum_filter :
      ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight levels t =
        ∑ t ∈ levels.filter (fun t => t ≤ a),
          coareaWeight (levels.filter (fun s => s ≤ a)) t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [coareaWeight_filter_le_eq (Finset.mem_filter.mp ht).2]
  rw [hsum_filter, sum_coareaWeight_eq_max_sq_or_zero]
  have hne : (levels.filter (fun t => t ≤ a)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha_mem, le_rfl⟩⟩
  have hmax : (levels.filter (fun t => t ≤ a)).max' hne = a := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (by
        intro t ht
        exact (Finset.mem_filter.mp ht).2)
    · exact Finset.le_max' (levels.filter (fun t => t ≤ a)) a
        (Finset.mem_filter.mpr ⟨ha_mem, le_rfl⟩)
  rw [dif_pos hne, hmax]

lemma sum_coareaWeight_initial_segment_eq_value_sq (G : SimpleGraph α) (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) (v : α) (hv : v ∈ V(G)) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t = y v ^ 2 := by
  classical
  intro levels
  by_cases hv_pos : 0 < y v
  · have hy_mem : y v ∈ levels := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hv_pos⟩
    exact sum_coareaWeight_initial_segment_eq_max_sq hy_mem
  · have hy_zero : y v = 0 := by
      have hy_nonneg := h_pos v
      linarith
    have hfilter_empty : levels.filter (fun t => t ≤ 0) = ∅ := by
      ext t
      simp [levels]
    rw [hy_zero]
    simp [hfilter_empty]

lemma sum_coareaWeight_between_vertex_values_eq_sq_sub
    (G : SimpleGraph α) (y : α → ℝ) (h_pos : ∀ v, 0 ≤ y v)
    {u v : α} (huV : u ∈ V(G)) (hvV : v ∈ V(G))
    (huv : y u ≤ y v) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
        coareaWeight levels t = y v ^ 2 - y u ^ 2 := by
  classical
  intro levels
  have hv_sum :=
    sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hvV
  have hu_sum :=
    sum_coareaWeight_initial_segment_eq_value_sq G y h_pos u huV
  dsimp [levels] at hv_sum hu_sum
  have hsplit :
      ∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t =
        ∑ t ∈ levels.filter (fun t => t ≤ y u), coareaWeight levels t +
          ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
            coareaWeight levels t := by
    have hpartition :
        levels.filter (fun t => t ≤ y v) =
          (levels.filter (fun t => t ≤ y u)) ∪
            (levels.filter (fun t => y u < t ∧ t ≤ y v)) := by
      ext t
      by_cases hleu : t ≤ y u
      · simp [hleu, le_trans hleu huv]
      · have hltu : y u < t := lt_of_not_ge hleu
        simp [hleu, hltu]
    have hdisjoint :
        Disjoint (levels.filter (fun t => t ≤ y u))
          (levels.filter (fun t => y u < t ∧ t ≤ y v)) := by
      rw [Finset.disjoint_left]
      intro t ht_left ht_right
      have hleu : t ≤ y u := (Finset.mem_filter.mp ht_left).2
      have hltu : y u < t := (Finset.mem_filter.mp ht_right).2.1
      linarith
    rw [hpartition, Finset.sum_union hdisjoint]
  linarith

lemma regular_level_volume_as_vertex_sum (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (t : ℝ) :
    (((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ)) =
      ∑ v ∈ V(G), if t ≤ y v then (d : ℝ) else 0 := by
  calc
    (((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ))
        = (d : ℝ) * ((V(G).filter (fun v => y v ≥ t)).card : ℝ) := by
          norm_num [Nat.cast_mul]
    _ = (d : ℝ) * ∑ v ∈ V(G).filter (fun v => y v ≥ t), (1 : ℝ) := by
          rw [Finset.card_eq_sum_ones]
          norm_num
    _ = ∑ v ∈ V(G).filter (fun v => y v ≥ t), (d : ℝ) := by
          rw [Finset.mul_sum]
          simp
    _ = ∑ v ∈ V(G), if t ≤ y v then (d : ℝ) else 0 := by
          rw [Finset.sum_filter]

lemma cut_card_eq_edge_indicator_sum (G : SimpleGraph α) (U : Finset α) :
    ((Cut G U).card : ℝ) =
      ∑ e ∈ E(G), if e ∈ Cut G U then (1 : ℝ) else 0 := by
  have hfilter : {e ∈ E(G) | e ∈ Cut G U} = Cut G U := by
    ext e
    simp [Cut]
  calc
    ((Cut G U).card : ℝ) = ∑ e ∈ Cut G U, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]
      norm_num
    _ = ∑ e ∈ E(G), if e ∈ Cut G U then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter, hfilter]

lemma edge_mem_level_cut_of_ge_lt (G : SimpleGraph α) (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ E(G))
    (hu : t ≤ y u) (hv : y v < t) :
    s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) := by
  have huV : u ∈ V(G) := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ V(G) := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  rw [Cut, Finset.mem_filter]
  refine ⟨he, ?_⟩
  refine ⟨u, ?_, Sym2.mem_mk_left u v, v, ?_, Sym2.mem_mk_right u v⟩
  · exact Finset.mem_filter.mpr ⟨huV, hu⟩
  · exact Finset.mem_sdiff.mpr ⟨hvV, by
      intro hv_mem
      have hv_ge : t ≤ y v := (Finset.mem_filter.mp hv_mem).2
      linarith⟩

lemma edge_mem_level_cut_of_lt_ge (G : SimpleGraph α) (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ E(G))
    (hu : y u < t) (hv : t ≤ y v) :
    s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) := by
  have hcut :
      s(v, u) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) :=
    edge_mem_level_cut_of_ge_lt G y (SimpleGraph.edgeSet_sym G u v he) hv hu
  simpa [Sym2.eq_swap] using hcut

lemma level_cut_edge_between_endpoints (G : SimpleGraph α) (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ E(G))
    (hcut : s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))) :
    (t ≤ y u ∧ y v < t) ∨ (t ≤ y v ∧ y u < t) := by
  rw [Cut, Finset.mem_filter] at hcut
  rcases hcut.2 with ⟨a, haU, ha_edge, b, hbNot, hb_edge⟩
  have ha_cases : a = u ∨ a = v := Sym2.mem_iff.mp ha_edge
  have hb_cases : b = u ∨ b = v := Sym2.mem_iff.mp hb_edge
  have ha_ge : t ≤ y a := (Finset.mem_filter.mp haU).2
  have hb_lt : y b < t := by
    have hb_not_mem : b ∉ V(G).filter (fun w => y w ≥ t) :=
      (Finset.mem_sdiff.mp hbNot).2
    by_contra hnot
    have hb_ge : t ≤ y b := le_of_not_gt hnot
    have hbV : b ∈ V(G) := (Finset.mem_sdiff.mp hbNot).1
    exact hb_not_mem (Finset.mem_filter.mpr ⟨hbV, hb_ge⟩)
  rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl
  · linarith
  · exact Or.inl ⟨ha_ge, hb_lt⟩
  · exact Or.inr ⟨ha_ge, hb_lt⟩
  · linarith

lemma edge_level_cut_weight_sum_le_abs_sq_sub (G : SimpleGraph α) (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) {u v : α} (he : s(u, v) ∈ E(G)) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (if s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
      ≤ |y u ^ 2 - y v ^ 2| := by
  classical
  intro levels
  have huV : u ∈ V(G) := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ V(G) := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  have hleft :
      ∑ t ∈ levels,
          coareaWeight levels t *
            (if s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
        =
      ∑ t ∈ levels.filter
          (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))),
        coareaWeight levels t := by
    calc
      ∑ t ∈ levels,
          coareaWeight levels t *
            (if s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
          = ∑ t ∈ levels,
              if s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) then
                coareaWeight levels t else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases hcut : s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))
            · simp [hcut]
            · simp [hcut]
      _ = ∑ t ∈ levels.filter
              (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))),
            coareaWeight levels t := by
            rw [← Finset.sum_filter]
  rw [hleft]
  by_cases huv : y u ≤ y v
  · have hsubset :
        levels.filter
            (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))) ⊆
          levels.filter (fun t => y u < t ∧ t ≤ y v) := by
      intro t ht
      have ht_levels : t ∈ levels := (Finset.mem_filter.mp ht).1
      have hcut : s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) :=
        (Finset.mem_filter.mp ht).2
      rcases level_cut_edge_between_endpoints G y he hcut with hbad | hgood
      · linarith
      · exact Finset.mem_filter.mpr ⟨ht_levels, hgood.symm⟩
    have hle_sum :
        ∑ t ∈ levels.filter
            (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))),
          coareaWeight levels t ≤
        ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
          coareaWeight levels t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t ht_big ht_not_small
      have ht_level : t ∈ levels := (Finset.mem_filter.mp ht_big).1
      exact le_of_lt (coareaWeight_pos_of_pos_mem
        (positive_value_level_pos G y) ((Finset.mem_filter.mp ht_level).2))
    have hinterval :=
      sum_coareaWeight_between_vertex_values_eq_sq_sub G y h_pos huV hvV huv
    dsimp [levels] at hinterval
    rw [hinterval] at hle_sum
    have habs : |y u ^ 2 - y v ^ 2| = y v ^ 2 - y u ^ 2 := by
      rw [abs_of_nonpos (show y u ^ 2 - y v ^ 2 ≤ 0 by
        have hsq : y u ^ 2 ≤ y v ^ 2 := by
          have hmul : y u * y u ≤ y v * y v :=
            mul_le_mul huv huv (h_pos u) (h_pos v)
          nlinarith
        linarith)]
      ring
    rw [habs]
    exact hle_sum
  · have hvu : y v ≤ y u := le_of_not_ge huv
    have hsubset :
        levels.filter
            (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))) ⊆
          levels.filter (fun t => y v < t ∧ t ≤ y u) := by
      intro t ht
      have ht_levels : t ∈ levels := (Finset.mem_filter.mp ht).1
      have hcut : s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t)) :=
        (Finset.mem_filter.mp ht).2
      rcases level_cut_edge_between_endpoints G y he hcut with hgood | hbad
      · exact Finset.mem_filter.mpr ⟨ht_levels, hgood.symm⟩
      · linarith
    have hle_sum :
        ∑ t ∈ levels.filter
            (fun t => s(u, v) ∈ Cut G (V(G).filter (fun w => y w ≥ t))),
          coareaWeight levels t ≤
        ∑ t ∈ levels.filter (fun t => y v < t ∧ t ≤ y u),
          coareaWeight levels t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t ht_big ht_not_small
      have ht_level : t ∈ levels := (Finset.mem_filter.mp ht_big).1
      exact le_of_lt (coareaWeight_pos_of_pos_mem
        (positive_value_level_pos G y) ((Finset.mem_filter.mp ht_level).2))
    have hinterval :=
      sum_coareaWeight_between_vertex_values_eq_sq_sub G y h_pos hvV huV hvu
    dsimp [levels] at hinterval
    rw [hinterval] at hle_sum
    have habs : |y u ^ 2 - y v ^ 2| = y u ^ 2 - y v ^ 2 := by
      rw [abs_of_nonneg (show 0 ≤ y u ^ 2 - y v ^ 2 by
        have hsq : y v ^ 2 ≤ y u ^ 2 := by
          have hmul : y v * y v ≤ y u * y u :=
            mul_le_mul hvu hvu (h_pos v) (h_pos u)
          nlinarith
        exact sub_nonneg.mpr hsq)]
    rw [habs]
    exact hle_sum

noncomputable def edgeAbsSqDiff (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => |y u ^ 2 - y v ^ 2|, by
    intro u v
    dsimp
    rw [abs_sub_comm]
  ⟩

noncomputable def edgeEndpointSqSum (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => y u ^ 2 + y v ^ 2, by
    intro u v
    dsimp
    ring
  ⟩

noncomputable def edgeAbsDiff (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => |y u - y v|, by
    intro u v
    dsimp
    rw [abs_sub_comm]
  ⟩

noncomputable def edgeEndpointSum (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => y u + y v, by
    intro u v
    dsimp
    ring
  ⟩

lemma edge_vertex_indicator_sum_eq_endpoint_sq_sum (G : SimpleGraph α) (y : α → ℝ)
    {u v : α} (he : s(u, v) ∈ E(G)) :
    ∑ x ∈ V(G), (if x ∈ s(u, v) then y x ^ 2 else 0) =
      y u ^ 2 + y v ^ 2 := by
  classical
  have huv_ne : u ≠ v := SimpleGraph.ne_of_mem_edgeSet G u v he
  have huV : u ∈ V(G) := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ V(G) := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  calc
    ∑ x ∈ V(G), (if x ∈ s(u, v) then y x ^ 2 else 0)
        = ∑ x ∈ V(G).filter (fun x => x ∈ s(u, v)), y x ^ 2 := by
          rw [← Finset.sum_filter]
    _ = ∑ x ∈ ({u, v} : Finset α), y x ^ 2 := by
          have hfilter : V(G).filter (fun x => x ∈ s(u, v)) = ({u, v} : Finset α) := by
            ext x
            constructor
            · intro hx
              have hcases : x = u ∨ x = v := Sym2.mem_iff.mp (Finset.mem_filter.mp hx).2
              simpa using hcases
            · intro hx
              have hx_edge : x ∈ s(u, v) := by
                simpa [Sym2.mem_iff] using hx
              have hxV : x ∈ V(G) := by
                rcases Sym2.mem_iff.mp hx_edge with rfl | rfl
                · exact huV
                · exact hvV
              exact Finset.mem_filter.mpr ⟨hxV, hx_edge⟩
          rw [hfilter]
    _ = y u ^ 2 + y v ^ 2 := by
          rw [Finset.sum_pair huv_ne]

lemma edge_endpoint_sq_sum_eq_deg_norm (G : SimpleGraph α) (y : α → ℝ) :
    ∑ e ∈ E(G), edgeEndpointSqSum y e = G.deg_norm y := by
  classical
  calc
    ∑ e ∈ E(G), edgeEndpointSqSum y e
        = ∑ e ∈ E(G), ∑ v ∈ V(G), (if v ∈ e then y v ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          induction e using Sym2.ind
          case h u v =>
            simpa [edgeEndpointSqSum] using
              (edge_vertex_indicator_sum_eq_endpoint_sq_sum G y he).symm
    _ = ∑ v ∈ V(G), ∑ e ∈ E(G), (if v ∈ e then y v ^ 2 else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ v ∈ V(G), ((#δ(G, v) : ℕ) : ℝ) * y v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            ∑ e ∈ E(G), (if v ∈ e then y v ^ 2 else 0)
                = ∑ e ∈ δ(G, v), y v ^ 2 := by
                  rw [← Finset.sum_filter]
            _ = ((#δ(G, v) : ℕ) : ℝ) * y v ^ 2 := by
                  rw [Finset.sum_const]
                  simp [nsmul_eq_mul]
    _ = G.deg_norm y := by
          rfl

lemma level_cut_sum_le_edge_abs_sq_diff_sum (G : SimpleGraph α) (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
      ∑ e ∈ E(G), edgeAbsSqDiff y e := by
  classical
  intro levels
  calc
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (V(G).filter (fun v => y v ≥ t))).card
        = ∑ t ∈ levels,
            coareaWeight levels t *
              (∑ e ∈ E(G),
                if e ∈ Cut G (V(G).filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [cut_card_eq_edge_indicator_sum]
    _ = ∑ t ∈ levels, ∑ e ∈ E(G),
          coareaWeight levels t *
            (if e ∈ Cut G (V(G).filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ e ∈ E(G), ∑ t ∈ levels,
          coareaWeight levels t *
            (if e ∈ Cut G (V(G).filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ E(G), edgeAbsSqDiff y e := by
          apply Finset.sum_le_sum
          intro e he
          induction e using Sym2.ind
          case h u v =>
            simpa [edgeAbsSqDiff, levels] using
              edge_level_cut_weight_sum_le_abs_sq_sub G y h_pos he

lemma edge_abs_diff_sq_sum_eq_energy (G : SimpleGraph α) (y : α → ℝ) :
    ∑ e ∈ E(G), (edgeAbsDiff y e) ^ 2 = G.energy y := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u v =>
    simp [edgeAbsDiff, sq_abs]

lemma edge_endpoint_sum_sq_le_two_deg_norm (G : SimpleGraph α) (y : α → ℝ) :
    ∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2 ≤ 2 * G.deg_norm y := by
  calc
    ∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2
        ≤ ∑ e ∈ E(G), 2 * edgeEndpointSqSum y e := by
          apply Finset.sum_le_sum
          intro e he
          induction e using Sym2.ind
          case h u v =>
            have hsq : (y u + y v) ^ 2 ≤ 2 * (y u ^ 2 + y v ^ 2) := by
              nlinarith [sq_nonneg (y u - y v)]
            simpa [edgeEndpointSum, edgeEndpointSqSum] using hsq
    _ = 2 * G.deg_norm y := by
          rw [← Finset.mul_sum, edge_endpoint_sq_sum_eq_deg_norm]

lemma edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm (G : SimpleGraph α) (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    ∑ e ∈ E(G), edgeAbsSqDiff y e ≤
      Real.sqrt (2 * G.energy y * G.deg_norm y) := by
  have hpoint :
      ∀ e ∈ E(G), edgeAbsSqDiff y e ≤ edgeAbsDiff y e * edgeEndpointSum y e := by
    intro e he
    induction e using Sym2.ind
    case h u v =>
      simpa [edgeAbsSqDiff, edgeAbsDiff, edgeEndpointSum] using
        abs_sq_sub_sq_le_abs_sub_mul_add_of_nonneg (h_pos u) (h_pos v)
  have hcs :=
    sum_le_sqrt_mul_sqrt_of_le_mul (E(G)) (edgeAbsSqDiff y)
      (edgeAbsDiff y) (edgeEndpointSum y) hpoint
  have hA : ∑ e ∈ E(G), (edgeAbsDiff y e) ^ 2 = G.energy y :=
    edge_abs_diff_sq_sum_eq_energy G y
  have hB : ∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2 ≤ 2 * G.deg_norm y :=
    edge_endpoint_sum_sq_le_two_deg_norm G y
  have hB_nonneg : 0 ≤ ∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2 := by
    exact Finset.sum_nonneg (by intro e he; exact sq_nonneg _)
  have hmul_sqrt :
      Real.sqrt (∑ e ∈ E(G), (edgeAbsDiff y e) ^ 2) *
          Real.sqrt (∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2)
        ≤ Real.sqrt (2 * G.energy y * G.deg_norm y) := by
    rw [hA]
    have hB_sqrt :
        Real.sqrt (∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2) ≤
          Real.sqrt (2 * G.deg_norm y) :=
      Real.sqrt_le_sqrt hB
    have henergy_nonneg : 0 ≤ G.energy y := energy_nonneg G y
    have hsqrt_energy_nonneg : 0 ≤ Real.sqrt (G.energy y) := Real.sqrt_nonneg _
    calc
      Real.sqrt (G.energy y) *
          Real.sqrt (∑ e ∈ E(G), (edgeEndpointSum y e) ^ 2)
          ≤ Real.sqrt (G.energy y) * Real.sqrt (2 * G.deg_norm y) := by
            exact mul_le_mul_of_nonneg_left hB_sqrt hsqrt_energy_nonneg
      _ = Real.sqrt (G.energy y * (2 * G.deg_norm y)) := by
            rw [Real.sqrt_mul henergy_nonneg]
      _ = Real.sqrt (2 * G.energy y * G.deg_norm y) := by
            ring_nf
  exact le_trans hcs hmul_sqrt

/-- Vertex-side layer-cake formula for the canonical positive levels of `y`.
With `w t = t^2 - pred(t)^2`, summing the level volumes recovers the
degree norm. -/
lemma level_coarea_volume_identity (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
      G.deg_norm y := by
  classical
  intro levels
  calc
    ∑ t ∈ levels,
        coareaWeight levels t *
          ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ)
        = ∑ t ∈ levels,
            coareaWeight levels t *
              (∑ v ∈ V(G), if t ≤ y v then (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [regular_level_volume_as_vertex_sum]
    _ = ∑ t ∈ levels, ∑ v ∈ V(G),
            coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ v ∈ V(G), ∑ t ∈ levels,
            coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ v ∈ V(G), (d : ℝ) * y v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          have hpoint :=
            sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hv
          dsimp [levels] at hpoint
          calc
            ∑ t ∈ levels, coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0)
                = ∑ t ∈ levels, if t ≤ y v then coareaWeight levels t * (d : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  by_cases hle : t ≤ y v
                  · simp [hle]
                  · simp [hle]
            _ = ∑ t ∈ levels.filter (fun t => t ≤ y v),
                    coareaWeight levels t * (d : ℝ) := by
                  rw [← Finset.sum_filter]
            _ = (∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t) * (d : ℝ) := by
                  rw [Finset.sum_mul]
            _ = (d : ℝ) * y v ^ 2 := by
                  rw [hpoint]
                  ring
    _ = G.deg_norm y := by
          rw [deg_norm_eq_sum_reg G y d h_reg]

/-- Edge-side coarea estimate for the canonical positive levels of `y`.
The weighted count of threshold cuts is bounded by the Cauchy-Schwarz
quantity `sqrt (2 * energy * deg_norm)`. -/
lemma level_coarea_cut_bound (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (V(G).image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
      Real.sqrt (2 * G.energy y * G.deg_norm y) := by
  intro levels
  exact
    (level_cut_sum_le_edge_abs_sq_diff_sum G y h_pos).trans
      (edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm G y h_pos)

noncomputable def normalizedSupportedOrthogonal (G : SimpleGraph α) : Set (α → ℝ) :=
  {x | (∀ v, v ∉ V(G) → x v = 0) ∧
    x ∈ orthogonalVectors G ∧
    G.deg_norm x = 1}

lemma edgeSet_empty_of_regular_zero (G : SimpleGraph α)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = 0) :
    E(G) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind
  case h u v =>
    have huV : u ∈ V(G) := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
    have hinc : s(u, v) ∈ δ(G,u) := by
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_left u v⟩
    have hcard_pos : 0 < #δ(G,u) := Finset.card_pos.mpr ⟨s(u, v), hinc⟩
    have hzero : #δ(G,u) = 0 := h_reg u huV
    omega

lemma R_values_eq_singleton_zero_of_regular_zero (G : SimpleGraph α) [Finite α]
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = 0) (hV : 2 ≤ #V(G)) :
    R_values G = {0} := by
  classical
  have hE : E(G) = ∅ := edgeSet_empty_of_regular_zero G h_reg
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hx, rfl⟩
    simp [rayleighQuotient, hE]
  · intro hr
    simp only [Set.mem_singleton_iff] at hr
    subst r
    have hcard : 1 < (V(G)).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    let x : α → ℝ := fun v => if v = a then (1 : ℝ) else if v = b then (-1 : ℝ) else 0
    refine ⟨x, ?_, ?_⟩
    · constructor
      · rw [show V(G).sum (fun v => (deg(G,v) : ℝ) * x v) =
            ∑ v ∈ V(G), (0 : ℝ) * x v by
          apply Finset.sum_congr rfl
          intro v hv
          rw [h_reg v hv]
          norm_num]
        simp
      · exact ⟨a, ha, by simp [x]⟩
    · simp [rayleighQuotient, hE]

lemma deg_norm_pos_of_supported_orthogonal_of_regular_pos (G : SimpleGraph α) (d : ℕ)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    {x : α → ℝ} (hx : x ∈ orthogonalVectors G) :
    0 < G.deg_norm (restrictToVertexSet G x) := by
  classical
  have hy : restrictToVertexSet G x ∈ orthogonalVectors G :=
    orthogonalVectors_restrictToVertexSet G x hx
  rcases hy with ⟨_, hy_ne⟩
  rw [deg_norm_eq_sum_reg G (restrictToVertexSet G x) d h_reg, ← Finset.mul_sum]
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
  · exact sum_sq_pos G (restrictToVertexSet G x) hy_ne

lemma normalizedSupportedOrthogonal_isCompact (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    IsCompact (normalizedSupportedOrthogonal G) := by
  classical
  haveI := Fintype.ofFinite α
  haveI : ProperSpace (α → ℝ) := FiniteDimensional.proper ℝ (α → ℝ)
  let K : Set (α → ℝ) := normalizedSupportedOrthogonal G
  have hsupport : IsClosed {x : α → ℝ | ∀ v, v ∉ V(G) → x v = 0} := by
    let Z : Set (α → ℝ) := ⋂ v : α, ⋂ (_ : v ∉ V(G)), {x : α → ℝ | x v = 0}
    have hZ : IsClosed Z := by
      apply isClosed_iInter
      intro v
      apply isClosed_iInter
      intro hv
      exact isClosed_eq (continuous_apply v) continuous_const
    have hZE : Z = {x : α → ℝ | ∀ v, v ∉ V(G) → x v = 0} := by
      ext x
      simp [Z]
    simpa [hZE] using hZ
  have horthClosed :
      IsClosed {x : α → ℝ | V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0} := by
    apply isClosed_eq _ continuous_const
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul (continuous_apply v)
  have hnormClosed : IsClosed {x : α → ℝ | G.deg_norm x = 1} := by
    apply isClosed_eq _ continuous_const
    unfold deg_norm
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul ((continuous_apply v).pow 2)
  have hclosed : IsClosed K := by
    have hK_eq : K = {x : α → ℝ | (∀ v, v ∉ V(G) → x v = 0)} ∩
        {x : α → ℝ | V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0} ∩
        {x : α → ℝ | G.deg_norm x = 1} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hsupp, ⟨horth, hne⟩, hnorm⟩
        exact ⟨⟨hsupp, horth⟩, hnorm⟩
      · intro hx
        rcases hx with ⟨⟨hsupp, horth⟩, hnorm⟩
        refine ⟨hsupp, ⟨horth, ?_⟩, hnorm⟩
        by_contra hnone
        push_neg at hnone
        have hzero_norm : G.deg_norm x = 0 := by
          unfold deg_norm
          apply Finset.sum_eq_zero
          intro v hv
          simp [hnone v hv]
        have hnorm_eq : G.deg_norm x = 1 := hnorm
        linarith
    rw [hK_eq]
    exact (hsupport.inter horthClosed).inter hnormClosed
  have hbounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : α → ℝ)]
    refine ⟨1, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Pi.norm_def]
    change (Finset.univ.sup fun b => ‖x b‖₊) ≤ (1 : NNReal)
    apply Finset.sup_le_iff.mpr
    intro v hv
    by_cases hvV : v ∈ V(G)
    · have hdeg : G.deg_norm x = ∑ u ∈ V(G), (d : ℝ) * x u ^ 2 :=
        deg_norm_eq_sum_reg G x d h_reg
      have hnorm : G.deg_norm x = 1 := hx.2.2
      have hsum_eq : (d : ℝ) * ∑ u ∈ V(G), x u ^ 2 = 1 := by
        rw [Finset.mul_sum]
        exact hdeg.symm.trans hnorm
      have hterm_le_sum : x v ^ 2 ≤ ∑ u ∈ V(G), x u ^ 2 := by
        exact Finset.single_le_sum (fun u hu => sq_nonneg (x u)) hvV
      have hd_ge_one : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_d_pos)
      have hsum_nonneg : 0 ≤ ∑ u ∈ V(G), x u ^ 2 :=
        Finset.sum_nonneg (by intro u hu; exact sq_nonneg _)
      have hsum_le_one : ∑ u ∈ V(G), x u ^ 2 ≤ 1 := by
        have hd_nonneg : (0 : ℝ) ≤ d := by positivity
        nlinarith
      have hsq_le : x v ^ 2 ≤ 1 := le_trans hterm_le_sum hsum_le_one
      have habs_le : |x v| ≤ 1 := by
        rw [← sq_le_sq₀ (abs_nonneg _) zero_le_one]
        simpa [sq_abs] using hsq_le
      exact NNReal.coe_le_coe.mp (by simpa [Real.norm_eq_abs] using habs_le)
    · have hxv : x v = 0 := hx.1 v hvV
      exact NNReal.coe_le_coe.mp (by simp [hxv])
  exact hbounded.isCompact_closure.of_isClosed_subset hclosed subset_closure

lemma continuous_rayleighQuotient_on_normalizedSupportedOrthogonal (G : SimpleGraph α) :
    ContinuousOn (fun x : α → ℝ => G.rayleighQuotient x)
      (normalizedSupportedOrthogonal G) := by
  classical
  unfold rayleighQuotient
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    apply continuous_finset_sum
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      simpa using ((continuous_apply u).sub (continuous_apply v)).pow 2
  · apply Continuous.continuousOn
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul ((continuous_apply v).pow 2)
  · intro x hx
    have hnorm : G.deg_norm x = 1 := hx.2.2
    unfold deg_norm at hnorm
    rw [hnorm]
    norm_num

lemma R_values_eq_rayleigh_image_normalizedSupportedOrthogonal (G : SimpleGraph α) [Finite α]
    (d : ℕ) (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    R_values G =
      (fun x : α → ℝ => G.rayleighQuotient x) '' normalizedSupportedOrthogonal G := by
  classical
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hxorth, rfl⟩
    let y0 := restrictToVertexSet G x
    let n := G.deg_norm y0
    let c : ℝ := (Real.sqrt n)⁻¹
    let y : α → ℝ := fun v => c * y0 v
    have hn_pos : 0 < n := by
      exact deg_norm_pos_of_supported_orthogonal_of_regular_pos G d h_d_pos h_reg hxorth
    have hc_ne : c ≠ 0 := by
      unfold c
      exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hn_pos))
    have hy0orth : y0 ∈ orthogonalVectors G :=
      orthogonalVectors_restrictToVertexSet G x hxorth
    refine ⟨y, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro v hv
        simp [y, y0, restrictToVertexSet, hv]
      · rcases hy0orth with ⟨hy0_sum, hy0_ne⟩
        constructor
        · unfold y
          calc
            ∑ v ∈ V(G), (deg(G,v) : ℝ) * (c * y0 v)
                = c * ∑ v ∈ V(G), (deg(G,v) : ℝ) * y0 v := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro v hv
                  ring
            _ = 0 := by rw [hy0_sum, mul_zero]
        · rcases hy0_ne with ⟨v, hv, hyv⟩
          exact ⟨v, hv, by simp [y, hc_ne, hyv]⟩
      · have hnorm_mul := deg_norm_mul G y0 c
        have hcn : c ^ 2 * n = 1 := by
          unfold c
          have hs_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
          field_simp [hs_ne]
          rw [Real.sq_sqrt (le_of_lt hn_pos)]
        calc
          G.deg_norm y = G.deg_norm (fun v => c * y0 v) := rfl
          _ = c ^ 2 * G.deg_norm y0 := hnorm_mul
          _ = c ^ 2 * n := rfl
          _ = 1 := hcn
    · have hy_rq : G.rayleighQuotient y = G.rayleighQuotient x := by
        calc
          G.rayleighQuotient y = G.rayleighQuotient (fun v => c * y0 v) := rfl
          _ = G.rayleighQuotient y0 := rayleighQuotient_mul G y0 hc_ne
          _ = G.rayleighQuotient x := rayleighQuotient_restrictToVertexSet G x
      exact hy_rq
  · intro hr
    rcases hr with ⟨x, hxK, rfl⟩
    exact ⟨x, hxK.2.1, rfl⟩

noncomputable def graphExpansionValidSubsets (G : SimpleGraph α) : Finset (Finset α) :=
  (V(G).powerset).filter (fun S => S.Nonempty ∧ 2 * S.card ≤ (V(G)).card)

lemma mem_graphExpansionValidSubsets_of_valid (G : SimpleGraph α) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ V(G))
    (hS_size : 2 * S.card ≤ (V(G)).card) :
    S ∈ graphExpansionValidSubsets G := by
  classical
  simp [graphExpansionValidSubsets, hS_sub, hS_ne, hS_size]

lemma graphExpansionValidSubsets_nonempty_of_valid (G : SimpleGraph α) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ V(G))
    (hS_size : 2 * S.card ≤ (V(G)).card) :
    (graphExpansionValidSubsets G).Nonempty := by
  exact ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size⟩

lemma edgeExpansion_mem_graphExpansion_image_of_valid (G : SimpleGraph α) (d : ℕ)
    (S : Finset α) (hS_ne : S.Nonempty) (hS_sub : S ⊆ V(G))
    (hS_size : 2 * S.card ≤ (V(G)).card) :
    edgeExpansion G d S ∈ (graphExpansionValidSubsets G).image (fun T => edgeExpansion G d T) := by
  exact Finset.mem_image.mpr
    ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size, rfl⟩

lemma edgeExpansion_zero_degree (G : SimpleGraph α) (S : Finset α) :
    edgeExpansion G 0 S = 0 := by
  unfold edgeExpansion
  simp

lemma graphExpansion_zero_degree (G : SimpleGraph α) :
    graphExpansion G 0 = 0 := by
  classical
  unfold graphExpansion
  dsimp only
  split_ifs with h
  · apply le_antisymm
    · obtain ⟨S, hS⟩ := h
      have hm : edgeExpansion G 0 S ∈ (Finset.image (fun S => edgeExpansion G 0 S)
          {S ∈ V(G).powerset | S.Nonempty ∧ 2 * #S ≤ #V(G)}) := by
        exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
      have hz : edgeExpansion G 0 S = 0 := edgeExpansion_zero_degree G S
      simpa [hz] using Finset.min'_le _ _ hm
    · apply Finset.le_min'
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
      rw [edgeExpansion_zero_degree]
  · rfl

/-- Level-set coarea counting for the sweep proof.  The finite set `levels`
and positive weights `w` are shared with `volume_coarea_counting` below. -/
lemma level_coarea_counting (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_pos : ∀ v, 0 ≤ y v)
    (h_y_pos : ∃ v ∈ V(G), 0 < y v) :
    ∃ levels : Finset ℝ, ∃ w : ℝ → ℝ,
      levels.Nonempty ∧
      (∀ t ∈ levels, 0 < t) ∧
      (∀ t ∈ levels, 0 < w t) ∧
      (∀ t ∈ levels, (V(G).filter (fun v => y v ≥ t)).Nonempty) ∧
      (∑ t ∈ levels, w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
        Real.sqrt (2 * G.energy y * G.deg_norm y)) ∧
      (∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
        G.deg_norm y) := by
  classical
  let levels := (V(G).image y).filter (fun t => 0 < t)
  let w := coareaWeight levels
  refine ⟨levels, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact positive_value_levels_nonempty G y h_y_pos
  · exact positive_value_level_pos G y
  · intro t ht
    exact coareaWeight_pos_of_pos_mem (positive_value_level_pos G y) ((Finset.mem_filter.mp ht).2)
  · exact positive_value_level_set_nonempty G y
  · simpa [levels, w] using level_coarea_cut_bound G d y h_reg h_pos
  · simpa [levels, w] using level_coarea_volume_identity G d y h_reg h_pos

/-- Volume coarea counting for the same finite sweep levels and weights
provided by `level_coarea_counting`. -/
lemma volume_coarea_counting (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (levels : Finset ℝ) (w : ℝ → ℝ)
    (h_levels_pos : ∀ t ∈ levels, 0 < t)
    (h_weights_pos : ∀ t ∈ levels, 0 < w t)
    (h_levels_nonempty : levels.Nonempty)
    (h_level_sets_nonempty :
      ∀ t ∈ levels, (V(G).filter (fun v => y v ≥ t)).Nonempty)
    (h_volume :
      ∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
        G.deg_norm y) :
    ∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
      G.deg_norm y := by
  exact h_volume

/-- Cauchy-Schwarz step in the sweep proof, converting the coarea numerator
bound into a Rayleigh-quotient bound. -/
lemma coarea_bound_to_rayleigh (G : SimpleGraph α) (y : α → ℝ)
    (d : ℕ) (levels : Finset ℝ) (w : ℝ → ℝ)
    (h_norm_pos : 0 < G.deg_norm y)
    (h_level_bound :
      ∑ t ∈ levels, w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
        Real.sqrt (2 * G.energy y * G.deg_norm y))
    (h_volume :
      ∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
        G.deg_norm y) :
    ∑ t ∈ levels, w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
      Real.sqrt (2 * G.rayleighQuotient y) *
        ∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) := by
  rw [h_volume, rQ_eq_energy_div_norm]
  have h_norm_nonneg : 0 ≤ G.deg_norm y := le_of_lt h_norm_pos
  have h_energy_nonneg : 0 ≤ G.energy y := energy_nonneg G y
  have h_norm_ne : G.deg_norm y ≠ 0 := ne_of_gt h_norm_pos
  have h_sqrt_eq :
      Real.sqrt (2 * G.energy y * G.deg_norm y) =
        Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := by
    have h_factor_nonneg : 0 ≤ 2 * (G.energy y / G.deg_norm y) := by
      exact mul_nonneg (by norm_num) (div_nonneg h_energy_nonneg h_norm_nonneg)
    calc
      Real.sqrt (2 * G.energy y * G.deg_norm y)
          = Real.sqrt ((2 * (G.energy y / G.deg_norm y)) *
              (G.deg_norm y * G.deg_norm y)) := by
            congr 1
            field_simp [h_norm_ne]
      _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) *
            Real.sqrt (G.deg_norm y * G.deg_norm y) := by
            exact Real.sqrt_mul h_factor_nonneg (G.deg_norm y * G.deg_norm y)
      _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := by
            rw [Real.sqrt_mul_self h_norm_nonneg]
  calc
    ∑ t ∈ levels, w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card
        ≤ Real.sqrt (2 * G.energy y * G.deg_norm y) := h_level_bound
    _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := h_sqrt_eq

lemma sweep_threshold_expansion_bound (G : SimpleGraph α) (d : ℕ) (y : α → ℝ)
    (hV : 2 ≤ (V(G)).card)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_pos : ∀ v, 0 ≤ y v)
    (h_y_pos : ∃ v ∈ V(G), 0 < y v)
    (h_supp : 2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) :
    ∃ t > 0,
      let S_t := V(G).filter (fun v => y v ≥ t)
      S_t.Nonempty ∧ edgeExpansion G d S_t ≤ Real.sqrt (2 * rayleighQuotient G y) := by
  obtain ⟨levels, w, hlevels_ne, hlevels_pos, hw_pos, hlevel_sets_ne, hlevel_bound,
      hvolume_raw⟩ :=
    level_coarea_counting G d y h_reg h_pos h_y_pos
  have hvolume :=
    volume_coarea_counting G d y h_reg levels w hlevels_pos hw_pos hlevels_ne
      hlevel_sets_ne hvolume_raw
  have h_norm_pos : 0 < G.deg_norm y := by
    rw [deg_norm_eq_sum_reg G y d h_reg, ← Finset.mul_sum]
    apply mul_pos
    · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
    · exact sum_sq_pos G y (by
        rcases h_y_pos with ⟨v, hv, hyv_pos⟩
        exact ⟨v, hv, ne_of_gt hyv_pos⟩)
  have h_sum_bound :
      ∑ t ∈ levels, w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card ≤
        Real.sqrt (2 * G.rayleighQuotient y) *
          ∑ t ∈ levels, w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) :=
    coarea_bound_to_rayleigh G y d levels w h_norm_pos hlevel_bound hvolume
  obtain ⟨t, ht_mem, ht_denom_pos, ht_ratio⟩ :=
    exists_ratio_le_of_sum_le levels
      (fun t => w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card)
      (fun t => w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ))
      (Real.sqrt (2 * G.rayleighQuotient y))
      hlevels_ne
      (by
        intro t ht
        apply mul_pos (hw_pos t ht)
        exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero h_d_pos)
          (Finset.card_pos.mpr (hlevel_sets_ne t ht)))
      h_sum_bound
  refine ⟨t, hlevels_pos t ht_mem, hlevel_sets_ne t ht_mem, ?_⟩
  unfold edgeExpansion
  have hw_ne : w t ≠ 0 := ne_of_gt (hw_pos t ht_mem)
  have hdcard_pos :
      0 < ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero h_d_pos)
      (Finset.card_pos.mpr (hlevel_sets_ne t ht_mem))
  have hdcard_ne :
      ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt hdcard_pos
  have hratio_eq :
      (w t * (Cut G (V(G).filter (fun v => y v ≥ t))).card) /
          (w t * ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ)) =
        ((Cut G (V(G).filter (fun v => y v ≥ t))).card : ℝ) /
          ((d * (V(G).filter (fun v => y v ≥ t)).card : ℕ) : ℝ) := by
    field_simp [hw_ne, hdcard_ne]
  rw [hratio_eq] at ht_ratio
  simpa [Nat.cast_mul] using ht_ratio

lemma lemma_4 (G : SimpleGraph α) (d : ℕ) (y : α → ℝ) (hV : 2 ≤ (V(G)).card)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_pos : ∀ v, 0 ≤ y v)
    (h_y_pos : ∃ v ∈ V(G), 0 < y v)
    (h_supp : 2 * (V(G).filter (fun v => y v > 0)).card ≤ V(G).card) :
    ∃ t > 0,
      let S_t := V(G).filter (fun v => y v ≥ t)
      S_t.Nonempty ∧ edgeExpansion G d S_t ≤ Real.sqrt (2 * rayleighQuotient G y) := by
  exact sweep_threshold_expansion_bound G d y hV h_d_pos h_reg h_pos h_y_pos h_supp




lemma lemma3 (G : SimpleGraph α) (d : ℕ) (x : α → ℝ) (h_d_pos : d ≠ 0)
    (hV : 2 ≤ (V(G)).card) (h_reg : ∀ v ∈ V(G), #δ(G,v) = d)
    (h_x_ne : ∃ v ∈ V(G), x v ≠ 0)
    (h_orth : V(G).sum (fun v => (deg(G,v) : ℝ) * x v) = 0) :
    let S_f := fiedlerCut G d x hV
    S_f.Nonempty ∧ S_f ⊆ V(G) ∧ 2 * S_f.card ≤ (V(G)).card ∧
      G.edgeExpansion d S_f ≤ Real.sqrt (2 * G.rayleighQuotient x) := by
  let S_f := fiedlerCut G d x hV
  let R_x := G.rayleighQuotient x
  -- 1. Structural Properties (Non-empty and Subset)
  have hS_ne : S_f.Nonempty := fiedlerCut_nonempty G d x hV
  have hS_sub : S_f ⊆ V(G) := fiedlerCut_is_subset G d x hV
  -- 2. Use Lemma 5 and Lemma 4 to establish the existence of a good threshold cut
  obtain ⟨y, h_pos, h_y_pos, h_supp, h_rayleigh, h_sweep_subset⟩ :=
    lemma_5 G x d hV h_d_pos h_x_ne h_orth h_reg
  obtain ⟨t, ht_pos, hSt_ne, h_lem_4⟩ :=
    lemma_4 G d y hV h_d_pos h_reg h_pos h_y_pos h_supp
  -- From lemma_5, there exists a specific S_t in sweepCuts G x
  -- that corresponds to the threshold t of y.
  let h_exists := h_sweep_subset t ht_pos
  let S_t := V(G).filter (fun v => y v ≥ t)
  have hSt_mem : S_t ∈ sweepCuts G x := h_exists hSt_ne
  have hSt_eq : S_t = V(G).filter (fun v => y v ≥ t) := by grind
  -- Assume y is the vector from Lemma 5 and t is from Lemma 4
  have hSt_ne' : (V(G).filter (fun v => y v ≥ t)).Nonempty := by
    simpa [S_t] using hSt_ne
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
  exact ⟨fiedlerCut_nonempty G d x hV, fiedlerCut_is_subset G d x hV,
    fiedlerCut_card_le_half G d x hV, h_alg⟩










/-- Lemma: There exists a non-zero vector x orthogonal to the constant vector
    such that its Rayleigh quotient achieves λ₂. -/
lemma R_values_nonempty_of_regular_two_vertices (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) (hV : 2 ≤ #V(G)) :
    (R_values G).Nonempty := by
  classical
  have hcard : 1 < (V(G)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  let x : α → ℝ := fun v => if v = a then (1 : ℝ) else if v = b then (-1 : ℝ) else 0
  refine ⟨G.rayleighQuotient x, ?_⟩
  refine ⟨x, ?_, rfl⟩
  constructor
  · rw [show V(G).sum (fun v => (deg(G,v) : ℝ) * x v) =
          ∑ v ∈ V(G), (d : ℝ) * x v by
        apply Finset.sum_congr rfl
        intro v hv
        rw [h_reg v hv]]
    rw [show (∑ v ∈ V(G), (d : ℝ) * x v) = (d : ℝ) * ∑ v ∈ V(G), x v by
      rw [Finset.mul_sum]]
    have hsum : ∑ v ∈ V(G), x v = 0 := by
      have hV_eq : V(G) = insert a (insert b ((V(G).erase a).erase b)) := by
        ext v
        by_cases hva : v = a
        · subst hva
          simp [ha]
        · by_cases hvb : v = b
          · subst hvb
            simp [hb, hab.symm]
          · simp [hva, hvb]
      rw [hV_eq]
      have hrest : ∑ v ∈ (V(G).erase a).erase b, x v = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have hva : v ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
        have hvb : v ≠ b := (Finset.mem_erase.mp hv).1
        simp [x, hva, hvb]
      simp [x, hab, hab.symm, hrest]
    rw [hsum, mul_zero]
  · exact ⟨a, ha, by simp [x]⟩

lemma R_values_bddBelow (G : SimpleGraph α) :
    BddBelow (R_values G) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  exact rayleighQuotient_nonneg G x

/-- Compactness/closedness interface for the Rayleigh values on nonzero vectors
orthogonal to constants.  The proof is by normalizing to `deg_norm = 1`,
using finite-dimensional compactness of the normalized feasible set, and then
projecting the continuous energy function to `ℝ`. -/
lemma R_values_isClosed_of_regular_two_vertices (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) (hV : 2 ≤ #V(G)) :
    IsClosed (R_values G) := by
  classical
  by_cases h_d_pos : d = 0
  · have hreg0 : ∀ v ∈ V(G), #δ(G,v) = 0 := by
      intro v hv
      simpa [h_d_pos] using h_reg v hv
    rw [R_values_eq_singleton_zero_of_regular_zero G hreg0 hV]
    exact isClosed_singleton
  · rw [R_values_eq_rayleigh_image_normalizedSupportedOrthogonal G d h_d_pos h_reg]
    exact ((normalizedSupportedOrthogonal_isCompact G d h_d_pos h_reg).image_of_continuousOn
      (continuous_rayleighQuotient_on_normalizedSupportedOrthogonal G)).isClosed

lemma lambda2_mem_R_values_of_regular_two_vertices (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) (hV : 2 ≤ #V(G)) :
    G.lambda2 ∈ R_values G := by
  unfold lambda2
  exact (R_values_isClosed_of_regular_two_vertices G d h_reg hV).csInf_mem
    (R_values_nonempty_of_regular_two_vertices G d h_reg hV)
    (R_values_bddBelow G)

lemma exists_eigenvector_lambda2 (G : SimpleGraph α) [Finite α] (d : ℕ)
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) (hV : 2 ≤ #V(G)) :
    ∃ x : α → ℝ, (∃ v ∈ V(G), x v ≠ 0) ∧
      (∑ v ∈ V(G), (deg(G,v) : ℝ) * x v = 0) ∧
      G.rayleighQuotient x = G.lambda2 := by
  obtain ⟨x, hx_orth, hx_rayleigh⟩ :=
    lambda2_mem_R_values_of_regular_two_vertices G d h_reg hV
  rcases hx_orth with ⟨horth, hx_ne⟩
  exact ⟨x, hx_ne, horth, hx_rayleigh.symm⟩

/-- `graphExpansion` is no larger than the expansion of any valid nonempty subset. -/
lemma graphExpansion_le_of_valid (G : SimpleGraph α) (d : ℕ) (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ V(G))
    (hS_size : 2 * S.card ≤ (V(G)).card) :
    graphExpansion G d ≤ edgeExpansion G d S := by
  classical
  let validSubsets := (V(G).powerset).filter
    (fun S : Finset α => S.Nonempty ∧ 2 * S.card ≤ (V(G)).card)
  have hS_mem_raw : S ∈ validSubsets := by
    simpa [validSubsets, graphExpansionValidSubsets] using
      mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size
  have hvalid_nonempty : validSubsets.Nonempty := by
    simpa [validSubsets, graphExpansionValidSubsets] using
      graphExpansionValidSubsets_nonempty_of_valid G S hS_ne hS_sub hS_size
  unfold graphExpansion
  dsimp only
  rw [dif_pos hvalid_nonempty]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨S, hS_mem_raw, rfl⟩

/-- The Hard Direction of Cheeger's Inequality: h(G) ≤ √(2 * λ₂) -/
theorem cheeger_hard_direction (G : SimpleGraph α) [Finite α] (d : ℕ)
    (hV : 2 ≤ #V(G))
    (h_reg : ∀ v ∈ V(G), #δ(G,v) = d) :
    graphExpansion G d ≤ Real.sqrt (2 * G.lambda2) := by
  -- 1. Obtain the second eigenvector x with R(x) = λ₂
  obtain ⟨x, h_x_ne, h_orth, h_lambda2⟩ := G.exists_eigenvector_lambda2 d h_reg hV
  -- 3. Handle the d = 0 case (isolated vertices)
  by_cases h_d_pos : d = 0
  · -- If d = 0, expansion is 0 and lambda2 is 0.
    rw [h_d_pos, graphExpansion_zero_degree]
    exact Real.sqrt_nonneg _
  -- 4. Apply Lemma 3 (The Sweep Cut Lemma)
  -- This provides a cut S_f (the Fiedler cut) from the level sets of x
  let S_f := fiedlerCut G d x hV
  obtain ⟨hS_ne, hS_sub, hS_size, hS_phi⟩ := lemma3 G d x h_d_pos hV h_reg h_x_ne h_orth
  -- 5. Relate h(G) to the expansion of this specific Fiedler cut
  -- Since h(G) = min_{|S|≤n/2} ϕ(S), and Lemma 3 guarantees S_f is valid:
  have h_cheeger_le : graphExpansion G d ≤ edgeExpansion G d S_f := by
    exact graphExpansion_le_of_valid G d S_f hS_ne hS_sub hS_size
  -- 6. Final Chain of Inequalities
  calc
    graphExpansion G d ≤ edgeExpansion G d S_f := h_cheeger_le
    _ ≤ Real.sqrt (2 * G.rayleighQuotient x) := hS_phi
    _ = Real.sqrt (2 * G.lambda2) := by rw [h_lambda2]

end SimpleGraph
