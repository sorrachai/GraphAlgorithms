import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic


import GraphAlgorithms.UndirectedGraphs.SimpleGraphs

-- Cuts and contractions (undirected simple)
-- Authors: Weixuan Yuan


set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open SimpleGraphs

def Cut (G : SimpleGraph α) (U : Finset α) :
  Finset (Edge α) := {e ∈ E(G) | ∃ u ∈ U, u ∈ e ∧ ∃ v ∈ V(G) \ U, v ∈ e}

--Weight function
class LinearOrderedAddCommMonoid (R : Type*) extends
  LinearOrder R, -- total order
  AddCommMonoid R, -- commutative addition
  IsOrderedAddMonoid R -- addition is monotone

variable {R : Type*} [LinearOrderedAddCommMonoid R]

open Finset BigOperators

namespace Cuts


def weight (G : SimpleGraph α) (U : Finset α) (w : Edge α → R) : R :=
  Finset.sum (Cut G U) w


lemma cut_submodular (G : SimpleGraph α) (U W : Finset α)
(w : Edge α → R) (w_pos : ∀ e, 0 ≤ w e) :
  weight G (U ∩ W) w + weight G (U ∪ W) w ≤ weight G U w + weight G W w := by
  have h1 : Cut G (U ∩ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h2 : Cut G (U ∪ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h3 : Cut G (U ∩ W) ∩ Cut G (U ∪ W) ⊆ Cut G U ∩ Cut G W := by grind [Cut]
  have h4 : (Cut G (U ∩ W)) ∪ (Cut G (U ∪ W)) ⊆ (Cut G U) ∪ (Cut G W) := by apply union_subset h1 h2
  clear h1 h2
  repeat unfold weight
  rw[<-Finset.sum_union_inter]
  nth_rw 2 [<-Finset.sum_union_inter]
  have h1 : Finset.sum (Cut G (U ∩ W) ∪ Cut G (U ∪ W)) w ≤ Finset.sum (Cut G U ∪ Cut G W) w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h4
    grind [Cut]
  have h2 : Finset.sum (Cut G (U ∩ W) ∩ Cut G (U ∪ W)) w ≤ Finset.sum (Cut G U ∩ Cut G W) w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h3
    grind [Cut]
  apply add_le_add h1 h2


def is_st_cut (G : SimpleGraph α) (U : Finset α) (s t : α) : Prop :=
  s ∈ U ∧ t ∉ U ∧ U.Nonempty ∧ U ⊂ V(G)

def is_st_mincut (G : SimpleGraph α) (U : Finset α) (s t : α) (w : Edge α → R) : Prop :=
  is_st_cut G U s t ∧ ∀ W : Finset α, is_st_cut G W s t → weight G U w ≤ weight G W w

instance (G : SimpleGraph α) (s t : α) :
    DecidablePred (fun U : Finset α => is_st_cut G U s t) := by
  intro U; unfold is_st_cut; infer_instance

def st_cuts (G : SimpleGraph α) (s t : α) : Finset (Finset α) :=
  G.vertexSet.powerset.filter (fun U => is_st_cut G U s t)

noncomputable def st_mincut_value (G : SimpleGraph α) (s t : α) (w : Edge α → R)
    (h : (st_cuts G s t).Nonempty) : R := by
  classical
  apply Finset.nonempty_def.1 at h;
  refine ((st_cuts G s t).image (fun U => weight G U w)).min' ?_
  rcases h with ⟨U, hU⟩
  exact ⟨weight G U w, by
    exact Finset.mem_image_of_mem (fun X => weight G X w) hU⟩

lemma st_min_cut {G : SimpleGraph α} {U : Finset α} {s t : α} {w : Edge α → R}
  (h : (st_cuts G s t).Nonempty) :
  is_st_mincut G U s t w ↔ is_st_cut G U s t ∧ weight G U w = st_mincut_value G s t w h := by
  constructor
  · intro hmin;  simp_all [is_st_mincut]
    apply le_antisymm
    · apply le_min'; grind [st_cuts]
    · apply min'_le; grind [st_cuts, is_st_cut]
  · rintro ⟨h1,h2⟩
    unfold is_st_mincut; simp_all
    rintro W hW; rw[<-h2]
    unfold st_mincut_value at h2; simp_all; apply min'_le
    grind [st_cuts, is_st_cut]


end Cuts


--The base case of a contraction is defined  w.r.t. an equivalence relation on α.
--The condition relies on G, i.e., V(G) should be closed under the equivalence relation.
structure ContractionSpec (G : SimpleGraph α) where
  s : Setoid α
  closed : ∀ {u v : α}, s.r u v → u ∈ V(G) → v ∈ V(G)

namespace Contraction
noncomputable section

variable (G : SimpleGraph α)

section
variable (spec : ContractionSpec G)

local notation "β" => Quotient spec.s
local notation "π" => (Quotient.mk spec.s : α → β)

def mapEdge : Edge α → Edge β := Sym2.map π

def vertexSet : Finset β := by classical
  exact (V(G)).image π

def edgeSet : Finset (Edge β) := by classical
  exact ((E(G)).image (mapEdge G spec)).filter (fun e => ¬ e.IsDiag)

lemma incidence : ∀ e ∈ edgeSet G spec, ∀ v ∈ e, v ∈ vertexSet G spec := by
  simp_all [edgeSet, vertexSet, mapEdge]
  grind [Sym2.mem_map, G.incidence]

lemma loopless : ∀ e ∈ edgeSet G spec, ¬ e.IsDiag := by grind [edgeSet]

def contract : SimpleGraph β where
  vertexSet := vertexSet G spec
  edgeSet   := edgeSet G spec
  incidence := incidence G spec
  loopless  := loopless G spec

def contraction_weight (w : Edge α → R) : Edge β → R := by classical
  exact fun e' => ∑ e ∈ (E(G)).filter (fun e => (mapEdge G spec e = e')
  ∧ ¬ (mapEdge G spec e).IsDiag), w e
end


-- Contracting a subset of vertices
def setoid_subset (U : Finset α) : Setoid α where
  r u v := u = v ∨ (u ∈ U ∧ v ∈ U)
  iseqv := by refine ⟨?refl, ?symm, ?trans⟩; all_goals grind

def contraction_spec_subset (U : Finset α) (hU : U ⊆ V(G)) :
    ContractionSpec G where
  s := setoid_subset U
  closed := by
    intro u v huv huV
    rcases huv with huv | huv
    all_goals grind

def contract' (U : Finset α) (hU : U ⊆ V(G)) : SimpleGraph (Quotient (setoid_subset U)) :=
  Contraction.contract (spec := contraction_spec_subset G U hU)

def contraction_weight' (U : Finset α) (hU : U ⊆ V(G))
    (w : Edge α → R) : Edge (Quotient (setoid_subset U)) → R := by classical
  exact Contraction.contraction_weight
    (spec := contraction_spec_subset G U hU) (w := w)

--Contracting a collection of disjoint subsets of vertices
def setoid_collection (Cs : Finset (Finset α))
(hdis : (Cs : Set (Finset α)).Pairwise (fun A B => Disjoint A B)) : Setoid α where
  r u v := u = v ∨ ∃ C ∈ Cs, u ∈ C ∧ v ∈ C
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    grind; grind; aesop
    have h : w = w_1 := by
      by_contra!;
      have h1 := hdis left left_1 this; grind [Finset.disjoint_left]
    grind

def contraction_spec_collection (Cs : Finset (Finset α))
    (hdis : (Cs : Set (Finset α)).Pairwise (fun A B => Disjoint A B))
    (hCs : ∀ C ∈ Cs, C ⊆ V(G)) :
    ContractionSpec G where
  s := setoid_collection Cs hdis
  closed := by
    intro u v huv huV
    rcases huv with huv | huv
    all_goals grind

def contract'' (Cs : Finset (Finset α))
    (hdis : (Cs : Set (Finset α)).Pairwise (fun A B => Disjoint A B))
    (hCs : ∀ C ∈ Cs, C ⊆ V(G)) :
    SimpleGraph (Quotient (setoid_collection (α := α) Cs hdis)) :=
  Contraction.contract (spec := contraction_spec_collection G Cs hdis hCs)

def contraction_weight'' (Cs : Finset (Finset α))
    (hdis : (Cs : Set (Finset α)).Pairwise (fun A B => Disjoint A B))
    (hCs : ∀ C ∈ Cs, C ⊆ V(G)) (w : Edge α → R) :
    Edge (Quotient (setoid_collection Cs hdis)) → R := by classical
  exact Contraction.contraction_weight
    (spec := contraction_spec_collection G Cs hdis hCs) (w := w)


end
end Contraction
