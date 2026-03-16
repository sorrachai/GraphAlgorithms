import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic


import GraphAlgorithms.UndirectedGraphs.SimpleGraphs
import GraphAlgorithms.UndirectedGraphs.Cuts


-- Contractions (undirected simple)
-- Authors: Weixuan Yuan


set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]
variable {R : Type*} [LinearOrderedAddCommMonoid R]


open SimpleGraphs

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

-- Configuration of weights
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
