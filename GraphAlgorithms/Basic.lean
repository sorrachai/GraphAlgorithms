import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Util.Notation3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic.Qify
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic


open Classical
universe u u'

def BinaryMatrix' (m : Type u) (n : Type u') := Matrix m n Prop
def BinaryMatrix (m n: ℕ ) := BinaryMatrix' (Fin m) (Fin n)
def BinarySqMatrix (n: ℕ ) := BinaryMatrix n n

lemma two_mul_choose_two_cancel (n : ℕ ) : 2*n.choose 2 = n*(n - 1) := by
  rw [Nat.choose_two_right]
  ring_nf
  suffices 2 ∣ n*(n-1) from Nat.div_mul_cancel this
  rw [@Nat.dvd_mul]
  obtain zero | pos := Nat.eq_zero_or_pos n
  · use 2,1
    simp
    exact Fin.natCast_eq_zero.mp (congrArg Nat.cast zero)
  observe: 1 ≤ n
  obtain even | odd := Nat.even_or_odd n
  · -- even
    use 2,1
    simp
    exact even_iff_two_dvd.mp even
  · -- odd
    use 1,2
    simp
    rw [Nat.odd_iff] at odd
    exact (Nat.modEq_iff_dvd' pos).mp (id (Eq.symm odd))


-- Metric.lean
-- Graph spanners: A tutorial review
-- Problem 1 (Basic t-Spanner Problem). Given a connected graph G = (V, E) and a fixed t ≥ 1,
-- find a subset E′ ⊆ E such that the subgraph G′ = (V, E′) of G satisfies
-- d_G′(u, v) ≤ t · d_G(u, v), for all u, v ∈ V
-- What is the minimum size of E′ that can be achieved?

open SimpleGraph Finset Classical
variable {n t : ℕ} [NeZero t]
def Edge n:= Sym2 (Fin n)

@[ext, aesop safe constructors (rule_sets := [SimpleGraph])]
structure WeightedSimpleGraph (V : Type u) [Fintype V] extends SimpleGraph V  where
  w: V → V → ℕ
  AdjAndWeight : ∀ u v : V, w u v > 0 ↔ Adj u v --:= by aesop_graph

def FinSimpleGraph (n : ℕ) := SimpleGraph (Fin n)

@[ext] theorem FinSimpleGraph.ext {G H : FinSimpleGraph n} (h: G.Adj = H.Adj): G = H := by
  cases G; cases H
  simp only [SimpleGraph.mk] at h
  subst h
  rfl

@[simps]
def FinSimpleGraph.mk':
    {adj : Fin n → Fin n → Prop // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ FinSimpleGraph n where
  toFun x := ⟨fun v w ↦ x.1 v w, fun v w ↦ by simp [x.2.1], fun v ↦ by simp [x.2.2]⟩
  inj' := by
    rintro ⟨adj, p1⟩ ⟨adj', p2⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    contrapose!
    intro h
    simp only [ne_eq, SimpleGraph.mk.injEq]
    exact h

noncomputable instance  FinSimpleGraphFintypeInst (n :ℕ ): Fintype (FinSimpleGraph n) where
  elems := Finset.univ.map FinSimpleGraph.mk'
  complete := by
    classical
    rintro ⟨Adj, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w ↦ Adj v w, ⟨?_, ?_⟩, ?_⟩
    · simp [hs.iff]
    · intro v; simp [hi v]
    · refine FinSimpleGraph.ext_iff.mpr ?_
      ext i j
      simp

open FinSimpleGraph Std

def FinSimpleGraph.IsSpannerOf   (H G : FinSimpleGraph n)  (t:ℕ)  : Prop :=
  H.IsSubgraph G ∧ ∀ u v : Fin n, H.dist u v ≤ t * G.dist u v ∧ G.dist u v ≤ H.dist u v

lemma num_edges_le_nn   (G :FinSimpleGraph n):  #G.edgeFinset < n*n+1:= by
  calc
    #G.edgeFinset ≤ (Fintype.card (Fin n)).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
    _ ≤ 2* ((Fintype.card (Fin n)).choose 2) := by omega
    _ = 2* (n.choose 2) := by rw [Fintype.card_fin]
    _ = (n*(n-1)) := two_mul_choose_two_cancel n
    _ < n*n +1:= by
      refine Nat.lt_add_one_of_le ?_
      cases n
      simp
      simp

noncomputable def FinSimpleGraph.numEdges  (G : FinSimpleGraph n) : ℕ := #G.edgeFinset
noncomputable def exGirth (n t:ℕ)  : ℕ := sup {H : FinSimpleGraph n | 2*t + 1 ≤ H.girth } numEdges

lemma exGirthUB (n t:ℕ) : exGirth n t ≤ 100 * n * (NNReal.rpow ↑n (1/(↑t))) := sorry

def BinarySqMatrix.AddEdge  (M : BinarySqMatrix n) ( e : Sym2 (Fin n) ):
 Fin n → Fin n → Prop := fun (i j : Fin n) ↦ M i j ∨ (e = s(i,j))

noncomputable def BinarySqMatrix.dist (M : BinarySqMatrix n) (e : Sym2 (Fin n)): ℕ
:= (SimpleGraph.fromRel M).dist (Quot.out e).1 (Quot.out e).2


lemma cardGDel_lt_cardG_of' (G : FinSimpleGraph n) { e : Edge n} (h:  e ∈ G.edgeSet):
  let G' := G.deleteEdges {e}
  G' < G := by
  constructor
  aesop_graph
  refine not_le_of_lt ?_
  rw [@Pi.lt_def]
  constructor
  aesop_graph
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  use u
  refine Pi.lt_def.mpr ?_
  constructor
  aesop_graph
  use v

  simp only [deleteEdges_adj, Set.mem_singleton_iff]
  have x: s(u,v) = e := by aesop
  have: (¬ s(u,v) = e) = False := by aesop
  rw [this]
  simp only [and_false, gt_iff_lt]

  suffices  G.Adj u v by
    simp only [gt_iff_lt]
    exact lt_of_le_not_le (fun a ↦ this) fun a ↦ a this
  rw [@adj_iff_exists_edge_coe]
  aesop

lemma cardGDel_lt_cardG_of (G : FinSimpleGraph n) {e : Edge n} (h: e ∈ G.edgeSet):
  let G' := G.deleteEdges {e}
  #G'.edgeFinset < #G.edgeFinset := by

  extract_lets G'
  have: G' < G := cardGDel_lt_cardG_of' G h
  suffices G'.edgeFinset ⊂ G.edgeFinset from card_lt_card this
  aesop

example  (G : FinSimpleGraph n) {e : Edge n} (h: e ∈ G.edgeSet):
  let G' := G.deleteEdges {e}
  #G'.edgeFinset < #G.edgeFinset := by

  extract_lets G'
  suffices G'.edgeFinset ⊂ G.edgeFinset from card_lt_card this
  simp only [Set.ssubset_toFinset, Set.coe_toFinset, edgeSet_ssubset_edgeSet]
  simp [G',deleteEdges]
  refine sdiff_lt ?_ ?_
  · show fromEdgeSet {e} ≤ G
    refine edgeFinset_subset_edgeFinset.mp ?_
    simp [Set.subset_toFinset, Set.coe_toFinset, edgeSet_fromEdgeSet]
    intro x hx
    aesop

  · show fromEdgeSet {e} ≠ ⊥
    by_contra! empty
    rw [← SimpleGraph.edgeSet_eq_empty] at empty
    simp at empty
    rw [@Set.diff_eq_empty] at empty
    simp at empty
    suffices ¬ e.IsDiag by contradiction
    refine G.not_isDiag_of_mem_edgeSet ?_
    exact h


-- A nice lemma to prove, but no need for now.
lemma cardGDel_eq_cardG_minus_of (G : FinSimpleGraph n) {E : Finset (Edge n)} (h: E ⊆  G.edgeFinset) :
let G' := G.deleteEdges (E : Set (Edge n))
#G'.edgeFinset = #G.edgeFinset - #E := by sorry


noncomputable def GreedySpannerRec (t :ℕ)[NeZero t]  (G : FinSimpleGraph n) (E_H :Set (Edge n))  (itr target:ℕ)   : FinSimpleGraph n :=
    if target ≤ itr then fromEdgeSet E_H
    else
    if h: G = emptyGraph (Fin n) then fromEdgeSet E_H
    else
      have Gnonempty: (edgeFinset G).toList ≠ [] := by
        simp only [ne_eq, toList_eq_nil, Set.toFinset_eq_empty, edgeSet_eq_empty]
        exact h
      let e := G.edgeFinset.toList.head Gnonempty
      let u := (Quot.out e).1
      let v := (Quot.out e).2
      let G' := G.deleteEdges {e}
      if h_dist: (2*t -1) < (fromEdgeSet E_H).dist u v then
        GreedySpannerRec t G' (E_H ∪ {e}) (itr+1) target
      else GreedySpannerRec t G' E_H (itr +1) target

    termination_by #G.edgeFinset decreasing_by all_goals (
      apply cardGDel_lt_cardG_of G
      apply mem_edgeFinset.mp
      apply mem_toList.mp
      exact List.head_mem Gnonempty
    )

noncomputable def FinSimpleGraph.IndexOfEdgeInG (G : FinSimpleGraph n) (e : Edge n) (h: e ∈ G.edgeSet) : ℕ :=
  let o := (G.edgeFinset.toList.indexOf? e)
  have: o.isSome := by
    simp [o,List.indexOf?]
    rw [List.findIdx?_isSome]
    aesop
  o.get this

--noncomputable def FinSimpleGraph.IndexOfEdge (G : FinSimpleGraph n) (e : Edge n) : ℕ := (G.edgeFinset.toList.indexOf e)

noncomputable def GreedySpanner   (G : FinSimpleGraph n) (t :ℕ)[NeZero t] :=
  GreedySpannerRec t G {} 0 #G.edgeFinset

noncomputable def GreedySpanner_itr   (G : FinSimpleGraph n) (t i:ℕ)[NeZero t]  :=
  GreedySpannerRec t G {} 0 i

lemma greedySpannerDistUBAtEdge (G : FinSimpleGraph n)(t :ℕ ) [NeZero t] {e : Edge n} (he: e ∈ G.edgeSet) :
  let H_i := GreedySpanner_itr G t (G.IndexOfEdgeInG e he)
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H_i.dist u v ≤ 2*t-1 := by sorry


lemma greedySpannerItrSubgraph(G : FinSimpleGraph n)(t i:ℕ ) [NeZero t]:
  let H_i := GreedySpanner_itr G t i
  let H := GreedySpanner G t
  H_i.IsSubgraph H := by sorry

lemma greedySpannerSubgraphOf(G : FinSimpleGraph n)(t :ℕ ) [NeZero t]:
  let H := GreedySpanner G t
  H.IsSubgraph G := by sorry

 def greedySpannerImperative  (G : FinSimpleGraph n) (t :ℕ )[NeZero t] : FinSimpleGraph n := Id.run do
  let mut f_H : BinarySqMatrix n := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < f_H.dist e then f_H := f_H.AddEdge e
  SimpleGraph.fromRel f_H

lemma GreedySpannerPreserveDistanceUB (G : FinSimpleGraph n)(t :ℕ ) [NeZero t] {e : Edge n} (he: e ∈ G.edgeSet) :
  let H := GreedySpanner G t
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H.dist u v ≤ 2*t-1  := by sorry

lemma GreedySpannerPreserveDistanceLB  (G : FinSimpleGraph n)(t :ℕ )[NeZero t] {e : Edge n} (he: e ∈ G.edgeSet) :
  let H := GreedySpanner G t
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  G.dist u v ≤ H.dist u v  := by sorry


lemma correctnessOfGreedySpanner (G : FinSimpleGraph n) (t : ℕ) [NeZero t]:
  let H := GreedySpanner G t
  H.IsSpannerOf G (2*t-1) := by sorry

lemma girthOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) [NeZero t] :
  let H := GreedySpanner G t
  2*t + 1 ≤ H.girth:= sorry

lemma sparsityOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) [NeZero t]:
  let H := GreedySpanner G t
  H.numEdges ≤ 100 * t * n * (NNReal.rpow ↑n (1/(↑t))) := sorry

noncomputable def FinSimpleGraph.numEdgesFin {n:ℕ}(G : FinSimpleGraph n): Fin (n*n+1) := ⟨#G.edgeFinset, num_edges_le_nn G⟩
noncomputable def minSpannerSize  {n:ℕ } (G : FinSimpleGraph n) (t:ℕ): Fin (n*n+1) := inf {H : FinSimpleGraph n | H.IsSpannerOf G t} numEdgesFin

theorem minSpannerSizeLe  {n:ℕ } (G : FinSimpleGraph n) (t:ℕ) :
  minSpannerSize G (2*t-1) ≤ 100 * t * n * (NNReal.rpow ↑n (1/(↑t))) := by sorry
