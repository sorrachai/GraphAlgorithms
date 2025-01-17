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

def Edge n:= Sym2 (Fin n)

@[ext, aesop safe constructors (rule_sets := [SimpleGraph])]
structure WeightedSimpleGraph (V : Type u) [Fintype V] extends SimpleGraph V  where
  w: V → V → ℕ
  AdjAndWeight : ∀ u v : V, w u v > 0 ↔ Adj u v --:= by aesop_graph

def FinSimpleGraph (n : ℕ) := SimpleGraph (Fin n)

@[ext] theorem FinSimpleGraph.ext {n : ℕ} {G H : FinSimpleGraph n} (h: G.Adj = H.Adj): G = H := by
  cases G; cases H
  simp only [SimpleGraph.mk] at h
  subst h
  rfl

@[simps]
def FinSimpleGraph.mk' {n : ℕ}:
    {adj : Fin n → Fin n → Prop // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ FinSimpleGraph n where
  toFun x := ⟨fun v w ↦ x.1 v w, fun v w ↦ by simp [x.2.1], fun v ↦ by simp [x.2.2]⟩
  inj' := by
    rintro ⟨adj, p1⟩ ⟨adj', p2⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    contrapose!
    intro h
    simp only [ne_eq, SimpleGraph.mk.injEq]
    exact h
--noncomputable instance  FinSimpleGraphMaxInst (n :ℕ ): Max (FinSimpleGraph n) := by exact { max := fun a b ↦ (a : SimpleGraph (Fin n) ⊓ (b : SimpleGraph (Fin n)}

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

--noncomputable instance  FinSimpleGraphEdgeSetInst (n :ℕ ) (G : FinSimpleGraph n): Fintype G.edgeSet := G.fintypeEdgeSet
--noncomputable instance  FinOrderTopInst (n :ℕ )[NeZero n]: OrderTop (Fin n) := by refine WellFoundedGT.toOrderTop

open FinSimpleGraph Std

def FinSimpleGraph.IsSpannerOf {n:ℕ } (H G : FinSimpleGraph n)  (t:ℕ)  : Prop :=
  H.IsSubgraph G ∧ ∀ u v : Fin n, H.dist u v ≤ t * G.dist u v ∧ G.dist u v ≤ H.dist u v

lemma num_edges_le_nn {n :ℕ}  (G :FinSimpleGraph n):  #G.edgeFinset < n*n+1:= by
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

noncomputable def FinSimpleGraph.numEdges {n : ℕ}(G : FinSimpleGraph n) : ℕ := #G.edgeFinset
noncomputable def exGirth (n t:ℕ)  : ℕ := sup {H : FinSimpleGraph n | 2*t + 1 ≤ H.girth } numEdges

lemma exGirthUB (n t:ℕ) : exGirth n t ≤ 100 * n * (NNReal.rpow ↑n (1/(↑t))) := sorry


def BinarySqMatrix.AddEdge {n :ℕ}(M : BinarySqMatrix n) ( e : Sym2 (Fin n) ):
 Fin n → Fin n → Prop := fun (i j : Fin n) ↦ M i j ∨ (e = s(i,j))

noncomputable def BinarySqMatrix.dist {n :ℕ}(M : BinarySqMatrix n) (e : Sym2 (Fin n)): ℕ
:= (SimpleGraph.fromRel M).dist (Quot.out e).1 (Quot.out e).2


lemma cardGDel_lt_cardG_of{n : ℕ }(G : FinSimpleGraph n) { E : Set (Edge n)} (h_subset: E ⊆ G.edgeSet) (h: E.Nonempty):
  let G' := G.deleteEdges E
  #G'.edgeFinset < #G.edgeFinset := by

  extract_lets G'
  suffices G'.edgeFinset ⊂ G.edgeFinset from card_lt_card this

  simp only [Set.ssubset_toFinset, Set.coe_toFinset, edgeSet_ssubset_edgeSet]
  simp [G',deleteEdges]

  refine sdiff_lt ?_ ?_
  · show fromEdgeSet E ≤ G
    refine edgeFinset_subset_edgeFinset.mp ?_
    dsimp [Set.subset_toFinset, Set.coe_toFinset, edgeSet_fromEdgeSet]
    intro x hx
    aesop

  · show fromEdgeSet E ≠ ⊥
    by_contra! empty
    rw [← SimpleGraph.edgeSet_eq_empty] at empty
    simp at empty
    rw [@Set.diff_eq_empty] at empty
    replace empty: ∀ e ∈ E, e.IsDiag := by aesop
    let e := h.some
    have  einE:= Set.Nonempty.some_mem h
    suffices ¬ e.IsDiag by
      have: Sym2.IsDiag e := by exact empty e einE
      contradiction
    refine G.not_isDiag_of_mem_edgeSet ?_
    exact h_subset einE

lemma cardGDele_lt_cardG_of{n : ℕ }(G : FinSimpleGraph n) {e : Sym2 (Fin n)} (h: e ∈ G.edgeSet):
  let G' := G.deleteEdges {e}
  #G'.edgeFinset < #G.edgeFinset := by apply cardGDel_lt_cardG_of;aesop; aesop

noncomputable def GreedySpannerRec {n :ℕ } (G : FinSimpleGraph n) (H :Set (Edge n)) (t :ℕ) : FinSimpleGraph n :=
  if h: G = emptyGraph (Fin n) then fromEdgeSet H
  else
    have Gnonempty: (edgeFinset G).toList ≠ [] := by
      simp only [ne_eq, toList_eq_nil, Set.toFinset_eq_empty, edgeSet_eq_empty]
      exact h
    let e := G.edgeFinset.toList.head Gnonempty
    let u := (Quot.out e).1
    let v := (Quot.out e).2
    let G' := G.deleteEdges {e}
    if h_dist: (2*t -1) < (fromEdgeSet H).dist u v then
      GreedySpannerRec G' (H ∪ {e}) t
    else GreedySpannerRec G' H t

  termination_by #G.edgeFinset decreasing_by all_goals (
    apply cardGDele_lt_cardG_of G
    apply mem_edgeFinset.mp
    apply mem_toList.mp
    exact List.head_mem Gnonempty
  )

noncomputable def GreedySpanner {n :ℕ } (G : FinSimpleGraph n) (t :ℕ) := GreedySpannerRec G {} t

 def greedySpannerImperative {n:ℕ }(G : FinSimpleGraph n) (t :ℕ ): FinSimpleGraph n := Id.run do
  let mut f_H : BinarySqMatrix n := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < f_H.dist e then f_H := f_H.AddEdge e
  SimpleGraph.fromRel f_H


lemma GreedySpannerPreserveDistanceLB {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) (u v : Fin n) :
  let H := GreedySpanner G t
  G.dist u v ≤ H.dist u v  := by sorry

lemma GreedySpannerPreserveDistanceUB {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) (u v : Fin n) :
  let H := GreedySpanner G t
  H.dist u v ≤ 2*t-1 := by sorry

lemma correctnessOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) :
  let H := GreedySpanner G t
  H.IsSpannerOf G (2*t-1) := by sorry

lemma girthOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) :
  let H := GreedySpanner G t
  2*t + 1 ≤ H.girth:= sorry

lemma sparsityOfGreedySpanner {n:ℕ }(G : FinSimpleGraph n)(t :ℕ ) :
  let H := GreedySpanner G t
  H.numEdges ≤ 100 * t * n * (NNReal.rpow ↑n (1/(↑t))) := sorry

noncomputable def FinSimpleGraph.numEdgesFin {n:ℕ}(G : FinSimpleGraph n): Fin (n*n+1) := ⟨#G.edgeFinset, num_edges_le_nn G⟩
noncomputable def minSpannerSize  {n:ℕ } (G : FinSimpleGraph n) (t:ℕ): Fin (n*n+1) := inf {H : FinSimpleGraph n | H.IsSpannerOf G t} numEdgesFin

theorem minSpannerSizeLe  {n:ℕ } (G : FinSimpleGraph n) (t:ℕ) :
  minSpannerSize G (2*t-1) ≤ 100 * t * n * (NNReal.rpow ↑n (1/(↑t))) := by sorry
