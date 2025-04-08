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
--import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

set_option autoImplicit false

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval NonTail.sum [1, 2, 3]

def Tail.sum (xs : List Nat) : Nat :=
  sumHelper 0 xs
  where sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

#eval Tail.sum [1,2,3]

theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sum.sumHelper n xs := by
  induction xs generalizing n with
  | nil =>
    rfl
  | cons y ys is =>
    simp [NonTail.sum,Tail.sum,Tail.sum.sumHelper]
    rw [← add_assoc]
    conv =>
      left
      left
      rw [add_comm]
    exact is (y + n)
  skip


theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil =>
    rfl
  | cons y ys is =>
    simp [NonTail.sum,Tail.sum,Tail.sum.sumHelper]
    exact helper_add_sum_accum ys y







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

--noncomputable instance  FinSimpleGraphBotInst (n :ℕ ):  Bot (FinSimpleGraph n) := by sorry

open FinSimpleGraph Std

def FinSimpleGraph.IsSpannerOf   (H G : FinSimpleGraph n)  (t:ℕ)  : Prop :=
  H.IsSubgraph G ∧ ∀ u v : Fin n, H.edist u v ≤ t * G.edist u v

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

-- fold operation
--
noncomputable def GreedySpanner (G : FinSimpleGraph n) (t :ℕ)[NeZero t] :=
  Rec t G {} 0 #G.edgeFinset
  where
  Rec (t :ℕ)[NeZero t]  (G : FinSimpleGraph n) (E_H :Set (Edge n))  (itr target:ℕ)   : FinSimpleGraph n :=
    if h: target ≤ itr ∨ G = emptyGraph (Fin n) then fromEdgeSet E_H
    else
      have Gnonempty: (edgeFinset G).toList ≠ [] := by
        simp only [ne_eq, toList_eq_nil, Set.toFinset_eq_empty, edgeSet_eq_empty]
        simp_all only [emptyGraph_eq_bot, not_or, not_le, not_false_eq_true]
      let e : Edge n := G.edgeFinset.toList.head Gnonempty
      let u := (Quot.out e).1
      let v := (Quot.out e).2
      let G' := G.deleteEdges {e}
      if (2*t -1) < (fromEdgeSet E_H).edist u v then
        Rec t G' (E_H ∪ {e}) (itr+1) target
      else Rec t G' E_H (itr +1) target

    termination_by #G.edgeFinset decreasing_by all_goals (
      apply cardGDel_lt_cardG_of G
      apply mem_edgeFinset.mp
      apply mem_toList.mp
      exact List.head_mem Gnonempty
    )


noncomputable def FinSimpleGraph.IndexOfEdgeInG' (G : FinSimpleGraph n) (e : Edge n) (h: e ∈ G.edgeSet) : ℕ :=
  let o := (G.edgeFinset.toList.indexOf? e)
  have: o.isSome := by
    simp [o,List.indexOf?]
    rw [List.findIdx?_isSome]
    aesop
  o.get this


noncomputable def FinSimpleGraph.IndexOfEdgeInG (G : FinSimpleGraph n) (e : Edge n) : ℕ := (G.edgeFinset.toList.indexOf e)


lemma  FinSimpleGraph.IndexOfEdgeZeroIsHead (G : FinSimpleGraph n) (Gnonempty: (edgeFinset G).toList ≠ []) (e : Edge n) (h1: e ∈ G.edgeSet) (h2: G.IndexOfEdgeInG e = 0) :
  e = (edgeFinset G).toList.head Gnonempty := by
  let e' : Edge n := (edgeFinset G).toList.head Gnonempty
  let l := (edgeFinset G).toList
  have e_inl: e ∈ l := by aesop
  have e'_inl: e' ∈ l := by aesop
  rw [← List.indexOf_inj e_inl e'_inl]
  simp [IndexOfEdgeInG] at h2
  have t1: List.indexOf e' l = 0 := by
    simp [List.indexOf,List.findIdx,List.findIdx.go]
    rw [List.findIdx.go.eq_def]
    aesop
  have t2: List.indexOf e l = 0 := by aesop
  simp [t1,t2]

--
--
--noncomputable def FinSimpleGraph.IndexOfEdge (G : FinSimpleGraph n) (e : Edge n) : ℕ := (G.edgeFinset.toList.indexOf e)

--noncomputable def GreedySpanner   (G : FinSimpleGraph n) (t :ℕ)[NeZero t] :=
--  GreedySpannerRec t G {} 0 #G.edgeFinset

noncomputable def GreedySpanner_itr   (G : FinSimpleGraph n) (t i:ℕ)[NeZero t]  :=
  GreedySpanner.Rec t G {} 0 i



lemma greedySpanneri_vs_i_plus'(G : FinSimpleGraph n)(t i:ℕ )(hi1: i < G.edgeFinset.toList.length) [NeZero t]:
  let H_i  := GreedySpanner.Rec t G {} 0 i --GreedySpanner_itr G t i
  let H := GreedySpanner G t
  let e := G.edgeFinset.toList.get ⟨i,hi1⟩
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  if (2*t -1) < H_i.edist u v then   e ∈ H.edgeSet
  else  e ∉ H.edgeSet :=  by
  sorry



#check Nat.twoStepInduction


lemma greedySpanneri_vs_i_plus(G : FinSimpleGraph n)(t i:ℕ )(hi1: i < G.edgeFinset.toList.length) [NeZero t]:
  let H_i  := GreedySpanner.Rec t G {} 0 i -- GreedySpanner_itr G t i
  let H_i2 := GreedySpanner.Rec t G {} 0 (i+1) --  GreedySpanner_itr G t (i+1)
  let e := G.edgeFinset.toList.get ⟨i,hi1⟩
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  if (2*t -1) < H_i.edist u v then   H_i2.edgeSet =  H_i.edgeSet ∪ {e}
  else  H_i = H_i2 :=  by

  extract_lets H_i H_i2 e u v

  have:= aux i (by rfl)
  extract_lets G' at this
  obtain ⟨E',⟨h1,h2⟩ ⟩ := this
  simp [H_i,H_i2]
  have: GreedySpanner.Rec t G' E' i i = fromEdgeSet E' := by
    simp [GreedySpanner.Rec]
  rw [this] at h1

  have G'_nonempty: ¬ (G' = (⊥ : SimpleGraph (Fin n))):= by sorry
  observe: ¬ (i+1 ≤ i)
  have non_base_p: ¬ (i+1 ≤ i ∨ G' = (⊥ : SimpleGraph (Fin n))) := by
    push_neg
    constructor
    omega
    exact G'_nonempty

--  have nonbase: ¬ (i ≤ i ∨ G' = emptyGraph (Fin n)):= by aesop
  conv at h2 =>
    right
    unfold GreedySpanner.Rec
    simp [non_base_p,G'_nonempty]

  have Gnonempty : (@edgeFinset (Fin n) G' G'.fintypeEdgeSet).toList ≠ []  := GreedySpanner.Rec.proof_1 G' i (i+1) (of_eq_false (eq_false non_base_p))
  have Gnonempty2 : G'.edgeFinset.toList ≠ [] := sorry

--  G_ih.edgeFinset.toList.head
  let e' := (@edgeFinset (Fin n) G' G'.fintypeEdgeSet).toList.head Gnonempty;
--     let e := G_ih.edgeFinset.toList.head Gnonempty;
  have eeqe': e = e' := sorry
  let u' := (Quot.out e').1;
  let v' := (Quot.out e').2;
  let G'' := G'.deleteEdges {e'}
  obtain ⟨uu',vv'⟩ : u = u' ∧ v = v' := sorry
--  obtain ⟨ ⟩ : u' = u ∧ v' = v ∧ G''

  by_cases h_distance: 2 * ↑t - 1 < (fromEdgeSet E').edist u' v'

  conv at h2 =>
    right
    unfold GreedySpanner.Rec
    simp [h_distance, e',u',v']



  rw [h1,uu',vv',eeqe']
  simp only [h_distance, ↓reduceIte, H_i, H_i2]
  rw [h2]
  simp only [e',edgeSet_fromEdgeSet, H_i, H_i2, insert,Set.insert]
  refine Set.ext ?_
  intro x
  constructor
  intro h
  aesop
  intro h
  simp
  simp at h
  obtain l | r := h
  constructor
  simp [l]
  refine Set.mem_setOf.mpr ?_
  left
  simp
  have: x ∈ G'.edgeFinset := sorry
  exact SimpleGraph.not_isDiag_of_mem_edgeFinset this
  obtain ⟨hr1,hr2⟩ := r
  refine ⟨?_ ,hr2⟩
  refine Set.mem_setOf.mpr ?_
  right
  exact hr1

  conv at h2 =>
    right
    unfold GreedySpanner.Rec
    simp [h_distance, e',u',v']

  rw [h1,uu',vv',eeqe']
  simp only [h_distance, ↓reduceIte, H_i, H_i2]
  rw [h2]




--  have: G'' = G' := sorry


 -- by_cases


  where
  aux (itr :ℕ) (h: itr ≤ i):
    let G' := fromEdgeSet (G.edgeFinset.toList.drop itr).toFinset.toSet
    ∃ E' : Set (Edge n),
    GreedySpanner.Rec t G {} 0 i     = GreedySpanner.Rec t G' E' itr i ∧  -- GreedySpanner_itr G t i
    GreedySpanner.Rec t G {} 0 (i+1) = GreedySpanner.Rec t G' E' itr (i+1) := by

   extract_lets G'
   induction itr with
   | zero =>
     have: G' = G := by aesop
     rw [this]
     use {}
   | succ itr ih =>
     observe: itr ≤ i
     replace ih:= ih this
     extract_lets G_ih at ih
     obtain ⟨E_ih,⟨ ih_itr_i, ih_itr_ip⟩⟩ := ih

     have Gih_nonempty: ¬ (G_ih = (⊥ : SimpleGraph (Fin n))):= by sorry
     observe: ¬ (i < itr)

     have non_base  : ¬ (i ≤ itr   ∨ G_ih = (⊥ : SimpleGraph (Fin n))) := by aesop
     have non_base_p: ¬ (i+1 ≤ itr ∨ G_ih = (⊥ : SimpleGraph (Fin n))) := by
      push_neg
      constructor
      omega
      exact Gih_nonempty


     have Gnonempty : (@edgeFinset (Fin n) G_ih G_ih.fintypeEdgeSet).toList ≠ []  := GreedySpanner.Rec.proof_1 G_ih itr i (of_eq_false (eq_false non_base))
   --  G_ih.edgeFinset.toList.head
     let e := (@edgeFinset (Fin n) G_ih G_ih.fintypeEdgeSet).toList.head Gnonempty;
--     let e := G_ih.edgeFinset.toList.head Gnonempty;
     let u := (Quot.out e).1
     let v := (Quot.out e).2
     let G'' := G_ih.deleteEdges {e}
     have: G'' = G' := sorry

     conv at ih_itr_i =>
      right
      unfold GreedySpanner.Rec
      simp [non_base]

     conv at ih_itr_ip =>
      right
      unfold GreedySpanner.Rec
      simp [non_base_p]

     by_cases h_distance: 2 * ↑t - 1 < (fromEdgeSet E_ih).edist u v
     ·
      simp [h_distance,u,v,e] at ih_itr_i
      simp [h_distance,u,v,e] at ih_itr_ip

      use (insert e E_ih)
      exact ⟨by aesop, by aesop⟩
     ·
      simp [h_distance,u,v,e] at ih_itr_i
      simp [h_distance,u,v,e] at ih_itr_ip
      use E_ih
      exact ⟨by aesop, by aesop⟩

lemma greedySpannerItrSubgraph(G : FinSimpleGraph n)(t i:ℕ ) [NeZero t]:
  let H_i := GreedySpanner_itr G t i
  let H_i2 := GreedySpanner_itr G t (i+1)
  H_i.IsSubgraph H_i2 := by

  simp [GreedySpanner_itr]

  induction G, ({}: Set (Edge n)), 0, i using GreedySpanner.Rec.induct t with
  | case1 G_aux E_H_aux itr target h =>
      obtain target_leq_itr | G_aux_eq_bot := h
      swap
      · conv =>
          conv =>
            left
            simp [G_aux_eq_bot, GreedySpanner.Rec]
          conv =>
            right
            simp [G_aux_eq_bot,GreedySpanner.Rec]

      · replace h:= target_leq_itr
        conv =>
          left
          unfold GreedySpanner.Rec
          simp [h]

        unfold GreedySpanner.Rec
        by_cases h2: G_aux = emptyGraph (Fin n)
        · simp [h2]
        by_cases h1: target +1 ≤ itr
        ·
          simp [h1]
        ·
          have Gnotbot: G_aux ≠ (⊥ : SimpleGraph (Fin n)) := by aesop
          have nottarget: ¬ (target +1 ≤ itr) := by  aesop
          have H : ¬ ( target + 1 ≤ itr ∨ G_aux = emptyGraph (Fin n) ) := by aesop

          simp only [nottarget, emptyGraph_eq_bot, Gnotbot, or_self, ↓reduceDIte, ge_iff_le]

          have Gnonempty:  (edgeFinset G_aux).toList ≠ [] := GreedySpanner.Rec.proof_1 G_aux itr (target+1) H
          simp [Gnotbot]

          let e := (edgeFinset G_aux).toList.head Gnonempty;
          let u := (Quot.out e).1;
          let v := (Quot.out e).2;

          by_cases h3: 2 * t - 1 <  (fromEdgeSet E_H_aux).edist u v
          · -- case 2.2.1
            simp [h3,e,u,v]
            unfold GreedySpanner.Rec
            simp [h]
            refine fromEdgeSet_mono ?_
            aesop
          · -- case 2.2.2
            simp [h3,e,u,v]
            unfold GreedySpanner.Rec
            simp [h]

  | case2 G_aux E_H itr target h1 Gnonempty e u v =>
    rename_i h3 h4
    have Gnotbot: G_aux ≠ (⊥ : SimpleGraph (Fin n)) := by aesop
    have H: ¬ (target ≤ itr) := by aesop
    have H': ¬ (target +1 ≤ itr) := by omega

    conv =>
      conv =>
        left
        unfold GreedySpanner.Rec
        simp [Gnotbot,h1, h3, Gnonempty,u,v,e,H]
        change (GreedySpanner.Rec t (deleteEdges G_aux {e}) (insert (e) E_H) (itr+1) target)

      conv =>
        right
        unfold GreedySpanner.Rec
        simp
        simp [Gnotbot,h1, H', h3, Gnonempty,u,v,e,H]
        change (GreedySpanner.Rec t (deleteEdges G_aux {e}) (insert (e) E_H) (itr+1) (target+1))

    aesop

  | case3 G_aux E_H itr target h1 Gnonempty e u v =>
    rename_i h3 h4

    have Gnotbot: G_aux ≠ (⊥ : SimpleGraph (Fin n)) := by aesop
--    have h5: ¬ (target + 2 ≤ itr) := by omega

    have H: ¬ (target ≤ itr) := by aesop
    have H': ¬ (target +1 ≤ itr) := by omega

    conv =>
      conv =>
        left
        unfold GreedySpanner.Rec
        simp [Gnotbot,h1, H, h3, Gnonempty,u,v,e]
        change (GreedySpanner.Rec t (deleteEdges G_aux {e}) E_H (itr+1) target)

      conv =>
        right
        unfold GreedySpanner.Rec
        simp [Gnotbot,h1, H', h3, Gnonempty,u,v,e]
        change (GreedySpanner.Rec t (deleteEdges G_aux {e}) (E_H) (itr+1) (target+1))
    aesop


lemma greedySpannerDistUBAtEdge (G : FinSimpleGraph n)(hG: G.Connected)(t :ℕ ) [NeZero t] {e : Edge n} (he: e ∈ G.edgeSet) :
  let H_i := GreedySpanner_itr G t (G.IndexOfEdgeInG e)
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H_i.edist u v ≤ 2*t-1 := by

  sorry

--   --have obst: 0 < t := by exact Nat.pos_of_neZero t
--   observe obs_t: 0 < t

--   extract_lets H_i u v
--   by_cases h_idx: ((G.IndexOfEdgeInG e) = 0)
--   · -- h_inx = 0
--     unfold H_i GreedySpanner_itr GreedySpannerRec
--     by_cases h2: G = emptyGraph (Fin n)
--     · -- case 2.1
--       have: ¬ (⊥ : SimpleGraph (Fin n)).Connected := by aesop
--       aesop

--     · -- case 2.2
--       have Gnotbot: G ≠ (⊥ : SimpleGraph (Fin n)) := by aesop
--       simp [h2,Gnotbot]

--       have Gnonempty:  (edgeFinset G).toList ≠ [] := GreedySpannerRec.proof_1 G (Eq.mpr_not (Eq.refl (G = (emptyGraph (Fin n)))) (of_eq_false (eq_false Gnotbot)))
--       simp [Gnotbot]

--       let e' : Edge n := (edgeFinset G).toList.head Gnonempty;
--       let u' := (Quot.out e').1
--       let v' := (Quot.out e').2

--       have eeqe: e = e' := by exact IndexOfEdgeZeroIsHead G Gnonempty e he h_idx
--       have uu' : u = u' := by aesop
--       have vv' : v = v' := by aesop
--       have h_idx': G.IndexOfEdgeInG ((edgeFinset G).toList.head Gnonempty) = 0 := by aesop
--       have h3: 2*t -1 < (fromEdgeSet {}).edist u' v' := by
--         have: (fromEdgeSet {}).edist u' v' = ⊤ := by
--           refine edist_eq_top_of_not_reachable ?_
--           simp only [fromEdgeSet_empty, reachable_bot]
--           rw [← uu',←  vv']
--           have : e = s(u,v) := by aesop
--           have: G.Adj u v := by
--             refine (mem_edgeSet G).mp ?_
--             aesop
--           aesop
--         rw [this]
--         exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
--       simp only [h3, ↓reduceIte, eeqe, ge_iff_le, e', v', u']
--       unfold GreedySpannerRec
--       simp only [h_idx', zero_add, le_refl, ↓reduceIte, e', v', u']
--       show (fromEdgeSet {e'}).edist u v ≤ 2 * ↑t - 1
--       rw [← eeqe]
--       have: (fromEdgeSet {e}).edist u v = 1 := by
--         refine edist_eq_one_iff_adj.mpr ?_
--         aesop
--       rw [this]
--       refine ENat.le_sub_of_add_le_left ?_ ?_
--       aesop
--       ring_nf
--       refine le_mul_of_one_le_left' ?_
--       exact Nat.one_le_cast.mpr obs_t

--   · -- h_indx > 0
--     let H_i_minus := GreedySpanner_itr G t ((G.IndexOfEdgeInG e)-1)
--     have hgindex: G.IndexOfEdgeInG e - 1 + 1 =  G.IndexOfEdgeInG e := by  rw [Nat.sub_one_add_one h_idx]
--     by_cases h_i_minus_dist: H_i_minus.edist u v ≤ 2*t - 1
--     · -- small dist
--       have H_i_minus_subgraph_H_i: H_i_minus.IsSubgraph H_i := by
--         have:= greedySpannerItrSubgraph G t ((G.IndexOfEdgeInG e)-1)
--         simp only at this
--         conv at this =>
--           enter [2,3]
--           simp [hgindex]
--         aesop

--       have ureachv: H_i_minus.Reachable u v := by
--         refine edist_ne_top_iff_reachable.mp ?_
--         have: (2 * ↑t - 1 : ENat ) < ⊤ := by exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
--         aesop
-- --        rw [SimpleGraph.connected_iff_exists_forall_reachable] at hG
-- --        obtain ⟨r,hr⟩ := hG
-- --        have ru: G.Reachable r u := by exact hr u
-- --       have rv: G.Reachable r v := by exact hr v
-- --        exact Reachable.trans (id (Reachable.symm ru)) (hr v)
--       calc
--         SimpleGraph.edist H_i u v ≤  SimpleGraph.edist H_i_minus u v  := SimpleGraph.edist_anti H_i_minus_subgraph_H_i
--         _ ≤ 2 * ↑t - 1  := h_i_minus_dist
--     · -- large dist
--       sorry

lemma greedySpannerSubgraphOf(G : FinSimpleGraph n)(t :ℕ ) [NeZero t]:
  let H := GreedySpanner G t
  H.IsSubgraph G := by sorry

 def greedySpannerImperative  (G : FinSimpleGraph n) (t :ℕ )[NeZero t] : FinSimpleGraph n := Id.run do
  let mut f_H : BinarySqMatrix n := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < f_H.dist e then f_H := f_H.AddEdge e
  SimpleGraph.fromRel f_H

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
