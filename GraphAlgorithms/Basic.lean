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
import «GraphAlgorithms».PreMathlib
--import Mathlib.Data.Fin.Rev



--#check Sym2.Mem.other
--import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
set_option maxHeartbeats 500000
set_option autoImplicit false

open Classical
universe u u'

def BinaryMatrix' (m : Type u) (n : Type u') := Matrix m n Prop
def BinaryMatrix (m n: ℕ ) := BinaryMatrix' (Fin m) (Fin n)
def BinarySqMatrix (n: ℕ ) := BinaryMatrix n n

--import Mathlib.Data.Nat.Choose.Basic -- Need this for n.choose and related lemmas

lemma two_mul_choose_two_cancel' (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right n] -- State: 2 * (n * (n - 1) / 2) = n * (n - 1)

  -- Prove explicitly that 2 divides n * (n - 1)
  have h_div : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with h_even | h_odd -- Split proof based on parity of n
    · -- Case 1: n is even
      -- If n is even, then 2 ∣ n.
      -- If 2 ∣ n, then 2 ∣ n * m for any m.
      apply dvd_mul_of_dvd_left -- Use the tactic: if a ∣ b, then a ∣ b * c
      -- We need to supply the proof that 2 ∣ n.
      -- The definition of Even n is n % 2 = 0. The lemma `Nat.even_iff_two_dvd` converts this to 2 ∣ n.
      exact even_iff_two_dvd.mp h_even
--      exact even_iff_two_dvd.mp h_even
    · -- Case 2: n is odd
      -- If n is odd, then n - 1 is even, so 2 ∣ (n - 1).
      -- If 2 ∣ (n - 1), then 2 ∣ m * (n - 1) for any m.
      apply dvd_mul_of_dvd_right -- Use the tactic: if a ∣ c, then a ∣ b * c
      -- We need to supply the proof that 2 ∣ (n - 1).
      -- If n is Odd, we know `n = 2*k + 1` for some k.
      rw [odd_iff_exists_bit1] at h_odd -- Converts Odd n to ∃ k, n = 2*k + 1
      rcases h_odd with ⟨k, rfl⟩ -- Introduce k and substitute n = 2*k + 1
      -- The goal is now to prove 2 ∣ (2*k + 1) - 1
      simp only [Nat.add_sub_cancel] -- Simplifies (2*k + 1) - 1 to 2*k. Goal: 2 ∣ 2*k
      -- Use the basic divisibility property a ∣ a * b
      exact Nat.dvd_mul_right 2 k

  -- Now that h_div (the proof of 2 ∣ n * (n - 1)) is established, use it.
  rw [Nat.mul_div_cancel' h_div] -- Applies lemma k * (m / k) = m, given k ∣ m.
                                 -- State: n * (n - 1) = n * (n - 1)
  -- The goal is now trivial (reflexivity) and should be closed automatically by rw.


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
noncomputable def exGirth (n t:ℕ) [NeZero n]  : ℕ := sup {H : FinSimpleGraph n | 2*t + 1 ≤ H.girth } numEdges

lemma exGirthUB (n t:ℕ) [NeZero n]: exGirth n t ≤ 100 * n * (NNReal.rpow ↑n (1/(↑t))) := sorry

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


-- -- A nice lemma to prove, but no need for now.
-- lemma cardGDel_eq_cardG_minus_of (G : FinSimpleGraph n) {E : Finset (Edge n)} (h: E ⊆  G.edgeFinset) :
-- let G' := G.deleteEdges (E : Set (Edge n))
-- #G'.edgeFinset = #G.edgeFinset - #E := by sorry

-- fold operation
--instance instBoundedOrder [NeZero n]: OrderTop (Fin n) := Fintype.toOrderTop (Fin n)

def lex : Sym2 (Fin n) → Sym2 (Fin n) → Prop := fun x ↦ fun y ↦  x.inf < y.inf ∨ (x.inf = y.inf ∧ x.sup ≤ y.sup) --x.inf + x.sup*(n) ≤ y.inf + y.sup*(n)

noncomputable instance IsTransSym2 (n:ℕ):  IsTrans (Sym2 (Fin n)) lex := by
  refine { trans := ?_ }
  intro a b c hab hbc
  simp_all [lex]
  by_cases abinf: a.inf < b.inf <;> by_cases bcinf: b.inf < c.inf
  · simp_all
    left
    exact Fin.lt_trans abinf bcinf
  · aesop
  · simp_all
  · simp [abinf] at hab
    simp [bcinf] at hbc
    right
    constructor
    aesop
    replace hab:= hab.right
    replace hbc:= hbc.right
    exact Fin.le_trans hab hbc

noncomputable instance IsAntisymmSym2 (n:ℕ):  IsAntisymm (Sym2 (Fin n)) lex := by
  refine { antisymm := ?_ }
  intro a b h1 h2
  simp_all [lex]
  by_cases h_lt: a.inf < b.inf
  simp_all
  observe: ¬ (b.inf < a.inf)
  simp [this] at h2
  aesop
  obtain H | H' : a.inf = b.inf ∨ b.inf < a.inf  := by exact eq_or_lt_of_not_lt h_lt
  swap
  aesop
  simp_all
  observe: a.sup = b.sup
  rw [← @inf_eq_inf_and_sup_eq_sup]
  exact And.symm ⟨this, H⟩

noncomputable instance IsTotalSym2 (n:ℕ):  IsTotal (Sym2 (Fin n)) lex := by
  refine { total := ?_ }
  intro a b
  by_cases h: lex a b
  exact Or.symm (Or.inr h)
  right
  simp [lex] at h
  simp [lex]
  obtain ⟨h1,h2⟩ := h
  by_cases h:b.inf < a.inf
  left
  exact h
  push_neg at h
  right
  constructor
  aesop (add unsafe Fin.le_antisymm)
  have: b.sup < a.sup := by aesop (add unsafe Fin.le_antisymm)
  exact Fin.le_of_lt this



noncomputable def GreedySpanner (G : FinSimpleGraph n) (t :ℕ)[NeZero t] :=
  Rec t G {} 0 #G.edgeFinset
  where
  Rec (t :ℕ)[NeZero t]  (G : FinSimpleGraph n) (E_H :Set (Edge n))  (itr target:ℕ)   : FinSimpleGraph n :=
    if h: target ≤ itr ∨ G = emptyGraph (Fin n) then fromEdgeSet E_H
    else
      have G_sort_non_empty :sort lex (edgeFinset G) ≠ []:= by
        rw [← @List.toFinset_nonempty_iff]
        aesop
      let e : Edge n := (G.edgeFinset.sort lex).head G_sort_non_empty
      let u := (Quot.out e).1
      let v := (Quot.out e).2
      let G' := G.deleteEdges {e}
      if (2*t -1) < (fromEdgeSet E_H).edist u v then
        Rec t G' (E_H ∪ {e}) (itr+1) target
      else Rec t G' E_H (itr +1) target

    termination_by #G.edgeFinset decreasing_by all_goals (
      apply cardGDel_lt_cardG_of G
      apply mem_edgeFinset.mp
      rw [← Finset.mem_sort lex]
      exact List.head_mem G_sort_non_empty
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

lemma  insert_an_edge_diff_ordering (E : Set (Edge n)) {e : Edge n} (h1: ¬e.IsDiag)
: (fromEdgeSet ({e} ∪ E)).edgeSet = {e} ∪ (fromEdgeSet E).edgeSet := by
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
  exact Eq.mpr_not (congrArg Sym2.IsDiag l) h1
  obtain ⟨hr1,hr2⟩ := r
  refine ⟨?_ ,hr2⟩
  refine Set.mem_setOf.mpr ?_
  right
  exact hr1

lemma G_list_non_empty_of_drop_lt_num_edges {G : FinSimpleGraph n}{i : ℕ }(h: i < G.edgeFinset.toList.length):
   (G.edgeFinset.toList.drop i) ≠ [] := by simp_all only [length_toList, Set.toFinset_card, Fintype.card_ofFinset,
     ne_eq, List.drop_eq_nil_iff, not_le]

lemma G_non_empty_of_drop_lt_num_edges (G : FinSimpleGraph n){i : ℕ }(h: i < G.edgeFinset.toList.length):
  fromEdgeSet (G.edgeFinset.toList.drop i).toFinset.toSet ≠ (⊥ : SimpleGraph (Fin n)) := by

  have drop_nonempty_list: (edgeFinset G).toList.drop i ≠ [] := by aesop
  have drop_nonempty: ((edgeFinset G).toList.drop i).toFinset ≠ {} := by aesop
  refine edgeSet_nonempty.mp ?_
  rw [@edgeSet_fromEdgeSet]

  have H': ∀ e ∈ (List.drop i (edgeFinset G).toList).toFinset, ¬e.IsDiag := by
    intro e he
    suffices e ∈ G.edgeFinset from  SimpleGraph.not_isDiag_of_mem_edgeFinset this
    refine mem_toList.mp ?_
    rw [@List.mem_toFinset] at he
    exact List.mem_of_mem_drop he

  have: ((edgeFinset G).toList.drop i).toFinset \ ({e : Edge n| e.IsDiag} : Finset (Sym2 (Fin n)) ) ≠ {} := by
    let e' := (List.drop i (edgeFinset G).toList).head drop_nonempty_list
    have: e' ∈ (List.drop i (edgeFinset G).toList).toFinset := by
      rw [@List.mem_toFinset]
      exact List.head_mem drop_nonempty_list
    have e'_not_diag: ¬ e'.IsDiag :=  H' e' this
    have e'_not_in_diag_set: e' ∉ ({ e : Sym2 (Fin n) | e.IsDiag} : Finset (Sym2 (Fin n))):= by
      rw [@mem_filter]
      push_neg
      intro h
      exact H' e' this
    have: e' ∈ ((List.drop i (edgeFinset G).toList).toFinset  \ ({ e : Sym2 (Fin n) | e.IsDiag} : Finset (Sym2 (Fin n)))  ) := by
      refine mem_sdiff.mpr ?_
      exact Decidable.not_imp_iff_and_not.mp fun a ↦ e'_not_in_diag_set (a this)
    exact ne_empty_of_mem this

  convert this
  constructor
  · intro h1
    aesop
  · intro h2
    refine Set.diff_nonempty.mpr ?_
    refine Set.not_subset.mpr ?_
    let e := ((edgeFinset G).toList.drop i).head drop_nonempty_list

    use e
    constructor
    · have: e ∈ ↑(List.drop i (edgeFinset G).toList).toFinset ↔ e ∈ ↑(List.drop i (edgeFinset G).toList) :=  List.mem_toFinset
      rw [@mem_coe]
      rw [this]
      exact List.head_mem drop_nonempty_list
    · suffices e ∈ (List.drop i (edgeFinset G).toList).toFinset from H' e this
      rw [@List.mem_toFinset]
      exact List.head_mem drop_nonempty_list

lemma G_lex_list_non_empty_of_drop_lt_num_edges {G : FinSimpleGraph n}{i : ℕ }(h: i < (G.edgeFinset.sort lex).length):
   ((G.edgeFinset.sort lex).drop i) ≠ [] := by simp_all only [length_toList, Set.toFinset_card, Fintype.card_ofFinset,
     ne_eq, List.drop_eq_nil_iff, not_le]

lemma G_lex_non_empty_of_drop_lt_num_edges (G : FinSimpleGraph n){i : ℕ }(h: i < (G.edgeFinset.sort lex).length):
  fromEdgeSet ((G.edgeFinset.sort lex).drop i).toFinset.toSet ≠ (⊥ : SimpleGraph (Fin n)) := by sorry

/- lemma G_ip_eq_G_i_minus_e (G :FinSimpleGraph n){i : ℕ} (h: i < G.edgeFinset.toList.length):
  let G_i : SimpleGraph (Fin n) := fromEdgeSet ↑(List.drop i (edgeFinset G).toList).toFinset;
  have Gnonempty:  G_i.edgeFinset.toList ≠ [] := by
    have: G_i ≠ (⊥ : SimpleGraph (Fin n)) := by exact G_non_empty_of_drop_lt_num_edges G h
    rw [← @edgeFinset_nonempty] at this
    exact Nonempty.toList_ne_nil this
  let e : Sym2 (Fin n) := G_i.edgeFinset.toList.head Gnonempty;
  let G_i_minus_e  : SimpleGraph (Fin n) := G_i.deleteEdges {e};
  let G_ip : SimpleGraph (Fin n) := fromEdgeSet ↑(List.drop (i + 1) (edgeFinset G).toList).toFinset;
  G_ip = G_i_minus_e  := sorry-/

     -- this : G'' = G'

--lemma sort_drop_sort_eq_drop_sort (s : Finset α) (i:ℕ):
--sort r ((s.sort r).drop i).toFinset = (s.sort r).drop i := sorry

lemma fromEdgeSet_edgeFinset_cancel {V : Type u} {s : Finset (Sym2 V)}: (fromEdgeSet ↑s).edgeFinset = s := sorry

noncomputable def list_Gi (G : FinSimpleGraph n)(i :ℕ ) : List (Sym2 (Fin n)) := ((edgeFinset G).sort lex).drop i
def Gi (G : FinSimpleGraph n)(i :ℕ ) : SimpleGraph (Fin n) := fromEdgeSet (list_Gi G i).toFinset

lemma  aux (G : FinSimpleGraph n)(i : ℕ)(h1: list_Gi G i ≠ [])(h2:(Gi G i).edgeFinset.sort lex ≠ [] ):
          ((Gi G i).edgeFinset.sort lex).head h2 = (list_Gi G i).head h1:= by

    have simp1: (Gi G i).edgeFinset =  (list_Gi G i).toFinset := by convert fromEdgeSet_edgeFinset_cancel
    have simp2: ((Gi G i).edgeFinset.sort lex) =  ((list_Gi G i).toFinset.sort lex) := by exact congrArg (sort lex) simp1
    have h3: ((list_Gi G i).toFinset.sort lex) ≠ [] := Ne.symm (ne_of_ne_of_eq (id (Ne.symm h2)) simp2)
    have simp3: ((Gi G i).edgeFinset.sort lex).head h2 =  ((list_Gi G i).toFinset.sort lex).head h3 := by simp_all only [ne_eq]
    rw [simp3]
    suffices sort lex (list_Gi G i).toFinset = list_Gi G i by aesop
    rw [list_Gi]
    exact sort_drop_sort_eq_drop_sort lex (edgeFinset G) i

lemma greedySpanneri_vs_i_plus_aux (G : FinSimpleGraph n)(t i:ℕ ) [NeZero t](itr :ℕ) (h: itr ≤ i) (hi1: i < (G.edgeFinset.sort lex).length):
    let G' := fromEdgeSet ((G.edgeFinset.sort lex).drop itr).toFinset.toSet
    ∃ E' : Set (Edge n),
    GreedySpanner.Rec t G {} 0 i     = GreedySpanner.Rec t G' E' itr i ∧  --
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

     have Gih_nonempty: ¬ (G_ih = (⊥ : SimpleGraph (Fin n))):= G_lex_non_empty_of_drop_lt_num_edges G (Nat.lt_of_le_of_lt this hi1)

     observe iltitr: ¬ (i < itr)

     have non_base  : ¬ (i ≤ itr   ∨ G_ih = (⊥ : SimpleGraph (Fin n))) := by aesop
     have non_base_p: ¬ (i+1 ≤ itr ∨ G_ih = (⊥ : SimpleGraph (Fin n))) := by
      push_neg
      constructor
      omega
      exact Gih_nonempty

     have Gnonempty : (@edgeFinset (Fin n) G_ih G_ih.fintypeEdgeSet).sort lex ≠ []  := GreedySpanner.Rec.proof_1 G_ih itr i (of_eq_false (eq_false non_base))
--
     let e := ((@edgeFinset (Fin n) G_ih G_ih.fintypeEdgeSet).sort lex).head Gnonempty;
--
     let u := (Quot.out e).1
     let v := (Quot.out e).2
     let G'' := G_ih.deleteEdges {e}
     have: G'' = G' := by

      ext x y
      let l1 := ((edgeFinset G).sort lex).drop itr
      have l1_non_empty_list : l1 ≠ [] := by
        have itr_lt_G_length: itr < ((edgeFinset G).sort lex).length := by exact  Nat.lt_of_le_of_lt this hi1
        exact G_lex_list_non_empty_of_drop_lt_num_edges itr_lt_G_length --G_list_non_empty_of_drop_lt_num_edges itr_lt_G_length
      let l1p := ((edgeFinset G).sort lex).drop (itr+1)
      have l1_nodup: l1.Nodup := by
        have list_from_G_nodup := (edgeFinset G).sort_nodup lex
        have l1_subseteq_list_from_G: l1.Sublist ((edgeFinset G).sort lex) := by exact List.drop_sublist itr (sort lex (edgeFinset G))--List.drop_sublist itr ((edgeFinset G).sort lex)--List.drop_subset itr (edgeFinset G).toList
        exact List.Sublist.nodup l1_subseteq_list_from_G list_from_G_nodup

      let le : List (Sym2 (Fin n)):= [e]

      have ldrop_eq_l1diffl2 :  l1p = l1.diff le := by
        let e' := l1.head l1_non_empty_list
        suffices ee': e = e' by
          simp [l1p,le]
          rw [← List.drop_drop]
          change List.drop 1 (l1) = l1.erase e
          rw [@List.drop_one]
          have H0:= List.head_cons_tail l1 l1_non_empty_list
          change e' :: l1.tail = l1 at H0
          have H1: l1.erase e' = l1.tail := by
            rw [← H0]
            simp only [List.erase_cons_head, List.tail_cons, l1p, le]
          rw [← H1,ee']

        simp [e,e',l1,G_ih]
        have:= aux G itr ?_ ?_
        simpa [list_Gi,Gi,l1,G_ih,l1_non_empty_list,Gnonempty]
        aesop
        dsimp [Gi]
        aesop

      constructor
      · simp [G',G'']
        intro h1 h2
        have xyinl1: s(x,y) ∈  l1 := by aesop_graph
        have xyinl1_minus_e: s(x,y) ∈  l1.diff le := by
           have: s(x,y) ∈ l1.diff le ↔ s(x,y) ∈ l1 ∧ s(x,y) ∉ le  := List.Nodup.mem_diff_iff l1_nodup
           rw [this]
           refine ⟨xyinl1, ?_⟩
           simp [le,h2]
        constructor
        · aesop
        · aesop_graph
      · simp [G',G'']
        intro h1 h2
        have: s(x, y) ∈ l1 := by
          suffices l1p ⊆ l1 by aesop
          apply List.drop_subset_drop_left
          omega
        constructor
        · aesop
        ·
          conv at h1 =>
            left
            change l1p
            rw [ldrop_eq_l1diffl2]
          rw [propext (List.Nodup.mem_diff_iff l1_nodup)] at h1
          obtain ⟨_,h3⟩ := h1
          exact List.ne_of_not_mem_cons h3

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

lemma greedySpanneri_vs_i_plus(G : FinSimpleGraph n)(t i:ℕ )(hi1: i < (G.edgeFinset.sort lex).length) [NeZero t]:
  let H_i  := GreedySpanner.Rec t G {} 0 i     -- GreedySpanner_itr G t i
  let H_i2 := GreedySpanner.Rec t G {} 0 (i+1) -- GreedySpanner_itr G t (i+1)
  let e := (G.edgeFinset.sort lex).get ⟨i,hi1⟩
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H_i2 = if (2 * t - 1) < H_i.edist u v then fromEdgeSet (H_i.edgeSet ∪ {e}) else H_i
  :=  by

  extract_lets H_i H_i2 e u v

  have:= greedySpanneri_vs_i_plus_aux G t i i (by rfl) hi1

  extract_lets G' at this
  obtain ⟨E',⟨h1,h2⟩ ⟩ := this
  simp [H_i,H_i2]
  have: GreedySpanner.Rec t G' E' i i = fromEdgeSet E' := by
    simp [GreedySpanner.Rec]
  rw [this] at h1

  have G'_nonempty: ¬ (G' = (⊥ : SimpleGraph (Fin n))):= G_lex_non_empty_of_drop_lt_num_edges G hi1
  observe: ¬ (i+1 ≤ i)
  have non_base_p: ¬ (i+1 ≤ i ∨ G' = (⊥ : SimpleGraph (Fin n))) := by
    push_neg
    constructor
    omega
    exact G'_nonempty

  conv at h2 =>
    right
    unfold GreedySpanner.Rec
    simp [non_base_p,G'_nonempty]

  have Gnonempty : (@edgeFinset (Fin n) G' G'.fintypeEdgeSet).sort lex ≠ []  := GreedySpanner.Rec.proof_1 G' i (i+1) (of_eq_false (eq_false non_base_p))

  let e' := ((@edgeFinset (Fin n) G' G'.fintypeEdgeSet).sort lex).head Gnonempty
  let u' := (Quot.out e').1
  let v' := (Quot.out e').2
  let G'' := G'.deleteEdges {e'}

  obtain ⟨uu',vv', ee'⟩ : u = u' ∧ v = v' ∧ e = e' := by
    suffices ee': e = e' by aesop
    simp [e,e']
    have:= aux G i ?_ ?_

    simp [list_Gi,Gi] at this
    simp [G']
    rw [this]
    simp [list_Gi]
    simpa using hi1
    dsimp [Gi]
    aesop

  by_cases h_distance: 2 * ↑t - 1 < (fromEdgeSet E').edist u' v'

  · -- if 2 * ↑t - 1 < (fromEdgeSet E').edist u' v'
    conv at h2 =>
      right
      unfold GreedySpanner.Rec
      simp [h_distance, e',u',v']

    rw [h1,uu',vv',ee']
    simp only [h_distance, ↓reduceIte, H_i, H_i2]
    rw [h2]

    change (fromEdgeSet ( {e'} ∪ E')) = fromEdgeSet ({e'} ∪  (fromEdgeSet E').edgeSet)

    have: ¬e'.IsDiag := by
      suffices e' ∈ G'.edgeFinset from  SimpleGraph.not_isDiag_of_mem_edgeFinset this
      have: e' ∈ G'.edgeFinset.sort lex:= by
        have:= List.head_mem Gnonempty
        convert this
      exact (mem_sort lex).mp this

    have:= insert_an_edge_diff_ordering E' this
    aesop

  · -- else
    conv at h2 =>
      right
      unfold GreedySpanner.Rec
      simp [h_distance, e',u',v']

    rw [h1,uu',vv',ee']
    simp only [h_distance, ↓reduceIte, H_i, H_i2]
    rw [h2]

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

          have Gnonempty:  (edgeFinset G_aux).sort lex ≠ [] := GreedySpanner.Rec.proof_1 G_aux itr (target+1) H
          simp [Gnotbot]

          let e := ((edgeFinset G_aux).sort lex).head Gnonempty;
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

noncomputable def FinSimpleGraph.IndexOfEdgeInGLex (G : FinSimpleGraph n) (e : Sym2 (Fin n)) : ℕ := ((G.edgeFinset.sort lex).indexOf e)

lemma greedySpannerDistUBAtEdgeItr (G : FinSimpleGraph n)(t :ℕ ) [NeZero t] {e : Sym2 (Fin n)} (he: e ∈ G.edgeSet) :
  let i :=  G.IndexOfEdgeInGLex e
  let H_e := GreedySpanner_itr G t (i+1)
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H_e.edist u v ≤ 2*t-1 := by

  extract_lets i H_e u v
  have h_index_e: i < (sort lex (edgeFinset G)).length := by
    dsimp [i,IndexOfEdgeInGLex]
    rw [@List.indexOf_lt_length]
    rw [@mem_sort]
    exact Set.mem_toFinset.mpr he

  have H:= greedySpanneri_vs_i_plus G t i h_index_e
  extract_lets H1 H2 e' u' v' at H
  have: H_e = H2 := rfl
  have ee': e = e' := by   simp [e',i,IndexOfEdgeInGLex]
  obtain ⟨uu',vv'⟩ : u = u' ∧ v = v' := by exact Prod.ext_iff.mp (congrArg Quot.out ee')
  rw [this,uu',vv']
  by_cases dist: 2 * ↑t - 1 < SimpleGraph.edist H1 u' v'
  · simp [dist] at H
    have: H2.edist u' v' = 1 := by
      rw [edist_eq_one_iff_adj]
      rw [← @mem_edgeSet]
      have: e' = s(u',v') := by simp [u',v']
      rw [← this]
      simp [H]
      refine G.not_isDiag_of_mem_edgeSet ?_
      exact Set.mem_of_eq_of_mem (id (Eq.symm ee')) he
    rw [this]
    observe: 1 ≤ t
    observe o: 1 ≤ (t : ℕ∞)
    have: 1 ≤ 2 *t -1 := by omega
    have: 2 ≤ 2 *(t : ℕ∞)  := by exact le_mul_of_one_le_right' o
    have: 2 -1 ≤ 2 *(t : ℕ∞) -1 := by exact tsub_le_tsub_right this 1
    have h1: 2 -1 = (1 :ℕ∞) := by rfl
    rw [h1] at this
    exact this
  · simp [dist] at H
    rw [H]
    exact le_of_not_lt dist

lemma greedySpannerDistUBAtEdge (G : FinSimpleGraph n)(t :ℕ ) [NeZero t] {e : Sym2 (Fin n)} (he: e ∈ G.edgeSet) :
  let i := G.IndexOfEdgeInGLex e
  let H := GreedySpanner G t
  let u := (Quot.out e).1
  let v := (Quot.out e).2
  H.edist u v ≤ 2*t-1 := by sorry

#check SimpleGraph.Walk


--variable {V : Type u} {V' : Type v} {V'' : Type w}
--variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

--def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
--  | nil, q => q
--  | cons h p, q => cons h (p.append q)


lemma greedySpannerDistUB (G : FinSimpleGraph n)(t :ℕ ) [NeZero t] (u v: Fin n) :
  let H := GreedySpanner G t
  H.edist u v ≤ (2*t-1)*G.edist u v := by
  extract_lets H
  by_cases hr: G.Reachable u v
  obtain ⟨p,hp⟩ : ∃ (p : G.Walk u v), p.length = G.dist u v := Reachable.exists_walk_length_eq_dist hr
  have: ∃ (q : H.Walk u v), q.length ≤ (2*t-1)* (G.dist u v) := by sorry
  sorry
  sorry





lemma greedySpannerSubgraphOf(G : FinSimpleGraph n)(t :ℕ ) [NeZero t]:
  let H := GreedySpanner G t
  H.IsSubgraph G := by sorry


lemma correctnessOfGreedySpanner (G : FinSimpleGraph n) (t : ℕ) [NeZero t]:
  let H := GreedySpanner G t
  H.IsSpannerOf G (2*t-1) := by
  simp [IsSpannerOf]
  sorry


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



def greedySpannerImperative  (G : FinSimpleGraph n) (t :ℕ )[NeZero t] : FinSimpleGraph n := Id.run do
  let mut f_H : BinarySqMatrix n := fun (_ _) ↦ false
  for e in G.edgeFinset.toList do
    if (2*t -1) < f_H.dist e then f_H := f_H.AddEdge e
  SimpleGraph.fromRel f_H
