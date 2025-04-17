import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

--      have h2': sort r (Gi G (i)).edgeFinset ≠ [] := by
--          suffices (Gi G i) ≠ ⊥ by
section
--open Multiset

theorem inf_eq_inf_and_sup_eq_sup [LinearOrder α] {s t : Sym2 α} :
    s.inf = t.inf ∧ s.sup = t.sup ↔ s = t := by
  induction' s with a b
  induction' t with c d
  obtain hab | hba := le_total a b <;> obtain hcd | hdc := le_total c d <;>
    aesop (add unsafe le_antisymm)

end

section
open SimpleGraph

--lemma fromEdgeSet_edgeFinset_cancel {V : Type u} {s : Finset (Sym2 V)}: (fromEdgeSet ↑s).edgeFinset = s :=  sorry

end

section
open Finset

variable {α}
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

lemma sort_drop_sort_eq_drop_sort [DecidableEq α ] (s : Finset α) (i:ℕ):
sort r ((s.sort r).drop i).toFinset = (s.sort r).drop i := by
  refine (List.toFinset_sort r ?_).mpr ?_
  · suffices (sort r (s)).Nodup by
      let l1 := List.drop i (sort r (s))
      let l2 := sort r (s)
      observe o1: l2.Nodup
      observe o2: l1.Sublist l2
      exact List.Sublist.nodup o2 this
    exact sort_nodup r (s)
  · induction' i  with i ih
    · simp
    · simp at ih
      rw [← List.drop_drop]
      have: (List.drop i (sort r (s))).drop 1 = (List.drop i (sort r (s))).tail := List.drop_one (List.drop i (sort r (s)))
      rw [this]
      apply List.Sorted.tail ih

theorem sort_non_empty_iff_non_empty {s : Finset α}  : sort r s ≠ [] ↔ s.Nonempty := by
  constructor
  · intro h
    observe: 0 < (sort r s).length
    have: 0 < #s := by aesop
    exact card_pos.mp this
  · intro h
    observe: 0 < #s
    have:  (s.sort r).length = #s := Finset.length_sort r
    observe: 0 < (s.sort r).length
    rwa [← @List.length_pos_iff_ne_nil]

end
