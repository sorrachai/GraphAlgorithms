import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Multiset.Lattice



variable {α}
theorem Sym2.eq_iff_inf_sup [LinearOrder α] (x y : Sym2 (α)) : x = y ↔ (x.inf,x.sup) = (y.inf,y.sup) := by
  constructor
  ·
    rw [@Sym2.ext_iff]
    intro h
    rw [@Prod.mk.inj_iff]
    by_cases diag: IsDiag x
    · rw [Sym2.isDiag_iff_mem_range_diag] at diag
      simp [IsDiag] at diag
      obtain ⟨b,h'⟩ := diag
      have: diag b = y := by aesop
      aesop
    ·
      let a := (Quot.out x).1
      have ainx:  a ∈ x := by exact out_fst_mem x
      let b := Sym2.Mem.other ainx
      have H:= Sym2.other_ne diag ainx
      have t': b ∈ x ∧ a ∈ x ↔ x = s(b, a) := Sym2.mem_and_mem_iff H
      observe binx: b ∈ x
      change  (Sym2.Mem.other ainx) ∈ x at binx
      have ainy: a ∈ y := by rwa [← h]
      have biny: b ∈ y := by rwa [← h]
      have: b ∈ y ∧ a ∈ y ↔ y = s(b, a) := Sym2.mem_and_mem_iff H
      replace this:y = s(b,a) := by aesop
      simp [ainx,binx] at t'
      have: x = s(b,a) := by
        rw [← t']
        exact binx
      have: x = y := by exact Sym2.ext_iff.mpr h
      exact ⟨congrArg inf this, congrArg sup this⟩
  ·
    let x1 := (Quot.out x).1
    let x2 := (Quot.out x).2
    let y1 := (Quot.out y).1
    let y2 := (Quot.out y).2

    by_cases diag: IsDiag x
    · rw [Sym2.isDiag_iff_mem_range_diag] at diag
      simp [IsDiag] at diag
      obtain ⟨b,h'⟩ := diag
      intro H
      simp at H
      obtain ⟨h1,h2⟩ := H
      simp [diag] at h'
      have: x.inf = b := by aesop
      have: x.sup = b := by aesop
      have yy: y.inf = b := by aesop
      have yy': y.sup = b := by aesop
      have: y.inf = y.sup := by rwa [yy']
      have sy1y2: s(y1,y2) = y := by aesop
      have yinfeq: y.inf = y1 ⊓ y2 := by
        rw [← sy1y2]
        simp only [inf_mk]
      rw [yy] at this
      have ysupeq: y.sup = y1 ⊔ y2 := by
        rw [← sy1y2]
        simp only [sup_mk]
      rw [yy'] at this
      have y1eqy2: y1 = y2 := by aesop
      have: y1 = b := by aesop
      rw [← y1eqy2,this] at sy1y2
      rwa [h'] at sy1y2
    ·
      have x1inx:  x1 ∈ x := by exact out_fst_mem x
      let x2' := Sym2.Mem.other x1inx
      have H:= Sym2.other_ne diag x1inx
      have sx1x2': s(x1,x2') = x := by aesop
      have xinfeq: x.inf = x1 ⊓ x2' := by
        rw [← sx1x2']
        simp only [inf_mk]
      have xsupeq: x.sup = x1 ⊔ x2' := by
        rw [← sx1x2']
        simp only [sup_mk]
      rw [xinfeq,xsupeq]
      intro h
      simp at h
      obtain ⟨h1,h2⟩ := h

      have sy1y2: s(y1,y2) = y := by aesop
      have ndiagy: ¬ y.IsDiag := by
        have yinfeq: y.inf = y1 ⊓ y2 := by
          rw [← sy1y2]
          simp only [inf_mk]
        have ysupeq: y.sup = y1 ⊔ y2 := by
          rw [← sy1y2]
          simp only [sup_mk]
        by_contra!
        rw [Sym2.isDiag_iff_mem_range_diag] at this
        simp at this
        obtain ⟨b,hb⟩ := this
        rw [← sy1y2] at hb
        simp [Sym2.diag] at hb
        have: y1 = y2 := by aesop
        have t1: y.sup = b := by aesop
        have t2: y.inf = b := by aesop
        suffices x1 = x2' by
          dsimp [x2'] at this
          rw [← this] at H
          contradiction
        rw [t2] at h1
        rw [t1] at h2
        have: x1 ⊔ x2' = x1 ⊓  x2':= by aesop
        rwa [sup_eq_inf] at this

      have y1inx:  y1 ∈ y := by exact out_fst_mem y
      let y2' := Sym2.Mem.other y1inx
      have Hy:= Sym2.other_ne ndiagy y1inx

      have sy1y2: s(y1,y2') = y := by aesop
      have yinfeq: y.inf = y1 ⊓ y2' := by
        rw [← sy1y2]
        simp only [inf_mk]
      have ysupeq: y.sup = y1 ⊔ y2' := by
        rw [← sy1y2]
        simp only [sup_mk]

      obtain ⟨xy1,xy2⟩ : x1 ⊓ x2' = y1 ⊓ y2' ∧ x1 ⊔ x2' = y1 ⊔ y2' := by aesop

      obtain hx12 | hx12' : x1 < x2' ∨ x2' < x1 := lt_or_gt_of_ne (id (Ne.symm H)) <;> obtain hy12 | hy12' : y1 < y2' ∨ y2' < y1 := lt_or_gt_of_ne (id (Ne.symm Hy))
      · observe H1: x1 ⊓ x2' = x1
        observe H2: y1 ⊓ y2' = y1
        observe H3: x1 ⊔ x2' = x2'
        have H4: y1 ⊔ y2' = y2' := by aesop
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
      · observe H1: x1 ⊓ x2' = x1
        observe H2: y1 ⊓ y2' = y2'
        observe H3: x1 ⊔ x2' = x2'
        have H4: y1 ⊔ y2' = y1 := by aesop
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
        exact eq_swap
      · observe H1: x1 ⊓ x2' = x2'
        observe H2: y1 ⊓ y2' = y1
        observe H3: x1 ⊔ x2' = x1
        have H4: y1 ⊔ y2' = y2' := by
          simp
          exact le_of_lt hy12
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
        exact eq_swap
      · observe H1: x1 ⊓ x2' = x2'
        have H2: y1 ⊓ y2' = y2' := by
          simp
          exact le_of_lt hy12'
        observe H3: x1 ⊔ x2' = x1
        have H4: y1 ⊔ y2' = y1 := by
          simp
          exact le_of_lt hy12'
        rw [H1,H2] at xy1
        rw [H3,H4] at xy2
        rw [xy1] at sx1x2'
        rw [xy2] at sx1x2'
        rw [← sx1x2',← sy1y2]
