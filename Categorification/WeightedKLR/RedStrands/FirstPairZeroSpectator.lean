/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairTerminalSpectator

/-!
# The first paired red exchange with a zero-weight final spectator

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
A loading ending at the spectator has zero higher kernel. Otherwise the
unit bigon across the black strand next to the final spectator gives
an equivalent higher loading, and the actual partial standard is zero.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

universe u v
variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 3 → I →₀ ℕ)

local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ

private theorem next_to_terminal_red_black (t : Seq μ) (order : redWord t = List.finRange 3)
    (h : (redPos t 2).val + 1 < N) :
    ∃ i : I, t.lbl ⟨(redPos t 2).val + 1, h⟩ = .inl i := by
  let q : Fin N := ⟨(redPos t 2).val + 1,h⟩
  change ∃ i, t.lbl q = .inl i
  rcases lbl : t.lbl q with i | r
  · exact ⟨i,rfl⟩
  · have pos : q = redPos t r := eq_redPos lbl
    have ord₀₁ : redPos t 0 < redPos t 1 :=
      lt_of_redWord_eq_append (show redWord t = ([] : List (Fin 3)) ++ 0 :: 1 :: [2] from order)
        (lbl_redPos t 0) (lbl_redPos t 1)
    have ord₁ : redPos t 1 < redPos t 2 :=
      lt_of_redWord_eq_append (show redWord t = [0] ++ 1 :: 2 :: [] from order)
        (lbl_redPos t 1) (lbl_redPos t 2)
    have le : redPos t r ≤ redPos t 2 := by
      fin_cases r
      · exact (ord₀₁.trans ord₁).le
      · exact ord₁.le
      · exact le_rfl
    have val : (q : ℕ) = (redPos t 2).val + 1 := rfl
    have lower : (q : ℕ) ≤ (redPos t 2).val := pos.symm ▸ le
    omega

private theorem blackCount_terminal_swap_lt (t : Seq μ) (j : ℕ) (h : j + 1 < N) (i : I)
    (hr : t.lbl ⟨j,by omega⟩ = .inr 2) (hi : t.lbl ⟨j+1,h⟩ = .inl i) :
    blackCount t 2 i < blackCount (sadj N j • t) 2 i := by
  classical
  have uniq : ∀ d, t.lbl d = .inr (2 : Fin 3) → d = ⟨j,by omega⟩ :=
    fun d hd => (eq_redPos hd).trans (eq_redPos hr).symm
  rw [blackCount_sadj]
  refine Finset.card_lt_card ⟨?_,fun subset => ?_⟩
  · intro c hc
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc ⊢
    exact ⟨hc.1, fun d hd => sadj_lt_sadj h hr hi hc.1 hd (hc.2 d hd)⟩
  · have add : (⟨j+1,h⟩ : Fin N) ∈ Finset.univ.filter fun c => t.lbl c = .inl i ∧
        ∀ d, t.lbl d = .inr (2 : Fin 3) → sadj N j c < sadj N j d := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      refine ⟨hi,fun d hd => ?_⟩
      rw [uniq d hd,Fin.lt_def,KLRAlgebra.sadj_apply_val h,KLRAlgebra.sadj_apply_val h]
      simp
    have old := subset add
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at old
    exact absurd (old.2 ⟨j,by omega⟩ hr) (by simp [Fin.lt_def])

private theorem terminalSpectator_adjacent_bigons (j : ℕ) (h : j+1 < N) (t : Seq μ) (i : I)
    (hr : t.lbl ⟨j,by omega⟩ = .inr 2) (hi : t.lbl ⟨j+1,h⟩ = .inl i)
    (zero : Λ 2 i = 0) :
    (ψ j * ψ j * e t : A) = e t ∧
      (ψ j * ψ j * e (sadj N j • t) : A) = e (sadj N j • t) := by
  let dots : Fin 2 → Fin N := ![⟨j,by omega⟩,⟨j+1,h⟩]
  have dotEq : ![(x ⟨j,by omega⟩ : A), x ⟨j+1,h⟩] = fun b => x (dots b) := by
    funext b
    fin_cases b <;> rfl
  have one : ncEval ![(x ⟨j,by omega⟩ : A), x ⟨j+1,h⟩] (1 : MvPolynomial (Fin 2) k) = 1 := by
    rw [dotEq,ncEval_eq_pol,map_one,map_one]
  let s := sadj N j • t
  have sh₁ : s.lbl ⟨j,by omega⟩ = .inl i := by
    rw [show s = _ from rfl,lbl_sadj,sadj_apply_left h]
    exact hi
  have sh₂ : s.lbl ⟨j+1,h⟩ = .inr 2 := by
    rw [show s = _ from rfl,lbl_sadj,sadj_apply_right h]
    exact hr
  constructor
  · rw [ψ_sq j h,hr,hi,ite_eq_right Sum.inr_ne_inl,stendhalQ_inr_inl,zero,pow_zero,one,one_mul]
  · change (ψ j * ψ j * e s : A) = e s
    rw [ψ_sq j h,sh₁,sh₂,ite_eq_right Sum.inl_ne_inr,stendhalQ_inl_inr,zero,pow_zero,one,one_mul]

/-- If a black strand lies after the final weight-zero spectator, the
source loading projective is entirely in the first-pair higher kernel. -/
theorem firstPair_blockLoadingKernel_eq_top_of_zeroSpectator_after (t : Seq μ)
    (order : redWord t = List.finRange 3) (zero : ∀ i : I, Λ 2 i = 0)
    (hasNext : (redPos t 2).val+1 < N) :
    blockLoadingKernel Q Λ t 0 1 = ⊤ := by
  let j := (redPos t 2).val
  have hj : j+1 < N := hasNext
  have hr : t.lbl ⟨j,by omega⟩ = .inr 2 := lbl_redPos t 2
  obtain ⟨i,hi⟩ := next_to_terminal_red_black t order hasNext
  let s := sadj N j • t
  have same : redWord s = redWord t :=
    redWord_sadj_smul t hj (by rw [hi]; simp)
  have monotone : adjacentBlockRoot 0 1 t ≤ adjacentBlockRoot 0 1 s := by
    intro label color
    unfold adjacentBlockRoot blockBlackCount
    refine Finset.card_le_card_of_injOn (sadj N j) ?_ (sadj N j).injective.injOn
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      s, lbl_sadj, sadj_sadj_apply] at hx ⊢
    exact ⟨hx.1, fun y r hy hred => by
      simpa only [sadj_sadj_apply] using sadj_lt_sadj hj hr hi hx.1 hred (hx.2 _ r hy hred)⟩
  have strict : adjacentBlockRoot 0 1 t < adjacentBlockRoot 0 1 s := by
    apply lt_of_le_not_ge monotone
    intro reverse
    have bound := reverse 2 i
    simp only [adjacentBlockRoot,show ¬ ((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) by decide,
      ite_false,blockBlackCount_singleton] at bound
    exact (not_le_of_gt (blackCount_terminal_swap_lt t j hj i hr hi)) bound
  have bigons := terminalSpectator_adjacent_bigons Q Λ j hj t i hr hi (zero i)
  exact blockLoadingKernel_eq_top_of_equiv Q Λ t s 0 1 same strict
    (loadingIdemEquiv_of_unit_bigon Q Λ t s same j rfl bigons.1 bigons.2)

section Derived

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
set_option quotPrecheck false in
local notation "corner" order => (isIdempotentElem_violMk_redProj k Q Λ ν order).Corner

set_option backward.isDefEq.respectTransparency false in
/-- In canonical source red order, a zero-weight last spectator gives
braid cohomology concentrated in degree zero for the first paired red
block, at arbitrary black content and arbitrary target red order. -/
theorem firstPair_zeroSpectator_partialStandard_braid_homology_vanish
    (t : Seq μ) (target : List (Fin 3))
    [HasDerivedCategory.{w,max u v} (corner (redWord t))ᵐᵒᵖ]
    [HasDerivedCategory.{w,max u v} (corner target)ᵐᵒᵖ]
    (order : redWord t = List.finRange 3) (zero : ∀ i : I, Λ 2 i = 0)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor («A» := (corner target)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν (redWord t) target).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (corner (redWord t))ᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t 0 1).X₃)))) := by
  by_cases next : (redPos t 2).val + 1 < N
  · have top := firstPair_blockLoadingKernel_eq_top_of_zeroSpectator_after Q Λ t order zero next
    have hZ : IsZero (blockLoadingShortComplex Q Λ t 0 1).X₃ := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      let P := rIdeal (orderedLoadingIdem Q Λ t)
      let : AddCommGroup P := Submodule.addCommGroup P
      let : Module (corner (redWord t))ᵐᵒᵖ P := Submodule.module P
      change Subsingleton (P ⧸ blockLoadingKernel Q Λ t 0 1)
      exact Submodule.Quotient.subsingleton_iff.mpr top
    let : (braidingFunctor.{w} k Q Λ ν (redWord t) target).Additive := by
      unfold braidingFunctor
      infer_instance
    let G := degreeZeroModuleFunctor (corner (redWord t))ᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
      braidingFunctor.{w} k Q Λ ν (redWord t) target ⋙
      homologyFunctor («A» := (corner target)ᵐᵒᵖ) ℤ n
    exact G.map_isZero hZ
  · have terminal (p : Fin N) (i : I) (hp : t.lbl p = .inl i) : p < redPos t 2 := by
      have ne : p ≠ redPos t 2 := fun eq => by rw [eq,lbl_redPos] at hp; cases hp
      have le : p.val ≤ (redPos t 2).val := by have h := p.isLt; omega
      exact lt_of_le_of_ne le ne
    exact blockPartialStandard_braid_homology_vanish_of_bot Q Λ t 0 1 target
      (firstPair_terminal_blockLoadingKernel_eq_bot Q Λ t order terminal) n hn

end Derived

end Categorification.Stendhal.BraidedStendhalAlgebra
