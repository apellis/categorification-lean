/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclotomicRouqAdjunction
import Categorification.KLR.CyclotomicCornerTrace

/-!
# The Rouquier leftward cap is the corner trace

The leftward cap `capL` of the interior Rouquier data `ConcreteAdjunction.loc` is the
counit of the opposite adjunction `res ⊣ ind`. On `EF(N)`, identified with the corner
tensor `e RΛ(β + 2i) e ⊗ N`, it acts by the prescribed corner trace `CornerTrace.trace`
on the left tensor factor. This is the identification of Brundan's leftward cap,
arXiv:1501.00350v1, (1.15), (1.17), with the cyclotomic trace used for the red cap of
Webster, arXiv:1309.3796v3, Theorem 4.25.

Both weight signs are covered: at positive Kang–Kashiwara weight the cap is the last
finite inverse column, and at nonpositive weight it is the dotted counit after the
inverse crossing.
-/

noncomputable section

namespace Categorification.TwoRep
open CategoryTheory

/-- An inverse component of `(f, g 0, …, g (n-1)) : Y ⊕ Z^{⊕ n} → X` is determined by its
composites with the original components. -/
theorem SumInvFrom.eq_g' {D : Type*} [Category D] [Preadditive D] {X Y Z : D} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n k : ℕ}
    (I : SumInvFrom f g n) (hk : k < n) (c : X ⟶ Z) (hf : f ≫ c = 0)
    (hg : ∀ m, m < n → g m ≫ c = if m = k then 𝟙 Z else 0) :
    c = I.g' k := by
  calc c = (I.f' ≫ f + ∑ m ∈ Finset.range n, I.g' m ≫ g m) ≫ c := by
        rw [I.total, Category.id_comp]
    _ = ∑ m ∈ Finset.range n, I.g' m ≫ (if m = k then 𝟙 Z else 0) := by
        rw [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, hf,
          Limits.comp_zero, zero_add]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Category.assoc, hg m (Finset.mem_range.mp hm)]
    _ = I.g' k := by
        simp only [comp_ite, Category.comp_id, Limits.comp_zero]
        rw [Finset.sum_eq_single k]
        · simp
        · intro m _ hmk
          simp [hmk]
        · intro hkn
          exact False.elim (hkn (Finset.mem_range.mpr hk))

/-- The main inverse component of `(f, g 0, …, g (n-1)) : X → Y ⊕ Z^{⊕ n}` is determined by its
composites with the original components. -/
theorem SumInvTo.eq_f' {D : Type*} [Category D] [Preadditive D] {X Y Z : D} {f : X ⟶ Y}
    {g : ℕ → (X ⟶ Z)} {n : ℕ} (I : SumInvTo f g n) (c : Y ⟶ X) (hf : c ≫ f = 𝟙 Y)
    (hg : ∀ m, m < n → c ≫ g m = 0) : c = I.f' := by
  calc c = c ≫ (f ≫ I.f' + ∑ m ∈ Finset.range n, g m ≫ I.g' m) := by
        rw [I.total, Category.comp_id]
    _ = I.f' := by
        rw [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc, hf, Category.id_comp,
          add_eq_left]
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [← Category.assoc, hg m (Finset.mem_range.mp hm), Limits.zero_comp]

end Categorification.TwoRep

namespace Categorification.KLR.KLRAlgebra.PresentColour
open Categorification.BalancedTensor

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I) (a : I → Polynomial k)
  (N : Type*) [AddCommGroup N] [Module k N]
  [Module (CycKLR k Q a ({i} + γ)) N] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N]
  (hsym : KLRSymm Q)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- On a pure tensor of the middle corner, the dotted coordinates of the nonnegative commutator
inverse are the commutator coordinates of the corner element acting on the module element. -/
theorem positiveEquiv_symm_tmul_snd
    (hwt : 0 ≤ RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX ({i} + γ))))
    (z : MiddleCyclotomic Q i γ a) (n : N) :
    ((positiveEquiv Q i γ a N hsym hQ ha RD Λ hΛ hdeg hwt).symm
        ((efMiddleEquiv Q i γ a N).symm (tmul z n))).2 =
      fun d => ((cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
        z).2 d • n := by
  simp only [positiveEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  rfl

/-- On a pure tensor of the middle corner, the nonpositive commutator inverse is the induced
lower tensor of the inverse with zero dotted coordinates. -/
theorem negativeEquiv_symm_tmul
    (hwt : RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX ({i} + γ))) ≤ 0)
    (z : MiddleCyclotomic Q i γ a) (n : N) :
    (negativeEquiv Q i γ a N hsym hQ ha RD Λ hΛ hdeg hwt).symm
        ((efMiddleEquiv Q i γ a N).symm (tmul z n), 0) =
      lowerToFE Q i γ a N (tmul
        ((cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
          (z, 0)) n) := by
  simp only [negativeEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  rw [prodFin_symm_tmul]
  rfl

end Categorification.KLR.KLRAlgebra.PresentColour

namespace Categorification.KLR.KLRAlgebra.AbsentColour.ConcreteAdjunction
open CategoryTheory Categorification.TwoRep InductionCalculus
open scoped ModuleCat.Algebra
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX (Si + β)))

/-- The dotted components of the inverse of `(σ, cupD 0, …)` at nonpositive Rouquier weight are
the dotted components of the explicit cyclotomic commutator inverse. -/
theorem iN_g' (hw : 0 ≤ wt) (hh : -wt ≤ 0) (n : ℕ) (hn : n < (wt).toNat) :
    ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).iN hh).g' n =
      ObjectProperty.homMk
        (positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw n) := by
  have hn' : n < (- -wt).toNat := by rwa [neg_neg]
  refine (SumInvFrom.eq_g' _ hn' _ ?_ ?_).symm
  · apply ObjectProperty.hom_ext
    erw [ObjectProperty.FullSubcategory.comp_hom, sigma_hom]
    exact (actualSumInvFrom.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw).fg n hn
  · intro m hm
    have hm' : m < (wt).toNat := by rwa [neg_neg] at hm
    apply ObjectProperty.hom_ext
    erw [ObjectProperty.FullSubcategory.comp_hom, cup_hom]
    have h := (actualSumInvFrom.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw).gg m n hm' hn
    split_ifs at h ⊢ <;> exact h

theorem capL_app_positive (hw : 0 < wt)
    (M : ModuleCat.{max u v w} (CycKLR k Q a (Si + β)))
    (z : MiddleCyclotomic Q i β a) (m : M) :
    ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).capL.hom.app M).hom
        ((PresentColour.efMiddleEquiv Q i β a M).symm (BalancedTensor.tmul z m)) =
      CornerTrace.positive Q i β a hsym hQ ha RD Λ hΛ hdeg hw z • m := by
  have hh : -wt < 0 := by omega
  have hd : (- -wt - 1).toNat < (wt).toNat := by omega
  rw [RouqLoc.capL_of_neg hh, RouqLoc.capN_of_nonpos hh.le,
    iN_g' Q i a β hsym hQ ha RD Λ hΛ hdeg hw.le hh.le _ hd]
  change (positiveInverseDot.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw.le _).app M _ = _
  refine (positiveInverseDot_app Q i a β hsym hQ ha RD Λ hΛ hdeg hw.le _ hd M _).trans ?_
  have hs : ∀ t, ((originalPositiveEquiv.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg M hw.le).symm
      t).2 = ((PresentColour.positiveEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hw.le).symm t).2 := by
    intro t
    rfl
  refine (congrFun (hs _) _).trans ?_
  rw [PresentColour.positiveEquiv_symm_tmul_snd]
  have he : (- -wt - 1).toNat = (wt).toNat - 1 := by omega
  simp only [he]
  rfl

/-- The main component of the inverse of `(σ, capD 0, …)` at nonnegative Rouquier weight is the
explicit cyclotomic inverse crossing. -/
theorem ip_f' (hw : wt ≤ 0) (hh : 0 ≤ -wt) :
    ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).ip hh).f' =
      ObjectProperty.homMk
        (negativeInverseCrossing.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw) := by
  refine (SumInvTo.eq_f' _ _ ?_ ?_).symm
  · apply ObjectProperty.hom_ext
    erw [ObjectProperty.FullSubcategory.comp_hom, sigma_hom]
    exact (actualSumInvTo.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw).ff
  · intro m hm
    apply ObjectProperty.hom_ext
    erw [ObjectProperty.FullSubcategory.comp_hom, cap_hom]
    exact (actualSumInvTo.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hw).fg m hm

/-- **The Rouquier leftward cap at nonpositive weight is the cyclotomic corner trace**: on a pure
tensor `z ⊗ m` of the middle corner it is the dotted counit of the inverse crossing of `z`. -/
theorem capL_app_nonpositive (hw : wt ≤ 0)
    (M : ModuleCat.{max u v w} (CycKLR k Q a (Si + β)))
    (z : MiddleCyclotomic Q i β a) (m : M) :
    ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).capL.hom.app M).hom
        ((PresentColour.efMiddleEquiv Q i β a M).symm (BalancedTensor.tmul z m)) =
      CornerTrace.nonpositive Q i β a hsym hQ ha RD Λ hΛ hdeg hw z • m := by
  have hh : 0 ≤ -wt := by omega
  rw [RouqLoc.capL_of_nonneg hh, RouqLoc.sigL_of_nonneg hh,
    ip_f' Q i a β hsym hQ ha RD Λ hΛ hdeg hw hh, Preadditive.neg_comp, neg_neg]
  have hc : ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).capD (-wt).toNat).hom =
      dottedCounit Q i a β (-wt).toNat := cap_hom Q i a β _
  erw [ObjectProperty.FullSubcategory.comp_hom, hc]
  change (dottedCounit Q i a β (-wt).toNat).app M
    ((originalNegativeEquiv.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg M hw).symm (_, 0)) = _
  have hs : ∀ t, (originalNegativeEquiv.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg M hw).symm t =
      feRebase Q i a β M ((PresentColour.negativeEquiv Q i β a M hsym hQ ha RD Λ hΛ hdeg hw).symm
        t) := fun t => rfl
  have key := PresentColour.negativeEquiv_symm_tmul Q i β a M hsym hQ ha RD Λ hΛ hdeg hw z m
  refine (congrArg _ ((hs _).trans (congrArg _ key))).trans ?_
  exact dottedCounit_comparison Q i a β M _ _ m

/-- **The Rouquier leftward cap is the cyclotomic corner trace** (Brundan (1.15), (1.17)): on a
pure tensor `z ⊗ m` of the middle corner it is multiplication by the corner trace of `z`. -/
theorem capL_app_tmul (M : ModuleCat.{max u v w} (CycKLR k Q a (Si + β)))
    (z : MiddleCyclotomic Q i β a) (m : M) :
    ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).capL.hom.app M).hom
        ((PresentColour.efMiddleEquiv Q i β a M).symm (BalancedTensor.tmul z m)) =
      CornerTrace.trace Q i β a hsym hQ ha RD Λ hΛ hdeg z • m := by
  unfold CornerTrace.trace
  split
  · exact capL_app_positive Q i a β hsym hQ ha RD Λ hΛ hdeg _ M z m
  · exact capL_app_nonpositive Q i a β hsym hQ ha RD Λ hΛ hdeg _ M z m

end Categorification.KLR.KLRAlgebra.AbsentColour.ConcreteAdjunction
