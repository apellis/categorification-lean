/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumTrace
import Categorification.KLR.CyclotomicAction.GlobalNilpotent
import Categorification.Algebra.InductionAlongEnd

/-!
# Bubbles at the vacuum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
**Proposition 3.25**. At an object `V` of weight `h = -l ≤ 0` of a Rouquier `sl₂`-datum in
`LinearCat K`, if the dot on `E V` satisfies a monic polynomial `p` of degree `l`, the clockwise
bubble with `m` dots acts on `V` by the coefficient of `y^{l-1}` in `y^m mod p`
(`TwoRep.RouqLoc.cw_hom_app_of_aeval`): the cups with `r < l` dots and the last `♣`-cap pair to
`δ_{r, l-1}` (Brundan (1.9)).

For the cyclotomic Rouquier family the dot of `F_i` out of the empty block satisfies the
cyclotomic relation `a_i(x) = 0` (`aeval_dot_of_zero`, `aeval_globalDot_app`), so at the weight
`-Λ`, on an object concentrated in the empty block, the clockwise bubble of colour `i` with `m`
dots acts by the coefficient of `y^{deg a_i - 1}` in `y^m mod a_i`
(`globalLoc_cw_app_of_vacuum`). For the universal cyclotomic polynomials of `Ř^λ_λ` this
coefficient is `vacTrace` (`coeff_modByMonic_univCycPoly`), and these traces generate `Ř^λ_λ`
(`adjoin_vacTrace_eq_top`).
-/

namespace Categorification

open CategoryTheory CategoryTheory.Bicategory Polynomial

namespace TwoRep

universe w v u

noncomputable section

variable {K : Type w} [CommRing K] {a b c : LinearCat.{w, v, u} K}
  {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}

theorem powComp_natTrans_app {C D : Type*} [Category C] [Category D] {F : C ⥤ D} (η : F ⟶ F)
    (X : C) : ∀ n : ℕ, (powComp η n).app X = powComp (η.app X) n
  | 0 => rfl
  | n + 1 => by rw [powComp_succ, NatTrans.comp_app, powComp_natTrans_app η X n]; rfl

namespace RouqLoc

variable (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- The value at `V` of a rightward cup with `r` dots followed by a map `E_i F_i 1_λ → 1_λ`. -/
theorem cupD_comp_hom_app (r : ℕ) (g : E₂ ≫ R₂ ⟶ 𝟙 b) (V : b) :
    (L.cupD r ≫ g).hom.app V =
      adj₂.unit.hom.app V ≫ R₂.obj.map (End.of (x₂.hom.app V) ^ r) ≫ g.hom.app V := by
  have e : (L.cupD r ≫ g).hom.app V =
      adj₂.unit.hom.app V ≫ R₂.obj.map ((powComp x₂ r).hom.app V) ≫ g.hom.app V := by
    rw [cupD, Category.assoc]; rfl
  rw [e, LinearCat.powComp_hom, powComp_natTrans_app, powComp_eq_endPow (End.of _)]

/-- **Clockwise bubbles at an object annihilated by a polynomial in the dot.** At weight
`h = -l ≤ 0`, if `p(x)` vanishes on `E V` for a monic `p` of degree `l`, the clockwise bubble with
`m` dots acts on `V` by the coefficient of `y^{l-1}` in `y^m mod p`. -/
theorem cw_hom_app_of_aeval {l : ℕ} (hh : h = -(l : ℤ)) (V : b) {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = l) (hV : aeval (End.of (x₂.hom.app V)) p = 0) (m : ℕ) :
    (L.cw m).hom.app V = (X ^ m %ₘ p).coeff (l - 1) • 𝟙 V := by
  set f : End (E₂.obj.obj V) := End.of (x₂.hom.app V)
  let u : V ⟶ R₂.obj.obj (E₂.obj.obj V) := adj₂.unit.hom.app V
  let cap : R₂.obj.obj (E₂.obj.obj V) ⟶ V := L.capL.hom.app V
  let ψ : End (E₂.obj.obj V) →ₗ[K] (V ⟶ V) :=
    { toFun := fun g => u ≫ R₂.obj.map g ≫ cap
      map_add' := fun g g' => by
        change _ ≫ R₂.obj.map (g + g') ≫ _ = _
        rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun c g => by
        change _ ≫ R₂.obj.map (c • g) ≫ _ = _
        rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
        rfl }
  have hcw : (L.cw m).hom.app V = ψ (f ^ m) := by
    rw [cw_of_nonneg (L := L) (Int.natCast_nonneg m), Int.toNat_natCast, cupD_comp_hom_app]
    rfl
  have hrem : f ^ m = aeval f (X ^ m %ₘ p) := by
    conv_lhs => rw [← aeval_X_pow (R := K) f, ← modByMonic_add_div (X ^ m) p]
    rw [map_add, map_mul, hV, zero_mul, add_zero]
  rw [hcw, hrem]
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hp1 : p = 1 := hp.natDegree_eq_zero.1 (hdeg.trans hl)
    rw [hp1, modByMonic_one, map_zero, map_zero, coeff_zero, zero_smul]
  · have hneg : h ≤ 0 := by omega
    have hcap : L.capL = (L.iN hneg).g' (l - 1) := by
      rw [capL_of_neg (L := L) (by omega), capN_of_nonpos (L := L) hneg]
      congr 1
      omega
    have hl' : (-h).toNat = l := by omega
    have hdegr : (X ^ m %ₘ p).natDegree < l := by
      rw [← hdeg]
      exact natDegree_modByMonic_lt _ hp (fun h1 => by rw [h1, natDegree_one] at hdeg; omega)
    rw [aeval_eq_sum_range' hdegr, map_sum]
    have hpair : ∀ r ∈ Finset.range l, ψ ((X ^ m %ₘ p).coeff r • f ^ r) =
        if r = l - 1 then (X ^ m %ₘ p).coeff (l - 1) • 𝟙 V else 0 := by
      intro r hr
      rw [map_smul]
      have := (L.iN hneg).gg r (l - 1) (by rw [hl']; exact Finset.mem_range.1 hr)
        (by rw [hl']; omega)
      have hψ : ψ (f ^ r) = (L.cupD r ≫ L.capL).hom.app V := by
        rw [cupD_comp_hom_app]; rfl
      rw [hψ, hcap, this]
      split_ifs with hr'
      · subst hr'; rfl
      · change _ • (0 : V ⟶ V) = 0
        exact smul_zero _
    rw [Finset.sum_congr rfl hpair, Finset.sum_ite_eq' (Finset.range l) (l - 1)]
    simp only [Finset.mem_range, show l - 1 < l by omega, ↓reduceIte]
    rfl

end RouqLoc

end


section AevalTransfer

variable {K : Type*} [CommRing K]

/-- An anti-multiplicative linear map preserving `1` commutes with polynomial evaluation. -/
theorem aeval_antihom {A B : Type*} [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (T : A →ₗ[K] B) (h1 : T 1 = 1) (hmul : ∀ x y, T (x * y) = T y * T x) (y : A) (p : K[X]) :
    T (aeval y p) = aeval (T y) p := by
  have hp : ∀ n : ℕ, T (y ^ n) = T y ^ n := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ']
  rw [aeval_eq_sum_range, aeval_eq_sum_range, map_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [map_smul, hp]

variable {C D : Type*} [Category C] [Preadditive C] [Linear K C] [Category D] [Preadditive D]
  [Linear K D]

/-- A `K`-linear functor commutes with polynomial evaluation of endomorphisms. -/
theorem Functor.map_aeval (F : C ⥤ D) [F.Additive] [F.Linear K] {X : C} (f : End X) (p : K[X]) :
    F.map (aeval f p : End X) = aeval (End.of (F.map f)) p := by
  let φ : End X →ₐ[K] End (F.obj X) :=
    { toFun := fun g => F.map g
      map_one' := F.map_id X
      map_mul' := fun g g' => F.map_comp g' g
      map_zero' := F.map_zero X X
      map_add' := fun g g' => F.map_add
      commutes' := fun c => by
        change F.map (c • 𝟙 X) = c • 𝟙 (F.obj X)
        rw [Functor.map_smul, F.map_id] }
  exact (aeval_algHom_apply φ f p).symm

/-- Components of natural transformations commute with polynomial evaluation. -/
theorem NatTrans.app_aeval {E : Type*} [Category E] {F : E ⥤ C} (η : End F) (Y : E) (p : K[X]) :
    (aeval η p : End F).app Y = aeval (End.of (η.app Y)) p := by
  let φ : End F →ₐ[K] End (F.obj Y) :=
    { toFun := fun g => g.app Y
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun c => by
        change (c • 𝟙 F).app Y = c • 𝟙 (F.obj Y)
        rw [NatTrans.app_smul]
        rfl }
  exact (aeval_algHom_apply φ η p).symm

/-- Polynomial evaluation is compatible with intertwining morphisms. -/
theorem comp_aeval_of_comp {X Y : C} (u : X ⟶ Y) {f : End X} {g : End Y}
    (hu : u ≫ (g : Y ⟶ Y) = (f : X ⟶ X) ≫ u) (p : K[X]) :
    u ≫ (aeval g p : Y ⟶ Y) = (aeval f p : X ⟶ X) ≫ u := by
  have hp : ∀ n : ℕ, u ≫ ((g ^ n : End Y) : Y ⟶ Y) = ((f ^ n : End X) : X ⟶ X) ≫ u :=
    fun n => by
      induction n with
      | zero => exact (Category.comp_id u).trans (Category.id_comp u).symm
      | succ n ih =>
        rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ← Category.assoc, hu, Category.assoc,
          ih, Category.assoc]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Preadditive.comp_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun n _ => by rw [Linear.comp_smul, hp, Linear.smul_comp]

end AevalTransfer

end TwoRep

namespace KLR.CyclotomicAction

open KLRAlgebra CategoryTheory.Limits TwoRep

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → k[X])

/-- **The cyclotomic relation on the dot of `F_i` at the empty block**: `a_i(x) = 0` for the dot
of `R^Λ({i})`, the last (and only) strand. -/
theorem aeval_dotElt_of_zero (i : I) {δ : Multiset I} (h : {i} + 0 = δ) :
    aeval (dotElt Q a i h) (a i) = 0 := by
  have hc : 0 < Multiset.card δ := by rw [← h]; simp
  have hδ : ∀ s : Seq δ, s.lbl ⟨0, hc⟩ = i := fun s => by
    have hm : s.lbl ⟨0, hc⟩ ∈ ({i} + 0 : Multiset I) := h ▸ s.mem ⟨0, hc⟩
    simpa using hm
  have hx : dotElt Q a i h = CycKLR.mk k Q a δ (x ⟨0, hc⟩) := rfl
  rw [hx, aeval_algHom_apply, ← mul_one (aeval _ _), ← sum_e, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have := CycKLR.mk_aeval_x_mul_e (Q := Q) (a := a) s hc
  rwa [hδ s] at this

/-- **The cyclotomic relation for the dot of `F_i` out of the empty block**: `a_i(x) = 0` as an
endomorphism of the functor `F_i : R^Λ(∅)-mod → R^Λ({i})-mod`. -/
theorem aeval_dot_of_zero (i : I) {δ : Multiset I} (h : {i} + 0 = δ) :
    aeval (End.of (dot.{u, v, w} Q a i h)) (a i) = 0 := by
  let y : InductionAlong.selfInt k (lastEmb Q a i h) :=
    ⟨dotElt Q a i h, intertwines_dotElt Q a i h⟩
  have hy : InductionAlong.endHom (G := ind.{u, v, w} Q a i h) (Iso.refl _) y =
      End.of (dot.{u, v, w} Q a i h) := by
    rw [InductionAlong.endHom_apply]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have hy0 : aeval y (a i) = 0 := Subtype.ext (by
    rw [aeval_subalgebra_coe]
    exact aeval_dotElt_of_zero Q a i h)
  have key := TwoRep.aeval_antihom (K := k)
    (InductionAlong.endHom (G := ind.{u, v, w} Q a i h) (Iso.refl _))
    (InductionAlong.endHom_one _) (InductionAlong.endHom_mul _) y (a i)
  rw [hy0, map_zero, hy] at key
  exact key.symm

theorem aeval_dot_of_eq_zero (i : I) {β δ : Multiset I} (hβ : β = 0) (h : {i} + β = δ) :
    aeval (End.of (dot.{u, v, w} Q a i h)) (a i) = 0 := by
  subst hβ
  exact aeval_dot_of_zero Q a i h

omit [DecidableEq I] in
/-- For the universal cyclotomic polynomials the bubble value is the vacuum trace `vacTrace`. -/
theorem coeff_modByMonic_univCycPoly [Nontrivial k] (lam : I → ℕ) (i : I) (m : ℕ) :
    (X ^ m %ₘ univCycPoly k lam i).coeff ((univCycPoly k lam i).natDegree - 1) =
      vacTrace k lam i m := by
  rw [univCycPoly_natDegree]
  rfl

section Global

variable {C : QuantumGroup.CartanDatum I} {Xw Yw : Type u₁} [AddCommGroup Xw] [AddCommGroup Yw]
  (RD : QuantumGroup.UDot.WeightDatum C Xw Yw) (Λ : Xw)

/-- **The cyclotomic relation for the global dot at the empty block**: on an object of the
weight space concentrated in the empty block, the global dot `x : F_i ⟶ F_i` satisfies
`a_i(x) = 0`. -/
theorem aeval_globalDot_app (i : I) {x y : Xw} (h : x + RD.iX i = y)
    (V : weightSpace.{u, v, w} Q a RD Λ x)
    (hV : ∀ β : WeightBlocks RD Λ x, β.1 ≠ 0 → IsZero (V β)) :
    aeval (End.of ((globalDot.{u, v, w} Q a RD Λ i h).hom.app V)) (a i) = 0 := by
  refine funext fun δ => ?_
  refine (TwoRep.Functor.map_aeval (K := k) (Pi.eval (fun δ : WeightBlocks RD Λ y =>
    ModuleCat.{max (max u v) w} (CycKLR k Q a δ.1)) δ)
      (End.of ((globalDot.{u, v, w} Q a RD Λ i h).hom.app V)) (a i)).trans ?_
  refine biproduct.hom_ext' _ _ fun p => ?_
  refine Eq.trans ?_ Limits.comp_zero.symm
  have hu := blockι_blockSumMap (blockSucc RD Λ i h)
    (fun _ _ hβ => dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ)) V p
  refine (TwoRep.comp_aeval_of_comp (K := k) _ hu (a i)).trans ?_
  by_cases hp : p.1.1 = 0
  · rw [← TwoRep.NatTrans.app_aeval, aeval_dot_of_eq_zero Q a i hp, zero_app, Limits.zero_comp]
    rfl
  · exact (Functor.map_isZero _ (hV p.1 hp)).eq_of_src _ _

variable {Q a} (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

omit [DecidableEq I] in
include hΛ in
theorem pair_blockWeight_zero (i : I) :
    RD.pair (RD.iY i) (blockWeight RD Λ 0) = -((a i).natDegree : ℤ) := by
  rw [hΛ, blockWeight, Multiset.map_zero, Multiset.sum_zero, zero_sub, map_neg]

/-- **Clockwise bubbles at the empty block** (Webster, arXiv:1309.3796v2, proof of
Proposition 3.25; Brundan, arXiv:1501.00350v1, (1.9)). At the weight `-Λ` of the empty block,
on an object concentrated in the empty block, the clockwise bubble of colour `i` with `m` dots
acts by the coefficient of `y^{deg a_i - 1}` in `y^m mod a_i`. -/
theorem globalLoc_cw_app_of_vacuum (i : I) {x z : Xw} (h₁ : x + RD.iX i = blockWeight RD Λ 0)
    (h₂ : blockWeight RD Λ 0 + RD.iX i = z)
    (V : weightSpace.{u, v, w} Q a RD Λ (blockWeight RD Λ 0))
    (hV : ∀ β : WeightBlocks RD Λ (blockWeight RD Λ 0), β.1 ≠ 0 → IsZero (V β)) (m : ℕ) :
    ((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).cw m).hom.app V =
      (Polynomial.X ^ m %ₘ a i).coeff ((a i).natDegree - 1) • 𝟙 V :=
  TwoRep.RouqLoc.cw_hom_app_of_aeval _ (pair_blockWeight_zero RD Λ hΛ i) V (ha i) rfl
    (aeval_globalDot_app Q a RD Λ i h₂ V hV) m

end Global

end KLR.CyclotomicAction

end Categorification
