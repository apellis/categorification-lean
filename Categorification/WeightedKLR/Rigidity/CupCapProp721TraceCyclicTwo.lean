/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclic
import Categorification.Algebra.CornerTwoStepCoefficient

/-!
# Conjugates along composite `Res ⊣ Ind` adjunctions and the two-step trace

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21, for the crossing on `𝔉_i²`. Let `φ₁ : A₀ → A₁`,
`φ₂ : A₁ → A₂` be ring maps and `adj₁ : Res_{φ₁} ⊣ Ind_{φ₁}`, `adj₂ : Res_{φ₂} ⊣ Ind_{φ₂}`
adjunctions on modules. The counit of the composite adjunction
`Res_{φ₂} Res_{φ₁} ⊣ Ind_{φ₁} Ind_{φ₂}` is determined by the **two-step trace**
`τ₁₂(w) = τ₁(τ₂(w) φ₁(1))` on `w ∈ A₂ φ₂(1)` with `φ₂(φ₁(1)) w = w`
(`CupCap.resIndCounit₂_app_mk_tmul`), where `τ₁`, `τ₂` are the one-step traces
(`CupCap.resIndTrace`).

Let `c ∈ A₂` commute with the image of `φ₂ ∘ φ₁` and satisfy `φ₂(1) c = c`. Left multiplication
by `c` on `Res_{φ₁} Res_{φ₂}` (`resAct₂`) has two conjugates on `Ind_{φ₂} Ind_{φ₁}`: along the
composite of the adjunctions `Ind ⊣ Res` it is `m ⊗ (z ⊗ n) ↦ m φ₂(z) c φ₂(1) ⊗ (φ₁(1) ⊗ n)`
(`InductionAlong.Corner.app_tmul_tmul_of_unitGen`), and along the composite of `adj₂`, `adj₁` it
is determined by the composite counit. They agree as soon as the two-step trace is symmetric:
`τ₁₂(c w) = τ₁₂(w φ₂(φ₁(1)) c φ₂(1))` (`CupCap.conjugateEquiv_resAct₂_eq_of_trace`).

For Webster's `𝔈_i ⊣ 𝔉_i` and `c` the crossing of the two newest strands this reduces the
agreement of the conjugate crossing on `𝔉_i²` with the crossing on `𝔉_i²` (`indCrossOfEq`) to the
symmetry of the two-step trace against the crossing.

## Main definitions

* `CupCap.resIndTrace₂ adj₁ adj₂ w hw`: the two-step trace.

## Main results

* `CupCap.resIndCounit₂_app_mk_tmul`: the composite counit on generators.
* `CupCap.res_res_ind_ind_hom_ext`: linear maps out of `Res Res Ind Ind N` are determined on the
  generators `w ⊗ (φ₁(1) ⊗ n)`.
* `CupCap.conjugateEquiv_resAct₂_eq_of_trace`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory MulOpposite InductionAlong

section TwoStep

variable {A₀ A₁ A₂ : Type} [Ring A₀] [Ring A₁] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁} {φ₂ : A₁ →ₙ+* A₂}
  (adj₁ : resFunctor.{0, 0} φ₁ ⊣ InductionAlong.functor.{0, 0} φ₁)
  (adj₂ : resFunctor.{0, 0} φ₂ ⊣ InductionAlong.functor.{0, 0} φ₂)

/-- An element fixed by `φ₂(φ₁(1))` is fixed by `φ₂(1)`. -/
theorem fixed_of_fixed₂ {w : Corner φ₂} (hw : φ₂ (φ₁ 1) * w.1 = w.1) : φ₂ 1 * w.1 = w.1 := by
  rw [← hw, ← mul_assoc, ← map_mul, one_mul]

omit [Ring A₀] in
/-- The trace of `Res ⊣ Ind` is linear for the left action through `φ`:
`τ(φ(a) w) = a τ(w)`. -/
theorem resIndTrace_map_smul (a : A₁) (w : Corner φ₂) (hw : φ₂ 1 * w.1 = w.1)
    (haw : φ₂ 1 * (φ₂ a • w).1 = (φ₂ a • w).1) :
    resIndTrace adj₂ (φ₂ a • w) haw = a * resIndTrace adj₂ w hw := by
  unfold resIndTrace
  have hm := (adj₂.counit.app (ModuleCat.of A₁ A₁)).hom.map_smul a
    (Res.mk (Ind.tmul w (1 : A₁)) (ind_tmul_fixed w hw (1 : A₁)))
  refine Eq.trans ?_ hm
  congr 1

/-- The one-step trace of an element fixed by `φ₂(φ₁(1))` is fixed by `φ₁(1)` on the left. -/
theorem one_mul_resIndTrace_of_fixed₂ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    φ₁ 1 * resIndTrace adj₂ w (fixed_of_fixed₂ hw) = resIndTrace adj₂ w (fixed_of_fixed₂ hw) := by
  have haw : φ₂ 1 * (φ₂ (φ₁ 1) • w).1 = (φ₂ (φ₁ 1) • w).1 := by
    change φ₂ 1 * (φ₂ (φ₁ 1) * w.1) = φ₂ (φ₁ 1) * w.1
    rw [hw]; exact fixed_of_fixed₂ hw
  rw [← resIndTrace_map_smul adj₂ (φ₁ 1) w (fixed_of_fixed₂ hw) haw]
  exact resIndTrace_congr adj₂ (Subtype.ext hw) _ _

/-- The corner element `τ₂(w) φ₁(1)` is fixed by `φ₁(1)`. -/
theorem trace_smul_unitGen_fixed (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    φ₁ 1 * (resIndTrace adj₂ w (fixed_of_fixed₂ hw) • unitGen φ₁).1 =
      (resIndTrace adj₂ w (fixed_of_fixed₂ hw) • unitGen φ₁).1 := by
  change φ₁ 1 * (resIndTrace adj₂ w _ * φ₁ 1) = resIndTrace adj₂ w _ * φ₁ 1
  rw [← mul_assoc, one_mul_resIndTrace_of_fixed₂ adj₂ w hw]

/-- **The two-step trace** of the composite of `adj₂` and `adj₁` (Webster, arXiv:1309.3796v3,
Theorem 4.31): `τ₁₂(w) = τ₁(τ₂(w) φ₁(1))` for `w ∈ A₂ φ₂(1)` with `φ₂(φ₁(1)) w = w`. -/
def resIndTrace₂ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) : A₀ :=
  resIndTrace adj₁ (resIndTrace adj₂ w (fixed_of_fixed₂ hw) • unitGen φ₁)
    (trace_smul_unitGen_fixed adj₂ w hw)

theorem resIndTrace₂_congr {w w' : Corner φ₂} (e : w = w') (hw : φ₂ (φ₁ 1) * w.1 = w.1)
    (hw' : φ₂ (φ₁ 1) * w'.1 = w'.1) :
    resIndTrace₂ adj₁ adj₂ w hw = resIndTrace₂ adj₁ adj₂ w' hw' := by
  subst e; rfl

/-- A generator `w ⊗ (φ₁(1) ⊗ n)` of `Ind_{φ₂} Ind_{φ₁} N` with `φ₂(φ₁(1)) w = w` lies in
`Res_{φ₁} Res_{φ₂}`. -/
theorem res_ind_tmul_fixed₂ {N : Type} [AddCommGroup N] [Module A₀ N] (w : Corner φ₂)
    (hw : φ₂ (φ₁ 1) * w.1 = w.1) (n : N) :
    φ₁ 1 • (Res.mk (Ind.tmul w (Ind.tmul (unitGen φ₁) n))
        (ind_tmul_fixed w (fixed_of_fixed₂ hw) _) : Res φ₂ (Ind (Ind N φ₁) φ₂)) =
      Res.mk (Ind.tmul w (Ind.tmul (unitGen φ₁) n)) (ind_tmul_fixed w (fixed_of_fixed₂ hw) _) :=
  Res.ext (by
    rw [Res.val_smul, Res.val_mk, Ind.smul_tmul]
    exact congrArg (Ind.tmul · _) (Subtype.ext hw))

/-- The generator `w ⊗ (φ₁(1) ⊗ n)` of `Res_{φ₁} Res_{φ₂} Ind_{φ₂} Ind_{φ₁} N`. -/
abbrev gen₂ {N : Type} [AddCommGroup N] [Module A₀ N] (w : Corner φ₂)
    (hw : φ₂ (φ₁ 1) * w.1 = w.1) (n : N) : Res φ₁ (Res φ₂ (Ind (Ind N φ₁) φ₂)) :=
  Res.mk (Res.mk (Ind.tmul w (Ind.tmul (unitGen φ₁) n))
    (ind_tmul_fixed w (fixed_of_fixed₂ hw) _)) (res_ind_tmul_fixed₂ w hw n)

/-- **The counit of the composite adjunction on generators** (Webster, arXiv:1309.3796v3,
Theorem 4.31): `ε (w ⊗ (φ₁(1) ⊗ n)) = τ₁₂(w) • n`. -/
theorem resIndCounit₂_app_mk_tmul (N : ModuleCat.{0} A₀) (w : Corner φ₂)
    (hw : φ₂ (φ₁ 1) * w.1 = w.1) (n : N) :
    ((adj₂.comp adj₁).counit.app N).hom (gen₂ w hw n) = resIndTrace₂ adj₁ adj₂ w hw • n := by
  rw [Adjunction.comp_counit_app]
  change (adj₁.counit.app N).hom (((resFunctor φ₁).map
    (adj₂.counit.app ((InductionAlong.functor.{0, 0} φ₁).obj N))).hom (gen₂ w hw n)) = _
  have e : ((resFunctor φ₁).map
      (adj₂.counit.app ((InductionAlong.functor.{0, 0} φ₁).obj N))).hom (gen₂ w hw n) =
      Res.mk (Ind.tmul (resIndTrace adj₂ w (fixed_of_fixed₂ hw) • unitGen φ₁) n)
        (ind_tmul_fixed _ (trace_smul_unitGen_fixed adj₂ w hw) n) := by
    apply Res.ext
    rw [Res.val_mk]
    refine (resIndCounit_app_mk_tmul adj₂ ((InductionAlong.functor.{0, 0} φ₁).obj N) w
      (fixed_of_fixed₂ hw) (Ind.tmul (unitGen φ₁) n)).trans ?_
    exact Ind.smul_tmul (resIndTrace adj₂ w (fixed_of_fixed₂ hw)) (unitGen φ₁) n
  rw [e, resIndCounit_app_mk_tmul adj₁ N _ (trace_smul_unitGen_fixed adj₂ w hw) n]
  rfl

/-- **Linear maps out of `Res_{φ₁} Res_{φ₂} Ind_{φ₂} Ind_{φ₁} N` are determined on the
generators** `w ⊗ (φ₁(1) ⊗ n)` with `φ₂(φ₁(1)) w = w`. -/
theorem res_res_ind_ind_hom_ext {N P : Type} [AddCommGroup N] [Module A₀ N] [AddCommGroup P]
    [Module A₀ P] {f g : Res φ₁ (Res φ₂ (Ind (Ind N φ₁) φ₂)) →ₗ[A₀] P}
    (h : ∀ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) (n : N),
      f (gen₂ w hw n) = g (gen₂ w hw n)) : f = g := by
  set e : A₂ := φ₂ (φ₁ 1) with he
  have hee : e * e = e := by rw [he, ← map_mul, unit_mul_unit]
  have he1 : φ₂ 1 * e = e := by rw [he, ← map_mul, one_mul]
  have hfix₁ : ∀ t : Ind (Ind N φ₁) φ₂, φ₂ 1 • (e • t) = e • t := fun t => by
    rw [smul_smul, he1]
  have hfix₂ : ∀ t : Ind (Ind N φ₁) φ₂, φ₁ 1 • (Res.mk (e • t) (hfix₁ t) :
      Res φ₂ (Ind (Ind N φ₁) φ₂)) = Res.mk (e • t) (hfix₁ t) := fun t =>
    Res.ext (by rw [Res.val_smul, Res.val_mk, smul_smul, hee])
  let R : Ind (Ind N φ₁) φ₂ → Res φ₁ (Res φ₂ (Ind (Ind N φ₁) φ₂)) := fun t =>
    Res.mk (Res.mk (e • t) (hfix₁ t)) (hfix₂ t)
  have hR0 : R 0 = 0 := Res.ext (Res.ext (smul_zero _))
  have hRadd : ∀ s t, R (s + t) = R s + R t := fun s t => Res.ext (Res.ext (smul_add _ _ _))
  have hfixw : ∀ m : Corner φ₂, φ₂ (φ₁ 1) * (e • m).1 = (e • m).1 := fun m => by
    change e * (e * m.1) = e * m.1
    rw [← mul_assoc, hee]
  have key : ∀ t, f (R t) = g (R t) := by
    intro t
    induction t using Ind.induction_on with
    | zero => rw [hR0, map_zero, map_zero]
    | add s t hs ht => rw [hRadd, map_add, map_add, hs, ht]
    | tmul m y =>
      induction y using Ind.induction_on with
      | zero =>
        have h0 : R (Ind.tmul m 0) = 0 := by rw [Ind.tmul_zero, hR0]
        rw [h0, map_zero, map_zero]
      | add s t hs ht => rw [Ind.tmul_add, hRadd, map_add, map_add, hs, ht]
      | tmul z n =>
        have hz : (Ind.tmul z n : Ind N φ₁) = z.1 • Ind.tmul (unitGen φ₁) n := by
          rw [Ind.smul_tmul]
          exact congrArg (Ind.tmul · n) (Subtype.ext z.2.symm)
        have hR : R (Ind.tmul m (Ind.tmul z n)) = gen₂ (e • (op z.1 • m)) (hfixw _) n := by
          apply Res.ext; apply Res.ext
          change e • Ind.tmul m (Ind.tmul z n) = Ind.tmul (e • (op z.1 • m)) _
          rw [hz, ← Ind.op_smul_tmul, Ind.smul_tmul]
        rw [hR]
        exact h _ _ n
  ext r
  have hr : r = R r.val.val := by
    apply Res.ext; apply Res.ext
    change r.val.val = e • r.val.val
    have := congrArg Res.val r.prop
    rw [Res.val_smul] at this
    exact this.symm
  rw [hr]
  exact key _

private theorem conjugateEquiv_eq_of_counit₂ {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (β : R₁ ⟶ R₂)
    (h : ∀ d : D, L₂.map (β.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    conjugateEquiv adj₁ adj₂ α = β := by
  ext d
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d]
  exact conjugateEquiv_counit adj₁ adj₂ α d

variable {c : A₂} (hfix : φ₂ 1 * c = c) (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)

include hc in
/-- Left multiplication by `c` preserves the generators' fixedness. -/
theorem smul_fixed₂ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    φ₂ (φ₁ 1) * (c • w).1 = (c • w).1 := by
  change φ₂ (φ₁ 1) * (c * w.1) = c * w.1
  rw [← mul_assoc, ← hc 1, mul_assoc, hw]

/-- The corner element `w φ₂(φ₁(1)) c φ₂(1)` is fixed by `φ₂(φ₁(1))`. -/
theorem twoStepRightElem_fixed₂ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    φ₂ (φ₁ 1) * (Corner.twoStepRightElem c w (unitGen φ₁)).1 =
      (Corner.twoStepRightElem c w (unitGen φ₁)).1 := by
  rw [Corner.twoStepRightElem_val, ← mul_assoc, hw]

variable (τ : resFunctor.{0, 0} φ₂ ⋙ resFunctor.{0, 0} φ₁ ⟶ resFunctor φ₂ ⋙ resFunctor φ₁)
  (hτ : ∀ M, τ.app M = ModuleCat.ofHom (resAct₂ c hfix hc M))

include hτ in
/-- **The conjugate of left multiplication along composite `Res ⊣ Ind` adjunctions is the
conjugate along the composite `Ind ⊣ Res`, when the two-step trace is symmetric against `c`**
(Webster, arXiv:1309.3796v3, Theorem 4.31): if `τ₁₂(c w) = τ₁₂(w φ₂(φ₁(1)) c φ₂(1))` for
every `w ∈ A₂ φ₂(1)` with `φ₂(φ₁(1)) w = w`, then the conjugate of `resAct₂ c` along the
composite of `adj₂` and `adj₁` is its conjugate along the composite of the adjunctions
`Ind ⊣ Res`. -/
theorem conjugateEquiv_resAct₂_eq_of_trace
    (htr : ∀ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1),
      resIndTrace₂ adj₁ adj₂ (c • w) (smul_fixed₂ hc w hw) =
        resIndTrace₂ adj₁ adj₂ (Corner.twoStepRightElem c w (unitGen φ₁))
          (twoStepRightElem_fixed₂ w hw)) :
    conjugateEquiv (adj₂.comp adj₁) (adj₂.comp adj₁) τ =
      (conjugateEquiv ((adjunction.{0, 0} φ₁).comp (adjunction.{0, 0} φ₂))
        ((adjunction φ₁).comp (adjunction φ₂))).symm τ := by
  refine conjugateEquiv_eq_of_counit₂ _ _ τ _ fun d => ?_
  refine ModuleCat.hom_ext (res_res_ind_ind_hom_ext fun w hw n => ?_)
  have hβ := Corner.app_tmul_tmul_of_unitGen c
    ((conjugateEquiv ((adjunction.{0, 0} φ₁).comp (adjunction.{0, 0} φ₂))
      ((adjunction φ₁).comp (adjunction φ₂))).symm τ)
    (conjugateEquiv_symm_resAct₂_tmul φ₁ φ₂ hc hfix τ hτ) d w (unitGen φ₁) n
  have hL : ((resFunctor φ₂ ⋙ resFunctor φ₁).map
      (((conjugateEquiv ((adjunction.{0, 0} φ₁).comp (adjunction.{0, 0} φ₂))
        ((adjunction φ₁).comp (adjunction φ₂))).symm τ).app d)).hom (gen₂ w hw n) =
      gen₂ (Corner.twoStepRightElem c w (unitGen φ₁)) (twoStepRightElem_fixed₂ w hw) n :=
    Res.ext (Res.ext hβ)
  have hR : (τ.app (((InductionAlong.functor.{0, 0} φ₁) ⋙
      InductionAlong.functor.{0, 0} φ₂).obj d)).hom (gen₂ w hw n) =
      gen₂ (c • w) (smul_fixed₂ hc w hw) n := by
    rw [hτ]
    exact Res.ext (Res.ext (Ind.smul_tmul _ _ _))
  change ((adj₂.comp adj₁).counit.app d).hom (((resFunctor φ₂ ⋙ resFunctor φ₁).map
      (((conjugateEquiv ((adjunction.{0, 0} φ₁).comp (adjunction.{0, 0} φ₂))
        ((adjunction φ₁).comp (adjunction φ₂))).symm τ).app d)).hom (gen₂ w hw n)) =
    ((adj₂.comp adj₁).counit.app d).hom ((τ.app (((InductionAlong.functor.{0, 0} φ₁) ⋙
      InductionAlong.functor.{0, 0} φ₂).obj d)).hom (gen₂ w hw n))
  rw [hL, hR, resIndCounit₂_app_mk_tmul adj₁ adj₂ d _ (twoStepRightElem_fixed₂ w hw) n,
    resIndCounit₂_app_mk_tmul adj₁ adj₂ d _ (smul_fixed₂ hc w hw) n, htr w hw]

end TwoStep

section Neg

variable {A₀ A₁ A₂ : Type} [Ring A₀] [Ring A₁] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁} {φ₂ : A₁ →ₙ+* A₂}
  (adj₁ : resFunctor.{0, 0} φ₁ ⊣ InductionAlong.functor.{0, 0} φ₁)
  (adj₂ : resFunctor.{0, 0} φ₂ ⊣ InductionAlong.functor.{0, 0} φ₂)

omit [Ring A₀] in
/-- The one-step trace is additive: `τ(-z) = -τ(z)`. -/
theorem resIndTrace_neg (z : Corner φ₂) (hz : φ₂ 1 * z.1 = z.1)
    (hz' : φ₂ 1 * (-z).1 = (-z).1) : resIndTrace adj₂ (-z) hz' = -resIndTrace adj₂ z hz := by
  unfold resIndTrace
  have hm := (adj₂.counit.app (ModuleCat.of A₁ A₁)).hom.map_neg
    (Res.mk (Ind.tmul z (1 : A₁)) (ind_tmul_fixed z hz (1 : A₁)))
  refine Eq.trans ?_ hm
  congr 1

theorem resIndTrace₂_neg (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1)
    (hw' : φ₂ (φ₁ 1) * (-w).1 = (-w).1) :
    resIndTrace₂ adj₁ adj₂ (-w) hw' = -resIndTrace₂ adj₁ adj₂ w hw := by
  unfold resIndTrace₂
  have h1 : resIndTrace adj₂ (-w) (fixed_of_fixed₂ hw') =
      -resIndTrace adj₂ w (fixed_of_fixed₂ hw) := resIndTrace_neg adj₂ w _ _
  have h2 : resIndTrace adj₂ (-w) (fixed_of_fixed₂ hw') • unitGen φ₁ =
      -(resIndTrace adj₂ w (fixed_of_fixed₂ hw) • unitGen φ₁) := by
    rw [h1, neg_smul]
  rw [resIndTrace_congr adj₁ h2 _ (by
      rw [← h2]; exact trace_smul_unitGen_fixed adj₂ (-w) hw'),
    resIndTrace_neg adj₁ _ (trace_smul_unitGen_fixed adj₂ w hw)]

/-- **Symmetry of the two-step trace against `-c` gives symmetry against `c`.** -/
theorem resIndTrace₂_cyclic_of_neg {c : A₂} (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)
    (hc' : ∀ a, (-c) * φ₂ (φ₁ a) = φ₂ (φ₁ a) * (-c))
    (h : ∀ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1),
      resIndTrace₂ adj₁ adj₂ ((-c) • w) (smul_fixed₂ hc' w hw) =
        resIndTrace₂ adj₁ adj₂ (Corner.twoStepRightElem (-c) w (unitGen φ₁))
          (twoStepRightElem_fixed₂ w hw))
    (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    resIndTrace₂ adj₁ adj₂ (c • w) (smul_fixed₂ hc w hw) =
      resIndTrace₂ adj₁ adj₂ (Corner.twoStepRightElem c w (unitGen φ₁))
        (twoStepRightElem_fixed₂ w hw) := by
  have e1 : (-c) • w = -(c • w) := neg_smul c w
  have e2 : Corner.twoStepRightElem (-c) w (unitGen φ₁) =
      -Corner.twoStepRightElem c w (unitGen φ₁) := Subtype.ext (by
    change w.1 * (φ₂ (φ₁ 1) * ((-c) * φ₂ 1)) = -(w.1 * (φ₂ (φ₁ 1) * (c * φ₂ 1)))
    rw [neg_mul, mul_neg, mul_neg])
  have h' := h w hw
  rw [resIndTrace₂_congr adj₁ adj₂ e1 _ (by rw [← e1]; exact smul_fixed₂ hc' w hw),
    resIndTrace₂_congr adj₁ adj₂ e2 _ (by rw [← e2]; exact twoStepRightElem_fixed₂ w hw),
    resIndTrace₂_neg adj₁ adj₂ _ (smul_fixed₂ hc w hw),
    resIndTrace₂_neg adj₁ adj₂ _ (twoStepRightElem_fixed₂ w hw)] at h'
  exact neg_injective h'

/-- Symmetry of the two-step trace against `c` follows from symmetry against an element equal
to `c`. -/
theorem resIndTrace₂_cyclic_of_eq {c c' : A₂} (e : c = c')
    (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)
    (hc' : ∀ a, c' * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c')
    (h : ∀ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1),
      resIndTrace₂ adj₁ adj₂ (c' • w) (smul_fixed₂ hc' w hw) =
        resIndTrace₂ adj₁ adj₂ (Corner.twoStepRightElem c' w (unitGen φ₁))
          (twoStepRightElem_fixed₂ w hw))
    (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    resIndTrace₂ adj₁ adj₂ (c • w) (smul_fixed₂ hc w hw) =
      resIndTrace₂ adj₁ adj₂ (Corner.twoStepRightElem c w (unitGen φ₁))
        (twoStepRightElem_fixed₂ w hw) := by
  subst e
  exact h w hw

end Neg

section Transport

variable {A₀ A₁ A₂ A₀' A₁' A₂' : Type} [Ring A₀] [Ring A₁] [Ring A₂] [Ring A₀'] [Ring A₁']
  [Ring A₂'] {φ₁ : A₀ →ₙ+* A₁} {φ₂ : A₁ →ₙ+* A₂} {φ₁' : A₀' →ₙ+* A₁'} {φ₂' : A₁' →ₙ+* A₂'}
  (a₀ : A₀ ≃+* A₀') (a₁ : A₁ ≃+* A₁') (a₂ : A₂ ≃+* A₂') (hac₁ : ∀ t, φ₁' (a₀ t) = a₁ (φ₁ t))
  (hac₂ : ∀ t, φ₂' (a₁ t) = a₂ (φ₂ t))
  (adj₁' : resFunctor.{0, 0} φ₁' ⊣ InductionAlong.functor.{0, 0} φ₁')
  (adj₂' : resFunctor.{0, 0} φ₂' ⊣ InductionAlong.functor.{0, 0} φ₂')

include hac₁ hac₂ in
/-- The transport of a generator fixed by `φ₂(φ₁(1))` is fixed by `φ₂'(φ₁'(1))`. -/
theorem transportCorner_fixed₂ (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    φ₂' (φ₁' 1) * (transportCorner a₁ a₂ hac₂ w).1 = (transportCorner a₁ a₂ hac₂ w).1 := by
  change φ₂' (φ₁' 1) * a₂ w.1 = a₂ w.1
  rw [← map_one a₀, hac₁, hac₂, ← map_mul, hw]

/-- **The two-step trace of transported adjunctions** (Webster, arXiv:1309.3796v3,
Theorem 4.31, transported along Lemma 4.29): `τ₁₂(w) = a₀⁻¹ (τ'₁₂ (a₂ w))`. -/
theorem resIndTrace₂_transport (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    resIndTrace₂ (resIndAdjunctionTransport.{0, 0} a₀ a₁ hac₁ adj₁')
        (resIndAdjunctionTransport.{0, 0} a₁ a₂ hac₂ adj₂') w hw =
      a₀.symm (resIndTrace₂ adj₁' adj₂' (transportCorner a₁ a₂ hac₂ w)
        (transportCorner_fixed₂ a₀ a₁ a₂ hac₁ hac₂ w hw)) := by
  unfold resIndTrace₂
  rw [resIndTrace_transport]
  congr 1
  refine resIndTrace_congr adj₁' (Subtype.ext ?_) _ _
  change a₁ (resIndTrace (resIndAdjunctionTransport.{0, 0} a₁ a₂ hac₂ adj₂') w
    (fixed_of_fixed₂ hw) * φ₁ 1) = _ * φ₁' 1
  rw [resIndTrace_transport, map_mul, RingEquiv.apply_symm_apply, ← hac₁, map_one]

variable {c₀ : A₂} (hc₀ : ∀ a, c₀ * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c₀)

include hac₁ hac₂ hc₀ in
/-- The image of an element commuting with the image of `φ₂ ∘ φ₁` commutes with the image of
`φ₂' ∘ φ₁'`. -/
theorem transport_commute₂ (t : A₀') :
    a₂ c₀ * φ₂' (φ₁' t) = φ₂' (φ₁' t) * a₂ c₀ := by
  rw [← a₀.apply_symm_apply t, hac₁, hac₂, ← map_mul, ← map_mul, hc₀]

/-- **Symmetry of the two-step trace transports along ring isomorphisms** (Webster,
arXiv:1309.3796v3, Theorem 4.31, transported along Lemma 4.29). -/
theorem resIndTrace₂_transport_cyclic
    (h' : ∀ (w : Corner φ₂') (hw : φ₂' (φ₁' 1) * w.1 = w.1),
      resIndTrace₂ adj₁' adj₂' (a₂ c₀ • w)
          (smul_fixed₂ (transport_commute₂ a₀ a₁ a₂ hac₁ hac₂ hc₀) w hw) =
        resIndTrace₂ adj₁' adj₂' (Corner.twoStepRightElem (a₂ c₀) w (unitGen φ₁'))
          (twoStepRightElem_fixed₂ w hw))
    (w : Corner φ₂) (hw : φ₂ (φ₁ 1) * w.1 = w.1) :
    resIndTrace₂ (resIndAdjunctionTransport.{0, 0} a₀ a₁ hac₁ adj₁')
        (resIndAdjunctionTransport.{0, 0} a₁ a₂ hac₂ adj₂') (c₀ • w) (smul_fixed₂ hc₀ w hw) =
      resIndTrace₂ (resIndAdjunctionTransport.{0, 0} a₀ a₁ hac₁ adj₁')
        (resIndAdjunctionTransport.{0, 0} a₁ a₂ hac₂ adj₂')
        (Corner.twoStepRightElem c₀ w (unitGen φ₁)) (twoStepRightElem_fixed₂ w hw) := by
  rw [resIndTrace₂_transport, resIndTrace₂_transport]
  congr 1
  have hwt := transportCorner_fixed₂ a₀ a₁ a₂ hac₁ hac₂ w hw
  refine (resIndTrace₂_congr adj₁' adj₂' (Subtype.ext (map_mul a₂ c₀ w.1)) _
    (smul_fixed₂ (transport_commute₂ a₀ a₁ a₂ hac₁ hac₂ hc₀) _ hwt)).trans
      ((h' _ hwt).trans (resIndTrace₂_congr adj₁' adj₂' (Subtype.ext ?_) _ _))
  change a₂ w.1 * (φ₂' (φ₁' 1) * (a₂ c₀ * φ₂' 1)) =
    a₂ (w.1 * (φ₂ (φ₁ 1) * (c₀ * φ₂ 1)))
  rw [map_mul, map_mul, map_mul, ← map_one a₀, hac₁, hac₂, ← map_one a₁, hac₂]

end Transport

end Categorification.Stendhal.CupCap
