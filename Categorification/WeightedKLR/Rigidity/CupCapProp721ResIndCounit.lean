/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateEF

/-!
# The counit of `𝔈_i ⊣ 𝔉_i` on generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21. The adjunction `𝔈_i ⊣ 𝔉_i` on right `T^λ`-modules
(`CupCap.blackEFAdjunction`) is built from `KLR.Diagram.MatEnd.resIndAdjunction`, whose
construction chooses a splitting `𝟙 = ∑ⱼ πⱼ ≫ ιⱼ` of `E G_Y` into copies of `G_X`. This file
records two facts that make its counit accessible independently of that choice.

* `KLR.Diagram.MatEnd.resIndAdjunction_eq_of_splitting`: the adjunction does not depend on the
  splitting (its counit is the evaluation `HomTensor.eval`, which does not involve it).
* `CupCap.resIndCounit_app_mk_tmul`: for any adjunction `Res_φ ⊣ Ind_φ` on modules, the counit is
  determined by its value on the regular module, the trace
  `z ↦ ε_A (z ⊗ 1)` on `φ(1) B φ(1)`: `ε_N (z ⊗ n) = ε_A (z ⊗ 1) • n`.

By `CupCap.capEFMateCompatible_of_counit`, the route hypothesis `CupCap.CapEFMateCompatible` is
the statement that the cap bimodule intertwines these traces on the `λ` and `λ⁺` sides.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Idempotents MulOpposite Categorification.InductionAlong

namespace Categorification.KLR.Diagram.MatEnd

universe v w

variable {C : Type*} [Category.{v} C] [Preadditive C] {D : Type*} [Category.{v} D]
  [Preadditive D] {ι κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type*} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)
  {J₂ : Type*} [Fintype J₂]
  (π₂ : J₂ → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι₂ : J₂ → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ₂ : ∑ j, π₂ j ≫ ι₂ j = 𝟙 _)

/-- **`Res ⊣ Ind` along the matrix map does not depend on the splitting**: the adjunctions
`resIndAdjunction` built from two decompositions of `E G_Y` into copies of `G_X` are equal,
since their counits are both the evaluation `HomTensor.eval` (Webster, arXiv:1309.3796v3,
Theorem 4.31). -/
theorem resIndAdjunction_eq_of_splitting :
    resIndAdjunction F he h adj adj' π ι' hπ = resIndAdjunction F he h adj adj' π₂ ι₂ hπ₂ :=
  Adjunction.ext_counit rfl

end Categorification.KLR.Diagram.MatEnd

namespace Categorification.Stendhal.CupCap

variable {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B}
  (adj : resFunctor.{0, 0} φ ⊣ InductionAlong.functor.{0, 0} φ)

/-- A generator `z ⊗ n` of an induced module with `φ(1) z = z` is fixed by `φ(1)`. -/
theorem ind_tmul_fixed {N : Type} [AddCommGroup N] [Module A N] (z : Corner φ)
    (hz : φ 1 * z.1 = z.1) (n : N) : φ 1 • (Ind.tmul z n : Ind N φ) = Ind.tmul z n := by
  rw [Ind.smul_tmul]
  congr 1
  exact Subtype.ext hz

/-- **The counit of `Res ⊣ Ind` is the trace on the regular module** (Webster,
arXiv:1309.3796v3, Theorem 4.31, for the adjunction `𝔈_i ⊣ 𝔉_i`): for any adjunction
`Res_φ ⊣ Ind_φ` on modules, a generator `z ⊗ n` of `Res (Ind N)` with `φ(1) z = z` is sent by the
counit to `ε_A (z ⊗ 1) • n`. Only naturality of the counit is used. -/
theorem resIndCounit_app_mk_tmul (N : ModuleCat.{0} A) (z : Corner φ) (hz : φ 1 * z.1 = z.1)
    (n : N) :
    (adj.counit.app N).hom (Res.mk (Ind.tmul z n) (ind_tmul_fixed z hz n)) =
      (adj.counit.app (ModuleCat.of A A)).hom
        (Res.mk (Ind.tmul z (1 : A)) (ind_tmul_fixed z hz (1 : A))) • n := by
  let f : ModuleCat.of A A ⟶ N := ModuleCat.ofHom (LinearMap.toSpanSingleton A N n)
  have nat := congrArg (fun g => g.hom (Res.mk (Ind.tmul z (1 : A))
    (ind_tmul_fixed z hz (1 : A)))) (adj.counit.naturality f)
  refine (Eq.trans ?_ nat).trans rfl
  change _ = (adj.counit.app N).hom (Res.mk (Ind.tmul z ((1 : A) • n)) _)
  exact congrArg (adj.counit.app N).hom (Res.ext (congrArg (Ind.tmul z) (one_smul A n).symm))

section Transport

variable {A' B' : Type} [Ring A'] [Ring B'] {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B')
  (hac : ∀ t, φ' (a t) = c (φ t)) (adj' : resFunctor.{0, 0} φ' ⊣ InductionAlong.functor.{0, 0} φ')

include hac in
/-- The transport of a corner element fixed by `φ(1)` is fixed by `φ'(1)`. -/
theorem transportCorner_fixed (z : Corner φ) (hz : φ 1 * z.1 = z.1) :
    φ' 1 * (transportCorner a c hac z).1 = (transportCorner a c hac z).1 := by
  change φ' 1 * c z.1 = c z.1
  rw [← map_one a, hac, ← map_mul, hz]

/-- **The counit of a transported `Res ⊣ Ind` on generators** (Webster, arXiv:1309.3796v3,
Theorem 4.31, for `𝔈_i ⊣ 𝔉_i`, which is transported along Lemma 4.29): for
`resIndAdjunctionTransport a c hac adj'`, the counit sends `z ⊗ n` to `a⁻¹ (τ' (c z)) • n`,
where `τ'` is the trace of `adj'` on the regular module (`CupCap.resIndCounit_app_mk_tmul`). -/
theorem resIndAdjunctionTransport_counit_app_mk_tmul (N : ModuleCat.{0} A) (z : Corner φ)
    (hz : φ 1 * z.1 = z.1) (n : N) :
    ((resIndAdjunctionTransport.{0, 0} a c hac adj').counit.app N).hom
        (Res.mk (Ind.tmul z n) (ind_tmul_fixed z hz n)) =
      a.symm ((adj'.counit.app (ModuleCat.of A' A')).hom
        (Res.mk (Ind.tmul (transportCorner a c hac z) (1 : A'))
          (ind_tmul_fixed _ (transportCorner_fixed a c hac z hz) (1 : A')))) • n :=
  resIndCounit_app_mk_tmul adj' ((ModuleCat.restrictScalars.{0} a.symm.toRingHom).obj N)
    (transportCorner a c hac z) (transportCorner_fixed a c hac z hz) n

end Transport

end Categorification.Stendhal.CupCap
