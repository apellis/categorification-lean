/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.WeightedKLR.Induction.Restriction

/-!
# Graded restriction for weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4: the
restriction `Res_{ν';ν''} L = e_{ν';ν''} L` along `ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}`,
which gives the coproduct of Theorem 2.19 on graded Grothendieck groups.

The idempotent `e_{ν';ν''} = ι(1)` has degree `0` (`GradingDatum.inductionMap_one_mem_klrGrade`),
so for a graded `W_{ν'+ν''}`-module `L` the subspace `e_{ν';ν''} L` is graded by
`(e L)_d = e L ∩ L_d`, and `ι` being degree-preserving makes it a graded
`W_{ν'} ⊗ W_{ν''}`-module. Projectivity and finite generation are those of the ungraded
restriction (`Juxtapose.res_projective`, `Juxtapose.res_finite`), under Webster's standing
hypothesis. Restriction carries no grading shift.

## Main definitions and results

* `Juxtapose.ResIdemW k Γ ν' ν'' L`: `e_{ν';ν''} L` as a `k`-subspace of `L`, a
  `W_{ν'} ⊗ W_{ν''}`-module, and `Juxtapose.resIdemWEquivRes`, its identification with `res`.
* `GradingDatum.resGProj G ν' ν'' hD hZ hS L`: `Res_{ν';ν''} L` in `(W_{ν'} ⊗ W_{ν''})-pmod`.
* `GradingDatum.resK0`: the `ℤ[q, q⁻¹]`-linear map `K₀(W_{ν'+ν''}) → K₀(W_{ν'} ⊗ W_{ν''})`,
  `[L] ↦ [Res_{ν';ν''} L]`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open scoped TensorProduct
open Categorification.Graded GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

section ResIdemW

variable (k Γ ν' ν'') in
/-- `e_{ν';ν''} L` as the `k`-subspace `{l | e_{ν';ν''} l = l}` of a `W_{ν'+ν''}`-module. -/
abbrev ResIdemW (L : Type*) [AddCommGroup L] [Module k L]
    [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [IsScalarTower k (WeightedKLRAlgebra k Γ (ν' + ν'')) L] : Type _ :=
  idemSubspace k L (inductionMap k Γ ν' ν'' 1)

variable {L : Type*} [AddCommGroup L] [Module k L] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
  [IsScalarTower k (WeightedKLRAlgebra k Γ (ν' + ν'')) L]

theorem inductionMap_smul_mem_resIdemW (t : TensorW k Γ ν' ν'') (l : L) :
    inductionMap k Γ ν' ν'' t • l ∈ idemSubspace k L (inductionMap k Γ ν' ν'' 1) := by
  rw [mem_idemSubspace, smul_smul, ← map_mul, one_mul]

instance : SMul (TensorW k Γ ν' ν'') (ResIdemW k Γ ν' ν'' L) :=
  ⟨fun t l => ⟨inductionMap k Γ ν' ν'' t • l.1, inductionMap_smul_mem_resIdemW t l.1⟩⟩

theorem coe_resIdemW_smul (t : TensorW k Γ ν' ν'') (l : ResIdemW k Γ ν' ν'' L) :
    ((t • l : ResIdemW k Γ ν' ν'' L) : L) = inductionMap k Γ ν' ν'' t • (l : L) := rfl

instance : Module (TensorW k Γ ν' ν'') (ResIdemW k Γ ν' ν'' L) where
  one_smul l := Subtype.ext l.2
  mul_smul s t l := Subtype.ext (by simp only [coe_resIdemW_smul, map_mul, mul_smul])
  smul_zero t := Subtype.ext (by simp only [coe_resIdemW_smul, ZeroMemClass.coe_zero, smul_zero])
  smul_add t m n := Subtype.ext (by simp only [coe_resIdemW_smul, Submodule.coe_add, smul_add])
  add_smul s t n := Subtype.ext (by simp only [coe_resIdemW_smul, map_add, add_smul,
    Submodule.coe_add])
  zero_smul n := Subtype.ext (by simp only [coe_resIdemW_smul, map_zero, zero_smul,
    ZeroMemClass.coe_zero])

instance : IsScalarTower k (TensorW k Γ ν' ν'') (ResIdemW k Γ ν' ν'' L) where
  smul_assoc c t n := Subtype.ext (by
    rw [coe_resIdemW_smul, Submodule.coe_smul, coe_resIdemW_smul, map_smul, smul_assoc])

variable (L) in
/-- `e_{ν';ν''} L` as a `k`-subspace and Webster's restriction `res` (an additive subgroup) are
the same `W_{ν'} ⊗ W_{ν''}`-module. -/
def resIdemWEquivRes : ResIdemW k Γ ν' ν'' L ≃ₗ[TensorW k Γ ν' ν''] res k Γ ν' ν'' L where
  toFun l := InductionAlong.Res.mk (l : L) l.2
  invFun l := ⟨l.val, l.prop⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {L' : Type*} [AddCommGroup L'] [Module k L'] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L']
  [IsScalarTower k (WeightedKLRAlgebra k Γ (ν' + ν'')) L']

/-- The restriction `e_{ν';ν''} f` of a `W_{ν'+ν''}`-linear map. -/
def resIdemWMap (f : L →ₗ[WeightedKLRAlgebra k Γ (ν' + ν'')] L') :
    ResIdemW k Γ ν' ν'' L →ₗ[TensorW k Γ ν' ν''] ResIdemW k Γ ν' ν'' L' where
  toFun l := ⟨f l, by rw [mem_idemSubspace, ← map_smul]; exact congrArg f l.2⟩
  map_add' m n := Subtype.ext (map_add f _ _)
  map_smul' t n := Subtype.ext (map_smul f (inductionMap k Γ ν' ν'' t) (n : L))

@[simp] theorem coe_resIdemWMap (f : L →ₗ[WeightedKLRAlgebra k Γ (ν' + ν'')] L')
    (l : ResIdemW k Γ ν' ν'' L) : ((resIdemWMap f l : ResIdemW k Γ ν' ν'' L') : L') = f l := rfl

/-- The restriction of an isomorphism. -/
def resIdemWCongr (f : L ≃ₗ[WeightedKLRAlgebra k Γ (ν' + ν'')] L') :
    ResIdemW k Γ ν' ν'' L ≃ₗ[TensorW k Γ ν' ν''] ResIdemW k Γ ν' ν'' L' :=
  LinearEquiv.ofLinearMap (resIdemWMap f.toLinearMap) (resIdemWMap f.symm.toLinearMap)
    (LinearMap.ext fun n => Subtype.ext (f.apply_symm_apply (n : L')))
    (LinearMap.ext fun n => Subtype.ext (f.symm_apply_apply (n : L)))

variable (L L') in
/-- `e_{ν';ν''} (L × L') ≅ e_{ν';ν''} L × e_{ν';ν''} L'`. -/
def resIdemWProd :
    ResIdemW k Γ ν' ν'' (L × L') ≃ₗ[TensorW k Γ ν' ν'']
      ResIdemW k Γ ν' ν'' L × ResIdemW k Γ ν' ν'' L' where
  toFun n := (⟨(n : L × L').1, congrArg Prod.fst n.2⟩, ⟨(n : L × L').2, congrArg Prod.snd n.2⟩)
  invFun n := ⟨((n.1 : L), (n.2 : L')), Prod.ext n.1.2 n.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end ResIdemW

end Juxtapose

open Juxtapose

namespace GradingDatum

variable (G : GradingDatum Γ) {ν' ν'' : I →₀ ℕ}

/-- `e_{ν';ν''} L` is a graded `W_{ν'} ⊗ W_{ν''}`-module, for `(e L)_d = e L ∩ L_d` and the
tensor product grading of `W_{ν'} ⊗ W_{ν''}`. -/
theorem resIdemW_gradedSMul {L : Type*} [AddCommGroup L] [Module k L]
    [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L]
    [IsScalarTower k (WeightedKLRAlgebra k Γ (ν' + ν'')) L] (ℒ : ℤ → Submodule k L)
    [SetLike.GradedSMul (G.klrGrade (ν' + ν'')) ℒ] :
    SetLike.GradedSMul (tensorGrading (G.klrGrade ν') (G.klrGrade ν''))
      (idem ℒ (inductionMap k Γ ν' ν'' 1) : ℤ → Submodule k (ResIdemW k Γ ν' ν'' L)) where
  smul_mem _ _ _ _ ht hl := by
    rw [mem_idem, coe_resIdemW_smul]
    exact SetLike.GradedSMul.smul_mem (A := G.klrGrade (ν' + ν'')) (G.inductionMap_mem_klrGrade ht)
      hl

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

variable (ν' ν'') in
/-- **Graded restriction** `Res_{ν';ν''} L = e_{ν';ν''} L` of a finitely generated graded
projective `W_{ν'+ν''}`-module, as a finitely generated graded projective
`W_{ν'} ⊗ W_{ν''}`-module (Webster, arXiv:1209.2463v4, §2.4), under the standing hypothesis.
There is no grading shift. -/
def resGProj (L : GProj (G.klrGrade (ν' + ν''))) :
    GProj (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) :=
  have := res_finite Γ ν' ν'' hD hZ hS L.carrier
  have := res_projective Γ ν' ν'' hD hZ hS L.carrier
  { carrier := ResIdemW k Γ ν' ν'' L.carrier
    grading := idem L.grading (inductionMap k Γ ν' ν'' 1)
    decomposition := idemDecomposition L.grading G.inductionMap_one_mem_klrGrade
    gradedSMul := G.resIdemW_gradedSMul L.grading
    finite := Module.Finite.equiv (resIdemWEquivRes L.carrier).symm
    projective := Module.Projective.of_equiv (resIdemWEquivRes L.carrier).symm }

theorem resGProj_carrier (L : GProj (G.klrGrade (ν' + ν''))) :
    (G.resGProj ν' ν'' hD hZ hS L).carrier = ResIdemW k Γ ν' ν'' L.carrier := rfl

@[simp] theorem mem_resGProj_grading {L : GProj (G.klrGrade (ν' + ν''))} {d : ℤ}
    {l : ResIdemW k Γ ν' ν'' L.carrier} :
    l ∈ (G.resGProj ν' ν'' hD hZ hS L).grading d ↔ (l : L.carrier) ∈ L.grading d := Iff.rfl

/-- `Res L ≅ Res L'` for `L ≅ L'`. -/
def resGProjCongr {L L' : GProj (G.klrGrade (ν' + ν''))} (e : L.Iso L') :
    (G.resGProj ν' ν'' hD hZ hS L).Iso (G.resGProj ν' ν'' hD hZ hS L') where
  toLinearEquiv := resIdemWCongr e.toLinearEquiv
  map_mem' _ _ hx := e.map_mem hx
  symm_map_mem' _ _ hx := e.symm_map_mem' hx

/-- `Res (L ⊕ L') ≅ Res L ⊕ Res L'`. -/
def resGProjProd (L L' : GProj (G.klrGrade (ν' + ν''))) :
    (G.resGProj ν' ν'' hD hZ hS (L.prod L')).Iso
      ((G.resGProj ν' ν'' hD hZ hS L).prod (G.resGProj ν' ν'' hD hZ hS L')) where
  toLinearEquiv := resIdemWProd L.carrier L'.carrier
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

/-- `Res (L{a}) ≅ (Res L){a}`. -/
def resGProjShift (L : GProj (G.klrGrade (ν' + ν''))) (a : ℤ) :
    (G.resGProj ν' ν'' hD hZ hS (L.shift a)).Iso ((G.resGProj ν' ν'' hD hZ hS L).shift a) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

variable (ν' ν'') in
/-- The additive map `K₀(W_{ν'+ν''}) → K₀(W_{ν'} ⊗ W_{ν''})`, `[L] ↦ [Res_{ν';ν''} L]`. -/
def resK0Add :
    K0 (G.klrGrade (ν' + ν'')) →+ K0 (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) :=
  K0.lift (fun L => K0.of (G.resGProj ν' ν'' hD hZ hS L))
    (fun _ _ e => K0.of_eq_of_iso (G.resGProjCongr hD hZ hS e))
    (fun L L' => by rw [K0.of_eq_of_iso (G.resGProjProd hD hZ hS L L'), K0.of_prod])

@[simp] theorem resK0Add_of (L : GProj (G.klrGrade (ν' + ν''))) :
    G.resK0Add ν' ν'' hD hZ hS (K0.of L) = K0.of (G.resGProj ν' ν'' hD hZ hS L) :=
  K0.lift_of _ _ _ L

theorem resK0Add_shift (a : ℤ) (x : K0 (G.klrGrade (ν' + ν''))) :
    G.resK0Add ν' ν'' hD hZ hS (K0.shiftHom a x) =
      K0.shiftHom a (G.resK0Add ν' ν'' hD hZ hS x) := by
  induction x using K0.induction_on with
  | of L =>
    rw [K0.shiftHom_of, resK0Add_of, resK0Add_of, K0.shiftHom_of]
    exact K0.of_eq_of_iso (G.resGProjShift hD hZ hS L a)
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

variable (ν' ν'') in
/-- **The coproduct component of Webster's Theorem 2.19 on graded Grothendieck groups**
(arXiv:1209.2463v4, §2.4): `K₀(W_{ν'+ν''}) → K₀(W_{ν'} ⊗ W_{ν''})`, `[L] ↦ [Res_{ν';ν''} L]`,
`ℤ[q, q⁻¹]`-linear, under the standing hypothesis. -/
def resK0 : K0 (G.klrGrade (ν' + ν'')) →ₗ[LaurentPolynomial ℤ]
    K0 (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) where
  toFun := G.resK0Add ν' ν'' hD hZ hS
  map_add' := map_add _
  map_smul' p x := K0.map_smul_of_shift (G.resK0Add ν' ν'' hD hZ hS)
    (fun a x => G.resK0Add_shift hD hZ hS a x) p x

/-- `[Res] [L] = [e_{ν';ν''} L]`. -/
theorem resK0_of (L : GProj (G.klrGrade (ν' + ν''))) :
    G.resK0 ν' ν'' hD hZ hS (K0.of L) = K0.of (G.resGProj ν' ν'' hD hZ hS L) :=
  G.resK0Add_of hD hZ hS L

end GradingDatum

end Categorification.WeightedKLR

end
