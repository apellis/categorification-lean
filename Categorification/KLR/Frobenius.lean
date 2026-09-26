/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ResK0
import Categorification.KLR.InductionAlgebra

/-!
# Frobenius reciprocity for `Ind_{ν,ν'}` and `Res_{ν,ν'}`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6 and the proof of Proposition 3.3 (TeX lines
1990–2003). Induction `Ind_{ν,ν'} N = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} N` is left adjoint to
restriction `Res_{ν,ν'} X = 1_{ν,ν'} X`:

`HOM_{R(ν+ν')}(Ind N, X) ≅ HOM_{R(ν) ⊗ R(ν')}(N, Res X)`, `f ↦ (n ↦ f(1_{ν,ν'} ⊗ n))`,

with inverse `g ↦ (r ⊗ n ↦ r g(n))`. The isomorphism preserves the degree of maps, so it gives
isomorphisms of the graded pieces `HOM(-, -)_d` and hence equal graded dimensions.

## Main results

* `KLRAlgebra.frobeniusEquiv` : the (ungraded) adjunction isomorphism, `k`-linear.
* `GradingDatum.homGradeFrobenius` : `HOM(Ind N, X)_d ≅ HOM(N, Res X)_d` for graded `N`, `X`.
* `GradingDatum.homGdim_indProj` : `gdim HOM(Ind (Y ⊠ Y'), X) = gdim HOM(Y ⊠ Y', Res X)`.
* `GradingDatum.homForm_indK0` : **KL I, Proposition 3.3 (4)** for the form
  `([P], [Q]) = gdim HOM(P, Q)`:
  `(x x', y) = (x ⊗ x', [Res] y)` for all `x ∈ K₀(R(ν))`, `x' ∈ K₀(R(ν'))`,
  `y ∈ K₀(R(ν + ν'))`, where `x x' = [Ind](x ⊗ x')` and `x ⊗ x' = K0.extTensor x x'`.

## Relation to the paper's form

KL I's pairing is `([P], [Q]) = gdim (P^ψ ⊗_{R(ν)} Q)` (bilinear, `eq_bil_pair2`); the repository's
form is `K0.homForm`, `([P], [Q]) = gdim HOM(P, Q)`, which is sesquilinear
(`(q^a x, y) = q^{-a} (x, y)`) and equals the paper's form evaluated at `(x̄, y)`. On the
self-dual modules `P_i` the two forms agree. Part (4) of Proposition 3.3 (the adjunction
`Ind ⊣ Res`) holds for `homForm` exactly as stated, for all `x`, `x'`, `y` (not only for classes
of self-dual modules): this is `homForm_indK0`. Part (3), `(x, y y') = ([Res] x, y ⊗ y')`, is the
statement with induction in the *second* slot; for `homForm` it is not a formal consequence of
the adjunction (it uses the symmetry of the paper's form, i.e. the bar involution), and it is not
formalized here.
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra MulOpposite MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' : Multiset I}

namespace KLRAlgebra

section Adjunction

variable {Nt : Type*} [AddCommGroup Nt] [Module k Nt] [Module (TensorKLR Q ν ν') Nt]
  [IsScalarTower k (TensorKLR Q ν ν') Nt]
  {X : Type*} [AddCommGroup X] [Module k X] [Module (KLRAlgebra k Q (ν + ν')) X]
  [IsScalarTower k (KLRAlgebra k Q (ν + ν')) X]

theorem oneConcat_smul_oneBimod :
    (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) • oneBimod Q ν ν' = oneBimod Q ν ν' :=
  Subtype.ext (oneConcat_idem (Q := Q) (ν := ν) (ν' := ν')).eq

/-- The adjunction map `f ↦ (n ↦ f(1_{ν,ν'} ⊗ n))`. -/
def frobFwd (f : Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X) :
    Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X where
  toFun n := ⟨f (BalancedTensor.tmul (oneBimod Q ν ν') n), by
    rw [mem_idemSubspace, ← map_smul, BalancedTensor.smul_tmul', oneConcat_smul_oneBimod]⟩
  map_add' n n' := Subtype.ext (by
    simp only [BalancedTensor.tmul_add, map_add, Submodule.coe_add])
  map_smul' t n := Subtype.ext (by
    show f (BalancedTensor.tmul (oneBimod Q ν ν') (t • n)) =
      concat Q ν ν' t • f (BalancedTensor.tmul (oneBimod Q ν ν') n)
    rw [← BalancedTensor.op_smul_tmul, ← concat_smul_oneBimod, ← BalancedTensor.smul_tmul',
      map_smul])

omit [IsScalarTower k (TensorKLR Q ν ν') Nt] in
theorem coe_frobFwd_apply (f : Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X) (n : Nt) :
    ((frobFwd f n : ResIdem Q ν ν' X) : X) = f (BalancedTensor.tmul (oneBimod Q ν ν') n) := rfl

/-- The bilinear map `(r, n) ↦ r g(n)`. -/
def frobBil (g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X) :
    IndBimod Q ν ν' →ₗ[k] Nt →ₗ[k] X :=
  LinearMap.mk₂ k (fun r n => (r : KLRAlgebra k Q (ν + ν')) • ((g n : ResIdem Q ν ν' X) : X))
    (fun r r' n => by simp only [Submodule.coe_add, add_smul])
    (fun c r n => by
      show ((c • r : IndBimod Q ν ν') : KLRAlgebra k Q (ν + ν')) • _ = c • _
      rw [Submodule.coe_smul_of_tower, smul_assoc])
    (fun r n n' => by simp only [map_add, Submodule.coe_add, smul_add])
    (fun c r n => by
      show (r : KLRAlgebra k Q (ν + ν')) • ((g (c • n) : ResIdem Q ν ν' X) : X) =
        c • ((r : KLRAlgebra k Q (ν + ν')) • ((g n : ResIdem Q ν ν' X) : X))
      rw [LinearMap.map_smul_of_tower, Submodule.coe_smul, smul_comm])

@[simp] theorem frobBil_apply (g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X)
    (r : IndBimod Q ν ν') (n : Nt) :
    frobBil g r n = (r : KLRAlgebra k Q (ν + ν')) • ((g n : ResIdem Q ν ν' X) : X) := rfl

/-- The inverse adjunction map `g ↦ (r ⊗ n ↦ r g(n))`. -/
def frobBwd (g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X) :
    Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X :=
  BalancedTensor.liftB (frobBil g)
    (fun r t n => by
      rw [frobBil_apply, frobBil_apply, coe_op_smul, map_smul, coe_resIdem_smul, mul_smul,
        unop_op])
    (fun b r n => by
      rw [frobBil_apply, frobBil_apply, Submodule.coe_smul, smul_eq_mul, mul_smul])

@[simp] theorem frobBwd_tmul (g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X)
    (r : IndBimod Q ν ν') (n : Nt) :
    frobBwd g (BalancedTensor.tmul r n) =
      (r : KLRAlgebra k Q (ν + ν')) • ((g n : ResIdem Q ν ν' X) : X) := rfl

theorem frobBwd_frobFwd (f : Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X) :
    frobBwd (frobFwd f) = f :=
  BalancedTensor.extB fun r n => by
    rw [frobBwd_tmul, coe_frobFwd_apply, ← map_smul, BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext (mem_leftIdeal.1 r.2)

theorem frobFwd_frobBwd (g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X) :
    frobFwd (frobBwd g) = g :=
  LinearMap.ext fun n => Subtype.ext (by
    rw [coe_frobFwd_apply, frobBwd_tmul, coe_oneBimod]
    exact (g n).2)

variable (Nt X) in
/-- **Frobenius reciprocity** (ungraded): `Hom_{R(ν+ν')}(Ind N, X) ≅ Hom_{R(ν) ⊗ R(ν')}(N, Res X)`
as `k`-vector spaces. -/
def frobeniusEquiv :
    (Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X) ≃ₗ[k]
      (Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X) where
  toFun := frobFwd
  invFun := frobBwd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := frobBwd_frobFwd
  right_inv := frobFwd_frobBwd

end Adjunction

end KLRAlgebra

namespace GradingDatum

variable (G : GradingDatum Q)

section Graded

variable {Nt : Type*} [AddCommGroup Nt] [Module k Nt] [Module (TensorKLR Q ν ν') Nt]
  [IsScalarTower k (TensorKLR Q ν ν') Nt]
  {X : Type*} [AddCommGroup X] [Module k X] [Module (KLRAlgebra k Q (ν + ν')) X]
  [IsScalarTower k (KLRAlgebra k Q (ν + ν')) X]
  {𝒩 : ℤ → Submodule k Nt} {𝒳 : ℤ → Submodule k X}
  [SetLike.GradedSMul (G.grade (ν + ν')) 𝒳]

omit [SetLike.GradedSMul (G.grade (ν + ν')) 𝒳] [IsScalarTower k (TensorKLR Q ν ν') Nt] in
theorem frobFwd_mem {d : ℤ} {f : Ind Q ν ν' Nt →ₗ[KLRAlgebra k Q (ν + ν')] X}
    (hf : f ∈ homGrade (KLRAlgebra k Q (ν + ν')) (G.indGrading ν ν' 𝒩) 𝒳 d) :
    frobFwd f ∈ homGrade (TensorKLR Q ν ν') 𝒩 (idem 𝒳 (oneConcat Q ν ν')) d := by
  intro e n hn
  have h := tmul_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (A := TensorKLR Q ν ν')
    (ℳ := G.bimodGrading ν ν') (𝒩 := 𝒩)
    (show oneBimod Q ν ν' ∈ G.bimodGrading ν ν' 0 from G.oneConcat_mem_grade) hn
  have := hf h
  rw [zero_add] at this
  exact (mem_idem 𝒳).2 this

theorem frobBwd_mem {d : ℤ} {g : Nt →ₗ[TensorKLR Q ν ν'] ResIdem Q ν ν' X}
    (hg : g ∈ homGrade (TensorKLR Q ν ν') 𝒩 (idem 𝒳 (oneConcat Q ν ν')) d) :
    frobBwd g ∈ homGrade (KLRAlgebra k Q (ν + ν')) (G.indGrading ν ν' 𝒩) 𝒳 d := by
  intro e y hy
  refine balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
    (𝒩 := 𝒩) (fun j => 𝒳 (j + d)) ((frobBwd g).restrictScalars k) ?_ hy
  intro i j r n hr hn
  have h1 : ((g n : ResIdem Q ν ν' X) : X) ∈ 𝒳 (j + d) := (mem_idem 𝒳).1 (hg hn)
  have h2 := SetLike.GradedSMul.smul_mem (A := G.grade (ν + ν')) (B := 𝒳) hr h1
  rw [vadd_eq_add, ← add_assoc] at h2
  exact h2

variable (𝒩 𝒳) in
/-- **Frobenius reciprocity, graded**: `HOM(Ind N, X)_d ≅ HOM(N, Res X)_d`, where
`Res X = 1_{ν,ν'} X` is graded by `(1_{ν,ν'} X)_d = 1_{ν,ν'} X ∩ X_d`. -/
def homGradeFrobenius (d : ℤ) :
    homGrade (KLRAlgebra k Q (ν + ν')) (G.indGrading ν ν' 𝒩) 𝒳 d ≃ₗ[k]
      homGrade (TensorKLR Q ν ν') 𝒩 (idem 𝒳 (oneConcat Q ν ν')) d where
  toFun f := ⟨frobFwd f.1, G.frobFwd_mem f.2⟩
  invFun g := ⟨frobBwd g.1, G.frobBwd_mem g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (frobBwd_frobFwd f.1)
  right_inv g := Subtype.ext (frobFwd_frobBwd g.1)

end Graded

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- `gdim HOM(Ind (Y ⊠ Y'), X) = gdim HOM(Y ⊠ Y', Res X)`. -/
theorem homGdim_indProj (Y : GProj (G.grade ν)) (Y' : GProj (G.grade ν'))
    (X : GProj (G.grade (ν + ν'))) :
    GProj.homGdim (G.indProj Y Y') X =
      GProj.homGdim (Y.extTensor Y') (G.resGProj ν ν' hPQ hP X) :=
  gdim_eq_of_finrank_eq fun d =>
    (G.homGradeFrobenius (ExtTensor.grading Y.grading Y'.grading) X.grading d).finrank_eq

/-- **KL I, Proposition 3.3 (4)**: `(x x', y) = (x ⊗ x', [Res] y)` for the form
`([P], [Q]) = gdim HOM(P, Q)`, for all `x ∈ K₀(R(ν))`, `x' ∈ K₀(R(ν'))`,
`y ∈ K₀(R(ν + ν'))`; here `x x' = [Ind_{ν,ν'}](x ⊗ x')` and `x ⊗ x' = [Y ⊠ Y']` on classes. -/
theorem homForm_indK0 [HasGdim (G.grade ν)] [HasGdim (G.grade ν')]
    [HasGdim (G.grade (ν + ν'))] (x : K0 (G.grade ν)) (x' : K0 (G.grade ν'))
    (y : K0 (G.grade (ν + ν'))) :
    K0.homForm (G.grade (ν + ν')) (G.indK0 ν ν' x x') y =
      K0.homForm (tensorGrading (G.grade ν) (G.grade ν'))
        (K0.extTensor (G.grade ν) (G.grade ν') x x') (G.resK0 ν ν' hPQ hP y) := by
  induction y using K0.induction_on with
  | of X =>
    induction x using K0.induction_on with
    | of Y =>
      induction x' using K0.induction_on with
      | of Y' =>
        rw [indK0_of, K0.extTensor_of, resK0_of, K0.homForm_of, K0.homForm_of,
          G.homGdim_indProj hPQ hP]
      | zero => simp
      | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
      | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]
    | zero => simp
    | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply, hx, hx']
    | neg x hx => simp only [map_neg, LinearMap.neg_apply, AddMonoidHom.neg_apply, hx]
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | neg y hy => simp only [map_neg, hy]

end GradingDatum

end Categorification.KLR

end
