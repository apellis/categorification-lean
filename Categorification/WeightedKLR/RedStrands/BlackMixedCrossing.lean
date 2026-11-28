/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackMixedCorner
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# The crossing of two appended black strands of different colours

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
the KLR action on right `T^λ`-modules by appending black strands (Rouquier's crossing
`τ_{ij}`, as in Khovanov–Lauda I, §2.1).

Fix colours `i ≠ j` and the content `δ = i + (j + ν)`. In `T^λ_δ` the two orders of appending
black strands to `T^λ_ν` are `p ∘ f_j` (first `j`, then `i`; `p = appendBlack i`) and
`r ∘ f_i` (first `i`, then `j`; `r = appendBlackAt j`). The signed terminal crossing
`mixedBlackCrossing` (Lemma 4.35), cut by the two idempotents, is
`mixedCrossElem = p(f_j 1) · χ · r(f_i 1)`. It intertwines the two appending maps
(`mixedCrossElem_intertwines`: `p(f_j a) χ' = χ' r(f_i a)`), which is the balancedness of the
mixed corner map `mixedBlackMap`. Right multiplication by it is the natural transformation

`blackMixedCross : Eⱼ ∘ Eᵢ ⟶ Eᵢ ∘ Eⱼ'`

from restriction along `p ∘ f_j` to restriction along `r ∘ f_i` (`Eⱼ'` is restriction along
`r`, that is, `Eⱼ` on the content `j + (i + ν)` identified with `δ`).

The hypotheses are those of `mixedBlackMap`: symmetric `Q` (`KLRSymm Q`) and `i ≠ j`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i j : I)

set_option hygiene false in
local notation "νi" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νj" => ((Singleton.singleton j : Multiset I) + ν)
set_option hygiene false in
local notation "δ" => ((Singleton.singleton i : Multiset I) + νj)
set_option hygiene false in
local notation "U" => TensorProductAlgebra k Q Λ δ
set_option hygiene false in
local notation "p" => appendBlack (k := k) Q Λ i νj
set_option hygiene false in
local notation "fj" => appendBlack Q Λ j ν
set_option hygiene false in
local notation "fi" => appendBlack Q Λ i ν

omit [DecidableEq I] in
theorem mixedSwap : ({j} : Multiset I) + νi = δ := by ac_rfl

set_option hygiene false in
local notation "r" => appendBlackAt (k := k) (Q := Q) Λ j (mixedSwap ν i j)

/-- The terminal crossing of two black strands of different colours, cut by the idempotents of
the two appending orders: `p(f_j 1) · χ · r(f_i 1)`. -/
def mixedCrossElem : U := p (fj 1) * mixedBlackCrossing (Q := Q) Λ ν i j * r (fi 1)

variable {Λ ν i j}

/-- **The mixed crossing intertwines the two appending maps**: `p(f_j a) χ' = χ' r(f_i a)`. -/
theorem mixedCrossElem_intertwines (hsym : KLRSymm Q) (hij : i ≠ j)
    (a : TensorProductAlgebra k Q Λ ν) :
    p (fj a) * mixedCrossElem Λ ν i j = mixedCrossElem Λ ν i j * r (fi a) := by
  let x₁ : CornerTensor.Left fj := ⟨fj 1, by
    change fj 1 * fj 1 = fj 1
    rw [← map_mul, one_mul]⟩
  let y₁ : CornerTensor.Right fi
      (AlgHom.id k (TensorProductAlgebra k Q Λ νi)) := ⟨fi 1, by
    change fi 1 * fi 1 = fi 1
    rw [← map_mul, one_mul]⟩
  have h := congrArg (mixedBlackMap (Q := Q) Λ ν i j hsym hij)
    (BalancedTensor.op_smul_tmul (k := k) (B := TensorProductAlgebra k Q Λ νj) x₁ a y₁)
  change p (fj 1 * fj a) * mixedBlackCrossing Λ ν i j * r (fi 1) =
    p (fj 1) * mixedBlackCrossing Λ ν i j * r (fi a * fi 1) at h
  rw [← map_mul, one_mul, ← map_mul, mul_one] at h
  unfold mixedCrossElem
  calc p (fj a) * (p (fj 1) * mixedBlackCrossing Λ ν i j * r (fi 1))
      = p (fj a * fj 1) * mixedBlackCrossing Λ ν i j * r (fi 1) := by
        rw [map_mul p]; noncomm_ring
    _ = p (fj 1) * mixedBlackCrossing Λ ν i j * r (fi a) := by rw [← map_mul, mul_one, h]
    _ = p (fj 1) * mixedBlackCrossing Λ ν i j * r (fi 1) * r (fi a) := by
        rw [mul_assoc _ (r (fi 1)), ← map_mul r, ← map_mul, one_mul]

theorem mixedCrossElem_mul_one : mixedCrossElem Λ ν i j * r (fi 1) = mixedCrossElem Λ ν i j := by
  unfold mixedCrossElem
  rw [mul_assoc _ (r (fi 1)), ← map_mul r, ← map_mul, one_mul]

theorem mixedCrossElem_mul_r_one : mixedCrossElem Λ ν i j * r 1 = mixedCrossElem Λ ν i j := by
  unfold mixedCrossElem
  rw [mul_assoc _ (r (fi 1)), ← map_mul r, mul_one]

/-! ### On right modules -/

variable (Λ ν i j)

/-- `appendBlackAt j` on the opposite rings. -/
def appendBlackAtOp :
    (TensorProductAlgebra k Q Λ νi)ᵐᵒᵖ →ₙ+* Uᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom r)

/-- Restriction along `appendBlackAt j`: `Eⱼ` on right modules over `T^λ_δ`, with
`δ = i + (j + ν)` read as `j + (i + ν)`. -/
def blackEAt : ModuleCat.{u} Uᵐᵒᵖ ⥤ ModuleCat.{u} (TensorProductAlgebra k Q Λ νi)ᵐᵒᵖ :=
  resFunctor.{u, u} (appendBlackAtOp Λ ν i j)

variable {Λ ν i j}

/-- The components of the mixed crossing: right multiplication by `mixedCrossElem`. -/
def blackMixedCrossApp (hsym : KLRSymm Q) (hij : i ≠ j) (M : ModuleCat.{u} Uᵐᵒᵖ) :
    ((blackE Q Λ i νj ⋙ blackE Q Λ j ν).obj M) ⟶ ((blackEAt Λ ν i j ⋙ blackE Q Λ i ν).obj M) :=
  ModuleCat.ofHom
    { toFun := fun w => (Res.mk (Res.mk (op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M)) (by
          change op (r 1) • op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M) = _
          rw [smul_smul, ← op_mul, mixedCrossElem_mul_r_one]) :
            Res (appendBlackAtOp Λ ν i j) M) (Res.ext (by
          change op (r (fi 1)) • op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M) = _
          rw [smul_smul, ← op_mul, mixedCrossElem_mul_one]; rfl)) :
            Res (appendBlackOp Q Λ i ν) (Res (appendBlackAtOp Λ ν i j) M))
      map_add' := fun w w' => Res.ext (Res.ext (smul_add _ (w.val.val : M) w'.val.val))
      map_smul' := fun a w => Res.ext (Res.ext (by
        change op (mixedCrossElem (Q := Q) Λ ν i j) • op (p (fj a.unop)) • (w.val.val : M) =
          op (r (fi a.unop)) • op (mixedCrossElem (Q := Q) Λ ν i j) • (w.val.val : M)
        rw [smul_smul, smul_smul, ← op_mul, ← op_mul, mixedCrossElem_intertwines hsym hij])) }

/-- **The crossing `τ` of two appended black strands of different colours** on right
`T^λ`-modules: from `Eⱼ ∘ Eᵢ` (restriction along first `j`, then `i`) to `Eᵢ ∘ Eⱼ'`
(restriction along first `i`, then `j`), by right multiplication by `mixedCrossElem`. -/
def blackMixedCross (hsym : KLRSymm Q) (hij : i ≠ j) :
    blackE Q Λ i νj ⋙ blackE Q Λ j ν ⟶ blackEAt Λ ν i j ⋙ blackE Q Λ i ν where
  app M := blackMixedCrossApp hsym hij M
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext
    (f.hom.map_smul (op (mixedCrossElem (Q := Q) Λ ν i j)) w.val.val).symm))


/-! ### The reverse crossing -/

theorem cast_appendBlackAt {μ β β' : Multiset I} (a : I) (h : β = β')
    (e : ({a} : Multiset I) + μ = β) (x : TensorProductAlgebra k Q Λ μ) :
    castTensorProductAlgebra Q Λ h (appendBlackAt Λ a e x) =
      appendBlackAt Λ a (e.trans h) x := by
  subst h; subst e; rfl

variable (Λ ν i j)

/-- The reverse crossing `r(f_i 1) · χ_{ji} · p(f_j 1)` in `T^λ_δ`: the signed terminal crossing
for the opposite order of colours, transported along `j + (i + ν) = δ`. -/
def mixedCrossRevElem : U :=
  castTensorProductAlgebra Q Λ (mixedSwap ν i j) (mixedCrossElem Λ ν j i)

variable {Λ ν i j}

theorem cast_appendBlack_mixed (a : TensorProductAlgebra k Q Λ νi) :
    castTensorProductAlgebra Q Λ (mixedSwap ν i j) (appendBlack Q Λ j νi a) = r a :=
  cast_appendBlackAt j (mixedSwap ν i j) rfl a

theorem cast_appendBlackAt_mixed (a : TensorProductAlgebra k Q Λ νj) :
    castTensorProductAlgebra Q Λ (mixedSwap ν i j)
      (appendBlackAt (k := k) (Q := Q) Λ i (mixedSwap ν j i) a) = p a :=
  cast_appendBlackAt i (mixedSwap ν i j) (mixedSwap ν j i) a

/-- **The reverse crossing intertwines the two appending maps**: `r(f_i a) χ'' = χ'' p(f_j a)`. -/
theorem mixedCrossRevElem_intertwines (hsym : KLRSymm Q) (hij : i ≠ j)
    (a : TensorProductAlgebra k Q Λ ν) :
    r (fi a) * mixedCrossRevElem Λ ν i j = mixedCrossRevElem Λ ν i j * p (fj a) := by
  have h := congrArg (castTensorProductAlgebra Q Λ (mixedSwap ν i j))
    (mixedCrossElem_intertwines (Q := Q) hsym hij.symm a)
  rwa [map_mul, map_mul, cast_appendBlack_mixed, cast_appendBlackAt_mixed] at h

theorem mixedCrossRevElem_mul_one :
    mixedCrossRevElem Λ ν i j * p (fj 1) = mixedCrossRevElem Λ ν i j := by
  have h := congrArg (castTensorProductAlgebra Q Λ (mixedSwap ν i j))
    (mixedCrossElem_mul_one (Q := Q) (Λ := Λ) (ν := ν) (i := j) (j := i))
  rwa [map_mul, cast_appendBlackAt_mixed] at h

theorem mixedCrossRevElem_mul_p_one :
    mixedCrossRevElem Λ ν i j * p 1 = mixedCrossRevElem Λ ν i j := by
  have h := congrArg (castTensorProductAlgebra Q Λ (mixedSwap ν i j))
    (mixedCrossElem_mul_r_one (Q := Q) (Λ := Λ) (ν := ν) (i := j) (j := i))
  rwa [map_mul, cast_appendBlackAt_mixed] at h

/-- The components of the reverse crossing: right multiplication by `mixedCrossRevElem`. -/
def blackMixedCrossRevApp (hsym : KLRSymm Q) (hij : i ≠ j) (M : ModuleCat.{u} Uᵐᵒᵖ) :
    ((blackEAt Λ ν i j ⋙ blackE Q Λ i ν).obj M) ⟶ ((blackE Q Λ i νj ⋙ blackE Q Λ j ν).obj M) :=
  ModuleCat.ofHom
    { toFun := fun w => (Res.mk (Res.mk (op (mixedCrossRevElem (Q := Q) Λ ν i j) •
          (w.val.val : M)) (by
          change op (p 1) • op (mixedCrossRevElem (Q := Q) Λ ν i j) • (w.val.val : M) = _
          rw [smul_smul, ← op_mul, mixedCrossRevElem_mul_p_one]) :
            Res (appendBlackOp Q Λ i νj) M) (Res.ext (by
          change op (p (fj 1)) • op (mixedCrossRevElem (Q := Q) Λ ν i j) • (w.val.val : M) = _
          rw [smul_smul, ← op_mul, mixedCrossRevElem_mul_one]; rfl)) :
            Res (appendBlackOp Q Λ j ν) (Res (appendBlackOp Q Λ i νj) M))
      map_add' := fun w w' => Res.ext (Res.ext (smul_add _ (w.val.val : M) w'.val.val))
      map_smul' := fun a w => Res.ext (Res.ext (by
        change op (mixedCrossRevElem (Q := Q) Λ ν i j) • op (r (fi a.unop)) • (w.val.val : M) =
          op (p (fj a.unop)) • op (mixedCrossRevElem (Q := Q) Λ ν i j) • (w.val.val : M)
        rw [smul_smul, smul_smul, ← op_mul, ← op_mul, mixedCrossRevElem_intertwines hsym hij])) }

/-- **The reverse crossing** `Eᵢ ∘ Eⱼ' ⟶ Eⱼ ∘ Eᵢ` of two appended black strands of different
colours, by right multiplication by `mixedCrossRevElem`. -/
def blackMixedCrossRev (hsym : KLRSymm Q) (hij : i ≠ j) :
    blackEAt Λ ν i j ⋙ blackE Q Λ i ν ⟶ blackE Q Λ i νj ⋙ blackE Q Λ j ν where
  app M := blackMixedCrossRevApp hsym hij M
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun w => Res.ext (Res.ext
    (f.hom.map_smul (op (mixedCrossRevElem (Q := Q) Λ ν i j)) w.val.val).symm))

end Categorification.Stendhal
