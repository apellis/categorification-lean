/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.Grading
import Categorification.WeightedKLR.Induction.Graded
import Categorification.KLR.Induction

/-!
# Graded induction for weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Definition
2.17 (induction along `ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}`) and the graded
Grothendieck groups of Theorem 2.19.

For a grading datum `G`, the map `ι` is graded (`Juxtapose.inductionMap_tmul_mem_grade`), and
`ι(1) = e_{ν';ν''}` has degree `0`. Hence the bimodule `W_{ν'+ν''} e_{ν';ν''}` is graded by
restriction, and the induced module

`Ind (P ⊠ P') = W_{ν'+ν''} e_{ν';ν''} ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ P')`

of graded finitely generated projective modules is graded, finitely generated and projective.
Induction carries no grading shift: this is the product of Webster's Theorem 2.19.

## Main definitions and results

* `GradingDatum.indProj G P P'`: `Ind (P ⊠ P')` as an object of `W_{ν'+ν''}-pmod`.
* `indProjCongr`, `indProjProdLeft`, `indProjProdRight`, `indProjShiftLeft`, `indProjShiftRight`:
  compatibility with isomorphisms, direct sums and grading shifts.
* `GradingDatum.indK0`: the `ℤ[q, q⁻¹]`-bilinear map
  `K₀(W_{ν'}) × K₀(W_{ν''}) → K₀(W_{ν'+ν''})`, `[P] ⊗ [P'] ↦ [Ind (P ⊠ P')]`.

This construction is over `BalancedTensor k`, separate from the ungraded `Juxtapose.ind`, which
is over `BalancedTensor ℤ`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open scoped TensorProduct
open MulOpposite Categorification.Graded GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable (k Γ) (ν' ν'' : I →₀ ℕ)

/-- The algebra `W_{ν'} ⊗ W_{ν''}`. -/
abbrev TensorW : Type _ := WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''

/-- The `(W_{ν'+ν''}, W_{ν'} ⊗ W_{ν''})`-bimodule `W_{ν'+ν''} e_{ν';ν''}`; the right action is
through `ι_{ν';ν''}`. -/
abbrev GradedIndBimod : Type _ := Graded.leftIdeal (inductionMap k Γ ν' ν'' 1)

variable {k Γ ν' ν''}

theorem inductionMap_mul_one (t : TensorW k Γ ν' ν'') :
    inductionMap k Γ ν' ν'' t * inductionMap k Γ ν' ν'' 1 = inductionMap k Γ ν' ν'' t := by
  rw [← map_mul, mul_one]

theorem isIdempotentElem_inductionMap_one :
    IsIdempotentElem (inductionMap k Γ ν' ν'' 1) :=
  inductionMap_mul_one 1

theorem mul_inductionMap_mem (m : GradedIndBimod k Γ ν' ν'') (t : TensorW k Γ ν' ν'') :
    (m : WeightedKLRAlgebra k Γ (ν' + ν'')) * inductionMap k Γ ν' ν'' t ∈
      Graded.leftIdeal (inductionMap k Γ ν' ν'' 1) := by
  rw [Graded.mem_leftIdeal, mul_assoc, inductionMap_mul_one]

instance : SMul (TensorW k Γ ν' ν'')ᵐᵒᵖ (GradedIndBimod k Γ ν' ν'') :=
  ⟨fun t m => ⟨m * inductionMap k Γ ν' ν'' t.unop, mul_inductionMap_mem m _⟩⟩

theorem coe_op_smul (t : (TensorW k Γ ν' ν'')ᵐᵒᵖ) (m : GradedIndBimod k Γ ν' ν'') :
    ((t • m : GradedIndBimod k Γ ν' ν'') : WeightedKLRAlgebra k Γ (ν' + ν'')) =
      m * inductionMap k Γ ν' ν'' t.unop := rfl

instance : Module (TensorW k Γ ν' ν'')ᵐᵒᵖ (GradedIndBimod k Γ ν' ν'') where
  one_smul m := Subtype.ext (by rw [coe_op_smul, unop_one]; exact m.2)
  mul_smul s t m := Subtype.ext (by simp only [coe_op_smul, unop_mul, map_mul, mul_assoc])
  smul_zero t := Subtype.ext (by simp [coe_op_smul])
  smul_add t m m' := Subtype.ext (by simp [coe_op_smul, add_mul])
  add_smul s t m := Subtype.ext (by simp [coe_op_smul, mul_add])
  zero_smul m := Subtype.ext (by simp [coe_op_smul])

instance : IsScalarTower k (TensorW k Γ ν' ν'')ᵐᵒᵖ (GradedIndBimod k Γ ν' ν'') where
  smul_assoc c t m := Subtype.ext (by
    show (m : WeightedKLRAlgebra k Γ (ν' + ν'')) * inductionMap k Γ ν' ν'' (unop (c • t)) =
      c • ((m : WeightedKLRAlgebra k Γ (ν' + ν'')) * inductionMap k Γ ν' ν'' t.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (WeightedKLRAlgebra k Γ (ν' + ν'')) (TensorW k Γ ν' ν'')ᵐᵒᵖ
    (GradedIndBimod k Γ ν' ν'') where
  smul_comm r t m := Subtype.ext (by
    rw [coe_op_smul, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul, smul_eq_mul,
      smul_eq_mul, mul_assoc])

instance : Module.Finite (WeightedKLRAlgebra k Γ (ν' + ν'')) (GradedIndBimod k Γ ν' ν'') :=
  Module.Finite.of_surjective (Graded.leftIdealProj isIdempotentElem_inductionMap_one) fun b =>
    ⟨b, Subtype.ext (Graded.mem_leftIdeal.1 b.2)⟩

instance : Module.Projective (WeightedKLRAlgebra k Γ (ν' + ν'')) (GradedIndBimod k Γ ν' ν'') :=
  Module.Projective.of_split (Graded.leftIdeal _).subtype
    (Graded.leftIdealProj isIdempotentElem_inductionMap_one)
    (Graded.leftIdealProj_comp_subtype isIdempotentElem_inductionMap_one)

variable (k Γ ν' ν'') in
/-- **Graded induction** `W_{ν'+ν''} e_{ν';ν''} ⊗_{W_{ν'} ⊗ W_{ν''}} N` (Webster,
arXiv:1209.2463v4, Definition 2.17), as a balanced tensor product over `k`. -/
abbrev GradedInd (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorW k Γ ν' ν'') N] :
    Type _ :=
  BalancedTensor k (WeightedKLRAlgebra k Γ (ν' + ν'')) (TensorW k Γ ν' ν'')
    (GradedIndBimod k Γ ν' ν'') N

end Juxtapose

open Juxtapose

namespace GradingDatum

variable (G : GradingDatum Γ) {ν' ν'' : I →₀ ℕ}

/-- `ι_{ν';ν''}` is degree-preserving for the tensor product grading of `W_{ν'} ⊗ W_{ν''}`. -/
theorem inductionMap_mem_klrGrade {t : TensorW k Γ ν' ν''} {d : ℤ}
    (ht : t ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') d) :
    inductionMap k Γ ν' ν'' t ∈ G.klrGrade (ν' + ν'') d :=
  tensorGrading_map_mem _ _ _ (LinearMap.ofClass (inductionMap k Γ ν' ν''))
    (fun _ _ _ _ ha hb => Juxtapose.inductionMap_tmul_mem_grade G ha hb) ht

theorem inductionMap_one_mem_klrGrade :
    inductionMap k Γ ν' ν'' 1 ∈ G.klrGrade (ν' + ν'') 0 := by
  show (inductionMap k Γ ν' ν'' 1).1 ∈ G.grade (ν' + ν'') 0
  rw [Algebra.TensorProduct.one_def, ← add_zero (0 : ℤ)]
  exact Juxtapose.inductionMap_tmul_mem_grade G (rankIdem_mem_grade G ν')
    (rankIdem_mem_grade G ν'')

variable (ν' ν'')

/-- The grading of `W_{ν'+ν''} e_{ν';ν''}`. -/
abbrev indBimodGrading : ℤ → Submodule k (GradedIndBimod k Γ ν' ν'') :=
  Graded.submodule (G.klrGrade (ν' + ν'')) (Graded.leftIdeal (inductionMap k Γ ν' ν'' 1))

instance : DirectSum.Decomposition (G.indBimodGrading ν' ν'') :=
  submoduleDecomposition _ (leftIdeal_isHomogeneous G.inductionMap_one_mem_klrGrade)

variable {ν' ν''}

/-- The right action of `W_{ν'} ⊗ W_{ν''}` on `W_{ν'+ν''} e_{ν';ν''}` is graded. -/
theorem op_smul_mem_indBimodGrading {i l : ℤ} {m : GradedIndBimod k Γ ν' ν''}
    {t : TensorW k Γ ν' ν''} (hm : m ∈ G.indBimodGrading ν' ν'' i)
    (ht : t ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') l) :
    op t • m ∈ G.indBimodGrading ν' ν'' (i + l) :=
  SetLike.GradedMul.mul_mem (A := G.klrGrade (ν' + ν'')) hm (G.inductionMap_mem_klrGrade ht)

variable (ν' ν'') in
/-- The grading of an induced module of a graded `W_{ν'} ⊗ W_{ν''}`-module. -/
abbrev gradedIndGrading {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorW k Γ ν' ν'') N] (𝒩 : ℤ → Submodule k N) :
    ℤ → Submodule k (GradedInd k Γ ν' ν'' N) :=
  balancedGrading (WeightedKLRAlgebra k Γ (ν' + ν'')) (TensorW k Γ ν' ν'')
    (G.indBimodGrading ν' ν'') 𝒩

/-- **`Ind (P ⊠ P')`** for finitely generated graded projective modules `P`, `P'` (Webster,
arXiv:1209.2463v4, Definition 2.17): a finitely generated graded projective
`W_{ν'+ν''}`-module, with no grading shift. -/
def indProj (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    GProj (G.klrGrade (ν' + ν'')) :=
  have := ExtTensor.finite (k := k) (A := WeightedKLRAlgebra k Γ ν')
    (B := WeightedKLRAlgebra k Γ ν'') (P := P.carrier) (Q := P'.carrier)
  have := ExtTensor.projective (k := k) (A := WeightedKLRAlgebra k Γ ν')
    (B := WeightedKLRAlgebra k Γ ν'') (P := P.carrier) (Q := P'.carrier)
  { carrier := GradedInd k Γ ν' ν'' (ExtTensor k P.carrier P'.carrier)
    grading := G.gradedIndGrading ν' ν'' (ExtTensor.grading P.grading P'.grading)
    decomposition := balancedDecomposition (tensorGrading (G.klrGrade ν') (G.klrGrade ν''))
      (fun _ _ _ _ hm ht => G.op_smul_mem_indBimodGrading hm ht)
    gradedSMul := gradedSMul_balanced (G.klrGrade (ν' + ν''))
    finite := BalancedTensor.finite
    projective := BalancedTensor.projective }

theorem indProj_carrier (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    (G.indProj P P').carrier = GradedInd k Γ ν' ν'' (ExtTensor k P.carrier P'.carrier) := rfl

/-! ### Functoriality -/

/-- `Ind (P₁ ⊠ P₁') ≅ Ind (P₂ ⊠ P₂')` for `P₁ ≅ P₂`, `P₁' ≅ P₂'`. -/
def indProjCongr {P₁ P₂ : GProj (G.klrGrade ν')} {P₁' P₂' : GProj (G.klrGrade ν'')} (e : P₁.Iso P₂)
    (e' : P₁'.Iso P₂') : (G.indProj P₁ P₁').Iso (G.indProj P₂ P₂') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr e.toLinearEquiv
    e'.toLinearEquiv)) fun _ y hy =>
      mapRight_mem_balancedGrading (B := WeightedKLRAlgebra k Γ (ν' + ν''))
        (ℳ := G.indBimodGrading ν' ν'')
        (ExtTensor.map_preservesGrading e.preservesGrading e'.preservesGrading) (y := y) hy

/-- `Ind ((P₁ ⊕ P₂) ⊠ P') ≅ Ind (P₁ ⊠ P') ⊕ Ind (P₂ ⊠ P')`. -/
def indProjProdLeft (P₁ P₂ : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    (G.indProj (P₁.prod P₂) P').Iso ((G.indProj P₁ P').prod (G.indProj P₂ P')) :=
  let e := (BalancedTensor.congrRight (k := k) (B := WeightedKLRAlgebra k Γ (ν' + ν''))
    (M := GradedIndBimod k Γ ν' ν'') (ExtTensor.prodLeft (k := k)
    (P := P₁.carrier) (P' := P₂.carrier) (Q := P'.carrier) (A := WeightedKLRAlgebra k Γ ν')
    (B := WeightedKLRAlgebra k Γ ν''))).trans
      (BalancedTensor.prodRight _ _ _ _ _ _)
  GradedEquiv.ofPreserves e fun _ y hy =>
    balancedGrading_map_mem (B := WeightedKLRAlgebra k Γ (ν' + ν''))
      (ℳ := G.indBimodGrading ν' ν'')
      (Graded.prod (G.indProj P₁ P').grading (G.indProj P₂ P').grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading
          (𝒰 := Graded.prod P₁.grading P₂.grading)
          (𝒱 := P'.grading) (𝒰' := P₁.grading)
          (f := LinearMap.fst _ P₁.carrier P₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.1) (fun _ _ h => h) hn),
         tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading
          (𝒰 := Graded.prod P₁.grading P₂.grading)
          (𝒱 := P'.grading) (𝒰' := P₂.grading)
          (f := LinearMap.snd _ P₁.carrier P₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.2) (fun _ _ h => h) hn)⟩) (y := y) hy

/-- `Ind (P ⊠ (P₁' ⊕ P₂')) ≅ Ind (P ⊠ P₁') ⊕ Ind (P ⊠ P₂')`. -/
def indProjProdRight (P : GProj (G.klrGrade ν')) (P₁' P₂' : GProj (G.klrGrade ν'')) :
    (G.indProj P (P₁'.prod P₂')).Iso ((G.indProj P P₁').prod (G.indProj P P₂')) :=
  let e := (BalancedTensor.congrRight (k := k) (B := WeightedKLRAlgebra k Γ (ν' + ν''))
    (M := GradedIndBimod k Γ ν' ν'') (ExtTensor.prodRight (k := k)
    (P := P.carrier) (Q := P₁'.carrier) (Q' := P₂'.carrier) (A := WeightedKLRAlgebra k Γ ν')
    (B := WeightedKLRAlgebra k Γ ν''))).trans
      (BalancedTensor.prodRight _ _ _ _ _ _)
  GradedEquiv.ofPreserves e fun _ y hy =>
    balancedGrading_map_mem (B := WeightedKLRAlgebra k Γ (ν' + ν''))
      (ℳ := G.indBimodGrading ν' ν'')
      (Graded.prod (G.indProj P P₁').grading (G.indProj P P₂').grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := P.grading)
          (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₁'.grading)
          (f := LinearMap.id) (g := LinearMap.fst _ P₁'.carrier P₂'.carrier)
          (fun _ _ h => h) (fun _ _ h => h.1) hn),
         tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := P.grading)
          (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₂'.grading)
          (f := LinearMap.id) (g := LinearMap.snd _ P₁'.carrier P₂'.carrier)
          (fun _ _ h => h) (fun _ _ h => h.2) hn)⟩) (y := y) hy

/-- `Ind (P{a} ⊠ P') ≅ Ind (P ⊠ P'){a}`. -/
def indProjShiftLeft (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) (a : ℤ) :
    (G.indProj (P.shift a) P').Iso ((G.indProj P P').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr (P.shiftLinearEquiv a)
      (LinearEquiv.refl _ P'.carrier))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := WeightedKLRAlgebra k Γ (ν' + ν''))
      (ℳ := G.indBimodGrading ν' ν'') (𝒩' := ExtTensor.grading (shift P.grading a) P'.grading)
      (ExtTensor.map_preservesGrading (P.shiftLinearEquiv_preservesGrading a)
        (g := (LinearEquiv.refl (WeightedKLRAlgebra k Γ ν'') P'.carrier).toLinearMap)
        (fun _ _ h => h)) (y := y) hy
    rw [ExtTensor.grading_shift_left, balancedGrading_shift_right] at h
    exact h

/-- `Ind (P ⊠ P'{a}) ≅ Ind (P ⊠ P'){a}`. -/
def indProjShiftRight (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) (a : ℤ) :
    (G.indProj P (P'.shift a)).Iso ((G.indProj P P').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr
      (LinearEquiv.refl _ P.carrier) (P'.shiftLinearEquiv a))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := WeightedKLRAlgebra k Γ (ν' + ν''))
      (ℳ := G.indBimodGrading ν' ν'') (𝒩' := ExtTensor.grading P.grading (shift P'.grading a))
      (ExtTensor.map_preservesGrading
        (f := (LinearEquiv.refl (WeightedKLRAlgebra k Γ ν') P.carrier).toLinearMap) (fun _ _ h => h)
        (P'.shiftLinearEquiv_preservesGrading a)) (y := y) hy
    rw [ExtTensor.grading_shift_right, balancedGrading_shift_right] at h
    exact h

/-! ### The product on Grothendieck groups (Webster, arXiv:1209.2463v4, Theorem 2.19) -/

variable (ν' ν'') in
/-- The biadditive map `K₀(W_{ν'}) × K₀(W_{ν''}) → K₀(W_{ν'+ν''})`,
`([P], [P']) ↦ [Ind_{ν',ν''} (P ⊠ P')]`. -/
def indK0Add : K0 (G.klrGrade ν') →+ K0 (G.klrGrade ν'') →+ K0 (G.klrGrade (ν' + ν'')) :=
  K0.lift₂ (fun P P' => K0.of (G.indProj P P'))
    (fun _ _ _ e => K0.of_eq_of_iso (G.indProjCongr e (GradedEquiv.refl _)))
    (fun _ _ _ e => K0.of_eq_of_iso (G.indProjCongr (GradedEquiv.refl _) e))
    (fun P₁ P₂ P' => by
      rw [K0.of_eq_of_iso (G.indProjProdLeft P₁ P₂ P'), K0.of_prod])
    (fun P P₁ P₂ => by
      rw [K0.of_eq_of_iso (G.indProjProdRight P P₁ P₂), K0.of_prod])

@[simp] theorem indK0Add_of (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    G.indK0Add ν' ν'' (K0.of P) (K0.of P') = K0.of (G.indProj P P') :=
  K0.lift₂_of _ _ _ _ _ P P'

theorem indK0Add_shift_left (a : ℤ) (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    G.indK0Add ν' ν'' (K0.shiftHom a x) y = K0.shiftHom a (G.indK0Add ν' ν'' x y) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      rw [K0.shiftHom_of, indK0Add_of, indK0Add_of, K0.shiftHom_of]
      exact K0.of_eq_of_iso (G.indProjShiftLeft P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

theorem indK0Add_shift_right (a : ℤ) (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    G.indK0Add ν' ν'' x (K0.shiftHom a y) = K0.shiftHom a (G.indK0Add ν' ν'' x y) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      rw [K0.shiftHom_of, indK0Add_of, indK0Add_of, K0.shiftHom_of]
      exact K0.of_eq_of_iso (G.indProjShiftRight P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

variable (ν' ν'') in
/-- **The `ℤ[q, q⁻¹]`-bilinear product `K₀(W_{ν'}) × K₀(W_{ν''}) → K₀(W_{ν'+ν''})`** of
Webster, arXiv:1209.2463v4, Theorem 2.19: `[P] ⊗ [P'] ↦ [Ind (P ⊠ P')]`, with no shift. -/
def indK0 : K0 (G.klrGrade ν') →ₗ[LaurentPolynomial ℤ]
    K0 (G.klrGrade ν'') →ₗ[LaurentPolynomial ℤ] K0 (G.klrGrade (ν' + ν'')) :=
  LinearMap.mk₂ (LaurentPolynomial ℤ) (fun x y => G.indK0Add ν' ν'' x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun p x y => K0.map_smul_of_shift ((G.indK0Add ν' ν'').flip y)
      (fun a x => G.indK0Add_shift_left a x y) p x)
    (fun x y y' => map_add _ y y')
    (fun p x y => K0.map_smul_of_shift (G.indK0Add ν' ν'' x)
      (fun a y => G.indK0Add_shift_right a x y) p y)

@[simp] theorem indK0_apply (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')) :
    G.indK0 ν' ν'' x y = G.indK0Add ν' ν'' x y := rfl

/-- `[P] · [P'] = [Ind_{ν',ν''} (P ⊠ P')]`. -/
theorem indK0_of (P : GProj (G.klrGrade ν')) (P' : GProj (G.klrGrade ν'')) :
    G.indK0 ν' ν'' (K0.of P) (K0.of P') = K0.of (G.indProj P P') :=
  G.indK0Add_of P P'


end GradingDatum

end Categorification.WeightedKLR
