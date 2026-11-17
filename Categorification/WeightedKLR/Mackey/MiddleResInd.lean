/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndFiltration

/-!
# The subquotients of the Mackey filtration of `Res ∘ Ind` as balanced tensor products

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). In the layout
`ν = (a + b) + (c + d)`, `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, the subquotient of
shuffle type `c` of the Mackey filtration of `Res_{ν₁;ν₂} Ind_{ν';ν''}` is the balanced tensor
product
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`, `W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`,
via `x ⊗ y ↦ [ι(x) ψ_c ι(y)]`, as a bimodule.

## Main definitions and results

* `Juxtapose.middleAux`: `x ⊗ y ↦ ι(x) ψ_c ι(y)`, with values in the step `S ∋ c`
  (`middleAux_mem_resIndFilt`).
* `Juxtapose.middleResIndMap`: the descended map from `MiddleTensor` to the subquotient
  `ResIndSubquotient S' S`, for `S' ⊇ {μ < c}`.
* `Juxtapose.resIndCornerProj_comp_middleResIndMap`: its corners are the maps
  `middleTensorMap` of the corners.
* `Juxtapose.middleResIndMap_comp_middleCornerMap`: it is a bimodule map,
  `Φ(z_L t ⊗ y z_R) = ι(z_L) Φ(t ⊗ y) ι(z_R)`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {a b c d : I →₀ ℕ} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)

variable (k) in
/-- The map `x ⊗ y ↦ ι(x) ψ_c ι(y)` of the shuffle type `c`, for the layout `a b c d`. -/
noncomputable def middleAux :
    (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗[k]
        (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) →ₗ[k]
      GalleryAlgebra k Γ (a + b + (c + d)) :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun x y => inductionVal k (layout_eq a b c d) x *
      typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) *
        inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) y)
    (fun x x' y => by rw [map_add, add_mul, add_mul])
    (fun r x y => by rw [map_smul, smul_mul_assoc, smul_mul_assoc])
    (fun x y y' => by rw [map_add, mul_add])
    (fun r x y => by rw [map_smul, mul_smul_comm])

theorem middleAux_tmul (x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleAux k hD hZ (x ⊗ₜ y) = inductionVal k (layout_eq a b c d) x *
      typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) *
        inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) y := rfl

/-- The corners of `middleAux` are the maps `typeInductionAux` of the corners. -/
theorem e_mul_middleAux_mul_e (L R : FullChamber Γ (a + b + (c + d)))
    (z : (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗[k]
        (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))) :
    e L * middleAux k hD hZ z * e R =
      typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) L R
        (middleLeft a b c d) z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [middleAux_tmul, typeInductionAux_tmul]
    simp only [mul_assoc]
  | add z z' h h' => rw [map_add, mul_add, add_mul, h, h', map_add]

/-- `ι(1) middleAux(z) = middleAux(z) = middleAux(z) ι(1)`. -/
theorem inductionVal_one_mul_middleAux
    (z : (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗[k]
        (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))) :
    inductionVal k (layout_eq a b c d) 1 * middleAux k hD hZ z = middleAux k hD hZ z ∧
      middleAux k hD hZ z * inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) 1 =
        middleAux k hD hZ z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [middleAux_tmul]
    constructor
    · rw [← mul_assoc, ← mul_assoc, ← inductionVal_mul, one_mul]
    · rw [mul_assoc, ← inductionVal_mul, mul_one]
  | add z z' h h' => exact ⟨by rw [map_add, mul_add, h.1, h'.1], by rw [map_add, add_mul, h.2, h'.2]⟩

section Descent

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S)

include hS hcS in
/-- **`middleAux` lands in the step `S ∋ c` of the Mackey filtration of `Res ∘ Ind`.** -/
theorem middleAux_mem_resIndFilt
    (z : (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗[k]
        (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))) :
    middleAux k hD hZ z ∈ resIndFilt k hP hD hZ hΓ hW hL
      (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) S :=
  ⟨(inductionVal_one_mul_middleAux hD hZ z).1, (inductionVal_one_mul_middleAux hD hZ z).2,
    fun L R hL' hR => by
      rw [e_mul_middleAux_mul_e]
      exact typeInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL _ _ hR hL' hS hcS
        (Set.mem_range.2 ⟨middleSwap a b c d, shuffleType_middleSwap⟩) z⟩

/-- **Balancedness of `middleAux` up to the shuffle types below `c`.** -/
theorem middleAux_balance_mem (hS' : Set.Iio ⇑c ⊆ S')
    (x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))
    (xa : WeightedKLRAlgebra k Γ a) (xb : WeightedKLRAlgebra k Γ b)
    (xc : WeightedKLRAlgebra k Γ c) (xd : WeightedKLRAlgebra k Γ d) :
    middleAux k hD hZ
        (x ⊗ₜ ((inductionMap k Γ a b (xa ⊗ₜ xb) ⊗ₜ inductionMap k Γ c d (xc ⊗ₜ xd)) * y)) -
      middleAux k hD hZ
        ((x * (inductionMap k Γ a c (xa ⊗ₜ xc) ⊗ₜ inductionMap k Γ b d (xb ⊗ₜ xd))) ⊗ₜ y) ∈
      resIndFilt k hP hD hZ hΓ hW hL
        (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) S' := by
  refine ⟨?_, ?_, fun L R hL' hR => ?_⟩
  · rw [mul_sub, (inductionVal_one_mul_middleAux hD hZ _).1,
      (inductionVal_one_mul_middleAux hD hZ _).1]
  · rw [sub_mul, (inductionVal_one_mul_middleAux hD hZ _).2,
      (inductionVal_one_mul_middleAux hD hZ _).2]
  · rw [mul_sub, sub_mul, e_mul_middleAux_mul_e, e_mul_middleAux_mul_e]
    exact mackeyFilt_mono hP hD hZ hΓ hW hL (a + b) (a + c) L R hS'
      (typeInductionAux_middle_sub_mem_mackeyFilt hP hD hZ hΓ hW hL hL' hR x y xa xb xc xd)

/-- `middleAux` into the step `S`. -/
noncomputable def middleAuxFilt :
    (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗[k]
        (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) →ₗ[k]
      resIndFilt k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S :=
  LinearMap.codRestrict _ (middleAux k hD hZ) (middleAux_mem_resIndFilt hD hZ hP hΓ hW hL hS hcS)

/-- The bilinear map `(t, y) ↦ [ι(t) ψ_c ι(y)]` on the two bimodules. -/
noncomputable def middleResIndBil :
    MiddleTop k Γ a b c d →ₗ[k] MiddleBot k Γ a b c d →ₗ[k]
      ResIndSubquotient k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' S :=
  (((TensorProduct.mk k _ _).compr₂
      (Submodule.mkQ _ ∘ₗ middleAuxFilt hD hZ hP hΓ hW hL hS hcS)).compl₁₂
    ((middleTopSub k Γ a b c d).subtype.restrictScalars k) (middleBotSub k Γ a b c d).subtype)

theorem middleResIndBil_apply (t : MiddleTop k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleResIndBil hD hZ hP hΓ hW hL hS hcS (S' := S') t y =
      Submodule.Quotient.mk (middleAuxFilt hD hZ hP hΓ hW hL hS hcS
        ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗ₜ
          (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)))) := rfl

theorem middleResIndBil_balanced (hS' : Set.Iio ⇑c ⊆ S') (t : MiddleTop k Γ a b c d)
    (r : MiddleAlg k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleResIndBil hD hZ hP hΓ hW hL hS hcS (S' := S') (op r • t) y =
      middleResIndBil hD hZ hP hΓ hW hL hS hcS (S' := S') t (r • y) := by
  rw [middleResIndBil_apply, middleResIndBil_apply, coe_op_smul_middleTop, coe_smul_middleBot,
    unop_op]
  suffices h : ∀ r : MiddleAlg k Γ a b c d,
      middleAux k hD hZ ((t.1 * middleTop k Γ a b c d r) ⊗ₜ y.1) -
        middleAux k hD hZ (t.1 ⊗ₜ (middleBot k Γ a b c d r * y.1)) ∈
      resIndFilt k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' by
    rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub, Submodule.subtype_apply,
      Submodule.subtype_apply]
    exact h r
  intro r
  induction r using TensorProduct.inductionOn with
  | add r r' h h' =>
    have := add_mem h h'
    simp only [map_add, mul_add, add_mul, TensorProduct.tmul_add, TensorProduct.add_tmul] at this ⊢
    convert this using 1
    abel
  | tmul p q =>
    induction p using TensorProduct.inductionOn with
    | add p p' h h' =>
      have := add_mem h h'
      simp only [TensorProduct.add_tmul, map_add, mul_add, add_mul, TensorProduct.tmul_add] at this ⊢
      convert this using 1
      abel
    | tmul xa xb =>
      induction q using TensorProduct.inductionOn with
      | add q q' h h' =>
        have := add_mem h h'
        simp only [TensorProduct.tmul_add, map_add, mul_add, add_mul, TensorProduct.add_tmul]
          at this ⊢
        convert this using 1
        abel
      | tmul xc xd =>
        rw [middleTop_tmul, middleBot_tmul, ← neg_mem_iff, neg_sub]
        exact middleAux_balance_mem hD hZ hP hΓ hW hL hS' t.1 y.1 xa xb xc xd

/-- **The descended map of the middle parabolic into the Mackey subquotient of `Res ∘ Ind`**:
`t ⊗ y ↦ [ι(t) ψ_c ι(y)]` on `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`, into the
subquotient `S / S'` of the Mackey filtration of `Res_{a+c;b+d} Ind_{a+b;c+d}`, for a lower set
`S ∋ c` and `S' ⊇ {μ < c}` (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19). -/
noncomputable def middleResIndMap (hS' : Set.Iio ⇑c ⊆ S') :
    MiddleTensor k Γ a b c d →ₗ[k]
      ResIndSubquotient k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' S :=
  BalancedTensor.lift (middleResIndBil hD hZ hP hΓ hW hL hS hcS)
    (middleResIndBil_balanced hD hZ hP hΓ hW hL hS hcS hS')

theorem middleResIndMap_tmul (hS' : Set.Iio ⇑c ⊆ S') (t : MiddleTop k Γ a b c d)
    (y : MiddleBot k Γ a b c d) :
    middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' (BalancedTensor.tmul t y) =
      Submodule.Quotient.mk (middleAuxFilt hD hZ hP hΓ hW hL hS hcS
        ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗ₜ
          (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)))) := rfl

/-- **The corners of the descended map are the descended maps of the corners**: for rank-ordered
`L`, `R`, projecting to the corner `e L W e R` gives `middleTensorMap`. -/
theorem resIndCornerProj_comp_middleResIndMap (hS' : Set.Iio ⇑c ⊆ S')
    {L R : FullChamber Γ (a + b + (c + d))} (hL' : L.IsRankOrdered) (hR : R.IsRankOrdered) :
    (resIndCornerProj hP hD hZ hΓ hW hL _ _ (S' := S') hL' hR).comp
        (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS') =
      middleTensorMap hP hD hZ hΓ hW hL hR hL' hS hcS hS' := by
  refine BalancedTensor.ext fun t y => ?_
  rw [LinearMap.comp_apply, middleResIndMap_tmul, resIndCornerProj_mk, middleTensorMap_tmul,
    typeInductionMap_apply]
  congr 1
  refine Subtype.ext ?_
  rw [coe_resIndCorner]
  exact e_mul_middleAux_mul_e hD hZ L R _

/-- **The descended map is a bimodule map** (B. Webster, arXiv:1209.2463v4, proof of
Theorem 2.19): `Φ(z_L t ⊗ y z_R) = ι(z_L) Φ(t ⊗ y) ι(z_R)` for `z_L ∈ W_{a+c} ⊗ W_{b+d}`,
`z_R ∈ W_{a+b} ⊗ W_{c+d}`. -/
theorem middleResIndMap_comp_middleCornerMap (hS' : Set.Iio ⇑c ⊆ S')
    (hS'l : IsLowerSet S')
    (zL : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (zR : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS').comp (middleCornerMap zL zR) =
      (resIndSubquotientMul hP hD hZ hΓ hW hL _ _ hS'l hS zL zR).comp
        (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS') := by
  refine BalancedTensor.ext fun t y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, middleCornerMap_tmul, middleResIndMap_tmul,
    middleResIndMap_tmul, resIndSubquotientMul_mk]
  congr 1
  refine Subtype.ext ?_
  show middleAux k hD hZ ((zL * t.1) ⊗ₜ (y.1 * zR)) = _
  rw [coe_resIndFiltMul]
  show _ = inductionVal k (layout_eq a b c d) zL * middleAux k hD hZ (t.1 ⊗ₜ y.1) *
    inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) zR
  rw [middleAux_tmul, middleAux_tmul, inductionVal_mul, inductionVal_mul]
  simp only [mul_assoc]

end Descent

end Juxtapose

end Categorification.WeightedKLR
