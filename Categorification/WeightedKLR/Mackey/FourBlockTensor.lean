/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockDescent
import Categorification.Algebra.BalancedTensor

/-!
# The balanced tensor product of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18).
For the layouts `a b c d` (of `ν' = a + b`, `ν'' = c + d`) and `a c b d` (of `ν₁ = a + c`,
`ν₂ = b + d`) and the shuffle type `c`, the subquotient of the Mackey filtration is a quotient of
the balanced tensor product

`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`,

`W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)` the algebra of the middle parabolic, acting on the right of
`W_{a+c} ⊗ W_{b+d}` through `ι_{a,c} ⊗ ι_{b,d}` (after exchanging the two middle factors) and on
the left of `W_{a+b} ⊗ W_{c+d}` through `ι_{a,b} ⊗ ι_{c,d}`, with `e'` and `e` the images of the
unit. The map `x ⊗ y ↦ [e D ι(x) ψ_c ι(y) e C]` descends to this balanced tensor product
(`Juxtapose.middleTensorMap`) and is surjective onto the subquotient of the single shuffle type
`c` (`Juxtapose.middleTensorMap_surjective`).

## Main definitions

* `Juxtapose.MiddleAlg`: the algebra `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`.
* `Juxtapose.middleTop`, `Juxtapose.middleBot`: its multiplicative maps into
  `W_{a+c} ⊗ W_{b+d}` and `W_{a+b} ⊗ W_{c+d}`.
* `Juxtapose.MiddleTop`, `Juxtapose.MiddleBot`: the bimodules `(W_{a+c} ⊗ W_{b+d}) e'` and
  `e (W_{a+b} ⊗ W_{c+d})`.
* `Juxtapose.MiddleTensor`: their balanced tensor product over `W'`.
* `Juxtapose.middleTensorMap`: the map into the subquotient of the Mackey filtration.

## Main results

* `Juxtapose.typeInductionAux_middle_unit`: the map of the shuffle type `c` does not see the
  idempotents `e'` and `e`.
* `Juxtapose.middleTensorMap_surjective`: the descended map is onto the subquotient of `c`.

## Implementation notes

Instance search does not find the ring structure of the corner `WeightedKLRAlgebra` inside
nested tensor products such as `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`. The shortcut instances
`GalleryAlgebra.instRingWeightedKLRAlgebra` and `GalleryAlgebra.instAlgebraWeightedKLRAlgebra`,
keyed on `WeightedKLRAlgebra` itself, fix this. The balanced tensor product is formed from the
one-level tensor products `W_{a+c} ⊗ W_{b+d}` and `W_{a+b} ⊗ W_{c+d}`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra MulOpposite

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

/-- The ring structure of `W_ν`, keyed on `WeightedKLRAlgebra` (a shortcut instance: it lets
instance search find it inside nested tensor products). -/
noncomputable instance instRingWeightedKLRAlgebra (ν : I →₀ ℕ) :
    Ring (WeightedKLRAlgebra k Γ ν) :=
  inferInstance

/-- The `k`-algebra structure of `W_ν`, keyed on `WeightedKLRAlgebra` (a shortcut instance). -/
noncomputable instance instAlgebraWeightedKLRAlgebra (ν : I →₀ ℕ) :
    Algebra k (WeightedKLRAlgebra k Γ ν) :=
  inferInstance

end GalleryAlgebra

namespace Juxtapose

/-- A tensor product of multiplicative linear maps is multiplicative. -/
theorem tensorMap_mul {A B C D : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C]
    [Algebra k C] [Ring D] [Algebra k D] (f : A →ₗ[k] C) (g : B →ₗ[k] D)
    (hf : ∀ a a', f (a * a') = f a * f a') (hg : ∀ b b', g (b * b') = g b * g b')
    (x y : A ⊗[k] B) : TensorProduct.map f g (x * y) =
      TensorProduct.map f g x * TensorProduct.map f g y := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, hf, hg]
    | add y y' h1 h2 => rw [mul_add, map_add, h1, h2, map_add, mul_add]
  | add x x' h1 h2 => rw [add_mul, map_add, h1, h2, map_add, add_mul]

variable {a b c d : I →₀ ℕ}

variable (k Γ a b c d) in
/-- The algebra `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)` of the middle parabolic. -/
abbrev MiddleAlg : Type _ :=
  (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ b) ⊗[k]
    (WeightedKLRAlgebra k Γ c ⊗[k] WeightedKLRAlgebra k Γ d)

variable (k Γ) in
/-- Webster's map `ι_{ν';ν''}` as a `k`-linear map. -/
noncomputable def inductionLin (ν' ν'' : I →₀ ℕ) :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₗ[k]
      WeightedKLRAlgebra k Γ (ν' + ν'') where
  toFun := inductionMap k Γ ν' ν''
  map_add' := map_add _
  map_smul' := map_smul _

theorem inductionLin_apply (ν' ν'' : I →₀ ℕ)
    (z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    inductionLin k Γ ν' ν'' z = inductionMap k Γ ν' ν'' z := rfl

variable (k Γ a b c d) in
/-- The map `ι_{a,b} ⊗ ι_{c,d} : W' → W_{a+b} ⊗ W_{c+d}`. -/
noncomputable def middleBot :
    MiddleAlg k Γ a b c d →ₗ[k]
      WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d) :=
  TensorProduct.map (inductionLin k Γ a b) (inductionLin k Γ c d)

variable (k Γ a b c d) in
/-- The map `W' → W_{a+c} ⊗ W_{b+d}`: exchange the two middle factors and apply
`ι_{a,c} ⊗ ι_{b,d}`. -/
noncomputable def middleTop :
    MiddleAlg k Γ a b c d →ₗ[k]
      WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d) :=
  TensorProduct.map (inductionLin k Γ a c) (inductionLin k Γ b d) ∘ₗ
    (Algebra.TensorProduct.tensorTensorTensorComm k k k k (WeightedKLRAlgebra k Γ a)
      (WeightedKLRAlgebra k Γ b) (WeightedKLRAlgebra k Γ c)
      (WeightedKLRAlgebra k Γ d)).toLinearMap

theorem middleBot_tmul (xa : WeightedKLRAlgebra k Γ a) (xb : WeightedKLRAlgebra k Γ b)
    (xc : WeightedKLRAlgebra k Γ c) (xd : WeightedKLRAlgebra k Γ d) :
    middleBot k Γ a b c d ((xa ⊗ₜ xb) ⊗ₜ (xc ⊗ₜ xd)) =
      inductionMap k Γ a b (xa ⊗ₜ xb) ⊗ₜ inductionMap k Γ c d (xc ⊗ₜ xd) := rfl

theorem middleTop_tmul (xa : WeightedKLRAlgebra k Γ a) (xb : WeightedKLRAlgebra k Γ b)
    (xc : WeightedKLRAlgebra k Γ c) (xd : WeightedKLRAlgebra k Γ d) :
    middleTop k Γ a b c d ((xa ⊗ₜ xb) ⊗ₜ (xc ⊗ₜ xd)) =
      inductionMap k Γ a c (xa ⊗ₜ xc) ⊗ₜ inductionMap k Γ b d (xb ⊗ₜ xd) := rfl

theorem middleBot_one :
    middleBot k Γ a b c d 1 = inductionMap k Γ a b 1 ⊗ₜ inductionMap k Γ c d 1 := by
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def,
    Algebra.TensorProduct.one_def]
  rfl

theorem middleTop_one :
    middleTop k Γ a b c d 1 = inductionMap k Γ a c 1 ⊗ₜ inductionMap k Γ b d 1 := by
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def,
    Algebra.TensorProduct.one_def, middleTop_tmul, ← Algebra.TensorProduct.one_def,
    ← Algebra.TensorProduct.one_def]

theorem middleBot_mul (r s : MiddleAlg k Γ a b c d) :
    middleBot k Γ a b c d (r * s) = middleBot k Γ a b c d r * middleBot k Γ a b c d s :=
  tensorMap_mul _ _ (fun x y => map_mul (inductionMap k Γ a b) x y)
    (fun x y => map_mul (inductionMap k Γ c d) x y) r s

theorem middleTop_mul (r s : MiddleAlg k Γ a b c d) :
    middleTop k Γ a b c d (r * s) = middleTop k Γ a b c d r * middleTop k Γ a b c d s := by
  simp only [middleTop, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul]
  exact tensorMap_mul _ _ (fun x y => map_mul (inductionMap k Γ a c) x y)
    (fun x y => map_mul (inductionMap k Γ b d) x y) _ _

/-! ### The bimodules -/

variable (k Γ a b c d) in
/-- The left ideal `(W_{a+c} ⊗ W_{b+d}) e'`, `e'` the image of the unit of `W'`. -/
def middleTopSub :
    Submodule (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) where
  carrier := {x | x * middleTop k Γ a b c d 1 = x}
  add_mem' {x y} hx hy := by simp_all [add_mul]
  zero_mem' := zero_mul _
  smul_mem' r x hx := by simp_all [smul_eq_mul, mul_assoc]

variable (k Γ a b c d) in
/-- The `(W_{a+c} ⊗ W_{b+d}, W')`-bimodule `(W_{a+c} ⊗ W_{b+d}) e'`. -/
abbrev MiddleTop : Type _ := middleTopSub k Γ a b c d

theorem mem_middleTopSub {x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)} :
    x ∈ middleTopSub k Γ a b c d ↔ x * middleTop k Γ a b c d 1 = x := Iff.rfl

theorem mul_middleTop_mem (x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (r : MiddleAlg k Γ a b c d) : x * middleTop k Γ a b c d r ∈ middleTopSub k Γ a b c d := by
  rw [mem_middleTopSub, mul_assoc, ← middleTop_mul, mul_one]

noncomputable instance : SMul (MiddleAlg k Γ a b c d)ᵐᵒᵖ (MiddleTop k Γ a b c d) :=
  ⟨fun r t => ⟨t * middleTop k Γ a b c d r.unop, mul_middleTop_mem _ _⟩⟩

theorem coe_op_smul_middleTop (r : (MiddleAlg k Γ a b c d)ᵐᵒᵖ) (t : MiddleTop k Γ a b c d) :
    ((r • t : MiddleTop k Γ a b c d) :
        WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) =
      t * middleTop k Γ a b c d r.unop := rfl

noncomputable instance : Module (MiddleAlg k Γ a b c d)ᵐᵒᵖ (MiddleTop k Γ a b c d) where
  one_smul t := Subtype.ext (by rw [coe_op_smul_middleTop, unop_one]; exact t.2)
  mul_smul r s t := Subtype.ext (by
    simp only [coe_op_smul_middleTop, unop_mul, middleTop_mul, mul_assoc])
  smul_zero r := Subtype.ext (by simp [coe_op_smul_middleTop])
  smul_add r t t' := Subtype.ext (by simp [coe_op_smul_middleTop, add_mul])
  add_smul r s t := Subtype.ext (by simp [coe_op_smul_middleTop, mul_add])
  zero_smul t := Subtype.ext (by simp [coe_op_smul_middleTop])

instance : IsScalarTower k (MiddleAlg k Γ a b c d)ᵐᵒᵖ (MiddleTop k Γ a b c d) where
  smul_assoc r s t := Subtype.ext (by
    show (t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) *
        middleTop k Γ a b c d (unop (r • s)) =
      r • ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) *
        middleTop k Γ a b c d s.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (MiddleAlg k Γ a b c d)ᵐᵒᵖ (MiddleTop k Γ a b c d) where
  smul_comm x r t := Subtype.ext (by
    rw [coe_op_smul_middleTop, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul_middleTop,
      smul_eq_mul, smul_eq_mul, mul_assoc])

variable (k Γ a b c d) in
/-- The `k`-submodule `e (W_{a+b} ⊗ W_{c+d})`, `e` the image of the unit of `W'`. -/
def middleBotSub :
    Submodule k (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) where
  carrier := {y | middleBot k Γ a b c d 1 * y = y}
  add_mem' {x y} hx hy := by simp_all [mul_add]
  zero_mem' := mul_zero _
  smul_mem' r x hx := by simp_all

variable (k Γ a b c d) in
/-- The left `W'`-module `e (W_{a+b} ⊗ W_{c+d})`. -/
abbrev MiddleBot : Type _ := middleBotSub k Γ a b c d

theorem mem_middleBotSub {y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)} :
    y ∈ middleBotSub k Γ a b c d ↔ middleBot k Γ a b c d 1 * y = y := Iff.rfl

theorem middleBot_mul_mem (r : MiddleAlg k Γ a b c d)
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleBot k Γ a b c d r * y ∈ middleBotSub k Γ a b c d := by
  rw [mem_middleBotSub, ← mul_assoc, ← middleBot_mul, one_mul]

noncomputable instance : SMul (MiddleAlg k Γ a b c d) (MiddleBot k Γ a b c d) :=
  ⟨fun r y => ⟨middleBot k Γ a b c d r * y, middleBot_mul_mem _ _⟩⟩

theorem coe_smul_middleBot (r : MiddleAlg k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    ((r • y : MiddleBot k Γ a b c d) :
        WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) =
      middleBot k Γ a b c d r * y := rfl

noncomputable instance : Module (MiddleAlg k Γ a b c d) (MiddleBot k Γ a b c d) where
  one_smul y := Subtype.ext (by rw [coe_smul_middleBot]; exact y.2)
  mul_smul r s y := Subtype.ext (by simp only [coe_smul_middleBot, middleBot_mul, mul_assoc])
  smul_zero r := Subtype.ext (by simp [coe_smul_middleBot])
  smul_add r y y' := Subtype.ext (by simp [coe_smul_middleBot, mul_add])
  add_smul r s y := Subtype.ext (by simp [coe_smul_middleBot, add_mul])
  zero_smul y := Subtype.ext (by simp [coe_smul_middleBot])

variable (k Γ a b c d) in
/-- **The balanced tensor product of the middle parabolic**:
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`, `W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`, a left
`W_{a+c} ⊗ W_{b+d}`-module (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
abbrev MiddleTensor : Type _ :=
  BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (MiddleBot k Γ a b c d)

/-! ### The unit idempotents -/

theorem inductionVal_middleBot_one :
    inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) (middleBot k Γ a b c d 1) =
      ∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q) := by
  rw [middleBot_one, inductionVal_apply, castGallery_rfl, inductionMap_tmul, inductionMap_one,
    inductionMap_one, galleryTensorHom_splitIdem_splitIdem]

theorem inductionVal_middleTop_one :
    inductionVal k (layout_eq a b c d) (middleTop k Γ a b c d 1) =
      ∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q) := by
  rw [middleTop_one, inductionVal_apply, inductionMap_tmul, inductionMap_one, inductionMap_one,
    castGallery_galleryTensorHom_splitIdem_splitIdem]

theorem typeShuffle_mul_sum_e_fourChamber (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) *
        ∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q) =
      typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) := by
  rw [Finset.mul_sum, Finset.sum_congr rfl fun q hq =>
    typeShuffle_mul_e_fourChamber hD hZ (isRankOrdered_of_mem_rankQuads hq),
    ← typeShuffle_middleLeft]

theorem sum_e_fourChamberSwap_mul_typeShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    (∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q)) *
        typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) =
      typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) := by
  rw [Finset.sum_mul, Finset.sum_congr rfl fun q hq =>
    e_fourChamberSwap_mul_typeShuffle hD hZ (isRankOrdered_of_mem_rankQuads hq),
    ← typeShuffle_middleLeft]

/-- **The map of the shuffle type `c` does not see the parabolic idempotents**:
`e L ι(x e') ψ_c ι(e y) e R = e L ι(x) ψ_c ι(y) e R`, `e'` and `e` the images of the unit of
`W_a ⊗ W_b ⊗ W_c ⊗ W_d` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem typeInductionAux_middle_unit (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (L R : FullChamber Γ (a + b + (c + d)))
    (x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) L R
        (middleLeft a b c d) ((x * middleTop k Γ a b c d 1) ⊗ₜ (middleBot k Γ a b c d 1 * y)) =
      typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) L R
        (middleLeft a b c d) (x ⊗ₜ y) := by
  have h : ∀ p q r s t u v : GalleryAlgebra k Γ (a + b + (c + d)),
      p * (q * r) * s * (t * u) * v = p * q * (r * s * t) * u * v := fun _ _ _ _ _ _ _ => by
    simp only [mul_assoc]
  rw [typeInductionAux_tmul, typeInductionAux_tmul, inductionVal_mul, inductionVal_mul,
    inductionVal_middleTop_one, inductionVal_middleBot_one, h, mul_assoc _ _
      (∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q)),
    typeShuffle_mul_sum_e_fourChamber, sum_e_fourChamberSwap_mul_typeShuffle]

/-! ### The descended map -/

section Descent

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  {L R : FullChamber Γ (a + b + (c + d))} (hR : R.IsRankOrdered) (hL' : L.IsRankOrdered)
  {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S)

/-- The bilinear map `(x, y) ↦ [e L ι(x) ψ_c ι(y) e R]` on the two bimodules. -/
noncomputable def middleBil :
    MiddleTop k Γ a b c d →ₗ[k] MiddleBot k Γ a b c d →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL (a + b) (a + c) L R S' S :=
  (((TensorProduct.mk k _ _).compr₂
      (typeInductionMap k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) hR hL' S' hS hcS
        (Set.mem_range.2 ⟨middleSwap a b c d, shuffleType_middleSwap⟩))).compl₁₂
    ((middleTopSub k Γ a b c d).subtype.restrictScalars k) (middleBotSub k Γ a b c d).subtype)

theorem middleBil_apply (t : MiddleTop k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleBil hP hD hZ hΓ hW hL hR hL' hS hcS (S' := S') t y =
      typeInductionMap k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) hR hL' S' hS hcS
        (Set.mem_range.2 ⟨middleSwap a b c d, shuffleType_middleSwap⟩)
        ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗ₜ
          (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))) := rfl

theorem middleBil_balanced (hS' : Set.Iio ⇑c ⊆ S') (t : MiddleTop k Γ a b c d)
    (r : MiddleAlg k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleBil hP hD hZ hΓ hW hL hR hL' hS hcS (S' := S') (op r • t) y =
      middleBil hP hD hZ hΓ hW hL hR hL' hS hcS (S' := S') t (r • y) := by
  rw [middleBil_apply, middleBil_apply, coe_op_smul_middleTop, coe_smul_middleBot, unop_op]
  induction r using TensorProduct.inductionOn with
  | add r r' h h' => simp only [map_add, mul_add, add_mul, TensorProduct.tmul_add,
      TensorProduct.add_tmul, h, h']
  | tmul p q =>
    induction p using TensorProduct.inductionOn with
    | add p p' h h' => simp only [TensorProduct.add_tmul, map_add, mul_add, add_mul,
        TensorProduct.tmul_add, h, h']
    | tmul xa xb =>
      induction q using TensorProduct.inductionOn with
      | add q q' h h' => simp only [TensorProduct.tmul_add, map_add, mul_add, add_mul,
          TensorProduct.add_tmul, h, h']
      | tmul xc xd =>
        rw [middleTop_tmul, middleBot_tmul]
        exact (typeInductionMap_middle_balance hP hD hZ hΓ hW hL hR hL' hS hcS hS' _ _ xa xb
          xc xd).symm

/-- **The descended map of the middle parabolic**: `x ⊗ y ↦ [e L ι(x) ψ_c ι(y) e R]` on the
balanced tensor product `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`, into the
subquotient of the Mackey filtration whose lower step contains the shuffle types below `c`
(Webster, arXiv:1209.2463v4, Theorem 2.19). -/
noncomputable def middleTensorMap (hS' : Set.Iio ⇑c ⊆ S') :
    MiddleTensor k Γ a b c d →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL (a + b) (a + c) L R S' S :=
  BalancedTensor.lift (middleBil hP hD hZ hΓ hW hL hR hL' hS hcS)
    (middleBil_balanced hP hD hZ hΓ hW hL hR hL' hS hcS hS')

theorem middleTensorMap_tmul (hS' : Set.Iio ⇑c ⊆ S') (t : MiddleTop k Γ a b c d)
    (y : MiddleBot k Γ a b c d) :
    middleTensorMap hP hD hZ hΓ hW hL hR hL' hS hcS hS' (BalancedTensor.tmul t y) =
      typeInductionMap k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) hR hL' S' hS hcS
        (Set.mem_range.2 ⟨middleSwap a b c d, shuffleType_middleSwap⟩)
        ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) ⊗ₜ
          (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))) := rfl

/-- **The descended map is onto the subquotient of the shuffle type `c`** (the surjectivity half
of the identification of the subquotients of the Mackey filtration in B. Webster,
arXiv:1209.2463v4, Theorem 2.19, for the layouts `a b c d`, `a c b d`). Let `R` be separated by
the strands of `a + b` and `L` by those of `a + c`, and let `c` be the only shuffle type in `S`
but not in `S'`, with all types below `c` in `S'`. Then the map
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d}) → S / S'` is surjective. -/
theorem middleTensorMap_surjective (hS' : Set.Iio ⇑c ⊆ S')
    (hRs : IsSeparated (fun t => decide (t.IsLeft (a + b))) R)
    (hLs : IsSeparated (fun t => decide (t.IsLeft (a + c))) L)
    (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c) :
    Function.Surjective (middleTensorMap hP hD hZ hΓ hW hL hR hL' hS hcS hS') := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← range_typeInductionMap_eq_top hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
      (layout_eq a b c d) hR hL' hRs hLs S' hS hcS
      (Set.mem_range.2 ⟨middleSwap a b c d, shuffleType_middleSwap⟩) hc]
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | add z z' h h' => rw [map_add]; exact add_mem h h'
  | tmul x y =>
    refine ⟨BalancedTensor.tmul ⟨x * middleTop k Γ a b c d 1, mul_middleTop_mem _ _⟩
      ⟨middleBot k Γ a b c d 1 * y, middleBot_mul_mem _ _⟩, ?_⟩
    rw [middleTensorMap_tmul, typeInductionMap_apply, typeInductionMap_apply]
    congr 2
    exact typeInductionAux_middle_unit hD hZ L R x y

end Descent

end Juxtapose

end Categorification.WeightedKLR
