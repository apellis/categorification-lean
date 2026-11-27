/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeBlackInduction
import Categorification.WeightedKLR.RedStrands.PrependBlack

/-!
# The reflected black induction `F̃_i^*` on `T̃^λ`

Webster, arXiv:1309.3796v3, Proposition 4.39, compatibility (4.40) for the reflected
functors `F̃_i^*`: induction along the map `prependBlackStendhal` that adds a black strand on
the left. Webster's printed form, `[F̃_i^*](u ⊗ w) ↦ F_i · (u ⊗ w)`, uses his right action
for `F̃_i`; with the corrected left action of ERRATA entry 11 (`negTensorF`) the two sides
exchange, and `F̃_i^*` acts by right multiplication `u ⊗ w ↦ u F_i ⊗ w` on the first factor.
For `λ = ∅` this is the statement that the class of the word `(i, i_1, …, i_n)` is
`F_{i_n} ⋯ F_{i_1} F_i`.

## Main definitions and results

* `tildeLeftBlackIndK0`, `tildeLeftLower` : the map induced by `F̃_i^*` on `K₀(T̃^λ)`.
* `TensorWord.prependBlack` : the word with a black block `i` of size one added on the left.
* `negWordVector_prependBlack` : `p̃_{i w} = p̃_w · F_i`.
* `tildeLeftLower_tildeClass` : `F̃_i^* [P̃_w] = [P̃_{i w}]`.
* `map_tildeLeftLower`, `exists_negIntegralTensorEquiv_leftLower` : the isomorphism of
  Proposition 4.39 intertwines `F̃_i^*` with right multiplication by `F_i`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded DirectSum MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Lowering

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => stendhalGrade G ν
local notation "dst" => stendhalGrade G νᵢ
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "T'" => StendhalAlgebra k Q Λ νᵢ
local notation "φ" => prependBlackStendhal Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
local notation "cornerGr" => Graded.submodule dst (lIdeal (φ 1))

private def tildeLeftProjective : GProj dst :=
  GProj.ofIdempotent (φ 1) (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))
    (prependBlackStendhal_mem_grade Q Λ i ν G SetLike.GradedOne.one_mem)

private local instance tildeLeftFinite : Module.Finite T' Mc :=
  Module.Finite.of_surjective (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T')))
    fun z => ⟨z, Subtype.ext z.property⟩

private local instance tildeLeftProjectiveModule : Module.Projective T' Mc :=
  Module.Projective.of_split (leftIdeal (φ 1)).subtype
    (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))) (leftIdealProj_comp_subtype _)

private theorem tildeLeftScalarTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeLeftDecomposition : DirectSum.Decomposition cornerGr :=
  (tildeLeftProjective G i ν).decomposition

private local instance tildeLeftOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private theorem tildeLeftRightAction_mem {d n : ℤ} {m : Mc} {a : T}
    (hm : m ∈ cornerGr d) (ha : a ∈ src n) : op a • m ∈ cornerGr (d + n) :=
  SetLike.GradedMul.mul_mem (A := dst) hm (prependBlackStendhal_mem_grade Q Λ i ν G ha)

/-- The reflected induction functor `F̃_i^*` of graded projective `T̃^λ`-modules, along the
left black strand map (Webster, arXiv:1309.3796v3, before Proposition 4.39). -/
def tildeLeftBlackIndProj (P : GProj src) : GProj dst :=
  @balancedIndGProj k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftScalarTower i ν) _ _
    (tildeLeftOpTower i ν) _ _ cornerGr (tildeLeftProjective G i ν).decomposition
    (tildeLeftProjective G i ν).gradedSMul (fun _ _ _ _ => tildeLeftRightAction_mem G i ν) P

/-- The map of `F̃_i^*` on graded projective Grothendieck groups of `T̃^λ`. -/
def tildeLeftBlackIndK0 : K0 src →ₗ[LaurentPolynomial ℤ] K0 dst :=
  @balancedIndK0 k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftScalarTower i ν) _ _
    (tildeLeftOpTower i ν) _ _ cornerGr (tildeLeftProjective G i ν).decomposition
    (tildeLeftProjective G i ν).gradedSMul (fun _ _ _ _ => tildeLeftRightAction_mem G i ν)

@[simp] theorem tildeLeftBlackIndK0_of (P : GProj src) :
    tildeLeftBlackIndK0 G i ν (K0.of P) = K0.of (tildeLeftBlackIndProj G i ν P) :=
  @balancedIndK0_of k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftScalarTower i ν) _ _
    (tildeLeftOpTower i ν) _ _ cornerGr (tildeLeftProjective G i ν).decomposition
    (tildeLeftProjective G i ν).gradedSMul (fun _ _ _ _ => tildeLeftRightAction_mem G i ν) P

local notation "K" => fun β : Multiset I => K0 (stendhalGrade G β)

/-- `F̃_i^*` on the sum of the projective Grothendieck groups of all black contents. -/
def tildeLeftLower : (⨁ β : Multiset I, K β) →ₗ[LaurentPolynomial ℤ] ⨁ β : Multiset I, K β :=
  DirectSum.toModule _ _ _ fun β =>
    DirectSum.lof _ _ _ ((Singleton.singleton i : Multiset I) + β) ∘ₗ tildeLeftBlackIndK0 G i β

@[simp] theorem tildeLeftLower_lof (x : K ν) :
    tildeLeftLower G i (DirectSum.lof (LaurentPolynomial ℤ) _ K ν x) =
      DirectSum.lof (LaurentPolynomial ℤ) _ K νᵢ (tildeLeftBlackIndK0 G i ν x) :=
  DirectSum.toModule_lof ..

end Lowering

section Principal

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => stendhalGrade G ν
local notation "dst" => stendhalGrade G νᵢ
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "T'" => StendhalAlgebra k Q Λ νᵢ
local notation "φ" => prependBlackStendhal Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')

private local instance tildeLeftPrincipalTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeLeftPrincipalOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private def tildeLeftIndMul (e : T) : BalancedTensor k T' T Mc (leftIdeal e) →ₗ[T'] T' :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T' T Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem tildeLeftIndMul_tmul (e : T) (b : Mc) (x : leftIdeal e) :
    tildeLeftIndMul (Q := Q) (Λ := Λ) i ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

private def tildeLeftIndPrincipalEquiv {e : T} (he : IsIdempotentElem e) :
    BalancedTensor k T' T Mc (leftIdeal e) ≃ₗ[T'] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (tildeLeftIndMul (Q := Q) (Λ := Λ) i ν e).codRestrict (leftIdeal (φ e)) fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      change (b.val * φ x.val) * φ e = b.val * φ x.val
      rw [mul_assoc, ← map_mul, mem_leftIdeal.mp x.2]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have inc (z : leftIdeal (φ e)) : z.val ∈ lIdeal (φ 1) := by
    change z.val * φ 1 = z.val
    conv_lhs => rw [← mem_leftIdeal.mp z.property, mul_assoc, ← map_mul, mul_one]
    exact z.property
  let g : leftIdeal (φ e) →ₗ[T'] BalancedTensor k T' T Mc (leftIdeal e) :=
    { toFun := fun b => BalancedTensor.tmul (⟨b.val, inc b⟩ : Mc) p
      map_add' := fun x y => BalancedTensor.add_tmul (⟨x.val, inc x⟩ : Mc) (⟨y.val, inc y⟩ : Mc) p
      map_smul' := fun c x => BalancedTensor.smul_tmul' c (⟨x.val, inc x⟩ : Mc) p }
  apply LinearEquiv.ofLinearMap f g
  · ext x
    exact x.property
  · apply BalancedTensor.extB
    intro b x
    change BalancedTensor.tmul (op x.val • b) p = BalancedTensor.tmul b x
    rw [BalancedTensor.op_smul_tmul]
    exact congrArg (BalancedTensor.tmul b) (Subtype.ext (mem_leftIdeal.mp x.property))

/-- `F̃_i^*` sends a degree-zero principal projective of `T̃^λ` to the one at the idempotent
with the black strand added on the left. -/
theorem tildeLeftBlackIndK0_ofIdempotent {e : T} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    tildeLeftBlackIndK0 G i ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dst) (φ e) (he.map φ)
        (prependBlackStendhal_mem_grade Q Λ i ν G he0)) := by
  rw [tildeLeftBlackIndK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (tildeLeftIndPrincipalEquiv (Q := Q) (Λ := Λ) i ν he) ?_
  intro d y hy
  change tildeLeftIndMul (Q := Q) (Λ := Λ) i ν e y ∈ dst d
  apply balancedGrading_map_mem dst
    ((tildeLeftIndMul (Q := Q) (Λ := Λ) i ν e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, tildeLeftIndMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dst) hz (prependBlackStendhal_mem_grade Q Λ i ν G hx)

end Principal

namespace FirstWeight

open QuantumGroup KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

section Words

variable {I : Type*}

/-- Add a black block `i` of size one on the left of a word. -/
def TensorWord.prependBlack (i : I) : {n : ℕ} → TensorWord I n → TensorWord I n
  | _, .empty => .black .empty i 1
  | _, .red w => .red (w.prependBlack i)
  | _, .black w j a => .black (w.prependBlack i) j a

theorem TensorWord.content_prependBlack (i : I) : ∀ {n : ℕ} (w : TensorWord I n),
    (w.prependBlack i).content = w.content + Finsupp.single i 1
  | _, .empty => by simp [TensorWord.prependBlack, TensorWord.content]
  | _, .red w => by
    simp only [TensorWord.prependBlack, TensorWord.content, w.content_prependBlack i]
  | _, .black w j a => by
    simp only [TensorWord.prependBlack, TensorWord.content, w.content_prependBlack i]
    abel

theorem TensorWord.content_prependBlack_toMultiset {n : ℕ} (w : TensorWord I n) (i : I) :
    (w.prependBlack i).content.toMultiset =
      (Singleton.singleton i : Multiset I) + w.content.toMultiset := by
  simp [w.content_prependBlack i, Finsupp.toMultiset_add, add_comm]

theorem TensorWord.blackBlocks_prependBlack (i : I) : ∀ {n : ℕ} (w : TensorWord I n),
    (w.prependBlack i).blackBlocks = (i, 1) :: w.blackBlocks
  | _, .empty => rfl
  | _, .red w => by
    simp only [TensorWord.prependBlack, TensorWord.blackBlocks, w.blackBlocks_prependBlack i]
  | _, .black w j a => by
    simp only [TensorWord.prependBlack, TensorWord.blackBlocks, w.blackBlocks_prependBlack i,
      List.cons_append]

theorem TensorWord.blocks_prependBlack (i : I) : ∀ {n : ℕ} (w : TensorWord I n),
    (w.prependBlack i).blocks = (.inl i, 1) :: w.blocks
  | _, .empty => rfl
  | _, .red w => by
    simp [TensorWord.prependBlack, TensorWord.blocks, w.blocks_prependBlack i]
  | _, .black w j a => by
    simp [TensorWord.prependBlack, TensorWord.blocks, w.blocks_prependBlack i]

variable {ℓ : ℕ}

/-- The loading of `i w` is the loading of `w` with a black strand `i` added on the left. -/
theorem TensorWord.prependBlackLoading_loading (w : TensorWord I ℓ) (i : I) :
    prependBlackLoading i _ w.loading =
      Seq.cast (congrArg (stendhalWeight ℓ) (w.content_prependBlack_toMultiset i))
        (w.prependBlack i).loading := by
  have he : expandDiv (w.prependBlack i).blocks = .inl i :: expandDiv w.blocks := by
    rw [w.blocks_prependBlack i]
    simp [expandDiv]
  apply Subtype.ext
  funext a
  change (prependBlackLoading i _ w.loading).lbl a = (w.prependBlack i).loading.lbl (Fin.cast _ a)
  change _ = (expandDiv (w.prependBlack i).blocks)[(a : ℕ)]'_
  simp only [getElem_congr_coll he]
  by_cases ha : a.val = 0
  · rw [prependBlackLoading_lbl_zero i _ _ a ha]
    simp [ha]
  · obtain ⟨c, rfl⟩ := eq_prependBlackPosition_of_ne_zero i _ a ha
    rw [prependBlackLoading_lbl, TensorWord.loading, Seq.ofList_lbl]
    simp

end Words

section Vectors

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "ρ" => tensorRepresentation
local instance instNeZeroXTildeLeft : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

variable (D) in
/-- Right multiplication by `F_i` on `U⁻ = 'f ⧸ J`. -/
def negFRight (i : I) : Um D 𝕍 →ₗ[𝕂] Um D 𝕍 :=
  (serreSubmodule D 𝕍).mapQ (serreSubmodule D 𝕍) (LinearMap.mulRight 𝕂 (FreeAlgebra.ι 𝕂 i))
    (fun _ hy => mem_serreSubmodule.mpr ((LusztigF.serreIdeal D 𝕍).mul_mem_right _ _
      (mem_serreSubmodule.mp hy)))

omit [DecidableEq I] in
theorem negFRight_mk (i : I) (y : LusztigF 𝕂 I) :
    negFRight D i (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y * FreeAlgebra.ι 𝕂 i) :=
  rfl

omit [DecidableEq I] in
theorem negFRight_comp_negF (i j : I) :
    negFRight D i ∘ₗ negF D j = negF D j ∘ₗ negFRight D i := by
  ext y
  change Submodule.Quotient.mk (FreeAlgebra.ι 𝕂 j * y * FreeAlgebra.ι 𝕂 i) =
    Submodule.Quotient.mk (FreeAlgebra.ι 𝕂 j * (y * FreeAlgebra.ι 𝕂 i))
  rw [mul_assoc]

theorem commute_negFRight_negTensorF {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i j : I) :
    Commute (TensorProduct.map (negFRight D i) LinearMap.id) (negTensorF D wt j) := by
  change _ ∘ₗ _ = _ ∘ₗ _
  rw [negTensorF, LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    negFRight_comp_negF]
  rfl

/-- `p̃_{i w} = p̃_w · F_i`: a black strand on the left of the word multiplies the `U⁻`
factor by `F_i` on the right. -/
theorem negWordVector_prependBlack (i : I) : ∀ {n : ℕ} (w : TensorWord I n)
    (wt : Fin n → Dom R), negWordVector D (w.prependBlack i) wt =
      TensorProduct.map (negFRight D i) LinearMap.id (negWordVector D w wt)
  | _, .empty, wt => by
    have h1 : qDivPow (𝕍 ^ D.d i) 1 (negTensorF D wt i) = negTensorF D wt i := by
      simp [qDivPow, qFactorial, qInt]
    have hF : ρ wt (F R 𝕍 i) = 0 := by
      change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))) (counit R 𝕍 (F R 𝕍 i)) = 0
      simp
    have hK : ρ wt (K R 𝕍 (-ktilde R i)) = 1 := by
      change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))) (counit R 𝕍 _) = 1
      simp
    change qDivPow (𝕍 ^ D.d i) 1 (negTensorF D wt i) _ = _
    rw [h1, negTensorF, hF, hK, TensorProduct.map_zero_right, add_zero, Module.End.one_eq_id]
    change TensorProduct.map (negF D i) LinearMap.id ((Submodule.Quotient.mk 1 : Um D 𝕍) ⊗ₜ _) =
      TensorProduct.map (negFRight D i) LinearMap.id ((Submodule.Quotient.mk 1 : Um D 𝕍) ⊗ₜ _)
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, negF_mk, negFRight_mk, mul_one, one_mul]
  | _, .red w, wt => by
    change TensorProduct.map LinearMap.id (appendHighest wt)
        (negWordVector D (w.prependBlack i) _) = _
    rw [negWordVector_prependBlack i w]
    change _ = TensorProduct.map (negFRight D i) LinearMap.id
      (TensorProduct.map LinearMap.id (appendHighest wt) _)
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      ← TensorProduct.map_comp]
    rfl
  | _, .black w j a, wt => by
    change negTensorDivF D wt j a (negWordVector D (w.prependBlack i) wt) =
      TensorProduct.map (negFRight D i) LinearMap.id (negTensorDivF D wt j a _)
    rw [negWordVector_prependBlack i w, negTensorDivF, qDivPow, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact (LinearMap.congr_fun ((commute_negFRight_negTensorF wt i j).pow_right a) _).symm

end Vectors

section Classes

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

local notation "LP" => LaurentPolynomial ℤ
local notation "D" => C.toLusztig
local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private abbrev invLPL := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance instRingHomInvPairInvLPLeft : RingHomInvPair invLPL.toRingHom invLPL.toRingHom :=
  RingHomInvPair.of_ringEquiv invLPL
local instance instNeZeroXTildeLeftClasses : NeZero (RatFunc.X : RatFunc ℚ) :=
  ⟨RatFunc.X_ne_zero⟩

variable (Λ : Fin ℓ → I →₀ ℕ)

local notation "fam" => fun β : Multiset I => K0 (stendhalGrade (moduleGrading Λ) β)

private theorem lof_e_cast_left {δ δ' : Multiset I} (h : δ = δ') (s : Seq (stendhalWeight ℓ δ))
    (hs : IsRedOrdered s) (hs' : IsRedOrdered (Seq.cast (congrArg (stendhalWeight ℓ) h) s))
    (he he' he0 he0') :
    DirectSum.lof LP _ fam δ (K0.of (GProj.ofIdempotent (StendhalAlgebra.e (k := k) (Q := Q)
      (Λ := Λ) s hs) he he0)) =
    DirectSum.lof LP _ fam δ' (K0.of (GProj.ofIdempotent
      (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) _ hs') he' he0')) := by
  subst h
  rfl

/-- **`F̃_i^* [P̃_w] = [P̃_{i w}]`** (Webster, arXiv:1309.3796v3, Proposition 4.39, (4.40)):
inducing along the left black strand adds a black block of size one on the left of the
word. -/
theorem tildeLeftLower_tildeClass (w : TensorWord I ℓ) (i : I) :
    tildeLeftLower (moduleGrading Λ) i
        (DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w)) =
      DirectSum.lof LP _ fam (w.prependBlack i).content.toMultiset
        (tildeClass C hQ Λ (w.prependBlack i)) := by
  have hf : divQFact2 C (w.prependBlack i).blackBlocks = divQFact2 C w.blackBlocks := by
    rw [w.blackBlocks_prependBlack i, show (i, 1) :: w.blackBlocks = [(i, 1)] ++ w.blackBlocks
      from rfl, divQFact2_append]
    simp [divQFact2]
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [h, map_zero])
  apply tildeK0_smul_injective C hQ Λ hn
  dsimp only
  rw [← map_smul, lof_tildeClass_factorial, ← hf, lof_tildeClass_factorial, tildeLeftLower_lof]
  erw [tildeLeftBlackIndK0_ofIdempotent]
  have hs := prependBlackLoading_ordered i _ w.loading w.blocks_redOrdered
  refine Eq.trans ?_ (lof_e_cast_left C hQ Λ (w.content_prependBlack_toMultiset i)
    (w.prependBlack i).loading (w.prependBlack i).blocks_redOrdered
    (by rw [← w.prependBlackLoading_loading i]; exact hs) _
    (stendhal_e_idem Λ _ _ _) _ (e_mem_stendhalGrade _ _ _ _)).symm
  refine congrArg _ (K0.of_ofIdempotent_congr ?_ _ _ _ _)
  refine (prependBlackStendhal_e Q Λ i _ w.loading w.blocks_redOrdered).trans ?_
  congr 1
  exact w.prependBlackLoading_loading i

variable {wt : Fin ℓ → Dom R}

include hR in
/-- **Compatibility (4.40) of Proposition 4.39 with the reflected functors `F̃_i^*`**
(Webster, arXiv:1309.3796v3, in the corrected convention of ERRATA entry 11): a semilinear
map `K₀(T̃^λ) → U^{-,ℤ} ⊗ V^ℤ_λ` sending every `[P̃_w]` to `p̃_w` intertwines `F̃_i^*` with
`u ⊗ w ↦ u F_i ⊗ w`. -/
theorem map_tildeLeftLower [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {σ : LP →+* LP}
    (f : DirectSum (Multiset I) fam →ₛₗ[σ] negIntegralTensor C wt)
    (hw : ∀ w : TensorWord I ℓ, (f (DirectSum.lof LP _ fam w.content.toMultiset
      (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt)
    (i : I) (x : DirectSum (Multiset I) fam) :
    (f (tildeLeftLower (moduleGrading Λ) i x) : NegTensor D wt) =
      TensorProduct.map (negFRight D i) LinearMap.id (f x : NegTensor D wt) := by
  have hx : x ∈ Submodule.span LP (Set.range fun w : TensorWord I ℓ =>
      DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w)) := by
    rw [span_lof_tildeClass C hQ hR Λ hρ hwt]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [tildeLeftLower_tildeClass, hw, hw, negWordVector_prependBlack]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      negTensor_laurent_smul, negTensor_laurent_smul, map_smul, hx]

include hR in
/-- **Webster, arXiv:1309.3796v3, Proposition 4.39 with the compatibility (4.40) for
`F̃_i^*`**, in the corrected convention of ERRATA entry 11: the isomorphism
`K₀(T̃^λ) ≅ U^{-,ℤ} ⊗ V^ℤ_λ`, `[P̃_w] ↦ p̃_w`, intertwines `F̃_i^*` with right multiplication
by `F_i` on `U⁻`. Same route hypothesis as `exists_negIntegralTensorEquiv`. -/
theorem exists_negIntegralTensorEquiv_leftLower [Finite I]
    (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ e : DirectSum (Multiset I) fam ≃ₛₗ[invLPL.toRingHom] negIntegralTensor C wt,
      (∀ w : TensorWord I ℓ, (e (DirectSum.lof LP _ fam w.content.toMultiset
        (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt) ∧
      ∀ (i : I) (x : DirectSum (Multiset I) fam),
        (e (tildeLeftLower (moduleGrading Λ) i x) : NegTensor D wt) =
          TensorProduct.map (negFRight D i) LinearMap.id (e x : NegTensor D wt) := by
  obtain ⟨e, he⟩ := exists_negIntegralTensorEquiv hQ hR hρ Λ hwt
  exact ⟨e, he, map_tildeLeftLower C hQ hR Λ hρ hwt e.toLinearMap he⟩

end Classes

end FirstWeight

end Categorification.Stendhal
