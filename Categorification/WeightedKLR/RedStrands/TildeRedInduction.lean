/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeBlackInduction

/-!
# Red induction on `T̃^λ` and `⊗ v_λ`

Webster, arXiv:1309.3796v3, Proposition 4.39, compatibility (4.40) for the red induction
functor `Ĩ_λ`. Appending a red strand on the right gives a non-unital map
`T̃^{λ₀} → T̃^{(λ₀, λ)}` (`appendRedStendhalValue`) whose value on the unit is the terminal red
idempotent; `Ĩ_λ` is extension of scalars along it.

## Main definitions and results

* `tildeRedIndK0`, `totalTildeRedInd` : the map induced by `Ĩ_λ` on `K₀(T̃^λ)`.
* `totalTildeRedInd_tildeClass` : `Ĩ_λ [P̃_w] = [P̃_{w λ}]`, appending the red strand to the
  word.
* `map_totalTildeRedInd`, `exists_negIntegralTensorEquiv_red` : the isomorphisms of
  Proposition 4.39 intertwine `Ĩ_λ` with `u ⊗ w ↦ u ⊗ w ⊗ v_λ`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded DirectSum MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Induction

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin (ℓ + 1) → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)

local notation "src" => stendhalGrade (restrictRedGrading Q Λ G) ν
local notation "dst" => stendhalGrade G ν
local notation "T" => StendhalAlgebra k Q (Λ ∘ Fin.castSucc) ν
local notation "T'" => StendhalAlgebra k Q Λ ν
local notation "φ" => appendRedStendhalValue Q Λ ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
local notation "cornerGr" => Graded.submodule dst (lIdeal (φ 1))

private def tildeRedProjective : GProj dst :=
  GProj.ofIdempotent (φ 1) (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))
    (appendRedStendhalValue_mem_grade Q Λ ν G SetLike.GradedOne.one_mem)

private local instance tildeRedFinite : Module.Finite T' Mc :=
  Module.Finite.of_surjective (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T')))
    fun z => ⟨z, Subtype.ext z.property⟩

private local instance tildeRedProjectiveModule : Module.Projective T' Mc :=
  Module.Projective.of_split (leftIdeal (φ 1)).subtype
    (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))) (leftIdealProj_comp_subtype _)

private theorem tildeRedScalarTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeRedDecomposition : DirectSum.Decomposition cornerGr :=
  (tildeRedProjective G ν).decomposition

private local instance tildeRedOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [appendRedStendhalValue_smul, mul_smul_comm])

private theorem tildeRedRightAction_mem {d n : ℤ} {m : Mc} {a : T}
    (hm : m ∈ cornerGr d) (ha : a ∈ src n) : op a • m ∈ cornerGr (d + n) :=
  SetLike.GradedMul.mul_mem (A := dst) hm (appendRedStendhalValue_mem_grade Q Λ ν G ha)

/-- The red induction functor `Ĩ_λ` of graded projective `T̃^λ`-modules (Webster,
arXiv:1309.3796v3, Proposition 4.39). -/
def tildeRedIndProj (P : GProj src) : GProj dst :=
  @balancedIndGProj k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeRedScalarTower ν) _ _
    (tildeRedOpTower ν) _ _ cornerGr (tildeRedProjective G ν).decomposition
    (tildeRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeRedRightAction_mem G ν) P

/-- The map of `Ĩ_λ` on graded projective Grothendieck groups of `T̃^λ`. -/
def tildeRedIndK0 : K0 src →ₗ[LaurentPolynomial ℤ] K0 dst :=
  @balancedIndK0 k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeRedScalarTower ν) _ _
    (tildeRedOpTower ν) _ _ cornerGr (tildeRedProjective G ν).decomposition
    (tildeRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeRedRightAction_mem G ν)

@[simp] theorem tildeRedIndK0_of (P : GProj src) :
    tildeRedIndK0 G ν (K0.of P) = K0.of (tildeRedIndProj G ν P) :=
  @balancedIndK0_of k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeRedScalarTower ν) _ _
    (tildeRedOpTower ν) _ _ cornerGr (tildeRedProjective G ν).decomposition
    (tildeRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeRedRightAction_mem G ν) P

end Induction

section Principal

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin (ℓ + 1) → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)

local notation "src" => stendhalGrade (restrictRedGrading Q Λ G) ν
local notation "dst" => stendhalGrade G ν
local notation "T" => StendhalAlgebra k Q (Λ ∘ Fin.castSucc) ν
local notation "T'" => StendhalAlgebra k Q Λ ν
local notation "φ" => appendRedStendhalValue Q Λ ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')

private local instance tildeRedPrincipalTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeRedPrincipalOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [appendRedStendhalValue_smul, mul_smul_comm])

private def tildeRedIndMul (e : T) : BalancedTensor k T' T Mc (leftIdeal e) →ₗ[T'] T' :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T' T Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem tildeRedIndMul_tmul (e : T) (b : Mc) (x : leftIdeal e) :
    tildeRedIndMul (Q := Q) (Λ := Λ) ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

private def tildeRedIndPrincipalEquiv {e : T} (he : IsIdempotentElem e) :
    BalancedTensor k T' T Mc (leftIdeal e) ≃ₗ[T'] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (tildeRedIndMul (Q := Q) (Λ := Λ) ν e).codRestrict (leftIdeal (φ e)) fun t => by
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

/-- `Ĩ_λ` sends a degree-zero principal projective of `T̃^λ` to the one at the appended
idempotent. -/
theorem tildeRedIndK0_ofIdempotent {e : T} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    tildeRedIndK0 G ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dst) (φ e) (he.map φ)
        (appendRedStendhalValue_mem_grade Q Λ ν G he0)) := by
  rw [tildeRedIndK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (tildeRedIndPrincipalEquiv (Q := Q) (Λ := Λ) ν he) ?_
  intro d y hy
  change tildeRedIndMul (Q := Q) (Λ := Λ) ν e y ∈ dst d
  apply balancedGrading_map_mem dst ((tildeRedIndMul (Q := Q) (Λ := Λ) ν e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, tildeRedIndMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dst) hz (appendRedStendhalValue_mem_grade Q Λ ν G hx)

end Principal

namespace FirstWeight

open QuantumGroup KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

local notation "LP" => LaurentPolynomial ℤ
local notation "D" => C.toLusztig
local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private abbrev invLPR := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance instRingHomInvPairInvLPRed : RingHomInvPair invLPR.toRingHom invLPR.toRingHom :=
  RingHomInvPair.of_ringEquiv invLPR
local instance instNeZeroXTildeRed : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩

variable (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "fam" Λ' => fun β : Multiset I => K0 (stendhalGrade (moduleGrading Λ') β)

omit [DecidableEq I] in
theorem restrictRedGrading_moduleGrading :
    restrictRedGrading Q Λ (moduleGrading Λ) = moduleGrading Λ₀ := by
  unfold restrictRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

private def tildeRedIndAt (G₀ : GradingDatum (stendhalQ Q Λ₀))
    (h : restrictRedGrading Q Λ (moduleGrading Λ) = G₀) (β : Multiset I) :
    K0 (stendhalGrade G₀ β) →ₗ[LP] K0 (stendhalGrade (moduleGrading Λ) β) :=
  h ▸ tildeRedIndK0 (moduleGrading Λ) β

private theorem tildeRedIndAt_e (G₀ : GradingDatum (stendhalQ Q Λ₀))
    (h : restrictRedGrading Q Λ (moduleGrading Λ) = G₀) {β : Multiset I}
    (s : Seq (stendhalWeight ℓ β)) (hs : IsRedOrdered s) (he he0 he' he0') :
    tildeRedIndAt C hQ Λ G₀ h β (K0.of (GProj.ofIdempotent
      (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ₀) s hs) he he0)) =
    K0.of (GProj.ofIdempotent (StendhalAlgebra.e (appendRedLoading s)
      ((appendRedLoading_ordered_iff s).2 hs)) he' he0') := by
  subst h
  exact (tildeRedIndK0_ofIdempotent _ β he he0).trans
    (K0.of_ofIdempotent_congr (appendRedStendhalValue_e Q Λ β s hs) _ _ _ _)

/-- `Ĩ_λ` on the sum over all black contents. -/
def totalTildeRedInd : DirectSum (Multiset I) (fam Λ₀) →ₗ[LP] DirectSum (Multiset I) (fam Λ) :=
  DirectSum.toModule _ _ _ fun β => DirectSum.lof LP _ (fam Λ) β ∘ₗ
    tildeRedIndAt C hQ Λ _ (restrictRedGrading_moduleGrading C hQ Λ) β

/-- **`Ĩ_λ [P̃_w] = [P̃_{w λ}]`** (Webster, arXiv:1309.3796v3, Proposition 4.39, (4.40)):
inducing along the right red strand appends the red strand to the word. -/
theorem totalTildeRedInd_tildeClass (w : TensorWord I ℓ) :
    totalTildeRedInd C hQ Λ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
        (tildeClass C hQ Λ₀ w)) =
      DirectSum.lof LP _ (fam Λ) w.red.content.toMultiset (tildeClass C hQ Λ w.red) := by
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [h, map_zero])
  apply tildeK0_smul_injective C hQ Λ hn
  dsimp only
  rw [← map_smul, lof_tildeClass_factorial, ← show w.red.blackBlocks = w.blackBlocks from rfl,
    lof_tildeClass_factorial, totalTildeRedInd, DirectSum.toModule_lof, LinearMap.comp_apply]
  refine (congrArg (DirectSum.lof LP _ (fam Λ) _) (tildeRedIndAt_e C hQ Λ _ _ w.loading
    w.blocks_redOrdered _ _ (stendhal_e_idem Λ _ _ _) (e_mem_stendhalGrade _ _ _ _))).trans ?_
  refine congrArg _ (K0.of_ofIdempotent_congr ?_ _ _ _ _)
  congr 1
  exact w.loading_red.symm

variable {wt : Fin (ℓ + 1) → Dom R}

local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)

include hR in
/-- **Compatibility (4.40) of Proposition 4.39 with red induction** (Webster,
arXiv:1309.3796v3): semilinear maps `K₀(T̃^λ) → U^{-,ℤ} ⊗ V^ℤ_λ` sending every `[P̃_w]` to
`p̃_w`, for the labels `λ₀ = (λ_1, …, λ_ℓ)` and `λ = (λ₀, λ_{ℓ+1})`, intertwine `Ĩ_{λ_{ℓ+1}}`
with `u ⊗ w ↦ u ⊗ w ⊗ v_{λ_{ℓ+1}}`. -/
theorem map_totalTildeRedInd [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {σ : LP →+* LP}
    (f₀ : DirectSum (Multiset I) (fam Λ₀) →ₛₗ[σ] negIntegralTensor C wt₀)
    (f : DirectSum (Multiset I) (fam Λ) →ₛₗ[σ] negIntegralTensor C wt)
    (hw₀ : ∀ w : TensorWord I ℓ, (f₀ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
      (tildeClass C hQ Λ₀ w)) : NegTensor D wt₀) = negWordVector D w wt₀)
    (hw : ∀ w : TensorWord I (ℓ + 1), (f (DirectSum.lof LP _ (fam Λ) w.content.toMultiset
      (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt)
    (x : DirectSum (Multiset I) (fam Λ₀)) :
    (f (totalTildeRedInd C hQ Λ x) : NegTensor D wt) =
      TensorProduct.map LinearMap.id (appendHighest wt) (f₀ x : NegTensor D wt₀) := by
  have hx : x ∈ Submodule.span LP (Set.range fun w : TensorWord I ℓ =>
      DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset (tildeClass C hQ Λ₀ w)) := by
    rw [span_lof_tildeClass C hQ hR Λ₀ hρ (fun r i => hwt _ i)]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [totalTildeRedInd_tildeClass, hw, hw₀]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f₀.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      negTensor_laurent_smul, negTensor_laurent_smul, map_smul, hx]

include hR in
/-- **Webster, arXiv:1309.3796v3, Proposition 4.39 with the compatibility (4.40) for
`Ĩ_λ`**: the isomorphisms `K₀(T̃^λ) ≅ U^{-,ℤ} ⊗ V^ℤ_λ`, `[P̃_w] ↦ p̃_w`, for `λ₀` and for
`(λ₀, λ_{ℓ+1})` intertwine `Ĩ_{λ_{ℓ+1}}` with `u ⊗ w ↦ u ⊗ w ⊗ v_{λ_{ℓ+1}}`. Same route
hypothesis as `exists_negIntegralTensorEquiv`. -/
theorem exists_negIntegralTensorEquiv_red [Finite I]
    (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ (e₀ : DirectSum (Multiset I) (fam Λ₀) ≃ₛₗ[invLPR.toRingHom] negIntegralTensor C wt₀)
      (e : DirectSum (Multiset I) (fam Λ) ≃ₛₗ[invLPR.toRingHom] negIntegralTensor C wt),
      (∀ w : TensorWord I ℓ, (e₀ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
        (tildeClass C hQ Λ₀ w)) : NegTensor D wt₀) = negWordVector D w wt₀) ∧
      (∀ w : TensorWord I (ℓ + 1), (e (DirectSum.lof LP _ (fam Λ) w.content.toMultiset
        (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt) ∧
      ∀ x, (e (totalTildeRedInd C hQ Λ x) : NegTensor D wt) =
        TensorProduct.map LinearMap.id (appendHighest wt) (e₀ x : NegTensor D wt₀) := by
  obtain ⟨e₀, he₀⟩ := exists_negIntegralTensorEquiv (wt := wt₀) hQ hR hρ Λ₀ (fun r i => hwt _ i)
  obtain ⟨e, he⟩ := exists_negIntegralTensorEquiv hQ hR hρ Λ hwt
  exact ⟨e₀, e, he₀, he, map_totalTildeRedInd C hQ hR Λ hρ hwt e₀.toLinearMap e.toLinearMap he₀ he⟩

end FirstWeight

end Categorification.Stendhal
