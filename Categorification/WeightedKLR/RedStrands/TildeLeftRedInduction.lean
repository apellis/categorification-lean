/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeRedInduction
import Categorification.WeightedKLR.RedStrands.PrependRed
import Categorification.WeightedKLR.RedStrands.NegTensorPrepend

/-!
# The reflected red induction `Ĩ_λ^*` on `T̃^λ`

Webster, arXiv:1309.3796v3, Proposition 4.39, compatibility (4.40) for the reflected red
induction `Ĩ_λ^*`: induction along the map `prependRedStendhal` that adds a red strand on the
left of every red-ordered diagram of `T̃^λ`. It corresponds to
`u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_λ ⊗ w)` (`negTensorPrepend`).

## Main definitions and results

* `prependRedStendhal` : the non-unital map `T̃^{λ} → T̃^{(λ₀, λ)}`.
* `tildeLeftRedIndK0`, `totalTildeLeftRedInd` : the map induced by `Ĩ_λ^*` on `K₀(T̃^λ)`.
* `totalTildeLeftRedInd_tildeClass` : `Ĩ_{λ₀}^* [P̃_w] = [P̃_{λ₀ w}]`.
* `map_totalTildeLeftRedInd`, `exists_negIntegralTensorEquiv_leftRed` : the isomorphisms of
  Proposition 4.39 intertwine `Ĩ_{λ₀}^*` with `negTensorPrepend`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded DirectSum MulOpposite

section Algebra

variable {I : Type*} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.succ)
local notation "μ" => stendhalWeight ℓ ν
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν

/-- `prependRedAllOrders` as a non-unital ring map into the ambient all-orders algebra. -/
def prependRedValue : StendhalAlgebraAllOrders k Q Λ₀ ν →ₙ+* A :=
  (KLR.cornerVal (isIdempotentElem_firstRedIdem Q Λ ν)).comp
    (prependRedAllOrders Q Λ ν).toRingHom.toNonUnitalRingHom

theorem prependRedValue_e (s : Seq μ) :
    prependRedValue Q Λ ν (StendhalAlgebraAllOrders.e s) =
      StendhalAlgebraAllOrders.e (prependRedLoading s) :=
  prependRedAllOrders_e Q Λ ν s

theorem prependRedValue_smul (c : k) (z : StendhalAlgebraAllOrders k Q Λ₀ ν) :
    prependRedValue Q Λ ν (c • z) = c • prependRedValue Q Λ ν z := by
  change (prependRedAllOrders Q Λ ν (c • z)).val = c • (prependRedAllOrders Q Λ ν z).val
  rw [AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem prependRedValue_ordered :
    prependRedValue Q Λ ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν) ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  classical
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  let J := Finset.univ.filter (fun s : Seq μ => IsRedOrdered s)
  let P := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  let E := ∑ s ∈ J, (StendhalAlgebraAllOrders.e s : StendhalAlgebraAllOrders k Q Λ₀ ν)
  change P * prependRedValue Q Λ ν E = prependRedValue Q Λ ν E ∧
    prependRedValue Q Λ ν E * P = prependRedValue Q Λ ν E
  dsimp only [E]
  simp only [map_sum, prependRedValue_e]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact (StendhalAlgebraAllOrders.redOrderedIdem_mul_e _).trans
      (ite_eq_left ((prependRedLoading_ordered_iff s).2 (Finset.mem_filter.mp hs).2))
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem _).trans
      (ite_eq_left ((prependRedLoading_ordered_iff s).2 (Finset.mem_filter.mp hs).2))

private theorem prependRedValue_corner (z : StendhalAlgebra k Q Λ₀ ν) :
    prependRedValue Q Λ ν z.val ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  let f := prependRedValue Q Λ ν
  let E : StendhalAlgebra k Q Λ ν := ⟨_, prependRedValue_ordered Q Λ ν⟩
  have hl : E.val * f z.val = f z.val :=
    (map_mul f _ _).symm.trans (congrArg f (KLR.Corner.E_mul_val z))
  have hr : f z.val * E.val = f z.val :=
    (map_mul f _ _).symm.trans (congrArg f (KLR.Corner.val_mul_E z))
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  exact ⟨by rw [← hl, ← mul_assoc]; exact congrArg (· * f z.val) (KLR.Corner.E_mul_val E),
    by rw [← hr, mul_assoc]; exact congrArg (f z.val * ·) (KLR.Corner.val_mul_E E)⟩

/-- The reflected red map: add a red strand on the left of a red-ordered diagram of `T̃^λ`
(Webster, arXiv:1309.3796v3, before Proposition 4.39). -/
def prependRedStendhal : StendhalAlgebra k Q Λ₀ ν →ₙₐ[k] StendhalAlgebra k Q Λ ν where
  toFun z := ⟨prependRedValue Q Λ ν z.val, prependRedValue_corner Q Λ ν z⟩
  map_zero' := Subtype.ext (map_zero (prependRedValue Q Λ ν))
  map_add' x y := Subtype.ext (map_add (prependRedValue Q Λ ν) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (prependRedValue Q Λ ν) x.val y.val)
  map_smul' c z := Subtype.ext (prependRedValue_smul Q Λ ν c z.val)

theorem prependRedStendhal_e (s : Seq μ) (hs : IsRedOrdered s) :
    prependRedStendhal Q Λ ν (StendhalAlgebra.e s hs) =
      StendhalAlgebra.e (prependRedLoading s) ((prependRedLoading_ordered_iff s).2 hs) :=
  Subtype.ext (prependRedValue_e Q Λ ν s)

/-- Adding a red strand on the left preserves degrees. -/
theorem prependRedStendhal_mem_grade (G : GradingDatum (stendhalQ Q Λ)) {d : ℤ}
    {z : StendhalAlgebra k Q Λ₀ ν} (hz : z ∈ stendhalGrade (restrictFirstRedGrading Q Λ G) ν d) :
    prependRedStendhal Q Λ ν z ∈ stendhalGrade G ν d :=
  prependRedAllOrders_mem_grade Q Λ ν G hz

end Algebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Induction

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin (ℓ + 1) → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)

local notation "src" => stendhalGrade (restrictFirstRedGrading Q Λ G) ν
local notation "dst" => stendhalGrade G ν
local notation "T" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "T'" => StendhalAlgebra k Q Λ ν
local notation "φ" => prependRedStendhal Q Λ ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
local notation "cornerGr" => Graded.submodule dst (lIdeal (φ 1))

private def tildeLeftRedProjective : GProj dst :=
  GProj.ofIdempotent (φ 1) (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))
    (prependRedStendhal_mem_grade Q Λ ν G SetLike.GradedOne.one_mem)

private local instance tildeLeftRedFinite : Module.Finite T' Mc :=
  Module.Finite.of_surjective (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T')))
    fun z => ⟨z, Subtype.ext z.property⟩

private local instance tildeLeftRedProjectiveModule : Module.Projective T' Mc :=
  Module.Projective.of_split (leftIdeal (φ 1)).subtype
    (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))) (leftIdealProj_comp_subtype _)

private theorem tildeLeftRedScalarTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeLeftRedDecomposition : DirectSum.Decomposition cornerGr :=
  (tildeLeftRedProjective G ν).decomposition

private local instance tildeLeftRedOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private theorem tildeLeftRedRightAction_mem {d n : ℤ} {m : Mc} {a : T}
    (hm : m ∈ cornerGr d) (ha : a ∈ src n) : op a • m ∈ cornerGr (d + n) :=
  SetLike.GradedMul.mul_mem (A := dst) hm (prependRedStendhal_mem_grade Q Λ ν G ha)

/-- The reflected red induction functor `Ĩ_λ^*` of graded projective `T̃^λ`-modules (Webster,
arXiv:1309.3796v3, before Proposition 4.39). -/
def tildeLeftRedIndProj (P : GProj src) : GProj dst :=
  @balancedIndGProj k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftRedScalarTower ν) _ _
    (tildeLeftRedOpTower ν) _ _ cornerGr (tildeLeftRedProjective G ν).decomposition
    (tildeLeftRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeLeftRedRightAction_mem G ν) P

/-- The map of `Ĩ_λ^*` on graded projective Grothendieck groups of `T̃^λ`. -/
def tildeLeftRedIndK0 : K0 src →ₗ[LaurentPolynomial ℤ] K0 dst :=
  @balancedIndK0 k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftRedScalarTower ν) _ _
    (tildeLeftRedOpTower ν) _ _ cornerGr (tildeLeftRedProjective G ν).decomposition
    (tildeLeftRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeLeftRedRightAction_mem G ν)

@[simp] theorem tildeLeftRedIndK0_of (P : GProj src) :
    tildeLeftRedIndK0 G ν (K0.of P) = K0.of (tildeLeftRedIndProj G ν P) :=
  @balancedIndK0_of k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeLeftRedScalarTower ν) _ _
    (tildeLeftRedOpTower ν) _ _ cornerGr (tildeLeftRedProjective G ν).decomposition
    (tildeLeftRedProjective G ν).gradedSMul (fun _ _ _ _ => tildeLeftRedRightAction_mem G ν) P

end Induction

section Principal

variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin (ℓ + 1) → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)

local notation "src" => stendhalGrade (restrictFirstRedGrading Q Λ G) ν
local notation "dst" => stendhalGrade G ν
local notation "T" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "T'" => StendhalAlgebra k Q Λ ν
local notation "φ" => prependRedStendhal Q Λ ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')

private local instance tildeLeftRedPrincipalTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeLeftRedPrincipalOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private def tildeLeftRedIndMul (e : T) : BalancedTensor k T' T Mc (leftIdeal e) →ₗ[T'] T' :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T' T Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem tildeLeftRedIndMul_tmul (e : T) (b : Mc) (x : leftIdeal e) :
    tildeLeftRedIndMul (Q := Q) (Λ := Λ) ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

private def tildeLeftRedIndPrincipalEquiv {e : T} (he : IsIdempotentElem e) :
    BalancedTensor k T' T Mc (leftIdeal e) ≃ₗ[T'] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (tildeLeftRedIndMul (Q := Q) (Λ := Λ) ν e).codRestrict (leftIdeal (φ e)) fun t => by
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

/-- `Ĩ_λ^*` sends a degree-zero principal projective of `T̃^λ` to the one at the idempotent
with the red strand added on the left. -/
theorem tildeLeftRedIndK0_ofIdempotent {e : T} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    tildeLeftRedIndK0 G ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dst) (φ e) (he.map φ)
        (prependRedStendhal_mem_grade Q Λ ν G he0)) := by
  rw [tildeLeftRedIndK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (tildeLeftRedIndPrincipalEquiv (Q := Q) (Λ := Λ) ν he) ?_
  intro d y hy
  change tildeLeftRedIndMul (Q := Q) (Λ := Λ) ν e y ∈ dst d
  apply balancedGrading_map_mem dst
    ((tildeLeftRedIndMul (Q := Q) (Λ := Λ) ν e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, tildeLeftRedIndMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dst) hz (prependRedStendhal_mem_grade Q Λ ν G hx)

end Principal

namespace FirstWeight

open QuantumGroup KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

section Words

variable {I : Type*}

theorem TensorWord.content_prependRed_toMultiset {n : ℕ} (w : TensorWord I n) :
    w.prependRed.content.toMultiset = w.content.toMultiset := by
  rw [w.content_prependRed]

variable {ℓ : ℕ}

/-- The loading of `λ₀ w` is the loading of `w` with a red strand added on the left. -/
theorem TensorWord.prependRedLoading_loading (w : TensorWord I ℓ) :
    prependRedLoading w.loading =
      Seq.cast (congrArg (stendhalWeight (ℓ + 1)) w.content_prependRed_toMultiset)
        w.prependRed.loading := by
  rw [← w.ofList_prependRed]
  apply Subtype.ext
  rfl

end Words

section Classes

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

local notation "LP" => LaurentPolynomial ℤ
local notation "D" => C.toLusztig
local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private abbrev invLPLR := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance instRingHomInvPairInvLPLeftRed :
    RingHomInvPair invLPLR.toRingHom invLPLR.toRingHom :=
  RingHomInvPair.of_ringEquiv invLPLR
local instance instNeZeroXTildeLeftRed : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩

variable (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Λ₀" => (Λ ∘ Fin.succ)
local notation "fam" Λ' => fun β : Multiset I => K0 (stendhalGrade (moduleGrading Λ') β)

omit [DecidableEq I] in
theorem restrictFirstRedGrading_moduleGrading :
    restrictFirstRedGrading Q Λ (moduleGrading Λ) = moduleGrading Λ₀ := by
  unfold restrictFirstRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

private def tildeLeftRedIndAt (G₀ : GradingDatum (stendhalQ Q Λ₀))
    (h : restrictFirstRedGrading Q Λ (moduleGrading Λ) = G₀) (β : Multiset I) :
    K0 (stendhalGrade G₀ β) →ₗ[LP] K0 (stendhalGrade (moduleGrading Λ) β) :=
  h ▸ tildeLeftRedIndK0 (moduleGrading Λ) β

private theorem tildeLeftRedIndAt_e (G₀ : GradingDatum (stendhalQ Q Λ₀))
    (h : restrictFirstRedGrading Q Λ (moduleGrading Λ) = G₀) {β : Multiset I}
    (s : Seq (stendhalWeight ℓ β)) (hs : IsRedOrdered s) (he he0 he' he0') :
    tildeLeftRedIndAt C hQ Λ G₀ h β (K0.of (GProj.ofIdempotent
      (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ₀) s hs) he he0)) =
    K0.of (GProj.ofIdempotent (StendhalAlgebra.e (prependRedLoading s)
      ((prependRedLoading_ordered_iff s).2 hs)) he' he0') := by
  subst h
  exact (tildeLeftRedIndK0_ofIdempotent _ β he he0).trans
    (K0.of_ofIdempotent_congr (prependRedStendhal_e Q Λ β s hs) _ _ _ _)

/-- `Ĩ_{λ₀}^*` on the sum over all black contents. -/
def totalTildeLeftRedInd :
    DirectSum (Multiset I) (fam Λ₀) →ₗ[LP] DirectSum (Multiset I) (fam Λ) :=
  DirectSum.toModule _ _ _ fun β => DirectSum.lof LP _ (fam Λ) β ∘ₗ
    tildeLeftRedIndAt C hQ Λ _ (restrictFirstRedGrading_moduleGrading C hQ Λ) β

private theorem lof_e_cast_leftRed {δ δ' : Multiset I} (h : δ = δ')
    (s : Seq (stendhalWeight (ℓ + 1) δ)) (hs : IsRedOrdered s)
    (hs' : IsRedOrdered (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h) s)) (he he' he0 he0') :
    DirectSum.lof LP _ (fam Λ) δ (K0.of (GProj.ofIdempotent (StendhalAlgebra.e (k := k) (Q := Q)
      (Λ := Λ) s hs) he he0)) =
    DirectSum.lof LP _ (fam Λ) δ' (K0.of (GProj.ofIdempotent
      (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) _ hs') he' he0')) := by
  subst h
  rfl

/-- **`Ĩ_{λ₀}^* [P̃_w] = [P̃_{λ₀ w}]`** (Webster, arXiv:1309.3796v3, Proposition 4.39,
(4.40)): inducing along the left red strand adds the red strand on the left of the word. -/
theorem totalTildeLeftRedInd_tildeClass (w : TensorWord I ℓ) :
    totalTildeLeftRedInd C hQ Λ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
        (tildeClass C hQ Λ₀ w)) =
      DirectSum.lof LP _ (fam Λ) w.prependRed.content.toMultiset
        (tildeClass C hQ Λ w.prependRed) := by
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [h, map_zero])
  apply tildeK0_smul_injective C hQ Λ hn
  dsimp only
  rw [← map_smul, lof_tildeClass_factorial, ← w.blackBlocks_prependRed,
    lof_tildeClass_factorial, totalTildeLeftRedInd, DirectSum.toModule_lof, LinearMap.comp_apply]
  have hs := (prependRedLoading_ordered_iff w.loading).2 w.blocks_redOrdered
  refine (congrArg (DirectSum.lof LP _ (fam Λ) _) (tildeLeftRedIndAt_e C hQ Λ _ _ w.loading
    w.blocks_redOrdered _ _ (stendhal_e_idem Λ _ _ _) (e_mem_stendhalGrade _ _ _ _))).trans ?_
  refine Eq.trans ?_ (lof_e_cast_leftRed C hQ Λ w.content_prependRed_toMultiset
    w.prependRed.loading w.prependRed.blocks_redOrdered
    (by rw [← w.prependRedLoading_loading]; exact hs) _
    (stendhal_e_idem Λ _ _ _) _ (e_mem_stendhalGrade _ _ _ _)).symm
  refine congrArg _ (K0.of_ofIdempotent_congr ?_ _ _ _ _)
  congr 1
  exact w.prependRedLoading_loading

variable {wt : Fin (ℓ + 1) → Dom R}

local notation "wt₀" => fun j : Fin ℓ => wt (Fin.succ j)

include hR in
/-- **Compatibility (4.40) of Proposition 4.39 with the reflected red induction**
(Webster, arXiv:1309.3796v3): semilinear maps `K₀(T̃^λ) → U^{-,ℤ} ⊗ V^ℤ_λ` sending every
`[P̃_w]` to `p̃_w`, for the labels `λ = (λ_1, …, λ_ℓ)` and `(λ₀, λ)`, intertwine `Ĩ_{λ₀}^*`
with `u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_{λ₀} ⊗ w)`. -/
theorem map_totalTildeLeftRedInd [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {σ : LP →+* LP}
    (f₀ : DirectSum (Multiset I) (fam Λ₀) →ₛₗ[σ] negIntegralTensor C wt₀)
    (f : DirectSum (Multiset I) (fam Λ) →ₛₗ[σ] negIntegralTensor C wt)
    (hw₀ : ∀ w : TensorWord I ℓ, (f₀ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
      (tildeClass C hQ Λ₀ w)) : NegTensor D wt₀) = negWordVector D w wt₀)
    (hw : ∀ w : TensorWord I (ℓ + 1), (f (DirectSum.lof LP _ (fam Λ) w.content.toMultiset
      (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt)
    (x : DirectSum (Multiset I) (fam Λ₀)) :
    (f (totalTildeLeftRedInd C hQ Λ x) : NegTensor D wt) =
      negTensorPrepend D wt (f₀ x : NegTensor D wt₀) := by
  have hx : x ∈ Submodule.span LP (Set.range fun w : TensorWord I ℓ =>
      DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset (tildeClass C hQ Λ₀ w)) := by
    rw [span_lof_tildeClass C hQ hR Λ₀ hρ (fun r i => hwt _ i)]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [totalTildeLeftRedInd_tildeClass, hw, hw₀, negWordVector_prependRed]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f₀.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      negTensor_laurent_smul, negTensor_laurent_smul, map_smul, hx]

include hR in
/-- **Webster, arXiv:1309.3796v3, Proposition 4.39 with the compatibility (4.40) for
`Ĩ_λ^*`**: the isomorphisms `K₀(T̃^λ) ≅ U^{-,ℤ} ⊗ V^ℤ_λ`, `[P̃_w] ↦ p̃_w`, for `λ` and for
`(λ₀, λ)` intertwine `Ĩ_{λ₀}^*` with `u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_{λ₀} ⊗ w)`. Same route
hypothesis as `exists_negIntegralTensorEquiv`. -/
theorem exists_negIntegralTensorEquiv_leftRed [Finite I]
    (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ (e₀ : DirectSum (Multiset I) (fam Λ₀) ≃ₛₗ[invLPLR.toRingHom] negIntegralTensor C wt₀)
      (e : DirectSum (Multiset I) (fam Λ) ≃ₛₗ[invLPLR.toRingHom] negIntegralTensor C wt),
      (∀ w : TensorWord I ℓ, (e₀ (DirectSum.lof LP _ (fam Λ₀) w.content.toMultiset
        (tildeClass C hQ Λ₀ w)) : NegTensor D wt₀) = negWordVector D w wt₀) ∧
      (∀ w : TensorWord I (ℓ + 1), (e (DirectSum.lof LP _ (fam Λ) w.content.toMultiset
        (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt) ∧
      ∀ x, (e (totalTildeLeftRedInd C hQ Λ x) : NegTensor D wt) =
        negTensorPrepend D wt (e₀ x : NegTensor D wt₀) := by
  obtain ⟨e₀, he₀⟩ := exists_negIntegralTensorEquiv (wt := wt₀) hQ hR hρ Λ₀ (fun r i => hwt _ i)
  obtain ⟨e, he⟩ := exists_negIntegralTensorEquiv hQ hR hρ Λ hwt
  exact ⟨e₀, e, he₀, he,
    map_totalTildeLeftRedInd C hQ hR Λ hρ hwt e₀.toLinearMap e.toLinearMap he₀ he⟩

end Classes

end FirstWeight

end Categorification.Stendhal
