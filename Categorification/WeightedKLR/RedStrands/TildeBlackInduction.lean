/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NegativeTensorLattice
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Black induction on `T̃^λ` and the operator `F̃_i`

Webster, arXiv:1309.3796v3, Proposition 4.39, compatibility (4.40) for the black induction
functors. Appending a black strand on the right gives a non-unital map
`T̃^λ_ν → T̃^λ_{ν+i}` (`appendBlackStendhal`); the induction functor `F̃_i` along it is
extension of scalars by the left ideal of the image of the unit, exactly as for `T^λ`
(Webster, §4.6 after Theorem 4.31).

## Main definitions and results

* `tildeBlackIndK0`, `tildeLower` : the map induced by `F̃_i` on `K₀(T̃^λ)`.
* `tildeLower_tildeClass` : `F̃_i [P̃_w] = [P̃_{w i}]`, appending a black block of size one.
* `map_tildeLower` : any map sending `[P̃_w] ↦ p̃_w` intertwines `F̃_i` on `K₀(T̃^λ)` with the
  operator `F̃_i (u ⊗ w) = F_i u ⊗ K_{-ĩ} w + u ⊗ F_i w` of `U⁻ ⊗ V_λ`; in particular the
  isomorphism of Proposition 4.39 (`exists_negIntegralTensorEquiv`) does.
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
local notation "φ" => appendBlackStendhal Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
local notation "cornerGr" => Graded.submodule dst (lIdeal (φ 1))

/-- Appending a straight black strand preserves the degree of a red-ordered diagram. -/
theorem appendBlackStendhal_mem_grade {d : ℤ} {z : T} (hz : z ∈ src d) : φ z ∈ dst d := by
  change (φ z).val ∈ allOrdersGrade G νᵢ d
  obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp (show z.val ∈ allOrdersGrade G ν d from hz)
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν a = z.val at he
  rw [appendBlackStendhal_val, ← he, appendBlackAllOrders_ofKLR_val]
  apply Graded.mem_map_of_mem
  have h1 : (1 : KLRAlgebra k (stendhalQ Q Λ) (Singleton.singleton (Sum.inl i))) ∈ G.grade _ 0 :=
    SetLike.GradedOne.one_mem
  exact G.castKLR_mem_grade _ (by simpa only [add_zero] using G.concat_tmul_mem_grade ha h1)

private def tildeBlackProjective : GProj dst :=
  GProj.ofIdempotent (φ 1) (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))
    (appendBlackStendhal_mem_grade G i ν SetLike.GradedOne.one_mem)

private local instance tildeBlackFinite : Module.Finite T' Mc :=
  Module.Finite.of_surjective (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T')))
    fun z => ⟨z, Subtype.ext z.property⟩

private local instance tildeBlackProjectiveModule : Module.Projective T' Mc :=
  Module.Projective.of_split (leftIdeal (φ 1)).subtype
    (leftIdealProj (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))) (leftIdealProj_comp_subtype _)

private theorem tildeBlackScalarTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildeBlackDecomposition : DirectSum.Decomposition cornerGr :=
  (tildeBlackProjective G i ν).decomposition

private local instance tildeBlackOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private theorem tildeBlackRightAction_mem {d n : ℤ} {m : Mc} {a : T}
    (hm : m ∈ cornerGr d) (ha : a ∈ src n) : op a • m ∈ cornerGr (d + n) :=
  SetLike.GradedMul.mul_mem (A := dst) hm (appendBlackStendhal_mem_grade G i ν ha)

/-- The induction functor `F̃_i` of `T̃^λ`-modules on graded projectives: extension of scalars
along the right black strand map (Webster, arXiv:1309.3796v3, Proposition 4.39). -/
def tildeBlackIndProj (P : GProj src) : GProj dst :=
  @balancedIndGProj k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeBlackScalarTower i ν) _ _ (tildeBlackOpTower i ν) _ _
    cornerGr (tildeBlackProjective G i ν).decomposition (tildeBlackProjective G i ν).gradedSMul
    (fun _ _ _ _ => tildeBlackRightAction_mem G i ν) P

/-- The map of `F̃_i` on graded projective Grothendieck groups of `T̃^λ` (Webster,
arXiv:1309.3796v3, Proposition 4.39). -/
def tildeBlackIndK0 : K0 src →ₗ[LaurentPolynomial ℤ] K0 dst :=
  @balancedIndK0 k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeBlackScalarTower i ν) _ _ (tildeBlackOpTower i ν) _ _
    cornerGr (tildeBlackProjective G i ν).decomposition (tildeBlackProjective G i ν).gradedSMul
    (fun _ _ _ _ => tildeBlackRightAction_mem G i ν)

@[simp] theorem tildeBlackIndK0_of (P : GProj src) :
    tildeBlackIndK0 G i ν (K0.of P) = K0.of (tildeBlackIndProj G i ν P) :=
  @balancedIndK0_of k _ T' _ _ dst T _ _ src _ Mc _ _ _ (tildeBlackScalarTower i ν) _ _ (tildeBlackOpTower i ν) _ _
    cornerGr (tildeBlackProjective G i ν).decomposition (tildeBlackProjective G i ν).gradedSMul
    (fun _ _ _ _ => tildeBlackRightAction_mem G i ν) P

local notation "K" => fun β : Multiset I => K0 (stendhalGrade G β)

/-- `F̃_i` on the sum of the projective Grothendieck groups of all black contents. -/
def tildeLower : (⨁ β : Multiset I, K β) →ₗ[LaurentPolynomial ℤ] ⨁ β : Multiset I, K β :=
  DirectSum.toModule _ _ _ fun β =>
    DirectSum.lof _ _ _ ((Singleton.singleton i : Multiset I) + β) ∘ₗ tildeBlackIndK0 G i β

@[simp] theorem tildeLower_lof (x : K ν) :
    tildeLower G i (DirectSum.lof (LaurentPolynomial ℤ) _ K ν x) =
      DirectSum.lof (LaurentPolynomial ℤ) _ K νᵢ (tildeBlackIndK0 G i ν x) :=
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
local notation "φ" => appendBlackStendhal Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')

private local instance tildePrincipalTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance tildePrincipalOpTower : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private def tildeIndMul (e : T) : BalancedTensor k T' T Mc (leftIdeal e) →ₗ[T'] T' :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T' T Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem tildeIndMul_tmul (e : T) (b : Mc) (x : leftIdeal e) :
    tildeIndMul (Q := Q) (Λ := Λ) i ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

private def tildeIndPrincipalEquiv {e : T} (he : IsIdempotentElem e) :
    BalancedTensor k T' T Mc (leftIdeal e) ≃ₗ[T'] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (tildeIndMul (Q := Q) (Λ := Λ) i ν e).codRestrict (leftIdeal (φ e)) fun t => by
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

/-- `F̃_i` sends a degree-zero principal projective of `T̃^λ` to the one at the appended
idempotent. -/
theorem tildeBlackIndK0_ofIdempotent {e : T} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    tildeBlackIndK0 G i ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dst) (φ e) (he.map φ)
        (appendBlackStendhal_mem_grade G i ν he0)) := by
  rw [tildeBlackIndK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (tildeIndPrincipalEquiv (Q := Q) (Λ := Λ) i ν he) ?_
  intro d y hy
  change tildeIndMul (Q := Q) (Λ := Λ) i ν e y ∈ dst d
  apply balancedGrading_map_mem dst ((tildeIndMul (Q := Q) (Λ := Λ) i ν e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, tildeIndMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dst) hz (appendBlackStendhal_mem_grade G i ν hx)

end Principal

namespace FirstWeight

open QuantumGroup KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

section Words

variable {I : Type*} {ℓ : ℕ} [DecidableEq I]

omit [DecidableEq I] in
theorem TensorWord.content_black_one (w : TensorWord I ℓ) (i : I) :
    (w.black i 1).content.toMultiset =
      (Singleton.singleton i : Multiset I) + w.content.toMultiset := by
  simp [TensorWord.content, Finsupp.toMultiset_add, add_comm]

omit [DecidableEq I] in
/-- The loading of `w i` is the loading of `w` with a black strand `i` appended. -/
theorem TensorWord.appendBlackLoading_loading (w : TensorWord I ℓ) (i : I) :
    appendBlackLoading i _ w.loading =
      Seq.cast (congrArg (stendhalWeight ℓ) (w.content_black_one i)) (w.black i 1).loading := by
  have hn : (expandDiv w.blocks).length = Multiset.card (stendhalWeight ℓ w.content.toMultiset) := by
    rw [← Multiset.coe_card, w.blocks_weight]
  have he : expandDiv (w.black i 1).blocks = expandDiv w.blocks ++ [.inl i] := by
    rw [TensorWord.blocks, expandDiv_append]
    simp [expandDiv]
  apply Subtype.ext
  funext a
  change (appendBlackLoading i _ w.loading).lbl a = (w.black i 1).loading.lbl (Fin.cast _ a)
  change _ = (expandDiv (w.black i 1).blocks)[(a : ℕ)]'_
  simp only [getElem_congr_coll he]
  by_cases ha : a.val < Multiset.card (stendhalWeight ℓ w.content.toMultiset)
  · rw [appendBlackLoading_lbl_of_lt i _ _ a ha, TensorWord.loading, Seq.ofList_lbl,
      List.getElem_append_left (by omega)]
  · have h2 := a.2
    have hc : Multiset.card (stendhalWeight ℓ ((Singleton.singleton i : Multiset I) +
        w.content.toMultiset)) = Multiset.card (stendhalWeight ℓ w.content.toMultiset) + 1 := by
      simp [stendhalWeight]
    have ha' : a.val = Multiset.card (stendhalWeight ℓ w.content.toMultiset) := by omega
    rw [appendBlackLoading_lbl_of_eq i _ _ a ha', List.getElem_append_right (by omega)]
    simp [hn, ha']

end Words

section Classes

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

local notation "LP" => LaurentPolynomial ℤ
local notation "D" => C.toLusztig

private abbrev invLPB := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance instRingHomInvPairInvLPBlack : RingHomInvPair invLPB.toRingHom invLPB.toRingHom :=
  RingHomInvPair.of_ringEquiv invLPB
local instance instNeZeroXTildeBlack : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩
local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

variable (Λ : Fin ℓ → I →₀ ℕ)

local notation "fam" => fun β : Multiset I => K0 (stendhalGrade (moduleGrading Λ) β)

omit [DecidableEq I] in
theorem moduleGrading_dot :
    ∀ a, (moduleGrading Λ).degX a = (affineCoverCartan C ℓ).dot a a := by
  rintro (i | r)
  · rfl
  · exact (CartanDatum.ofGraph_dot_self (⊥ : SimpleGraph (Fin ℓ)) r).symm

theorem tildeK0_smul_injective {r : LP} (hr : r ≠ 0) :
    Function.Injective ((r • ·) : DirectSum (Multiset I) fam → _) := by
  intro x y h
  apply DFinsupp.ext
  intro ν
  let := hasGdim_stendhalGrade (moduleGrading Λ) ν (stendhalQ_symm Q Λ hQ.klrSymm)
    (moduleGrading_degX_pos C hQ Λ)
  exact smul_right_injective (K0 (stendhalGrade (moduleGrading Λ) ν)) hr (DFinsupp.ext_iff.mp h ν)

theorem tildeProjection_e (ν : Multiset I) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) :
    tildeProjection (k := k) (Q := Q) Λ ν (KLRAlgebra.e s) = StendhalAlgebra.e s hs := by
  classical
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν = _
  rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  exact ite_eq_left_of_eq_true _ _ (eq_true hs)

theorem stendhal_e_idem (ν : Multiset I) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) : IsIdempotentElem (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) s hs) := by
  rw [← tildeProjection_e Λ ν s hs]
  exact (show IsIdempotentElem (KLRAlgebra.e s) from e_mul_self s).map _

private theorem lof_e_cast {δ δ' : Multiset I} (h : δ = δ') (s : Seq (stendhalWeight ℓ δ))
    (hs : IsRedOrdered s) (hs' : IsRedOrdered (Seq.cast (congrArg (stendhalWeight ℓ) h) s))
    (he he' he0 he0') :
    DirectSum.lof LP _ fam δ (K0.of (GProj.ofIdempotent (StendhalAlgebra.e (k := k) (Q := Q)
      (Λ := Λ) s hs) he he0)) =
    DirectSum.lof LP _ fam δ' (K0.of (GProj.ofIdempotent
      (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) _ hs') he' he0')) := by
  subst h
  rfl

theorem lof_tildeClass_factorial (w : TensorWord I ℓ) :
    divQFact2 C w.blackBlocks • DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w) =
      DirectSum.lof LP _ fam w.content.toMultiset (K0.of (GProj.ofIdempotent
        (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) w.loading w.blocks_redOrdered)
        (stendhal_e_idem Λ _ _ w.blocks_redOrdered) (e_mem_stendhalGrade _ _ _ _))) := by
  rw [← map_smul, tildeClass, ← tildeWordClass_factorial Λ C (moduleGrading Λ) _
    (moduleGrading_dot C hQ Λ)]
  congr 1
  exact K0.of_ofIdempotent_congr (tildeProjection_e Λ _ _ w.blocks_redOrdered) _ _ _ _

/-- **`F̃_i [P̃_w] = [P̃_{w i}]`** (Webster, arXiv:1309.3796v3, Proposition 4.39, (4.40)):
inducing along the right black strand appends a black block of size one to the word. -/
theorem tildeLower_tildeClass (w : TensorWord I ℓ) (i : I) :
    tildeLower (moduleGrading Λ) i
        (DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w)) =
      DirectSum.lof LP _ fam (w.black i 1).content.toMultiset (tildeClass C hQ Λ (w.black i 1)) := by
  have hf : divQFact2 C (w.black i 1).blackBlocks = divQFact2 C w.blackBlocks := by
    rw [TensorWord.blackBlocks, divQFact2_append]
    simp [divQFact2]
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [h, map_zero])
  apply tildeK0_smul_injective C hQ Λ hn
  dsimp only
  rw [← map_smul, lof_tildeClass_factorial, ← hf, lof_tildeClass_factorial, tildeLower_lof]
  erw [tildeBlackIndK0_ofIdempotent]
  have hs := appendBlackLoading_ordered i _ w.loading w.blocks_redOrdered
  refine Eq.trans ?_ (lof_e_cast C hQ Λ (w.content_black_one i) (w.black i 1).loading
    (w.black i 1).blocks_redOrdered (by rw [← w.appendBlackLoading_loading i]; exact hs) _
    (stendhal_e_idem Λ _ _ _) _ (e_mem_stendhalGrade _ _ _ _)).symm
  refine congrArg _ (K0.of_ofIdempotent_congr ?_ _ _ _ _)
  refine (appendBlackStendhal_e Q Λ i _ w.loading w.blocks_redOrdered).trans ?_
  congr 1
  exact w.appendBlackLoading_loading i

variable {wt : Fin ℓ → Dom R}

include hR in
theorem span_lof_tildeClass [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    Submodule.span LP (Set.range fun w : TensorWord I ℓ =>
      DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | of β y =>
    change DirectSum.lof LP _ fam β y ∈ _
    have hy : y ∈ Submodule.span LP (Set.range (tildeClassAt C hQ Λ β)) := by
      rw [span_tildeClassAt C hQ hR Λ wt hρ hwt β]; trivial
    have h := Submodule.mem_map_of_mem (f := DirectSum.lof LP _ fam β) hy
    rw [Submodule.map_span, ← Set.range_comp] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩

include hR in
/-- **Compatibility (4.40) of Proposition 4.39 with the lowering functors** (Webster,
arXiv:1309.3796v3): a semilinear map `K₀(T̃^λ) → U^{-,ℤ} ⊗ V^ℤ_λ` sending every `[P̃_w]` to
`p̃_w` intertwines the induction functor `F̃_i` with the operator
`F̃_i (u ⊗ w) = F_i u ⊗ K_{-ĩ} w + u ⊗ F_i w`. -/
theorem map_tildeLower [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {σ : LP →+* LP}
    (f : DirectSum (Multiset I) fam →ₛₗ[σ] negIntegralTensor C wt)
    (hw : ∀ w : TensorWord I ℓ, (f (DirectSum.lof LP _ fam w.content.toMultiset
      (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt)
    (i : I) (x : DirectSum (Multiset I) fam) :
    (f (tildeLower (moduleGrading Λ) i x) : NegTensor D wt) = negTensorF D wt i (f x) := by
  have hx : x ∈ Submodule.span LP (Set.range fun w : TensorWord I ℓ =>
      DirectSum.lof LP _ fam w.content.toMultiset (tildeClass C hQ Λ w)) := by
    rw [span_lof_tildeClass C hQ hR Λ hρ hwt]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl⟩ := hz
    rw [tildeLower_tildeClass, hw, hw]
    change negTensorDivF D wt i 1 _ = _
    simp [negTensorDivF, qDivPow, qFactorial, qInt]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      negTensor_laurent_smul, negTensor_laurent_smul, map_smul, hx]

include hR in
/-- **Webster, arXiv:1309.3796v3, Proposition 4.39 with the first compatibility of (4.40)**:
the isomorphism `K₀(T̃^λ) ≅ U^{-,ℤ} ⊗ V^ℤ_λ`, `[P̃_w] ↦ p̃_w`, intertwines the induction
functor `F̃_i` with the operator `F̃_i` of `U⁻ ⊗ V_λ`. Same route hypothesis as
`exists_negIntegralTensorEquiv`. -/
theorem exists_negIntegralTensorEquiv_lower [Finite I]
    (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ e : DirectSum (Multiset I) fam ≃ₛₗ[invLPB.toRingHom] negIntegralTensor C wt,
      (∀ w : TensorWord I ℓ, (e (DirectSum.lof LP _ fam w.content.toMultiset
        (tildeClass C hQ Λ w)) : NegTensor D wt) = negWordVector D w wt) ∧
      ∀ (i : I) (x : DirectSum (Multiset I) fam),
        (e (tildeLower (moduleGrading Λ) i x) : NegTensor D wt) = negTensorF D wt i (e x) := by
  obtain ⟨e, he⟩ := exists_negIntegralTensorEquiv hQ hR hρ Λ hwt
  exact ⟨e, he, map_tildeLower C hQ hR Λ hρ hwt e.toLinearMap he⟩

end Classes

end FirstWeight

end Categorification.Stendhal
