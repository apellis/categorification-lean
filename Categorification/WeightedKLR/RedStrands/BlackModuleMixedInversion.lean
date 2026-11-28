/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedMate
import Categorification.WeightedKLR.RedStrands.BlackMixedCorner
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossTransportQ
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedSigma
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.Algebra.InductionAlongTensorRepresented

/-!
# Mixed inversion `Eᵢ Fⱼ ≅ Fⱼ Eᵢ` on modules over the tensor product algebras

For distinct colours `i ≠ j`, the mate through `Fᵢ ⊣ Eᵢ` of the induction crossing
`indCrossOfEq` is invertible on right `T^λ`-modules (`blackModuleMixedInversion`). This is the
module form of the relation `E_i F_j ≅ F_j E_i` of Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 4.31, i.e. Brundan's mixed inversion
(Brundan, arXiv:1501.00350v1, (1.7)) for the black-strand induction functors. It discharges the
hypothesis `BlackModuleMixedInversion` of `blackRouqFamily_mixedInversion_of`
(`blackRouqFamily_mixedInversion`).

Proof. By `indCrossOfEq_mixedMate` the mate is the Beck–Chevalley map
`blackMixedBeckChevalley` of the restriction crossing through `Fⱼ ⊣ Eⱼ`.

* Both sides are tensoring with bimodules (`InductionAlong.isTensorRepresented_functor`,
  `InductionAlong.isTensorRepresented_resFunctor`), so it suffices that the component at the
  regular module is bijective (`TensorRepresented.isIso_of_bijective_app_regular`).
* On the regular module the component sends `z ⊗ x` to `−φ(z) χ (x ⊗ 1)`, where `χ` is the
  mixed crossing (`blackMixedBeckChevalley_tmul`), so its image is the image of the Mackey map
  `mixedBlackMap`, which is onto the corner (Webster, Lemma 4.35, `exists_mixedBlackMap_eq`):
  `blackMixedBeckChevalley_regular_surjective`.
* Webster's Theorem 4.31 isomorphism `clBlackModuleCrossEquivQ` identifies the target with the
  source abstractly (`nonempty_blackMixedRegularEquiv`); the source is a finitely generated
  module over the finite-dimensional algebra `T^λ_{j+μ}` (`tensorProductAlgebra_finite`), hence
  Noetherian (`isNoetherian_blackMixedRegular`), and a surjection onto a module isomorphic to a
  Noetherian source is injective (`injective_of_surjective_of_linearEquiv`).

The hypotheses are those of `clBlackModuleCrossEquivQ`: Theorem 4.30 in the form
`CoverRelsNegligible` with `WFDom`, and exactness of the Rouquier polynomials (`hQ`); no further
route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal
open CategoryTheory MulOpposite InductionAlong KLR QuantumGroup QuantumGroup.UDot StringDiagrams
  TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
universe u
variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

variable (hsym : KLRSymm Q) (i j : I) (μ : Multiset I)
    (h₂ : ({i} : Multiset I) + ({j} + μ) = {j} + ({i} + μ))

local notation "T" => TensorProductAlgebra k Q Λ

/-- The restriction crossing `resCrossOfEq` at the contents `j + (i + μ)` and `i + μ`. -/
def blackMixedResCross :
    blackEOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)) ⋙
      blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ) ⟶
      blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ) :=
  resCrossOfEq Λ hsym i j rfl h₂ rfl rfl

theorem res_eqToHom_val_val {A B C : Type u} [Ring A] [Ring B] [Ring C] {φ₁ φ₂ : A →ₙ+* B}
    (hφ : φ₁ = φ₂) (ψ : C →ₙ+* A) (M : ModuleCat.{u} B)
    (h : (resFunctor.{u, u} φ₁ ⋙ resFunctor.{u, u} ψ).obj M =
      (resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} ψ).obj M)
    (w : Res ψ (Res φ₁ M)) :
    (((eqToHom h).hom w : Res ψ (Res φ₂ M)).val.val : M) = w.val.val := by
  subst hφ
  rfl

theorem blackMixedResCross_val (hij : i ≠ j) (M : ModuleCat.{u} (T ({j} + ({i} + μ)))ᵐᵒᵖ)
    (w : Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ))
      (Res (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ))) M)) :
    let x : Res (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ))
        (Res (appendBlackOpOfEq Q Λ i h₂) M) := ((blackMixedResCross Λ hsym i j μ h₂).app M).hom w
    (x.val.val : M) = -(op (mixedCrossElem (Q := Q) Λ μ j i) • (w.val.val : M)) := by
  intro x
  have hc : blackMixedResCross Λ hsym i j μ h₂ =
      -blackMixedCrossOfEq (i := j) (j := i) hsym (Ne.symm hij) rfl rfl rfl h₂ := by
    simp only [blackMixedResCross, resCrossOfEq, hij, dite_false]
  have hx : x = -(((blackMixedCrossOfEq (i := j) (j := i) hsym (Ne.symm hij)
      rfl rfl rfl h₂).app M).hom w) := by
    simp only [x, hc, NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply]
  rw [hx]
  change -(Res.val (Res.val (((blackMixedCrossOfEq (i := j) (j := i) hsym (Ne.symm hij)
    rfl rfl rfl h₂).app M).hom w))) = _
  congr 1
  rw [blackMixedCrossOfEq, NatTrans.comp_app, ModuleCat.comp_apply]
  rw [eqToHom_app]
  exact res_eqToHom_val_val (appendBlackAtOp_eq (Q := Q) Λ μ j i) _ M _ _

/-- The Beck–Chevalley map `Eᵢ Fⱼ ⟶ Fⱼ Eᵢ` of the mixed restriction crossing through
`Fⱼ ⊣ Eⱼ`; by `indCrossOfEq_mixedMate` it is the mate of the induction crossing in
`BlackModuleMixedInversion`. -/
def blackMixedBeckChevalley :
    blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ) ⋙
      blackFOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ) ⟶
    blackFOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)) ⋙
      blackEOfEq Q Λ i h₂ :=
  ((mateEquiv (blackAdjOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)))
      (blackAdjOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ))).symm
      (TwoSquare.mk _ _ _ _ (blackMixedResCross Λ hsym i j μ h₂))).natTrans

theorem blackMixedBeckChevalley_tmul (hij : i ≠ j) (N : ModuleCat.{u} (T ({i} + μ))ᵐᵒᵖ)
    (z : Corner (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ)))
    (n : Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ)) N) :
    let y : Res (appendBlackOpOfEq Q Λ i h₂) (Ind N (appendBlackOpOfEq Q Λ j
        (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)))) :=
      ((blackMixedBeckChevalley Λ hsym i j μ h₂).app N).hom (Ind.tmul z n)
    y.val = -(appendBlackOpOfEq Q Λ i h₂ z.1 • op (mixedCrossElem (Q := Q) Λ μ j i) •
      Ind.tmul (unitGen _) n.val) := by
  intro y
  have key := blackMixedResCross_val Λ hsym i j μ h₂ hij ((blackFOfEq Q Λ j rfl).obj N)
    (((blackEOfEq Q Λ i rfl).map ((blackAdjOfEq Q Λ j rfl).unit.app N)).hom n)
  simp only [y, blackMixedBeckChevalley, mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Category.id_comp, Functor.comp_obj]
  change appendBlackOpOfEq Q Λ i h₂ z.1 • (Res.val (Res.val
    (((blackMixedResCross Λ hsym i j μ h₂).app _).hom
      (((blackEOfEq Q Λ i rfl).map ((blackAdjOfEq Q Λ j rfl).unit.app N)).hom n)))) = _
  rw [key, smul_neg]
  rfl

/-- Induction along `Fⱼ` into the upper content `j + (i + μ)`. -/
abbrev blackUpperAppend : (T ({i} + μ))ᵐᵒᵖ →ₙ+* (T ({j} + ({i} + μ)))ᵐᵒᵖ :=
  appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ))

set_option hygiene false in
local notation "φu" => blackUpperAppend (Q := Q) Λ i j μ

-- The regular right module of `T^λ_{i+μ}`.
set_option hygiene false in
local notation "Rg" => ModuleCat.of (T ({i} + μ))ᵐᵒᵖ (T ({i} + μ))ᵐᵒᵖ

/-- The induction of the regular module along `blackUpperAppend`. -/
abbrev BlackIndReg : Type u := InductionAlong.Ind (T ({i} + μ))ᵐᵒᵖ (φu)

/-- The induction of the regular module inside the upper algebra. -/
def blackIndRegVal : BlackIndReg (Q := Q) Λ i j μ →ₗ[(T ({j} + ({i} + μ)))ᵐᵒᵖ]
    (T ({j} + ({i} + μ)))ᵐᵒᵖ :=
  Ind.lift (fun c b => c.1 * (φu) b) (fun c c' b => add_mul _ _ _)
    (fun c b b' => by rw [map_add, mul_add])
    (fun c a b => by
      change c.1 * (φu) a * (φu) b = c.1 * (φu) (a * b)
      rw [map_mul, mul_assoc])
    (fun a c b => by
      change a * c.1 * (φu) b = a • (c.1 * (φu) b)
      rw [smul_eq_mul, mul_assoc])

theorem blackIndRegVal_injective : Function.Injective (blackIndRegVal (Q := Q) Λ i j μ) := by
  let g : (T ({j} + ({i} + μ)))ᵐᵒᵖ →+ InductionAlong.Ind (T ({i} + μ))ᵐᵒᵖ (φu) :=
    { toFun := fun x => Ind.tmul ⟨x * (φu) 1, mul_mem_corner _ x 1⟩ 1
      map_zero' := by
        rw [show (⟨0 * (φu) 1, mul_mem_corner _ 0 1⟩ : Corner (φu)) = 0 from
          Subtype.ext (zero_mul _), Ind.zero_tmul]
      map_add' := fun x x' => by
        rw [← Ind.add_tmul]
        congr 1
        exact Subtype.ext (add_mul _ _ _) }
  have hg : ∀ t, g (blackIndRegVal (Q := Q) Λ i j μ t) = t := fun t => by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c b =>
      change Ind.tmul ⟨c.1 * (φu) b * (φu) 1, _⟩ 1 = Ind.tmul c b
      have : (⟨c.1 * (φu) b * (φu) 1, mul_mem_corner _ _ 1⟩ : Corner (φu)) = op b • c :=
        Subtype.ext (by
          change c.1 * (φu) b * (φu) 1 = c.1 * (φu) b
          rw [mul_assoc, ← map_mul, mul_one])
      rw [this, Ind.op_smul_tmul, smul_eq_mul, mul_one]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  exact Function.LeftInverse.injective hg

theorem blackUpperAppend_op (a : T ({i} + μ)) :
    φu (op a) = op (appendBlack Q Λ j ({i} + μ) a) := rfl

theorem blackLowerAppend_op (b : T ({j} + μ)) :
    appendBlackOpOfEq Q Λ i h₂ (op b) = op (appendBlackAt Λ i h₂ b) := by
  rw [← appendBlackAtOp_eq (Q := Q) Λ μ j i]
  rfl

theorem blackMixedBeckChevalley_regular_tmul (hij : i ≠ j)
    (x : CornerTensor.Left (appendBlack Q Λ i μ))
    (y : CornerTensor.Right (appendBlack Q Λ j μ) (AlgHom.id k (T ({j} + μ)))) :
    let zc : Corner (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ)) :=
      ⟨op (y : T ({j} + μ)), by
        change op (y : T ({j} + μ)) * op (appendBlack Q Λ j μ 1) = op (y : T ({j} + μ))
        rw [← op_mul]; exact congrArg op (CornerTensor.right_mem _ _ y)⟩
    let nr : Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ))
        Rg :=
      Res.mk (op (x : T ({i} + μ))) (by
        change op (appendBlack Q Λ i μ 1) * op (x : T ({i} + μ)) = op (x : T ({i} + μ))
        rw [← op_mul]; exact congrArg op (CornerTensor.left_mem _ x))
    let y' : Res (appendBlackOpOfEq Q Λ i h₂) (InductionAlong.Ind (T ({i} + μ))ᵐᵒᵖ
        (φu)) :=
      ((blackMixedBeckChevalley Λ hsym i j μ h₂).app _).hom (-Ind.tmul zc nr)
    unop (blackIndRegVal (Q := Q) Λ i j μ y'.val) =
      mixedBlackMap Λ μ j i hsym hij.symm (BalancedTensor.tmul x y) := by
  intro zc nr y'
  have h := blackMixedBeckChevalley_tmul Λ hsym i j μ h₂ hij _ zc nr
  have hy' : y'.val = -(-(appendBlackOpOfEq Q Λ i h₂ zc.1 •
      op (mixedCrossElem (Q := Q) Λ μ j i) • Ind.tmul (unitGen _) nr.val)) := by
    rw [← h]
    simp only [y', map_neg]
    rfl
  rw [hy', neg_neg, map_smul, map_smul]
  change unop (appendBlackOpOfEq Q Λ i h₂ (op (y : T ({j} + μ))) *
    (op (mixedCrossElem (Q := Q) Λ μ j i) *
      (φu 1 * φu (op (x : T ({i} + μ)))))) =
    appendBlack Q Λ j ({i} + μ) x * mixedBlackCrossing Λ μ j i * appendBlackAt Λ i h₂ y
  rw [blackLowerAppend_op, ← op_one, blackUpperAppend_op, blackUpperAppend_op]
  simp only [unop_mul, unop_op, mixedCrossElem]
  have hx : (x : T ({i} + μ)) * appendBlack Q Λ i μ 1 = x := CornerTensor.left_mem _ x
  have hy : appendBlack Q Λ j μ 1 * (y : T ({j} + μ)) = y := CornerTensor.right_mem _ _ y
  calc _ = appendBlack Q Λ j ({i} + μ) ((x : T ({i} + μ)) * 1 * appendBlack Q Λ i μ 1) *
        mixedBlackCrossing Λ μ j i *
          appendBlackAt Λ i h₂ (appendBlack Q Λ j μ 1 * (y : T ({j} + μ))) := by
        simp only [map_mul]; noncomm_ring
    _ = _ := by rw [mul_one, hx, hy]

theorem blackIndRegVal_unit_mul (t : BlackIndReg (Q := Q) Λ i j μ) :
    let ι := blackIndRegVal (Q := Q) Λ i j μ
    appendBlack Q Λ j ({i} + μ) 1 * unop (ι t) = unop (ι t) := by
  intro ι
  induction t using Ind.induction_on with
  | zero => rw [map_zero, unop_zero, mul_zero]
  | tmul c b =>
    change appendBlack Q Λ j ({i} + μ) 1 * unop (c.1 * φu b) =
      unop (c.1 * φu b)
    rw [unop_mul, ← mul_assoc, show unop (φu b) =
      appendBlack Q Λ j ({i} + μ) (unop b) from rfl, ← map_mul, one_mul]
  | add s t hs ht => rw [map_add, MulOpposite.unop_add, mul_add, hs, ht]

/-- **The Beck–Chevalley map of the mixed restriction crossing is onto on the regular
module** (Webster, arXiv:1309.3796v3, Lemma 4.35, distinct colours). -/
theorem blackMixedBeckChevalley_regular_surjective (hij : i ≠ j) :
    Function.Surjective ((blackMixedBeckChevalley Λ hsym i j μ h₂).app
      Rg).hom := by
  let B := ModuleCat.of (T ({i} + μ))ᵐᵒᵖ (T ({i} + μ))ᵐᵒᵖ
  let ι := blackIndRegVal (Q := Q) Λ i j μ
  let val : ((blackFOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)) ⋙
      blackEOfEq Q Λ i h₂).obj B) → T ({j} + ({i} + μ)) := fun w =>
    unop (ι (w : Res (appendBlackOpOfEq Q Λ i h₂) (InductionAlong.Ind (T ({i} + μ))ᵐᵒᵖ
      (φu))).val)
  have hval : Function.Injective val := fun w w' h =>
    Res.ext (blackIndRegVal_injective Λ i j μ (unop_injective h))
  have key : ∀ t, ∃ s, val (((blackMixedBeckChevalley Λ hsym i j μ h₂).app B).hom s) =
      mixedBlackMap Λ μ j i hsym hij.symm t := fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]; rfl⟩
    | add a d ha hd =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hd
      refine ⟨s + s', ?_⟩
      rw [map_add, map_add, ← hs, ← hs']
      change unop (ι (_ + _)) = _
      rw [map_add]
      rfl
    | tmul x y => exact ⟨_, blackMixedBeckChevalley_regular_tmul Λ hsym i j μ h₂ hij x y⟩
  intro w
  let w' : Res (appendBlackOpOfEq Q Λ i h₂) (InductionAlong.Ind (T ({i} + μ))ᵐᵒᵖ
      (φu)) := w
  have hu : appendBlack Q Λ j ({i} + μ) 1 * val w * appendBlackAt Λ i h₂ 1 = val w := by
    have h2 := congrArg (fun t => unop (ι t)) w'.prop
    simp only [map_smul, smul_eq_mul, unop_mul] at h2
    change unop (ι w'.val) * unop (appendBlackOpOfEq Q Λ i h₂ (op 1)) = _ at h2
    rw [blackLowerAppend_op, unop_op] at h2
    change appendBlack Q Λ j ({i} + μ) 1 * unop (ι w'.val) * appendBlackAt Λ i h₂ 1 =
      unop (ι w'.val)
    rw [blackIndRegVal_unit_mul Λ i j μ, h2]
  obtain ⟨t, ht⟩ := exists_mixedBlackMap_eq Λ μ j i hsym hij.symm (val w) hu
  obtain ⟨s, hs⟩ := key t
  exact ⟨s, hval (hs.trans ht)⟩

theorem nonempty_res_ind_congr {A C D : Type u} [Ring A] [Ring C] [Ring D]
    {ψ₁ ψ₂ : A →ₙ+* D} (h : ψ₁ = ψ₂) (χ : C →ₙ+* D) (N : Type u) [AddCommGroup N]
    [Module A N] :
    Nonempty (Res χ (InductionAlong.Ind N ψ₁) ≃ₗ[C] Res χ (InductionAlong.Ind N ψ₂)) := by
  subst h
  exact ⟨LinearEquiv.refl _ _⟩

theorem nonempty_ind_res_congr {A C D : Type u} [Ring A] [Ring C] [Ring D]
    {φ₁ φ₂ : A →ₙ+* D} (h : φ₁ = φ₂) {ψ₁ ψ₂ : A →ₙ+* C} (h' : ψ₁ = ψ₂) (N : Type u)
    [AddCommGroup N] [Module D N] :
    Nonempty (InductionAlong.Ind (Res φ₁ N) ψ₁ ≃ₗ[C] InductionAlong.Ind (Res φ₂ N) ψ₂) := by
  subst h h'
  exact ⟨LinearEquiv.refl _ _⟩


theorem injective_of_surjective_of_linearEquiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [IsNoetherian R M] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (e : N ≃ₗ[R] M) : Function.Injective f :=
  fun _ _ h => IsNoetherian.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ f)
    (e.surjective.comp hf) (congrArg e h)

section CL

universe w

variable {Λ} {C : QuantumGroup.CartanDatum I} {hQ : IsRouquierQ C Q}
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

include hP hwf in

include hP hwf in
theorem nonempty_blackMixedRegularEquiv (hij : i ≠ j) :
    Nonempty (Res (appendBlackOpOfEq Q Λ i h₂) (InductionAlong.Ind Rg
        (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)))) ≃ₗ[
          (T (({j} : Multiset I) + μ))ᵐᵒᵖ] InductionAlong.Ind
      (Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ)) Rg)
      (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ))) := by
  have ej : appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)) =
      appendBlackOp Q Λ j ({i} + μ) := NonUnitalRingHom.ext fun _ => rfl
  have ej' : appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ) =
      appendBlackOp Q Λ j μ := NonUnitalRingHom.ext fun _ => rfl
  have ei : appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ) =
      appendBlackOp Q Λ i μ := NonUnitalRingHom.ext fun _ => rfl
  obtain ⟨eT⟩ := nonempty_res_ind_congr ej (appendBlackOpOfEq Q Λ i h₂) Rg
  obtain ⟨eS⟩ := nonempty_ind_res_congr ei ej' Rg
  have e1 := clBlackModuleCrossEquivQ hP hwf j i μ Rg hij
  exact ⟨(eT.trans e1).trans eS.symm⟩

theorem isNoetherian_blackMixedRegular (hQ' : IsRouquierQ C Q) :
    IsNoetherian (T (({j} : Multiset I) + μ))ᵐᵒᵖ (InductionAlong.Ind
      (Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ)) Rg)
      (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ))) := by
  have ej' : appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ) =
      appendBlackOp Q Λ j μ := NonUnitalRingHom.ext fun _ => rfl
  have ei : appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ) =
      appendBlackOp Q Λ i μ := NonUnitalRingHom.ext fun _ => rfl
  obtain ⟨eS⟩ := nonempty_ind_res_congr ei ej' Rg
  have : Module.Finite k (T ({j} + μ)) := tensorProductAlgebra_finite Λ _ hQ'
  have : Module.Finite k (T ({i} + μ)) := tensorProductAlgebra_finite Λ _ hQ'
  have : IsNoetherianRing (T ({j} + μ))ᵐᵒᵖ :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k (T ({j} + μ))ᵐᵒᵖ)
  have hφ : ∀ (c : k) (a : (T μ)ᵐᵒᵖ), appendBlackOp Q Λ i μ (c • a) =
      c • appendBlackOp Q Λ i μ a := fun c a => by
    induction a using MulOpposite.rec' with
    | h a => exact congrArg op (map_smul (appendBlack Q Λ i μ) c a)
  have : Module.Finite (T μ)ᵐᵒᵖ (Res (appendBlackOp Q Λ i μ) (T ({i} + μ))ᵐᵒᵖ) :=
    Res.finite k hφ
  have : Module.Finite (T ({j} + μ))ᵐᵒᵖ (InductionAlong.Ind
    (Res (appendBlackOp Q Λ i μ) (T ({i} + μ))ᵐᵒᵖ) (appendBlackOp Q Λ j μ)) := Ind.finite
  have := isNoetherian_of_isNoetherianRing_of_finite (T ({j} + μ))ᵐᵒᵖ (InductionAlong.Ind
    (Res (appendBlackOp Q Λ i μ) (T ({i} + μ))ᵐᵒᵖ) (appendBlackOp Q Λ j μ))
  have : IsNoetherian (T ({j} + μ))ᵐᵒᵖ (InductionAlong.Ind
    (Res (appendBlackOp Q Λ i μ) Rg) (appendBlackOp Q Λ j μ)) := this
  exact isNoetherian_of_linearEquiv eS.symm

include hP hwf hQ in
theorem isIso_blackMixedBeckChevalley (hij : i ≠ j) :
    IsIso (blackMixedBeckChevalley Λ hsym i j μ h₂) := by
  let B := ModuleCat.of (T ({i} + μ))ᵐᵒᵖ (T ({i} + μ))ᵐᵒᵖ
  have hsurj₀ := blackMixedBeckChevalley_regular_surjective Λ hsym i j μ h₂ hij
  obtain ⟨α, hα⟩ : ∃ f : InductionAlong.Ind
      (Res (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ)) B)
      (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ)) →ₗ[
        (T (({j} : Multiset I) + μ))ᵐᵒᵖ] Res (appendBlackOpOfEq Q Λ i h₂) (InductionAlong.Ind B
          (appendBlackOpOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)))),
      ⇑f = ⇑((blackMixedBeckChevalley Λ hsym i j μ h₂).app B).hom :=
    ⟨((blackMixedBeckChevalley Λ hsym i j μ h₂).app B).hom, rfl⟩
  have hsurj : Function.Surjective α := hα ▸ hsurj₀
  obtain ⟨e⟩ := nonempty_blackMixedRegularEquiv hP hwf (i := i) (j := j) (μ := μ) (h₂ := h₂) hij
  have := isNoetherian_blackMixedRegular (Λ := Λ) (i := i) (j := j) (μ := μ) hQ
  have hinj := injective_of_surjective_of_linearEquiv α hsurj e
  have hF : IsTensorRepresented (blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = {i} + μ) ⋙
      blackFOfEq Q Λ j (rfl : ({j} : Multiset I) + μ = {j} + μ)) :=
    TensorRepresented.IsTensorRepresented.comp _ _ (InductionAlong.isTensorRepresented_resFunctor _)
      (InductionAlong.isTensorRepresented_functor _)
  have hG : IsTensorRepresented
      (blackFOfEq Q Λ j (rfl : ({j} : Multiset I) + ({i} + μ) = {j} + ({i} + μ)) ⋙
        blackEOfEq Q Λ i h₂) :=
    TensorRepresented.IsTensorRepresented.comp _ _ (InductionAlong.isTensorRepresented_functor _)
      (InductionAlong.isTensorRepresented_resFunctor _)
  exact TensorRepresented.isIso_of_bijective_app_regular hF hG _ (hα ▸ ⟨hinj, hsurj⟩)

include hP hwf hQ in
/-- **Mixed inversion on modules** (Webster, arXiv:1309.3796v3, Theorem 4.31, `E_i F_j ≅ F_j E_i`
for `i ≠ j`; Brundan, arXiv:1501.00350v1, (1.7)): for distinct colours the mate through
`Fᵢ ⊣ Eᵢ` of the induction crossing of right `T^λ`-modules is invertible. -/
theorem blackModuleMixedInversion (hsym : KLRSymm Q) : BlackModuleMixedInversion Λ hsym := by
  intro i j hij μ β₁ β₂ δ h₁ h₂ h₃ h₄
  apply isIso_indCrossOfEq_mixedMate
  subst h₁ h₃ h₄
  exact isIso_blackMixedBeckChevalley hP hwf (hsym := hsym) (i := i) (j := j) (μ := μ)
    (h₂ := h₂) hij

section Family

universe w₂ u₁

variable [∀ β : Multiset I,
    HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))

/-- **Brundan's mixed inversion for Webster's derived action** (Brundan, arXiv:1501.00350v1,
(1.7); Webster, arXiv:1309.3796v3, Theorem 4.31), with the module statement proved
(`blackModuleMixedInversion`). The hypotheses are those of `blackRouqFamily`: Theorem 4.30
(`CoverRelsNegligible`, `WFDom`), exactness (`hQ`), `KLRSymm Q` and the route hypothesis
`hΛ₀`. -/
theorem blackRouqFamily_mixedInversion (hsym : KLRSymm Q) :
    BrundanMixedInversion (blackRouqFamily.{u, w} hP hwf hsym hΛ₀) :=
  blackRouqFamily_mixedInversion_of hP hwf hΛ₀ (blackModuleMixedInversion hP hwf hsym)

/-- **Cautis–Lauda's normalized `U_Q(g)` acts on Webster's derived categories** (Brundan,
arXiv:1501.00350v1, Theorem 1.2; Webster, arXiv:1309.3796v3, Theorem 4.31), from Brundan's
upward KLR relations `H` for distinct colours (an explicit hypothesis of this assembly), with
`r_i = 1` and the homogeneity condition `hq` on the scalars. Mixed inversion is proved
(`blackRouqFamily_mixedInversion`). -/
def blackPresCLPseudofunctorOfUpKLR (hsym : KLRSymm Q) (Sc : CL.CLScalars C k)
    (H : BrundanUpKLR (blackRouqFamily.{u, w} hP hwf hsym hΛ₀) Sc) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    Pseudofunctor (RevBicat (CL.presCL RD k Sc).Bicat) (LinearCat k) :=
  blackPresCLPseudofunctorOf hP hwf hΛ₀ Sc H (blackModuleMixedInversion hP hwf hsym) hr hq

end Family

end CL
