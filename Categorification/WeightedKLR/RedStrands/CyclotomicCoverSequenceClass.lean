/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverGrading
import Categorification.WeightedKLR.RedStrands.CyclotomicRestrictionWords

/-!
# Projecting sequence projectives from the cyclotomic cover

Webster, arXiv:1309.3796v2, Definition 4.34 and Lemmas 4.35–4.36.
Extension of scalars sends a cyclotomic sequence projective to its
ordered Stendhal sequence projective. The cyclotomic deletion formula
can then be projected to the Stendhal Grothendieck group.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra QuantumGroup QuantumGroup.UDot Categorification.Graded MulOpposite
open LieLean.QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe uI uk

variable {I : Type uI} {k : Type uk} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)

local notation "D" => I ⊕ Fin ℓ
local notation "μ" => stendhalWeight ℓ ν
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "H" => IsRouquierQ.gradingDatum hS
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum
  (fun j => C.dot j j / 2) (dotDegree C hQ)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "𝒯" => tensorProductGrade G ν
local notation "A" => CycKLR k S p μ
local notation "𝒜" => cyclotomicCoverGrade Λ C hQ ν
local notation "φ" => cyclotomicCoverToTensor (Q := Q) Λ ν C
local notation "LP" => LaurentPolynomial ℤ

open Classical in
/-- The class of a Stendhal loading, with unordered red loadings sent to zero. -/
def projectedSequenceClass (s : Seq μ) : K0 𝒯 :=
  if hs : IsRedOrdered s then K0.of (sequenceProj G s hs) else 0

/-- The ordered boundary idempotent is the image of the cover idempotent. -/
theorem cyclotomicCoverToTensor_mk_e (s : Seq μ) (hs : IsRedOrdered s) :
    φ (CycKLR.mk k S p μ (e s)) = TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) := by
  have h : φ (CycKLR.mk k S p μ (e s)) =
      TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s)) :=
    cyclotomicCoverToTensor_mk (Q := Q) Λ ν C (fe k μ s)
  rw [h]
  exact congrArg _ (Subtype.ext
    ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)))

theorem projectedSequenceClass_ordered (s : Seq μ) (hs : IsRedOrdered s) :
    projectedSequenceClass Λ C hQ ν s = K0.of (sequenceProj G s hs) := by
  simp [projectedSequenceClass, hs]


section Extension

universe u

variable {B F : Type u} [Ring B] [Algebra k B] [Ring F] [Algebra k F]
  (ℬ : ℤ → Submodule k B) [GradedAlgebra ℬ]
  (ℱ : ℤ → Submodule k F) [GradedAlgebra ℱ]
  (f : B →ₐ[k] F) (hf : PreservesGrading ℬ ℱ f.toLinearMap)

abbrev coverRightModule : Module Bᵐᵒᵖ F := Module.compHom F f.toRingHom.op

theorem coverSmulComm :
    letI := coverRightModule f
    SMulCommClass F Bᵐᵒᵖ F :=
  letI := coverRightModule f
  ⟨fun b r x => (mul_assoc b x (f r.unop)).symm⟩

theorem coverScalarTower :
    letI := coverRightModule f
    IsScalarTower k Bᵐᵒᵖ F := by
  let := coverRightModule f
  constructor
  intro c r x
  change x * f (c • r.unop) = c • (x * f r.unop)
  rw [map_smul, mul_smul_comm]

/-- Extension of scalars with the right action given by the algebra map. -/
def coverExtensionK0 : K0 ℬ →ₗ[LP] K0 ℱ :=
  @extensionK0 k B F _ _ _ _ _ ℬ ℱ _ _ f hf
    (coverRightModule f) (coverSmulComm f) (coverScalarTower f) (fun _ _ => rfl)

private theorem coverExtension_ofIdempotent (b : B) (hb : IsIdempotentElem b) (hb0 : b ∈ ℬ 0) :
    coverExtensionK0 ℬ ℱ f hf (K0.of (GProj.ofIdempotent b hb hb0)) =
      K0.of (GProj.ofIdempotent (f b) (hb.map f) (hf hb0)) := by
  exact @extensionK0_ofIdempotent k B F _ _ _ _ _ ℬ ℱ _ _ f hf
    (coverRightModule f) (coverSmulComm f) (coverScalarTower f) (fun _ _ => rfl) b hb hb0

end Extension

section Sequence

variable {B : Type (max uI uk)} [Ring B] [Algebra k B]
  (ℬ : ℤ → Submodule k B) [GradedAlgebra ℬ]
  (f : B →ₐ[k] TensorProductAlgebra k Q Λ ν)
  (hf : PreservesGrading ℬ
    (tensorProductGrade (stendhalGradingDatum Λ hQ.gradingDatum
      (fun j => C.dot j j / 2) (dotDegree C hQ)) ν) f.toLinearMap)

private theorem coverExtension_sequence (s : Seq μ) (b : B)
    (hb : IsIdempotentElem b) (hb0 : b ∈ ℬ 0)
    (he : f b = φ (CycKLR.mk k S p μ (e s))) :
    coverExtensionK0 ℬ 𝒯 f hf (K0.of (GProj.ofIdempotent b hb hb0)) =
      projectedSequenceClass Λ C hQ ν s := by
  classical
  rw [coverExtension_ofIdempotent]
  have h : φ (CycKLR.mk k S p μ (e s)) =
      TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s)) :=
    cyclotomicCoverToTensor_mk (Q := Q) Λ ν C (fe k μ s)
  by_cases hs : IsRedOrdered s
  · rw [projectedSequenceClass, dite_eq_left hs]
    have ho : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s) = StendhalAlgebra.e s hs :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))
    exact K0.of_ofIdempotent_congr (he.trans (h.trans (congrArg _ ho))) _ _ _ _
  · rw [projectedSequenceClass, dite_eq_right hs]
    have ho : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s) = 0 :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
    have hz : f b = 0 := he.trans (h.trans (by rw [ho, map_zero]))
    let P : GProj 𝒯 := GProj.ofIdempotent (f b) (hb.map f) (hf hb0)
    have hsub : Subsingleton P.carrier := by
      change Subsingleton (leftIdeal (f b))
      rw [hz]
      refine ⟨fun a b => Subtype.ext ?_⟩
      exact ((mul_zero _).symm.trans (mem_leftIdeal.mp a.2)).symm.trans
        ((mul_zero _).symm.trans (mem_leftIdeal.mp b.2))
    exact K0.of_eq_zero_of_subsingleton _

end Sequence

/-- Extension of graded projectives through the cyclotomic cover quotient. -/
def cyclotomicCoverProjectionK0 : K0 𝒜 →ₗ[LP] K0 𝒯 :=
  coverExtensionK0 𝒜 𝒯 φ (cyclotomicCoverToTensor_preservesGrading Λ C hQ ν)

/-- The principal cyclotomic cover projective at a loading. -/
abbrev cyclotomicCoverSequenceProjective (s : Seq μ) : GProj 𝒜 :=
  GProj.ofIdempotent _ ((show IsIdempotentElem (e (Q := S) s) from e_mul_self s).map (CycKLR.mk k S p μ))
    (Graded.mem_map_of_mem _ (CycKLR.mk k S p μ).toLinearMap ((H).e_mem_grade s))

theorem cyclotomicCoverProjectionK0_sequenceProjective (s : Seq μ) :
    cyclotomicCoverProjectionK0 Λ C hQ ν (K0.of (cyclotomicCoverSequenceProjective Λ C hQ ν s)) =
      projectedSequenceClass Λ C hQ ν s :=
  coverExtension_sequence Λ C hQ ν 𝒜 φ (cyclotomicCoverToTensor_preservesGrading Λ C hQ ν) s _ _ _ rfl

/-- The highest-weight multiplicities of the auxiliary cyclotomic cover. -/
abbrev cyclotomicCoverExponent : D → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

local notation "m" => cyclotomicCoverExponent (I := I) (ℓ := ℓ)
local notation "powP" => (fun j : D => (Polynomial.X : Polynomial k) ^ m j)

omit [DecidableEq I] in
theorem cyclotomicCoverPolynomial_eq_pow : p = powP := by
  funext j
  cases j <;> simp [cyclotomicCoverPolynomial]

/-- Identify the two presentations of the cover by matching all affine diagrams. -/
def powerCoverMap : CycKLR k S powP μ →ₐ[k] A :=
  CycKLR.lift (CycKLR.mk k S p μ) fun s => by
    rw [← cyclotomicCoverPolynomial_eq_pow]
    exact CycKLR.mk_cycElt s

private theorem powerCoverMap_graded :
    PreservesGrading (CycKLR.grade H m μ) 𝒜 (powerCoverMap (Q := Q) Λ C ν).toLinearMap := by
  rintro n x ⟨a, ha, rfl⟩
  change powerCoverMap (Q := Q) Λ C ν (CycKLR.mk k S powP μ a) ∈ 𝒜 n
  rw [powerCoverMap, CycKLR.lift_mk]
  exact Graded.mem_map_of_mem _ _ ha

local notation "powφ" => AlgHom.comp φ (powerCoverMap (Q := Q) Λ C ν)

theorem powerCoverToTensor_graded :
    PreservesGrading (CycKLR.grade H m μ) 𝒯 (powφ).toLinearMap :=
  fun _ _ ha => cyclotomicCoverToTensor_preservesGrading Λ C hQ ν
    (powerCoverMap_graded Λ C hQ ν ha)

/-- Extension from the power-polynomial presentation used by cyclotomic
raising on graded projective classes. -/
def cyclotomicCoverPowerProjectionK0 : K0 (CycKLR.grade H m μ) →ₗ[LP] K0 𝒯 :=
  coverExtensionK0 _ 𝒯 (powφ) (powerCoverToTensor_graded Λ C hQ ν)

theorem cyclotomicCoverPowerProjectionK0_sequenceProjective (s : Seq μ) :
    cyclotomicCoverPowerProjectionK0 Λ C hQ ν
      (K0.of (CycKLR.sequenceProjective hS m s)) = projectedSequenceClass Λ C hQ ν s := by
  apply coverExtension_sequence
  rw [AlgHom.comp_apply, powerCoverMap, CycKLR.lift_mk]

section Deletion

open CycKLR

theorem markedWord_split {J : Type*} {w : List J} {t : List J × J × List J}
    (ht : t ∈ markedWords w) : w = t.1 ++ t.2.1 :: t.2.2 := by
  induction w generalizing t with
  | nil => simp [markedWords] at ht
  | cons a w ih =>
    simp only [markedWords, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨z, hz, rfl⟩
    · rfl
    · simp [ih hz]

omit [DecidableEq I] in
/-- Deletion of the marked black letter keeps every red label and removes just
one copy of the chosen black colour from the content. -/
theorem markedBlackDeletionContent {i : I} {w : List D}
    (hw : (w : Multiset D) = ({Sum.inl i} : Multiset D) + μ)
    {t : List D × D × List D} (ht : t ∈ markedWords w) (hi : Sum.inl i = t.2.1) :
    ((t.1 ++ t.2.2 : List D) : Multiset D) = μ := by
  apply add_left_cancel (a := ({Sum.inl i} : Multiset D))
  rw [← hw, markedWord_split ht, ← hi]
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
  ac_rfl

local notation "C₀" => extendedCartanDatum C Λ
local notation "fam" => fun β : Multiset D => K0 (CycKLR.grade H m β)
local notation "ι" => DirectSum.lof LP _ fam

private theorem coverWordSequence_lof {β : Multiset D} (w : List D) (hw : (w : Multiset D) = β) :
    sequenceClass hS m w = ι β (K0.of (sequenceProjective hS m (Seq.ofList w hw))) := by
  subst β
  rw [sequenceClass]
  exact (totalQuotientK0_lof ..).trans (congrArg _ (quotientK0_ofIdempotent H m _ _ _))

/-- The normalized cyclotomic deletion sum after projecting to the lower
Stendhal weight. Every occurrence of the chosen black label contributes the
prefix quantum integer times its projected sequence class. -/
theorem cyclotomicCoverPowerProjectionK0_raise_sequenceProjective
    (i : I) (w : List D) (hw : (w : Multiset D) = ({Sum.inl i} : Multiset D) + μ) :
    cyclotomicCoverPowerProjectionK0 Λ C hQ ν
      (raiseK0 H m (Sum.inl i) μ (hS).klrSymm (hS).polyInY_leading C₀
        (K0.of (sequenceProjective hS m (Seq.ofList w hw)))) =
      (((markedWords w).attach).map fun t =>
        if hi : Sum.inl i = t.1.2.1 then
          qIntU (qUnitLP ^ di C₀ (Sum.inl i)) (prefixPair C₀ m (Sum.inl i) t.1.1) •
            projectedSequenceClass Λ C hQ ν
              (Seq.ofList (t.1.1 ++ t.1.2.2) (markedBlackDeletionContent ν hw t.2 hi))
        else 0).sum := by
  let RD : WeightDatum C₀ (D → ℤ) ((D → ℤ) →+ ℤ) :=
    { pair := AddMonoidHom.id _
      iX := fun j i => QuantumGroup.UDot.A C₀ i j
      iY := fun i => { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
      pair_iY_iX := fun _ _ => rfl }
  have h := raise_sequenceClass hS m RD (fun j => (m j : ℤ)) (fun _ => rfl) (Sum.inl i) w
  rw [coverWordSequence_lof Λ C hQ w hw, raise_lof] at h
  let F := (cyclotomicCoverPowerProjectionK0 Λ C hQ ν).comp (DirectSum.component LP _ fam μ)
  have hh := congrArg F h
  change cyclotomicCoverPowerProjectionK0 Λ C hQ ν (DirectSum.component LP _ fam μ (ι μ _)) = F _ at hh
  rw [DirectSum.component.lof_self] at hh
  rw [hh, map_list_sum]
  conv_lhs =>
    rw [← List.attach_map_subtype_val (markedWords w)]
    simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  change F (if Sum.inl i = t.1.2.1 then _ else 0) = _
  split_ifs with hi
  · rw [map_smul, coverWordSequence_lof Λ C hQ _ (markedBlackDeletionContent ν hw t.2 hi)]
    change _ • cyclotomicCoverPowerProjectionK0 Λ C hQ ν (DirectSum.component LP _ fam μ (ι μ _)) = _
    rw [DirectSum.component.lof_self, cyclotomicCoverPowerProjectionK0_sequenceProjective]
  · exact map_zero F

omit [DecidableEq I] in
/-- Restriction in the cover and in the red tensor algebra uses the same
normalizing shift at every black weight. -/
theorem cyclotomicCover_raiseShift (i : I) :
    raiseShift m (Sum.inl i) μ C₀ = raiseShift (fun j => ∑ r, Λ r j) i ν C := by
  have hred (r : Fin ℓ) := cover_black_red (C := C) Λ i r
  have hblack (j : I) : QuantumGroup.UDot.A C₀ (.inl i) (.inl j) = QuantumGroup.UDot.A C i j := rfl
  have hdi : di C₀ (.inl i) = di C i := rfl
  rw [raiseShift, raiseShift, hdi, stendhalWeight, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.map_map]
  simp only [Function.comp_def, hblack, hred, cyclotomicCoverExponent, Sum.elim_inl,
    Nat.cast_zero, zero_sub]
  have hreds : (Multiset.map (fun r : Fin ℓ => -(Λ r i : ℤ)) Finset.univ.val).sum =
      -(↑(∑ r, Λ r i) : ℤ) := by
    change (∑ r : Fin ℓ, -(Λ r i : ℤ)) = _
    rw [Finset.sum_neg_distrib, Nat.cast_sum]
  rw [hreds]
  ring

end Deletion

end Categorification.Stendhal
