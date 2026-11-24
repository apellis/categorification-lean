/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleEndomorphism
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Mathlib.Algebra.Exact.Basic

/-!
# The fixed middle-loading complex for the label-two standard

Webster, arXiv:1309.3796v2, §8.2, preceding Proposition 8.4.
The separated idempotent transports the two diagrammatic dot maps to
multiplication by the sum and difference in the middle algebra.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory Categorification.Webster.LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "W" => fixSub k S E

/-- The two right-dot differentials on the actual diagrammatic standard. -/
abbrev diagramPlus : Module.End A S := dotEnd k 0 + dotEnd k 1

/-- Difference of the two diagrammatic right dots. -/
abbrev diagramMinus : Module.End A S := dotEnd k 0 - dotEnd k 1

private theorem diagramPlus_mul_diagramMinus :
    diagramPlus k * diagramMinus k = 0 := by
  have h : Commute (dotEnd k 0) (dotEnd k 1) := by
    rw [← middleDotQuotientAction_X k 0, ← middleDotQuotientAction_X k 1]
    exact (Commute.all _ _).map (middleDotQuotientAction k)
  simp only [diagramPlus, diagramMinus, add_mul, mul_sub, ← pow_two, dotEnd_sq,
    zero_add, add_zero, ← h.eq, sub_self]

private theorem diagramMinus_mul_diagramPlus :
    diagramMinus k * diagramPlus k = 0 := by
  have h : Commute (dotEnd k 0) (dotEnd k 1) := by
    rw [← middleDotQuotientAction_X k 0, ← middleDotQuotientAction_X k 1]
    exact (Commute.all _ _).map (middleDotQuotientAction k)
  simp only [diagramPlus, diagramMinus, sub_mul, mul_add, ← pow_two, dotEnd_sq,
    zero_sub, sub_zero, ← h.eq, neg_add_cancel]

private abbrev diagramModule := ModuleCat.of A S

/-- The differential from degree `n + 1` to degree `n`. -/
def diagramDifferential (n : ℕ) : diagramModule k ⟶ diagramModule k :=
  ModuleCat.ofHom (if Even n then diagramPlus k else diagramMinus k)

private theorem diagramDifferential_square (n : ℕ) :
    diagramDifferential k (n + 1) ≫ diagramDifferential k n = 0 := by
  by_cases hn : Even n
  · have hnext : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using hn
    unfold diagramDifferential
    rw [ite_eq_right hnext, ite_eq_left hn]
    apply ModuleCat.hom_ext
    exact diagramPlus_mul_diagramMinus k
  · have hnext : Even (n + 1) := by simpa [Nat.even_add_one] using hn
    unfold diagramDifferential
    rw [ite_eq_left hnext, ite_eq_right hn]
    apply ModuleCat.hom_ext
    exact diagramMinus_mul_diagramPlus k

/-- The actual chain complex with the diagrammatic standard in each
degree and the alternating dot differentials. -/
def diagramMiddleComplex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun _ => diagramModule k) (diagramDifferential k) (diagramDifferential_square k)

/-- The augmentation from degree zero to the actual dot-sum quotient. -/
def diagramMiddleAugmentation : diagramModule k ⟶ ModuleCat.of A (StandardDotSumQuotient k) :=
  ModuleCat.ofHom (LinearMap.range (diagramPlus k)).mkQ

/-- The first differential is killed by the diagrammatic augmentation. -/
theorem diagramDifferential_zero_aug :
    diagramDifferential k 0 ≫ diagramMiddleAugmentation k = 0 := by
  unfold diagramDifferential diagramMiddleAugmentation
  rw [ite_eq_left (show Even (0 : ℕ) from ⟨0,rfl⟩)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

private def reflectedAction : Aᵐᵒᵖ →+* A :=
  (RingEquiv.opOp A).symm.toRingHom.comp
    (tensorReflect (Q := parameter k) (Λ := weights) (ν := blackWeight)).toRingHom.op

/-- Horizontal reflection identifies the middle idempotent in the right
and left conventions. -/
theorem reflectedAction_loading :
    reflectedAction k (MulOpposite.op E) = E := by
  exact unop_tensorReflect_e _ _

/-- The actual middle dot-sum quotient, viewed as a right diagram module
by horizontal reflection. -/
def rightMiddleDotSumQuotient : ModuleCat Aᵐᵒᵖ :=
  (ModuleCat.restrictScalars (reflectedAction k)).obj
    (ModuleCat.of A (StandardDotSumQuotient k))

/-- The alternating diagram complex in the right-module convention. -/
def rightMiddleComplex : ChainComplex (ModuleCat Aᵐᵒᵖ) ℕ :=
  ((ModuleCat.restrictScalars (reflectedAction k)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (diagramMiddleComplex k)

/-- Augmentation of the reflected diagram complex to the right
dot-sum quotient. -/
def rightMiddleAugmentation :
    (rightMiddleComplex k).X 0 ⟶ rightMiddleDotSumQuotient k :=
  (ModuleCat.restrictScalars (reflectedAction k)).map (diagramMiddleAugmentation k)

private def restrictFixed (f : Module.End A S) : W →ₗ[k] W where
  toFun z := ⟨f z.val, by
    change E • f z.val = f z.val
    rw [← f.map_smul, show E • z.val = z.val from z.property]⟩
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' c x := Subtype.ext ((f.restrictScalars k).map_smul c x.val)

/-- Sum differential on the fixed middle-loading space. -/
def fixedPlus := restrictFixed k (diagramPlus k)

/-- Difference differential on the fixed middle-loading space. -/
def fixedMinus := restrictFixed k (diagramMinus k)

private def algebraToEnd : Middle k ≃ₐ[k] Module.End A S :=
  (middlePolynomialEquiv k).symm.trans (middleEndomorphismEquiv k)

/-- The actual middle corner is the regular middle algebra, as a vector
space, by evaluation of the right-dot algebra on the loading generator. -/
def middleToFixed : Middle k ≃ₗ[k] W :=
  (algebraToEnd k).toLinearEquiv.trans
    (leftStandardEndEquivFixed (parameter k) weights loading loading_ordered)

private theorem algebraToEnd_y₁ : algebraToEnd k (y₁ : Middle k) = dotEnd k 0 := by
  have h : (middlePolynomialEquiv k).symm (y₁ : Middle k) = squareQuotientVariable k 0 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr
      (middlePolynomialEquiv_variable_zero k).symm
  have hh := congrArg (fun a : SquareQuotient k => middleEndomorphismEquiv k a) h
  exact hh.trans (middleDotQuotientAction_X k 0)

private theorem algebraToEnd_y₂ : algebraToEnd k (y₂ : Middle k) = dotEnd k 1 := by
  have h : (middlePolynomialEquiv k).symm (y₂ : Middle k) = squareQuotientVariable k 1 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr
      (middlePolynomialEquiv_variable_one k).symm
  have hh := congrArg (fun a : SquareQuotient k => middleEndomorphismEquiv k a) h
  exact hh.trans (middleDotQuotientAction_X k 1)

private theorem fixed_mul_formula (a b : Middle k) :
    restrictFixed k (algebraToEnd k a) (middleToFixed k b) = middleToFixed k (a * b) := by
  apply Subtype.ext
  change (algebraToEnd k a) ((algebraToEnd k b) g) = (algebraToEnd k (a*b)) g
  rw [map_mul, Module.End.mul_apply]

/-- The sum of the two diagrammatic right dots restricts to the algebraic
sum differential on the separated middle cut. -/
theorem fixedPlus_transport (a : Middle k) :
    fixedPlus k (middleToFixed k a) = middleToFixed k (plus (k := k) a) := by
  have h : algebraToEnd k (y₁ + y₂) = diagramPlus k := by
    exact ((algebraToEnd k).map_add _ _).trans
      (congrArg₂ (· + ·) (algebraToEnd_y₁ k) (algebraToEnd_y₂ k))
  exact (congrArg (fun f => restrictFixed k f (middleToFixed k a)) h).symm.trans
    (fixed_mul_formula k (y₁ + y₂) a)

/-- The difference of the two diagrammatic right dots restricts to the
algebraic difference differential on the separated middle cut. -/
theorem fixedMinus_transport (a : Middle k) :
    fixedMinus k (middleToFixed k a) = middleToFixed k (minus (k := k) a) := by
  have h : algebraToEnd k (y₁ - y₂) = diagramMinus k := by
    exact ((algebraToEnd k).map_sub _ _).trans
      (congrArg₂ (· - ·) (algebraToEnd_y₁ k) (algebraToEnd_y₂ k))
  exact (congrArg (fun f => restrictFixed k f (middleToFixed k a)) h).symm.trans
    (fixed_mul_formula k (y₁ - y₂) a)

private theorem transfer_exact {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] (e : V₁ ≃ₗ[k] V₂) (f₁ g₁ : V₁ → V₁)
    (f₂ g₂ : V₂ → V₂) (hf : ∀ a, f₂ (e a) = e (f₁ a))
    (hg : ∀ a, g₂ (e a) = e (g₁ a)) (h : Function.Exact f₁ g₁) :
    Function.Exact f₂ g₂ := by
  intro x
  obtain ⟨a, rfl⟩ := e.surjective x
  rw [hg, ← e.map_zero, e.injective.eq_iff, h a]
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨e b, hf b⟩
  · rintro ⟨b,hb⟩
    obtain ⟨c,rfl⟩ := e.surjective b
    exact ⟨c, e.injective ((hf c).symm.trans hb)⟩

/-- At the middle cut the difference–sum pair of diagrammatic dot maps
is exact. -/
theorem fixedMinusPlus_exact : Function.Exact (fixedMinus k) (fixedPlus k) :=
  transfer_exact k (middleToFixed k) minus plus (fixedMinus k) (fixedPlus k)
    (fixedMinus_transport k) (fixedPlus_transport k)
    (LinearMap.exact_iff.mpr ker_plus)

/-- At the middle cut the sum–difference pair of diagrammatic dot maps
is exact. -/
theorem fixedPlusMinus_exact : Function.Exact (fixedPlus k) (fixedMinus k) :=
  transfer_exact k (middleToFixed k) plus minus (fixedPlus k) (fixedMinus k)
    (fixedPlus_transport k) (fixedMinus_transport k)
    (LinearMap.exact_iff.mpr ker_minus)

local notation "targetFixed" => fixSub k (StandardDotSumQuotient k) E

private def fixQuotientMap {B M : Type*} [Ring B] [Algebra k B]
    [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
    (e : B) (U : Submodule B M) : fixSub k M e →ₗ[k] fixSub k (M ⧸ U) e where
  toFun z := ⟨U.mkQ z.val, by
    change e • U.mkQ z.val = _
    rw [← map_smul, show e • z.val = z.val from z.property]⟩
  map_add' x y := Subtype.ext (U.mkQ.map_add x.val y.val)
  map_smul' c x := Subtype.ext ((U.mkQ.restrictScalars k).map_smul c x.val)

private theorem fixQuotientMap_surjective {B M : Type*} [Ring B] [Algebra k B]
    [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
    {e : B} (he : IsIdempotentElem e) (U : Submodule B M) :
    Function.Surjective (fixQuotientMap k e U) := by
  intro z
  let z₀ : M ⧸ U := z.val
  have hs : ∃ a : M, (Submodule.Quotient.mk a : M ⧸ U) = z₀ :=
    Submodule.Quotient.mk_surjective U z₀
  obtain ⟨a, ha⟩ := hs
  have hs' : U.mkQ a = z₀ := ha
  have h₀ : e • z₀ = z₀ := z.property
  exact ⟨⟨e • a, smul_mem_fixSub he a⟩, Subtype.ext
    ((U.mkQ.map_smul e a).trans ((congrArg (fun y : M ⧸ U => e • y) hs').trans h₀))⟩

/-- Map the middle fixed space to the fixed space of its diagrammatic quotient. -/
def fixedQuotientMap : W →ₗ[k] targetFixed :=
  fixQuotientMap k (B := A) (M := S) E (LinearMap.range (diagramPlus k))

/-- Every fixed quotient vector lifts to a fixed vector in the middle standard. -/
theorem fixedQuotientMap_surj : Function.Surjective (fixedQuotientMap k) :=
  fixQuotientMap_surjective k (B := A) (M := S) (e := E)
    (seqIdem_mul_self (parameter k) weights loading loading_ordered)
    (LinearMap.range (diagramPlus k))

private theorem fixedQuotientMap_ker :
    LinearMap.ker (fixedQuotientMap k) = LinearMap.range (fixedPlus k) := by
  ext z
  constructor
  · intro hz
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    change (LinearMap.range (diagramPlus k)).mkQ z.val = 0 at h
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
    let hE : IsIdempotentElem E := seqIdem_mul_self (parameter k) weights loading loading_ordered
    refine ⟨⟨E • x, smul_mem_fixSub hE x⟩, Subtype.ext ?_⟩
    change diagramPlus k (E • x) = z.val
    rw [map_smul, hx]
    exact z.property
  · rintro ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (LinearMap.range (diagramPlus k)).mkQ (diagramPlus k x.val) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x.val, rfl⟩

/-- The augmentation of the fixed periodic diagram complex is the middle
idempotent image of the actual dot-sum quotient of the standard. -/
def fixedDotSumQuotientEquiv :
    (W ⧸ LinearMap.range (fixedPlus k)) ≃ₗ[k] targetFixed :=
  (Submodule.quotEquivOfEq _ _ (fixedQuotientMap_ker k).symm).trans
    (LinearMap.quotKerEquivOfSurjective (fixedQuotientMap k) (fixedQuotientMap_surj k))

/-- The augmentation on the actual fixed cut is the algebraic
specialization to the quotient with the two dots opposite. -/
def fixedAugmentation : W →ₗ[k] DualNumber k :=
  ((specialize (k := k)).restrictScalars k).toLinearMap.comp
    (middleToFixed k).symm.toLinearMap

theorem fixedAugmentation_surjective : Function.Surjective (fixedAugmentation k) :=
  (augmentation_surjective (k := k)).comp (middleToFixed k).symm.surjective

private theorem fixedAugmentation_apply (a : Middle k) :
    fixedAugmentation k (middleToFixed k a) = specialize a :=
  congrArg specialize ((middleToFixed k).symm_apply_apply a)

private theorem specialize_zero_iff (a : Middle k) :
    specialize a = 0 ↔ a ∈ LinearMap.range (plus (k := k)) := by
  change a ∈ RingHom.ker specialize.toRingHom ↔ _
  have hspan : a ∈ sumIdeal k ↔ ((y₁ : Middle k) + y₂) ∣ a :=
    Ideal.mem_span_singleton (α := Middle k)
  rw [ker_specialize_eq_span, hspan]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,hb⟩
    exact ⟨b,hb.symm⟩

private theorem exact_transport_into {R X Y : Type*}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (e : X ≃ₗ[k] Y) (f : X → X) (g₀ : X → R) (f' : Y → Y) (g' : Y → R)
    [Zero R] (hf : ∀ x, f' (e x) = e (f x)) (hg : ∀ x, g' (e x) = g₀ x)
    (hex : Function.Exact f g₀) : Function.Exact f' g' := by
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [hg, hex x]
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨e b, hf b⟩
  · rintro ⟨b,hb⟩
    obtain ⟨a,rfl⟩ := e.surjective b
    exact ⟨a,e.injective ((hf a).symm.trans hb)⟩

theorem fixedAugmentation_ker :
    LinearMap.ker (fixedAugmentation k) = LinearMap.range (fixedPlus k) :=
  LinearMap.exact_iff.mp <| exact_transport_into k (middleToFixed k) plus specialize
    (fixedPlus k) (fixedAugmentation k) (fixedPlus_transport k) (fixedAugmentation_apply k)
    (specialize_zero_iff k)

/-- The actual dot-sum quotient at the separated middle loading is the
dual-number specialization used in the algebraic periodic resolution. -/
def middleCutDotSumEquiv : targetFixed ≃ₗ[k] DualNumber k :=
  (fixedDotSumQuotientEquiv k).symm.trans <|
    (Submodule.quotEquivOfEq _ _ (fixedAugmentation_ker k).symm).trans
      (LinearMap.quotKerEquivOfSurjective (fixedAugmentation k) (fixedAugmentation_surjective k))


/-- The fixed quotient coordinates send a lifted middle polynomial to its specialization. -/
theorem middleCutDotSumEquiv_specialize (a : Middle k) :
    middleCutDotSumEquiv k (fixedQuotientMap k (middleToFixed k a)) = specialize a := by
  let z := middleToFixed k a
  have hz : fixedDotSumQuotientEquiv k ((LinearMap.range (fixedPlus k)).mkQ z) =
      fixedQuotientMap k z := rfl
  calc
    _ = middleCutDotSumEquiv k
        (fixedDotSumQuotientEquiv k ((LinearMap.range (fixedPlus k)).mkQ z)) :=
      congrArg (middleCutDotSumEquiv k) hz.symm
    _ = fixedAugmentation k z := by
      let H := (Submodule.quotEquivOfEq _ _ (fixedAugmentation_ker k).symm).trans
        (LinearMap.quotKerEquivOfSurjective (fixedAugmentation k) (fixedAugmentation_surjective k))
      let x := (LinearMap.range (fixedPlus k)).mkQ z
      change H ((fixedDotSumQuotientEquiv k).symm ((fixedDotSumQuotientEquiv k) x)) = _
      calc
        _ = H x := congrArg H ((fixedDotSumQuotientEquiv k).symm_apply_apply x)
        _ = fixedAugmentation k z := rfl
    _ = specialize a := fixedAugmentation_apply k a

private theorem dot_smul_middle_fixed (a : A) (f : Module.End A S)
    (ha : f g = a • g) (hf : ∀ b : Middle k, Commute f (algebraToEnd k b)) (z : W) :
    a • z.val = f z.val := by
  obtain ⟨b, rfl⟩ := (middleToFixed k).surjective z
  change a • ((algebraToEnd k b) g) = f ((algebraToEnd k b) g)
  rw [← (algebraToEnd k b).map_smul, ← ha]
  exact (DFunLike.congr_fun (hf b).eq g).symm

/-- At the fixed middle cut, the ambient left dot acts as the right-dot endomorphism. -/
theorem leftMiddleDot_smul_middle_fixed (z : W) :
    leftMiddleDot k • z.val = dotEnd k 0 z.val :=
  dot_smul_middle_fixed k _ _ (dotEnd_zero_gen k)
    (fun a => by
      rw [← algebraToEnd_y₁]
      exact (Commute.all (y₁ : Middle k) a).map (algebraToEnd k).toAlgHom) z

/-- At the fixed middle cut, the ambient right-position dot acts as the
second right-dot endomorphism. -/
theorem rightMiddleDot_smul_middle_fixed (z : W) :
    rightMiddleDot k • z.val = dotEnd k 1 z.val :=
  dot_smul_middle_fixed k _ _ (dotEnd_one_gen k)
    (fun a => by
      rw [← algebraToEnd_y₂]
      exact (Commute.all (y₂ : Middle k) a).map (algebraToEnd k).toAlgHom) z

end Categorification.Stendhal.LabelTwo
