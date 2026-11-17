/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedRestriction
import Categorification.KLR.CyclotomicMixedMate.Square

/-!
# The graded mixed cyclotomic commutator

Kang–Kashiwara, arXiv:1102.4677v4, §5.1, Theorem 5.1, and §6,
Lemma 6.1. At distinct colours the crossing gives the comparison from
shifted induction after restriction to restriction after induction.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded
open scoped ModuleCat.Algebra

section Coefficient

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (γ : Multiset I) (i j : I)

local notation "aΛ" => (fun u => (Polynomial.X : Polynomial k) ^ Λ u)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "U" => Si + (Sj + γ)
local notation "V" => Sj + (Si + γ)

private theorem cast_grade_symm {μ ν : Multiset I} (h : μ = ν) {d : ℤ}
    {z : CycKLR k Q aΛ ν} (hz : z ∈ grade G Λ ν d) :
    (MixedTransport.weightEquiv Q aΛ h).symm z ∈ grade G Λ μ d := by
  subst ν
  exact hz

/-- The signed terminal crossing in the distinct-colour mate has the degree
of a crossing with bottom labels `i,j` (KK §5.1, Theorem 5.1). -/
theorem mixedCoefficient_mem_grade :
    MixedMate.coefficient Q aΛ γ i j ∈ grade G Λ U (G.degΨ i j) := by
  unfold MixedMate.coefficient
  apply Graded.mem_map_of_mem
  rw [MixedCrossing.crossingElement, neg_mul]
  apply Submodule.neg_mem
  rw [← sum_e (k := k) (Q := Q) (ν := γ), map_sum, map_sum, Finset.mul_sum]
  apply Submodule.sum_mem
  intro s _
  change ψ _ * castKLR Q _ (cL Q j _ (cL Q i γ (e s))) ∈ _
  rw [cL_e, cL_e, castKLR_e]
  let h := MixedCrossing.square γ i j
  let t := Seq.cast h (MixedCrossing.doubleSeq γ j i s)
  have h₁ : t.lbl ⟨γ.card, by simp⟩ = i :=
    MixedCrossing.doubleSeq_apply_mid γ j i s _ rfl
  have h₂ : t.lbl ⟨γ.card + 1, by simp⟩ = j :=
    MixedCrossing.doubleSeq_apply_last γ j i s _ rfl
  change ψ γ.card * e t ∈ G.grade U (G.degΨ i j)
  simpa only [h₁, h₂] using G.ψ_mul_e_mem_grade (j := γ.card) (by simp) t

private theorem mixedFactor_mem_grade {d : ℤ} {z : IndCorner Q j aΛ γ}
    (hz : z.val ∈ grade G Λ (Sj + γ) d) :
    (MixedMate.factor Q aΛ γ i j z).val ∈ grade G Λ V (d + G.degΨ i j) :=
  cast_grade_symm G Λ _ (SetLike.GradedMul.mul_mem (A := grade G Λ U)
    (cyclotomicLast_mem_grade G Λ i (Sj + γ) hz) (mixedCoefficient_mem_grade G Λ γ i j))

/-- The balanced tensor grading on cyclotomic induction of a graded module. -/
def gradedIndModule (P : GMod (grade G Λ γ)) : GMod (grade G Λ (Si + γ)) := by
  let Γ := Graded.submodule (grade G Λ (Si + γ)) (lIdeal (lastIdem Q i aΛ γ))
  letI : DirectSum.Decomposition Γ := (GProj.ofIdempotent (lastIdem Q i aΛ γ)
    (lastIdem_mul Q i aΛ γ) (cyclotomicLast_mem_grade G Λ i γ SetLike.GradedOne.one_mem)).decomposition
  refine
    { carrier := Ind Q i aΛ γ P.carrier
      grading := balancedGrading _ _ Γ P.grading
      decomposition := balancedDecomposition (grade G Λ γ) ?_
      gradedSMul := gradedSMul_balanced (grade G Λ (Si + γ)) }
  intro d l m b hm hb
  exact SetLike.GradedMul.mul_mem (A := grade G Λ (Si + γ)) hm (cyclotomicLast_mem_grade G Λ i γ hb)

/-- The idempotent grading on cyclotomic restriction of a graded module. -/
def gradedResModule (P : GMod (grade G Λ (Si + γ))) : GMod (grade G Λ γ) where
  carrier := Res Q i aΛ γ P.carrier
  module := resModule Q i aΛ γ P.carrier
  isScalarTower := resTower Q i aΛ γ P.carrier
  grading := idem P.grading (lastIdem Q i aΛ γ)
  decomposition := idemDecomposition P.grading
    (cyclotomicLast_mem_grade G Λ i γ SetLike.GradedOne.one_mem)
  gradedSMul := ⟨fun _ _ _ _ hr hz => SetLike.GradedSMul.smul_mem (A := grade G Λ (Si + γ))
    (B := P.grading) (cyclotomicLast_mem_grade G Λ i γ hr) hz⟩

/-- Reindex a graded module along equality of contents using the algebra equivalence. -/
def transportGradedModule {μ ν : Multiset I} (h : μ = ν) (P : GMod (grade G Λ μ)) :
    GMod (grade G Λ ν) where
  carrier := P.carrier
  module := Module.compHom P.carrier (MixedTransport.weightEquiv Q aΛ h).symm.toRingHom
  isScalarTower := by subst ν; exact P.isScalarTower
  grading := P.grading
  decomposition := P.decomposition
  gradedSMul := by subst ν; exact P.gradedSMul

variable (P : GMod (grade G Λ (({i} : Multiset I) + γ))) (hij : i ≠ j) (hsym : KLRSymm Q)
local notation "R₀" => CycKLR k Q aΛ γ
local notation "R₁" => CycKLR k Q aΛ (Sj + γ)
local notation "cor" => Graded.submodule (grade G Λ (Sj + γ)) (lIdeal (lastIdem Q j aΛ γ))
local notation "upperCor" => Graded.submodule (grade G Λ V) (lIdeal (lastIdem Q j aΛ (Si + γ)))
local notation "sq" => MixedCrossing.square γ i j
local notation "rM" => gradedResModule G Λ γ i P
local notation "fM" => gradedIndModule G Λ (Si + γ) j P
local notation "feM" => gradedIndModule G Λ γ j rM
local notation "efM" => gradedResModule G Λ (Sj + γ) i (transportGradedModule G Λ sq fM)
local notation "E" => MixedComparison.originalMateEquiv Q aΛ γ i j hij hsym P.carrier

include hij hsym in
private theorem mixedMate_tmul_mem {d n : ℤ} {z : IndCorner Q j aΛ γ}
    {m : Res Q i aΛ γ P.carrier} (hz : z ∈ cor d) (hm : m.1 ∈ P.grading n) :
    E (BalancedTensor.tmul z m) ∈ (efM).grading (d + n + G.degΨ i j) := by
  change ((MixedComparison.originalMateEquiv Q aΛ γ i j hij hsym P.carrier).toLinearMap
    (BalancedTensor.tmul z m)).1 ∈ (gradedIndModule G Λ (Si + γ) j P).grading (d+n+G.degΨ i j)
  rw [MixedComparison.originalMateEquiv_eq_mate, MixedMate.mate_tmul]
  rw [show d + n + G.degΨ i j = (d + G.degΨ i j) + n by omega]
  exact tmul_mem_balancedGrading (ℳ := upperCor) (𝒩 := P.grading) (mixedFactor_mem_grade G Λ γ i j hz) hm

private def upperResEquiv (X : GMod (grade G Λ V)) :
    Res Q i aΛ (Sj + γ) ((MixedMate.upperTransport Q aΛ γ i j).obj (ModuleCat.of _ X.carrier))
      ≃ₗ[R₁] (gradedResModule G Λ (Sj + γ) i (transportGradedModule G Λ sq X)).carrier where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def mixedLinear (P : GMod (grade G Λ (({i} : Multiset I) + γ))) (hij : i ≠ j) (hsym : KLRSymm Q) :
    (gradedIndModule G Λ γ j (gradedResModule G Λ γ i P)).carrier ≃ₗ[R₁]
      (gradedResModule G Λ (Sj + γ) i (transportGradedModule G Λ sq
        (gradedIndModule G Λ (Si + γ) j P))).carrier :=
  (MixedComparison.originalMateEquiv Q aΛ γ i j hij hsym P.carrier).trans
    (upperResEquiv G Λ γ i j (gradedIndModule G Λ (Si + γ) j P))

private def isoOfPreserves {R : Type*} [Ring R] [Algebra k R] {A : ℤ → Submodule k R}
    (X Y : GMod A) (e : X.carrier ≃ₗ[R] Y.carrier)
    (he : ∀ ⦃d x⦄, x ∈ X.grading d → e x ∈ Y.grading d) : X.Iso Y :=
  GradedEquiv.ofPreserves e he

private def kLinear {R : Type*} [Ring R] [Algebra k R] {A : ℤ → Submodule k R}
    (X Y : GMod A) (e : X.carrier ≃ₗ[R] Y.carrier) : X.carrier →ₗ[k] Y.carrier :=
  { toFun := fun x => e x
    map_add' := e.map_add
    map_smul' := e.toLinearMap.map_smul_of_tower }

private theorem indModule_map_mem (P : GMod (grade G Λ γ)) {X : Type*} [AddCommGroup X] [Module k X]
    (𝒳 : ℤ → Submodule k X) (f : (gradedIndModule G Λ γ j P).carrier →ₗ[k] X)
    (hf : ∀ ⦃p q : ℤ⦄ ⦃b : IndCorner Q j aΛ γ⦄ ⦃m : P.carrier⦄,
      b ∈ cor p → m ∈ P.grading q → f (BalancedTensor.tmul b m) ∈ 𝒳 (p + q))
    ⦃d z⦄ (hz : z ∈ (gradedIndModule G Λ γ j P).grading d) : f z ∈ 𝒳 d :=
  balancedGrading_map_mem (ℳ := cor) (𝒩 := P.grading) 𝒳 f hf hz

private def indModule_iso_of_tmul (P : GMod (grade G Λ γ)) (Y : GMod (grade G Λ (Sj + γ))) (a : ℤ)
    (e : (gradedIndModule G Λ γ j P).carrier ≃ₗ[R₁] Y.carrier)
    (he : ∀ ⦃p q : ℤ⦄ ⦃b : IndCorner Q j aΛ γ⦄ ⦃m : P.carrier⦄,
      b ∈ cor p → m ∈ P.grading q → e (BalancedTensor.tmul b m) ∈ Y.grading (p + q + a)) :
    ((gradedIndModule G Λ γ j P).shift a).Iso Y := by
  apply isoOfPreserves ((gradedIndModule G Λ γ j P).shift a) Y e
  intro d z hz
  have H := indModule_map_mem G Λ γ j P (Graded.shift Y.grading (-a))
    (kLinear (gradedIndModule G Λ γ j P) Y e)
    (fun p q b m hb hm => by
      change e (BalancedTensor.tmul b m) ∈ Y.grading (p + q - -a)
      rw [sub_neg_eq_add]
      exact he hb hm)
    (d := d - a) (z := z) hz
  change e z ∈ Y.grading (d - a - -a) at H
  rwa [sub_neg_eq_add, sub_add_cancel] at H

/-- Kang–Kashiwara, arXiv:1102.4677v4, §5.1, Theorem 5.1. The mixed mate
is a graded isomorphism on every graded module of content `{i} + γ`. In the
Cartan grading the shift is `−(αᵢ|αⱼ)`. -/
def mixedIndResIso (P : GMod (grade G Λ (({i} : Multiset I) + γ))) (hij : i ≠ j) (hsym : KLRSymm Q) :
    ((gradedIndModule G Λ γ j (gradedResModule G Λ γ i P)).shift (G.degΨ i j)).Iso
      (gradedResModule G Λ (Sj + γ) i (transportGradedModule G Λ sq
        (gradedIndModule G Λ (Si + γ) j P))) :=
  indModule_iso_of_tmul G Λ γ j (gradedResModule G Λ γ i P) _ _
    (mixedLinear G Λ γ i j P hij hsym)
    (fun _ _ _ _ hb hm => mixedMate_tmul_mem G Λ γ i j P hij hsym hb hm)

end Coefficient

section Projective

open QuantumGroup QuantumGroup.UDot

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (γ : Multiset I) (i j : I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    (C : CartanDatum I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "sq" => MixedCrossing.square γ i j
local notation "LP" => LaurentPolynomial ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)

private def reindexK0 {μ ν : Multiset I} (h : μ = ν) :
    K0 (grade G Λ μ) →ₗ[LP] K0 (grade G Λ ν) := by
  subst ν
  exact LinearMap.id

private theorem reindexK0_of {μ ν : Multiset I} (h : μ = ν) (P : GProj (grade G Λ μ)) :
    reindexK0 G Λ h (K0.of P) = K0.of (h ▸ P : GProj (grade G Λ ν)) := by
  subst ν
  rfl

private theorem lof_reindexK0 {μ ν : Multiset I} (h : μ = ν) (x : K0 (grade G Λ μ)) :
    DirectSum.lof LP _ (fun δ => K0 (grade G Λ δ)) μ x =
      DirectSum.lof LP _ _ ν (reindexK0 G Λ h x) := by
  subst ν
  rfl

private theorem transport_proj {μ ν : Multiset I} (h : μ = ν) (P : GProj (grade G Λ μ)) :
    transportGradedModule G Λ h P.toGMod = (h ▸ P : GProj (grade G Λ ν)).toGMod := by
  subst ν
  rfl

private theorem mixed_unshiftedK0 (hij : i ≠ j) (x : K0 (grade G Λ (Si + γ))) :
    resK0 G Λ i (Sj + γ) hsym hQ (reindexK0 G Λ sq (indK0 G Λ j (Si + γ) x)) =
      T (G.degΨ i j) • indK0 G Λ j γ (resK0 G Λ i γ hsym hQ x) := by
  induction x using K0.induction_on with
  | of P =>
    rw [indK0_of, reindexK0_of, resK0_of, resK0_of, indK0_of, K0.T_smul_of]
    apply Eq.symm
    apply K0.of_eq_of_iso
    have e := mixedIndResIso G Λ γ i j P.toGMod hij hsym
    change GMod.Iso _ (gradedResModule G Λ (Sj + γ) i (transportGradedModule G Λ sq
      (gradedIndProj G Λ j (Si + γ) P).toGMod)) at e
    rw [transport_proj] at e
    exact e
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | neg x hx => simp only [map_neg, smul_neg, hx]

omit [DecidableEq I] in
private theorem mixed_shift (hcross : G.degΨ i j = -C.dot i j) :
    raiseShift Λ i (Sj + γ) C + G.degΨ i j = raiseShift Λ i γ C := by
  simp only [raiseShift, Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, hcross, ← di_mul_A C i j]
  ring

private theorem mixed_normalized (hij : i ≠ j) (hcross : G.degΨ i j = -C.dot i j)
    (x : K0 (grade G Λ (Si + γ))) :
    raiseK0 G Λ i (Sj + γ) hsym hQ C (reindexK0 G Λ sq (indK0 G Λ j (Si + γ) x)) =
      indK0 G Λ j γ (raiseK0 G Λ i γ hsym hQ C x) := by
  simp only [raiseK0, LinearMap.smul_apply, map_smul]
  rw [mixed_unshiftedK0 G Λ γ i j hsym hQ hij, smul_smul, ← LaurentPolynomial.T_add,
    mixed_shift G Λ γ i j C hcross]

/-- In the Cartan grading, the normalized raising and lowering operators
at distinct colours commute on the entire graded projective Grothendieck
group (Kang–Kashiwara, arXiv:1102.4677v4, §6, Lemma 6.1, `i ≠ j`). -/
theorem raise_lower_commute_of_ne (hij : i ≠ j) (hcross : G.degΨ i j = -C.dot i j) :
    Commute (raise G Λ i hsym hQ C) (lower G Λ j) := by
  apply LinearMap.ext
  intro x
  change raise G Λ i hsym hQ C (lower G Λ j x) = lower G Λ j (raise G Λ i hsym hQ C x)
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of ν y =>
    change raise G Λ i hsym hQ C (lower G Λ j (DirectSum.lof LP _ _ ν y)) =
      lower G Λ j (raise G Λ i hsym hQ C (DirectSum.lof LP _ _ ν y))
    by_cases hi : i ∈ ν
    · obtain ⟨γ, he⟩ := Multiset.exists_cons_of_mem hi
      rw [← Multiset.singleton_add] at he
      subst ν
      rw [raise_lof, lower_lof, lower_lof,
        lof_reindexK0 G Λ (MixedCrossing.square γ i j), raise_lof,
        mixed_normalized G Λ γ i j hsym hQ C hij hcross]
    · have hn : i ∉ Sj + ν := by simpa [Multiset.singleton_add] using ⟨hij, hi⟩
      rw [lower_lof, raise_lof_of_notMem _ _ _ _ _ _ _ hn,
        raise_lof_of_notMem _ _ _ _ _ _ _ hi, map_zero]

end Projective

end Categorification.KLR.CycKLR
