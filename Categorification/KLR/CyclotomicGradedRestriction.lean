/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedInduction
import Categorification.KLR.CyclotomicRestrictionProjective
import Categorification.QuantumGroup.UDotWords

/-!
# Graded cyclotomic restriction on projectives

Kang–Kashiwara, arXiv:1102.4677v4, §6, immediately before Lemma 6.1.
On the projective Grothendieck group the raising operator is restriction
from content β + αᵢ to β, shifted by dᵢ (1 − ⟨hᵢ, Λ − β⟩).
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ (Si + β)
local notation "srcGr" => grade G Λ (Si + β)
local notation "dstGr" => grade G Λ β
local notation "LP" => LaurentPolynomial ℤ

/-- Unshifted restriction on finitely generated graded projectives
(Kang–Kashiwara, Corollary 4.6). -/
def gradedResProj (P : GProj srcGr) : GProj dstGr where
  carrier := Res Q i aΛ β P.carrier
  module := resModule Q i aΛ β P.carrier
  isScalarTower := resTower Q i aΛ β P.carrier
  grading := idem P.grading (lastIdem Q i aΛ β)
  decomposition := idemDecomposition P.grading
    (cyclotomicLast_mem_grade G Λ i β SetLike.GradedOne.one_mem)
  gradedSMul := ⟨fun _ _ _ _ hr hz =>
    SetLike.GradedSMul.smul_mem (A := srcGr) (B := P.grading) (cyclotomicLast_mem_grade G Λ i β hr) hz⟩
  finite := finite_res β i aΛ hQ (fun _ => Polynomial.monic_X_pow _) P.carrier
  projective := projective_res β i aΛ hsym hQ (Polynomial.monic_X_pow _) P.carrier

private def resCongr {P P' : GProj srcGr} (e : P.Iso P') :
    (gradedResProj G Λ i β hsym hQ P).Iso (gradedResProj G Λ i β hsym hQ P') where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (resMap Q i aΛ β P.carrier e.toLinearEquiv.toLinearMap)
    (resMap Q i aΛ β P'.carrier e.toLinearEquiv.symm.toLinearMap)
    (LinearMap.ext fun z => Subtype.ext (e.toLinearEquiv.apply_symm_apply z.1))
    (LinearMap.ext fun z => Subtype.ext (e.toLinearEquiv.symm_apply_apply z.1))
  map_mem' _ _ hx := e.map_mem hx
  symm_map_mem' _ _ hx := e.symm_map_mem' hx

private def resProd (P P' : GProj srcGr) :
    (gradedResProj G Λ i β hsym hQ (P.prod P')).Iso
      ((gradedResProj G Λ i β hsym hQ P).prod (gradedResProj G Λ i β hsym hQ P')) where
  toLinearEquiv :=
    { toFun := fun z => (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
      invFun := fun z => ⟨(z.1.1, z.2.1), Prod.ext z.1.2 z.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

private def resShift (P : GProj srcGr) (d : ℤ) :
    (gradedResProj G Λ i β hsym hQ (P.shift d)).Iso
      ((gradedResProj G Λ i β hsym hQ P).shift d) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

private def resAdd : K0 srcGr →+ K0 dstGr :=
  K0.lift (fun P => K0.of (gradedResProj G Λ i β hsym hQ P))
    (fun _ _ e => K0.of_eq_of_iso (resCongr G Λ i β hsym hQ e))
    (fun P P' => (K0.of_eq_of_iso (resProd G Λ i β hsym hQ P P')).trans (K0.of_prod ..))

/-- Unshifted cyclotomic restriction on the graded projective Grothendieck group. -/
def resK0 : K0 srcGr →ₗ[LP] K0 dstGr where
  __ := resAdd G Λ i β hsym hQ
  map_smul' := K0.map_smul_of_shift (resAdd G Λ i β hsym hQ) fun d x => by
    induction x using K0.induction_on with
    | of P =>
      simp only [K0.shiftHom_of, resAdd, K0.lift_of]
      exact K0.of_eq_of_iso (resShift G Λ i β hsym hQ P d)
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | neg x hx => simp only [map_neg, hx]

@[simp] theorem resK0_of (P : GProj srcGr) :
    resK0 G Λ i β hsym hQ (K0.of P) = K0.of (gradedResProj G Λ i β hsym hQ P) := by
  change resAdd G Λ i β hsym hQ (K0.of P) = _
  exact K0.lift_of _ _ _ _

variable (C : CartanDatum I)

/-- The projective normalization in the diagram preceding Kang–Kashiwara,
Lemma 6.1. Here Λ is recorded by its simple coroot coordinates. -/
def raiseShift : ℤ := di C i * (1 - ((Λ i : ℤ) - (β.map (A C i)).sum))

/-- The raising operator on one edge of the projective weight decomposition. -/
def raiseK0 : K0 srcGr →ₗ[LP] K0 dstGr :=
  (LaurentPolynomial.T (raiseShift Λ i β C) : LP) • resK0 G Λ i β hsym hQ

private def raiseComponent (ν : Multiset I) :
    K0 (grade G Λ ν) →ₗ[LP] projectiveK0 G Λ :=
  if h : i ∈ ν then
    let e : Si + ν.erase i = ν := (Multiset.singleton_add ..).trans (Multiset.cons_erase h)
    e ▸ (DirectSum.lof LP _ _ (ν.erase i) ∘ₗ raiseK0 G Λ i (ν.erase i) hsym hQ C :
      K0 (grade G Λ (Si + ν.erase i)) →ₗ[LP] projectiveK0 G Λ)
  else 0

/-- The projective raising operator in Kang–Kashiwara, §6.
On a block with no strand of colour i it acts by zero. -/
def raise : projectiveK0 G Λ →ₗ[LP] projectiveK0 G Λ :=
  DirectSum.toModule LP _ _ (raiseComponent G Λ i hsym hQ C)

@[simp] theorem raise_lof (x : K0 srcGr) :
    raise G Λ i hsym hQ C (DirectSum.lof LP _ _ (Si + β) x) =
      DirectSum.lof LP _ _ β (raiseK0 G Λ i β hsym hQ C x) := by
  rw [raise, DirectSum.toModule_lof, raiseComponent]
  rw [dite_eq_left (show i ∈ Si + β by simp)]
  have eval (μ : Multiset I) (hμ : μ = β) (he : Si + μ = Si + β) :
      (he ▸ (DirectSum.lof LP _ _ μ ∘ₗ raiseK0 G Λ i μ hsym hQ C :
        K0 (grade G Λ (Si + μ)) →ₗ[LP] projectiveK0 G Λ)) x =
          DirectSum.lof LP _ _ β (raiseK0 G Λ i β hsym hQ C x) := by
    subst μ
    rfl
  apply eval
  rw [Multiset.singleton_add, Multiset.erase_cons_head]

@[simp] theorem raise_lof_of_notMem (ν : Multiset I) (h : i ∉ ν) (x : K0 (grade G Λ ν)) :
    raise G Λ i hsym hQ C (DirectSum.lof LP _ _ ν x) = 0 := by
  rw [raise, DirectSum.toModule_lof, raiseComponent, dite_eq_right h, LinearMap.zero_apply]

/-- After more steps than there are strands of colour i in a block, repeated
raising vanishes (Kang–Kashiwara, §6, after Lemma 6.1). -/
theorem raise_pow_lof_eq_zero (n : ℕ) (ν : Multiset I) (h : ν.count i < n)
    (x : K0 (grade G Λ ν)) :
    (raise G Λ i hsym hQ C ^ n) (DirectSum.lof LP _ _ ν x) = 0 := by
  induction n generalizing ν with
  | zero => omega
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    by_cases hi : i ∈ ν
    · obtain ⟨μ, hμ⟩ := Multiset.exists_cons_of_mem hi
      rw [← Multiset.singleton_add] at hμ
      subst ν
      rw [raise_lof]
      apply ih
      simpa [Multiset.singleton_add] using h
    · rw [raise_lof_of_notMem _ _ _ _ _ _ _ hi, map_zero]

/-- The raising operator is locally nilpotent on the entire projective
Grothendieck group (Kang–Kashiwara, §6, after Lemma 6.1). -/
theorem raise_locally_nilpotent (x : projectiveK0 G Λ) :
    ∃ n : ℕ, (raise G Λ i hsym hQ C ^ n) x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨1, map_zero _⟩
  | of ν y => exact ⟨ν.count i + 1, raise_pow_lof_eq_zero G Λ i hsym hQ C _ ν (by omega) y⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [map_add]
    conv_lhs =>
      lhs
      rw [Nat.add_comm, pow_add, Module.End.mul_apply, hm, map_zero]
    rw [pow_add, Module.End.mul_apply, hn, map_zero, add_zero]

end Categorification.KLR.CycKLR
