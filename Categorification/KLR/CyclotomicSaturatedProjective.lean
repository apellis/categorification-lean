/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicTerminalSymmetric
import Categorification.KLR.NilHeckeFullSplitting
import Categorification.Algebra.NilHeckeDemazure
import Categorification.Algebra.IdempotentEquiv

/-!
# Terminal cyclotomic divided-power projectives

For saturated content consisting of one colour, the divided-power
idempotent remains full in the cyclotomic quotient. Its corner consists
of scalars because the positive symmetric polynomials vanish. This proves
simplicity of its actual right ideal, a single-colour input for Webster,
arXiv:1309.3796v2, Proposition 7.2.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra MvPolynomial Categorification.NilHecke MulOpposite

private theorem simple_of_scalar_full_corner {k A : Type*} [Field k] [Ring A]
    [Algebra k A] [Nontrivial A] {E : A} (he : IsIdempotentElem E)
    (scalar : ∀ z : A, ∃ c : k, E*z*E = c • E)
    {ι : Type*} [Fintype ι] (a b : ι → A)
    (ha : ∀ j, a j * E = a j) (full : ∑ j, a j * b j = 1) :
    IsSimpleModule Aᵐᵒᵖ (rIdeal E) := by
  classical
  have hE : E ≠ 0 := by
    intro ez
    have hz (j : ι) : a j = 0 := by simpa [ez] using (ha j).symm
    simp [hz] at full
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨⟨⟨⟨E,he⟩,0,fun h => hE (congrArg Subtype.val h)⟩⟩, ?_⟩
  intro z hz y
  have supported := mem_rIdeal.mp z.property
  have witness : ∃ j, z.val * a j ≠ 0 := by
    by_contra! hall
    apply hz
    apply Subtype.ext
    change z.val = 0
    calc
      z.val = z.val * (∑ j, a j * b j) := by rw [full, mul_one]
      _ = 0 := by simp only [Finset.mul_sum, ← mul_assoc, hall, zero_mul, Finset.sum_const_zero]
  obtain ⟨j, hj⟩ := witness
  obtain ⟨c,hc⟩ := scalar (z.val * a j)
  rw [← mul_assoc E, supported, mul_assoc, ha] at hc
  have hc0 : c ≠ 0 := fun h => hj (by simpa [h] using hc)
  refine ⟨op (a j * (algebraMap k A c⁻¹ * y.val)), ?_⟩
  apply Subtype.ext
  change z.val * (a j * (algebraMap k A c⁻¹ * y.val)) = y.val
  rw [← mul_assoc, hc, smul_mul_assoc, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  exact mem_rIdeal.mp y.property

variable {k I : Type*} [Field k] [DecidableEq I] {ν : Multiset I} {i : I}
  (same : ∀ j ∈ ν, j = i) (Q : I → I → MvPolynomial (Fin 2) k)

local notation "n" => Multiset.card ν
local notation "powers" => fun _ : I => (Polynomial.X ^ n : Polynomial k)
local notation "R" => CycKLR k Q powers ν
local notation "π" => CycKLR.mk k Q powers ν

/-- The image of the standard terminal nilHecke divided-power projector. -/
def terminalDividedIdem : R := π (pol (xDelta n) * ψw (w0Word n))

local notation "E" => terminalDividedIdem (ν := ν) Q

omit [DecidableEq I] in
private theorem ddw_longest_isSymmetric (g : MvPolynomial (Fin n) k) :
    (ddw (w0Word n) g).IsSymmetric := by
  intro w
  have hadd (j : ℕ) : rename (TypeA.sadj n j) (ddw (w0Word n) g) = ddw (w0Word n) g := by
    by_cases h : j+1 < n
    · rw [TypeA.sadj, dite_eq_left h]
      exact rename_swap_ddw_w0Word h g
    · rw [TypeA.sadj, dite_eq_right h]
      exact rename_id_apply _
  have hw (ρ : List ℕ) :
      rename (TypeA.wordProd n ρ) (ddw (w0Word n) g) = ddw (w0Word n) g := by
    induction ρ with
    | nil => exact rename_id_apply _
    | cons j ρ ih =>
      rw [TypeA.wordProd_cons]
      change rename (TypeA.sadj n j ∘ TypeA.wordProd n ρ) _ = _
      rw [← rename_rename, ih, hadd]
  rw [← TypeA.wordProd_canWord n w]
  exact hw _

include same in
private theorem terminalDividedIdem_scalar_corner
    (vanish : ∀ p ∈ coinvIdeal k n, π (pol p) = 0) (z : R) :
    ∃ c : k, terminalDividedIdem (ν := ν) Q * z * terminalDividedIdem (ν := ν) Q =
      c • terminalDividedIdem (ν := ν) Q := by
  obtain ⟨a,rfl⟩ := CycKLR.mk_surjective z
  let T := toNH same Q a
  let g := ddw (w0Word n) (T (xDelta n))
  let f := pol (xDelta n) * ψw (w0Word n) (k := k) (Q := Q) (ν := ν)
  have hn (w : MvPolynomial (Fin n) k) :
      T (ddw (w0Word n) w * xDelta n) = ddw (w0Word n) w * T (xDelta n) := by
    have mem : T ∈ nilHecke k n := range_toNH same Q ▸ ⟨a, rfl⟩
    have h := congrArg (fun u : Module.End k (MvPolynomial (Fin n) k) => u (xDelta n))
      (mul_mulPoly_of_forall (fun j hj => rename_swap_ddw_w0Word hj w) mem)
    simpa only [Module.End.mul_apply, mulPoly_apply] using h
  have relation : f * a * f = pol g * f := by
    apply toNH_injective same Q
    simp only [map_mul, f, toNH_pol, toNH_ψw]
    refine LinearMap.ext fun w => ?_
    simp only [Module.End.mul_apply, mulPoly_apply]
    rw [mul_comm (xDelta n) (ddw _ w), hn,
      ddw_w0Word_mul_of_mem (ddw_w0Word_mem_adjInv _ _)]
    ring
  let c := constantCoeff g
  have hg : g - C c ∈ coinvIdeal k n := by
    apply Ideal.subset_span
    exact ⟨(ddw_longest_isSymmetric (ν := ν) (T (xDelta n))).sub (show (C c).IsSymmetric from fun w => rename_C _ _),
      by simp [c]⟩
  have hq := vanish _ hg
  rw [map_sub, map_sub, sub_eq_zero] at hq
  refine ⟨c, ?_⟩
  change π f * π a * π f = c • π f
  rw [← map_mul, ← map_mul, relation, map_mul, hq, ← algebraMap_eq, AlgHom.commutes,
    AlgHom.commutes, Algebra.smul_def]

include same in
theorem terminalDividedIdem_idempotent : IsIdempotentElem E := by
  let f := pol (xDelta n) * ψw (w0Word n) (k := k) (Q := Q) (ν := ν)
  have hf : IsIdempotentElem f := by
    apply toNH_injective same Q
    simp only [map_mul, f, toNH_pol, toNH_ψw]
    exact (isIdempotentElem_idemNH (k := k) (m := n)).eq
  exact hf.map π

include same in
/-- In the saturated one-colour cyclotomic block, the actual right ideal cut
out by the divided-power idempotent is simple. -/
theorem terminalDividedProjective_simple :
    CategoryTheory.Simple (ModuleCat.of Rᵐᵒᵖ (rIdeal E)) := by
  let _ : Nontrivial R := (terminalCoinvAct same Q).toRingHom.domain_nontrivial
  obtain ⟨ι, _, _, a, b, _, h⟩ := exists_isSplitting_one_idemNH k n
  let φ := (π).comp (nilHeckeEquivOfForall same Q).symm.toAlgHom
  have hE : φ ⟨idemNH k n, idemNH_mem⟩ = E := by
    let e := nilHeckeEquivOfForall same Q
    have he : e (pol (xDelta n) * ψw (w0Word n)) = ⟨idemNH k n, idemNH_mem⟩ := by
      apply Subtype.ext
      change toNH same Q (pol (xDelta n) * ψw (w0Word n)) = _
      rw [map_mul, toNH_pol, toNH_ψw]
      rfl
    change π (e.symm ⟨idemNH k n, idemNH_mem⟩) = π (pol (xDelta n) * ψw (w0Word n))
    rw [← he, e.symm_apply_apply]
  apply simple_iff_isSimpleModule.mpr
  refine simple_of_scalar_full_corner (terminalDividedIdem_idempotent same Q)
    (terminalDividedIdem_scalar_corner same Q (terminal_pol_eq_zero_of_mem_coinvIdeal same Q))
    (φ ∘ a) (φ ∘ b) ?_ ?_
  · intro j
    change φ (a j) * E = φ (a j)
    rw [← hE, ← map_mul]
    congr 1
    simpa only [one_mul] using (h.left_mul_a j).symm
  · simpa only [map_sum, map_mul, Function.comp_apply, map_one] using congrArg φ h.sum_eq

end Categorification.KLR.CycKLR
