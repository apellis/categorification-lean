/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.SerreMaps
import Categorification.KLR.Rouquier.Coefficient
import Categorification.KLR.Rouquier.Polynomial

/-!
# The endpoint composites in Rouquier's Serre homotopy

R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §3.2.3, Lemma 3.13,
and §4.1.1, Proposition 4.2. These endpoint identities retain the leading pure-power
coefficient explicitly. The crossing calculations adapt Khovanov–Lauda II,
arXiv:0804.2080v1, §3, equations (17)–(26), using nilHecke divided differences to
annihilate the lower polynomial terms over an arbitrary commutative ring.
-/

namespace Categorification.KLR.Rouquier

open Equiv MvPolynomial KLRAlgebra TypeA QuantumGroup KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- A nilHecke sandwich which kills lower powers extracts the leading coefficient. -/
theorem polynomial_sandwich_eq_coeff_smul (B L E z : A) (u v : Fin m) (d : ℕ)
    (hEL : Commute E L) (hvB : Commute (x v) B)
    (hpow : ∀ r, r ≤ d → B * x u ^ r * L * E = if r = d then z else 0)
    (f : MvPolynomial (Fin 2) k)
    (hf : ∀ s ∈ f.support, s 0 ≤ d ∧ (s 0 = d → s 1 = 0)) :
    B * (pol (rename ![u, v] f) * E) * L = f.coeff (Finsupp.single 0 d) • z := by
  classical
  let F : MvPolynomial (Fin 2) k →ₗ[k] A :=
    { toFun := fun f => B * (pol (rename ![u, v] f) * E) * L
      map_add' := by intro f g; simp only [map_add, add_mul, mul_add]
      map_smul' := by intro c f; simp only [map_smul, smul_mul_assoc, mul_smul_comm, RingHom.id_apply] }
  change F f = _
  apply map_eq_coeff_smul F f (Finsupp.single 0 d) z
  intro s hs
  have hmono : pol (rename ![u, v] (monomial s (1 : k))) =
      (x u ^ s 0 * x v ^ s 1 : A) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [C_1, one_mul, map_mul, map_pow, rename_X, pol_X, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  change B * (pol (rename ![u, v] (monomial s (1 : k))) * E) * L = _
  rw [hmono]
  have hvBU : Commute (x v ^ s 1 : A) (B * x u ^ s 0) :=
    (hvB.pow_left _).mul_right ((commute_x_x v u).pow_pow _ _)
  have hform : B * (x u ^ s 0 * x v ^ s 1 * E) * L =
      x v ^ s 1 * (B * x u ^ s 0 * L * E) := by
    calc
      B * (x u ^ s 0 * x v ^ s 1 * E) * L =
          (B * x u ^ s 0) * x v ^ s 1 * (E * L) := by simp only [mul_assoc]
      _ = x v ^ s 1 * (B * x u ^ s 0) * (L * E) := by rw [← hvBU.eq, hEL.eq]
      _ = x v ^ s 1 * (B * x u ^ s 0 * L * E) := by simp only [mul_assoc]
  rw [hform, hpow _ (hf s hs).1]
  by_cases hr : s 0 = d
  · have hs1 := (hf s hs).2 hr
    have he : s = Finsupp.single 0 d := by
      ext a; fin_cases a <;> simp [hr, hs1]
    simp [he]
  · have he : s ≠ Finsupp.single 0 d := by
      intro he; apply hr; simp [he]
    rw [ite_eq_right hr, mul_zero, ite_eq_right he]

variable {t : Seq ν} {p N : ℕ} {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

local notation "S" => serreSeq t p

include hpN ht₀ ht

theorem serre_B_step (hN1 : 1 ≤ N) :
    (aminus t p N 1 * aplus t p N 0 : A) =
      blockElt (p + 1) N * (ψ p * ψ p * e (S 0)) * chainL (p + 1) (N - 1) := by
  set L' : A := chainL (p + 1) (N - 1)
  set BR1 : A := blockElt (p + 1) N
  set BR2 : A := blockElt (p + 2) (N - 1)
  have hm : (aminus t p N 1 : A) = BR1 * ψ p * e (S 1) := by
    rw [aminus, Nat.sub_self, blockElt_zero, one_mul, show N - 1 + 1 = N by omega, chainR_one]
  have hp : (aplus t p N 0 : A) = BR2 * (ψ p * L') * e (S 0) := by
    rw [aplus, zero_add, blockElt_one, one_mul, add_zero, Nat.sub_zero,
      chainL_eq_ψ_mul hN1, show p + 0 + 2 = p + 2 by omega]
  have hA : (ψ p * (L' * e (S 0)) : A) = e (S 1) * (ψ p * L') := by
    have := chainL_serre (k := k) (Q := Q) hpN ht₀ ht (a := 0) (l := N) hN1 (by omega)
    rwa [add_zero, chainL_eq_ψ_mul hN1, mul_assoc] at this
  have hBR1 : Commute BR2 (e (S 1)) :=
    commute_blockElt_right_e hpN ht₀ ht hN1 (by omega) (by omega)
  have hL' : Commute L' (e (S 0)) :=
    commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hψ1 := ψ_serre_L (k := k) (Q := Q) hpN ht₀ ht (a := 0) (by omega)
  have hψ2 := ψ_serre_R (k := k) (Q := Q) hpN ht₀ ht (a := 1) le_rfl hN1
  rw [add_zero] at hψ1
  rw [show p + 1 - 1 = p by omega, Nat.sub_self] at hψ2
  have hB : (ψ p * (ψ p * (L' * e (S 0))) : A) = e (S 0) * (ψ p * (ψ p * L')) := by
    rw [hL'.eq, ← mul_assoc (ψ p) (e (S 0)), hψ1, mul_assoc, ← mul_assoc (ψ p) (e (S 1)), hψ2]
    simp only [mul_assoc]
  have hc : Commute (ψ p : A) BR2 := commute_ψ_blockElt (by omega)
  -- KL II (10) on the block `[p + 1, p + N + 1)`
  have h10 := blockElt_mul_blockElt_right (k := k) (Q := Q) (t := S 0) (q := p + 1)
    (n := N - 1) (by omega) (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
  rw [show N - 1 + 1 = N by omega, show p + 1 + 1 = p + 2 by omega] at h10
  have step : (aminus t p N 1 * aplus t p N 0 : A) = BR1 * (ψ p * ψ p * e (S 0)) * L' := by
    calc (aminus t p N 1 * aplus t p N 0 : A)
        = BR1 * (ψ p * (e (S 1) * (BR2 * (ψ p * (L' * e (S 0)))))) := by
          rw [hm, hp]; simp only [mul_assoc]
      _ = BR1 * (ψ p * (BR2 * (ψ p * (L' * e (S 0))))) := by
          rw [hA, hBR1.left_comm, ← mul_assoc (e (S 1)) (e (S 1)), e_mul_self,
            ← hBR1.left_comm, ← hA]
      _ = BR1 * (BR2 * (e (S 0) * (ψ p * (ψ p * L')))) := by rw [hc.left_comm, hB]
      _ = BR1 * (e (S 0) * (ψ p * (ψ p * L'))) := by
          rw [← mul_assoc, ← mul_assoc, h10, mul_assoc]
      _ = BR1 * (ψ p * ψ p * e (S 0)) * L' := by
          rw [← hB]; simp only [mul_assoc]; rw [hL'.eq]
  exact step

theorem serre_C_step (hN1 : 1 ≤ N) :
    (aplus t p N (N - 1) * aminus t p N N : A) =
      blockElt p N * (ψ (p + N - 1) * ψ (p + N - 1) * e (S N)) * chainR p (N - 1) := by
  set R' : A := chainR p (N - 1)
  set BLN : A := blockElt p N
  set BLm : A := blockElt p (N - 1)
  have hp : (aplus t p N (N - 1) : A) = BLN * ψ (p + N - 1) * e (S (N - 1)) := by
    rw [aplus, show N - 1 + 1 = N by omega, show N - (N - 1) - 1 = 0 by omega, blockElt_zero,
      mul_one, show N - (N - 1) = 1 by omega, chainL_one, show p + (N - 1) = p + N - 1 by omega]
  have hm : (aminus t p N N : A) = BLm * (ψ (p + N - 1) * R') * e (S N) := by
    rw [aminus, Nat.sub_self, zero_add, blockElt_one, mul_one, chainR_eq_ψ_mul hN1]
  have hRN : (ψ (p + N - 1) * (R' * e (S N)) : A) = e (S (N - 1)) * (ψ (p + N - 1) * R') := by
    have := chainR_serre (k := k) (Q := Q) hpN ht₀ ht (a := N) hN1 le_rfl
    rwa [chainR_eq_ψ_mul hN1, mul_assoc] at this
  have hBLm : Commute BLm (e (S (N - 1))) :=
    commute_blockElt_left_e hpN ht₀ ht (by omega) le_rfl (by omega)
  have hR' : Commute R' (e (S N)) := commute_chainR_left_e hpN ht₀ ht le_rfl le_rfl (by omega)
  have hψ1 := ψ_serre_L (k := k) (Q := Q) hpN ht₀ ht (a := N - 1) (by omega)
  have hψ2 := ψ_serre_R (k := k) (Q := Q) hpN ht₀ ht (a := N) hN1 le_rfl
  rw [show p + (N - 1) = p + N - 1 by omega, show N - 1 + 1 = N by omega] at hψ1
  have hB : (ψ (p + N - 1) * (ψ (p + N - 1) * (R' * e (S N))) : A) =
      e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R')) := by
    rw [hR'.eq, ← mul_assoc (ψ (p + N - 1)) (e (S N)), hψ2, mul_assoc,
      ← mul_assoc (ψ (p + N - 1)) (e (S (N - 1))), hψ1]
    simp only [mul_assoc]
  have hc : Commute (ψ (p + N - 1) : A) BLm := commute_ψ_blockElt (by omega)
  have h10 := blockElt_mul_blockElt_left (k := k) (Q := Q) (t := S N) (q := p)
    (n := N - 1) (by omega) (isConstOn_serreSeq_left hpN ht₀ ht le_rfl le_rfl (by omega))
  rw [show N - 1 + 1 = N by omega] at h10
  have step : (aplus t p N (N - 1) * aminus t p N N : A) =
      BLN * (ψ (p + N - 1) * ψ (p + N - 1) * e (S N)) * R' := by
    calc (aplus t p N (N - 1) * aminus t p N N : A)
        = BLN * (ψ (p + N - 1) * (e (S (N - 1)) * (BLm * (ψ (p + N - 1) * (R' * e (S N)))))) := by
          rw [hp, hm]; simp only [mul_assoc]
      _ = BLN * (ψ (p + N - 1) * (BLm * (ψ (p + N - 1) * (R' * e (S N))))) := by
          rw [hRN, hBLm.left_comm, ← mul_assoc (e (S (N - 1))) (e (S (N - 1))), e_mul_self,
            ← hBLm.left_comm, ← hRN]
      _ = BLN * (BLm * (e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R')))) := by
          rw [hc.left_comm, hB]
      _ = BLN * (e (S N) * (ψ (p + N - 1) * (ψ (p + N - 1) * R'))) := by
          rw [← mul_assoc, ← mul_assoc, h10, mul_assoc]
      _ = BLN * (ψ (p + N - 1) * ψ (p + N - 1) * e (S N)) * R' := by
          rw [← hB]; simp only [mul_assoc]; rw [hR'.eq]
  exact step

/-- The left endpoint nilHecke block extracts the leading pure-power coefficient. -/
theorem serre_B_polynomial (hN1 : 1 ≤ N) (f : MvPolynomial (Fin 2) k)
    (hf : ∀ s ∈ f.support, s 0 ≤ N - 1 ∧ (s 0 = N - 1 → s 1 = 0)) :
    (blockElt (p + 1) N *
      (pol (rename ![⟨p + 1, by omega⟩, ⟨p, by omega⟩] f) * e (S 0)) *
        chainL (p + 1) (N - 1) : A) =
      f.coeff (Finsupp.single 0 (N - 1)) • etop t p N 0 := by
  have hE : (etop t p N 0 : A) = blockElt (p + 1) N * e (S 0) := by
    simp only [etop, blockElt_zero, one_mul, Nat.sub_zero]
  rw [hE]
  refine polynomial_sandwich_eq_coeff_smul _ _ _ _ _ _ _
    (commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)).symm
    (commute_x_blockElt (by simp only; omega)) ?_ f hf
  intro r hr
  exact blockElt_mul_x_pow_mul_chainL' (s := S 0) (by omega) hN1
    (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega)) hr

/-- The right endpoint nilHecke block extracts the leading coefficient with its sign. -/
theorem serre_C_polynomial (hN1 : 1 ≤ N) (f : MvPolynomial (Fin 2) k)
    (hf : ∀ s ∈ f.support, s 0 ≤ N - 1 ∧ (s 0 = N - 1 → s 1 = 0)) :
    (blockElt p N *
      (pol (rename ![⟨p + N - 1, by omega⟩, ⟨p + N, hpN⟩] f) * e (S N)) *
        chainR p (N - 1) : A) =
      f.coeff (Finsupp.single 0 (N - 1)) • ((-1) ^ (N - 1) * etop t p N N) := by
  have hE : (etop t p N N : A) = blockElt p N * e (S N) := by
    simp only [etop, Nat.sub_self, blockElt_zero, mul_one]
  rw [hE]
  refine polynomial_sandwich_eq_coeff_smul _ _ _ _ _ _ _
    (commute_chainR_left_e hpN ht₀ ht le_rfl le_rfl (by omega)).symm
    (commute_x_blockElt (by simp only; omega)) ?_ f hf
  intro r hr
  exact blockElt_mul_x_pow_mul_chainR' (s := S N) (by omega) hN1
    (isConstOn_serreSeq_left hpN ht₀ ht le_rfl le_rfl (by omega)) hr

variable {C : CartanDatum I}

/-- The left endpoint composite is the leading coefficient times its divided-power
idempotent (Rouquier arXiv:0812.5023v1, Lemma 3.13, endpoint calculation). -/
theorem serre_B (hQ : IsRouquierQ C Q) (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (aminus t p N 1 * aplus t p N 0 : A) =
      (Q i j).coeff (Finsupp.single 0 (C.dij i j)) • etop t p N 0 := by
  have hN1 : 1 ≤ N := by omega
  rw [serre_B_step hpN ht₀ ht hN1]
  have hl0 : (S 0).lbl ⟨p, by omega⟩ = j :=
    serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ (by simp)
  have hl1 : (S 0).lbl ⟨p + 1, by omega⟩ = i :=
    serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp) (by simp only; omega)
      (by simp only; omega)
  have hswap : rename (![⟨p, by omega⟩, ⟨p + 1, by omega⟩] : Fin 2 → Fin m) (Q j i) =
      rename ![⟨p + 1, by omega⟩, ⟨p, by omega⟩] (Q i j) := by
    rw [← hQ.symm i j hij, rename_rename]
    apply congrArg (fun f : Fin 2 → Fin m => rename f (Q i j))
    funext a
    fin_cases a <;> rfl
  have hsq := KLRAlgebra.ψ_sq (Q := Q) p (by omega) (S 0)
  rw [hl0, hl1, ite_eq_right (Ne.symm hij), ncEval_x_two, hswap] at hsq
  rw [hsq]
  have hNm : N - 1 = C.dij i j := by omega
  simpa only [hNm] using serre_B_polynomial hpN ht₀ ht hN1 (Q i j)
    (fun s hs => by simpa only [hNm] using hQ.support_bound hij hs)

/-- The right endpoint composite has the same leading coefficient and the
nilHecke sign (Rouquier arXiv:0812.5023v1, Lemma 3.13, endpoint calculation). -/
theorem serre_C (hQ : IsRouquierQ C Q) (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (aplus t p N (N - 1) * aminus t p N N : A) =
      (Q i j).coeff (Finsupp.single 0 (C.dij i j)) •
        ((-1) ^ (N - 1) * etop t p N N) := by
  have hN1 : 1 ≤ N := by omega
  rw [serre_C_step hpN ht₀ ht hN1]
  have hl0 : (S N).lbl ⟨p + N - 1, by omega⟩ = i :=
    serreSeq_lbl_eq_i hpN ht₀ ht le_rfl _ (by simp only; omega) (by simp only; omega)
      (by simp only; omega)
  have hl1 : (S N).lbl ⟨p + N - 1 + 1, by omega⟩ = j :=
    serreSeq_lbl_eq_j hpN ht₀ ht le_rfl _ (by simp only; omega)
  have hsq := KLRAlgebra.ψ_sq (Q := Q) (p + N - 1) (by omega) (S N)
  rw [hl0, hl1, ite_eq_right hij, ncEval_x_two] at hsq
  simp only [show p + N - 1 + 1 = p + N by omega] at hsq
  rw [hsq]
  have hNm : N - 1 = C.dij i j := by omega
  simpa only [hNm] using serre_C_polynomial hpN ht₀ ht hN1 (Q i j)
    (fun s hs => by simpa only [hNm] using hQ.support_bound hij hs)

end Categorification.KLR.Rouquier
