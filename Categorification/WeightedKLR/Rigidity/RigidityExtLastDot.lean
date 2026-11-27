/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclotomicLocalCommutator

/-!
# The last dot at a lowest weight

Input for Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3. Let `S = R^Λ(i + β)` be a nonzero
cyclotomic KLR block whose centre consists of scalars, on whose terminal-colour corner the last
dot is nilpotent, and such that the next block `R^Λ(i + i + β)` vanishes. Then the Kang–Kashiwara
weight `⟨h_i, Λ - (i + β)⟩ = -h` is nonpositive and the last dot satisfies `x^h e(β, i) = 0`.

By Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2 (`originalPositiveEquiv`), a positive weight
would embed `S` into `E F(S) = 0`. At nonpositive weight (`originalNegativeEquiv`) the dotted
counits `c_d : F E → 1`, `d < h`, identify `F E(S)` with `S^h`. Hence the counit with `h` dots is
an `S`-combination of the first `h`, with central and so scalar coefficients. This gives a monic
polynomial of degree `h` killing the dot on `e(β, i)`, and nilpotency leaves `x^h`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra.AbsentColour

open CategoryTheory Categorification.TwoRep InductionCalculus
open scoped ModuleCat.Algebra

universe u v

variable {I : Type u} [DecidableEq I] {k : Type v} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
  (hsym : KLRSymm Q)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

local notation "β₁" => ((Singleton.singleton i : Multiset I) + β)
local notation "S" => CycKLR k Q a β₁
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β₁))
local notation "xl" => dotElement Q i a β
local notation "el" => lastIdem Q i a β

/-- A polynomial relation for the last dot on the terminal corner, together with nilpotency,
forces the power of the polynomial's lowest vanishing order. -/
private theorem pow_mul_eq_zero_of_monic {R : Type*} [Ring R] [Algebra k R] (x e : R)
    (p : Polynomial k) (hp : p.Monic) (hpe : Polynomial.aeval x p * e = 0)
    (N : ℕ) (hN : x ^ N * e = 0) : x ^ p.natDegree * e = 0 := by
  let J : Ideal (Polynomial k) :=
    { carrier := {q | Polynomial.aeval x q * e = 0}
      add_mem' := by
        intro q r hq hr
        simp only [Set.mem_ofPred_eq, map_add, add_mul] at *
        rw [hq, hr, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c q hq
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        rw [mul_assoc, hq, mul_zero] }
  have hJp : p ∈ J := hpe
  have hJN : Polynomial.X ^ N ∈ J := by
    change Polynomial.aeval x (Polynomial.X ^ N) * e = 0
    rw [map_pow, Polynomial.aeval_X, hN]
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal J)
  have hdvd (q : Polynomial k) (hq : q ∈ J) : g ∣ q := by
    rw [hg] at hq
    exact Ideal.mem_span_singleton.mp hq
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow Polynomial.prime_X N).mp (hdvd _ hJN)
  have hmp : Polynomial.X ^ m ∣ p := (hm.symm.dvd).trans (hdvd p hJp)
  have hle : m ≤ p.natDegree := by
    have := Polynomial.natDegree_le_of_dvd hmp hp.ne_zero
    simpa using this
  have hmem : Polynomial.X ^ m ∈ J := by
    rw [hg]
    exact Ideal.mem_span_singleton.mpr hm.dvd
  have : Polynomial.X ^ (p.natDegree - m) * Polynomial.X ^ m ∈ J := J.mul_mem_left _ hmem
  rw [← pow_add, Nat.sub_add_cancel hle] at this
  change Polynomial.aeval x (Polynomial.X ^ p.natDegree) * e = 0 at this
  rwa [map_pow, Polynomial.aeval_X] at this

include hsym hQ ha hΛ hdeg in
/-- **The last dot at a lowest weight.** If `R^Λ(i + β)` is nonzero with scalar centre, the
next block `R^Λ(i + i + β)` vanishes and the last dot is nilpotent, then the Kang–Kashiwara
weight `⟨h_i, Λ - (i + β)⟩ = -h` is nonpositive and `x^h e(β, i) = 0` in `R^Λ(i + β)` (input
for Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3). -/
theorem dotElement_pow_mul_lastIdem_eq_zero [Nontrivial S]
    (hvan : Subsingleton (CycKLR k Q a ({i} + β₁)))
    (hcen : ∀ z : S, (∀ y : S, z * y = y * z) → ∃ c : k, z = algebraMap k S c)
    (hnil : IsNilpotent (xl * el)) :
    xl ^ (-wt).toNat * el = 0 := by
  classical
  let h := (-wt).toNat
  let M : ModuleCat.{max u v} S := ModuleCat.of S S
  have hsub : Subsingleton
      ((inductionFunctor.{u, v, 0} Q i a β₁ ⋙ restrictionFunctor.{u, v, 0} Q i a β₁).obj M) := by
    have : Subsingleton ((inductionFunctor.{u, v, 0} Q i a β₁).obj M) :=
      Module.subsingleton (CycKLR k Q a ({i} + β₁)) _
    exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  -- the Kang–Kashiwara weight is nonpositive, since `E F (S) = 0` while `S ≠ 0`
  have hwt : wt ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    let Pos := originalPositiveEquiv.{u, v, 0} Q i a β hsym hQ ha RD Λ hΛ hdeg M hpos.le
    let d0 : Fin (wt).toNat := ⟨0, by omega⟩
    have h0 := Pos.injective (a₁ := (0, Pi.single d0 (1 : S))) (a₂ := 0) (Subsingleton.elim _ _)
    have h1 := congrArg (fun z => z.2 d0) h0
    simp only [Pi.single_eq_same, Prod.snd_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  let FEF := restrictionFunctor.{u, v, 0} Q i a β ⋙ inductionFunctor.{u, v, 0} Q i a β
  let c : ℕ → (FEF.obj M →ₗ[S] S) := fun d => ((dottedCounit.{u, v, 0} Q i a β d).app M).hom
  let Neg := originalNegativeEquiv.{u, v, 0} Q i a β hsym hQ ha RD Λ hΛ hdeg M hwt
  have hNeg (t : FEF.obj M) : Neg t = (0, fun d : Fin h => c d t) := by
    rw [originalNegativeEquiv_apply]
    exact Prod.ext (Subsingleton.elim _ _) rfl
  -- the inverse generators
  let g : Fin h → FEF.obj M := fun d => Neg.symm (0, Pi.single d 1)
  have hg (d d' : Fin h) : c d' (g d) = (Pi.single d (1 : S) : Fin h → S) d' := by
    have := congrArg (fun z => z.2 d') (Neg.apply_symm_apply (0, Pi.single d 1))
    simpa only [hNeg] using this
  have hexp (t : FEF.obj M) : t = ∑ d : Fin h, c d t • g d := by
    apply Neg.injective
    rw [map_sum, hNeg]
    simp only [map_smul, g, Neg.apply_symm_apply]
    refine Prod.ext (Subsingleton.elim _ _) ?_
    funext d'
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single d']
    · rw [Pi.single_eq_same, mul_one]
    · intro d _ hd
      rw [Pi.single_eq_of_ne (Ne.symm hd), mul_zero]
    · simp
  -- the coefficients of the counit with `h` dots are central
  have hcentral (d : Fin h) (y : S) : c h (g d) * y = y * c h (g d) := by
    let ρ : M ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton S S y)
    have hnat (e : ℕ) (t : FEF.obj M) : c e (FEF.map ρ t) = c e t * y := by
      exact congrArg (fun f => f.hom t) ((dottedCounit.{u, v, 0} Q i a β e).naturality ρ)
    have hρ : FEF.map ρ (g d) = y • g d := by
      apply Neg.injective
      rw [hNeg, map_smul, Neg.apply_symm_apply]
      refine Prod.ext (Subsingleton.elim _ _) ?_
      funext d'
      change c d' (FEF.map ρ (g d)) = y • (Pi.single d (1 : S) : Fin h → S) d'
      rw [hnat, hg]
      by_cases hdd : d' = d
      · subst hdd
        rw [Pi.single_eq_same, one_mul, smul_eq_mul, mul_one]
      · rw [Pi.single_eq_of_ne hdd, zero_mul, smul_zero]
    rw [← hnat, hρ, map_smul, smul_eq_mul]
  choose κ hκ using fun d : Fin h => hcen (c h (g d)) (hcentral d)
  -- evaluate on the generator `e(β,i) ⊗ e(β,i)`
  let m : (restrictionFunctor.{u, v, 0} Q i a β).obj M := ⟨el, lastIdem_mul Q i a β⟩
  let t₀ : FEF.obj M := BalancedTensor.tmul (indGenerator Q i a β) m
  have hct (e : ℕ) : c e t₀ = xl ^ e * el := by
    change (dottedCounit.{u, v, 0} Q i a β e).app M (BalancedTensor.tmul (indGenerator Q i a β) m)
      = _
    rw [dottedCounit_tmul]
    change (el * xl ^ e) * el = _
    have hcomm : Commute (xl ^ e) el := (dot_commute Q i a β 1).pow_left e
    rw [← hcomm.eq, mul_assoc, lastIdem_mul]
  let p : Polynomial k := Polynomial.X ^ h - ∑ d : Fin h, Polynomial.C (κ d) * Polynomial.X ^ (d : ℕ)
  have hpm : p.Monic := by
    apply Polynomial.monic_X_pow_sub
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro d _
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast d.isLt)
  have hpd : p.natDegree = h := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Polynomial.degree_X_pow, Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro d _
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast d.isLt)
  have hpe : Polynomial.aeval xl p * el = 0 := by
    have hrel := congrArg (c h) (hexp t₀)
    rw [map_sum] at hrel
    simp only [map_smul, smul_eq_mul, hκ, hct] at hrel
    simp only [p, map_sub, map_sum, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      sub_mul, Finset.sum_mul]
    rw [sub_eq_zero, hrel]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.commutes, mul_assoc]
  obtain ⟨N, hN⟩ := hnil
  have hN' : xl ^ N * el = 0 := by
    have hcomm : Commute xl el := dot_commute Q i a β 1
    rcases N with _ | N
    · have h1 : (1 : S) = 0 := by rw [pow_zero] at hN; exact hN
      rw [← mul_one (xl ^ 0 * el), h1, mul_zero]
    · have hel : IsIdempotentElem el := lastIdem_mul Q i a β
      rw [hcomm.mul_pow, hel.pow_succ_eq] at hN
      exact hN
  have := pow_mul_eq_zero_of_monic xl el p hpm hpe N hN'
  rwa [hpd] at this

end Categorification.KLR.KLRAlgebra.AbsentColour
