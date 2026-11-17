/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedInduction
import Categorification.KLR.CyclotomicNilpotent
import Categorification.KLR.CyclotomicTruncation
import Categorification.KLR.Rouquier.Polynomial
import Categorification.KLR.Rouquier.Coefficient

/-!
# Local nilpotence of lowering in cyclotomic blocks

Kang–Kashiwara, arXiv:1102.4677v4, §4.1 and §6, Theorem 6.2, and Webster,
arXiv:1309.3796v2, Proposition 3.21. For monomial cyclotomic parameters,
the dot nilpotence induction of Brundan–Kleshchev, arXiv:0808.2032v3,
Lemma 2.1, gives bounds independent of the total weight when the set of colours
and dot position are fixed. A long word with boundedly many strands different
from a fixed colour has a constant block longer than its initial dot bound.
-/

namespace Categorification.KLR.IsRouquierQ

open QuantumGroup MvPolynomial
variable {I k : Type*} [CommRing k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k}

/-- For Rouquier's homogeneous parameters the second-variable specialization is
the pure power with the invertible leading coefficient of the reversed pair
(Rouquier, arXiv:0812.5023v1, §3.2.3). -/
theorem aeval_zero_first (hQ : IsRouquierQ C Q) (i j : I) (hij : i ≠ j) :
    ∃ (c : k) (d : ℕ), IsUnit c ∧
      aeval (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * X 1 ^ d := by
  classical
  let u := Finsupp.single (0 : Fin 2) (C.dij j i)
  refine ⟨_, C.dij j i, hQ.unit_coeff j i hij.symm, ?_⟩
  rw [← hQ.symm j i hij.symm, aeval_rename]
  let v : Fin 2 → MvPolynomial (Fin 2) k := ![X 1, 0]
  have hv : (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k) ∘ ![1, 0] = v := by
    funext z
    fin_cases z <;> rfl
  rw [hv]
  have he (s : Fin 2 →₀ ℕ) : aeval v (monomial s (1 : k)) =
      (X 1 : MvPolynomial (Fin 2) k) ^ s 0 * 0 ^ s 1 := by
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp [v, Fin.prod_univ_two]
  change (aeval v).toLinearMap (Q j i) = _
  rw [Rouquier.map_eq_coeff_smul _ _ u (X 1 ^ C.dij j i) (by
    intro s hs
    change aeval v (monomial s 1) = _
    rw [he]
    by_cases hz : s 1 = 0
    · have hw := hQ.homogeneous j i hij.symm (mem_support_iff.mp hs)
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hw
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hz, nsmul_eq_mul,
        Nat.cast_zero, zero_mul, add_zero] at hw
      have h0 : s 0 = C.dij j i := by
        exact_mod_cast (mul_left_inj' (C.dot_self_pos j).ne').1
          (hw.trans (C.dij_mul hij.symm).symm)
      have hu : s = u := by
        ext t
        fin_cases t <;> simp [u, h0, hz]
      simp [hu, u]
    · have hu : s ≠ u := by
        intro h
        exact hz (by simp [h,u])
      simp [hu, zero_pow hz])]
  exact smul_eq_C_mul _ _
end Categorification.KLR.IsRouquierQ

namespace Categorification.KLR.CycKLR

open KLRAlgebra Polynomial Categorification.Graded

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : I → ℕ)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)

section Dots

variable (hQ : ∀ a b : I, a ≠ b → ∃ (c : k) (d : ℕ), IsUnit c ∧
  MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q a b) =
    MvPolynomial.C c * MvPolynomial.X 1 ^ d)

private theorem next_uniform_smul {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M]
    (B : ℕ) (hB : ∀ i ∈ ν, ∀ j ∈ ν, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d ∧ d ≤ B)
    (b N : ℕ) (hb : b+1 < ν.card) (hN : ∀ v : M,
      (pol (MvPolynomial.X ⟨b, by omega⟩ ^ N) : KLRAlgebra k Q ν) • v = 0) (v : M) :
    (pol (MvPolynomial.X ⟨b+1, hb⟩ ^ max N (N*(N+B))) : KLRAlgebra k Q ν) • v = 0 := by
  have hl (s : Seq ν) :
      (MvPolynomial.X ⟨b+1, hb⟩ : MvPolynomial (Fin ν.card) k) ^ max N (N * (N+B)) ∈ annE (Q := Q) M s := by
    let i := s.lbl ⟨b, by omega⟩
    let j := s.lbl ⟨b+1, hb⟩
    have inc {L : ℕ} (h : L ≤ max N (N * (N+B)))
        (hmem : (MvPolynomial.X ⟨b+1, hb⟩ : MvPolynomial (Fin ν.card) k) ^ L ∈ annE (Q := Q) M s) :
        (MvPolynomial.X ⟨b+1, hb⟩ : MvPolynomial (Fin ν.card) k) ^ max N (N * (N+B)) ∈ annE (Q := Q) M s := by
      rw [← Nat.sub_add_cancel h, pow_add]
      exact Ideal.mul_mem_left _ _ hmem
    by_cases he : i = j
    · exact inc (le_max_left ..) (next_pow_mem_annE_of_eq b hb N hN s he)
    · obtain ⟨c, d, hc, hcd, hd⟩ := hB i (s.mem _) j (s.mem _) he
      exact inc ((Nat.mul_le_mul_left N (Nat.add_le_add_left hd _)).trans (le_max_right ..))
        (next_pow_mem_annE_of_ne b hb N hN s he c d hc hcd)
  exact smul_eq_zero_of_mul_e _ (fun s => hl s) v

include hQ in
/-- Fixing the finite set of colours makes the annihilating power of the dot at
each position uniform over all word lengths. This is the quantitative induction
in Brundan–Kleshchev, arXiv:0808.2032v3, Lemma 2.1. -/
theorem exists_uniform_dot_pow (S : Finset I) :
    ∃ L : ℕ → ℕ, ∀ {ν : Multiset I}, ν.toFinset ⊆ S → ∀ p : Fin ν.card,
      (mk k Q aΛ ν (x p)) ^ L p.val = 0 := by
  classical
  choose c d hc hcd using hQ
  let D (i j : I) := if h : i ≠ j then d i j h else 0
  let B := S.sup fun i => S.sup (D i)
  let L (p : ℕ) : ℕ := Nat.rec (S.sup Λ) (fun _ N => max N (N * (N+B))) p
  refine ⟨L, ?_⟩
  intro ν hν p
  let R := CycKLR k Q aΛ ν
  let π := mk k Q aΛ ν
  let _ : Module (KLRAlgebra k Q ν) R := Module.compHom _ π.toRingHom
  have hpow (b : ℕ) (hb : b < ν.card) : π (x ⟨b, hb⟩) ^ L b = 0 := by
    induction b with
    | zero => exact pow_eq_zero_of_le (Finset.sup_mono hν) (x_zero_pow_eq_zero Λ hb)
    | succ b ih =>
      have hN (v : R) : (pol (MvPolynomial.X ⟨b, by omega⟩ ^ L b) : KLRAlgebra k Q ν) • v = 0 := by
        change π _ * v = 0
        rw [map_pow, pol_X, map_pow, ih (by omega), zero_mul]
      have hB (i : I) (hi : i ∈ ν) (j : I) (hj : j ∈ ν) (he : i ≠ j) :
          ∃ (c : k) (d : ℕ), IsUnit c ∧
            MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
              MvPolynomial.C c * MvPolynomial.X 1 ^ d ∧ d ≤ B := by
        refine ⟨_, _, hc i j he, hcd i j he, ?_⟩
        have h := (Finset.le_sup (f := D i) (hν (Multiset.mem_toFinset.mpr hj))).trans
          (Finset.le_sup (f := fun t => S.sup (D t)) (hν (Multiset.mem_toFinset.mpr hi)))
        simpa only [D, dite_eq_left he] using h
      have hh := next_uniform_smul (Q := Q) B hB b (L b) hb hN (1 : R)
      change π _ * 1 = 0 at hh
      rwa [mul_one, map_pow, pol_X, map_pow] at hh
  exact hpow p.val p.isLt

end Dots

private theorem exists_long_constant_block (L : ℕ → ℕ) (i : I) (t : ℕ) :
    ∃ B : ℕ, ∀ {ν : Multiset I} (s : Seq ν),
      (ν.filter (· ≠ i)).card ≤ t → B ≤ ν.card →
      ∃ p : ℕ, p + (L p + 1) ≤ ν.card ∧ IsConstOn s p (L p + 1) := by
  classical
  let start : ℕ → ℕ := Nat.rec 0 fun _ p => p + (L p + 1)
  have step (r : ℕ) : start (r+1) = start r + (L (start r)+1) := rfl
  have mono : StrictMono start := strictMono_nat_of_lt_succ fun r => by rw [step]; omega
  refine ⟨start (t+1), ?_⟩
  intro ν s ht hlen
  by_contra! h
  have bad (r : Fin (t+1)) : ∃ a : Fin ν.card,
      start r ≤ a.val ∧ a.val < start (r.val+1) ∧ s.lbl a ≠ i := by
    by_contra! none
    have hu := (mono.monotone (show r.val + 1 ≤ t+1 by omega)).trans hlen
    apply h (start r) ((step r).symm ▸ hu)
    intro a b ha ha' hb hb'
    exact (none a ha (step r ▸ ha')).trans (none b hb (step r ▸ hb')).symm
  choose a ha hb hc using bad
  let f (r : Fin (t+1)) : {b : Fin ν.card // s.lbl b ≠ i} := ⟨a r, hc r⟩
  have hinj : Function.Injective f := by
    have hlt {r u : Fin (t+1)} (hru : r < u) : (a r).val < (a u).val :=
      (hb r).trans_le ((mono.monotone (show r.val+1 ≤ u.val from hru)).trans (ha u))
    intro r u he
    have he' := congrArg (fun b : {b : Fin ν.card // s.lbl b ≠ i} => b.1.val) he
    rcases lt_trichotomy r u with h | h | h
    · exact ((hlt h).ne he').elim
    · exact h
    · exact ((hlt h).ne he'.symm).elim
  have hcard := Fintype.card_le_of_injective f hinj
  have hc' : Fintype.card {b : Fin ν.card // s.lbl b ≠ i} = (ν.filter (· ≠ i)).card := by
    have h := congrArg (fun v : Multiset I => (v.filter (· ≠ i)).card) s.2
    simp only [Multiset.filter_map, Multiset.card_map] at h
    rw [Fintype.card_subtype]
    exact h
  rw [Fintype.card_fin, hc'] at hcard
  omega

section Lower

variable (hQ : ∀ a b : I, a ≠ b → ∃ (c : k) (d : ℕ), IsUnit c ∧
  MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q a b) =
    MvPolynomial.C c * MvPolynomial.X 1 ^ d)

include hQ in
/-- With the other strands fixed, adjoining sufficiently many strands of one
colour gives the zero cyclotomic algebra. This yields the lowering part of
integrability for Kang–Kashiwara, arXiv:1102.4677v4, §6, Theorem 6.2. -/
theorem eventually_subsingleton_replicate_add (i : I) (β : Multiset I) :
    ∃ B : ℕ, ∀ n ≥ B, Subsingleton (CycKLR k Q aΛ (Multiset.replicate n i + β)) := by
  classical
  let S := insert i β.toFinset
  obtain ⟨L, hL⟩ := exists_uniform_dot_pow Λ hQ S
  obtain ⟨B, hB⟩ := exists_long_constant_block L i β.card
  refine ⟨B, ?_⟩
  intro n hn
  let ν := Multiset.replicate n i + β
  have hν : ν.toFinset ⊆ S := by
    intro j hj
    rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hj) with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Multiset.eq_of_mem_replicate h))
    · exact Finset.mem_insert.mpr (Or.inr (Multiset.mem_toFinset.mpr h))
  have hrep (r : ℕ) : (Multiset.replicate r i).filter (· ≠ i) = 0 := by
    induction r with
    | zero => simp
    | succ r ih => simp [ih]
  have hcount : (ν.filter (· ≠ i)).card ≤ β.card := by
    simp only [ν, Multiset.filter_add, hrep, zero_add]
    exact Multiset.card_le_card (Multiset.filter_le ..)
  have hlen : B ≤ ν.card := by simp [ν]; omega
  have he (s : Seq ν) : mk k Q aΛ ν (e s) = 0 := by
    obtain ⟨p, hpn, hc⟩ := hB s hcount hlen
    apply map_e_eq_zero_of_block_dot_pow (mk k Q aΛ ν).toRingHom s p (L p) hpn hc
    change mk k Q aΛ ν _ = 0
    rw [map_mul, map_pow, hL hν (⟨p, by omega⟩ : Fin ν.card), zero_mul]
  apply subsingleton_of_zero_eq_one
  have hsum := congrArg (mk k Q aΛ ν) (sum_e (Q := Q) (ν := ν))
  simpa [map_sum, he] using hsum

variable (G : GradingDatum Q)
local notation "LP" => LaurentPolynomial ℤ

private theorem lower_pow_mem_block (i : I) (β : Multiset I) (x : K0 (grade G Λ β)) (n : ℕ) :
    ∃ y : K0 (grade G Λ (Multiset.replicate n i + β)),
      (lower G Λ i ^ n) (DirectSum.lof LP _ _ β x) =
        DirectSum.lof LP _ _ (Multiset.replicate n i + β) y := by
  induction n with
  | zero =>
    rw [Multiset.replicate_zero, zero_add, pow_zero, Module.End.one_apply]
    exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    rw [pow_succ', Module.End.mul_apply, hy, lower_lof]
    rw [Multiset.replicate_succ, ← Multiset.singleton_add, add_assoc]
    exact ⟨_, rfl⟩

private theorem k0_eq_zero_of_subsingleton {ν : Multiset I} [Subsingleton (CycKLR k Q aΛ ν)]
    (x : K0 (grade G Λ ν)) : x = 0 := by
  induction x using K0.induction_on with
  | of P =>
    let := Module.subsingleton (CycKLR k Q aΛ ν) P.carrier
    have e : P.Iso (P.prod P) :=
      GradedEquiv.ofLinearMaps (M := P.carrier) (N := P.carrier × P.carrier)
        (LinearMap.prod LinearMap.id LinearMap.id) (LinearMap.fst _ P.carrier P.carrier)
        (fun _ => rfl) (fun _ => Subsingleton.elim _ _) (fun _ _ hx => ⟨hx, hx⟩)
        (fun _ _ hx => hx.1)
    have h := K0.of_eq_of_iso e
    rw [K0.of_prod] at h
    simpa using h
  | zero => rfl
  | add _ _ hx hy => simp [hx, hy]
  | neg _ hx => simp [hx]

/-- The highest-weight power relation on the vacuum block for the integral
cyclotomic projective group (Webster, arXiv:1309.3796v2, Proposition 3.21).
The exponent is one more than the highest-weight multiplicity. -/
theorem lower_pow_vacuum_eq_zero (i : I) (x : K0 (grade G Λ 0)) :
    (lower G Λ i ^ (Λ i + 1)) (DirectSum.lof LP _ _ 0 x) = 0 := by
  obtain ⟨y, hy⟩ := lower_pow_mem_block Λ G i 0 x (Λ i + 1)
  let : Subsingleton (CycKLR k Q aΛ (Multiset.replicate (Λ i + 1) i + 0)) := by
    rw [add_zero]
    exact subsingleton_replicate_of_lt Q Λ i _ (Nat.lt_succ_self _)
  rw [hy, k0_eq_zero_of_subsingleton Λ G y, map_zero]

include hQ in
/-- Induction at each colour is locally nilpotent on the full projective
Grothendieck group of the undeformed cyclotomic algebra (Kang–Kashiwara,
arXiv:1102.4677v4, §6, Theorem 6.2). -/
theorem lower_locally_nilpotent (i : I) (x : projectiveK0 G Λ) :
    ∃ n : ℕ, (lower G Λ i ^ n) x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact ⟨1, map_zero _⟩
  | of β x =>
    obtain ⟨B, hB⟩ := eventually_subsingleton_replicate_add Λ hQ i β
    let := hB B le_rfl
    obtain ⟨y, hy⟩ := lower_pow_mem_block Λ G i β x B
    exact ⟨B, hy.trans (by rw [k0_eq_zero_of_subsingleton Λ G y, map_zero])⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m+n, ?_⟩
    rw [map_add]
    conv_lhs =>
      lhs
      rw [Nat.add_comm, pow_add, Module.End.mul_apply, hm, map_zero]
    rw [pow_add, Module.End.mul_apply, hn, map_zero, add_zero]

end Lower

end Categorification.KLR.CycKLR
