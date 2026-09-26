/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Injectivity

/-!
# KL III Proposition 3.12, Corollary 3.13 and nondegeneracy

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3
("Spanning sets for general `𝐢` and `𝐣`", TeX lines 4470–4632):

* the spanning set `B_{𝐢,𝐣,λ}`: for each `(𝐢, 𝐣)`-pairing its minimal diagram `D`, an arbitrary
  number of dots on each strand, and a bubble monomial of `Π_λ` to the right;
* **Proposition 3.11** (TeX l. 4568): `B_{𝐢,𝐣,λ}` spans `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`;
* **Proposition 3.12** (`eq_pi_bi_s`, l. 4582): `π (E_𝐢 1_λ, E_𝐣 1_λ) = Σ_{s ∈ B} q^{deg s}`;
* eq. (3.68) (`eq_another_equality`): `gdim HOM = Σ_{s ∈ B} q^{deg s}` iff `B` is a basis;
* **Corollary 3.13** (`cor-ineq`): `gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) ≤ π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`;
* the definition of nondegeneracy and "a calculus is nondegenerate iff the equality holds in
  Corollary 3.13 for all `𝐢, 𝐣, λ`".

## The index set `B_{𝐢,𝐣,λ}` and Proposition 3.12

The elements of `B_{𝐢,𝐣,λ}` are indexed by `SpanIdx s t`: a pairing `D ∈ p(𝐢, 𝐣)`
(`QuantumGroup.UDot.pairings`), a number of dots on each strand of `D` (a function on the strands
`Arc D`, the cups `(a, D a)`, `a < D a`, of the boundary word), and a monomial in the generators
`(i, α)` of `Π_λ` (`(I × ℕ) →₀ ℕ`). Its degree (`spanDeg`, KL III: "determined by the rules in
Section 3.1") is `deg(D, λ) + Σ_strands (#dots)(i·i) + deg(monomial)`: a dot on an `i`-strand
has degree `i·i`, the generator `(i, α)` of `Π_λ` degree `(α + 1)(i·i)` (`wPi`), and the minimal
diagram `D` the degree `deg(D, λ) = QuantumGroup.UDot.pdeg` of Theorem 2.7. (That the degree of
the minimal diagram of `U` agrees with `pdeg`: the degrees of cups, caps and crossings in
`Categorification.Diagrams.KL3.Grading` (`deg_cup_FE`, `deg_cap_EF`, …) are those of the table in
KL III §2.2 used for `pdeg`.)

**Proposition 3.12** (`prop_3_12`): for every `d`, the number of elements of `B_{𝐢,𝐣,λ}` of degree
`d` is finite and equals the coefficient of `q^d` in `π (E_𝐢 1_λ, E_𝐣 1_λ)` (`I` finite). The
proof is KL III's: Theorem 2.7, `Σ_{a ≥ 0} q^{a (i·i)} = 1/(1 - q_i²)` for the dots on an
`i`-strand, and `π` for the bubble monomials.

## Corollary 3.13 and nondegeneracy, given Proposition 3.11

Proposition 3.11 is **not** proved here. We formulate it as a hypothesis `Prop311 RD k` (for all
`λ, 𝐢, 𝐣` there is a family of homogeneous elements of `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)` indexed by
`SpanIdx`, of degrees `spanDeg`, spanning every graded piece — the family of diagrams of
`B_{𝐢,𝐣,λ}` being the one KL III construct), and prove:

* `cor_3_13` — Corollary 3.13, given `Prop311`;
* `finrank_eq_iff_linearIndependent` — eq. (3.68) for any such family: equality of the
  dimensions with the counts in degree `d` iff the family is linearly independent in degree `d`;
* `calculusNondeg_iff` — given `Prop311`, `CalculusNondeg RD k` (the equality form of
  nondegeneracy used for Theorem 1.2) holds iff every such spanning family is a basis in every
  degree, i.e. KL III's definition.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Module Finset

universe w u v

/-! ## Counting -/

section Count

/-- The solutions of `f a + g b = n`, sorted by `(f a, g b)`. -/
def addEqEquiv {α β : Type*} (f : α → ℕ) (g : β → ℕ) (n : ℕ) :
    {p : α × β // f p.1 + g p.2 = n} ≃
      Σ q : antidiagonal n, {a // f a = q.1.1} × {b // g b = q.1.2} where
  toFun p := ⟨⟨(f p.1.1, g p.1.2), mem_antidiagonal.2 p.2⟩, ⟨p.1.1, rfl⟩, ⟨p.1.2, rfl⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by rw [x.2.1.2, x.2.2.2]; exact mem_antidiagonal.1 x.1.2⟩
  left_inv p := rfl
  right_inv := by
    rintro ⟨⟨⟨i, j⟩, hq⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    dsimp only at ha hb
    subst ha; subst hb
    rfl

theorem finite_add_eq {α β : Type*} (f : α → ℕ) (g : β → ℕ) (n : ℕ)
    [hf : ∀ i, Finite {a // f a = i}] [hg : ∀ j, Finite {b // g b = j}] :
    Finite {p : α × β // f p.1 + g p.2 = n} :=
  Finite.of_equiv _ (addEqEquiv f g n).symm

/-- `Nat.card` of the solutions of `f a + g b = n` is the convolution of the counts. -/
theorem card_add_eq {α β : Type*} (f : α → ℕ) (g : β → ℕ) (n : ℕ)
    [hf : ∀ i, Finite {a // f a = i}] [hg : ∀ j, Finite {b // g b = j}] :
    Nat.card {p : α × β // f p.1 + g p.2 = n} =
      ∑ q ∈ antidiagonal n, Nat.card {a // f a = q.1} * Nat.card {b // g b = q.2} := by
  rw [Nat.card_congr (addEqEquiv f g n), Nat.card_sigma]
  simp only [Nat.card_prod]
  exact (Finset.sum_coe_sort (antidiagonal n)
    (fun q => Nat.card {a // f a = q.1} * Nat.card {b // g b = q.2}))

/-- The geometric series `Σ_a q^{a w}`. -/
def geomPS (w : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => if w ∣ n then 1 else 0

theorem card_mul_eq (w n : ℕ) (hw : 0 < w) :
    (Nat.card {a : ℕ // a * w = n} : ℚ) = PowerSeries.coeff ℚ n (geomPS w) := by
  rw [geomPS, PowerSeries.coeff_mk]
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    have hs : Subsingleton {a : ℕ // a * w = w * c} :=
      ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext (Nat.eq_of_mul_eq_mul_right hw (ha.trans hb.symm))⟩
    have hn : Nonempty {a : ℕ // a * w = w * c} := ⟨⟨c, mul_comm c w⟩⟩
    rw [Nat.card_eq_one_iff_unique.2 ⟨hs, hn⟩]; simp
  · have : IsEmpty {a : ℕ // a * w = n} := ⟨fun ⟨a, ha⟩ => h ⟨a, by rw [← ha, mul_comm]⟩⟩
    rw [Nat.card_of_isEmpty]; simp

theorem finite_dots {A : Type*} [Fintype A] (w : A → ℕ) (hw : ∀ x, 0 < w x) (n : ℕ) :
    Finite {a : A → ℕ // ∑ x, a x * w x = n} := by
  refine Finite.of_injective (β := A → Fin (n + 1))
    (fun a x => ⟨a.1 x, Nat.lt_succ_of_le ?_⟩) (fun a b h => Subtype.ext (funext fun x => ?_))
  · have h1 : a.1 x * w x ≤ n := le_of_le_of_eq
      (Finset.single_le_sum (f := fun y => a.1 y * w y) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x)) a.2
    have := hw x
    nlinarith
  · have := congrFun h x
    simpa using congrArg Fin.val this

/-- **Counting dots**: the number of ways to put dots on strands of degrees `w x` with total
degree `n` is the coefficient of `q^n` in `∏_x Σ_a q^{a w x}`. -/
theorem card_dots (A : Type*) [Fintype A] (w : A → ℕ) (hw : ∀ x, 0 < w x) (n : ℕ) :
    (Nat.card {a : A → ℕ // ∑ x, a x * w x = n} : ℚ) =
      PowerSeries.coeff ℚ n (∏ x, geomPS (w x)) := by
  revert w n
  refine (Fintype.induction_empty_option (P := fun A _ => ∀ (w : A → ℕ), (∀ x, 0 < w x) → ∀ n,
    (Nat.card {a : A → ℕ // ∑ x, a x * w x = n} : ℚ) =
      PowerSeries.coeff ℚ n (∏ x, geomPS (w x))) ?_ ?_ ?_) A
  · intro α β _ e ih w hw n
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (w ∘ e) (fun x => hw _) n
    have e2 : {a : β → ℕ // ∑ x, a x * w x = n} ≃ {a : α → ℕ // ∑ x, a x * (w ∘ e) x = n} :=
      (e.arrowCongr (Equiv.refl ℕ)).symm.subtypeEquiv fun a => by
        simp only [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
          Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply, id]
        rw [← Equiv.sum_comp e]
    rw [Nat.card_congr e2, h, ← Equiv.prod_comp e]
    rfl
  · intro w _ n
    rw [Finset.univ_eq_empty, Finset.prod_empty, PowerSeries.coeff_one]
    simp only [Finset.sum_empty]
    split_ifs with h
    · subst h
      have : Unique {a : PEmpty → ℕ // (0 : ℕ) = 0} := ⟨⟨⟨fun x => x.elim, rfl⟩⟩,
        fun a => Subtype.ext (funext fun x => x.elim)⟩
      rw [Nat.card_unique]; simp
    · have : IsEmpty {a : PEmpty → ℕ // (0 : ℕ) = n} := ⟨fun a => h a.2.symm⟩
      rw [Nat.card_of_isEmpty]; simp
  · intro α _ ih w hw n
    have e : {a : Option α → ℕ // ∑ x, a x * w x = n} ≃
        {p : ℕ × (α → ℕ) // p.1 * w none + ∑ x, p.2 x * w (some x) = n} :=
      (Equiv.piOptionEquivProd (β := fun _ => ℕ)).subtypeEquiv fun a => by
        simp [Fintype.sum_option]
    haveI : ∀ i, Finite {a0 : ℕ // a0 * w none = i} := fun i =>
      @Finite.of_subsingleton _ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ =>
        Subtype.ext (Nat.eq_of_mul_eq_mul_right (hw none) (ha.trans hb.symm))⟩
    haveI : ∀ j, Finite {a : α → ℕ // ∑ x, a x * w (some x) = j} := fun j =>
      finite_dots (fun x => w (some x)) (fun x => hw _) j
    rw [Nat.card_congr e, card_add_eq (fun a0 => a0 * w none)
      (fun a : α → ℕ => ∑ x, a x * w (some x)) n, Fintype.prod_option, PowerSeries.coeff_mul]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [card_mul_eq _ _ (hw none), ih (fun x => w (some x)) (fun x => hw _)]

end Count

/-! ## Laurent expansions of the factors -/

section Series

theorem coeff_ofPS (F : PowerSeries ℚ) (e : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℚ F).coeff e =
      if 0 ≤ e then PowerSeries.coeff ℚ e.toNat F else 0 := by
  split_ifs with h
  · conv_lhs => rw [← Int.toNat_of_nonneg h]
    exact HahnSeries.ofPowerSeries_apply_coeff F e.toNat
  · rw [HahnSeries.ofPowerSeries_apply]
    refine HahnSeries.embDomain_notin_range ?_
    rintro ⟨m, hm⟩
    exact h (by rw [← hm]; exact Int.natCast_nonneg m)

theorem one_sub_X_pow_mul_geomPS (w : ℕ) (hw : 0 < w) :
    (1 - PowerSeries.X ^ w) * geomPS w = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one, geomPS,
    PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.2 hw]
  · rw [if_neg hn.ne']
    by_cases hwn : w ≤ n
    · have e : n = (n - w) + w := (Nat.sub_add_cancel hwn).symm
      have hiff : w ∣ n ↔ w ∣ n - w := by
        conv_lhs => rw [e]
        exact Nat.dvd_add_self_right
      rw [if_pos hwn]
      by_cases hd : w ∣ n
      · rw [if_pos hd, PowerSeries.coeff_mk, if_pos (hiff.1 hd), sub_self]
      · rw [if_neg hd, PowerSeries.coeff_mk, if_neg (fun h => hd (hiff.2 h)), sub_self]
    · rw [if_neg hwn, if_neg (Nat.not_dvd_of_pos_of_lt hn (lt_of_not_le hwn)), sub_self]

variable {I : Type u} {C : CartanDatum I}

theorem dot_self_toNat_pos (i : I) : 0 < (C.dot i i).toNat := by
  have := C.dot_self_pos i; omega

/-- `1/(1 - q_i²) = Σ_a q^{a (i·i)}`: the generating function of the dots on an `i`-strand. -/
theorem toLS_cK (i : I) :
    toLS (KL3.cK C i) = HahnSeries.ofPowerSeries ℤ ℚ (geomPS (C.dot i i).toNat) := by
  have hq : toLS ((qi C KL3.qK i : (RatFunc ℚ)ˣ) : RatFunc ℚ) = HahnSeries.single (di C i) 1 :=
    toLS_vQ_zpow (di C i)
  have hX : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X ^ (C.dot i i).toNat) =
      HahnSeries.single (2 * di C i) 1 := by
    rw [HahnSeries.ofPowerSeries_X_pow, two_mul_di, Int.toNat_of_nonneg (C.dot_self_pos i).le]
  have h1 : toLS (1 - ((qi C KL3.qK i : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ 2) =
      HahnSeries.ofPowerSeries ℤ ℚ (1 - PowerSeries.X ^ (C.dot i i).toNat) := by
    rw [map_sub, map_one, map_pow, hq, HahnSeries.single_pow, map_sub, hX,
      map_one (HahnSeries.ofPowerSeries ℤ ℚ), one_pow, nsmul_eq_mul]
    push_cast; rfl
  rw [KL3.cK, map_inv₀, h1]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, one_sub_X_pow_mul_geomPS _ (dot_self_toNat_pos i), map_one]

end Series

/-! ## The index set `B_{𝐢,𝐣,λ}` -/

section SpanIdx

variable {I : Type u} (C : CartanDatum I)

/-- The strands of the minimal diagram of the pairing `σ` (the cups `(a, σ a)`, `a < σ a`, of the
boundary word `ρW(s) t`). -/
abbrev Arc (s t : List (Bool × I)) (σ : Equiv.Perm (Fin (ρW s ++ t).length)) : Type :=
  {a : Fin (ρW s ++ t).length // a < σ a}

/-- The colour of a strand. -/
def arcCol {s t : List (Bool × I)} {σ : Equiv.Perm (Fin (ρW s ++ t).length)} (x : Arc s t σ) : I :=
  ((ρW s ++ t).get x.1).2

/-- **The index set of `B_{𝐢,𝐣,λ}`** (KL III §3.2.3): a pairing `D ∈ p(𝐢, 𝐣)`, a number of dots on
each strand of `D`, and a monomial in the generators `(i, α)` of `Π_λ`. -/
def SpanIdx (s t : List (Bool × I)) : Type u :=
  Σ σ : {σ // σ ∈ pairings s t}, (Arc s t σ.1 → ℕ) × ((I × ℕ) →₀ ℕ)

/-- **The degree of an element of `B_{𝐢,𝐣,λ}`**: `deg(D, λ)` plus `i·i` for each dot on an
`i`-strand plus the degree of the bubble monomial. -/
def spanDeg (ℓ : I → ℤ) {s t : List (Bool × I)} (b : SpanIdx s t) : ℤ :=
  pdeg C ℓ s t b.1.1 + (∑ x, (b.2.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) +
    Finsupp.weight (wPi C) b.2.2

end SpanIdx

section Prop312

variable {I : Type u} {C : CartanDatum I} [Finite I]

/-- The degree of a strand's dots, as a natural number. -/
abbrev dotW {s t : List (Bool × I)} {σ : Equiv.Perm (Fin (ρW s ++ t).length)} (x : Arc s t σ) : ℕ :=
  (C.dot (arcCol x) (arcCol x)).toNat

omit [Finite I] in
theorem weight_toNat (m : (I × ℕ) →₀ ℕ) :
    ((Finsupp.weight (wPi C) m).toNat : ℤ) = Finsupp.weight (wPi C) m :=
  Int.toNat_of_nonneg (weight_wPi_nonneg m)

theorem card_monomials (j : ℕ) :
    Finite {m : (I × ℕ) →₀ ℕ // (Finsupp.weight (wPi C) m).toNat = j} ∧
    (Nat.card {m : (I × ℕ) →₀ ℕ // (Finsupp.weight (wPi C) m).toNat = j} : ℚ) =
      PowerSeries.coeff ℚ j (piPS C) := by
  have e : {m : (I × ℕ) →₀ ℕ // (Finsupp.weight (wPi C) m).toNat = j} ≃ monDeg C (j : ℤ) :=
    Equiv.subtypeEquivRight fun m => by
      simp only [monDeg, Set.mem_setOf_eq]
      rw [← weight_toNat (C := C) m]
      omega
  haveI : Finite (monDeg C (j : ℤ)) := (monDeg_finite (C := C) (j : ℤ)).to_subtype
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Set.Nat.card_coe_set_eq, piPS, PowerSeries.coeff_mk]

variable {s t : List (Bool × I)}

/-- The count of dots and bubble monomials of total degree `e` on the strands of `σ`. -/
theorem card_inner (σ : Equiv.Perm (Fin (ρW s ++ t).length)) (e : ℤ) :
    Finite {p : (Arc s t σ → ℕ) × ((I × ℕ) →₀ ℕ) //
      (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 = e} ∧
    (Nat.card {p : (Arc s t σ → ℕ) × ((I × ℕ) →₀ ℕ) //
      (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 = e} : ℚ) =
      (HahnSeries.ofPowerSeries ℤ ℚ ((∏ x : Arc s t σ, geomPS (dotW (C := C) x)) * piPS C)).coeff e := by
  have hW : ∀ x : Arc s t σ, ((dotW (C := C) x : ℕ) : ℤ) = C.dot (arcCol x) (arcCol x) :=
    fun x => Int.toNat_of_nonneg (C.dot_self_pos _).le
  rw [coeff_ofPS]
  split_ifs with he
  · -- nonnegative degree: count in `ℕ`
    have e1 : {p : (Arc s t σ → ℕ) × ((I × ℕ) →₀ ℕ) //
        (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 = e} ≃
        {p : (Arc s t σ → ℕ) × ((I × ℕ) →₀ ℕ) //
          (∑ x, p.1 x * dotW (C := C) x) + (Finsupp.weight (wPi C) p.2).toNat = e.toNat} :=
      Equiv.subtypeEquivRight fun p => by
        have key : (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) =
            ((∑ x, p.1 x * dotW (C := C) x : ℕ) : ℤ) := by
          push_cast; simp only [hW]
        have h1 := weight_toNat (C := C) p.2
        have h2 := Int.toNat_of_nonneg he
        omega
    haveI hf : ∀ i, Finite {a : Arc s t σ → ℕ // ∑ x, a x * dotW (C := C) x = i} := fun i =>
      finite_dots _ (fun x => dot_self_toNat_pos _) i
    haveI hg : ∀ j, Finite {m : (I × ℕ) →₀ ℕ // (Finsupp.weight (wPi C) m).toNat = j} :=
      fun j => (card_monomials j).1
    have hcount := card_add_eq (fun a : Arc s t σ → ℕ => ∑ x, a x * dotW (C := C) x)
      (fun m : (I × ℕ) →₀ ℕ => (Finsupp.weight (wPi C) m).toNat) e.toNat
    refine ⟨?_, ?_⟩
    · haveI := finite_add_eq (fun a : Arc s t σ → ℕ => ∑ x, a x * dotW (C := C) x)
        (fun m : (I × ℕ) →₀ ℕ => (Finsupp.weight (wPi C) m).toNat) e.toNat
      exact Finite.of_equiv _ e1.symm
    · rw [Nat.card_congr e1, hcount, PowerSeries.coeff_mul]
      push_cast
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [card_dots _ _ (fun x => dot_self_toNat_pos _), (card_monomials q.2).2]
  · -- negative degree: no elements
    have hE : IsEmpty {p : (Arc s t σ → ℕ) × ((I × ℕ) →₀ ℕ) //
        (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 = e} := by
      refine ⟨fun p => he ?_⟩
      rw [← p.2]
      refine add_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (Int.natCast_nonneg _)
        (C.dot_self_pos _).le) (weight_wPi_nonneg _)
    exact ⟨inferInstance, by rw [Nat.card_of_isEmpty]; simp⟩

omit [Finite I] in
/-- The strand factor as a product over the strands. -/
theorem pweight_eq {K : Type*} [Field K] (c : I → K) (σ : Equiv.Perm (Fin (ρW s ++ t).length)) :
    pweight c s t σ = ∏ x : Arc s t σ, c (arcCol x) := by
  rw [pweight, arcProd, Finset.prod_ite, Finset.prod_const_one, mul_one]
  exact Finset.prod_subtype _ (fun x => by simp) (fun a => c ((ρW s ++ t).get a).2)

/-- The fibre of `spanDeg` over `d`, sorted by the pairing. -/
def spanFiberEquiv (ℓ : I → ℤ) (d : ℤ) :
    {b : SpanIdx s t // spanDeg C ℓ b = d} ≃
      Σ σ : {σ // σ ∈ pairings s t}, {p : (Arc s t σ.1 → ℕ) × ((I × ℕ) →₀ ℕ) //
        (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 =
          d - pdeg C ℓ s t σ.1} where
  toFun b := ⟨b.1.1, ⟨b.1.2, by have := b.2; simp only [spanDeg] at this; linarith⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by have := x.2.2; simp only [spanDeg]; linarith⟩
  left_inv b := rfl
  right_inv x := rfl

variable {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)

/-- **Khovanov–Lauda III, Proposition 3.12** (`eq_pi_bi_s`): for signed sequences `𝐢 = s`,
`𝐣 = t`, a weight `λ` and every degree `d`, the set of elements of `B_{𝐢,𝐣,λ}` of degree `d` is
finite, and its cardinality is the coefficient of `q^d` in `π (E_𝐢 1_λ, E_𝐣 1_λ)`
(i.e. `π (E_𝐢 1_λ, E_𝐣 1_λ) = Σ_{b ∈ B_{𝐢,𝐣,λ}} q^{deg b}`; `I` finite). -/
theorem prop_3_12 (lam : X) (d : ℤ) :
    Finite {b : SpanIdx s t // spanDeg C (RD.ellOf lam) b = d} ∧
    (Nat.card {b : SpanIdx s t // spanDeg C (RD.ellOf lam) b = d} : ℚ) =
      (piLS C * toLS (UDot.KL3.form RD (E1 RD vQ s lam) (E1 RD vQ t lam))).coeff d := by
  haveI : ∀ σ : {σ // σ ∈ pairings s t}, Finite {p : (Arc s t σ.1 → ℕ) × ((I × ℕ) →₀ ℕ) //
      (∑ x, (p.1 x : ℤ) * C.dot (arcCol x) (arcCol x)) + Finsupp.weight (wPi C) p.2 =
        d - pdeg C (RD.ellOf lam) s t σ.1} := fun σ => (card_inner σ.1 _).1
  refine ⟨Finite.of_equiv _ (spanFiberEquiv (RD.ellOf lam) d).symm, ?_⟩
  rw [Nat.card_congr (spanFiberEquiv (RD.ellOf lam) d), Nat.card_sigma, Nat.cast_sum]
  simp only [fun σ : {σ // σ ∈ pairings s t} => (card_inner (C := C) σ.1 (d - pdeg C (RD.ellOf lam) s t σ.1)).2]
  rw [(UDot.KL3.thm_2_7 C RD s t lam lam).2, if_pos rfl, map_sum, Finset.mul_sum,
    HahnSeries.coeff_sum, ← Finset.sum_coe_sort (pairings s t)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hq : toLS (qp KL3.qK (pdeg C (RD.ellOf lam) s t σ.1)) = HahnSeries.single (pdeg C (RD.ellOf lam) s t σ.1) 1 :=
    toLS_vQ_zpow _
  have hw : toLS (pweight (KL3.cK C) s t σ.1) =
      HahnSeries.ofPowerSeries ℤ ℚ (∏ x : Arc s t σ.1, geomPS (dotW (C := C) x)) := by
    rw [pweight_eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun x _ => toLS_cK _
  rw [map_mul toLS, hq, hw, piLS]
  have e : HahnSeries.ofPowerSeries ℤ ℚ (piPS C) * (HahnSeries.single (pdeg C (RD.ellOf lam) s t σ.1) 1 *
      HahnSeries.ofPowerSeries ℤ ℚ (∏ x : Arc s t σ.1, geomPS (dotW (C := C) x))) =
      HahnSeries.single (pdeg C (RD.ellOf lam) s t σ.1) 1 *
        (HahnSeries.ofPowerSeries ℤ ℚ (∏ x : Arc s t σ.1, geomPS (dotW (C := C) x)) *
          HahnSeries.ofPowerSeries ℤ ℚ (piPS C)) := by ring
  rw [e]
  have := HahnSeries.coeff_single_mul_add (r := (1 : ℚ))
    (x := HahnSeries.ofPowerSeries ℤ ℚ (∏ x : Arc s t σ.1, geomPS (dotW (C := C) x)) *
      HahnSeries.ofPowerSeries ℤ ℚ (piPS C))
    (a := d - pdeg C (RD.ellOf lam) s t σ.1) (b := pdeg C (RD.ellOf lam) s t σ.1)
  rw [sub_add_cancel, one_mul] at this
  rw [this, map_mul]

end Prop312

/-! ## Spanning families, Corollary 3.13 and nondegeneracy -/

section Linear

variable {k : Type w} [Field k]

/-- **KL III eq. (3.68)** for a finite spanning family: the dimension is at most the number of
elements, with equality iff the family is linearly independent. -/
theorem finrank_le_and_iff {V : Type*} [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι]
    (b : ι → V) (W : Submodule k V) (h : Submodule.span k (Set.range b) = W) :
    finrank k W ≤ Fintype.card ι ∧ (finrank k W = Fintype.card ι ↔ LinearIndependent k b) := by
  have e : finrank k W = Set.finrank k (Set.range b) := by rw [Set.finrank, h]
  refine ⟨e ▸ finrank_range_le_card b, ?_⟩
  rw [e, linearIndependent_iff_card_eq_finrank_span, eq_comm]

end Linear

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

variable (RD k) in
/-- `b` is a **graded spanning family of `HOM_U(E_s 1_λ, E_t 1_λ)` indexed by `B_{s,t,λ}`**: each
`b x` is homogeneous of degree `spanDeg x`, and the elements of degree `d` span the degree-`d`
part. -/
def IsSpanFamily (lam : X) (s t : List (Letter I))
    (b : SpanIdx s t → ((pres RD k).obj (ob RD lam s) ⟶ (pres RD k).obj (ob RD lam t))) : Prop :=
  (∀ x, b x ∈ HomD RD k lam s t (spanDeg C (RD.ellOf lam) x)) ∧
    ∀ d, Submodule.span k (Set.range fun x : {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d} =>
      b x.1) = HomD RD k lam s t d

variable (RD k) in
/-- **KL III Proposition 3.11, as a hypothesis**: for all `λ, 𝐢, 𝐣`, `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`
has a graded spanning family indexed by `B_{𝐢,𝐣,λ}` (KL III: the diagrams obtained from the minimal
diagrams of the `(𝐢, 𝐣)`-pairings by adding dots and a bubble monomial). **Not proved here.** -/
def Prop311 : Prop :=
  ∀ (lam : X) (s t : List (Letter I)), ∃ b, IsSpanFamily RD k lam s t b

variable [Finite I]

/-- The count of `B_{s,t,λ}` in degree `d` is the coefficient of `π ⟨E_s 1_λ, E_t 1_λ⟩`. -/
theorem card_fiber_eq (lam : X) (s t : List (Letter I)) (d : ℤ)
    [Fintype {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d}] :
    (Fintype.card {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d} : ℚ) =
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ t lam))).coeff d := by
  rw [← Nat.card_eq_fintype_card, (prop_3_12 RD lam d).2, (UDot.KL3.thm_2_7 C RD s t lam lam).1]

/-- **KL III eq. (3.68)** (`eq_another_equality`): for a graded spanning family indexed by
`B_{𝐢,𝐣,λ}` (as provided by Proposition 3.11), the dimension of `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)_d` is the
coefficient of `q^d` in `π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` iff the elements of degree `d` are linearly
independent (so, in all degrees, iff the family is a basis). -/
theorem finrank_eq_iff_linearIndependent (lam : X) (s t : List (Letter I))
    {b : SpanIdx s t → ((pres RD k).obj (ob RD lam s) ⟶ (pres RD k).obj (ob RD lam t))}
    (hb : IsSpanFamily RD k lam s t b) (d : ℤ) :
    ((finrank k (HomD RD k lam s t d) : ℤ) : ℚ) =
        (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ t lam))).coeff d ↔
      LinearIndependent k fun x : {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d} => b x.1 := by
  haveI := (prop_3_12 (s := s) (t := t) RD lam d).1
  haveI := Fintype.ofFinite {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d}
  rw [← card_fiber_eq lam s t d, ← (finrank_le_and_iff _ _ (hb.2 d)).2]
  push_cast
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- **KL III Corollary 3.13** (`cor-ineq`), given Proposition 3.11:
`gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) ≤ π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`, coefficientwise. -/
theorem cor_3_13 (h311 : Prop311 RD k) (lam : X) (s t : List (Letter I)) (d : ℤ) :
    ((finrank k (HomD RD k lam s t d) : ℤ) : ℚ) ≤
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ t lam))).coeff d := by
  obtain ⟨b, hb⟩ := h311 lam s t
  haveI := (prop_3_12 (s := s) (t := t) RD lam d).1
  haveI := Fintype.ofFinite {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d}
  rw [← card_fiber_eq lam s t d]
  exact_mod_cast (finrank_le_and_iff _ _ (hb.2 d)).1

variable (RD k) in
/-- **KL III, definition of nondegeneracy** (§3.2.3, after Corollary 3.13): "our graphical calculus
is nondegenerate if for all `𝐢, 𝐣, λ` the set `B_{𝐢,𝐣,λ}` is a basis of
`HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`". Formulated for every graded spanning family indexed by
`B_{𝐢,𝐣,λ}`. -/
def BasisNondeg : Prop :=
  ∀ (lam : X) (s t : List (Letter I)) b, IsSpanFamily RD k lam s t b →
    ∀ d, LinearIndependent k fun x : {x : SpanIdx s t // spanDeg C (RD.ellOf lam) x = d} => b x.1

/-- **KL III: "a calculus is nondegenerate if the equality holds in Corollary 3.13 for all
`𝐢, 𝐣, λ`"** — given Proposition 3.11, the basis definition of nondegeneracy (`BasisNondeg`) is
equivalent to the equality form (`CalculusNondeg`) used in Theorem 1.2. -/
theorem calculusNondeg_iff (h311 : Prop311 RD k) : CalculusNondeg RD k ↔ BasisNondeg RD k := by
  constructor
  · intro h lam s t b hb d
    exact (finrank_eq_iff_linearIndependent lam s t hb d).1 (h lam s t d)
  · intro h lam s t d
    obtain ⟨b, hb⟩ := h311 lam s t
    exact (finrank_eq_iff_linearIndependent lam s t hb d).2 (h lam s t b hb d)

/-- **KL III Theorem 1.2 in its original form**: given Proposition 3.11 (`Prop311`) and
Proposition 2.5 (`UDot.KL3.FormNondeg`), if the graphical calculus is nondegenerate in KL III's
sense (every spanning family indexed by `B_{𝐢,𝐣,λ}` is a basis, `BasisNondeg`), then
`γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is injective, hence bijective (simply-laced, `I` finite). -/
theorem gammaUA'_bijective_of_basisNondeg [DecidableEq I] (hSL : SimplyLaced C)
    (h311 : Prop311 RD k) (hB : BasisNondeg RD k) (h25 : UDot.KL3.FormNondeg RD) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  gammaUA'_bijective hSL ((calculusNondeg_iff h311).2 hB) h25 lam ρ

end Categorification.KL3.Diagram
