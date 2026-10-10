/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMaps

/-!
# The sequence `K_1 → K_0 → F^Λ → 0`: Kang–Kashiwara Lemma 4.9

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2: Lemma 4.9 and the exactness of
`K_1 → K_0 → F^Λ → 0` ((4.9) in KK).

* `span_tauProd_eq_top`: `R(ν) = ∑_{a ≤ n} (k[x_1] ⊗ R^1(β)) ψ_0 ⋯ ψ_{a-1}` (the left coset
  decomposition used in KK's proof of Lemma 4.9 (a), from `S_{n+1} = ⊔_a S_n s_1 ⋯ s_a`).
* `cycAt_mul_mem` (KK Lemma 4.9): `a^Λ(x_1) R(ν) ⊆ R(ν) a^Λ(x_1) R(β) + R(ν) a^Λ(x_1) ψ_0 ⋯ ψ_{n-1}`,
  hence the cyclotomic ideal of `R(ν)` lies in `R(ν) a^Λ(x_1) R(β) + R(ν) P̃` (`cycIdeal_le`).
* `range_pMap` (KK (4.9)): the image of `P : K_1 → K_0` is the kernel of the projection
  `π : K_0 → F^Λ = R(ν) / R(ν) a^Λ(x_1) R(ν)` (`piMap`, surjective).
-/

namespace Categorification.KLR

open MvPolynomial TypeA Equiv PolyRep NilHecke

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-! ### Moving polynomials and idempotents to the left past a crossing -/

/-- `ψ_j f = (s_j f) ψ_j + ∂_j f [i_j = i_{j+1}]`, summed over all idempotents. -/
theorem ψ_mul_pol (j : ℕ) (h : j + 1 < m) (f : MvPolynomial (Fin m) k) :
    (ψ j * pol f : A) = pol (swapPol j h f) * ψ j + pol (dd k m j f) * eqIdem j h := by
  apply ext_e
  intro t
  have he : (eqIdem j h * e t : A) = if t.1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ then e t else 0 := by
    rw [eqIdem, Finset.sum_mul, Finset.sum_eq_single t]
    · split_ifs <;> simp [e_mul_self]
    · intro u _ hu; split_ifs <;> simp [e_mul_e, hu]
    · simp
  rw [ψ_mul_pol_mul_e j h t f, add_mul, mul_assoc (pol _) (eqIdem _ _), he]
  split_ifs <;> simp

theorem exists_ψ_mul_eSub {δ : A} (hδ : δ ∈ eSub (k := k) (Q := Q) ν) (j : ℕ) :
    ∃ δ' ∈ eSub (k := k) (Q := Q) ν, ψ j * δ = δ' * ψ j := by
  induction hδ using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    exact ⟨e (sadj m j • t), e_mem_eSub _, ψ_mul_e j t⟩
  | algebraMap c => exact ⟨algebraMap k A c, Subalgebra.algebraMap_mem _ c, (Algebra.commutes c _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', hy⟩ := hy
    obtain ⟨z', hz', hz⟩ := hz
    exact ⟨y' + z', Subalgebra.add_mem _ hy' hz', by rw [mul_add, add_mul, hy, hz]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hy⟩ := hy
    obtain ⟨z', hz', hz⟩ := hz
    exact ⟨y' * z', Subalgebra.mul_mem _ hy' hz', by rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]⟩

theorem eSub_le_subR1 : eSub (k := k) (Q := Q) ν ≤ subR1 ν :=
  Algebra.adjoin_mono fun _ hy => Or.inl (Or.inr hy)

theorem tauProd_mul_ψw (a : ℕ) (ρ : List ℕ) (hρ : ∀ l ∈ ρ, a + 1 ≤ l) :
    (tauProd a * ψw ρ : A) = ψw ρ * tauProd a := by
  induction ρ with
  | nil => simp
  | cons l ρ ih =>
    rw [ψw_cons, ← mul_assoc, ← ψ_mul_tauProd l a (hρ l (by simp)), mul_assoc,
      ih (fun l' hl' => hρ l' (by simp [hl'])), mul_assoc]

theorem ψw_mem_subR1 (ρ : List ℕ) (hρ : ∀ l ∈ ρ, 1 ≤ l) : (ψw ρ : A) ∈ subR1 (k := k) (Q := Q) ν := by
  induction ρ with
  | nil => rw [ψw_nil]; exact Subalgebra.one_mem _
  | cons l ρ ih =>
    rw [ψw_cons]
    exact Subalgebra.mul_mem _ (ψ_mem_subR1 (hρ l (by simp))) (ih fun l' hl' => hρ l' (by simp [hl']))

/-! ### The left coset decomposition -/

variable (ν) in
/-- `∑_{a ≤ c} (k[x_1] ⊗ R^1(β)) ψ_0 ⋯ ψ_{a-1}` as a `k`-submodule. -/
noncomputable def spTau (c : ℕ) : Submodule k A :=
  Submodule.span k {y | ∃ u ∈ subR1 (k := k) (Q := Q) ν, ∃ a ≤ c, y = u * tauProd a}

theorem mem_spTau {c a : ℕ} (ha : a ≤ c) {u : A} (hu : u ∈ subR1 (k := k) (Q := Q) ν) :
    u * tauProd a ∈ spTau (k := k) (Q := Q) ν c :=
  Submodule.subset_span ⟨u, hu, a, ha, rfl⟩

theorem spTau_mono {c c' : ℕ} (h : c ≤ c') :
    spTau (k := k) (Q := Q) ν c ≤ spTau ν c' :=
  Submodule.span_mono fun _ ⟨u, hu, a, ha, hy⟩ => ⟨u, hu, a, le_trans ha h, hy⟩

theorem subR1_mul_mem_spTau {c : ℕ} {u y : A} (hu : u ∈ subR1 (k := k) (Q := Q) ν)
    (hy : y ∈ spTau (k := k) (Q := Q) ν c) : u * y ∈ spTau ν c := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u', hu', a, ha, rfl⟩ := hz
    rw [← mul_assoc]; exact mem_spTau ha (Subalgebra.mul_mem _ hu hu')
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

theorem mul_ψw_mem_spTau {c : ℕ} {y : A} (hy : y ∈ spTau (k := k) (Q := Q) ν c) (ρ : List ℕ)
    (hρ : ∀ l ∈ ρ, c + 1 ≤ l) : y * ψw ρ ∈ spTau ν c := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, a, ha, rfl⟩ := hz
    rw [mul_assoc, tauProd_mul_ψw a ρ (fun l hl => by have := hρ l hl; omega), ← mul_assoc]
    exact mem_spTau ha (Subalgebra.mul_mem _ hu (ψw_mem_subR1 ρ (fun l hl => by
      have := hρ l hl; omega)))
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

theorem mul_ψ_mem_spTau {c : ℕ} {y : A} (hy : y ∈ spTau (k := k) (Q := Q) ν c) :
    y * ψ c ∈ spTau ν (c + 1) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, a, ha, rfl⟩ := hz
    rcases Nat.lt_or_ge a c with hac | hac
    · rw [mul_assoc, ← ψ_mul_tauProd c a hac, ← mul_assoc]
      exact mem_spTau (by omega) (Subalgebra.mul_mem _ hu (ψ_mem_subR1 (by omega)))
    · obtain rfl : a = c := le_antisymm ha hac
      rw [mul_assoc, ← tauProd_succ]; exact mem_spTau le_rfl hu
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

/-- `Ψ_c f δ ∈ ∑_{a ≤ c} (k[x_1] ⊗ R^1(β)) Ψ_a` for a polynomial `f` and an idempotent sum `δ`. -/
theorem tauProd_pol_mem_spTau (c : ℕ) :
    ∀ (f : MvPolynomial (Fin m) k) (δ : A), δ ∈ eSub (k := k) (Q := Q) ν →
      tauProd c * pol f * δ ∈ spTau (k := k) (Q := Q) ν c := by
  induction c with
  | zero =>
    intro f δ hδ
    rw [tauProd_zero, one_mul, ← mul_one (pol f * δ), ← tauProd_zero (k := k) (Q := Q) (ν := ν)]
    exact mem_spTau le_rfl (Subalgebra.mul_mem _ (pol_mem_subR1 f) (eSub_le_subR1 hδ))
  | succ c ih =>
    intro f δ hδ
    by_cases hc : c + 1 < m
    · obtain ⟨δ', hδ', hδψ⟩ := exists_ψ_mul_eSub hδ c
      have key : (tauProd (c + 1) * pol f * δ : A) =
          tauProd c * pol (swapPol c hc f) * δ' * ψ c +
            tauProd c * pol (dd k m c f) * (eqIdem c hc * δ) := by
        rw [tauProd_succ, mul_assoc (tauProd c), ψ_mul_pol c hc, mul_add, add_mul]
        simp only [mul_assoc]
        rw [hδψ]
      rw [key]
      exact Submodule.add_mem _ (mul_ψ_mem_spTau (ih _ _ hδ'))
        (spTau_mono (Nat.le_succ c) (ih _ _ (Subalgebra.mul_mem _ (eqIdem_mem c hc) hδ)))
    · rw [tauProd_succ, ψ_eq_zero c (by omega), mul_zero, zero_mul, zero_mul]
      exact Submodule.zero_mem _

/-- Right multiplication by a crossing preserves `∑_{a ≤ n} (k[x_1] ⊗ R^1(β)) Ψ_a`. -/
theorem tauProd_mul_ψ_mem_spTau (n : ℕ) (hn : n + 1 = m) (a : ℕ) (ha : a ≤ n) (j : ℕ) :
    (tauProd a * ψ j : A) ∈ spTau (k := k) (Q := Q) ν n := by
  rcases Nat.lt_or_ge a j with haj | haj
  · rw [← ψ_mul_tauProd j a haj]
    exact mem_spTau ha (ψ_mem_subR1 (by omega))
  · rcases Nat.lt_or_ge j a with hja | hja
    · rcases Nat.lt_or_ge (j + 1) a with hj1 | hj1
      · -- `j + 2 ≤ a`: the braid relation
        have hsplit := tauProd_eq (k := k) (Q := Q) (ν := ν) j a (by omega)
        have hl : List.range' j (a - j) = j :: (j + 1) :: List.range' (j + 2) (a - (j + 2)) := by
          rw [show a - j = (a - (j + 2)) + 1 + 1 by omega, List.range'_succ, List.range'_succ]
        rw [hl, ψw_cons, ψw_cons] at hsplit
        have hj' : j + 2 < m := by omega
        have hcomm : (ψ j * ψw (List.range' (j + 2) (a - (j + 2))) : A) =
            ψw (List.range' (j + 2) (a - (j + 2))) * ψ j :=
          ψ_mul_ψw j _ (fun l hl => by have := List.mem_range'_1.mp hl; omega)
        have key : (tauProd a * ψ j : A) = ψ (j + 1) * tauProd a +
            tauProd j * (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) *
              ψw (List.range' (j + 2) (a - (j + 2))) := by
          rw [hsplit, ← mul_assoc (ψ (j + 1)), ψ_mul_tauProd (j + 1) j le_rfl]
          have : (tauProd j * (ψ j * (ψ (j + 1) * ψw (List.range' (j + 2) (a - (j + 2))))) *
              ψ j : A) = tauProd j * (ψ j * ψ (j + 1) * ψ j) *
                ψw (List.range' (j + 2) (a - (j + 2))) := by
            simp only [mul_assoc]; rw [← hcomm]
          rw [this]
          noncomm_ring
        rw [key]
        refine Submodule.add_mem _ (subR1_mul_mem_spTau (ψ_mem_subR1 (by omega))
          (by have := mem_spTau (k := k) (Q := Q) (ν := ν) ha (Subalgebra.one_mem _)
              rwa [one_mul] at this)) ?_
        rw [← mul_one (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)), ← sum_e,
          Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Submodule.sum_mem _ fun t _ => ?_
        rw [braid (Q := Q) j hj' t]
        split_ifs
        · rw [ncEval_x₃, ← mul_assoc]
          exact spTau_mono (by omega) (mul_ψw_mem_spTau (tauProd_pol_mem_spTau j _ _
            (e_mem_eSub t)) _ (fun l hl => by have := List.mem_range'_1.mp hl; omega))
        · rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
      · -- `j + 1 = a`: the quadratic relation
        obtain rfl : a = j + 1 := by omega
        rw [tauProd_succ, mul_assoc, ← mul_one (ψ j * ψ j), ← sum_e, Finset.mul_sum,
          Finset.mul_sum]
        refine Submodule.sum_mem _ fun t _ => ?_
        rw [ψ_sq j (by omega) t]
        split_ifs
        · rw [mul_zero]; exact Submodule.zero_mem _
        · rw [ncEval_x₂, ← mul_assoc]
          exact spTau_mono (by omega) (tauProd_pol_mem_spTau j _ _ (e_mem_eSub t))
    · -- `j = a`
      obtain rfl : j = a := le_antisymm haj hja
      by_cases hj : j + 1 ≤ n
      · rw [← tauProd_succ, ← one_mul (tauProd (j + 1))]
        exact mem_spTau hj (Subalgebra.one_mem _)
      · rw [ψ_eq_zero j (by omega), mul_zero]; exact Submodule.zero_mem _

/-- **The left coset decomposition** `R(ν) = ∑_{a ≤ n} (k[x_1] ⊗ R^1(β)) ψ_0 ⋯ ψ_{a-1}`
(used in KK's proof of Lemma 4.9 (a); KK Prop. 2.16 for the opposite parabolic). -/
theorem spTau_eq_top (n : ℕ) (hn : n + 1 = m) : spTau (k := k) (Q := Q) ν n = ⊤ := by
  have hgen : ∀ y ∈ spTau (k := k) (Q := Q) ν n, ∀ w : FreeAlgebra k (Gen ν),
      y * mk k Q ν w ∈ spTau ν n := by
    intro y hy w
    induction w using FreeAlgebra.induction generalizing y with
    | grade0 r =>
      rw [AlgHom.commutes, ← Algebra.commutes, ← Algebra.smul_def]; exact Submodule.smul_mem _ r hy
    | grade1 g =>
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u, hu, a, ha, rfl⟩ := hz
        rw [mul_assoc]
        refine subR1_mul_mem_spTau hu ?_
        cases g with
        | idem t =>
          have := tauProd_pol_mem_spTau (k := k) (Q := Q) (ν := ν) a 1 (e t) (e_mem_eSub t)
          rw [map_one, mul_one] at this
          exact spTau_mono ha this
        | dot b =>
          have := tauProd_pol_mem_spTau (k := k) (Q := Q) (ν := ν) a (X b) 1
            (Subalgebra.one_mem _)
          rw [pol_X, mul_one] at this
          exact spTau_mono ha this
        | cross j => exact tauProd_mul_ψ_mem_spTau n hn a ha j
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy
    | mul u v hu hv => rw [map_mul, ← mul_assoc]; exact hv _ (hu y hy)
    | add u v hu hv => rw [map_add, mul_add]; exact Submodule.add_mem _ (hu y hy) (hv y hy)
  refine eq_top_iff.2 fun r _ => ?_
  obtain ⟨w, rfl⟩ := mk_surjective r
  have h1 : (1 : A) ∈ spTau (k := k) (Q := Q) ν n := by
    rw [← mul_one (1 : A), ← tauProd_zero (k := k) (Q := Q) (ν := ν)]
    exact mem_spTau (Nat.zero_le _) (Subalgebra.one_mem _)
  simpa using hgen 1 h1 w

/-! ### KK Lemma 4.9 and exactness at `K_0` -/

section lemma49

variable (a : I → Polynomial k)

/-- **Kang–Kashiwara, Lemma 4.9**: `a^Λ(x_1) R(ν) ⊆ R(ν) a^Λ(x_1) R(β) + R(ν) a^Λ(x_1) ψ_0 ⋯ ψ_{n-1}`. -/
theorem cycAt_mul_mem (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m) (u : A) :
    cycAt a ⟨0, h0⟩ * u ∈ cycL0 a h0 ⊔ Submodule.span A {tauW a h0 n} := by
  have hu : u ∈ spTau (k := k) (Q := Q) ν n := by rw [spTau_eq_top n hn]; trivial
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u', hu', b, hb, rfl⟩ := hy
    rw [← mul_assoc, cycAt_zero_comm a hu', mul_assoc]
    refine Submodule.smul_mem _ u' ?_
    rcases Nat.lt_or_ge b n with hbn | hbn
    · exact Submodule.mem_sup_left (cycAt_mul_mem_cycL0 a h0 (tauProd_mem_subR0 b (by omega)))
    · obtain rfl : b = n := le_antisymm hb hbn
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton_iff.mpr rfl))
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_of_tower_mem _ r hy

theorem cycElt_eq (h0 : 0 < m) (t : Seq ν) :
    (cycElt Q a t : A) = cycAt a ⟨0, h0⟩ * e t := by
  rw [cycElt_of_pos Q a t h0, cycAt_mul_e, pol_aeval_X]

theorem cycAt_mem_cycIdeal (h0 : 0 < m) : (cycAt a ⟨0, h0⟩ : A) ∈ cycIdeal Q a ν := by
  rw [← mul_one (cycAt a ⟨0, h0⟩), ← sum_e, Finset.mul_sum]
  exact sum_mem fun t _ => by rw [← cycElt_eq a h0]; exact cycElt_mem_cycIdeal Q a t

/-- The cyclotomic ideal of `R(ν)` lies in `R(ν) a^Λ(x_1) R(β) + R(ν) a^Λ(x_1) Ψ_n`
(KK Lemma 4.9 (b), summed over the colour of the last strand). -/
theorem cycIdeal_le (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m) {z : A} (hz : z ∈ cycIdeal Q a ν) :
    z ∈ cycL0 a h0 ⊔ Submodule.span A {tauW a h0 n} := by
  suffices h : ∀ b : A, z * b ∈ cycL0 a h0 ⊔ Submodule.span A {tauW a h0 n} by
    simpa using h 1
  induction hz using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨t, rfl⟩ := hy
    intro b
    rw [cycElt_eq a h0, mul_assoc]
    exact cycAt_mul_mem a h0 n hn _
  | zero => intro b; rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => intro b; rw [add_mul]; exact Submodule.add_mem _ (hy b) (hz b)
  | neg y _ hy => intro b; rw [neg_mul]; exact Submodule.neg_mem _ (hy b)
  | left_absorb c y _ hy => intro b; rw [mul_assoc]; exact Submodule.smul_mem _ c (hy b)
  | right_absorb c y _ hy => intro b; rw [mul_assoc]; exact hy (c * b)

theorem cycL0_le (h0 : 0 < m) : cycL0 (Q := Q) a h0 ≤ (cycIdeal Q a ν).asIdeal := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, _, rfl⟩
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a h0)

variable (Q ν) in
/-- KK's `F^Λ = R^Λ(ν) = R(ν) / R(ν) a^Λ(x_1) R(ν)`, as a left `R(ν)`-module. -/
abbrev FLam : Type _ := A ⧸ (cycIdeal Q a ν).asIdeal

/-- KK's projection `π : K_0 → F^Λ`. -/
noncomputable def piMap (h0 : 0 < m) : KZero Q ν a h0 →ₗ[A] FLam Q ν a :=
  Submodule.factor (cycL0_le a h0)

theorem piMap_surjective (h0 : 0 < m) : Function.Surjective (piMap (Q := Q) a h0) :=
  Submodule.factor_surjective (cycL0_le a h0)

/-- **Exactness at `K_0`** (KK (4.9)): the image of `P : K_1 → K_0` is the kernel of
`π : K_0 → F^Λ`. -/
theorem range_pMap (h0 : 0 < m) (h1 : 1 < m) (n : ℕ) (hn : n + 1 = m) :
    LinearMap.range (pMap (Q := Q) a h0 h1 n hn) = LinearMap.ker (piMap a h0) := by
  have htauW : (tauW a h0 n : A) ∈ cycIdeal Q a ν :=
    TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a h0)
  have hpi : ∀ r : A, piMap a h0 (Submodule.Quotient.mk r : KZero Q ν a h0) =
      Submodule.Quotient.mk r := fun r => Submodule.factor_mk (cycL0_le a h0) r
  ext y
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_range, LinearMap.mem_ker, hpi, Submodule.Quotient.mk_eq_zero,
    TwoSidedIdeal.mem_asIdeal]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [pMap_mk, Submodule.Quotient.eq] at hz
    have h2 := (cycL0_le a h0) hz
    rw [TwoSidedIdeal.mem_asIdeal] at h2
    have h3 : c * tauW a h0 n ∈ cycIdeal Q a ν := TwoSidedIdeal.mul_mem_left _ _ _ htauW
    have := TwoSidedIdeal.sub_mem _ h3 h2
    rwa [sub_sub_cancel] at this
  · intro hr
    obtain ⟨l, hl, s, hs, rfl⟩ := Submodule.mem_sup.1 (cycIdeal_le a h0 n hn hr)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [pMap_mk, Submodule.Quotient.eq, smul_eq_mul, sub_add_cancel_right]
    exact Submodule.neg_mem _ hl

end lemma49

end KLRAlgebra

end Categorification.KLR
