/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRecursion

/-!
# The balanced crossing image and the cokernel coordinate

The coordinate projection `C` annihilates the multiplication map
`x ⊗ y ↦ cL(x) ψ_{n-1} cL(y)`. This is the comparison between the
free-coordinate decomposition and the balanced crossing map used in
Kang–Kashiwara, arXiv:1102.4677v4, §5.2.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Ri" => KLRAlgebra k Q Si
local notation "T0" => Rb ⊗[k] Ri

/-- Multipliers which pass through the final crossing into the coefficient algebra. -/
noncomputable def crossingCore : Subalgebra k R where
  carrier := {w | ∃ y : Rb, w * ψ (Multiset.card β - 1) * cL Q i β 1 =
    ψ (Multiset.card β - 1) * cL Q i β y}
  one_mem' := ⟨1, by rw [one_mul]⟩
  zero_mem' := ⟨0, by rw [zero_mul, zero_mul, cL_zero, mul_zero]⟩
  add_mem' := by
    rintro u v ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [add_mul, add_mul, hy, hz, cL_add, mul_add]⟩
  mul_mem' := by
    rintro u v ⟨y, hy⟩ ⟨z, hz⟩
    refine ⟨y * z, ?_⟩
    have he : cL Q i β 1 * cL Q i β z = cL Q i β z := by rw [← cL_mul, one_mul]
    calc
      (u * v) * ψ (Multiset.card β - 1) * cL Q i β 1 = u * (v * ψ (Multiset.card β - 1) * cL Q i β 1) := by simp only [mul_assoc]
      _ = u * (ψ (Multiset.card β - 1) * cL Q i β z) := by rw [hz]
      _ = (u * ψ (Multiset.card β - 1) * cL Q i β 1) * cL Q i β z := by rw [mul_assoc, mul_assoc, he]
      _ = ψ (Multiset.card β - 1) * cL Q i β (y * z) := by rw [hy, mul_assoc, ← cL_mul]
  algebraMap_mem' := by
    intro r
    exact ⟨r • 1, by rw [cL_smul, mul_smul_comm, ← smul_mul_assoc,
      Algebra.smul_def, mul_assoc]⟩

theorem e_mem_crossingCore (t : Seq (Si + β)) : (e t : R) ∈ crossingCore i β := by
  obtain ⟨y, hy⟩ := e_mem_cLCore (Q := Q) i β (sadj (Multiset.card (Si + β))
    (Multiset.card β - 1) • t)
  exact ⟨y, by rw [e_mul_ψ, mul_assoc, hy]⟩

theorem cL_one_mem_crossingCore : cL Q i β 1 ∈ crossingCore i β := by
  rw [cL_one]
  exact Subalgebra.sum_mem _ fun t _ => e_mem_crossingCore i β _

theorem cL_e_mem_crossingCore (t : Seq β) : cL Q i β (e t) ∈ crossingCore i β := by
  rw [cL_e]
  exact e_mem_crossingCore i β _

theorem x_mem_crossingCore (b : Fin (Multiset.card β)) (hb : b.val < Multiset.card β - 1) :
    (x ⟨b.val, by have := b.2; rw [card_single_add]; omega⟩ : R) ∈ crossingCore i β := by
  refine ⟨x b, ?_⟩
  rw [x_mul_ψ _ _ (by change b.val ≠ Multiset.card β - 1; omega)
      (by change b.val ≠ Multiset.card β - 1 + 1; omega), mul_assoc]
  exact congrArg (ψ (Multiset.card β - 1) * ·) (cL_x i β b).symm

theorem ψ_mem_crossingCore (j : ℕ) (hj : j + 2 < Multiset.card β) :
    (ψ j : R) ∈ crossingCore i β := by
  refine ⟨ψ j, ?_⟩
  rw [ψ_mul_ψ j (Multiset.card β - 1) (by omega), mul_assoc, ← cL_ψ i β (by omega)]

/-- The first `n-1` strands of `R(β)`, together with all colour idempotents. -/
noncomputable def penSub : Subalgebra k Rb := Algebra.adjoin k
  (({x b | (b : Fin (Multiset.card β)) (_ : b.val < Multiset.card β - 1)} ∪
    Set.range e) ∪ {ψ j | (j : ℕ) (_ : j + 2 < Multiset.card β)})

theorem penSub_crossing {z : Rb} (hz : z ∈ penSub (Q := Q) β) :
    cL Q i β z ∈ crossingCore i β := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with (⟨b, hb, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [cL_x]
      exact Subalgebra.mul_mem _ (x_mem_crossingCore i β b hb) (cL_one_mem_crossingCore i β)
    · exact cL_e_mem_crossingCore i β t
    · rw [cL_ψ i β (by omega)]
      exact Subalgebra.mul_mem _ (ψ_mem_crossingCore i β j hj) (cL_one_mem_crossingCore i β)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul]
    exact Subalgebra.smul_mem _ (cL_one_mem_crossingCore i β) r
  | add x y _ _ hx hy => rw [cL_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [cL_mul]; exact Subalgebra.mul_mem _ hx hy

variable (hβ : 0 < Multiset.card β)

/-- The last dot of `R(β)` centralizes its first `n-1` strands. -/
theorem penSub_commute {z : Rb} (hz : z ∈ penSub (Q := Q) β) :
    Commute (x ⟨Multiset.card β - 1, by omega⟩ : Rb) z := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with (⟨b, hb, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · exact x_commute _ _
    · exact x_mul_e _ _
    · exact x_mul_ψ _ _ (by change Multiset.card β - 1 ≠ j; omega)
        (by change Multiset.card β - 1 ≠ j + 1; omega)
  | algebraMap r => exact (Algebra.commutes r _).symm
  | add x y _ _ hx hy => exact hx.add_right hy
  | mul x y _ _ hx hy => exact hx.mul_right hy

/-- Separating the last dot from the lower coefficient algebra. -/
noncomputable def penSpan : Submodule k Rb := Submodule.span k
  {w | ∃ d : ℕ, ∃ z ∈ penSub (Q := Q) β,
    w = (x ⟨Multiset.card β - 1, by omega⟩ : Rb) ^ d * z}

theorem penSpan_mul {u v : Rb} (hu : u ∈ penSpan (Q := Q) β hβ)
    (hv : v ∈ penSpan (Q := Q) β hβ) : u * v ∈ penSpan (Q := Q) β hβ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨d, z, hz, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨d', z', hz', rfl⟩ := hv
      refine Submodule.subset_span ⟨d + d', z * z', Subalgebra.mul_mem _ hz hz', ?_⟩
      rw [pow_add]
      have hc := ((penSub_commute β hβ hz).symm.pow_right d').eq
      rw [mul_assoc, ← mul_assoc z, hc]
      simp only [mul_assoc]
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem subR0_le_penSpan : (subR0 (k := k) (Q := Q) β).toSubmodule ≤ penSpan β hβ := by
  intro u hu
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    rcases hu with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · by_cases hb : b.val < Multiset.card β - 1
      · exact Submodule.subset_span ⟨0, x b, Algebra.subset_adjoin (Or.inl (Or.inl ⟨b, hb, rfl⟩)),
          by rw [pow_zero, one_mul]⟩
      · have he : b = ⟨Multiset.card β - 1, by omega⟩ := Fin.ext (by change b.val = Multiset.card β - 1; have := b.2; omega)
        rw [he]
        exact Submodule.subset_span ⟨1, 1, Subalgebra.one_mem _, by rw [pow_one, mul_one]⟩
    · exact Submodule.subset_span ⟨0, e t, Algebra.subset_adjoin (Or.inl (Or.inr ⟨t, rfl⟩)),
        by rw [pow_zero, one_mul]⟩
    · exact Submodule.subset_span ⟨0, ψ j, Algebra.subset_adjoin (Or.inr ⟨j, hj, rfl⟩),
        by rw [pow_zero, one_mul]⟩
  | algebraMap r =>
    exact Submodule.subset_span ⟨0, algebraMap k Rb r, Subalgebra.algebraMap_mem _ r,
      by rw [pow_zero, one_mul]⟩
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy => exact penSpan_mul β hβ hx hy

theorem hflip_mem_subR0 {ν : Multiset I} {u : KLRAlgebra k Q ν}
    (hu : u ∈ subR0 (k := k) (Q := Q) ν) : hflip u ∈ subR0 ν := by
  induction hu using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [hflip_x]; exact x_mem_subR0 _
    · rw [hflip_e]; exact e_mem_subR0 _
    · rw [hflip_ψ]; exact ψ_mem_subR0 hj
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, hflip_smul, hflip_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) r
  | add y z _ _ hy hz => rw [hflip_add]; exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => rw [hflip_mul]; exact Subalgebra.mul_mem _ hz hy

theorem hflip_tauRev {ν : Multiset I} {n d : ℕ} (hd : d ≤ n) :
    hflip (tauRev n d : KLRAlgebra k Q ν) = ψw (upW (n - d) n) := by
  rw [tauRev, hflip_ψw]
  congr 1
  apply List.reverse_injective
  rw [List.reverse_reverse, upW, List.reverse_range']
  simp only [Nat.sub_sub_self hd, Nat.sub_add_cancel hd]

/-- Right-handed last-strand coset induction, without fixing the final colour. -/
theorem lastCoset_induction {ν : Multiset I} (hQ : KLRSymm Q) (n : ℕ)
    (hn : n + 1 = Multiset.card ν) (M : KLRAlgebra k Q ν → Prop)
    (gen : ∀ b ≤ n, ∀ u ∈ subR0 (k := k) (Q := Q) ν, M (ψw (upW b n) * u))
    (zero : M 0) (add : ∀ x y, M x → M y → M (x + y))
    (smul : ∀ (r : k) x, M x → M (r • x)) (x : KLRAlgebra k Q ν) : M x := by
  have hx : hflip x ∈ spTauR (k := k) (Q := Q) ν n n := by
    rw [spTauR_eq_top hQ n hn]; trivial
  have key : ∀ z ∈ spTauR (k := k) (Q := Q) ν n n, M (hflip z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, d, hd, rfl⟩ := hz
      rw [hflip_mul, hflip_tauRev hd]
      exact gen _ (Nat.sub_le _ _) _ (hflip_mem_subR0 hu)
    | zero => simpa only [hflip_zero] using zero
    | add x y _ _ hx hy => simpa only [hflip_add] using add _ _ hx hy
    | smul r x _ hx => simpa only [hflip_smul] using smul r _ hx
  simpa only [hflip_hflip] using key _ hx

theorem cL_ψw (w : List ℕ) (hw : ∀ j ∈ w, j + 1 < Multiset.card β) :
    cL Q i β (ψw w) = ψw w * cL Q i β 1 := by
  induction w with
  | nil => simp only [ψw_nil, one_mul]
  | cons j w ih =>
    have hj := hw j (by simp)
    have ht := ih (fun l hl => hw l (by simp [hl]))
    rw [ψw_cons, cL_mul, cL_ψ i β hj, mul_assoc, ← cL_mul, one_mul,
      ht, ← mul_assoc, ψw_cons]

theorem cL_x_pow (b : Fin (Multiset.card β)) (d : ℕ) :
    cL Q i β (x b ^ d) =
      (x ⟨b.val, by have := b.2; rw [card_single_add]; omega⟩ : R) ^ d * cL Q i β 1 := by
  induction d with
  | zero => rw [pow_zero, pow_zero, one_mul]
  | succ d ih =>
    rw [pow_succ', cL_mul, cL_x, mul_assoc, ← cL_mul, one_mul, ih, ← mul_assoc]
    change (x ⟨b.val, _⟩ : R) * x ⟨b.val, _⟩ ^ d * _ = _
    rw [← pow_succ']

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (a : I → Polynomial k)

/-- A lower last-strand normal form is one free `F` coordinate after crossing. -/
theorem cPoly_coset_crossing (b : ℕ) (hb : b ≤ Multiset.card β - 1)
    (d : ℕ) (z : Rb) (hz : z ∈ penSub (Q := Q) β) (y : Rb) :
    cPoly i β hPQ hP a
      (cL Q i β (ψw (upW b (Multiset.card β - 1)) *
        ((x ⟨Multiset.card β - 1, by omega⟩ : Rb) ^ d * z)) *
          ψ (Multiset.card β - 1) * cL Q i β y) = 0 := by
  obtain ⟨v, hv⟩ := penSub_crossing i β hz
  have hy : cL Q i β z * ψ (Multiset.card β - 1) * cL Q i β y =
      ψ (Multiset.card β - 1) * cL Q i β (v * y) := by
    have he : cL Q i β 1 * cL Q i β y = cL Q i β y := by rw [← cL_mul, one_mul]
    calc
      _ = (cL Q i β z * ψ (Multiset.card β - 1) * cL Q i β 1) * cL Q i β y := by
        simp only [mul_assoc, he]
      _ = _ := by rw [hv, mul_assoc, ← cL_mul]
  have hw : ∀ j ∈ upW b (Multiset.card β - 1), j + 1 < Multiset.card β := by
    intro j hj; rw [upW, List.mem_range'_1] at hj; omega
  have he : cL Q i β (ψw (upW b (Multiset.card β - 1)) *
        ((x ⟨Multiset.card β - 1, by omega⟩ : Rb) ^ d * z)) *
          ψ (Multiset.card β - 1) * cL Q i β y =
      fT Q i β b ((v * y) ⊗ₜ ((x ⟨0, by rw [card_single']; omega⟩ : Ri) ^ d)) := by
    have hunit (r : Rb) : cL Q i β 1 * cL Q i β r = cL Q i β r := by rw [← cL_mul, one_mul]
    rw [cL_mul, cL_ψw i β _ hw, mul_assoc (ψw (upW b (Multiset.card β - 1))), hunit,
      cL_mul, cL_x_pow, mul_assoc (x _ ^ d), hunit,
      fT_tmul, map_pow, singlePoly_x, Polynomial.aeval_X_pow]
    simp only [mul_assoc] at hy ⊢
    rw [hy]
  rw [he]
  exact cPoly_fT i β a hPQ hP ⟨b, by omega⟩ _

include hβ in
/-- `C` annihilates the actual balanced crossing image, including the
`e(β,i)` cuts supplied by both occurrences of `cL`. -/
theorem cPoly_cL_crossing (x y : Rb) :
    cPoly i β hPQ hP a
      (cL Q i β x * ψ (Multiset.card β - 1) * cL Q i β y) = 0 := by
  apply lastCoset_induction (sym_of_factor hPQ) (Multiset.card β - 1) (by omega)
    (fun x => cPoly i β hPQ hP a
      (cL Q i β x * ψ (Multiset.card β - 1) * cL Q i β y) = 0)
    (x := x)
  · intro b hb u hu
    have hu' := subR0_le_penSpan β hβ hu
    clear hu
    induction hu' using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨d, z, hz, rfl⟩ := hu
      exact cPoly_coset_crossing i β hβ hPQ hP a b hb d z hz y
    | zero => simp only [mul_zero, cL_zero, zero_mul, map_zero]
    | add u v _ _ hu hv => simp only [mul_add, cL_add, add_mul, map_add, hu, hv, add_zero]
    | smul r u _ hu => simp only [mul_smul_comm, cL_smul, smul_mul_assoc, map_smul, hu, smul_zero]
  · simp only [cL_zero, zero_mul, map_zero]
  · intro u v hu hv
    simp only [cL_add, add_mul, map_add, hu, hv, add_zero]
  · intro r u hu
    simp only [cL_smul, smul_mul_assoc, map_smul, hu, smul_zero]

theorem cMap_cL_crossing (x y : Rb) :
    cMap i β hPQ hP a hβ (Submodule.Quotient.mk
      (cL Q i β x * ψ (Multiset.card β - 1) * cL Q i β y)) = 0 :=
  cPoly_cL_crossing i β hβ hPQ hP a x y

omit [IsDomain k] in
theorem commute_cL_one_subR0 {w : R} (hw : w ∈ subR0 (k := k) (Q := Q) (Si + β)) :
    w * cL Q i β 1 = cL Q i β 1 * w := by
  have h := commute_oneConcat_subR0 (Q := Q) i β
    ((castKLR_mem_subR0 (Q := Q) (add_comm β Si).symm w).2 hw)
  have h' := congrArg (castKLR Q (add_comm β Si)) h
  simpa only [map_mul, castKLR_symm_castAlg, ← cL_one_eq_cast] using h'

omit [IsDomain k] in
theorem cL_one_mul_core {w : R} (hw : w ∈ cLCore i β)
    (hw' : w ∈ subR0 (k := k) (Q := Q) (Si + β)) :
    ∃ z : Rb, cL Q i β 1 * w = cL Q i β z := by
  obtain ⟨z, hz⟩ := hw
  exact ⟨z, by rw [← commute_cL_one_subR0 i β hw', hz]⟩

include hβ in
/-- The left colour cut preserves every free crossing summand. -/
theorem cPoly_cL_one_fT (b : Fin (Multiset.card β)) (t : T0) :
    cPoly i β hPQ hP a (cL Q i β 1 * fT Q i β b.val t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul y c =>
    let w : R := ψw (upW b.val (Multiset.card β - 1)) *
      Polynomial.aeval (x ⟨Multiset.card β - 1, penPos_lt i β⟩ : R) (singlePoly Q i c)
    have hw : w ∈ cLCore i β := Subalgebra.mul_mem _
      (ψw_mem_cLCore i β _ (fun j hj => by rw [upW, List.mem_range'_1] at hj; omega))
      (aeval_mem_cLCore i β ⟨Multiset.card β - 1, by omega⟩ _)
    have hw' : w ∈ subR0 (k := k) (Q := Q) (Si + β) := by
      apply Subalgebra.mul_mem _
      · exact ψw_mem_subR0 _ (fun j hj => by rw [upW, List.mem_range'_1] at hj; rw [card_single_add]; omega)
      · rw [Polynomial.aeval_eq_sum_range]
        exact Subalgebra.sum_mem _ fun d _ =>
          Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (x_mem_subR0 _) _) _
    obtain ⟨z, hz⟩ := cL_one_mul_core i β hw hw'
    rw [fT_tmul]
    change cPoly i β hPQ hP a (cL Q i β 1 * (w * ψ (Multiset.card β - 1) * cL Q i β y)) = 0
    rw [← mul_assoc, ← mul_assoc, hz]
    exact cPoly_cL_crossing i β hβ hPQ hP a z y
  | add s t hs ht => simp only [map_add, mul_add, hs, ht, add_zero]

include hβ in
/-- The complementary coordinate already includes the left `e(β,i)` cut. -/
theorem cPoly_cL_one_mul (r : R) :
    cPoly i β hPQ hP a (cL Q i β 1 * r) = cPoly i β hPQ hP a r := by
  obtain ⟨p, q, hpq⟩ := kkF_surj i β hPQ hP r
  calc
    _ = cPoly i β hPQ hP a (cL Q i β 1 * (r * cL Q i β 1)) := by
      rw [← mul_assoc, cPoly_mul_cL_one]
    _ = thetaL0 Q i β a q := by
      rw [hpq, kkF, mul_add, Finset.mul_sum, map_add, map_sum, cL_one_mul_cLL]
      simp only [cPoly_cL_one_fT i β hβ hPQ hP a, Finset.sum_const_zero, zero_add]
      exact cPoly_cLL i β a hPQ hP q
    _ = cPoly i β hPQ hP a r := by
      rw [← cPoly_kkF i β hPQ hP a p q, ← hpq, cPoly_mul_cL_one]

include hβ in
/-- A colour-preserving lower multiplier before the final crossing has zero `C` coordinate. -/
theorem cPoly_core_crossing {w : R} (hw : w ∈ cLCore i β)
    (hw' : w ∈ subR0 (k := k) (Q := Q) (Si + β)) (y : Rb) :
    cPoly i β hPQ hP a (w * ψ (Multiset.card β - 1) * cL Q i β y) = 0 := by
  rw [← cPoly_cL_one_mul i β hβ hPQ hP a]
  obtain ⟨z, hz⟩ := cL_one_mul_core i β hw hw'
  rw [← mul_assoc, ← mul_assoc, hz]
  exact cPoly_cL_crossing i β hβ hPQ hP a z y

end Categorification.KLR.KLRAlgebra
