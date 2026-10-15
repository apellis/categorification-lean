/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMirror

/-!
# `R(n) ⊗_{R(n-1)} R(n) ⊕ R(n, 1) ≅ R(n + 1)`: Kang–Kashiwara Proposition 3.3

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, Props. 3.2, 3.3 and the decomposition of
`E_i K_0` in the proof of Thm. 5.2 (§5.2). Throughout, `ν = {i} + β`, `n = |β|`, the strand of
colour `i` is the last one (zero-indexed: strand `n`), `e(β, i) = cL 1` and
`ι = cLL : R(β) ⊗ R(i) → R(ν)`. KK's `τ_a` is the library's `ψ_{a-1}`.

* `wordProd_descRun_symm_val`, `shLast`, `lastW`: the shuffles of `S_n × S_1 ⊆ S_{n+1}` are the
  cycles `s_{n-1} ⋯ s_a` (`a ≤ n`), with reduced words `[a, …, n - 1]`.
* `lastFree_injective`, `lastFree_span` (**KK Prop. 3.2**, right-handed form):
  `R(ν) e(β, i) = ⊕_{a ≤ n} ψ_a ⋯ ψ_{n-1} ι(R(β) ⊗ R(i))`, a free right `R(β) ⊗ R(i)`-module.
* `fT b` (KK's `F : x ⊗ y ↦ x τ_n y` on the summand `ψ_b ⋯ ψ_{n-2} k[x_{n-1}] ⊗_{R(n-1)} R(n)`),
  `fT_sub_mem` (triangularity: `F_b(t) ≡ ψ_b ⋯ ψ_{n-1} ι(t)` modulo `ι(R(β) ⊗ R(i))`), and
  `kkF_surj`, `kkF_inj` (**KK Prop. 3.3** multiplied on the right by `e(β, i)`, in coordinates):
  every `r e(β, i)` is uniquely `∑_{b < n} F_b(p_b) + ι(q)`; `kkF_mul_cL`: right `R(β)`-linearity.
* `lastFree_mem_cycL0_iff`, `kkF_mem_cycL0_iff` (Prop. 3.3 tensored with `R^Λ(β)`, the
  decomposition `E_i K_0 = F(K_0') ⊕ (R^Λ(β) ⊗ k[t]) e(β, i)` of KK §5.2):
  `∑_{b < n} F_b(p_b) + ι(q) ∈ R(ν) a^Λ(x_1) R(β)` iff all `p_b`, `q` lie in `J ⊗ R(i)`, `J` the
  cyclotomic ideal of `R(β)`.

The free-module statements use the basis theorem over a commutative ring
(`KLRAlgebra.basisOfSymm`), so they assume (like `KLRAlgebra.freeBasis`) that `Q` is symmetric
(`KLRSymm Q`); `k` is any commutative ring.
-/

namespace Categorification.KLR

open Equiv TypeA

/-! ### Shuffles of `S_n × S_1` -/

section ShuffleLast

theorem wordProd_descRun_symm_val {m b l : ℕ} (h : b + l < m) (y : Fin m) :
    ((wordProd m (descRun b l)).symm y).val =
      if y.val < b then y.val else if y.val < b + l then y.val + 1
      else if y.val = b + l then b else y.val := by
  induction l generalizing b with
  | zero =>
    rw [descRun_zero, wordProd_nil]
    show y.val = _
    split_ifs <;> omega
  | succ l ih =>
    have e1 : (wordProd m (descRun b (l + 1))).symm y =
        sadj m b ((wordProd m (descRun (b + 1) l)).symm y) := by
      rw [descRun_succ, wordProd_append, wordProd_singleton]
      show (sadj m b).symm ((wordProd m (descRun (b + 1) l)).symm y) = _
      rw [KLRAlgebra.sadj_symm]
    have hz := ih (b := b + 1) (by omega)
    rw [e1, KLRAlgebra.sadj_apply_val (by omega), hz]
    split_ifs <;> omega

variable {n m : ℕ} (h : n + 1 = m)

/-- The last position `n` of `Fin m`, `m = n + 1`. -/
def lastFin : Fin m := ⟨n, by omega⟩

/-- The cycle `c_a = s_{n-1} ⋯ s_a`, sending `a` to `n` and `b > a` to `b - 1`. -/
def cycA (a : ℕ) : Perm (Fin m) := wordProd m (descRun a (n - a))

include h in
theorem cycA_symm_val {a : ℕ} (ha : a ≤ n) (y : Fin m) :
    ((cycA (n := n) a).symm y).val =
      if y.val < a then y.val else if y.val < n then y.val + 1 else a := by
  rw [cycA, wordProd_descRun_symm_val (by omega)]
  have := y.2
  split_ifs <;> omega

/-! #### Shuffles for the blocks `n + 1` -/

variable {n' : ℕ} (hb : n + n' = m) (h1 : n' = 1)

/-- The position of the second block. -/
def lastB : Fin m := blockEquiv hb (Sum.inr ⟨0, h1 ▸ Nat.one_pos⟩)

include h1 in
theorem mem_range_inl_iff (w : Perm (Fin m)) (z : Fin m) :
    (∃ x, w⁻¹ (blockEquiv hb (Sum.inl x)) = z) ↔ z ≠ w⁻¹ (lastB hb h1) := by
  constructor
  · rintro ⟨x, rfl⟩ hx
    have := (blockEquiv hb).injective (w⁻¹.injective hx)
    exact Sum.inl_ne_inr this
  · intro hz
    rcases hs : (blockEquiv hb).symm (w z) with x | y
    · refine ⟨x, ?_⟩
      rw [← hs, Equiv.apply_symm_apply]; exact w.symm_apply_apply z
    · exfalso
      apply hz
      have hy : y = ⟨0, by omega⟩ := Fin.ext (by have := y.2; omega)
      rw [lastB, ← hy, ← hs, Equiv.apply_symm_apply]; exact (w.symm_apply_apply z).symm

include h1 in
theorem eq_of_isShuffle_last {u v : Perm (Fin m)} (hu : IsShuffle hb u) (hv : IsShuffle hb v)
    (he : u⁻¹ (lastB hb h1) = v⁻¹ (lastB hb h1)) : u = v := by
  have hf : (fun x => u⁻¹ (blockEquiv hb (Sum.inl x))) =
      (fun x => v⁻¹ (blockEquiv hb (Sum.inl x))) := by
    rw [← StrictMono.range_inj_of_wellFoundedLT hu.1 hv.1]
    ext z
    simp only [Set.mem_range]
    rw [mem_range_inl_iff hb h1, mem_range_inl_iff hb h1, he]
  have hinv : u⁻¹ = v⁻¹ := by
    ext1 z
    obtain ⟨s, rfl⟩ := (blockEquiv hb).surjective z
    rcases s with x | y
    · exact congrFun hf x
    · have hy : y = ⟨0, by omega⟩ := Fin.ext (by have := y.2; omega)
      rw [hy]; exact he
  exact inv_injective hinv

include h hb in
theorem isShuffle_cycA {a : ℕ} (ha : a ≤ n) : IsShuffle hb (cycA (m := m) (n := n) a) := by
  refine ⟨fun x x' hxx' => ?_, fun y y' hyy' => ?_⟩
  · rw [Fin.lt_def] at hxx' ⊢
    show ((cycA (n := n) a).symm _).val < ((cycA (n := n) a).symm _).val
    rw [cycA_symm_val h ha, cycA_symm_val h ha, blockEquiv_inl_val, blockEquiv_inl_val]
    have := x'.2
    split_ifs <;> omega
  · exfalso; rw [Fin.lt_def] at hyy'; have := y'.2; omega

include h in
theorem cycA_symm_lastB {a : ℕ} (ha : a ≤ n) :
    ((cycA (m := m) (n := n) a)⁻¹ (lastB hb h1)).val = a := by
  show ((cycA (n := n) a).symm _).val = a
  rw [cycA_symm_val h ha, lastB, blockEquiv_inr_val]
  split_ifs <;> omega

include h in
theorem symm_lastB_le (u : Perm (Fin m)) : (u⁻¹ (lastB hb h1)).val ≤ n := by
  have := (u⁻¹ (lastB hb h1)).2; omega

include h in
theorem eq_cycA (u : Shuffle hb) :
    u.1 = cycA (m := m) (n := n) (u.1⁻¹ (lastB hb h1)).val :=
  eq_of_isShuffle_last hb h1 u.2 (isShuffle_cycA h hb (symm_lastB_le h hb h1 u.1))
    (Fin.ext (by rw [cycA_symm_lastB h hb h1 (symm_lastB_le h hb h1 u.1)]))

/-- The shuffles of `S_n × S_1`, indexed by the position `a ≤ n` of the last strand. -/
def shLast : Fin (n + 1) ≃ Shuffle hb where
  toFun a := ⟨cycA (n := n) a.val, isShuffle_cycA h hb (Nat.lt_succ_iff.1 a.2)⟩
  invFun u := ⟨(u.1⁻¹ (lastB hb h1)).val, Nat.lt_succ_of_le (symm_lastB_le h hb h1 u.1)⟩
  left_inv a := Fin.ext (cycA_symm_lastB h hb h1 (Nat.lt_succ_iff.1 a.2))
  right_inv u := Subtype.ext (eq_cycA h hb h1 u).symm

theorem shLast_apply (a : Fin (n + 1)) : (shLast h hb h1 a).1 = cycA (n := n) a.val := rfl

include h in
theorem isReduced_descRun {a : ℕ} (ha : a ≤ n) : IsReduced m (descRun a (n - a)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : a = 0 := by omega
    have := isReduced_canWord m (wordProd m (codeWord []))
    rwa [canWord_wordProd_codeWord isCode_nil (by simp; omega)] at this
  · have hc : IsCode (a :: idCode (n - 1)) := ⟨by simp; omega, isCode_idCode _⟩
    have hl : (a :: idCode (n - 1)).length = m - 1 := by simp; omega
    have hw : codeWord (a :: idCode (n - 1)) = descRun a (n - a) := by
      rw [codeWord_cons, codeWord_idCode, List.nil_append, length_idCode,
        show n - 1 + 1 - a = n - a by omega]
    have := isReduced_canWord m (wordProd m (codeWord (a :: idCode (n - 1))))
    rwa [canWord_wordProd_codeWord hc hl, hw] at this

end ShuffleLast

/-! ### `R(β + i) 1_{β,i}` is a free right `R(β) ⊗ R(i)`-module on `ψ_a ⋯ ψ_{n-1}` -/

section RightFreeLast

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (hsym : KLRSymm Q)

namespace KLRAlgebra

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T0" => KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si

omit [DecidableEq I] in
theorem card_add_single_eq : Multiset.card β + 1 = Multiset.card (β + Si) := by simp

omit [DecidableEq I] in
theorem card_single' : Multiset.card Si = 1 := Multiset.card_singleton i

/-- The explicit reduced word `[n - 1, …, a]` of the shuffle moving the last strand to `a`. -/
noncomputable def lastW (u : Shuffle (Seq.card_add' β Si)) : List ℕ :=
  descRun (u.1⁻¹ (lastB (Seq.card_add' β Si) (card_single' i))).val
    (Multiset.card β - (u.1⁻¹ (lastB (Seq.card_add' β Si) (card_single' i))).val)

omit [DecidableEq I] in
theorem lastW_spec (u : Shuffle (Seq.card_add' β Si)) :
    IsReduced (Multiset.card (β + Si)) (lastW i β u) ∧
      wordProd (Multiset.card (β + Si)) (lastW i β u) = u.1 :=
  ⟨isReduced_descRun (card_add_single_eq i β)
      (symm_lastB_le (card_add_single_eq i β) _ (card_single' i) u.1),
    (eq_cycA (card_add_single_eq i β) _ (card_single' i) u).symm⟩

/-- `ψ_a ψ_{a+1} ⋯ ψ_{n-1}`. -/
noncomputable def upW (a n : ℕ) : List ℕ := List.range' a (n - a)

theorem hflip_hatW_lastW (a : Fin (Multiset.card β + 1)) :
    hflip (hatW (Q := Q) (lastW i β) (shLast (card_add_single_eq i β) _ (card_single' i) a)) =
      ψw (upW a.val (Multiset.card β)) * oneConcat Q β Si := by
  rw [hatW, hflip_mul, hflip_oneConcat_eq, hflip_ψw]
  congr 2
  rw [lastW, upW, descRun, List.reverse_reverse]
  rw [shLast_apply, cycA_symm_lastB (card_add_single_eq i β) _ _ (Nat.lt_succ_iff.1 a.2)]

/-- The basis element `ψ(ŵ_u)` of the right free module for the reduced words `lastW`. -/
noncomputable def rWL (u : Shuffle (Seq.card_add' β Si)) : KLRAlgebra k Q (β + Si) :=
  hflip (hatW (lastW i β) u)

/-- `∑_u ψ(ŵ_u) ι(t_u)` for the reduced words `lastW`. -/
noncomputable def rFreeL (t : Shuffle (Seq.card_add' β Si) → T0) : KLRAlgebra k Q (β + Si) :=
  ∑ u, rWL (Q := Q) i β u * concat Q β Si (t u)

theorem hflip_freeMap_eq_rFreeL (t : Shuffle (Seq.card_add' β Si) → T0) :
    hflip ((freeMap (Q := Q) (lastW i β) (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q β Si (t u))) : KLRAlgebra k Q (β + Si))) = rFreeL i β t := by
  rw [freeMap, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Submodule.coe_sum, hflip_sum, rFreeL]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [coe_tensor_smul, Finsupp.coe_equivFunOnFinite_symm, hflip_mul,
      hflip_concat_eq_tflip, tflip_tflip]
    rfl
  · intro _; exact zero_smul _ _

include hsym in
/-- Uniqueness in the right free decomposition for the reduced words `lastW`. -/
theorem rfreeL_injective {t : Shuffle (Seq.card_add' β Si) → T0} (h : rFreeL i β t = 0) :
    ∀ u, t u = 0 := by
  have hbij := freeMap_bijective (ν := β) (ν' := Si) hsym (canWord _) (canWord _) (lastW i β)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) (lastW_spec i β)
  have h1 : ((freeMap (Q := Q) (lastW i β) (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q β Si (t u))) : oneConcatSub (ν := β) (ν' := Si) Q) :
        KLRAlgebra k Q (β + Si)) = 0 := by
    rw [← hflip_hflip ((freeMap (Q := Q) (lastW i β) (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q β Si (t u))) : oneConcatSub (ν := β) (ν' := Si) Q) :
        KLRAlgebra k Q (β + Si)), hflip_freeMap_eq_rFreeL, h, hflip_zero]
  have h0 : freeMap (Q := Q) (lastW i β) (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q β Si (t u))) = 0 := Subtype.ext h1
  have := hbij.1 (h0.trans (map_zero _).symm)
  intro u
  have hu := congrArg (fun f => f u) this
  simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply] at hu
  rw [← tflip_tflip (t := t u), hu, map_zero]

include hsym in
/-- Existence in the right free decomposition for the reduced words `lastW`. -/
theorem rfreeL_span (r : KLRAlgebra k Q (β + Si)) :
    ∃ t : Shuffle (Seq.card_add' β Si) → T0, r * oneConcat Q β Si = rFreeL i β t := by
  have hbij := freeMap_bijective (ν := β) (ν' := Si) hsym (canWord _) (canWord _) (lastW i β)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) (lastW_spec i β)
  have hmem : oneConcat Q β Si * hflip r ∈ oneConcatSub (ν := β) (ν' := Si) Q :=
    mem_oneConcatSub.2 (by rw [← mul_assoc, oneConcat_idem.eq])
  obtain ⟨f, hf⟩ := hbij.2 ⟨_, hmem⟩
  refine ⟨fun u => tflip Q β Si (f u), ?_⟩
  rw [← hflip_freeMap_eq_rFreeL]
  have hf' : (Finsupp.equivFunOnFinite.symm fun u => tflip Q β Si (tflip Q β Si (f u))) = f := by
    ext u; simp
  rw [hf', hf, hflip_mul, hflip_hflip, hflip_oneConcat_eq]

/-- `∑_{a ≤ n} ψ_a ⋯ ψ_{n-1} ι(t_a)` in `R(β + i)`. -/
noncomputable def lastFree' (t : Fin (Multiset.card β + 1) → T0) : KLRAlgebra k Q (β + Si) :=
  ∑ a, ψw (upW a.val (Multiset.card β)) * concat Q β Si (t a)

theorem rFreeL_comp_symm (t : Fin (Multiset.card β + 1) → T0) :
    rFreeL i β (t ∘ (shLast (card_add_single_eq i β) _ (card_single' i)).symm) =
      lastFree' i β t := by
  refine Fintype.sum_equiv (shLast (card_add_single_eq i β) _ (card_single' i)).symm _ _
    fun u => ?_
  conv_lhs => rw [← Equiv.apply_symm_apply (shLast (card_add_single_eq i β) _ (card_single' i)) u]
  rw [Function.comp_apply, rWL, hflip_hatW_lastW, mul_assoc, oneConcat_mul_concat,
    Equiv.symm_apply_apply]

include hsym in
theorem lastFree'_injective {t : Fin (Multiset.card β + 1) → T0} (h : lastFree' i β t = 0) :
    t = 0 := by
  rw [← rFreeL_comp_symm] at h
  funext a
  have := rfreeL_injective hsym i β h (shLast (card_add_single_eq i β) _ (card_single' i) a)
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at this

include hsym in
theorem lastFree'_span (r : KLRAlgebra k Q (β + Si)) :
    ∃ t : Fin (Multiset.card β + 1) → T0, r * oneConcat Q β Si = lastFree' i β t := by
  obtain ⟨t, ht⟩ := rfreeL_span hsym i β r
  refine ⟨t ∘ shLast (card_add_single_eq i β) _ (card_single' i), ?_⟩
  rw [← rFreeL_comp_symm, ht]
  congr 1
  funext u
  simp

end KLRAlgebra

end RightFreeLast

/-! ### Transport to `R({i} + β)` and KK Proposition 3.3 -/

section Prop34

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

theorem castKLR_ψw {μ μ' : Multiset I} (h : μ = μ') (ρ : List ℕ) :
    castKLR Q h (ψw ρ) = ψw ρ := by
  subst h; rfl

theorem castKLR_mem_subR0 {μ μ' : Multiset I} (h : μ = μ') (z : KLRAlgebra k Q μ) :
    castKLR Q h z ∈ subR0 (k := k) (Q := Q) μ' ↔ z ∈ subR0 (k := k) (Q := Q) μ := by
  subst h; rfl

theorem ψw_mem_subR0 {ν : Multiset I} (ρ : List ℕ) (hρ : ∀ j ∈ ρ, j + 2 < Multiset.card ν) :
    (ψw ρ : KLRAlgebra k Q ν) ∈ subR0 (k := k) (Q := Q) ν := by
  induction ρ with
  | nil => rw [ψw_nil]; exact Subalgebra.one_mem _
  | cons j ρ ih =>
    rw [ψw_cons]
    exact Subalgebra.mul_mem _ (ψ_mem_subR0 (hρ j (by simp)))
      (ih fun l hl => hρ l (by simp [hl]))

/-- A dot `x_b` commutes with `R(β) ⊗ k[x_m]` when `b` is the last strand. -/
theorem commute_x_last_subR0 {ν : Multiset I} (b : Fin (Multiset.card ν))
    (hb : b.val + 1 = Multiset.card ν) {w : KLRAlgebra k Q ν}
    (hw : w ∈ subR0 (k := k) (Q := Q) ν) : Commute (x b) w := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨c, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · exact x_mul_x b c
    · exact x_mul_e b t
    · exact x_mul_ψ b j (by omega) (by omega)
  | algebraMap c => exact Algebra.commutes c _ |>.symm
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

theorem commute_aeval_of_commute {A : Type*} [Ring A] [Algebra k A] {y w : A}
    (h : Commute y w) (f : Polynomial k) : Commute (Polynomial.aeval y f) w := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Commute.sum_left _ _ _ fun d _ => (h.pow_left d).smul_left _

/-- `f(x_j) ψ_j ≡ ψ_j f(x_{j+1})` modulo the subalgebra `R(β) ⊗ k[x_m]` of dots and
idempotents. -/
theorem aeval_x_mul_ψ_sub_mem {ν : Multiset I} (a b : Fin (Multiset.card ν))
    (hab : b.val = a.val + 1) (f : Polynomial k) :
    Polynomial.aeval (x a : KLRAlgebra k Q ν) f * ψ a.val -
        ψ a.val * Polynomial.aeval (x b : KLRAlgebra k Q ν) f ∈
      subR0 (k := k) (Q := Q) ν := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only at hab
  subst hab
  have key : ∀ d : ℕ, (x ⟨a, ha⟩ : KLRAlgebra k Q ν) ^ d * ψ a - ψ a * x ⟨a + 1, hb⟩ ^ d ∈
      subR0 (k := k) (Q := Q) ν := by
    intro d
    induction d with
    | zero => rw [pow_zero, pow_zero, one_mul, mul_one, sub_self]; exact Subalgebra.zero_mem _
    | succ d ih =>
      have hx := x_mul_ψ_self (Q := Q) (ν := ν) a hb
      have : (x ⟨a, ha⟩ : KLRAlgebra k Q ν) ^ (d + 1) * ψ a - ψ a * x ⟨a + 1, hb⟩ ^ (d + 1) =
          x ⟨a, ha⟩ * (x ⟨a, ha⟩ ^ d * ψ a - ψ a * x ⟨a + 1, hb⟩ ^ d) +
            (x ⟨a, ha⟩ * ψ a - ψ a * x ⟨a + 1, hb⟩) * x ⟨a + 1, hb⟩ ^ d := by
        rw [pow_succ', pow_succ']
        noncomm_ring
      rw [this, hx, add_sub_cancel_left]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (x_mem_subR0 _) ih)
        (Subalgebra.mul_mem _ (eSub_le_subR0 (eqIdem_mem a hb))
          (Subalgebra.pow_mem _ (x_mem_subR0 _) _))
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Subalgebra.sum_mem _ fun d _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  exact Subalgebra.smul_mem _ (key d) _

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T0" => KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si
local notation "R" => KLRAlgebra k Q (Si + β)

variable (Q) in
/-- `ι : R(β) ⊗ R(i) → R({i} + β)`: `R(β)` on the first `n` strands, the colour `i` last. -/
noncomputable def cLL : T0 →ₗ[k] R :=
  (castKLR Q (add_comm β Si)).toLinearMap ∘ₗ concat Q β Si

theorem cLL_apply (t : T0) : cLL Q i β t = castKLR Q (add_comm β Si) (concat Q β Si t) := rfl

theorem cLL_mul (s t : T0) : cLL Q i β (s * t) = cLL Q i β s * cLL Q i β t := by
  rw [cLL_apply, cLL_apply, cLL_apply, concat_mul, map_mul]

theorem cLL_tmul_one (b : Rb) : cLL Q i β (b ⊗ₜ 1) = cL Q i β b := rfl

theorem cLL_tmul (b : Rb) (c : Ri) :
    cLL Q i β (b ⊗ₜ c) = cL Q i β b * cLL Q i β (1 ⊗ₜ c) := by
  rw [← cLL_tmul_one, ← cLL_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cLL_mul_cL (t : T0) (b : Rb) :
    cLL Q i β (t * (b ⊗ₜ 1)) = cLL Q i β t * cL Q i β b := by
  rw [cLL_mul, cLL_tmul_one]

theorem cL_one_mul_cLL (t : T0) : cL Q i β 1 * cLL Q i β t = cLL Q i β t := by
  rw [← cLL_tmul_one, ← cLL_mul, ← Algebra.TensorProduct.one_def, one_mul]

theorem cLL_mul_cL_one (t : T0) : cLL Q i β t * cL Q i β 1 = cLL Q i β t := by
  rw [← cLL_tmul_one, ← cLL_mul, ← Algebra.TensorProduct.one_def, mul_one]

omit [DecidableEq I] in
/-- The last strand `n` of `R({i} + β)`. -/
theorem lastPos_lt : Multiset.card β < Multiset.card (Si + β) := by
  rw [card_single_add]; omega

theorem cLL_one_tmul_x :
    cLL Q i β (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩) =
      x ⟨Multiset.card β, lastPos_lt i β⟩ * cL Q i β 1 := by
  rw [cLL_apply, concat_one_tmul_x, map_mul, castKLR_x, ← cL_one_eq_cast]
  congr 2

theorem commute_x_last_cL (b : Rb) :
    Commute (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) (cL Q i β b) :=
  commute_x_last_subR0 _ (card_single_add i β).symm (cL_mem_subR0 i β b)

/-- `ι(1 ⊗ f(x)) = f(x_n) e(β, i)`. -/
theorem cLL_one_tmul_aeval (f : Polynomial k) :
    cLL Q i β (1 ⊗ₜ Polynomial.aeval (x ⟨0, by rw [card_single']; omega⟩ : Ri) f) =
      Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) f * cL Q i β 1 := by
  have hp : ∀ d : ℕ, cLL Q i β (1 ⊗ₜ ((x ⟨0, by rw [card_single']; omega⟩ : Ri) ^ d)) =
      (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) ^ d * cL Q i β 1 := by
    intro d
    induction d with
    | zero => rw [pow_zero, pow_zero, one_mul]; rfl
    | succ d ih =>
      have e1 : ((1 : Rb) ⊗ₜ[k] ((x ⟨0, by rw [card_single']; omega⟩ : Ri) ^ (d + 1)) : T0) =
          (1 ⊗ₜ ((x ⟨0, by rw [card_single']; omega⟩ : Ri) ^ d)) *
            (1 ⊗ₜ (x ⟨0, by rw [card_single']; omega⟩ : Ri)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, pow_succ]
      rw [e1, cLL_mul, ih, cLL_one_tmul_x, mul_assoc, ← mul_assoc (cL Q i β 1),
        ← (commute_x_last_cL i β 1).eq, mul_assoc, ← cL_mul, mul_one, ← mul_assoc, pow_succ]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, TensorProduct.tmul_sum,
    map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [TensorProduct.tmul_smul, map_smul, hp, smul_mul_assoc]

theorem cLL_one_tmul (c : Ri) :
    cLL Q i β (1 ⊗ₜ c) =
      Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) (singlePoly Q i c) *
        cL Q i β 1 := by
  conv_lhs => rw [← sec_singlePoly (Q := Q) i c]
  exact cLL_one_tmul_aeval i β _

/-- Elements of `R(β) ⊗ k[x_m]` times `e(β, i)` lie in the image of `ι`. -/
theorem exists_cLL_of_subR0 {w : R} (hw : w ∈ subR0 (k := k) (Q := Q) (Si + β)) :
    ∃ t : T0, w * cL Q i β 1 = cLL Q i β t := by
  have hw' : castKLR Q (add_comm β Si).symm w ∈ subR0 (k := k) (Q := Q) (β + Si) :=
    (castKLR_mem_subR0 _ _).2 hw
  obtain ⟨c, hc⟩ := exists_concat_of_subR0 i β hw'
  refine ⟨c, ?_⟩
  rw [cLL_apply, ← hc, map_mul, castKLR_castAlg_symm, cL_one_eq_cast]

/-! #### The right free decomposition of `R({i} + β) e(β, i)` -/

/-- `∑_{a ≤ n} ψ_a ⋯ ψ_{n-1} ι(t_a)` in `R({i} + β)` (zero-indexed; KK's
`∑_a τ_{a+1} ⋯ τ_n R(n, 1)`). -/
noncomputable def lastFree (t : Fin (Multiset.card β + 1) → T0) : R :=
  ∑ a, ψw (upW a.val (Multiset.card β)) * cLL Q i β (t a)

theorem lastFree_eq (t : Fin (Multiset.card β + 1) → T0) :
    lastFree i β t = castKLR Q (add_comm β Si) (lastFree' i β t) := by
  simp only [lastFree, lastFree', map_sum, map_mul, castKLR_ψw, cLL_apply]

theorem lastFree_add (t t' : Fin (Multiset.card β + 1) → T0) :
    lastFree i β (t + t') = lastFree i β t + lastFree i β t' := by
  simp only [lastFree, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem lastFree_sub (t t' : Fin (Multiset.card β + 1) → T0) :
    lastFree i β (t - t') = lastFree i β t - lastFree i β t' := by
  simp only [lastFree, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem lastFree_mul_cL (t : Fin (Multiset.card β + 1) → T0) (b : Rb) :
    lastFree i β (fun a => t a * (b ⊗ₜ 1)) = lastFree i β t * cL Q i β b := by
  simp only [lastFree, cLL_mul_cL, Finset.sum_mul, mul_assoc]

section Domain

variable (hsym : KLRSymm Q)

include hsym in
/-- **Uniqueness**: `R({i} + β) e(β, i) = ⊕_{a ≤ n} ψ_a ⋯ ψ_{n-1} ι(R(β) ⊗ R(i))`. -/
theorem lastFree_injective {t : Fin (Multiset.card β + 1) → T0} (h : lastFree i β t = 0) :
    t = 0 := by
  rw [lastFree_eq, map_eq_zero_iff _ (castKLR Q (add_comm β Si)).injective] at h
  exact lastFree'_injective hsym i β h

include hsym in
/-- **Existence**: `r e(β, i) = ∑_{a ≤ n} ψ_a ⋯ ψ_{n-1} ι(t_a)`. -/
theorem lastFree_span (r : R) :
    ∃ t : Fin (Multiset.card β + 1) → T0, r * cL Q i β 1 = lastFree i β t := by
  obtain ⟨t, ht⟩ := lastFree'_span hsym i β ((castKLR Q (add_comm β Si)).symm r)
  refine ⟨t, ?_⟩
  rw [lastFree_eq, ← ht, map_mul, castKLR_symm_apply, castKLR_castAlg_symm, cL_one_eq_cast]

end Domain

/-! #### KK's map `F : R(n) ⊗_{R(n-1)} R(n) → R(n + 1)` in coordinates -/

omit [DecidableEq I] in
theorem penPos_lt : Multiset.card β - 1 < Multiset.card (Si + β) := by
  rw [card_single_add]; omega

variable (Q) in
/-- KK's map `F(x ⊗ y) = x τ_n y` on the summand `ψ_b ⋯ ψ_{n-2} k[x_{n-1}] ⊗_{R(n-1)} R(n)` of
`R(n) ⊗_{R(n-1)} R(n)` (zero-indexed): `y ⊗ c ↦ ψ_b ⋯ ψ_{n-2} c(x_{n-1}) ψ_{n-1} y`, where
`c ∈ R(i) = k[x]`. -/
noncomputable def fT (b : ℕ) : T0 →ₗ[k] R :=
  TensorProduct.lift (LinearMap.mk₂ k (fun (y : Rb) (c : Ri) =>
      ψw (upW b (Multiset.card β - 1)) *
        Polynomial.aeval (x ⟨Multiset.card β - 1, penPos_lt i β⟩ : R) (singlePoly Q i c) *
          ψ (Multiset.card β - 1) * cL Q i β y)
    (fun y y' c => by rw [cL_add, mul_add])
    (fun r y c => by rw [cL_smul, mul_smul_comm])
    (fun y c c' => by rw [map_add, map_add, mul_add, add_mul, add_mul])
    (fun r y c => by rw [map_smul, map_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc]))

theorem fT_tmul (b : ℕ) (y : Rb) (c : Ri) :
    fT Q i β b (y ⊗ₜ c) = ψw (upW b (Multiset.card β - 1)) *
      Polynomial.aeval (x ⟨Multiset.card β - 1, penPos_lt i β⟩ : R) (singlePoly Q i c) *
        ψ (Multiset.card β - 1) * cL Q i β y := rfl

/-- `F` is right `R(β)`-linear. -/
theorem fT_mul_cL (b : ℕ) (t : T0) (y : Rb) :
    fT Q i β b (t * (y ⊗ₜ 1)) = fT Q i β b t * cL Q i β y := by
  induction t using TensorProduct.inductionOn with
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, fT_tmul, fT_tmul, cL_mul]
    simp only [mul_assoc]
  | add s t hs ht => rw [add_mul, map_add, map_add, hs, ht, add_mul]

theorem upW_succ {b n : ℕ} (hb : b < n) : upW b n = upW b (n - 1) ++ [n - 1] := by
  rw [upW, upW, show n - b = n - 1 - b + 1 by omega, List.range'_concat]
  congr 2
  omega

/-- **Triangularity of `F`**: `F_b(t) ≡ ψ_b ⋯ ψ_{n-1} ι(t)` modulo `ι(R(β) ⊗ R(i))`. -/
theorem fT_sub_mem (b : ℕ) (hb : b < Multiset.card β) (t : T0) :
    fT Q i β b t - ψw (upW b (Multiset.card β)) * cLL Q i β t ∈ LinearMap.range (cLL Q i β) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht =>
    rw [map_add, map_add, mul_add, add_sub_add_comm]; exact Submodule.add_mem _ hs ht
  | tmul y c =>
    set f := singlePoly Q i c
    have hs := aeval_x_mul_ψ_sub_mem (Q := Q) (ν := Si + β)
      ⟨Multiset.card β - 1, penPos_lt i β⟩ ⟨Multiset.card β, lastPos_lt i β⟩
      (by simp only; omega) f
    simp only at hs
    set s := Polynomial.aeval (x ⟨Multiset.card β - 1, penPos_lt i β⟩ : R) f *
        ψ (Multiset.card β - 1) -
      ψ (Multiset.card β - 1) * Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) f
      with hs_def
    have hw : ψw (upW b (Multiset.card β - 1)) * s ∈ subR0 (k := k) (Q := Q) (Si + β) :=
      Subalgebra.mul_mem _ (ψw_mem_subR0 _ fun j hj => by
        rw [upW, List.mem_range'_1] at hj; rw [card_single_add]; omega) hs
    obtain ⟨t₀, ht₀⟩ := exists_cLL_of_subR0 i β hw
    refine ⟨t₀ * (y ⊗ₜ 1), ?_⟩
    have hc : cLL Q i β (y ⊗ₜ c) =
        Polynomial.aeval (x ⟨Multiset.card β, lastPos_lt i β⟩ : R) f * cL Q i β y := by
      rw [cLL_tmul, cLL_one_tmul, ← mul_assoc,
        ← (commute_aeval_of_commute (commute_x_last_cL i β y) f).eq, mul_assoc, ← cL_mul,
        mul_one]
    have hy : cL Q i β 1 * cL Q i β y = cL Q i β y := by rw [← cL_mul, one_mul]
    rw [cLL_mul_cL, ← ht₀, fT_tmul, hc, upW_succ hb, ψw_append, ψw_cons, ψw_nil, mul_one,
      mul_assoc _ (cL Q i β 1), hy, hs_def]
    noncomm_ring

/-- **KK Proposition 3.3** (`R(n) ⊗_{R(n-1)} R(n) ⊕ R(n, 1) ≅ R(n + 1)`, multiplied on the right
by `e(β, i)`), in coordinates: `∑_{b < n} F_b(p_b) + ι(q)`. -/
noncomputable def kkF (p : Fin (Multiset.card β) → T0) (q : T0) : R :=
  ∑ b, fT Q i β b.val (p b) + cLL Q i β q

theorem kkF_mul_cL (p : Fin (Multiset.card β) → T0) (q : T0) (y : Rb) :
    kkF i β (fun b => p b * (y ⊗ₜ 1)) (q * (y ⊗ₜ 1)) = kkF i β p q * cL Q i β y := by
  simp only [kkF, fT_mul_cL, cLL_mul_cL, add_mul, Finset.sum_mul]

/-- The correction term of `fT_sub_mem`. -/
theorem exists_fT_eq (b : Fin (Multiset.card β)) (t : T0) :
    ∃ s : T0, fT Q i β b.val t = ψw (upW b.val (Multiset.card β)) * cLL Q i β t + cLL Q i β s := by
  obtain ⟨s, hs⟩ := fT_sub_mem i β b.val b.2 t
  exact ⟨s, by rw [hs, add_sub_cancel]⟩

/-- `lastFree` of the coordinates of `kkF p q`. -/
theorem kkF_eq_lastFree (p : Fin (Multiset.card β) → T0) (q : T0) (s : Fin (Multiset.card β) → T0)
    (hs : ∀ b, fT Q i β b.val (p b) =
      ψw (upW b.val (Multiset.card β)) * cLL Q i β (p b) + cLL Q i β (s b)) :
    kkF i β p q = lastFree i β (Fin.lastCases (q + ∑ b, s b) p) := by
  rw [kkF, lastFree, Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last, hs,
    Finset.sum_add_distrib, upW, Nat.sub_self, List.range'_zero, ψw_nil, one_mul, map_add,
    map_sum]
  abel

section Domain

variable (hsym : KLRSymm Q)

include hsym in
/-- **KK Proposition 3.3, existence**: every `r e(β, i)` is `∑_{b < n} F_b(p_b) + ι(q)`. -/
theorem kkF_surj (r : R) :
    ∃ (p : Fin (Multiset.card β) → T0) (q : T0), r * cL Q i β 1 = kkF i β p q := by
  obtain ⟨t, ht⟩ := lastFree_span i β hsym r
  choose s hs using fun b : Fin (Multiset.card β) => exists_fT_eq i β b (t b.castSucc)
  refine ⟨fun b => t b.castSucc, t (Fin.last _) - ∑ b, s b, ?_⟩
  rw [ht, kkF_eq_lastFree i β _ _ s hs, sub_add_cancel]
  congr 1
  funext a
  induction a using Fin.lastCases <;> simp

include hsym in
/-- **KK Proposition 3.3, uniqueness**: the map `(p, q) ↦ ∑_{b < n} F_b(p_b) + ι(q)` is
injective. -/
theorem kkF_inj {p : Fin (Multiset.card β) → T0} {q : T0} (h : kkF i β p q = 0) :
    p = 0 ∧ q = 0 := by
  choose s hs using fun b : Fin (Multiset.card β) => exists_fT_eq i β b (p b)
  rw [kkF_eq_lastFree i β _ _ s hs] at h
  have h0 := lastFree_injective i β hsym h
  have hp : p = 0 := funext fun b => by
    simpa using congrFun h0 b.castSucc
  refine ⟨hp, ?_⟩
  have hs0 : ∀ b, s b = 0 := fun b => by
    have := hs b
    rw [hp, Pi.zero_apply, map_zero, map_zero, mul_zero, zero_add] at this
    have h1 := lastFree_injective i β hsym (t := Fin.lastCases (s b) 0) (by
      rw [lastFree, Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Pi.zero_apply, map_zero, mul_zero,
        Finset.sum_const_zero, zero_add, Fin.val_last, upW, Nat.sub_self, List.range'_zero, ψw_nil,
        one_mul]
      exact this.symm)
    simpa using congrFun h1 (Fin.last _)
  have := congrFun h0 (Fin.last _)
  simpa [hs0] using this

end Domain

/-! #### Tensoring with `R^Λ(β)`: `E_i K_0 = F(K_0') ⊕ (R^Λ(β) ⊗ R(i)) e(β, i)` -/

theorem castKLR_cycAt (a : I → Polynomial k) {μ μ' : Multiset I} (h : μ = μ')
    (p : Fin (Multiset.card μ)) :
    castKLR Q h (cycAt a p) = cycAt a (Fin.cast (congrArg Multiset.card h) p) := by
  subst h; rfl

variable (a : I → Polynomial k)

theorem cycAt_mul_cL_one (hβ : 0 < Multiset.card β) :
    (cycAt a ⟨0, zero_lt_card_single_add i β⟩ * cL Q i β 1 : R) =
      cLL Q i β (cycAt a ⟨0, hβ⟩ ⊗ₜ 1) := by
  have h0 : 0 < Multiset.card (β + Si) := by rw [add_comm]; exact zero_lt_card_single_add i β
  rw [cLL_apply, ← cycAt_zero_mul_oneConcat i β a h0 hβ, map_mul, castKLR_cycAt,
    ← cL_one_eq_cast]
  rfl

theorem cLL_mem_cycL0 (hβ : 0 < Multiset.card β) {t : T0} (ht : t ∈ tJ0 (Q := Q) i β a) :
    cLL Q i β t ∈ cycL0 a (zero_lt_card_single_add i β) := by
  have h0 : 0 < Multiset.card (β + Si) := by rw [add_comm]; exact zero_lt_card_single_add i β
  rw [cLL_apply, castKLR_mem_cycL0 a _ h0]
  exact concat_mem_cycL0 i β a h0 hβ ht

theorem lastFree_mem_cycL0 (hβ : 0 < Multiset.card β) {t : Fin (Multiset.card β + 1) → T0}
    (ht : ∀ b, t b ∈ tJ0 (Q := Q) i β a) :
    lastFree i β t ∈ cycL0 a (zero_lt_card_single_add i β) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (cLL_mem_cycL0 i β a hβ (ht b))

theorem lastFree_single_last (t : T0) :
    lastFree i β (Pi.single (Fin.last _) t) = cLL Q i β t := by
  rw [lastFree, Finset.sum_eq_single (Fin.last _)]
  · rw [Pi.single_eq_same, Fin.val_last, upW, Nat.sub_self, List.range'_zero, ψw_nil, one_mul]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
  · simp

theorem fT_mem_cycL0 (hβ : 0 < Multiset.card β) (b : ℕ) {t : T0}
    (ht : t ∈ tJ0 (Q := Q) i β a) : fT Q i β b t ∈ cycL0 a (zero_lt_card_single_add i β) := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, c, hj, rfl⟩ := hy
    have : (j ⊗ₜ c : T0) = (1 ⊗ₜ c) * (j ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [this, fT_mul_cL, ← cLL_tmul_one]
    exact Submodule.smul_mem _ _ (cLL_mem_cycL0 i β a hβ
      (Submodule.subset_span ⟨j, 1, hj, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_of_tower_mem _ r hy

theorem kkF_mem_cycL0 (hβ : 0 < Multiset.card β) {p : Fin (Multiset.card β) → T0} {q : T0}
    (hp : ∀ b, p b ∈ tJ0 (Q := Q) i β a) (hq : q ∈ tJ0 (Q := Q) i β a) :
    kkF i β p q ∈ cycL0 a (zero_lt_card_single_add i β) :=
  Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => fT_mem_cycL0 i β a hβ b (hp b))
    (cLL_mem_cycL0 i β a hβ hq)

section Domain

variable (hsym : KLRSymm Q)

include hsym in
theorem exists_mul_lastFree (r : R) (t : Fin (Multiset.card β + 1) → T0) :
    ∃ t' : Fin (Multiset.card β + 1) → T0, r * lastFree i β t = lastFree i β t' ∧
      ((∀ b, t b ∈ tJ0 (Q := Q) i β a) → ∀ b, t' b ∈ tJ0 (Q := Q) i β a) := by
  choose c hc using fun b : Fin (Multiset.card β + 1) =>
    lastFree_span i β hsym (r * ψw (upW b.val (Multiset.card β)))
  refine ⟨fun b' => ∑ b, c b b' * t b, ?_,
    fun ht b' => Submodule.sum_mem _ fun b _ => mul_mem_tJ0 i β a (ht b) _⟩
  have hc' : ∀ b, r * (ψw (upW b.val (Multiset.card β)) * cLL Q i β (t b)) =
      lastFree i β (fun b' => c b b' * t b) := fun b => by
    rw [← cL_one_mul_cLL, ← mul_assoc, ← mul_assoc, hc b, lastFree, lastFree, Finset.sum_mul]
    simp only [mul_assoc, cLL_mul]
  rw [lastFree, Finset.mul_sum]
  simp_rw [hc', lastFree, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

include hsym in
/-- **KK Lemma 4.8 for `K_0`, with the basis `ψ_a ⋯ ψ_{n-1}`**: `∑_a ψ_a ⋯ ψ_{n-1} ι(t_a)` lies in
`R(ν) a^Λ(x_1) R(β)` exactly when every `t_a` lies in `J ⊗ R(i)`. -/
theorem lastFree_mem_cycL0_iff (hβ : 0 < Multiset.card β) (t : Fin (Multiset.card β + 1) → T0) :
    lastFree i β t ∈ cycL0 a (zero_lt_card_single_add i β) ↔ ∀ b, t b ∈ tJ0 (Q := Q) i β a := by
  refine ⟨fun ht => ?_, lastFree_mem_cycL0 i β a hβ⟩
  have key : ∀ z ∈ cycL0 (Q := Q) a (zero_lt_card_single_add i β),
      ∃ t' : Fin (Multiset.card β + 1) → T0, (∀ b, t' b ∈ tJ0 (Q := Q) i β a) ∧
        z * cL Q i β 1 = lastFree i β t' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨c, hc⟩ := exists_cLL_of_subR0 i β hw
      have hcyc : (cycAt a ⟨0, hβ⟩ ⊗ₜ 1 : T0) ∈ tJ0 (Q := Q) i β a :=
        Submodule.subset_span ⟨_, 1, cycAt_mem_cycIdeal a hβ, rfl⟩
      refine ⟨Pi.single (Fin.last _) ((cycAt a ⟨0, hβ⟩ ⊗ₜ 1) * c), fun b => ?_, ?_⟩
      · by_cases hb : b = Fin.last _
        · subst hb; rw [Pi.single_eq_same]; exact tJ0_mul_mem i β a hcyc c
        · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
      · rw [lastFree_single_last, cLL_mul, ← cycAt_mul_cL_one i β a hβ,
          mul_assoc (cycAt a _) (cL Q i β 1), cL_one_mul_cLL, ← hc, mul_assoc]
    | zero => exact ⟨0, fun _ => Submodule.zero_mem _, by
        simp only [zero_mul, lastFree, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]⟩
    | add y z _ _ hy hz =>
      obtain ⟨t₁, ht₁, hy⟩ := hy
      obtain ⟨t₂, ht₂, hz⟩ := hz
      exact ⟨t₁ + t₂, fun b => Submodule.add_mem _ (ht₁ b) (ht₂ b), by
        rw [add_mul, hy, hz, lastFree_add]⟩
    | smul r y _ hy =>
      obtain ⟨t', ht', hy⟩ := hy
      obtain ⟨t'', ht'', hS⟩ := exists_mul_lastFree i β a hsym r t'
      exact ⟨t'', hS ht', by rw [smul_eq_mul, mul_assoc, hy, ht'']⟩
  obtain ⟨t', ht', heq⟩ := key _ ht
  have hself : lastFree i β t * cL Q i β 1 = lastFree i β t := by
    simp only [lastFree, Finset.sum_mul, mul_assoc, cLL_mul_cL_one]
  rw [hself] at heq
  have h0 : t - t' = 0 := lastFree_injective i β hsym (by rw [lastFree_sub, heq, sub_self])
  intro b
  rw [sub_eq_zero.1 h0]; exact ht' b

include hsym in
/-- **KK Proposition 3.3 tensored with `R^Λ(β)`** (`E_i K_0 = F(K_0') ⊕ (R^Λ(β) ⊗ R(i)) e(β,i)`,
as in KK's proof of Thm. 5.2, in coordinates): `∑_{b < n} F_b(p_b) + ι(q)` lies in
`R(ν) a^Λ(x_1) R(β)` exactly when all `p_b` and `q` lie in `J ⊗ R(i)`. -/
theorem kkF_mem_cycL0_iff (hβ : 0 < Multiset.card β) (p : Fin (Multiset.card β) → T0) (q : T0) :
    kkF i β p q ∈ cycL0 a (zero_lt_card_single_add i β) ↔
      (∀ b, p b ∈ tJ0 (Q := Q) i β a) ∧ q ∈ tJ0 (Q := Q) i β a := by
  refine ⟨fun h => ?_, fun h => kkF_mem_cycL0 i β a hβ h.1 h.2⟩
  choose s hs using fun b : Fin (Multiset.card β) => exists_fT_eq i β b (p b)
  have h' := h
  rw [kkF_eq_lastFree i β _ _ s hs, lastFree_mem_cycL0_iff i β a hsym hβ] at h'
  have hp : ∀ b, p b ∈ tJ0 (Q := Q) i β a := fun b => by simpa using h' b.castSucc
  refine ⟨hp, ?_⟩
  have hq : cLL Q i β q ∈ cycL0 a (zero_lt_card_single_add i β) := by
    have := Submodule.sub_mem _ h (kkF_mem_cycL0 i β a hβ hp (Submodule.zero_mem _))
    rwa [kkF, kkF, map_zero, add_zero, add_sub_cancel_left] at this
  rw [← lastFree_single_last, lastFree_mem_cycL0_iff i β a hsym hβ] at hq
  simpa using hq (Fin.last _)

end Domain

end KLRAlgebra

end Prop34

end Categorification.KLR
