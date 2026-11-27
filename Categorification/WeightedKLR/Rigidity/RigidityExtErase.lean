/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.WeightedKLR.RedStrands.AddRed

/-!
# Erasing both red strands of a coevaluation loading

Input for Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3. For two red strands `λ₁, λ₂` and black
weight `ν`, the *wrap* loadings put the first red strand at the left end, all black strands in the
middle and the second red strand at the right end. Erasing both red strands sends a wrap loading to
the black word in the middle and every other loading to zero, sends the dots and crossings of black
strands to the corresponding generators and every dot or crossing involving a red strand to zero.

This is a map `T^{(λ₁,λ₂)}(ν) → R^{λ₁}(ν)` to the cyclotomic quotient at the left red strand
exactly when the cyclotomic relation of the second red strand holds there on the last black strand:
`x_n ^ ⟨α_i^∨, λ₂⟩ e(t) = 0` for every word `t` ending in `i` (hypothesis `hR`). After appending the
second red strand to the cyclotomic projection of `R^{λ₁}(ν)`, erasure is the identity
(`eraseWrap_appendRed_cyclotomicProjection`).
-/

noncomputable section

namespace Categorification.Stendhal.TwoRedErase

open KLR KLRAlgebra TypeA StendhalAlgebraAllOrders

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight 2 ν
local notation "m" => Multiset.card μ
local notation "n" => Multiset.card ν
local notation "B" => KLRAlgebra k Q ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "π" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "Fr" => FreeAlgebra k (Gen μ)

omit [DecidableEq I] in
theorem card_two : m = n + 2 := by simp [stendhalWeight]

/-- The wrap loading of a black word: the first red strand, the black word, the second red
strand. -/
def wrap (t : Seq ν) : Seq μ :=
  appendRedLoading (ℓ := 1) (SingleRed.insertWord ν t)

/-- The label at position `c` of a wrap loading, as a function of the position's value. -/
def wrapLbl (t : Seq ν) (c : ℕ) : I ⊕ Fin 2 :=
  if h0 : c = 0 then .inr 0 else if h : c ≤ n then .inl (t.lbl ⟨c - 1, by omega⟩) else .inr 1

omit [DecidableEq I] in
theorem wrap_cases (a : Fin m) :
    a.val = 0 ∨ (∃ c, c < n ∧ a.val = c + 1) ∨ a.val = n + 1 := by
  have := a.isLt
  have hm := card_two ν
  by_cases h0 : a.val = 0
  · exact Or.inl h0
  · by_cases hl : a.val = n + 1
    · exact Or.inr (Or.inr hl)
    · exact Or.inr (Or.inl ⟨a.val - 1, by omega, by omega⟩)

omit [DecidableEq I] in
theorem wrap_lbl (t : Seq ν) (a : Fin m) : (wrap ν t).lbl a = wrapLbl ν t a.val := by
  rcases wrap_cases ν a with h0 | ⟨c, hc, hca⟩ | hl
  · have ha : a = appendRedPosition (ℓ := 1) ⟨0, by simp [stendhalWeight]⟩ := Fin.ext h0
    rw [congrArg (wrap ν t).lbl ha, h0, wrap, appendRedLoading_lbl, SingleRed.insertWord_head]
    simp [wrapLbl, addRedColor]
  · have ha : a = appendRedPosition (ℓ := 1) (SingleRed.blackPos ν ⟨c, hc⟩) := Fin.ext hca
    rw [congrArg (wrap ν t).lbl ha, hca, wrap, appendRedLoading_lbl, SingleRed.insertWord_black]
    simp [wrapLbl, addRedColor, show c + 1 ≤ n by omega]
  · have ha : a = lastRedPosition 1 ν := Fin.ext hl
    have hlast := hasLastRed_appendRedLoading (ℓ := 1) (SingleRed.insertWord ν t)
    rw [congrArg (wrap ν t).lbl ha, hl]
    refine hlast.trans ?_
    simp [wrapLbl]

omit [DecidableEq I] in
theorem wrap_lbl_zero (t : Seq ν) : (wrap ν t).lbl ⟨0, by simp [stendhalWeight]⟩ = .inr 0 := by
  rw [wrap_lbl]; simp [wrapLbl]

omit [DecidableEq I] in
theorem wrap_lbl_succ (t : Seq ν) (c : ℕ) (hc : c < n) :
    (wrap ν t).lbl ⟨c + 1, by rw [card_two]; omega⟩ = .inl (t.lbl ⟨c, hc⟩) := by
  rw [wrap_lbl]
  simp [wrapLbl, show c + 1 ≤ n by omega]

omit [DecidableEq I] in
theorem wrap_lbl_last (t : Seq ν) :
    (wrap ν t).lbl ⟨n + 1, by rw [card_two]; omega⟩ = .inr 1 := by
  rw [wrap_lbl]; simp [wrapLbl]

omit [DecidableEq I] in
theorem wrapLbl_zero (t : Seq ν) : wrapLbl ν t 0 = .inr 0 := by simp [wrapLbl]

omit [DecidableEq I] in
theorem wrapLbl_succ (t : Seq ν) (c : ℕ) (hc : c < n) :
    wrapLbl ν t (c + 1) = .inl (t.lbl ⟨c, hc⟩) := by
  simp [wrapLbl, show c + 1 ≤ n by omega]

omit [DecidableEq I] in
theorem wrapLbl_of_gt (t : Seq ν) (c : ℕ) (hc : n < c) : wrapLbl ν t c = .inr 1 := by
  simp [wrapLbl, show c ≠ 0 by omega, show ¬ c ≤ n by omega]

omit [DecidableEq I] in
theorem inr_zero_ne_wrapLbl (t : Seq ν) (c : ℕ) (h : c ≠ 0) : .inr 0 ≠ wrapLbl ν t c := by
  unfold wrapLbl
  split_ifs <;> simp_all

omit [DecidableEq I] in
theorem wrap_injective : Function.Injective (wrap ν) :=
  appendRedLoading_injective.comp (SingleRed.insertWord_injective ν)

omit [DecidableEq I] in
private theorem wrap_swap (j : ℕ) (hj : j + 1 < n) (t : Seq ν) :
    sadj m (j + 1) • wrap ν t = wrap ν (sadj n j • t) := by
  have hm : j + 1 + 1 < m := by rw [card_two]; omega
  apply Subtype.ext
  funext a
  change (sadj m (j + 1) • wrap ν t).1 a = (wrap ν (sadj n j • t)).lbl a
  rw [sadj_smul_apply]
  change (wrap ν t).lbl _ = _
  have hs : ∀ b : Fin n, (sadj n j • t).lbl b = t.lbl (sadj n j b) := fun b =>
    sadj_smul_apply j t b
  rw [wrap_lbl, wrap_lbl]
  rcases wrap_cases ν a with h0 | ⟨c, hc, hca⟩ | hl
  · have hv : (sadj m (j + 1) a).val = 0 := by
      rw [sadj_apply_val hm, h0]; split_ifs <;> omega
    rw [hv, h0]
    simp [wrapLbl]
  · have hlt := (sadj n j ⟨c, hc⟩).isLt
    have hv : (sadj m (j + 1) a).val = (sadj n j ⟨c, hc⟩).val + 1 := by
      rw [sadj_apply_val hm, sadj_apply_val hj, hca]; simp only; split_ifs <;> omega
    rw [hv, hca]
    simp [wrapLbl, hs, show (sadj n j ⟨c, hc⟩).val + 1 ≤ n by omega, show c + 1 ≤ n by omega]
  · have hv : (sadj m (j + 1) a).val = n + 1 := by
      rw [sadj_apply_val hm, hl]; split_ifs <;> omega
    rw [hv, hl]
    simp [wrapLbl]

/-- A wrap loading maps to its black word, every other loading to zero. -/
private def erasedE (s : Seq μ) : B :=
  ∑ t : Seq ν, if wrap ν t = s then KLRAlgebra.e t else 0

private theorem erasedE_wrap (t : Seq ν) : erasedE Q ν (wrap ν t) = KLRAlgebra.e t := by
  classical
  simp [erasedE, (wrap_injective ν).eq_iff]

private theorem erasedE_zero {s : Seq μ} (hs : s ∉ Set.range (wrap ν)) : erasedE Q ν s = 0 := by
  have hn (t : Seq ν) : wrap ν t ≠ s := fun h => hs ⟨t, h⟩
  simp [erasedE, hn]

private theorem erasedE_sum : ∑ s : Seq μ, erasedE Q ν s = 1 := by
  classical
  simp only [erasedE]
  rw [Finset.sum_comm]
  simp [KLRAlgebra.sum_e]

/-- Dots on black strands keep their position (shifted by the first red strand); dots on red
strands vanish. -/
private def erasedX (a : Fin m) : B :=
  if h : 0 < a.val ∧ a.val ≤ n then KLRAlgebra.x ⟨a.val - 1, by omega⟩ else 0

private def erasedCross : ℕ → B
  | 0 => 0
  | j + 1 => KLRAlgebra.ψ j

private def eraseGen : Gen μ → B
  | .idem s => erasedE Q ν s
  | .dot a => erasedX Q ν a
  | .cross j => erasedCross Q ν j

private def eraseFree : Fr →ₐ[k] B := FreeAlgebra.lift k (eraseGen Q ν)

private theorem erase_fe (s : Seq μ) : eraseFree Q ν (fe k μ s) = erasedE Q ν s :=
  FreeAlgebra.lift_ι_apply _ _

private theorem erase_fx (a : Fin m) : eraseFree Q ν (fx k μ a) = erasedX Q ν a :=
  FreeAlgebra.lift_ι_apply _ _

private theorem erase_fψ (j : ℕ) : eraseFree Q ν (fψ k μ j) = erasedCross Q ν j :=
  FreeAlgebra.lift_ι_apply _ _

private theorem erasedX_succ (c : ℕ) (hc : c < n) (h : c + 1 < m) :
    erasedX Q ν ⟨c + 1, h⟩ = KLRAlgebra.x ⟨c, hc⟩ := by
  simp [erasedX, show c + 1 ≤ n by omega]

private theorem erasedX_zero (h : 0 < m) : erasedX Q ν ⟨0, h⟩ = 0 := by simp [erasedX]

private theorem erasedX_last (h : n + 1 < m) : erasedX Q ν ⟨n + 1, h⟩ = 0 := by simp [erasedX]

private theorem erase_eval {d : ℕ} (v : Fin d → Fr) (p : MvPolynomial (Fin d) k) :
    eraseFree Q ν (ncEval v p) = ncEval (fun a => eraseFree Q ν (v a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

private theorem erasedE_mul (s t : Seq μ) :
    erasedE Q ν s * erasedE Q ν t = if s = t then erasedE Q ν s else 0 := by
  by_cases he : s = t
  · subst t
    by_cases hs : s ∈ Set.range (wrap ν)
    · obtain ⟨i, rfl⟩ := hs
      simp [erasedE_wrap, KLRAlgebra.e_mul_self]
    · simp [erasedE_zero Q ν hs]
  · rw [ite_eq_right_iff.mpr (fun h => (he h).elim)]
    by_cases hs : s ∈ Set.range (wrap ν)
    · obtain ⟨i, rfl⟩ := hs
      by_cases ht : t ∈ Set.range (wrap ν)
      · obtain ⟨j, rfl⟩ := ht
        have hij : i ≠ j := fun h => he (congrArg (wrap ν) h)
        simp [erasedE_wrap, KLRAlgebra.e_mul_e, hij]
      · simp [erasedE_zero Q ν ht]
    · simp [erasedE_zero Q ν hs]

private theorem erasedX_mul_e (a : Fin m) (s : Seq μ) :
    erasedX Q ν a * erasedE Q ν s = erasedE Q ν s * erasedX Q ν a := by
  by_cases hs : s ∈ Set.range (wrap ν)
  · obtain ⟨i, rfl⟩ := hs
    rw [erasedE_wrap]
    unfold erasedX
    split <;> simp [KLRAlgebra.x_mul_e]
  · simp [erasedE_zero Q ν hs]

private theorem erasedCross_mul_e (j : ℕ) (s : Seq μ) :
    erasedCross Q ν j * erasedE Q ν s =
      erasedE Q ν (sadj m j • s) * erasedCross Q ν j := by
  cases j with
  | zero => simp [erasedCross]
  | succ j =>
    by_cases hj : j + 1 < n
    · by_cases hs : s ∈ Set.range (wrap ν)
      · obtain ⟨i, rfl⟩ := hs
        simp [wrap_swap ν j hj, erasedCross, erasedE_wrap, KLRAlgebra.ψ_mul_e]
      · have hn : sadj m (j + 1) • s ∉ Set.range (wrap ν) := by
          rintro ⟨i, h⟩
          exact hs ⟨_, by rw [← wrap_swap ν j hj, h, sadj_smul_smul]⟩
        simp [erasedE_zero Q ν hs, erasedE_zero Q ν hn]
    · simp [erasedCross, ψ_eq_zero j (by omega : n ≤ j + 1)]

private theorem erasedX_comm (a b : Fin m) :
    erasedX Q ν a * erasedX Q ν b = erasedX Q ν b * erasedX Q ν a := by
  unfold erasedX
  split_ifs <;> simp [KLRAlgebra.x_mul_x]

private theorem erasedX_cross (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    erasedX Q ν a * erasedCross Q ν j = erasedCross Q ν j * erasedX Q ν a := by
  cases j with
  | zero => simp [erasedCross]
  | succ j =>
    unfold erasedX
    split
    · exact KLRAlgebra.x_mul_ψ _ j (by simp; omega) (by simp; omega)
    · simp

private theorem erase_nceval_two (j : ℕ) (h : j + 1 < m) (p : MvPolynomial (Fin 2) k) :
    eraseFree Q ν (ncEval ![fx k μ ⟨j, by omega⟩, fx k μ ⟨j + 1, h⟩] p) =
      ncEval ![erasedX Q ν ⟨j, by omega⟩, erasedX Q ν ⟨j + 1, h⟩] p := by
  rw [erase_eval]
  congr 1
  funext a
  fin_cases a <;> apply erase_fx

private theorem erase_nceval_three (j : ℕ) (h : j + 2 < m) (p : MvPolynomial (Fin 3) k) :
    eraseFree Q ν (ncEval ![fx k μ ⟨j, by omega⟩, fx k μ ⟨j + 1, by omega⟩,
      fx k μ ⟨j + 2, h⟩] p) =
      ncEval ![erasedX Q ν ⟨j, by omega⟩, erasedX Q ν ⟨j + 1, by omega⟩,
        erasedX Q ν ⟨j + 2, h⟩] p := by
  rw [erase_eval]
  congr 1
  funext a
  fin_cases a <;> apply erase_fx

private theorem eval_X_one_pow (z : B) (b : ℕ) :
    ncEval ![(0 : B), z] (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) k) = z ^ b := by
  rw [MvPolynomial.X_pow_eq_monomial]
  change (Finsupp.single _ (1 : k)).sum _ = _
  rw [Finsupp.sum_single_index (by simp)]
  simp [List.ofFn_succ, Finsupp.single_apply]

private theorem eval_X_zero_pow (z : B) (b : ℕ) :
    ncEval ![z, (0 : B)] (MvPolynomial.X 0 ^ b : MvPolynomial (Fin 2) k) = z ^ b := by
  rw [MvPolynomial.X_pow_eq_monomial]
  change (Finsupp.single _ (1 : k)).sum _ = _
  rw [Finsupp.sum_single_index (by simp)]
  simp [List.ofFn_succ]

/-- The cyclotomic relation of the second red strand on the last black strand of `R^{λ₁}(ν)`:
`x_n ^ ⟨α_i^∨, λ₂⟩ e(t) = 0` for every word `t`, with `i` the colour of its last letter. -/
def LastDotRelation : Prop :=
  ∀ (t : Seq ν) (h : 0 < n),
    π (KLRAlgebra.x ⟨n - 1, by omega⟩ ^ Λ 1 (t.lbl ⟨n - 1, by omega⟩) * KLRAlgebra.e t) = 0

variable (hR : LastDotRelation Q Λ ν)

include hR in
private theorem erase_rel {a b : Fr} (h : KLR.Rel k (stendhalQ Q Λ) μ a b) :
    π (eraseFree Q ν a) = π (eraseFree Q ν b) := by
  classical
  have hm := card_two ν
  cases h with
  | idem_mul s t =>
    apply congrArg π
    by_cases h : s = t <;> simp [erase_fe, h, erasedE_mul]
  | idem_sum =>
    apply congrArg π
    simp [erase_fe, erasedE_sum]
  | dot_idem a s =>
    apply congrArg π
    simp [erase_fx, erase_fe, erasedX_mul_e]
  | cross_idem j s =>
    apply congrArg π
    simp [erase_fψ, erase_fe, erasedCross_mul_e]
  | cross_zero j h =>
    apply congrArg π
    cases j with
    | zero => simp [erase_fψ, erasedCross]
    | succ j => simp [erase_fψ, erasedCross, ψ_eq_zero j (by omega : n ≤ j + 1)]
  | dot_dot a b =>
    apply congrArg π
    simp only [map_mul, erase_fx]
    exact erasedX_comm Q ν a b
  | cross_cross j l h =>
    apply congrArg π
    simp only [map_mul, erase_fψ]
    cases j with
    | zero => simp [erasedCross]
    | succ j =>
      cases l with
      | zero => omega
      | succ l => exact ψ_mul_ψ j l (by omega)
  | dot_cross a j h1 h2 =>
    apply congrArg π
    simp only [map_mul, erase_fx, erase_fψ]
    exact erasedX_cross Q ν a j h1 h2
  | dot_cross_left j h s | dot_cross_right j h s =>
    apply congrArg π
    by_cases hs : s ∈ Set.range (wrap ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        simp [erase_fe, erase_fx, erase_fψ, erasedCross, wrap_lbl, erasedX, wrapLbl_zero,
          inr_zero_ne_wrapLbl ν t 1 one_ne_zero]
      | succ j =>
        by_cases hj : j + 1 < n
        · simp only [map_mul, map_sub, apply_ite (eraseFree Q ν), map_zero, erase_fx, erase_fe,
            erase_fψ, erasedCross, erasedX_succ Q ν j (by omega), erasedX_succ Q ν (j + 1) hj,
            erasedE_wrap, wrap_lbl_succ ν t j (by omega), wrap_lbl_succ ν t (j + 1) hj,
            Sum.inl.injEq]
          first | exact dot_cross_left j hj t | exact dot_cross_right j hj t
        · simp [erase_fe, erase_fx, erase_fψ, erasedCross, wrap_lbl, ψ_eq_zero j (by omega : n ≤ j + 1),
            wrapLbl_succ ν t j (by omega), wrapLbl_of_gt ν t (j + 1 + 1) (by omega)]
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]
  | cross_sq j h s =>
    by_cases hs : s ∈ Set.range (wrap ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        by_cases h0 : 0 < n
        · have hc := CycKLR.mk_aeval_x_mul_e (Q := Q) (a := fun i => Polynomial.X ^ Λ 0 i)
            t h0
          simp only [map_pow, Polynomial.aeval_X] at hc
          have hl1 := wrap_lbl_succ ν t 0 h0
          simp only [zero_add] at hl1
          simpa [erase_fψ, erase_fe, erasedCross, wrap_lbl_zero, hl1,
            erase_nceval_two, erasedX_zero, erasedX_succ Q ν 0 h0, stendhalQ, eval_X_one_pow,
            erasedE_wrap] using hc.symm
        · have hl1 : (wrap ν t).lbl ⟨0 + 1, h⟩ = .inr 1 := by
            rw [wrap_lbl]; exact wrapLbl_of_gt ν t (0 + 1) (by omega)
          apply congrArg π
          simp [erase_fψ, erase_fe, erasedCross, wrap_lbl_zero, hl1, stendhalQ, ncEval]
      | succ j =>
        by_cases hj : j + 1 < n
        · apply congrArg π
          simp only [map_mul, apply_ite (eraseFree Q ν), erase_fψ, erase_fe, erasedCross,
            erasedE_wrap, wrap_lbl_succ ν t j (by omega), wrap_lbl_succ ν t (j + 1) hj,
            Sum.inl.injEq, map_zero, erase_nceval_two, erasedX_succ Q ν j (by omega),
            erasedX_succ Q ν (j + 1) hj, stendhalQ_inl_inl]
          exact ψ_sq j hj t
        · have hlj := wrap_lbl_succ ν t j (by omega)
          have hll : (wrap ν t).lbl ⟨j + 1 + 1, h⟩ = .inr 1 := by
            rw [wrap_lbl]; exact wrapLbl_of_gt ν t (j + 1 + 1) (by omega)
          have hr := hR t (by omega)
          have hpos : (⟨n - 1, by omega⟩ : Fin n) = ⟨j, by omega⟩ := Fin.ext (by simp only; omega)
          rw [hpos] at hr
          have hx0 : erasedX Q ν ⟨j + 1 + 1, h⟩ = 0 := by
            simp [erasedX, show ¬ j + 1 + 1 ≤ n by omega]
          simp only [map_mul, erase_fψ, erase_fe, erasedCross,
            erasedE_wrap, hlj, hll, reduceCtorEq, ↓reduceIte, erase_nceval_two,
            erasedX_succ Q ν j (by omega), hx0, stendhalQ_inl_inr, eval_X_zero_pow,
            ψ_eq_zero j (by omega : n ≤ j + 1), mul_zero, zero_mul, map_zero]
          rw [← map_mul]
          exact hr.symm
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]
  | braid j h s =>
    apply congrArg π
    by_cases hs : s ∈ Set.range (wrap ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        simp [erase_fψ, erase_fe, erasedCross, wrap_lbl, wrapLbl_zero,
          inr_zero_ne_wrapLbl ν t 2 two_ne_zero]
      | succ j =>
        by_cases hj : j + 2 < n
        · simp only [map_mul, map_sub, apply_ite (eraseFree Q ν), erase_fψ, erase_fe,
            erasedCross, erasedE_wrap, wrap_lbl_succ ν t j (by omega),
            wrap_lbl_succ ν t (j + 1) (by omega), wrap_lbl_succ ν t (j + 2) hj, ne_eq,
            Sum.inl.injEq, map_zero, erase_nceval_three, erasedX_succ Q ν j (by omega),
            erasedX_succ Q ν (j + 1) (by omega), erasedX_succ Q ν (j + 2) hj,
            stendhalQ_inl_inl]
          exact braid j hj t
        · have hl : (wrap ν t).lbl ⟨j + 1 + 2, h⟩ = .inr 1 := by
            rw [wrap_lbl]; exact wrapLbl_of_gt ν t (j + 1 + 2) (by omega)
          simp [erase_fψ, erase_fe, erasedCross, hl, wrap_lbl_succ ν t j (by omega),
            ψ_eq_zero (j + 1) (by omega : n ≤ j + 1 + 1)]
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]

omit [DecidableEq I] in
private theorem red_pos (t : Seq ν) (a : Fin m) (ha : ((wrap ν t).lbl a).isRight) :
    a.val = 0 ∨ a.val = n + 1 := by
  rw [wrap_lbl] at ha
  unfold wrapLbl at ha
  split_ifs at ha with h0 h1
  · exact Or.inl h0
  · cases ha
  · right; have := a.isLt; have hm := card_two ν; omega

include hR in
private def eraseAll : StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] C :=
  RingQuot.liftAlgHom k ⟨(π).comp (eraseFree Q ν), fun _ _ h => by
    rcases h with h | ⟨a, s, hs⟩ | ⟨j, h, s, hl, hr⟩
    · exact erase_rel Q Λ ν hR h
    · apply congrArg π
      by_cases hi : s ∈ Set.range (wrap ν)
      · obtain ⟨t, rfl⟩ := hi
        have := red_pos ν t a hs
        have hx : erasedX Q ν a = 0 := by
          unfold erasedX
          split_ifs with hh
          · omega
          · rfl
        simp [erase_fe, erase_fx, hx]
      · simp [erase_fe, erasedE_zero Q ν hi]
    · apply congrArg π
      by_cases hi : s ∈ Set.range (wrap ν)
      · obtain ⟨t, rfl⟩ := hi
        have h1 := red_pos ν t _ hl
        have h2 := red_pos ν t _ hr
        simp only at h1 h2
        have hj : j = 0 := by omega
        subst hj
        simp [erase_fψ, erasedCross]
      · simp [erase_fe, erasedE_zero Q ν hi]⟩

include hR in
private theorem eraseAll_gen (g : Gen μ) :
    eraseAll Q Λ ν hR (RingQuot.mkAlgHom k (Stendhal.Rel k Q Λ ν) (FreeAlgebra.ι k g)) =
      π (eraseGen Q ν g) := by
  trans ((π).comp (eraseFree Q ν)) (FreeAlgebra.ι k g)
  · exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  · rw [AlgHom.comp_apply, eraseFree, FreeAlgebra.lift_ι_apply]

include hR in
private theorem eraseAll_e (s : Seq μ) :
    eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.e s) = π (erasedE Q ν s) := by
  rw [StendhalAlgebraAllOrders.e, KLRAlgebra.e, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν hR (.idem s)

include hR in
private theorem eraseAll_x (a : Fin m) :
    eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.x a) = π (erasedX Q ν a) := by
  rw [StendhalAlgebraAllOrders.x, KLRAlgebra.x, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν hR (.dot a)

include hR in
private theorem eraseAll_ψ (j : ℕ) :
    eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.ψ j) = π (erasedCross Q ν j) := by
  rw [StendhalAlgebraAllOrders.ψ, KLRAlgebra.ψ, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν hR (.cross j)

omit [DecidableEq I] in
theorem wrap_ordered (t : Seq ν) : IsRedOrdered (wrap ν t) :=
  (appendRedLoading_ordered_iff _).2 (SingleRed.ordered ν _)

include hR in
private theorem eraseAll_redOrderedIdem :
    eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = 1 := by
  classical
  rw [StendhalAlgebraAllOrders.redOrderedIdem, map_sum, Finset.sum_filter]
  simp only [eraseAll_e]
  rw [← map_one π, ← erasedE_sum Q ν, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rfl
  · rw [erasedE_zero Q ν, map_zero]
    rintro ⟨t, rfl⟩
    exact hs (wrap_ordered ν t)

include hR in
/-- Erasure on Webster's algebra `T̃^{(λ₁,λ₂)}(ν)` of red-ordered diagrams. -/
private def eraseStendhal : StendhalAlgebra k Q Λ ν →+* C where
  toFun z := eraseAll Q Λ ν hR z.1
  map_one' := eraseAll_redOrderedIdem Q Λ ν hR
  map_mul' x y := map_mul (eraseAll Q Λ ν hR) x.1 y.1
  map_zero' := map_zero (eraseAll Q Λ ν hR)
  map_add' x y := map_add (eraseAll Q Λ ν hR) x.1 y.1

include hR in
/-- **Erasing both red strands of a wrap loading**, `T^{(λ₁,λ₂)}(ν) → R^{λ₁}(ν)`, under the
cyclotomic relation `hR` of the second red strand on the last black strand. -/
def eraseWrap : TensorProductAlgebra k Q Λ ν →+* C :=
  (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.lift (eraseStendhal Q Λ ν hR) (by
    have hJ : StendhalAlgebra.violatedIdeal k Q Λ ν ≤
        TwoSidedIdeal.ker (eraseStendhal Q Λ ν hR) := by
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨s, _, hv, rfl⟩
      apply (TwoSidedIdeal.mem_ker _).mpr
      change eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.e s) = 0
      rw [eraseAll_e, erasedE_zero, map_zero]
      rintro ⟨t, rfl⟩
      obtain ⟨h0, hl⟩ := hv
      rw [wrap_lbl_zero] at hl
      cases hl
    intro a b hab
    change eraseStendhal Q Λ ν hR a = eraseStendhal Q Λ ν hR b
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (TwoSidedIdeal.mem_ker _).mp (hJ ((TwoSidedIdeal.rel_iff _ _ _).mp hab)))

private theorem eraseWrap_mk (z : StendhalAlgebra k Q Λ ν) :
    eraseWrap Q Λ ν hR (TensorProductAlgebra.mk Q Λ ν z) = eraseAll Q Λ ν hR z.1 := rfl

/-- Erasure sends a wrap idempotent to the idempotent of its black word. -/
theorem eraseWrap_e_wrap (t : Seq ν) :
    eraseWrap Q Λ ν hR (TensorProductAlgebra.mk Q Λ ν
      (StendhalAlgebra.e (wrap ν t) (wrap_ordered ν t))) = π (KLRAlgebra.e t) := by
  rw [eraseWrap_mk]
  change eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.e (wrap ν t)) = _
  rw [eraseAll_e, erasedE_wrap]

/-- Erasure kills every red-ordered idempotent other than a wrap idempotent. -/
theorem eraseWrap_e_of_not_wrap (s : Seq μ) (hs : IsRedOrdered s)
    (hw : s ∉ Set.range (wrap ν)) :
    eraseWrap Q Λ ν hR (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)) = 0 := by
  rw [eraseWrap_mk]
  change eraseAll Q Λ ν hR (StendhalAlgebraAllOrders.e s) = 0
  rw [eraseAll_e, erasedE_zero Q ν hw, map_zero]

/-! ### Erasure after appending the second red strand -/

local notation "Λ₀" => (Λ ∘ Fin.castSucc : Fin 1 → I →₀ ℕ)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem appendRedAllOrders_one_val :
    (appendRedAllOrders (ℓ := 1) Q Λ ν 1).val =
      ∑ s : Seq (stendhalWeight 1 ν), StendhalAlgebraAllOrders.e (appendRedLoading s) := by
  have h1 : (1 : StendhalAlgebraAllOrders k Q Λ₀ ν) = ∑ s, StendhalAlgebraAllOrders.e s := by
    simp only [StendhalAlgebraAllOrders.e, ← map_sum, KLRAlgebra.sum_e, map_one]
  rw [h1, map_sum]
  change (∑ s, (appendRedAllOrders (ℓ := 1) Q Λ ν (StendhalAlgebraAllOrders.e s))).val = _
  rw [KLR.Corner.val_sum]
  exact Finset.sum_congr rfl fun s _ => appendRedAllOrders_e Q Λ ν s

include hR in
private theorem eraseAll_appendRed_one :
    eraseAll Q Λ ν hR (appendRedAllOrders (ℓ := 1) Q Λ ν 1).val = 1 := by
  classical
  rw [appendRedAllOrders_one_val, map_sum]
  simp only [eraseAll_e]
  rw [← map_one π, ← erasedE_sum Q ν, map_sum]
  refine (Finset.sum_map Finset.univ
    ⟨appendRedLoading (ℓ := 1), appendRedLoading_injective⟩
    (fun x => π (erasedE Q ν x))).symm.trans (Finset.sum_subset (Finset.subset_univ _) ?_)
  intro s _ hs
  rw [erasedE_zero Q ν, map_zero]
  rintro ⟨t, ht⟩
  exact hs (Finset.mem_map.mpr ⟨SingleRed.insertWord ν t, Finset.mem_univ _, ht⟩)

set_option backward.isDefEq.respectTransparency false in
include hR in
/-- **Erasure inverts appending the second red strand to the cyclotomic projection.** -/
theorem eraseWrap_appendRed_cyclotomicProjection (z : C) :
    eraseWrap Q Λ ν hR (appendRed (ℓ := 1) Q Λ ν
      (SingleRed.cyclotomicProjection Q Λ₀ ν z)).val = z := by
  obtain ⟨w, rfl⟩ := CycKLR.mk_surjective z
  have hz : SingleRed.cyclotomicProjection Q Λ₀ ν (π w) = SingleRed.insertRed Q Λ₀ ν w := by
    exact CycKLR.lift_mk _ _ w
  rw [hz]
  clear hz
  have hT := eraseAll_appendRed_one Q Λ ν hR
  have hE (s : Seq ν) : eraseWrap Q Λ ν hR (appendRed (ℓ := 1) Q Λ ν
      (SingleRed.insertRed Q Λ₀ ν (KLRAlgebra.e s))).val = π (KLRAlgebra.e s) := by
    rw [SingleRed.insertRed_e]
    change eraseAll Q Λ ν hR (appendRedAllOrders (ℓ := 1) Q Λ ν
      (StendhalAlgebraAllOrders.e (SingleRed.insertWord ν s))).val = _
    rw [appendRedAllOrders_e, eraseAll_e]
    exact congrArg π (erasedE_wrap Q ν s)
  have h2 (r : k) : eraseWrap Q Λ ν hR (algebraMap k (TensorProductAlgebra k Q Λ ν) r) =
      algebraMap k C r := by
    change eraseAll Q Λ ν hR
      (algebraMap k _ r * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = _
    rw [map_mul, AlgHom.commutes, eraseAll_redOrderedIdem, mul_one]
  induction w using klr_induction with
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, ← KLRAlgebra.sum_e, Finset.smul_sum]
    simp only [map_sum, KLR.Corner.val_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower, KLR.Corner.val_smul, Algebra.smul_def,
      map_mul, hE, h2, map_smul, Algebra.smul_def]
  | hadd u v hu hv => simp only [map_add, KLR.Corner.val_add, hu, hv]
  | hmul u v hu hv => simp only [map_mul, KLR.Corner.val_mul, hu, hv]
  | he s => exact hE s
  | hx a =>
    rw [SingleRed.insertRed_x]
    change eraseAll Q Λ ν hR (appendRedAllOrders (ℓ := 1) Q Λ ν
      (StendhalAlgebraAllOrders.x (SingleRed.blackPos ν a))).val = _
    rw [appendRedAllOrders_x, map_mul, hT, mul_one, eraseAll_x]
    change π (erasedX Q ν ⟨a.val + 1, _⟩) = _
    rw [erasedX_succ Q ν a.val a.isLt]
  | hψ j =>
    by_cases h : j + 1 < n
    · rw [SingleRed.insertRed_ψ Q Λ₀ ν j h]
      change eraseAll Q Λ ν hR (appendRedAllOrders (ℓ := 1) Q Λ ν
        (StendhalAlgebraAllOrders.ψ (j + 1))).val = _
      rw [appendRedAllOrders_ψ Q Λ ν (j + 1) (by simp [stendhalWeight]; omega), map_mul, hT,
        mul_one, eraseAll_ψ]
      rfl
    · simp [ψ_eq_zero j (Nat.le_of_not_gt h)]

end Categorification.Stendhal.TwoRedErase
