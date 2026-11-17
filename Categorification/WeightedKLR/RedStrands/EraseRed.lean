/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicProjection

/-!
# Erasing the leftmost red strand

Webster, arXiv:1309.3796v2, §4.4, Theorem 4.20. On surviving words erasure
removes the leftmost red strand. It sends the first dot and first crossing
to zero, and shifts the indices of the remaining dots and crossings down
by one. The square relation for the first crossing then holds precisely by
the cyclotomic relation on the first black dot. This gives the inverse to
`cyclotomicProjection` in every black weight.
-/

noncomputable section
namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight 1 ν
local notation "m" => Multiset.card μ
local notation "n" => Multiset.card ν
local notation "B" => KLRAlgebra k Q ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "π" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "Fr" => FreeAlgebra k (Gen μ)

omit [DecidableEq I] in
private theorem card_red : m = n + 1 := by simp [stendhalWeight]

omit [DecidableEq I] in
theorem insertWord_injective : Function.Injective (insertWord ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  exact Sum.inl.inj ((insertWord_black ν s a).symm.trans
    ((congrArg (fun z : Seq μ => z.lbl (blackPos ν a)) h).trans (insertWord_black ν t a)))

omit [DecidableEq I] in
private theorem blackPos_swap (j : ℕ) (a : Fin n) :
    sadj m (j+1) (blackPos ν a) = blackPos ν (sadj n j a) := by
  by_cases hj : j+1 < n
  · have hm : j+1+1 < m := by rw [card_red]; omega
    apply Fin.ext
    rw [sadj_apply_val hm]
    change (if a.val + 1 = j + 1 then j + 1 + 1 else
      if a.val + 1 = j + 1 + 1 then j + 1 else a.val + 1) = (sadj n j a).val + 1
    rw [sadj_apply_val hj]
    split_ifs <;> omega
  · have h : ¬ j+1+1 < m := by rw [card_red]; omega
    simp [sadj, hj, h]

omit [DecidableEq I] in
private theorem word_swap (j : ℕ) (s : Seq ν) :
    sadj m (j+1) • insertWord ν s = insertWord ν (sadj n j • s) := by
  apply Subtype.ext
  funext a
  rcases ha : a.val with _ | u
  · have h := Fin.ext (b := (⟨0, by simp [stendhalWeight]⟩ : Fin m)) ha
    subst a
    rw [sadj_smul_apply, sadj_apply_of_ne _ (by simp) (by simp)]
    exact (insertWord_head ν s).trans (insertWord_head ν _).symm
  · have hu : u < n := by have := a.isLt; have := card_red ν; omega
    have h : a = blackPos ν ⟨u, hu⟩ := Fin.ext ha
    subst a
    rw [sadj_smul_apply, blackPos_swap]
    change (insertWord ν s).lbl _ = (insertWord ν _).lbl _
    rw [insertWord_black, insertWord_black]
    exact congrArg Sum.inl (sadj_smul_apply j s _).symm

/-- A red-left word maps to the corresponding black idempotent. Every other
word maps to zero. -/
private def erasedE (s : Seq μ) : B :=
  ∑ t : Seq ν, if insertWord ν t = s then KLRAlgebra.e t else 0

private theorem erasedE_word (s : Seq ν) : erasedE Q ν (insertWord ν s) = KLRAlgebra.e s := by
  classical
  simp [erasedE, (insertWord_injective ν).eq_iff]

private theorem erasedE_zero {s : Seq μ} (hs : s ∉ Set.range (insertWord ν)) :
    erasedE Q ν s = 0 := by
  have hn (t : Seq ν) : insertWord ν t ≠ s := fun h => hs ⟨t, h⟩
  simp [erasedE, hn]

private theorem erasedE_sum : ∑ s : Seq μ, erasedE Q ν s = 1 := by
  classical
  simp only [erasedE]
  rw [Finset.sum_comm]
  simp [KLRAlgebra.sum_e]

private def erasedX (a : Fin m) : B :=
  if h : a.val = 0 then 0 else KLRAlgebra.x ⟨a.val - 1, by
    have := a.isLt; have := card_red ν; omega⟩

private def erasedCross : ℕ → B
  | 0 => 0
  | j+1 => KLRAlgebra.ψ j

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

private theorem erasedX_zero (h : 0 < m) : erasedX Q ν ⟨0, h⟩ = 0 := by simp [erasedX]
private theorem erasedX_succ (j : ℕ) (h : j+1 < m) :
    erasedX Q ν ⟨j+1, h⟩ = KLRAlgebra.x ⟨j, by rw [card_red] at h; omega⟩ := by simp [erasedX]

private theorem erase_eval {d : ℕ} (v : Fin d → Fr) (p : MvPolynomial (Fin d) k) :
    eraseFree Q ν (ncEval v p) = ncEval (fun a => eraseFree Q ν (v a)) p := by
  simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow]

omit [DecidableEq I] in
private theorem word_lbl_succ (s : Seq ν) (j : ℕ) (h : j+1 < m) :
    (insertWord ν s).lbl ⟨j+1,h⟩ = .inl (s.lbl ⟨j, by have := card_red ν; omega⟩) :=
  insertWord_black ν s ⟨j, by have := card_red ν; omega⟩

private theorem erasedE_mul (s t : Seq μ) :
    erasedE Q ν s * erasedE Q ν t = if s = t then erasedE Q ν s else 0 := by
  by_cases he : s = t
  · subst t
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨i, rfl⟩ := hs
      simp [erasedE_word, e_mul_self]
    · simp [erasedE_zero Q ν hs]
  · rw [ite_eq_right_iff.mpr (fun h => (he h).elim)]
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨i, rfl⟩ := hs
      by_cases ht : t ∈ Set.range (insertWord ν)
      · obtain ⟨j, rfl⟩ := ht
        have hij : i ≠ j := fun h => he (congrArg (insertWord ν) h)
        simp [erasedE_word, e_mul_e, hij]
      · simp [erasedE_zero Q ν ht]
    · simp [erasedE_zero Q ν hs]

private theorem erasedX_mul_e (a : Fin m) (s : Seq μ) :
    erasedX Q ν a * erasedE Q ν s = erasedE Q ν s * erasedX Q ν a := by
  by_cases hs : s ∈ Set.range (insertWord ν)
  · obtain ⟨i, rfl⟩ := hs
    rw [erasedE_word]
    unfold erasedX
    split <;> simp [x_mul_e]
  · simp [erasedE_zero Q ν hs]

private theorem erasedCross_mul_e (j : ℕ) (s : Seq μ) :
    erasedCross Q ν j * erasedE Q ν s =
      erasedE Q ν (sadj m j • s) * erasedCross Q ν j := by
  cases j with
  | zero => simp [erasedCross]
  | succ j =>
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨i, rfl⟩ := hs
      simp [word_swap, erasedCross, erasedE_word, ψ_mul_e]
    · have hn : sadj m (j+1) • s ∉ Set.range (insertWord ν) := by
        rintro ⟨i, h⟩
        exact hs ⟨_, by rw [← word_swap, h, sadj_smul_smul]⟩
      simp [erasedE_zero Q ν hs, erasedE_zero Q ν hn]

private theorem erasedX_comm (a b : Fin m) :
    erasedX Q ν a * erasedX Q ν b = erasedX Q ν b * erasedX Q ν a := by
  unfold erasedX
  split_ifs <;> simp [x_mul_x]

private theorem erasedX_cross (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j+1) :
    erasedX Q ν a * erasedCross Q ν j = erasedCross Q ν j * erasedX Q ν a := by
  cases j with
  | zero => simp [erasedCross]
  | succ j =>
    unfold erasedX
    split
    · simp
    · exact x_mul_ψ _ j (by simp; omega) (by simp; omega)

private theorem erase_nceval_two (j : ℕ) (h : j+1 < m) (p : MvPolynomial (Fin 2) k) :
    eraseFree Q ν (ncEval ![fx k μ ⟨j, by omega⟩, fx k μ ⟨j+1,h⟩] p) =
      ncEval ![erasedX Q ν ⟨j, by omega⟩, erasedX Q ν ⟨j+1,h⟩] p := by
  rw [erase_eval]
  congr 1
  funext a
  fin_cases a <;> apply erase_fx

private theorem erase_nceval_three (j : ℕ) (h : j+2 < m) (p : MvPolynomial (Fin 3) k) :
    eraseFree Q ν (ncEval ![fx k μ ⟨j, by omega⟩, fx k μ ⟨j+1,by omega⟩,
      fx k μ ⟨j+2,h⟩] p) =
      ncEval ![erasedX Q ν ⟨j, by omega⟩, erasedX Q ν ⟨j+1,by omega⟩,
        erasedX Q ν ⟨j+2,h⟩] p := by
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

private theorem erase_rel {a b : Fr} (h : KLR.Rel k (stendhalQ Q Λ) μ a b) :
    π (eraseFree Q ν a) = π (eraseFree Q ν b) := by
  classical
  have hm := card_red ν
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
    | succ j => simp [erase_fψ, erasedCross, ψ_eq_zero j (by omega : n ≤ j+1)]
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
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        simp [erase_fe, erase_fx, erase_fψ, erasedCross, insertWord_head,
          word_lbl_succ]
      | succ j =>
        simp only [map_mul, map_sub, apply_ite (eraseFree Q ν), map_zero, erase_fx, erase_fe, erase_fψ,
          erasedCross, erasedX_succ, erasedE_word, word_lbl_succ, Sum.inl.injEq]
        first | exact dot_cross_left j (by omega) t | exact dot_cross_right j (by omega) t
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]
  | cross_sq j h s =>
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        have hc := CycKLR.mk_aeval_x_mul_e (Q := Q) (a := fun i => Polynomial.X ^ Λ 0 i)
          t (by omega : 0 < n)
        simp only [map_pow, Polynomial.aeval_X] at hc
        simpa [apply_ite, erase_fψ, erase_fe, erasedCross, insertWord_head, word_lbl_succ,
          erase_nceval_two, erasedX_zero, erasedX_succ, stendhalQ, eval_X_one_pow, erasedE_word]
          using hc.symm
      | succ j =>
        apply congrArg π
        simp only [map_mul, apply_ite (eraseFree Q ν), erase_fψ, erase_fe, erasedCross, erasedE_word,
          word_lbl_succ, Sum.inl.injEq, map_zero, erase_nceval_two, erasedX_succ, stendhalQ_inl_inl]
        exact ψ_sq j (by omega) t
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]
  | braid j h s =>
    apply congrArg π
    by_cases hs : s ∈ Set.range (insertWord ν)
    · obtain ⟨t, rfl⟩ := hs
      cases j with
      | zero =>
        simp [erase_fψ, erase_fe, erasedCross, insertWord_head, word_lbl_succ]
      | succ j =>
        simp only [map_mul, map_sub, apply_ite (eraseFree Q ν), erase_fψ, erase_fe, erasedCross, erasedE_word,
          word_lbl_succ, ne_eq, Sum.inl.injEq, map_zero, erase_nceval_three, erasedX_succ, stendhalQ_inl_inl]
        exact braid j (by omega) t
    · simp [apply_ite, erase_fe, erasedE_zero Q ν hs]

omit [DecidableEq I] in
private theorem red_pos_zero (s : Seq ν) (a : Fin m) (ha : ((insertWord ν s).lbl a).isRight) :
    a.val = 0 := by
  cases h : a.val with
  | zero => rfl
  | succ j =>
    have hj : j+1 < m := h ▸ a.isLt
    rw [show a = ⟨j+1, hj⟩ from Fin.ext h, word_lbl_succ] at ha
    cases ha

private def eraseAll : StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] C :=
  RingQuot.liftAlgHom k ⟨(π).comp (eraseFree Q ν), fun _ _ h => by
    rcases h with h | ⟨a, s, hs⟩ | ⟨j, h, s, _, hr⟩
    · exact erase_rel Q Λ ν h
    · apply congrArg π
      by_cases hi : s ∈ Set.range (insertWord ν)
      · obtain ⟨t, rfl⟩ := hi
        simp [map_mul, erase_fe, erase_fx, erasedX, red_pos_zero ν t a hs]
      · simp [erase_fe, erasedE_zero Q ν hi]
    · apply congrArg π
      by_cases hi : s ∈ Set.range (insertWord ν)
      · obtain ⟨t, rfl⟩ := hi
        have := red_pos_zero ν t ⟨j+1,h⟩ hr
        simp at this
      · simp [erase_fe, erasedE_zero Q ν hi]⟩

private theorem eraseAll_gen (g : Gen μ) :
    eraseAll Q Λ ν (RingQuot.mkAlgHom k (Stendhal.Rel k Q Λ ν) (FreeAlgebra.ι k g)) =
      π (eraseGen Q ν g) := by
  trans ((π).comp (eraseFree Q ν)) (FreeAlgebra.ι k g)
  · exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  · rw [AlgHom.comp_apply, eraseFree, FreeAlgebra.lift_ι_apply]

private theorem eraseAll_e (s : Seq μ) :
    eraseAll Q Λ ν (StendhalAlgebraAllOrders.e s) = π (erasedE Q ν s) := by
  rw [StendhalAlgebraAllOrders.e, KLRAlgebra.e, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν (.idem s)

private theorem eraseAll_x (a : Fin m) :
    eraseAll Q Λ ν (StendhalAlgebraAllOrders.x a) = π (erasedX Q ν a) := by
  rw [StendhalAlgebraAllOrders.x, KLRAlgebra.x, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν (.dot a)

private theorem eraseAll_ψ (j : ℕ) :
    eraseAll Q Λ ν (StendhalAlgebraAllOrders.ψ j) = π (erasedCross Q ν j) := by
  rw [StendhalAlgebraAllOrders.ψ, KLRAlgebra.ψ, StendhalAlgebraAllOrders.ofKLR_mk]
  exact eraseAll_gen Q Λ ν (.cross j)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Erasing the one red strand descends to the violating quotient. -/
def eraseRed : TensorProductAlgebra k Q Λ ν →ₐ[k] C := by
  let J := StendhalAlgebra.violatedIdeal k Q Λ ν
  let f := (eraseAll Q Λ ν).comp (orderedEquiv Q Λ ν).symm.toAlgHom
  refine J.ringCon.liftₐ f ?_
  have hJ : J ≤ TwoSidedIdeal.ker f.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨s, _, ⟨_, hs⟩, rfl⟩
    apply (TwoSidedIdeal.mem_ker f.toRingHom).mpr
    change eraseAll Q Λ ν (StendhalAlgebraAllOrders.e s) = 0
    rw [eraseAll_e, erasedE_zero, map_zero]
    rintro ⟨t, rfl⟩
    rw [insertWord_head] at hs
    cases hs
  intro a b hab
  change f a = f b
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (TwoSidedIdeal.mem_ker f.toRingHom).mp (hJ ((TwoSidedIdeal.rel_iff _ _ _).mp hab))

private theorem eraseRed_mk (z : StendhalAlgebraAllOrders k Q Λ ν) :
    eraseRed Q Λ ν (mk Q Λ ν z) = eraseAll Q Λ ν z := rfl

/-- Erasure is left inverse to red-left insertion on the cyclotomic quotient. -/
theorem eraseRed_projection (z : C) :
    eraseRed Q Λ ν (cyclotomicProjection Q Λ ν z) = z := by
  obtain ⟨w, rfl⟩ := CycKLR.mk_surjective z
  rw [cyclotomicProjection, CycKLR.lift_mk]
  induction w using klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hmul u v hu hv => simp only [map_mul, hu, hv]
  | he s => rw [insertRed_e, eraseRed_mk, eraseAll_e, erasedE_word]
  | hx a =>
    rw [insertRed_x, eraseRed_mk, eraseAll_x]
    change π (erasedX Q ν ⟨a.val+1, _⟩) = _
    rw [erasedX_succ]
  | hψ j =>
    by_cases h : j+1 < n
    · rw [insertRed_ψ Q Λ ν j h, eraseRed_mk, eraseAll_ψ]
      rfl
    · simp [ψ_eq_zero j (Nat.le_of_not_gt h)]

/-- **Webster, arXiv:1309.3796v2, §4.4, Theorem 4.20.** In every black
weight the ordinary cyclotomic quotient is isomorphic to the tensor product algebra
with one red strand. The forward map inserts the red strand on the left, and
the inverse erases it from surviving diagrams. -/
def cyclotomicEquiv : C ≃ₐ[k] TensorProductAlgebra k Q Λ ν :=
  AlgEquiv.ofAlgHom (cyclotomicProjection Q Λ ν) (eraseRed Q Λ ν)
    (AlgHom.ext fun z => by
      obtain ⟨w, rfl⟩ := cyclotomicProjection_surjective Q Λ ν z
      exact congrArg (cyclotomicProjection Q Λ ν) (eraseRed_projection Q Λ ν w))
    (AlgHom.ext (eraseRed_projection Q Λ ν))

end Categorification.Stendhal.SingleRed
