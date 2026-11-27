/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerWords
import Categorification.WeightedKLR.Rigidity.CupCapMidNull
import Categorification.WeightedKLR.Rigidity.CupCapEndFactor
import Categorification.KLR.CyclotomicExact

/-!
# Diagrams in the window before `λ_{j+1}` and dots outside it

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`.
For a loading `s` of `λ` the strands of `λ⁺` split into the window `[c, c + N)`, `c = midPos j s`,
holding the strands at the maximum, and the strands of `λ` around it (`outPos`). A diagram
`x^p ψ_β e(t)` at the maximum placed in the window is `x^{p'} ψ_{c + β} e(midSeq s t)`
(`insertMap_pol_ψw_e`); dots outside the window commute with crossings in it
(`pol_out_mul_ψw_shift`); and exponent vectors of `λ⁺` split along the two parts (`midExp`).

## Main definitions

* `CupCap.midPosEquiv`, `CupCap.outPos`: the positions of the two parts.
* `CupCap.midExp`: exponent vectors split along the two parts.

## Main results

* `CupCap.insertMap_pol_ψw_e`: a diagram at the maximum in the window.
* `CupCap.pol_out_mul_ψw_shift`: dots outside the window commute with crossings in it.
* `CupCap.monomial_midExp`: monomials split along the two parts.
* `CupCap.midMapKLR_mul_e_midSeq`: the diagrams at the maximum above `e(midSeq s t)`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

/-! ### Positions -/

section Positions

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

theorem insert_window_le {n : ℕ} (hn : n ≤ m) : n + N ≤ M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

variable (j ν₀) in
/-- The positions of `λ⁺` split into the strands of `λ` and the window at `midPos j s`. -/
def midPosEquiv (s : Seq (stendhalWeight ℓ ν)) : Fin m ⊕ Fin N ≃ Fin M :=
  (insertPos m N (midPos j s) (midPos_le j s)).trans
    (finCongr (card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)).symm)

variable (j ν₀) in
/-- The position of the strand `a` of `λ` in `λ⁺`, around the window at `midPos j s`. -/
def outPos (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) : Fin M := midPosEquiv j ν₀ s (.inl a)

theorem outPos_val (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    (outPos j ν₀ s a).val = if a.val < midPos j s then a.val else a.val + N := by
  simp only [outPos, midPosEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    insertPos_inl_val]

theorem midPosEquiv_inr (s : Seq (stendhalWeight ℓ ν)) (b : Fin N) :
    midPosEquiv j ν₀ s (.inr b) = winPos (midPos_add_N_le j ν₀ s) b :=
  Fin.ext (by simp [midPosEquiv])

theorem outPos_injective (s : Seq (stendhalWeight ℓ ν)) : Function.Injective (outPos j ν₀ s) :=
  fun _ _ h => Sum.inl_injective ((midPosEquiv j ν₀ s).injective h)

theorem outPos_ne_winPos (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) (b : Fin N) :
    outPos j ν₀ s a ≠ winPos (midPos_add_N_le j ν₀ s) b := by
  rw [outPos, ← midPosEquiv_inr]
  exact fun h => Sum.inl_ne_inr ((midPosEquiv j ν₀ s).injective h)

theorem outPos_val_ne (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) {q : ℕ} (hq : q < N) :
    (outPos j ν₀ s a).val ≠ midPos j s + q := by
  rw [outPos_val]; split_ifs <;> omega

theorem midSeq_lbl_outPos (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (a : Fin m) : (midSeq j hj s t).lbl (outPos j ν₀ s a) = oldColour j hj (s.lbl a) := by
  rw [← midSeq_lbl_old (hj := hj) s t a]
  congr 1
  apply Fin.ext
  rw [outPos_val, Fin.val_cast, insertPos_inl_val, Multiset.card_map]

end Positions

/-! ### Exponent vectors -/

section Exponents

/-- Exponent vectors along a decomposition `α ⊕ β ≃ γ`. -/
theorem domCongr_sumFinsupp_symm {α β γ : Type*} (e : α ⊕ β ≃ γ) (d : (α →₀ ℕ) × (β →₀ ℕ)) :
    Finsupp.domCongr e (Finsupp.sumFinsuppEquivProdFinsupp.symm d) =
      d.1.mapDomain (e ∘ Sum.inl) + d.2.mapDomain (e ∘ Sum.inr) := by
  classical
  have hl : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have hr : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  ext c
  obtain ⟨x, rfl⟩ := e.surjective c
  rcases x with a | b
  · rw [Finsupp.coe_add, Pi.add_apply, show e (Sum.inl a) = (e ∘ Sum.inl) a from rfl,
      Finsupp.mapDomain_apply_of_injective hl, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨b, hb⟩
      exact Sum.inr_ne_inl (e.injective hb)
  · rw [Finsupp.coe_add, Pi.add_apply, show e (Sum.inr b) = (e ∘ Sum.inr) b from rfl,
      Finsupp.mapDomain_apply_of_injective hr, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr (e.injective ha)

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (j ν₀) in
/-- Exponent vectors of `λ⁺` split into the strands of `λ` and the window at `midPos j s`. -/
def midExp (s : Seq (stendhalWeight ℓ ν)) : (Fin m →₀ ℕ) × (Fin N →₀ ℕ) ≃ (Fin M →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr (midPosEquiv j ν₀ s)).toEquiv

theorem midExp_eq (s : Seq (stendhalWeight ℓ ν)) (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) :
    midExp j ν₀ s d = d.1.mapDomain (outPos j ν₀ s) +
      d.2.mapDomain (winPos (midPos_add_N_le j ν₀ s)) := by
  rw [midExp, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
    domCongr_sumFinsupp_symm]
  congr 2

theorem midExp_outPos (s : Seq (stendhalWeight ℓ ν)) (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ))
    (a : Fin m) : midExp j ν₀ s d (outPos j ν₀ s a) = d.1 a := by
  simp [midExp, outPos]

theorem midExp_winPos (s : Seq (stendhalWeight ℓ ν)) (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ))
    (b : Fin N) : midExp j ν₀ s d (winPos (midPos_add_N_le j ν₀ s) b) = d.2 b := by
  rw [← midPosEquiv_inr]
  simp [midExp]

theorem monomial_midExp {k : Type*} [CommRing k] (s : Seq (stendhalWeight ℓ ν))
    (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) :
    (monomial (midExp j ν₀ s d) 1 : MvPolynomial (Fin M) k) =
      rename (outPos j ν₀ s) (monomial d.1 1) *
        rename (winPos (midPos_add_N_le j ν₀ s)) (monomial d.2 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, one_mul, midExp_eq]

end Exponents

/-! ### Diagrams in the window -/

section Window

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

/-- Polynomials at the maximum, placed in the window `[n, n + N)`. -/
theorem insertMap_pol (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (p : MvPolynomial (Fin N) k) :
    ι s n hn (pol p) = pol (rename (winPos (insert_window_le (ν₀ := ν₀) hn)) p) * E s n hn := by
  change (((insertEmb s n hn).hom (stendhalQ Q (plusLabels Λ Λc j hj)))
    (KLRAlgebra.relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc) (pol p))).val = _
  rw [relabelHom_pol, BlockEmb.hom_pol, val_polCorner, rename_rename]
  congr 3

/-- **A diagram `x^p ψ_β e(t)` at the maximum, in the window `[n, n + N)`**, is
`x^{p'} ψ_{n + β} e(insertSeq s n t)`. -/
theorem insertMap_pol_ψw_e (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (p : MvPolynomial (Fin N) k) {β : List ℕ} (hβ : ValidWord N β)
    (t : Seq (stendhalWeight 2 ν₀)) :
    ι s n hn (pol p * ψw β * KLRAlgebra.e t) =
      pol (rename (winPos (insert_window_le (ν₀ := ν₀) hn)) p) * ψw (shiftWord n β) *
        KLRAlgebra.e (insertSeq s n hn (Seq.map (cupColour j hj) t)) := by
  have hE := eSum_idem (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
  have hβ' : ValidWord (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) j hj))) β :=
    by rwa [Multiset.card_map]
  have hc := (insertEmb (j := j) (hj := hj) (ν₀ := ν₀) s n hn).eSum_mul_ψw
    (Q := stendhalQ Q (plusLabels Λ Λc j hj)) (k := k) hβ'
  change (E s n hn * ψw (β.map (n + ·)) : Rp) = ψw (β.map (n + ·)) * E s n hn at hc
  rw [show shiftWord n β = β.map (n + ·) from rfl, insertMap_mul, insertMap_mul, insertMap_pol,
    insertMap_ψw s hn β hβ, insertMap_e,
    ← mul_assoc, mul_assoc _ (E s n hn) (E s n hn), hE.eq, mul_assoc (pol _) (E s n hn), hc,
    ← mul_assoc, mul_assoc _ (E s n hn), eSum_mul_e_insertSeq]

/-- A polynomial in the dots outside the window commutes with a crossing in it. -/
theorem ψ_mul_pol_out (s : Seq (stendhalWeight ℓ ν)) (p : MvPolynomial (Fin m) k) {q : ℕ}
    (hq : q + 1 < N) :
    (ψ (midPos j s + q) * pol (rename (outPos j ν₀ s) p) : Rp) =
      pol (rename (outPos j ν₀ s) p) * ψ (midPos j s + q) := by
  have hqM : midPos j s + q + 1 < M := by
    have := midPos_add_N_le j ν₀ s; omega
  refine ψ_mul_pol_of_symm _ hqM ?_
  rw [swapPol, rename_rename]
  suffices hf : (⇑(swap (⟨midPos j s + q, by omega⟩ : Fin M) ⟨midPos j s + q + 1, hqM⟩) ∘
      outPos j ν₀ s) = outPos j ν₀ s by rw [hf]
  funext a
  have h1 := outPos_val_ne (j := j) (ν₀ := ν₀) s a (q := q) (by omega)
  have h2 := outPos_val_ne (j := j) (ν₀ := ν₀) s a (q := q + 1) hq
  rw [Function.comp_apply, swap_apply_of_ne_of_ne (fun h => h1 (congrArg Fin.val h))
    (fun h => h2 (by rw [h]; rfl))]

/-- **Dots outside the window commute with the crossings in it.** -/
theorem pol_out_mul_ψw_shift (s : Seq (stendhalWeight ℓ ν)) (p : MvPolynomial (Fin m) k)
    {β : List ℕ} (hβ : ValidWord N β) :
    (pol (rename (outPos j ν₀ s) p) * ψw (shiftWord (midPos j s) β) : Rp) =
      ψw (shiftWord (midPos j s) β) * pol (rename (outPos j ν₀ s) p) := by
  induction β with
  | nil => simp [shiftWord]
  | cons q β ih =>
    obtain ⟨hq, hβ⟩ := validWord_cons.1 hβ
    have : shiftWord (midPos j s) (q :: β) = (midPos j s + q) :: shiftWord (midPos j s) β := rfl
    rw [this, ψw_cons, ← mul_assoc, ← ψ_mul_pol_out s p hq, mul_assoc, ih hβ, mul_assoc]

/-- The diagrams at the maximum above `e(midSeq s t)` are those in the window of `s`. -/
theorem midMapKLR_mul_e_midSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (x : Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ x * KLRAlgebra.e (midSeq j hj s t) =
      ι s (midPos j s) (midPos_le j s) x * KLRAlgebra.e (midSeq j hj s t) := by
  rw [midMapKLR, Finset.sum_mul, Finset.sum_eq_single s _ (by simp)]
  intro s' _ hs'
  have hmem : midSeq j hj s t ∈ insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s)
      (midPos_le j s) := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hnot : midSeq j hj s t ∉ insertSet (j := j) (hj := hj) (ν₀ := ν₀) s' (midPos j s')
      (midPos_le j s') := fun h =>
    Finset.disjoint_left.1 (disjoint_insertSet_midPos (j := j) (hj := hj) (ν₀ := ν₀)
      (Ne.symm hs')) hmem h
  rw [← insertMap_mul_eSum, mul_assoc, eSum_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hnot),
    mul_zero]

/-- The diagrams at the maximum on the idempotent `e(t)` are the idempotents `e(midSeq s t)`. -/
theorem midMapKLR_e (t : Seq (stendhalWeight 2 ν₀)) :
    midMapKLR j hj Q Λ Λc ν ν₀ (KLRAlgebra.e t) =
      ∑ s : Seq (stendhalWeight ℓ ν), KLRAlgebra.e (midSeq j hj s t) :=
  Finset.sum_congr rfl fun s _ => insertMap_e s (midPos_le j s) t

theorem midMapKLR_sum {ι' : Type*} (S : Finset ι') (f : ι' → Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ (∑ x ∈ S, f x) = ∑ x ∈ S, midMapKLR j hj Q Λ Λc ν ν₀ (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, midMapKLR_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, midMapKLR_add, ih]

end Window

end Categorification.Stendhal.CupCap
