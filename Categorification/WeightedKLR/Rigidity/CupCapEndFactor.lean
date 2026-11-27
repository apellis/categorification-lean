/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapModelInverse
import Categorification.KLR.InductionFree

/-!
# Diagrams of `λ⁺` that factor through the two blocks at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`: a diagram of `λ` on
the first `m` strands of `λ⁺` and a diagram at the maximum on the last `N` strands, both written
with dots on top, multiply to a diagram of `λ⁺` with dots on top whose word is the concatenation of
the two words, the second shifted by `m` (`prefixMapKLR_mul_endMapKLR`). This is the KLR form of
the factorization `x^u ψ_{(a × b) σ} e(i) = (x^{u₁} ψ_a ⊗ x^{u₂} ψ_b) ψ_σ e(i)` used to see the
corner of `T̃^{λ⁺}` cut by the end block as a sum of projective modules over the end block
(cf. Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.16).

## Main results

* `prefixMapKLR_pol`, `endMapKLR_pol`, `prefixMapKLR_ψw`, `endMapKLR_ψw`: the two blocks on
  polynomials and words.
* `prefixMapKLR_mul_endMapKLR`: the factorization.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MvPolynomial

section Factor

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "σ" => Multiset.map (cupColour (I := I) ℓ le_rfl) (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eₑ" => KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (endSet ν ν₀)

/-- Relabelling sends polynomials to the same polynomials in the cast variables. -/
theorem relabelHom_pol {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
    {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
    {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)
    (p : MvPolynomial (Fin (Multiset.card ν₁)) k) :
    relabelHom R (pol p) = pol (rename (Fin.cast R.card_eq) p) := by
  have : (relabelHom R).comp (pol (Q := Q₁)) =
      (pol (Q := Q₂)).comp (rename (Fin.cast R.card_eq)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  exact congrArg (fun φ : MvPolynomial (Fin (Multiset.card ν₁)) k →ₐ[k] _ => φ p) this

/-- Relabelling sends words in the crossings to the same words. -/
theorem relabelHom_ψw {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
    {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
    {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂) (ρ : List ℕ) :
    relabelHom R (ψw ρ) = ψw ρ := by
  induction ρ with
  | nil => simp
  | cons j ρ ih => rw [ψw_cons, ψw_cons, map_mul, relabelHom_ψ, ih]

variable (ν₀) in
/-- The positions of the strands of `λ` in `λ⁺`. -/
def posL (a : Fin m) : Fin M :=
  ⟨a.val, by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩

variable (ν) in
/-- The positions of the strands at the maximum in `λ⁺`. -/
def posR (b : Fin N) : Fin M :=
  ⟨m + b.val, by have := m_add_N (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩

omit [DecidableEq I] in
@[simp] theorem posL_val (a : Fin m) : (posL (ν₀ := ν₀) a).val = a.val := rfl

omit [DecidableEq I] in
@[simp] theorem posR_val (b : Fin N) : (posR (ν := ν) (ℓ := ℓ) b).val = m + b.val := rfl

theorem prefixMapKLR_pol (p : MvPolynomial (Fin m) k) :
    prefixMapKLR Q Λ Λc ν ν₀ (pol p) = pol (rename (posL ν₀) p) * Eₑ := by
  rw [prefixMapKLR, relabelHom_pol, BlockEmb.hom_pol, val_polCorner, rename_rename]
  congr 3
  congr 1
  funext a
  exact Fin.ext (by simp [prefixWindow, BlockEmb.window, windowPos, posL])

theorem endMapKLR_pol (p : MvPolynomial (Fin N) k) :
    endMapKLR Q Λ Λc ν ν₀ (pol p) = pol (rename (posR ν) p) * Eₑ := by
  rw [endMapKLR, relabelHom_pol, BlockEmb.hom_pol, val_polCorner, rename_rename]
  rfl

theorem prefixMapKLR_ψw {α : List ℕ} (hα : ValidWord m α) :
    prefixMapKLR Q Λ Λc ν ν₀ (ψw α) = ψw α * Eₑ := by
  rw [prefixMapKLR, relabelHom_ψw, BlockEmb.val_hom_ψw _ (by rwa [card_μL])]
  congr 2
  simp [prefixWindow, BlockEmb.window]

theorem endMapKLR_ψw {β : List ℕ} (hβ : ValidWord N β) :
    endMapKLR Q Λ Λc ν ν₀ (ψw β) = ψw (shiftWord m β) * Eₑ := by
  rw [endMapKLR, relabelHom_ψw, BlockEmb.val_hom_ψw _ (by rwa [card_σ])]
  rfl

theorem eSum_end_mul_ψw_prefix {α : List ℕ} (hα : ValidWord m α) :
    (Eₑ * ψw α : Rp) = ψw α * Eₑ := by
  have h := (prefixWindow ν ν₀).eSum_mul_ψw
    (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (k := k) (α := α) (by rwa [card_μL])
  simpa [prefixWindow, BlockEmb.window] using h

theorem eSum_end_mul_ψw_end {β : List ℕ} (hβ : ValidWord N β) :
    (Eₑ * ψw (shiftWord m β) : Rp) = ψw (shiftWord m β) * Eₑ :=
  (endWindow ν ν₀).eSum_mul_ψw
    (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (k := k) (α := β) (by rwa [card_σ])

theorem prefixMapKLR_e_mul_endMapKLR_e (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) :
    prefixMapKLR Q Λ Λc ν ν₀ (e s) * endMapKLR Q Λ Λc ν ν₀ (e t) =
      e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl (Seq.map (cupColour ℓ le_rfl) t)) := by
  rw [← insertMap_eq_prefix_mul_end, insertMap_e]

/-- **Diagrams of the two blocks multiply to a diagram of `λ⁺`** (dots on top): the words are
concatenated, the second shifted by `m`, and the bottoms are concatenated. -/
theorem prefixMapKLR_mul_endMapKLR (p₁ : MvPolynomial (Fin m) k) (p₂ : MvPolynomial (Fin N) k)
    {α β : List ℕ} (hα : ValidWord m α) (hβ : ValidWord N β)
    (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    prefixMapKLR Q Λ Λc ν ν₀ (pol p₁ * ψw α * e s) *
        endMapKLR Q Λ Λc ν ν₀ (pol p₂ * ψw β * e t) =
      pol (rename (posL ν₀) p₁ * rename (posR ν) p₂) * ψw (α ++ shiftWord m β) *
        e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl (Seq.map (cupColour ℓ le_rfl) t)) := by
  have hc := commute_prefixMapKLR_endMapKLR Q Λ Λc ν ν₀
  rw [prefixMapKLR_mul, prefixMapKLR_mul, endMapKLR_mul, endMapKLR_mul]
  set P₁ := prefixMapKLR Q Λ Λc ν ν₀ (pol p₁) with hP₁
  set Pα := prefixMapKLR Q Λ Λc ν ν₀ (ψw α) with hPα
  set Ps := prefixMapKLR Q Λ Λc ν ν₀ (e s) with hPs
  set E₂ := endMapKLR Q Λ Λc ν ν₀ (pol p₂) with hE₂
  set Eβ := endMapKLR Q Λ Λc ν ν₀ (ψw β) with hEβ
  set Et := endMapKLR Q Λ Λc ν ν₀ (e t) with hEt
  have h1 : P₁ * Pα * Ps * (E₂ * Eβ * Et) = P₁ * E₂ * (Pα * Eβ) * (Ps * Et) := by
    have hsE₂ : Ps * E₂ = E₂ * Ps := (hc _ _).eq
    have hsEβ : Ps * Eβ = Eβ * Ps := (hc _ _).eq
    have hαE₂ : Pα * E₂ = E₂ * Pα := (hc _ _).eq
    calc P₁ * Pα * Ps * (E₂ * Eβ * Et) = P₁ * Pα * (Ps * E₂) * Eβ * Et := by noncomm_ring
      _ = P₁ * (Pα * E₂) * (Ps * Eβ) * Et := by rw [hsE₂]; noncomm_ring
      _ = _ := by rw [hαE₂, hsEβ]; noncomm_ring
  rw [h1, hPs, hEt, prefixMapKLR_e_mul_endMapKLR_e, hP₁, hE₂, hPα, hEβ, prefixMapKLR_pol,
    endMapKLR_pol, prefixMapKLR_ψw hα, endMapKLR_ψw hβ]
  have hE : IsIdempotentElem (Eₑ : Rp) := eSum_idem _
  have hEi : (Eₑ * e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl
      (Seq.map (cupColour ℓ le_rfl) t)) : Rp) =
      e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl (Seq.map (cupColour ℓ le_rfl) t)) := by
    rw [eSum_mul_e, ite_eq_left (insertSeq_mem_endSet s _)]
  rw [map_mul, ψw_append]
  set E := (Eₑ : Rp)
  set x := (e (insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl (Seq.map (cupColour ℓ le_rfl) t)) : Rp)
  set q₁ := (pol (rename (posL ν₀) p₁) : Rp)
  set q₂ := (pol (rename (posR ν) p₂) : Rp)
  set a := (ψw α : Rp)
  set b := (ψw (shiftWord m β) : Rp)
  have h2 : E * q₂ = q₂ * E := (pol_mul_eSum _ _).symm
  have ha : E * a = a * E := eSum_end_mul_ψw_prefix hα
  have hb : E * b = b * E := eSum_end_mul_ψw_end hβ
  calc q₁ * E * (q₂ * E) * (a * E * (b * E)) * x
      = q₁ * ((E * q₂) * E) * (a * (E * b) * E) * x := by noncomm_ring
    _ = q₁ * q₂ * ((E * E) * a) * b * ((E * E) * x) := by rw [h2, hb]; noncomm_ring
    _ = q₁ * q₂ * a * (E * b) * x := by rw [hE.eq, ha, hEi]; noncomm_ring
    _ = q₁ * q₂ * a * b * (E * x) := by rw [hb]; noncomm_ring
    _ = q₁ * q₂ * (a * b) * x := by rw [hEi]; noncomm_ring

end Factor

end Categorification.Stendhal.CupCap
