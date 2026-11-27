/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowDescent
import Categorification.WeightedKLR.Rigidity.CupCapEndIndex

/-!
# Loadings and diagrams split along the two blocks with the maximum at the left end

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, the block decomposition (B3) with the black
block at the right end, steps 2 and 3 of the paper argument. The loading `frontSeq s t` of `λ⁺`
puts a loading `t` of the strands at the maximum on the first `N` strands and a loading `s` of
`λ` on the last `m`. Permutations of the two blocks act on the two parts
(`blockPerm_smul_frontSeq`), and `frontSeq s t` is red-ordered exactly when `s` and `t` are
(`isRedOrdered_frontSeq`). A diagram at the maximum on the first `N` strands and a diagram of `λ`
on the last `m` strands, both with dots on top, multiply to a diagram of `λ⁺` with dots on top
whose word is the concatenation of the two words, the second shifted by `N`
(`frontMapKLR_mul_suffixMapKLR`), with no correction terms.

This is the mirror of `CupCap.endSeq` and `CupCap.prefixMapKLR_mul_endMapKLR`.

## Main definitions

* `CupCap.frontSeq`: the loading with the maximum at the left end.
* `CupCap.frontPos`, `CupCap.suffixPos`: the positions of the two blocks.

## Main results

* `CupCap.blockPerm_smul_frontSeq`, `CupCap.isRedOrdered_frontSeq`.
* `CupCap.frontMapKLR_mul_suffixMapKLR`: the factorization.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

section Words

variable {I : Type*} {ℓ : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "z₀" => Nat.zero_le ℓ
local notation "zm" => Nat.zero_le (Multiset.card (stendhalWeight ℓ ν))

theorem N_add_m_front : N + m = M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- The loading of `λ⁺` with the loading `t` of the strands at the maximum on the first `N`
strands and the loading `s` of `λ` on the last `m`. -/
def frontSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  insertSeq (j := 0) (hj := z₀) s 0 zm (Seq.map (cupColour 0 z₀) t)

theorem frontSeq_lbl_lt (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : c.val < N) : (frontSeq s t).lbl c = cupColour 0 z₀ (t.lbl ⟨c.val, hc⟩) := by
  have hb : c.val <
      Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) 0 z₀)) := by
    rw [Multiset.card_map]; exact hc
  rw [frontSeq, insertSeq_lbl_win s zm _ ⟨c.val, hb⟩ (by simp), Seq.map_lbl]
  rfl

theorem frontSeq_lbl_ge (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) (c : Fin M)
    (hc : N ≤ c.val) :
    (frontSeq s t).lbl c = oldColour 0 z₀ (s.lbl ⟨c.val - N, by
      have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩) :=
  insertSeq_lbl_ge s zm _ _ (Nat.zero_le _) (by simp; omega)

theorem frontSeq_injective {s s' : Seq (stendhalWeight ℓ ν)} {t t' : Seq (stendhalWeight 2 ν₀)}
    (h : frontSeq s t = frontSeq s' t') : s = s' ∧ t = t' := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  constructor
  · apply Subtype.ext; funext a
    have h1 := frontSeq_lbl_ge s t ⟨N + a.val, by omega⟩ (by simp)
    have h2 := frontSeq_lbl_ge s' t' ⟨N + a.val, by omega⟩ (by simp)
    rw [h, h2] at h1
    have := (oldColour_injective 0 z₀ h1).symm
    simpa using this
  · apply Subtype.ext; funext b
    have h1 := frontSeq_lbl_lt s t ⟨b.val, by omega⟩ b.2
    have h2 := frontSeq_lbl_lt s' t' ⟨b.val, by omega⟩ b.2
    rw [h, h2] at h1
    exact (cupColour_injective (I := I) 0 z₀ h1).symm

theorem frontSeq_mem_frontSet [DecidableEq I] (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) : frontSeq s t ∈ frontSet ν ν₀ :=
  insertSeq_mem_frontSet s _

theorem exists_frontSeq_of_mem [DecidableEq I] {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    (hu : u ∈ frontSet ν ν₀) : ∃ s t, frontSeq s t = u := by
  obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
  refine ⟨s, (Seq.mapEquiv (cupColour_injective 0 z₀) _).symm t, ?_⟩
  rw [frontSeq, Seq.map_mapEquiv_symm]

/-- Adjacent transpositions of the strands at the maximum act on the sequences of the mapped
colours as on the sequences. -/
theorem sadj_smul_map_front (t : Seq (stendhalWeight 2 ν₀)) (q : ℕ) :
    sadj (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) 0 z₀))) q •
        Seq.map (cupColour 0 z₀) t = Seq.map (cupColour 0 z₀) (sadj N q • t) := by
  apply Subtype.ext
  funext c
  change (Seq.map _ t).1 ((sadj _ q).symm c) = cupColour 0 z₀ ((sadj N q • t).1 (Fin.cast _ c))
  rw [Seq.smul_apply, ← Perm.inv_def, ← Perm.inv_def, sadj_inv, sadj_inv]
  change cupColour 0 z₀ (t.1 (Fin.cast _ (sadj _ q c))) = _
  rw [cast_sadj]

theorem smul_frontSeq_left (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    {β : List ℕ} (hβ : ValidWord N β) :
    wordProd M β • frontSeq s t = frontSeq s (wordProd N β • t) := by
  induction β with
  | nil => simp
  | cons q β ih =>
    obtain ⟨hq, hβ⟩ := validWord_cons.1 hβ
    have h := smul_insertSeq_new (j := 0) (hj := z₀) s zm (Seq.map (cupColour 0 z₀)
      (wordProd N β • t)) (q := q) (by rw [Multiset.card_map]; exact hq)
    rw [zero_add] at h
    rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih hβ, frontSeq, frontSeq, h,
      sadj_smul_map_front]

theorem smul_frontSeq_right (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    {α : List ℕ} (hα : ValidWord m α) :
    wordProd M (shiftWord N α) • frontSeq s t = frontSeq (wordProd m α • s) t := by
  induction α with
  | nil => simp [shiftWord]
  | cons p α ih =>
    obtain ⟨hp, hα⟩ := validWord_cons.1 hα
    have ih' := ih hα
    have hc : crossPos 0 (Multiset.card ((stendhalWeight 2 ν₀).map
        (cupColour (I := I) 0 z₀))) p = N + p := by
      rw [crossPos, ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_zero p)),
        Multiset.card_map]; omega
    have h := smul_insertSeq_old (j := 0) (hj := z₀) (wordProd m α • s) zm
      (Seq.map (cupColour 0 z₀) t) (Or.inr (Nat.zero_le p))
    rw [hc] at h
    simp only [shiftWord, List.map_cons] at ih' ⊢
    rw [wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih']
    exact h

/-- **Permutations of the two blocks act on the two parts.** -/
theorem blockPerm_smul_frontSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀))
    (b : Perm (Fin N)) (a : Perm (Fin m)) :
    blockPerm (N_add_m_front (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)) b a • frontSeq s t =
      frontSeq (a • s) (b • t) := by
  obtain ⟨α, hα, rfl⟩ := exists_validWord m a
  obtain ⟨β, hβ, rfl⟩ := exists_validWord N b
  rw [← wordProd_append_shiftWord _ hβ hα, wordProd_append, mul_smul,
    smul_frontSeq_right _ _ hα, smul_frontSeq_left _ _ hβ]

private theorem inr_of_map_eq_inr' {ℓ₁ : ℕ} {f : Fin ℓ₁ → Fin (ℓ + 2)} {x : I ⊕ Fin ℓ₁}
    {r : Fin (ℓ + 2)} (h : Sum.map id f x = .inr r) : ∃ r₀, x = .inr r₀ ∧ f r₀ = r := by
  rcases x with x | x
  · simp at h
  · exact ⟨x, rfl, by simpa using h⟩

theorem oldRed_val_front (r : Fin ℓ) : (oldRed 0 z₀ r).val = r.val + 2 :=
  oldRed_val_of_ge (j := 0) (hj := z₀) (Nat.zero_le _)

theorem cupRed_val_front (r : Fin 2) : (cupRed (ℓ := ℓ) 0 z₀ r).val = r.val := by
  rw [cupRed_val, zero_add]

/-- **`frontSeq s t` is red-ordered exactly when `s` and `t` are.** -/
theorem isRedOrdered_frontSeq (s : Seq (stendhalWeight ℓ ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    IsRedOrdered (frontSeq s t) ↔ IsRedOrdered s ∧ IsRedOrdered t := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  constructor
  · intro h
    refine ⟨fun a b r r' hab ha hb => ?_, fun a b r r' hab ha hb => ?_⟩
    · have h1 := frontSeq_lbl_ge s t ⟨N + a.val, by omega⟩ (by simp)
      have h2 := frontSeq_lbl_ge s t ⟨N + b.val, by omega⟩ (by simp)
      simp only [Nat.add_sub_cancel_left, Fin.eta, ha, hb] at h1 h2
      have := h _ _ _ _ (show (⟨N + a.val, by omega⟩ : Fin M) < ⟨N + b.val, by
        omega⟩ by rw [Fin.lt_def]; simp; exact hab) h1 h2
      rw [Fin.lt_def, oldRed_val_front, oldRed_val_front] at this
      exact Fin.lt_def.2 (by omega)
    · have h1 := frontSeq_lbl_lt s t ⟨a.val, by omega⟩ a.2
      have h2 := frontSeq_lbl_lt s t ⟨b.val, by omega⟩ b.2
      rw [Fin.eta, ha] at h1
      rw [Fin.eta, hb] at h2
      have := h _ _ _ _ (show (⟨a.val, by omega⟩ : Fin M) < ⟨b.val, by omega⟩ from hab) h1 h2
      rw [Fin.lt_def, cupRed_val_front, cupRed_val_front] at this
      exact this
  · rintro ⟨hs, ht⟩ a b r r' hab ha hb
    rw [Fin.lt_def] at hab
    by_cases hb' : b.val < N
    · rw [frontSeq_lbl_lt s t b hb'] at hb
      rw [frontSeq_lbl_lt s t a (by omega)] at ha
      obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr' ha
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_map_eq_inr' hb
      have := ht _ _ _ _ (show (⟨a.val, by omega⟩ : Fin N) < ⟨b.val, hb'⟩ from hab) hr₀ hr₀'
      rw [Fin.lt_def, cupRed_val_front, cupRed_val_front]
      exact this
    · rw [frontSeq_lbl_ge s t b (by omega)] at hb
      obtain ⟨r₀', hr₀', rfl⟩ := inr_of_map_eq_inr' hb
      by_cases ha' : a.val < N
      · rw [frontSeq_lbl_lt s t a ha'] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr' ha
        rw [Fin.lt_def, cupRed_val_front, oldRed_val_front]
        omega
      · rw [frontSeq_lbl_ge s t a (by omega)] at ha
        obtain ⟨r₀, hr₀, rfl⟩ := inr_of_map_eq_inr' ha
        have := hs _ _ _ _ (show (⟨a.val - N, by omega⟩ : Fin m) < ⟨b.val - N, by omega⟩ by
          rw [Fin.lt_def]; simp; omega) hr₀ hr₀'
        rw [Fin.lt_def, oldRed_val_front, oldRed_val_front]
        rw [Fin.lt_def] at this
        omega

end Words

section Factor

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "z₀" => Nat.zero_le ℓ
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eₑ" =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (frontSet ν ν₀)

variable (ν) in
/-- The positions of the strands at the maximum in `λ⁺`, at the left end. -/
def frontPos (b : Fin N) : Fin M :=
  ⟨b.val, by have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩

variable (ν₀) in
/-- The positions of the strands of `λ` in `λ⁺`, after the strands at the maximum. -/
def suffixPos (a : Fin m) : Fin M :=
  ⟨N + a.val, by have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩

omit [DecidableEq I] in
@[simp] theorem frontPos_val (b : Fin N) : (frontPos (ℓ := ℓ) ν b).val = b.val := rfl

omit [DecidableEq I] in
@[simp] theorem suffixPos_val (a : Fin m) : (suffixPos ν₀ a).val = N + a.val := rfl

theorem frontMapKLR_pol (p : MvPolynomial (Fin N) k) :
    frontMapKLR Q Λ Λc ν ν₀ (pol p) = pol (rename (frontPos ν) p) * Eₑ := by
  rw [frontMapKLR, relabelHom_pol, BlockEmb.hom_pol, val_polCorner, rename_rename]
  congr 3
  congr 1
  funext b
  exact Fin.ext (by simp [frontWindow, BlockEmb.window, windowPos, frontPos])

theorem suffixMapKLR_pol (p : MvPolynomial (Fin m) k) :
    suffixMapKLR Q Λ Λc ν ν₀ (pol p) = pol (rename (suffixPos ν₀) p) * Eₑ := by
  rw [suffixMapKLR, relabelHom_pol, BlockEmb.hom_pol, val_polCorner, rename_rename]
  rfl

theorem frontMapKLR_ψw {β : List ℕ} (hβ : ValidWord N β) :
    frontMapKLR Q Λ Λc ν ν₀ (ψw β) = ψw β * Eₑ := by
  rw [frontMapKLR, relabelHom_ψw, BlockEmb.val_hom_ψw _ (by rwa [card_σ₀])]
  congr 2
  simp [frontWindow, BlockEmb.window]

theorem suffixMapKLR_ψw {α : List ℕ} (hα : ValidWord m α) :
    suffixMapKLR Q Λ Λc ν ν₀ (ψw α) = ψw (shiftWord N α) * Eₑ := by
  rw [suffixMapKLR, relabelHom_ψw, BlockEmb.val_hom_ψw _ (by rwa [card_μ₀])]
  rfl

theorem eSum_front_mul_ψw_front {β : List ℕ} (hβ : ValidWord N β) :
    (Eₑ * ψw β : Rp) = ψw β * Eₑ := by
  have h := (frontWindow ν ν₀).eSum_mul_ψw
    (Q := stendhalQ Q (plusLabels Λ Λc 0 z₀)) (k := k) (α := β) (by rwa [card_σ₀])
  simpa [frontWindow, BlockEmb.window] using h

theorem eSum_front_mul_ψw_suffix {α : List ℕ} (hα : ValidWord m α) :
    (Eₑ * ψw (shiftWord N α) : Rp) = ψw (shiftWord N α) * Eₑ :=
  (suffixWindow ν ν₀).eSum_mul_ψw
    (Q := stendhalQ Q (plusLabels Λ Λc 0 z₀)) (k := k) (α := α) (by rwa [card_μ₀])

theorem frontMapKLR_e_mul_suffixMapKLR_e (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (e t) * suffixMapKLR Q Λ Λc ν ν₀ (e s) = e (frontSeq s t) := by
  rw [← (commute_suffixMapKLR_frontMapKLR Q Λ Λc ν ν₀ _ _).eq, ← insertMap_eq_suffix_mul_front,
    insertMap_e]
  rfl

/-- **Diagrams of the two blocks multiply to a diagram of `λ⁺`** (dots on top): the words are
concatenated, the second shifted by `N`, and the bottoms are concatenated. -/
theorem frontMapKLR_mul_suffixMapKLR (p₂ : MvPolynomial (Fin N) k) (p₁ : MvPolynomial (Fin m) k)
    {β α : List ℕ} (hβ : ValidWord N β) (hα : ValidWord m α)
    (t : Seq (stendhalWeight 2 ν₀)) (s : Seq (stendhalWeight ℓ ν)) :
    frontMapKLR Q Λ Λc ν ν₀ (pol p₂ * ψw β * e t) *
        suffixMapKLR Q Λ Λc ν ν₀ (pol p₁ * ψw α * e s) =
      pol (rename (frontPos ν) p₂ * rename (suffixPos ν₀) p₁) * ψw (β ++ shiftWord N α) *
        e (frontSeq s t) := by
  have hc : ∀ a x, frontMapKLR Q Λ Λc ν ν₀ x * suffixMapKLR Q Λ Λc ν ν₀ a =
      suffixMapKLR Q Λ Λc ν ν₀ a * frontMapKLR Q Λ Λc ν ν₀ x :=
    fun a x => (commute_suffixMapKLR_frontMapKLR Q Λ Λc ν ν₀ a x).eq.symm
  rw [frontMapKLR_mul, frontMapKLR_mul, suffixMapKLR_mul, suffixMapKLR_mul]
  set P₁ := frontMapKLR Q Λ Λc ν ν₀ (pol p₂) with hP₁
  set Pα := frontMapKLR Q Λ Λc ν ν₀ (ψw β) with hPα
  set Ps := frontMapKLR Q Λ Λc ν ν₀ (e t) with hPs
  set E₂ := suffixMapKLR Q Λ Λc ν ν₀ (pol p₁) with hE₂
  set Eβ := suffixMapKLR Q Λ Λc ν ν₀ (ψw α) with hEβ
  set Et := suffixMapKLR Q Λ Λc ν ν₀ (e s) with hEt
  have h1 : P₁ * Pα * Ps * (E₂ * Eβ * Et) = P₁ * E₂ * (Pα * Eβ) * (Ps * Et) := by
    have hsE₂ : Ps * E₂ = E₂ * Ps := hc _ _
    have hsEβ : Ps * Eβ = Eβ * Ps := hc _ _
    have hαE₂ : Pα * E₂ = E₂ * Pα := hc _ _
    calc P₁ * Pα * Ps * (E₂ * Eβ * Et) = P₁ * Pα * (Ps * E₂) * Eβ * Et := by noncomm_ring
      _ = P₁ * (Pα * E₂) * (Ps * Eβ) * Et := by rw [hsE₂]; noncomm_ring
      _ = _ := by rw [hαE₂, hsEβ]; noncomm_ring
  rw [h1, hPs, hEt, frontMapKLR_e_mul_suffixMapKLR_e, hP₁, hE₂, hPα, hEβ, frontMapKLR_pol,
    suffixMapKLR_pol, frontMapKLR_ψw hβ, suffixMapKLR_ψw hα]
  have hE : IsIdempotentElem (Eₑ : Rp) := eSum_idem _
  have hEi : (Eₑ * e (frontSeq s t) : Rp) = e (frontSeq s t) := by
    rw [eSum_mul_e, ite_eq_left_of_eq_true _ _ (eq_true (frontSeq_mem_frontSet s t))]
  rw [map_mul, ψw_append]
  set E := (Eₑ : Rp)
  set x := (e (frontSeq s t) : Rp)
  set q₁ := (pol (rename (frontPos ν) p₂) : Rp)
  set q₂ := (pol (rename (suffixPos ν₀) p₁) : Rp)
  set a := (ψw β : Rp)
  set b := (ψw (shiftWord N α) : Rp)
  have h2 : E * q₂ = q₂ * E := (pol_mul_eSum _ _).symm
  have ha : E * a = a * E := eSum_front_mul_ψw_front hβ
  have hb : E * b = b * E := eSum_front_mul_ψw_suffix hα
  calc q₁ * E * (q₂ * E) * (a * E * (b * E)) * x
      = q₁ * ((E * q₂) * E) * (a * (E * b) * E) * x := by noncomm_ring
    _ = q₁ * q₂ * ((E * E) * a) * b * ((E * E) * x) := by rw [h2, hb]; noncomm_ring
    _ = q₁ * q₂ * a * (E * b) * x := by rw [hE.eq, ha, hEi]; noncomm_ring
    _ = q₁ * q₂ * a * b * (E * x) := by rw [hb]; noncomm_ring
    _ = q₁ * q₂ * (a * b) * x := by rw [hEi]; noncomm_ring

end Factor

end Categorification.Stendhal.CupCap
