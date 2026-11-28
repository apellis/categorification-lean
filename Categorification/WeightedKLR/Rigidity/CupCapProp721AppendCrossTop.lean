/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotTop
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossMid

/-!
# The crossing of the two appended strands passing under the window

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` with the crossing, for a cap at the
right end (`j = ℓ`). There `ι₂ ∘ ι₁` passes the two appended strands under the window, one after
the other. Both have colour `i`, so the crossing of the two strands slides through the two
passages exactly: each braid move is between the two passing strands and one window strand, and
the KLR braid relation has no error term when the two strands on one side of the middle strand
have the same colour (`CupCap.ψ_mul_underRight_two`). Hence the crossing of the last two strands
of `λ` acts on the image of `ι₂ ∘ ι₁` as the crossing `Y` of the last two strands of `λ⁺`
(`CupCap.midCross_mul_topPass_two`, `CupCap.appendTopIota_two_appendedCross`).

## Main results

* `CupCap.ψ_mul_underRight_two`: `ψ_q · ψ_{q+1} ⋯ ψ_{q+n} · ψ_q ⋯ ψ_{q+n-1} =
  ψ_{q+1} ⋯ ψ_{q+n} · ψ_q ⋯ ψ_{q+n-1} · ψ_{q+n}` on a loading with equal labels at `q + n` and
  `q + n + 1`.
* `CupCap.midCross_mul_topPass_two`, `CupCap.appendTopIota_two_appendedCross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-- **Two strands of equal colour passing a block of `n` strands**: the crossing of the two
strands at the top equals the crossing at the bottom. Every braid move is between the two passing
strands and one strand of the block, with the two passing strands on the same side, so the braid
relation holds exactly. -/
theorem ψ_mul_underRight_two {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} {q n : ℕ}
    (h : q + n + 1 < Multiset.card μ) (t : Seq μ)
    (ht : t.1 ⟨q + n, by omega⟩ = t.1 ⟨q + n + 1, h⟩) :
    (KLRAlgebra.ψ q * KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψw (List.range' q n) *
        KLRAlgebra.e t : KLRAlgebra k Q' μ) =
      KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψw (List.range' q n) *
        KLRAlgebra.ψ (q + n) * KLRAlgebra.e t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hl : ∀ a b : Fin (Multiset.card μ), a.val = b.val → t.1 a = t.1 b :=
      fun a b hab => congrArg t.1 (Fin.ext hab)
    rw [← List.range'_append_1, ← List.range'_append_1, List.range'_one, List.range'_one,
      KLRAlgebra.ψw_append, KLRAlgebra.ψw_append, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_cons,
      KLRAlgebra.ψw_nil, mul_one, mul_one]
    have hc : Commute (KLRAlgebra.ψ (q + 1 + n) : KLRAlgebra k Q' μ)
        (KLRAlgebra.ψw (List.range' q n)) :=
      KLRAlgebra.commute_ψ_ψw fun p hp => by rw [List.mem_range'_1] at hp; omega
    set t'' := sadj (Multiset.card μ) (q + 1 + n) • sadj (Multiset.card μ) (q + n) • t
      with ht''
    have hX : (KLRAlgebra.ψ (q + 1 + n) * KLRAlgebra.ψ (q + n) * KLRAlgebra.e t :
        KLRAlgebra k Q' μ) =
        KLRAlgebra.e t'' * (KLRAlgebra.ψ (q + 1 + n) * KLRAlgebra.ψ (q + n)) := by
      rw [mul_assoc, KLRAlgebra.ψ_mul_e, ← mul_assoc, KLRAlgebra.ψ_mul_e, mul_assoc]
    have h1 : t''.1 ⟨q + n, by omega⟩ = t''.1 ⟨q + n + 1, by omega⟩ := by
      rw [ht'', Seq.smul_apply, Seq.smul_apply, Seq.smul_apply, Seq.smul_apply,
        ← Equiv.Perm.inv_def, ← Equiv.Perm.inv_def, sadj_inv, sadj_inv,
        sadj_apply_of_ne (k := q + 1 + n) _ (by dsimp only; omega) (by dsimp only; omega),
        sadj_apply_left (k := q + n) (by omega),
        show (⟨q + n + 1, by omega⟩ : Fin (Multiset.card μ)) = ⟨q + 1 + n, by omega⟩ from
          Fin.ext (by dsimp only; omega),
        sadj_apply_left (k := q + 1 + n) (by omega),
        sadj_apply_of_ne (k := q + n) _ (by dsimp only; omega) (by dsimp only; omega)]
      exact (hl _ _ (by dsimp only; omega)).trans (ht.trans (hl _ _ (by dsimp only; omega)))
    have hbr : ((KLRAlgebra.ψ (q + n) * KLRAlgebra.ψ (q + n + 1) * KLRAlgebra.ψ (q + n) -
        KLRAlgebra.ψ (q + n + 1) * KLRAlgebra.ψ (q + n) * KLRAlgebra.ψ (q + n + 1)) *
          KLRAlgebra.e t : KLRAlgebra k Q' μ) = 0 := by
      rw [KLRAlgebra.braid (q + n) (by omega)]
      split_ifs with hcond
      · exfalso
        refine hcond.2 (hcond.1.trans ?_)
        exact ((hl _ _ (by dsimp only; omega)).trans
          (ht.trans (hl _ _ (by dsimp only; omega)))).symm
      · rfl
    rw [sub_mul, sub_eq_zero] at hbr
    have e1 : q + 1 + n = q + n + 1 := by omega
    rw [show q + (n + 1) = q + n + 1 by omega]
    calc (KLRAlgebra.ψ q * (KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψ (q + 1 + n)) *
          (KLRAlgebra.ψw (List.range' q n) * KLRAlgebra.ψ (q + n)) * KLRAlgebra.e t :
          KLRAlgebra k Q' μ)
        = KLRAlgebra.ψ q * KLRAlgebra.ψw (List.range' (q + 1) n) *
            KLRAlgebra.ψw (List.range' q n) *
            (KLRAlgebra.ψ (q + 1 + n) * KLRAlgebra.ψ (q + n) * KLRAlgebra.e t) := by
          simp only [mul_assoc]
          rw [← mul_assoc (KLRAlgebra.ψ (q + 1 + n)) (KLRAlgebra.ψw (List.range' q n)), hc.eq,
            mul_assoc]
      _ = KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψw (List.range' q n) *
            KLRAlgebra.ψ (q + n) *
            (KLRAlgebra.ψ (q + 1 + n) * KLRAlgebra.ψ (q + n) * KLRAlgebra.e t) := by
          rw [hX, ← mul_assoc, ih (by omega) t'' h1, mul_assoc _ (KLRAlgebra.e t'')]
      _ = _ := by
          rw [e1]
          simp only [← mul_assoc] at hbr ⊢
          rw [mul_assoc _ (KLRAlgebra.ψ (q + n)) (KLRAlgebra.ψ (q + n + 1)),
            mul_assoc _ (KLRAlgebra.ψ (q + n) * KLRAlgebra.ψ (q + n + 1)) (KLRAlgebra.ψ (q + n)),
            mul_assoc _ (KLRAlgebra.ψ (q + n) * KLRAlgebra.ψ (q + n + 1) * KLRAlgebra.ψ (q + n)),
            hbr]
          have hc' : Commute (KLRAlgebra.ψ (q + n + 1) : KLRAlgebra k Q' μ)
              (KLRAlgebra.ψw (List.range' q n)) := e1 ▸ hc
          simp only [mul_assoc]
          rw [← mul_assoc (KLRAlgebra.ψw (List.range' q n)) (KLRAlgebra.ψ (q + n + 1)), ← hc'.eq]
          simp only [mul_assoc]

end Generic

section Ring

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "mᵢ" => Multiset.card (stendhalWeight ℓ ((Singleton.singleton i : Multiset I) + ν))
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "Rpᵢᵢ" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (νᵢᵢ + ν₀))
local notation "Eᵢᵢ" u:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u n hn) : Rpᵢᵢ)
local notation "sᵢᵢ" s:max => appendBlackLoading i νᵢ (appendBlackLoading i ν s)
local notation "D₁" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "D₂" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νᵢ i
local notation "eA₂" =>
  topPassIdem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νᵢ i
local notation "Ap₂" => appendPlus Q Λ Λc j hj νᵢ ν₀ i

omit [DecidableEq I] in
theorem card_appendBlackWeight_two : Multiset.card (stendhalWeight ℓ νᵢᵢ) = m + 2 := by
  rw [card_appendBlackWeight, card_appendBlackWeight]

omit [DecidableEq I] in
theorem le_card_appendBlackWeight_two : m ≤ Multiset.card (stendhalWeight ℓ νᵢᵢ) := by
  have := card_appendBlackWeight_two (ℓ := ℓ) ν i; omega

omit [DecidableEq I] in
theorem succ_le_card_appendBlackWeight_two :
    m + 1 ≤ Multiset.card (stendhalWeight ℓ νᵢᵢ) := by
  have := card_appendBlackWeight_two (ℓ := ℓ) ν i; omega

/-- The window idempotents of the second passage fix the doubly appended loadings with the
window at `m + 1`. -/
theorem topPassIdem_two_mul_eSum (s : Seq (stendhalWeight ℓ ν)) :
    eA₂ * Eᵢᵢ (sᵢᵢ s) (m + 1) (succ_le_card_appendBlackWeight_two ν i) =
      Eᵢᵢ (sᵢᵢ s) (m + 1) (succ_le_card_appendBlackWeight_two ν i) := by
  have hE : Eᵢᵢ (sᵢᵢ s) (m + 1) (succ_le_card_appendBlackWeight_two ν i) =
      Eᵢᵢ (sᵢᵢ s) mᵢ (le_card_appendBlackWeight νᵢ i) :=
    congrArg _ (insertSet_congr' _ _ _ (card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)).symm)
  rw [hE]
  exact topPassIdem_mul_eSum νᵢ i (appendBlackLoading i ν s)

/-- **The two passages**: `D₂ · appendPlus(D₁)` passes the two appended strands under the window,
`ψ_{m+1} ⋯ ψ_{m+N} · ψ_m ⋯ ψ_{m+N-1}` on the doubly appended loadings with the window at `m`. -/
theorem topPass_mul_appendPlus_topPass :
    D₂ * Ap₂ D₁ = ∑ s : Seq (stendhalWeight ℓ ν),
      underRight N (m + 1) * underRight N m *
        Eᵢᵢ (sᵢᵢ s) m (le_card_appendBlackWeight_two ν i) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢ) (ν₀ := ν₀)
  have hU : (underRight N mᵢ : Rpᵢᵢ) = underRight N (m + 1) :=
    congrArg (fun q => (underRight N q : Rpᵢᵢ)) hm
  rw [topPass, topPass, hU, show (underRight N m : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
      (stendhalWeight (ℓ + 2) (νᵢ + ν₀))) = KLRAlgebra.ψw (List.range' m N) from rfl,
    appendPlus_ψw_mul νᵢ i _ (fun q hq => by rw [List.mem_range'_1] at hq; omega),
    topPassIdem.eq_1 (ν := ν), map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [appendPlus_eSum_insertSet νᵢ i (appendBlackLoading i ν s) (le_card_appendBlackWeight ν i)
    (le_card_appendBlackWeight_two ν i)]
  have hc := underRight_mul_eSum Q Λ Λc (j := j) (hj := hj) (ν₀ := ν₀) (sᵢᵢ s) (q := m)
    (succ_le_card_appendBlackWeight_two ν i)
  change _ * (underRight N m * _) = _
  rw [hc, mul_assoc, ← mul_assoc eA₂, topPassIdem_two_mul_eSum, ← hc, ← mul_assoc]

/-- **The crossing of the two appended strands slides through both passages**, on a doubly
appended loading. -/
theorem ψ_mul_underRight_two_eSum (s : Seq (stendhalWeight ℓ ν)) :
    KLRAlgebra.ψ m * (underRight N (m + 1) * underRight N m *
        Eᵢᵢ (sᵢᵢ s) m (le_card_appendBlackWeight_two ν i)) =
      underRight N (m + 1) * underRight N m *
        Eᵢᵢ (sᵢᵢ s) m (le_card_appendBlackWeight_two ν i) * KLRAlgebra.ψ (m + N) := by
  have h2 := card_appendBlackWeight_two (ℓ := ℓ) ν i
  have h1 := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢᵢ) (ν₀ := ν₀)
  rw [eSum_insertSet, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  set t := sᵢᵢ s with ht
  set t' := insertSeq t m (le_card_appendBlackWeight_two ν i) (Seq.map (cupColour j hj) w)
  have ha : t.lbl ⟨m, by omega⟩ = .inl i := by
    rw [ht, appendBlackLoading_lbl_of_lt i νᵢ _ _ (by dsimp only; omega)]
    exact appendBlackLoading_lbl_of_eq i ν _ _ rfl
  have hb : t.lbl ⟨m + 1, by omega⟩ = .inl i := by
    rw [ht]
    exact appendBlackLoading_lbl_of_eq i νᵢ _ _ (by dsimp only; omega)
  have l1 : t'.lbl ⟨m + N, by omega⟩ = oldColour j hj (t.lbl ⟨m, by omega⟩) :=
    insertSeq_lbl_ge t _ _ ⟨m, by omega⟩ le_rfl rfl
  have l2 : t'.lbl ⟨m + N + 1, by omega⟩ = oldColour j hj (t.lbl ⟨m + 1, by omega⟩) :=
    insertSeq_lbl_ge t _ _ ⟨m + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)
  have hl : t'.1 ⟨m + N, by omega⟩ = t'.1 ⟨m + N + 1, by omega⟩ := by
    change t'.lbl _ = t'.lbl _
    rw [l1, l2, ha, hb]
  have key := ψ_mul_underRight_two (Q' := stendhalQ Q (plusLabels Λ Λc j hj)) (q := m) (n := N)
    (by omega) t' hl
  have hfix : sadj (Multiset.card (stendhalWeight (ℓ + 2) (νᵢᵢ + ν₀))) (m + N) • t' = t' :=
    sadj_smul_eq_self_of_lbl (by omega) hl
  have hψe : (KLRAlgebra.ψ (m + N) * KLRAlgebra.e t' : Rpᵢᵢ) = KLRAlgebra.e t' *
      KLRAlgebra.ψ (m + N) := by
    rw [KLRAlgebra.ψ_mul_e, hfix]
  rw [show (underRight N (m + 1) : Rpᵢᵢ) = KLRAlgebra.ψw (List.range' (m + 1) N) from rfl,
    show (underRight N m : Rpᵢᵢ) = KLRAlgebra.ψw (List.range' m N) from rfl, ← mul_assoc,
    ← mul_assoc, key, mul_assoc _ (KLRAlgebra.ψ (m + N)), hψe, ← mul_assoc]

/-- **The crossing of the last two strands of `λ` on the image of the two passages**, for
`j = ℓ`: it equals the crossing of the last two strands of `λ⁺` below the passages. -/
theorem midCross_mul_topPass_two (h : ¬ j < ℓ) :
    midCross j hj Q Λ Λc νᵢᵢ ν₀ m * (D₂ * Ap₂ D₁) =
      D₂ * Ap₂ D₁ * KLRAlgebra.ψ (Multiset.card ρ) := by
  have h2 := card_appendBlackWeight_two (ℓ := ℓ) ν i
  rw [midCross_eq_of_not_lt h (by omega), mul_assoc, ← mul_assoc _ D₂,
    sum_midIdem_mul_topPass νᵢ i h, topPass_mul_appendPlus_topPass, Finset.mul_sum,
    Finset.sum_mul, card_plus']
  exact Finset.sum_congr rfl fun s _ => ψ_mul_underRight_two_eSum ν i s

end Ring

section Model

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "aB₁" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "aB₂" => appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i
local notation "Y" => lastCrossPlus k Q Λ Λc j hj ν ν₀ i
local notation "D₁" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "D₂" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νᵢ i

/-- **Appending two strands carries the crossing of the new strands to the crossing**, for
`j = ℓ` (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): on the image of `ι₂ ∘ ι₁`, the
left action of minus the crossing of the two appended strands of `T̃^λ` times their unit is the
right action of minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` times their
unit. Route hypotheses (tracked): `hκ`, `hP`, `hPL`. -/
theorem appendTopIota_two_appendedCross (h : ¬ j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (hR'' : MidKLRRel j hj Q Λ Λc νᵢᵢ ν₀ L hL)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hR'' (orderProjection Q Λ νᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ i ν) *
        appendBlackStendhal Q Λ i νᵢ (appendBlackStendhal Q Λ i ν 1))
        (appendTopIota νᵢ i hP hPL hL hκ h (appendTopIota ν i hP hPL hL hκ h y)) =
      op (-(Y * aB₂ (aB₁ 1))) •
        appendTopIota νᵢ i hP hPL hL hκ h (appendTopIota ν i hP hPL hL hκ h y) := by
  rw [map_mul, Module.End.mul_apply, ← appendTopIota_midLeftAlg νᵢ i hP hPL hL hκ h hR' hR'',
    ← appendTopIota_midLeftAlg ν i hP hPL hL hκ h hR hR' 1, map_one, Module.End.one_apply]
  have hY : orderProjection Q Λ νᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ i ν) =
      topMap k Q Λ νᵢᵢ (-(KLRAlgebra.ψ (Multiset.card (stendhalWeight ℓ ν)))) := by
    rw [map_neg, map_neg]; rfl
  rw [hY, map_neg, map_neg, midLeftAlg_topMap, LinearMap.neg_apply, midKLRAct_ψ, op_neg, neg_smul,
    neg_inj]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : ∀ μ : Multiset I, appendTopIota (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
        (ν₀ := ν₀) μ i hP hPL hL hκ h 0 = 0 := fun μ => by
      rw [appendTopIota, Ind.tmul_zero, map_zero]; rfl
    rw [h0, h0, map_zero, smul_zero]
  | add a b ha hb => rw [appendTopIota_add, appendTopIota_add, map_add, ha, hb, smul_add]
  | tmul w v =>
    rw [appendTopIota_tmul, appendTopIota_tmul, midEnd]
    change natMapOn _ (Ind.tmul _ v) = op (Y * aB₂ (aB₁ 1)) • Ind.tmul _ v
    rw [natMapOn_tmul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    have hA : ∀ (μ : Multiset I) x, (appendBlackPlusOp Q Λ Λc j hj μ ν₀ i x).unop =
        appendBlackPlus Q Λ Λc j hj μ ν₀ i x.unop := fun _ _ => rfl
    have hsm : ∀ c : Corner (midOp j hj Q Λ Λc νᵢᵢ ν₀),
        ((op (Y * aB₂ (aB₁ 1)) • c : Corner (midOp j hj Q Λ Λc νᵢᵢ ν₀)) : _) =
          op (Y * aB₂ (aB₁ 1)) * c.1 := fun _ => rfl
    simp only [cornerMulOf_val, midElt, compMul, unitGen, unop_mul, unop_op, hA, unop_one, hsm]
    set w' := w.1.unop
    have hZ : aB₂ (botMap k Q Λ Λc j hj νᵢ ν₀ D₁ * (aB₁ w' * aB₁ 1)) * aB₂ 1 =
        botMap k Q Λ Λc j hj νᵢᵢ ν₀ (appendPlus Q Λ Λc j hj νᵢ ν₀ i D₁) * aB₂ (aB₁ w') := by
      rw [← map_mul aB₂ _ 1, mul_one, ← map_mul aB₁ w' 1, mul_one, map_mul,
        appendBlackPlus_botMap]
    rw [hZ, ← mul_assoc (botMap k Q Λ Λc j hj νᵢᵢ ν₀ D₂), ← map_mul]
    set P := D₂ * appendPlus Q Λ Λc j hj νᵢ ν₀ i D₁ with hPdef
    set Z := aB₂ (aB₁ w') with hZdef
    have hs : midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1 =
        botMap k Q Λ Λc j hj νᵢᵢ ν₀ (∑ u, midIdem j hj Q Λ Λc νᵢᵢ ν₀ u) :=
      midStendhal_one_eq_botMap _
    have f1 : midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1 * botMap k Q Λ Λc j hj νᵢᵢ ν₀ P =
        botMap k Q Λ Λc j hj νᵢᵢ ν₀ P := by
      rw [hs, ← map_mul, hPdef, ← mul_assoc, sum_midIdem_mul_topPass νᵢ i h]
    have f2 : botMap k Q Λ Λc j hj νᵢᵢ ν₀ (midCross j hj Q Λ Λc νᵢᵢ ν₀
        (Multiset.card (stendhalWeight ℓ ν))) * botMap k Q Λ Λc j hj νᵢᵢ ν₀ P =
        botMap k Q Λ Λc j hj νᵢᵢ ν₀ P * Y := by
      rw [← map_mul, hPdef, midCross_mul_topPass_two ν i h, map_mul]
      rfl
    have f3 : Y * Z = Z * Y := by
      rw [hZdef]; exact (commute_lastCrossPlus_appendBlackPlus_two ν i _).eq
    have f4 : Z * aB₂ (aB₁ 1) = Z := by
      rw [hZdef, ← map_mul, ← map_mul, mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1) (botMap k Q Λ Λc j hj νᵢᵢ ν₀ P), f1,
      ← mul_assoc (botMap k Q Λ Λc j hj νᵢᵢ ν₀ _) (botMap k Q Λ Λc j hj νᵢᵢ ν₀ P), f2,
      mul_assoc, ← mul_assoc (midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1), f1, ← mul_assoc Z Y, ← f3,
      mul_assoc, f4]

end Model

end Categorification.Stendhal.CupCap
