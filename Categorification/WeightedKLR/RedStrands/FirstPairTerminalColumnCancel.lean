/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairOneAfterSpectator
import Categorification.WeightedKLR.RedStrands.FirstPairAllBottom
import Categorification.WeightedKLR.RedStrands.FirstPairTwoAfterSpectator
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.KLR.EqualBlackReturnKernel
import Categorification.WeightedKLR.RedStrands.BraidedEqualBlackReturns

/-!
# Terminal spectator factors in a first-pair bottom column

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ

local notation "b" => firstPairBottomTwoInterior
local notation "lower" => firstPairOneAfterSpectator
local notation "upper" => fun side => sadj N 3 • lower side

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "U" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "φ" => ofKLR k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) φ
local notation "J" => violIdeal k Q Λ ν
local notation "ρ" => terminalWord («ν» := ν) (ℓ := 2)
local notation "last" => (⟨4, by decide⟩ : Fin N)
local notation "c" => fun side => (ψ 3 * e (upper side) : R)

private def TerminalLeftFactor (t : Seq μ) (crossing : R) : Prop :=
  ∀ u : Seq μ, u.lbl last = .inr 2 → ∀ x : R,
    ∃ z : R, (e t : R) * x * e u = crossing * z

private theorem firstPairTerminal_column_violated_factor
    (hQ : KLRSymm Q) (t : Seq μ) (crossing : R) (factor : TerminalLeftFactor Q Λ t crossing)
    (s : Seq μ) (hs : IsViolated s) (x y : R) :
    ∃ w : R, (e t : R) * y * e s * x * e b = crossing * w ∧ φ w ∈ J := by
  classical
  let B := basisOfSymm (k := k) («ν» := μ) (stendhalQ_symm Q Λ hQ) ρ
    (fun w => terminalWord_spec («ν» := ν) (ℓ := 2) w)
  induction B.mem_span x using Submodule.span_induction with
  | zero => exact ⟨0, by simp only [mul_zero,zero_mul], by rw [map_zero]; exact (J).zero_mem⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨z,hz,zJ⟩ := hx
    obtain ⟨z',hz',zJ'⟩ := hx'
    exact ⟨z+z', by simpa only [mul_add,add_mul] using congrArg₂ (·+·) hz hz',
      by rw [map_add]; exact (J).add_mem zJ zJ'⟩
  | smul a x _ hx =>
    obtain ⟨z,hz,zJ⟩ := hx
    refine ⟨a • z, by simpa only [mul_smul_comm,smul_mul_assoc] using congrArg (a • ·) hz, ?_⟩
    rw [Algebra.smul_def, map_mul]
    exact TwoSidedIdeal.mul_mem_left J _ _ zJ
  | mem x hx =>
    obtain ⟨⟨d,w,dots⟩,rfl⟩ := hx
    rw [basisOfSymm_apply]
    by_cases e₀ : d = b
    · subst d
      by_cases e₁ : w • b = s
      · let rest := terminalRest (ℓ := 2) («ν» := ν) w
        let pref := terminalPrefix (ℓ := 2) («ν» := ν) w
        let u := wordProd N rest • b
        let v : R := ψw rest * pol (monomial dots 1) * e b
        have target : wordProd N pref • u = s := by
          rw [← mul_smul, ← wordProd_append, show pref ++ rest = ρ w from rfl, terminalWord_prod, e₁]
        have target' : u = (cycA (m := N) (n := 4) (w last).val) • s := by
          have hp : wordProd N pref = (cycA (m := N) (n := 4) (w last).val)⁻¹ :=
            wordProd_reverse _ _
          rw [hp] at target
          rw [← target, smul_inv_smul]
        have uData : IsViolated u ∧ u.lbl last = .inr 2 := by
          rw [target', ← e₁]
          have finite : ∀ w : Perm (Fin N),
              ((w • b).lbl ⟨0,by decide⟩).isLeft →
              ((cycA (m := N) (n := 4) (w last).val • (w • b)).lbl ⟨0,by decide⟩).isLeft ∧
              (cycA (m := N) (n := 4) (w last).val • (w • b)).lbl last = .inr 2 := by decide +kernel
          have data := finite w (by rw [e₁]; exact hs.2)
          exact ⟨⟨by decide, data.1⟩, data.2⟩
        have cut : (e u : R) * v = v := by
          change (e (wordProd N rest • b) : R) * (ψw rest * pol (monomial dots 1) * e b) = _
          rw [e_mul_gen, inv_smul_smul, ite_eq_left rfl]
        have cv : v * e b = v := by simp only [v, mul_assoc, e_mul_self]
        have pc : (e s : R) * ψw pref * e u = ψw pref * e u := by
          rw [e_mul_ψw, ← target, inv_smul_smul, mul_assoc, e_mul_self]
        have col : (e s : R) * (ψw (ρ w) * pol (monomial dots 1) * e b) * e b =
            ψw pref * (e u * v) := by
          calc
            _ = ((e s : R) * ψw pref) * v * e b := by
              simp only [show ρ w = pref ++ rest from rfl, ψw_append, v, mul_assoc]
            _ = ((e s : R) * ψw pref * e u) * (v * e b) := by
              simp only [mul_assoc,cv,cut]
            _ = _ := by rw [pc,cv,mul_assoc]
        let x₀ := y * ψw pref
        obtain ⟨d,fact⟩ := factor u uData.2 x₀
        have pu : φ (e u) ∈ J := TwoSidedIdeal.subset_span ⟨u,uData.1,rfl⟩
        refine ⟨d * e u * v, ?_, ?_⟩
        · calc
            _ = (e t : R) * y * (e s * (ψw (ρ w) * pol (monomial dots 1) * e b) * e b) := by
              simp only [mul_assoc]
            _ = ((e t : R) * x₀ * e u) * v := by rw [col]; simp only [x₀,mul_assoc]
            _ = crossing * (d * e u * v) := by
              rw [fact]
              simp only [mul_assoc, cut]
        · simp only [map_mul]
          exact TwoSidedIdeal.mul_mem_right J _ _ (TwoSidedIdeal.mul_mem_left J _ _ pu)
      · refine ⟨0, ?_, by rw [map_zero]; exact (J).zero_mem⟩
        have cut : (e s : R) * (ψw (ρ w) * pol (monomial dots 1) * e b) = 0 := by
          have neq : w⁻¹ • s ≠ b := fun he => e₁ (by rw [← he, smul_inv_smul])
          rw [e_mul_gen, terminalWord_prod, ite_eq_right neq]
        rw [mul_assoc ((e t : R) * y) (e s), cut]
        simp only [mul_zero,zero_mul]
    · refine ⟨0, ?_, by rw [map_zero]; exact (J).zero_mem⟩
      simp only [mul_assoc, e_mul_e, ite_eq_right e₀, mul_zero]

private theorem firstPairTerminal_lift_violating_relation (hQ : KLRSymm Q)
    (t : Seq μ) (crossing : R) (factor : TerminalLeftFactor Q Λ t crossing)
    (z : U) (hz : z ∈ J) :
    ∃ w : R, φ (e t) * z * φ (e b) = φ (crossing * w) ∧ φ w ∈ J := by
  change z ∈ TwoSidedIdeal.span {r : U | ∃ s : Seq μ, IsViolated s ∧ r = φ (e s)} at hz
  have cut : ∀ y x : R, ∃ w : R,
      φ (e t * y) * z * φ (x * e b) = φ (crossing * w) ∧ φ w ∈ J := by
    refine TwoSidedIdeal.span_induction
      (p := fun r _ => ∀ y x : R, ∃ w : R,
        φ (e t * y) * r * φ (x * e b) = φ (crossing * w) ∧ φ w ∈ J)
      ?_ ?_ ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨s,hs,rfl⟩ y x
      obtain ⟨w,hw,hwJ⟩ := firstPairTerminal_column_violated_factor Q Λ hQ t crossing factor s hs x y
      exact ⟨w, by simpa only [map_mul φ,mul_assoc] using congrArg φ hw, hwJ⟩
    · intro y x
      exact ⟨0, by rw [mul_zero,zero_mul,mul_zero,map_zero], by rw [map_zero]; exact (J).zero_mem⟩
    · intro a d _ _ ha hd y x
      obtain ⟨u,hu,huJ⟩ := ha y x
      obtain ⟨v,hv,hvJ⟩ := hd y x
      exact ⟨u + v, by simpa only [mul_add, add_mul, map_add] using congrArg₂ (·+·) hu hv,
        by rw [map_add]; exact (J).add_mem huJ hvJ⟩
    · intro a _ ha y x
      obtain ⟨u,hu,huJ⟩ := ha y x
      exact ⟨-u, by simpa only [mul_neg, neg_mul, map_neg] using congrArg Neg.neg hu,
        by rw [map_neg]; exact (J).neg_mem huJ⟩
    · intro a d _ hd y x
      obtain ⟨r,rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) a
      simpa only [map_mul φ, mul_assoc] using hd (y * r) x
    · intro a d _ hd y x
      obtain ⟨r,rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) a
      simpa only [map_mul φ, mul_assoc] using hd y (r * x)
  simpa only [mul_one,one_mul] using cut 1 1

private theorem firstPairTerminal_affine_rightWord_cancel (hQ : KLRSymm Q)
    (lowerCut upperCut : Seq μ) (exitWord l r : List ℕ)
    (step : wordProd N exitWord • lowerCut = upperCut)
    (hl : IsReduced N l) (hr : IsReduced N r) (ne : wordProd N l ≠ wordProd N r)
    (matchings : ∀ w : Perm (Fin N), w • upperCut = b ↔ w = wordProd N l ∨ w = wordProd N r)
    (hl' : IsReduced N (l ++ exitWord)) (hr' : IsReduced N (r ++ exitWord))
    (ne' : wordProd N (l ++ exitWord) ≠ wordProd N (r ++ exitWord))
    (z : R) (left : e b * z = z) (right : z * e upperCut = z)
    (zero : z * (ψw exitWord * e lowerCut) = 0) : z = 0 := by
  obtain ⟨f,g,rows⟩ := exists_two_corner_coefficients_of_words
    (stendhalQ_symm Q Λ hQ) upperCut b l r hl hr ne matchings z left right
  have cut : (e upperCut : R) * (ψw exitWord * e lowerCut) = ψw exitWord * e lowerCut := by
    rw [← step, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  rw [rows, add_mul] at zero
  simp only [mul_assoc,cut] at zero
  rw [← mul_assoc (ψw l), ← mul_assoc (ψw r), ← ψw_append, ← ψw_append] at zero
  have hf := (top_polynomial_pair_eq_zero_iff_of_words (stendhalQ_symm Q Λ hQ)
    hl' hr' ne' lowerCut f g).mp zero
  rw [rows, hf.1, hf.2]
  simp only [map_zero, zero_mul, add_zero]

private theorem firstPairTerminal_affine_cancel (hQ : KLRSymm Q)
    (side : Bool) (z : R) (left : e (upper side) * z = z) (right : z * e b = z)
    (zero : c side * z = 0) : z = 0 := by
  have step : wordProd N [3] • lower side = upper side := by cases side <;> decide +kernel
  have zL : (e b : R) * hflip z = hflip z := by
    simpa only [hflip_mul,hflip_e] using congrArg hflip right
  have zR : hflip z * (e (upper side) : R) = hflip z := by
    simpa only [hflip_mul,hflip_e] using congrArg hflip left
  have flip : hflip (c side) = ψw [3] * e (lower side) := by
    rw [hflip_mul, hflip_ψ, hflip_e, e_mul_ψ]
    simp only [ψw_cons, ψw_nil, mul_one]
    congr 2
    cases side <;> decide +kernel
  have z0 : hflip z * (ψw [3] * e (lower side)) = 0 := by
    simpa only [hflip_mul, hflip_zero, flip] using congrArg hflip zero
  have red (w : List ℕ) (h₁ : ValidWord N w)
      (h₂ : w.length = invCount N (wordProd N w)) : IsReduced N w :=
    ⟨h₁, by rw [length_eq_invCount]; exact h₂⟩
  have eq : hflip z = 0 := by
    cases side
    · exact firstPairTerminal_affine_rightWord_cancel Q Λ hQ _ _ [3] [2,0,1,0] [1,2,0,1,0] step
        (red _ (by simp [ValidWord, stendhalWeight]) (by decide)) (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
        (by decide) (by decide +kernel) (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
        (red _ (by simp [ValidWord, stendhalWeight]) (by decide)) (by decide) _ zL zR z0
    · exact firstPairTerminal_affine_rightWord_cancel Q Λ hQ _ _ [3] [2,1,0] [1,2,1,0] step
        (red _ (by simp [ValidWord, stendhalWeight]) (by decide)) (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
        (by decide) (by decide +kernel) (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
        (red _ (by simp [ValidWord, stendhalWeight]) (by decide)) (by decide) _ zL zR z0
  simpa only [hflip_hflip,hflip_zero] using congrArg hflip eq

private theorem firstPairTerminal_common_exit (hQ : KLRSymm Q)
    (p : ℕ) (hp : p + 1 < N) (s w : Seq μ)
    (hr : s.lbl ⟨p,by omega⟩ = .inr 2) (terminal : w.lbl last = .inr 2) (x : R) :
    ∃ z : R, e s * x * e w = (ψ p * e (sadj N p • s)) * z := by
  have descent (σ : Perm (Fin N)) (hσ : σ • s = w) :
      σ ⟨p+1,hp⟩ < σ ⟨p,by omega⟩ := by
    have hred : w.lbl (σ ⟨p,by omega⟩) = .inr 2 := by
      rw [← hσ, lbl_smul]
      change s.lbl (σ.symm (σ ⟨p,by omega⟩)) = _
      rw [σ.symm_apply_apply]
      exact hr
    have h := lbl_inj_of_inr w (2 : Fin 3) hred terminal
    have le : σ ⟨p+1,hp⟩ ≤ last := Nat.le_of_lt_succ (σ ⟨p+1,hp⟩).isLt
    have ne : σ ⟨p+1,hp⟩ ≠ last := fun he => by
      have val : p + 1 = p := congrArg Fin.val (σ.injective (he.trans h.symm))
      exact Nat.succ_ne_self p val
    rw [h]
    exact lt_of_le_of_ne le ne
  obtain ⟨z,hz⟩ := exists_singleExitColumn_coefficient (stendhalQ_symm Q Λ hQ)
    s w p hp descent (hflip x)
  have flip : hflip (ψ p * e s : R) = ψ p * e (sadj N p • s) := by
    simp only [hflip_mul,hflip_e,hflip_ψ,e_mul_ψ]
  exact ⟨hflip z, by simpa only [hflip_mul,hflip_e,hflip_hflip,flip,mul_assoc] using congrArg hflip hz⟩

private theorem firstPairTerminal_reflect_crossing_zero (hQ : KLRSymm Q)
    (t u : Seq μ) (crossing : R) (factor : TerminalLeftFactor Q Λ t crossing)
    (cl : (e t : R) * crossing = crossing) (cr : crossing * e u = crossing)
    (diagram : toKLR k Q Λ ν (φ crossing) = crossing)
    (affineCancel : ∀ z : R, e u * z = z → z * e b = z → crossing * z = 0 → z = 0)
    (y : V) (left : F (e u) * y = y) (right : y * F (e b) = y)
    (zero : F crossing * y = 0) : y = 0 := by
  obtain ⟨a,ha⟩ := (violMk_surjective (Q := Q) (Λ := Λ)) y
  let G := toKLR k Q Λ ν
  let z := (e u : R) * G a * e b
  have back (r : U) : φ (G r) = r := ofKLR_toKLR (hQ := hQ) r
  have hz : F z = y := by
    change F ((e u : R) * G a * e b) = y
    rw [map_mul F, map_mul F, show F (G a) = y from (congrArg (violMk k Q Λ ν) (back a)).trans ha,
      left,right]
  have zG : G (φ z) = z := by
    simp only [z,map_mul φ,back,map_mul G,G,toKLR_ofKLR_e]
  have zl : e u * z = z := by simp only [z, ← mul_assoc, e_mul_self]
  have zr : z * e b = z := by simp only [z, mul_assoc, e_mul_self]
  have hxV : φ (crossing * z) ∈ J := (violMk_eq_zero_iff _).1 (by
    change F (crossing * z) = 0
    rwa [map_mul F,hz])
  obtain ⟨w, hw, hwJ⟩ := firstPairTerminal_lift_violating_relation Q Λ hQ t crossing factor _ hxV
  have phiEq : φ (crossing * z) = φ (crossing * w) := by
    rw [← map_mul φ (e t), ← map_mul φ, ← mul_assoc (e t : R) (crossing),
      cl, mul_assoc, zr] at hw
    exact hw
  let w₀ := G (φ w)
  have zeq : crossing * z = crossing * w₀ := by
    have h := congrArg G phiEq
    rw [map_mul φ (crossing) z, map_mul φ (crossing) w, map_mul G, map_mul G, diagram, zG] at h
    exact h
  let w' := (e u : R) * w₀ * e b
  have wL : e u * w' = w' := by simp only [w',← mul_assoc,e_mul_self]
  have wR : w' * e b = w' := by simp only [w',mul_assoc,e_mul_self]
  have cheq : crossing * (z - w') = 0 := by
    have cW : crossing * w' = crossing * w₀ * e b := by
      rw [show w' = _ from rfl, ← mul_assoc, ← mul_assoc, cr]
    rw [mul_sub, cW, ← zeq, mul_assoc (crossing) z (e b), zr, sub_self]
  have eq : z = w' := sub_eq_zero.mp <| affineCancel _ (by
    rw [mul_sub,zl,wL]) (by rw [sub_mul,zr,wR]) cheq
  have wJ : φ w' ∈ J := by
    simp only [w',w₀,map_mul φ,back]
    exact TwoSidedIdeal.mul_mem_right J _ _ (TwoSidedIdeal.mul_mem_left J _ _ hwJ)
  rw [← hz,eq]
  exact (violMk_eq_zero_iff _).2 wJ

/-- In the exchanged two-interior bottom column, the one-after-spectator
crossing is injective on the terminal source coefficient in the violated quotient. -/
theorem firstPairTerminal_column_crossing_cancel (hQ : KLRSymm Q)
    (side : Bool) (y : V) (left : F (e (upper side)) * y = y) (right : y * F (e b) = y)
    (zero : F (c side) * y = 0) : y = 0 := by
  refine firstPairTerminal_reflect_crossing_zero Q Λ hQ (lower side) (upper side) (c side)
    ?_ ?_ ?_ ?_ (firstPairTerminal_affine_cancel Q Λ hQ side) y left right zero
  · intro u terminal x
    exact firstPairTerminal_common_exit Q Λ hQ 3 (by decide) (lower side) u
      (by cases side <;> decide) terminal x
  · have step : sadj N 3 • lower side = upper side := rfl
    rw [← mul_assoc, e_mul_ψ,step,mul_assoc,e_mul_self]
  · simp only [mul_assoc,e_mul_self]
  · simp only [map_mul φ,map_mul (toKLR k Q Λ ν),toKLR_ofKLR_ψ,toKLR_ofKLR_e]

local notation "rightmost" => firstPairTwoAfterSpectator
local notation "middle" => firstPairOneAfterSpectator true
local notation "terminal" => sadj N 3 • middle
local notation "double" => (ψw [2,3] * e terminal : R)

private theorem firstPairRightmost_terminal_double_factor (hQ : KLRSymm Q) :
    TerminalLeftFactor Q Λ rightmost double := by
  intro w hlast x
  obtain ⟨a,ha₀⟩ := firstPairTerminal_common_exit Q Λ hQ 2 (by decide)
    rightmost w (by decide) hlast x
  have up : sadj N 2 • rightmost = middle := by decide +kernel
  have ha : (e rightmost : R) * x * e w = (ψ 2 * e middle) * a := by rwa [up] at ha₀
  have cutr : (ψ 2 * e middle : R) * e middle = ψ 2 * e middle := by
    rw [mul_assoc,e_mul_self]
  have hz : (e rightmost : R) * x * e w = (ψ 2 * e middle) * (e middle * a * e w) := by
    have hr : ((e rightmost : R) * x * e w) * e w = e rightmost * x * e w := by
      rw [mul_assoc (e rightmost * x : R), e_mul_self]
    calc
      _ = ((e rightmost : R) * x * e w) * e w := hr.symm
      _ = (ψ 2 * e middle) * (a * e w) := by rw [ha, mul_assoc]
      _ = ((ψ 2 * e middle) * e middle) * (a * e w) :=
        congrArg (· * (a * e w)) cutr.symm
      _ = _ := by simp only [mul_assoc]
  obtain ⟨z,hz'⟩ := firstPairTerminal_common_exit Q Λ hQ 3 (by decide)
    middle w (by decide) hlast a
  refine ⟨z, ?_⟩
  rw [hz,hz', ← mul_assoc]
  have hcut : (e middle : R) * ψ 3 * e terminal = ψ 3 * e terminal := by
    rw [e_mul_ψ, mul_assoc, e_mul_self]
  rw [mul_assoc (ψ 2) (e middle), ← mul_assoc (e middle : R) (ψ 3), hcut]
  simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]

private theorem firstPairRightmost_terminal_affine_cancel (hQ : KLRSymm Q)
    (z : R) (left : e terminal * z = z) (right : z * e b = z)
    (zero : double * z = 0) : z = 0 := by
  have step : wordProd N [3,2] • rightmost = terminal := by decide +kernel
  have zL : (e b : R) * hflip z = hflip z := by
    simpa only [hflip_mul,hflip_e] using congrArg hflip right
  have zR : hflip z * (e terminal : R) = hflip z := by
    simpa only [hflip_mul,hflip_e] using congrArg hflip left
  have flip : hflip double = ψw [3,2] * e rightmost := by
    rw [hflip_mul, hflip_e, hflip_ψw]
    change (e terminal : R) * ψw [3,2] = ψw [3,2] * e rightmost
    rw [e_mul_ψw, ← step, inv_smul_smul]
  have z0 : hflip z * (ψw [3,2] * e rightmost) = 0 := by
    simpa only [hflip_mul,hflip_zero,flip] using congrArg hflip zero
  have red (w : List ℕ) (h₁ : ValidWord N w)
      (h₂ : w.length = invCount N (wordProd N w)) : IsReduced N w :=
    ⟨h₁, by rw [length_eq_invCount]; exact h₂⟩
  have eq := firstPairTerminal_affine_rightWord_cancel Q Λ hQ _ _ [3,2] [2,1,0] [1,2,1,0] step
    (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
    (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
    (by decide) (by decide +kernel)
    (red _ (by simp [ValidWord, stendhalWeight]) (by decide))
    (red _ (by simp [ValidWord, stendhalWeight]) (by decide)) (by decide) _ zL zR z0
  simpa only [hflip_hflip,hflip_zero] using congrArg hflip eq

/-- The common double spectator crossing cancels in the actual exchanged
two-interior bottom column at the rightmost top. -/
theorem firstPairRightmost_terminal_double_cancel (hQ : KLRSymm Q)
    (y : V) (left : F (e terminal) * y = y) (right : y * F (e b) = y)
    (zero : F double * y = 0) : y = 0 := by
  refine firstPairTerminal_reflect_crossing_zero Q Λ hQ rightmost terminal double
    (firstPairRightmost_terminal_double_factor Q Λ hQ)
    ?_ ?_ ?_ (firstPairRightmost_terminal_affine_cancel Q Λ hQ) y left right zero
  · have step : wordProd N [2,3] • terminal = rightmost := by decide +kernel
    rw [← mul_assoc, e_mul_ψw, ← step, inv_smul_smul, mul_assoc,e_mul_self]
  · simp only [mul_assoc,e_mul_self]
  · simp only [map_mul φ,map_mul (toKLR k Q Λ ν),toKLR_ofKLR_ψw,toKLR_ofKLR_e]

/-- Both one-after-spectator tops satisfy the actual balanced kernel
test at the remaining first-pair bottom column. -/
theorem firstPairOneAfter_terminal_blockKernelColumnInclusion_injective
    (hQ : KLRSymm Q) (side : Bool) :
    Function.Injective (blockKernelColumnInclusion Q Λ (lower side) 0 1 b) :=
  firstPairOneAfter_blockKernelColumnInclusion_injective_of_cancellation Q Λ side hQ b
    (firstPairTerminal_column_crossing_cancel Q Λ hQ side)

section Standard

open QuantumGroup KL3.Diagram

variable {k₀ : Type} [Field k₀] (C : CartanDatum Unit) (weights : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k₀)

/-- Both one-after-spectator tops satisfy the ordinary balanced inclusion
over the full first-pair exchanged red order at standard parameters. -/
theorem firstPairOneAfter_blockKernelTensorInclusion_injective_standard (side : Bool) :
    Function.Injective
      (blockKernelTensorInclusion Qstd weights (lower side) 0 1 [1, 0, 2]) := by
  apply firstPair_blockKernelTensorInclusion_injective_standard_of_twoInterior C weights
  · cases side <;> decide
  · exact firstPairOneAfter_terminal_blockKernelColumnInclusion_injective Qstd weights
      (fun i j h => (h (Subsingleton.elim i j)).elim) side

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra
