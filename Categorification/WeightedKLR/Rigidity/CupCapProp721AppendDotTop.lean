/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotMidCap

/-!
# The dot on the appended strand passing under the window

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the dot, for a cap at the right
end (`j = ℓ`). There `ι` passes the appended strand under the window (`CupCap.topPass`). A dot on
the passing strand slides through the passage up to the smoothings of its crossings with the
window strands of the same colour (`CupCap.x_mul_underRight_self`). In each smoothing the
window strand at the crossing leaves the window at the top, and the bottom loading of the window
ends with a black strand, so it is not of the form `μ ⋯ μ*`; these diagrams lie in the exit span
of the maximum (`CupCap.sum_midIdem_mul_topDotDiff_mem_midExit`), so they vanish in the model
(`CupCap.appendTopIota_appendedDot`). Hence `ι` carries the dot to the dot
(`CupCap.capTopIota_appendedDot`), and `CupCap.capEOrdIsoOfEqTop` carries the dot on `𝔈_i` to
the dot on `𝔈⁺_i` (`CupCap.capEOrdIsoOfEqTop_dot`).

Route hypotheses (tracked), as for `CupCap.capEEquivTop`: each piece `L e(t)` finitely
generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units (`hκ`) and the pull-off
identities (`hP`, `hPL`).

## Main results

* `CupCap.x_mul_underRight_self`, `CupCap.sum_midIdem_mul_topDotDiff_mem_midExit`.
* `CupCap.appendTopIota_appendedDot`, `CupCap.capTopIota_appendedDot`.
* `CupCap.capEOrdIsoOfEqTop_dot`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

theorem eqIdem_congr {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} {p p' : ℕ}
    (h : p = p') (hp : p + 1 < Multiset.card μ) (hp' : p' + 1 < Multiset.card μ) :
    (KLRAlgebra.eqIdem p hp : KLRAlgebra k Q' μ) = KLRAlgebra.eqIdem p' hp' := by
  subst h; rfl

/-- **A dot on the passing strand, moved through the passage `underRight`**: the error terms
are the smoothings of the crossings of the passing strand, `ψ_q ⋯ ψ_{q+b-1} · e_{=} ·
ψ_{q+b+1} ⋯ ψ_{q+n-1}`, where `e_{=}` is the idempotent of equal colours at `q + b`. -/
theorem x_mul_underRight_self {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} {q n : ℕ}
    (h : q + n < Multiset.card μ) :
    (KLRAlgebra.x ⟨q, by omega⟩ * KLRAlgebra.ψw (List.range' q n) : KLRAlgebra k Q' μ) =
      KLRAlgebra.ψw (List.range' q n) * KLRAlgebra.x ⟨q + n, h⟩ +
        ∑ b : Fin n, KLRAlgebra.ψw (List.range' q b.val) *
          KLRAlgebra.eqIdem (q + b.val) (by have := b.2; omega) *
          KLRAlgebra.ψw (List.range' (q + 1 + b.val) (n - 1 - b.val)) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    have h' : q + 1 + n < Multiset.card μ := by omega
    rw [List.range'_succ, KLRAlgebra.ψw_cons, ← mul_assoc,
      KLRAlgebra.x_mul_ψ_self q (by omega), add_mul, mul_assoc, ih h', mul_add, Finset.mul_sum,
      Fin.sum_univ_succ]
    have hx : (KLRAlgebra.x ⟨q + 1 + n, h'⟩ : KLRAlgebra k Q' μ) = KLRAlgebra.x ⟨q + (n + 1), h⟩ :=
      congrArg _ (Fin.ext (by dsimp only; omega))
    have hS : ∀ b : Fin n,
        (KLRAlgebra.ψ q * (KLRAlgebra.ψw (List.range' (q + 1) b.val) *
          KLRAlgebra.eqIdem (q + 1 + b.val) (by have := b.2; omega) *
          KLRAlgebra.ψw (List.range' (q + 1 + 1 + b.val) (n - 1 - b.val))) :
            KLRAlgebra k Q' μ) =
        KLRAlgebra.ψw (List.range' q b.succ.val) *
          KLRAlgebra.eqIdem (q + b.succ.val) (by have := b.2; simp only [Fin.val_succ]; omega) *
          KLRAlgebra.ψw (List.range' (q + 1 + b.succ.val) (n + 1 - 1 - b.succ.val)) := by
      intro b
      have hb := b.2
      simp only [Fin.val_succ]
      rw [List.range'_succ, KLRAlgebra.ψw_cons, eqIdem_congr (show q + 1 + b.val = q + (b.val + 1)
        by omega) _ (by omega), show q + 1 + 1 + b.val = q + 1 + (b.val + 1) by omega,
        show n - 1 - b.val = n + 1 - 1 - (b.val + 1) by omega]
      simp only [mul_assoc]
    have h0 : (KLRAlgebra.ψw (List.range' q (0 : Fin (n + 1)).val) *
        KLRAlgebra.eqIdem (q + (0 : Fin (n + 1)).val) (by simp; omega) *
        KLRAlgebra.ψw (List.range' (q + 1 + (0 : Fin (n + 1)).val)
          (n + 1 - 1 - (0 : Fin (n + 1)).val)) : KLRAlgebra k Q' μ) =
        KLRAlgebra.eqIdem q (by omega) * KLRAlgebra.ψw (List.range' (q + 1) n) := by
      simp only [Fin.val_zero, List.range'_zero, KLRAlgebra.ψw_nil, one_mul, add_zero,
        Nat.add_sub_cancel, Nat.sub_zero]
    rw [hx, Finset.sum_congr rfl fun b _ => hS b, h0, mul_assoc]
    abel

end Generic

section Ring

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

variable (ν) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "mᵢ" => Multiset.card (stendhalWeight ℓ ((Singleton.singleton i : Multiset I) + ν))
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Mᵢ" =>
  Multiset.card (stendhalWeight (ℓ + 2) ((Singleton.singleton i : Multiset I) + ν + ν₀))
local notation "Rpᵢ" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
    (stendhalWeight (ℓ + 2) ((Singleton.singleton i : Multiset I) + ν + ν₀))
local notation "Eᵢ" u:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u n hn) : Rpᵢ)
local notation "eA" => topPassIdem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "D" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "sᵢ" => appendBlackLoading i ν

omit [DecidableEq I] in
theorem add_card_lt_card_append : m + N < Mᵢ := by
  have := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢ) (ν₀ := ν₀)
  omega

omit [DecidableEq I] in
theorem card_lt_card_append : m < Mᵢ := by
  have := add_card_lt_card_append (ℓ := ℓ) (ν₀ := ν₀) ν i; omega

/-- `∑_u e_{u, m + 1}` fixes each window idempotent at `m + 1` from the left. -/
theorem sum_midIdem_mul_eSum_succ (h : ¬ j < ℓ) (t : Seq (stendhalWeight ℓ νᵢ)) :
    (∑ u, midIdem j hj Q Λ Λc νᵢ ν₀ u) * Eᵢ t (m + 1) (succ_le_card_appendBlackWeight ν i) =
      Eᵢ t (m + 1) (succ_le_card_appendBlackWeight ν i) := by
  rw [Finset.sum_mul, Finset.sum_eq_single t
    (fun u _ hu => by
      rw [midIdem_append_eq_of_not_lt ν i h]
      exact eSum_insertSet_mul_of_ne hu _)
    (fun h' => absurd (Finset.mem_univ _) h'), midIdem_append_eq_of_not_lt ν i h,
    (KLRAlgebra.eSum_idem _).eq]

/-- The difference of a dot on the passing strand above and below the passage carries the
window at `m` to the window at `m + 1`. -/
theorem underRightDotDiff_mul_eSum (t : Seq (stendhalWeight ℓ νᵢ)) :
    ((KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ *
          underRight N m -
        underRight N m * KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩ : Rpᵢ) *
        Eᵢ t m (le_card_appendBlackWeight ν i)) =
      Eᵢ t (m + 1) (succ_le_card_appendBlackWeight ν i) *
        (KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ *
          underRight N m -
        underRight N m * KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩) := by
  have hU := underRight_mul_eSum Q Λ Λc (j := j) (hj := hj) (ν₀ := ν₀) t
    (succ_le_card_appendBlackWeight ν i)
  rw [sub_mul, mul_sub, mul_assoc, hU, ← mul_assoc, (commute_x_eSum _ _).eq,
    mul_assoc (underRight N m), (commute_x_eSum _ _).eq, ← mul_assoc, hU]
  simp only [mul_assoc]

/-- **The dot on the passing strand moves through `D` modulo the exit span**: on the window
of the maximum, `x_m D - D x_{m + N}` is a sum of diagrams in which a window strand leaves the
maximum at the top. -/
theorem sum_midIdem_mul_topDotDiff_mem_midExit (h : ¬ j < ℓ) :
    (∑ u, midIdem j hj Q Λ Λc νᵢ ν₀ u) *
        (KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ * D -
          D * KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩) ∈
      midExit j hj Q Λ Λc νᵢ ν₀ := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hD : (KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ * D -
      D * KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩ : Rpᵢ) =
      ∑ s : Seq (stendhalWeight ℓ ν),
        (KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ *
            underRight N m -
          underRight N m * KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩) *
          Eᵢ (sᵢ s) m (le_card_appendBlackWeight ν i) := by
    rw [← Finset.mul_sum, ← topPassIdem, topPass, sub_mul]
    simp only [mul_assoc]
    rw [(commute_x_topPassIdem ν i _).eq]
  rw [hD, Finset.mul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [underRightDotDiff_mul_eSum, ← mul_assoc, sum_midIdem_mul_eSum_succ ν i h,
    ← (KLRAlgebra.eSum_idem _).eq, mul_assoc, ← underRightDotDiff_mul_eSum,
    underRight, x_mul_underRight_self (add_card_lt_card_append ν i), add_sub_cancel_left,
    Finset.sum_mul, Finset.mul_sum]
  refine mem_midExit_of (sᵢ s) (succ_le_card_appendBlackWeight ν i)
    (by rw [midPos_of_not_lt j _ h, hm]) (Submodule.sum_mem _ fun b _ => ?_)
  exact exitTerm_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (sᵢ s)
    (succ_le_card_appendBlackWeight ν i) b

section Model

local notation "bot'" => botMap k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "σ'" => midStendhal j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "aB⁺" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "X" => lastDotPlus k Q Λ Λc j hj ν₀ ν i
local notation "σK" => ∑ u, midIdem j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ u

/-- For a cap at the right end, the dot on the last strand of `λ` is `x_m` times the sum of
the window idempotents. -/
theorem midDot_last_eq_of_not_lt (h : ¬ j < ℓ) :
    midDot j hj Q Λ Λc νᵢ ν₀ (lastLoading ℓ ν i) =
      KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩ * σK := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  rw [midDot_eq_of_not_lt h]
  congr 2
  apply Fin.ext
  rw [dotPos_val_of_lt _ _ (by
    change Multiset.card (stendhalWeight ℓ νᵢ) - 1 < Multiset.card (stendhalWeight ℓ νᵢ)
    omega)]
  change _ - 1 = m
  omega

/-- The dot on the last strand of `λ⁺` is `x_{m + N}`. -/
theorem lastDotPlus_eq_botMap :
    X = bot' (KLRAlgebra.x ⟨m + N, add_card_lt_card_append ν i⟩) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hc := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢ) (ν₀ := ν₀)
  refine congrArg (fun a => bot' (KLRAlgebra.x a)) (Fin.ext ?_)
  change _ - 1 = m + N
  omega

variable (L : Type) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- The diagrams of the exit span vanish in the model after the unit of the maximum. -/
theorem midStendhal_mul_botMap_mem_nullIdeal
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0) {μ : Multiset I}
    {y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (μ + ν₀))}
    (hy : y ∈ midExit j hj Q Λ Λc μ ν₀) :
    op (midStendhal j hj Q Λ Λc μ ν₀ 1 * botMap k Q Λ Λc j hj μ ν₀ y) ∈
      nullIdeal L (midOp j hj Q Λ Λc μ ν₀) := by
  refine Submodule.iSup_induction _
    (motive := fun y => op (midStendhal j hj Q Λ Λc μ ν₀ 1 * botMap k Q Λ Λc j hj μ ν₀ y) ∈
      nullIdeal L (midOp j hj Q Λ Λc μ ν₀)) hy
    (fun s y hy => exitSpan_midPos_mem_nullIdeal L hL s hy) ?_ ?_
  · rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  · intro y y' h h'; rw [map_add, mul_add, op_add]; exact add_mem h h'

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **Appending a strand carries the new dot to the new dot**, for `j = ℓ` (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21): on the image of `ι`, the left action of the dot on the
appended strand of `T̃^λ` times its unit is the right action of the dot `X` on the appended
strand of `T̃^{λ⁺}` times its unit. The two differ by the smoothings of
`CupCap.sum_midIdem_mul_topDotDiff_mem_midExit`, which vanish in the model. Route hypotheses
(tracked): `hκ`, `hP`, `hPL`. -/
theorem appendTopIota_appendedDot (h : ¬ j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hR' (orderProjection Q Λ νᵢ (StendhalAlgebraAllOrders.newDot Q Λ i ν) *
        appendBlackStendhal Q Λ i ν 1) (appendTopIota ν i hP hPL hL hκ h y) =
      op (X * aB⁺ 1) • appendTopIota ν i hP hPL hL hκ h y := by
  rw [map_mul, Module.End.mul_apply, ← appendTopIota_midLeftAlg ν i hP hPL hL hκ h hR hR' 1,
    map_one, Module.End.one_apply, newDot_eq_ofKLR_lastLoading]
  change midLeftAlg L hL hR' (topMap k Q Λ νᵢ (KLRAlgebra.x (lastLoading ℓ ν i))) _ = _
  rw [midLeftAlg_topMap, midKLRAct_x]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : appendTopIota (Λ := Λ) (hj := hj) ν i hP hPL hL hκ h 0 = 0 := by
      rw [appendTopIota, Ind.tmul_zero, map_zero]; rfl
    rw [h0, map_zero, smul_zero]
  | add a b ha hb => rw [appendTopIota_add, map_add, ha, hb, smul_add]
  | tmul w v =>
    rw [appendTopIota_tmul, midEnd]
    change natMapOn _ (Ind.tmul _ v) = op (X * aB⁺ 1) • Ind.tmul _ v
    rw [natMapOn_tmul, Ind.smul_tmul, ← sub_eq_zero, sub_eq_add_neg, ← Ind.neg_tmul,
      ← Ind.add_tmul, ← sub_eq_add_neg]
    have hy := sum_midIdem_mul_topDotDiff_mem_midExit (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj)
      (ν₀ := ν₀) ν i h
    have hmem := midStendhal_mul_botMap_mem_nullIdeal (L := L) hL hy
    refine (congrArg (fun z => Ind.tmul z v) ?_).trans
      (tmul_eq_zero_of_mem_nullIdeal (mul_mem_nullIdeal (op (aB⁺ w.1.unop * aB⁺ 1)) hmem) v)
    apply Subtype.ext
    apply MulOpposite.unop_injective
    have hA : ∀ x, (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i x).unop = aB⁺ x.unop := fun _ => rfl
    have hsm : ∀ c : Corner (midOp j hj Q Λ Λc νᵢ ν₀),
        ((op (X * aB⁺ 1) • c : Corner (midOp j hj Q Λ Λc νᵢ ν₀)) : _) = op (X * aB⁺ 1) * c.1 :=
      fun _ => rfl
    simp only [Submodule.coe_sub, cornerMulOf_val, midElt, compMul, unitGen, unop_sub, unop_mul,
      unop_op, hA, unop_one, hsm]
    have hs : σ' 1 = bot' σK := midStendhal_one_eq_botMap _
    have f1 : bot' (midDot j hj Q Λ Λc νᵢ ν₀ (lastLoading ℓ ν i)) =
        bot' (KLRAlgebra.x ⟨m, card_lt_card_append ν i⟩) * σ' 1 := by
      rw [midDot_last_eq_of_not_lt ν i h, map_mul, hs]
    have f2 : σ' 1 * bot' D = bot' D := by
      rw [hs, ← map_mul, sum_midIdem_mul_topPass ν i h]
    have f3 : σ' 1 * σ' 1 = σ' 1 := by rw [← map_mul, one_mul]
    have f4 := lastDotPlus_eq_botMap (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i
    have f5 : ∀ W, X * aB⁺ W = aB⁺ W * X := fun W => (commute_lastDotPlus_appendBlackPlus ν i W).eq
    have f6 : aB⁺ 1 * aB⁺ 1 = aB⁺ 1 := by rw [← map_mul, one_mul]
    have t2 : bot' D * (aB⁺ w.1.unop * aB⁺ 1) * (X * aB⁺ 1) =
        bot' D * X * (aB⁺ w.1.unop * aB⁺ 1) := by
      simp only [mul_assoc]
      rw [← mul_assoc (aB⁺ 1) X, ← f5, mul_assoc X, f6, ← mul_assoc (aB⁺ w.1.unop) X, ← f5,
        mul_assoc]
    rw [f1, t2, map_mul, ← hs, map_sub, map_mul, map_mul, ← f4]
    have f2' : ∀ z, σ' 1 * (bot' D * z) = bot' D * z := fun z => by rw [← mul_assoc, f2]
    have f3' : ∀ z, σ' 1 * (σ' 1 * z) = σ' 1 * z := fun z => by rw [← mul_assoc, f3]
    simp only [mul_sub, sub_mul, mul_assoc, f2', f3']

end Model

section Cap

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **`ι` carries the dot to the dot**, for `j = ℓ` (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21): the left action of the dot on the appended strand of `T^λ` on `ι(c)` is the
right action of the dot on the appended strand of `T^{λ⁺}`. Route hypotheses (tracked): `hκ`,
`hP`, `hPL`. -/
theorem capTopIota_appendedDot (h : ¬ j < ℓ) (c : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    appendedDot Q Λ i ν • capTopIota ν i hR hR' hP hPL hκ h c =
      castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
        (op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀))) •
        capTopIota ν i hR hR' hP hPL hκ h c := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hι := capModelRightEquiv_capTopIota ν i hR hR' hP hPL hκ h c y hy.symm
  rw [castOp_appendedDot_plus, ← capStendhal_smul, appendedDot_eq_mk_mul]
  change capLeftLin (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) L
      (orderProjection Q Λ νᵢ (StendhalAlgebraAllOrders.newDot Q Λ i ν) *
        appendBlackStendhal Q Λ i ν 1) _ = _
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  rw [capModelRightEquiv_capLeftLin hR' hP hPL hκ _ _ _ hι, LinearEquiv.map_smul, hι,
    ← Submodule.Quotient.mk_smul, appendTopIota_appendedDot ν i hP hPL hκ h hR hR']

end Cap

end Ring

section Field

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

open CategoryTheory in
/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` carries the dot to the dot, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): `(K ∘ x) ≫ φ = φ ≫ (x ∘ K)` for
`φ = CupCap.capEOrdIsoOfEqTop`, with `x` the dot on `𝔈_i` (`blackDot`) and on `𝔈⁺_i`
(`resDotOfEq`). Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
theorem capEOrdIsoOfEqTop_dot (h : ¬ j < ℓ) :
    Functor.whiskerRight (blackDot Q Λ i ν) OrdK ≫
        (capEOrdIsoOfEqTop ν i hR hR' hP hPL hκ hQ hfin h).hom =
      (capEOrdIsoOfEqTop ν i hR hR' hP hPL hκ hQ hfin h).hom ≫ Functor.whiskerLeft OrdKᵢ
        (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) :=
  capEOrdIsoOfEq_dot _ (capTopIota_appendedDot ν i hR hR' hP hPL hκ h)

end Field

end Categorification.Stendhal.CupCap
