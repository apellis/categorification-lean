/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftDescent

/-!
# The mirrored pull-off identity in the model of a cap at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. Let `Y` be the
induced model of `K̃^{λ⁺}_λ` (`CupCap.EndModel`), with the maximum of the cap on the last `N`
strands of `λ⁺`. Below the cap generators at a loading `s` of `λ` and a position `n`, let the
strand of `s` at `n` be black of colour `i`. The strands of `s` at `n + 1, …, m - 1` pass under
the maximum (`CupCap.passU`), and the block of the strand at `n` and the window at `n + 1`
(`CupCap.blockStendhal`) carries a copy of the module induced along adjoining a black strand on
the left. Its intertwining element gives a map into `Y`, which carries the left pull-off identity
of `L` (`CupCap.PullOffLeft`) to the relation (max2) in `Y`
(`CupCap.leftLoop_endModel`): the strand at `n`, pulled under the maximum to the right and back,
multiplies by the scalar of (max1).

## Main results

* `CupCap.leftBlockMap_underRight_underLeft`: the loop on the block.
* `CupCap.botMap_leftBlockMap_redOrdered_mul`: only red-ordered loadings of the block survive.
* `CupCap.intertwinesOn_passBlock`: the intertwining element of the passage.
* `CupCap.leftLoop_endModel`: the relation (max2) in the model, from `PullOffLeft`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Block

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} (i : I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Ri" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 νᵢ)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "EL" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) (leftBlockSet j hj ν₀ i s n hn)

open Classical in
theorem eSum_leftBlockSet_mul_ψ (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) {p : ℕ}
    (hp : p + 1 < N + 1) :
    (EL s n hn * KLRAlgebra.ψ (n + p) : Rp) = KLRAlgebra.ψ (n + p) * EL s n hn :=
  ((leftBlock j hj ν₀ i s n hn).ψ_mul_E (Q := stendhalQ Q (plusLabels Λ Λc j hj)) (j := p)
    (by rw [card_μB i (j := j) (hj := hj) (ν₀ := ν₀)]; exact hp)).symm

open Classical in
theorem leftBlockMap_ψw (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (ρ : List ℕ)
    (hρ : ∀ p ∈ ρ, p + 1 < N + 1) :
    (leftBlockMap j hj i Q Λ Λc s n hn (KLRAlgebra.ψw ρ)).val =
      EL s n hn * KLRAlgebra.ψw (ρ.map (n + ·)) := by
  induction ρ with
  | nil => rw [KLRAlgebra.ψw_nil, map_one, Corner.val_one, List.map_nil, KLRAlgebra.ψw_nil, mul_one]
  | cons p ρ ih =>
    rw [KLRAlgebra.ψw_cons, map_mul, Corner.val_mul, leftBlockMap_ψ i Q Λ Λc s hn (hρ p (by simp)),
      ih fun q hq => hρ q (by simp [hq]), List.map_cons, KLRAlgebra.ψw_cons,
      ← mul_assoc, mul_assoc (KLRAlgebra.ψ (n + p)),
      (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq,
      ← eSum_leftBlockSet_mul_ψ Q Λ Λc i s hn (hρ p (by simp)), mul_assoc]

open Classical in
theorem eSum_leftBlockSet_mul_ψw (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (ρ : List ℕ) (hρ : ∀ p ∈ ρ, p + 1 < N + 1) :
    (EL s n hn * KLRAlgebra.ψw (ρ.map (n + ·)) : Rp) =
      KLRAlgebra.ψw (ρ.map (n + ·)) * EL s n hn := by
  induction ρ with
  | nil => rw [List.map_nil, KLRAlgebra.ψw_nil, mul_one, one_mul]
  | cons p ρ ih =>
    rw [List.map_cons, KLRAlgebra.ψw_cons, ← mul_assoc,
      eSum_leftBlockSet_mul_ψ Q Λ Λc i s hn (hρ p (by simp)), mul_assoc,
      ih fun q hq => hρ q (by simp [hq]), mul_assoc]

omit [DecidableEq I] in
theorem mem_range'_zero_of_succ_lt {p : ℕ} (hp : p ∈ List.range' 0 N) : p + 1 < N + 1 := by
  rw [List.mem_range'_1] at hp; omega

open Classical in
/-- **The loop on the block**: the black strand at `n` pulled under the window to the right end of
the block and back. -/
theorem leftBlockMap_underRight_underLeft (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) :
    (leftBlockMap j hj i Q Λ Λc s n hn (underRight N 0 * underLeft N 0)).val =
      EL s n hn * (underRight N n * underLeft N n : Rp) := by
  have hr : (List.range' 0 N).map (n + ·) = List.range' n N := by
    rw [List.map_add_range', add_zero]
  have h1 := leftBlockMap_ψw (j := j) (hj := hj) Q Λ Λc i s hn (List.range' 0 N) fun p hp =>
    mem_range'_zero_of_succ_lt (ν₀ := ν₀) hp
  have h2 := leftBlockMap_ψw (j := j) (hj := hj) Q Λ Λc i s hn (List.range' 0 N).reverse fun p hp =>
    mem_range'_zero_of_succ_lt (ν₀ := ν₀) (List.mem_reverse.1 hp)
  have hc := eSum_leftBlockSet_mul_ψw (j := j) (hj := hj) Q Λ Λc i s hn (List.range' 0 N) fun p hp =>
    mem_range'_zero_of_succ_lt (ν₀ := ν₀) hp
  rw [hr] at h1 hc
  rw [List.map_reverse, hr] at h2
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (leftBlockSet j hj ν₀ i s n hn)).eq
  rw [map_mul, Corner.val_mul, underRight, underLeft, h1, h2]
  calc EL s n hn * KLRAlgebra.ψw (List.range' n N) *
        (EL s n hn * KLRAlgebra.ψw (List.range' n N).reverse) =
        EL s n hn * (KLRAlgebra.ψw (List.range' n N) * EL s n hn) *
          KLRAlgebra.ψw (List.range' n N).reverse := by simp only [mul_assoc]
    _ = EL s n hn * (KLRAlgebra.ψw (List.range' n N) * KLRAlgebra.ψw (List.range' n N).reverse) := by
      rw [← hc, ← mul_assoc, hE, mul_assoc]

omit [DecidableEq I] in
theorem isRedOrdered_of_prependBlackLoading {t : Seq (stendhalWeight 2 ν₀)}
    (h : IsRedOrdered (prependBlackLoading i ν₀ t)) : IsRedOrdered t := by
  intro a b r r' hab ha hb
  refine h (prependBlackPosition i ν₀ a) (prependBlackPosition i ν₀ b) r r' ?_
    (by rw [prependBlackLoading_lbl, ha]) (by rw [prependBlackLoading_lbl, hb])
  rw [Fin.lt_def, prependBlackPosition_val, prependBlackPosition_val]
  rw [Fin.lt_def] at hab
  omega

open Classical in
theorem redOrderedKLR_mul_e_prependBlackLoading (t : Seq (stendhalWeight 2 ν₀)) :
    redOrderedKLR k Q Λc νᵢ * KLRAlgebra.e (prependBlackLoading i ν₀ t) =
      if IsRedOrdered t then KLRAlgebra.e (prependBlackLoading i ν₀ t) else 0 := by
  classical
  change KLRAlgebra.eSum _ _ * _ = _
  rw [KLRAlgebra.eSum_mul_e]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (isRedOrdered_of_prependBlackLoading i h1) h2
  · exact absurd (prependBlackLoading_ordered i ν₀ t h2) h1
  · rfl

/-- The red-ordered loadings of `(i, μ, μ*)` beginning with the new black strand are the
prepended red-ordered loadings of `(μ, μ*)`. -/
theorem redOrderedKLR_mul_prependKLR_one :
    redOrderedKLR k Q Λc νᵢ * prependKLR ν₀ i Q Λc 1 =
      prependKLR ν₀ i Q Λc (redOrderedKLR k Q Λc ν₀) := by
  classical
  rw [← KLRAlgebra.sum_e (Q := stendhalQ Q Λc) (ν := stendhalWeight 2 ν₀), map_sum,
    Finset.mul_sum]
  simp_rw [prependKLR_e, redOrderedKLR_mul_e_prependBlackLoading]
  rw [redOrderedKLR, map_sum, Finset.sum_filter]
  simp_rw [prependKLR_e]

/-- **Only red-ordered loadings of the block survive** below the cap generators at `n + 1`. -/
theorem botMap_leftBlockMap_redOrdered_mul (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    botMap k Q Λ Λc j hj ν ν₀ ((leftBlockMap j hj i Q Λ Λc s n hn (redOrderedKLR k Q Λc νᵢ)).val *
        KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)) =
      botMap k Q Λ Λc j hj ν ν₀
        (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)) := by
  have h : (leftBlockMap j hj i Q Λ Λc s n hn
      (redOrderedKLR k Q Λc νᵢ * prependKLR ν₀ i Q Λc 1)).val =
      (leftBlockMap j hj i Q Λ Λc s n hn (redOrderedKLR k Q Λc νᵢ)).val *
        KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn) := by
    rw [map_mul, Corner.val_mul, leftBlockMap_prepend_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc
      s hn hs]
  rw [← h, redOrderedKLR_mul_prependKLR_one, leftBlockMap_prepend i Q Λ Λc s hn hs,
    botMap_insertMap_redOrderedKLR]

end Block

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc ℓ le_rfl ν ν₀

variable (ν ν₀) in
/-- An element `e · Z` of the corner of the end block. -/
def endGen (Z : Tp) : Corner (endOp Q Λ Λc ν ν₀) :=
  ⟨op (endStendhal Q Λ Λc ν ν₀ 1 * Z), by
    change op (endStendhal Q Λ Λc ν ν₀ 1 * Z) * endOp Q Λ Λc ν ν₀ 1 = _
    rw [endOp_apply, ← op_mul, unop_one, ← mul_assoc, ← map_mul, one_mul]⟩

theorem endGen_val (Z : Tp) : (endGen Q Λ Λc ν ν₀ Z).1 = op (endStendhal Q Λ Λc ν ν₀ 1 * Z) :=
  rfl

theorem op_smul_endGen (b Z : Tp) :
    (op b : Tpᵐᵒᵖ) • endGen Q Λ Λc ν ν₀ Z = endGen Q Λ Λc ν ν₀ (Z * b) :=
  Subtype.ext (by
    change op b * op _ = op _
    rw [← op_mul, mul_assoc])

theorem insertSet_congr (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') : insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s p hp =
      insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s p' hp' := by
  subst h; rfl

theorem insertMap_congr (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') (x : Rc) : ι s p hp x = ι s p' hp' x := by
  subst h; rfl

theorem exitSpan_congr (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') :
    exitSpan Q Λ Λc ℓ le_rfl (ν₀ := ν₀) s p hp = exitSpan Q Λ Λc ℓ le_rfl s p' hp' := by
  subst h; rfl

variable (ν ν₀) in
/-- The strands of `s` at `n + 1, …, m - 1` passing under the maximum to the right end. -/
abbrev passEnd (n : ℕ) : Rp := passU Q Λ Λc ℓ le_rfl ν ν₀ (n + 1) (m - (n + 1))

theorem passEnd_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) :
    passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn = E s m le_rfl * passEnd Q Λ Λc ν ν₀ n := by
  have h := passU_mul_eSum (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc s (n + 1) (m - (n + 1))
    (by omega)
  rwa [insertSet_congr s (p := n + 1 + (m - (n + 1))) _ le_rfl (by omega)] at h

theorem slides_passEnd (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (x : Rc) :
    ι s m le_rfl x * passEnd Q Λ Λc ν ν₀ n - passEnd Q Λ Λc ν ν₀ n * ι s (n + 1) hn x ∈
      exitSpan Q Λ Λc ℓ le_rfl s m le_rfl := by
  have h := slides_passU (j := ℓ) (hj := le_rfl) Q Λ Λc s (n + 1) x (m - (n + 1)) (by omega)
  rwa [insertMap_congr Q Λ Λc s (p := n + 1 + (m - (n + 1))) _ le_rfl (by omega),
    exitSpan_congr Q Λ Λc s (p := n + 1 + (m - (n + 1))) _ le_rfl (by omega)] at h

theorem cupMap_surjective (c : Tc) : ∃ w : Rc, cupMap k Q Λc ν₀ w = c := by
  obtain ⟨w, hw⟩ := StendhalAlgebraAllOrders.ofKLR_surjective c.val
  refine ⟨w, Subtype.ext ?_⟩
  change StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ w * _ = c.val
  rw [hw]
  exact KLR.Corner.val_mul_E c

variable (ν₀) in
/-- The block map on the opposite rings. -/
def blockOp (i : I) (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    (StendhalAlgebra k Q Λc ({i} + ν₀))ᵐᵒᵖ →ₙ+* Tpᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom
    (blockStendhal Q Λ Λc ℓ le_rfl ν₀ i s n hn))

variable (ν ν₀) in
/-- **The passage element**: `e · E_{s,m} · U`, where `U` passes the strands of `s` right of `n`
under the maximum to the right end. -/
def passElt (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) : Tpᵐᵒᵖ :=
  (endGen Q Λ Λc ν ν₀ (bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n))).1

theorem passElt_unit (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) :
    passElt Q Λ Λc ν ν₀ s n * endOp Q Λ Λc ν ν₀ 1 = passElt Q Λ Λc ν ν₀ s n :=
  (endGen Q Λ Λc ν ν₀ (bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n))).2

section Values

variable (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
  (hn : n + 1 ≤ Multiset.card (stendhalWeight ℓ ν))
  (hs : s.lbl ⟨n, by omega⟩ = .inl i)

include hn

local notation "θ" => blockStendhal Q Λ Λc ℓ le_rfl ν₀ i s n hn
local notation "lb" => leftBlockMap ℓ le_rfl i Q Λ Λc s n hn
local notation "RO" => redOrderedKLR k Q Λc ((Singleton.singleton i : Multiset I) + ν₀)

include hs in
theorem blockStendhal_prependBlack_one :
    θ (prependBlackStendhal Q Λc i ν₀ 1) = bot (E s (n + 1) hn) := by
  have h := blockStendhal_prependBlack (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc i s hn hs 1
  rwa [map_one, insertMap_one] at h

theorem blockStendhal_one : θ 1 = bot (lb RO).val := by
  have h := blockStendhal_cupMap (ν₀ := ν₀) (j := ℓ) (hj := le_rfl) Q Λ Λc i s hn 1
  rwa [map_one, blockBot_apply, blockBot_apply, ← map_mul, ← Corner.val_mul, ← map_mul,
    one_mul] at h

theorem bot_leftBlockMap_redOrdered_idem :
    bot (lb RO).val * bot (lb RO).val = bot (lb RO).val := by
  classical
  rw [← map_mul, ← Corner.val_mul, ← map_mul]
  congr 3
  exact (KLRAlgebra.eSum_idem (Q := stendhalQ Q Λc) (Finset.univ.filter fun t => IsRedOrdered t)).eq

include hs in
theorem eSum_mul_eSum_leftBlockSet :
    (E s (n + 1) hn * KLRAlgebra.eSum _ (leftBlockSet ℓ le_rfl ν₀ i s n hn) : Rp) =
      E s (n + 1) hn := by
  have h := KLR.Corner.val_mul_E (lb (prependKLR ν₀ i Q Λc 1))
  rwa [leftBlockMap_prepend_one (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) i Q Λ Λc s hn hs] at h

theorem eSum_passEnd_mul_eSum :
    (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn : Rp) =
      E s m le_rfl * passEnd Q Λ Λc ν ν₀ n := by
  rw [mul_assoc, passEnd_mul_eSum Q Λ Λc s hn, ← mul_assoc,
    (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq]

include hs in
/-- The value of the transported loop. -/
theorem loop_value :
    bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) *
        θ (prependBlackStendhal Q Λc i ν₀ 1 * pullOffLeftLoop k Q Λc ν₀ i) * θ 1 *
          bot (E s (n + 1) hn) =
      bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * (underRight N n * underLeft N n) *
        E s (n + 1) hn) := by
  rw [map_mul (blockStendhal Q Λ Λc ℓ le_rfl ν₀ i s n hn),
    blockStendhal_prependBlack_one (ν₀ := ν₀) Q Λ Λc i s hn hs, pullOffLeftLoop,
    blockStendhal_cupMap, blockStendhal_one, blockBot_apply, blockBot_apply]
  have hR := botMap_leftBlockMap_redOrdered_mul (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  calc bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) *
        (bot (E s (n + 1) hn) * (bot (lb (underRight N 0 * underLeft N 0)).val *
          bot (lb RO).val)) * bot (lb RO).val * bot (E s (n + 1) hn) =
        bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) * bot (E s (n + 1) hn) *
          bot (lb (underRight N 0 * underLeft N 0)).val *
            (bot (lb RO).val * bot (lb RO).val * bot (E s (n + 1) hn)) := by
        simp only [mul_assoc]
    _ = bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn *
          (lb (underRight N 0 * underLeft N 0)).val * E s (n + 1) hn) := by
        rw [bot_leftBlockMap_redOrdered_idem, hR]
        simp only [map_mul]
    _ = _ := by
        rw [leftBlockMap_underRight_underLeft,
          ← mul_assoc (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn),
          mul_assoc (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) (E s (n + 1) hn),
          eSum_mul_eSum_leftBlockSet Q Λ Λc i s hn hs, eSum_passEnd_mul_eSum Q Λ Λc s hn]

include hs in
/-- The value of the transported unit. -/
theorem unit_value :
    bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) * θ (prependBlackStendhal Q Λc i ν₀ 1) * θ 1 *
        bot (E s (n + 1) hn) =
      bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn) := by
  have hR := botMap_leftBlockMap_redOrdered_mul (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  rw [blockStendhal_prependBlack_one (ν₀ := ν₀) Q Λ Λc i s hn hs, blockStendhal_one,
    mul_assoc _ _ (bot _), hR,
    ← map_mul, ← map_mul, mul_assoc _ (E s (n + 1) hn),
    (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) _).eq]

end Values

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The passage element intertwines** the black-prepending map followed by the block map with
the end block, on a module supported on the loadings `μ ⋯ μ*`. -/
theorem intertwinesOn_passElt
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    IntertwinesOn L ((blockOp Q Λ Λc ν₀ i s n hn).comp (prependBlackTildeOp k Q Λc ν₀ i))
      (endOp Q Λ Λc ν ν₀) (passElt Q Λ Λc ν ν₀ s n) where
  unit := passElt_unit Q Λ Λc s n
  slide a z v := by
    refine IntertwinesOn.slide_of_mem_nullIdeal _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have he : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 =
        endStendhal Q Λ Λc ν ν₀ 1 := by rw [← map_mul, one_mul]
    have hc := (commute_endStendhal_one_endBot Q Λ Λc (ν := ν) w).eq
    have h1 : E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * ι s (n + 1) hn w =
        passEnd Q Λ Λc ν ν₀ n * ι s (n + 1) hn w := by
      rw [← passEnd_mul_eSum Q Λ Λc s hn, mul_assoc, ← insertMap_one Q Λ Λc s hn,
        ← insertMap_mul, one_mul]
    have key : ((blockOp Q Λ Λc ν₀ i s n hn).comp (prependBlackTildeOp k Q Λc ν₀ i))
        (op (cupMap k Q Λc ν₀ w)) * passElt Q Λ Λc ν ν₀ s n -
          passElt Q Λ Λc ν ν₀ s n * endOp Q Λ Λc ν ν₀ (op (cupMap k Q Λc ν₀ w)) =
        op (endStendhal Q Λ Λc ν ν₀ 1 *
          bot (-(ι s m le_rfl w * passEnd Q Λ Λc ν ν₀ n -
            passEnd Q Λ Λc ν ν₀ n * ι s (n + 1) hn w))) := by
      change op (blockStendhal Q Λ Λc ℓ le_rfl ν₀ i s n hn
          (prependBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) *
          op (endStendhal Q Λ Λc ν ν₀ 1 * bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n)) -
        op (endStendhal Q Λ Λc ν ν₀ 1 * bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n)) *
          op (endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ w)) = _
      rw [blockStendhal_prependBlack Q Λ Λc i s hn hs, endStendhal_cupMap', ← op_mul, ← op_mul,
        ← op_sub]
      congr 1
      have l1 : endStendhal Q Λ Λc ν ν₀ 1 * bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n) *
          bot (ι s (n + 1) hn w) =
          endStendhal Q Λ Λc ν ν₀ 1 * bot (passEnd Q Λ Λc ν ν₀ n * ι s (n + 1) hn w) := by
        rw [mul_assoc, ← map_mul, h1]
      have l2 : endStendhal Q Λ Λc ν ν₀ 1 * endBot Q Λ Λc ν ν₀ w *
          (endStendhal Q Λ Λc ν ν₀ 1 * bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n)) =
          endStendhal Q Λ Λc ν ν₀ 1 * bot (ι s m le_rfl w * passEnd Q Λ Λc ν ν₀ n) := by
        rw [map_mul bot (ι s m le_rfl w), ← endBot_mul_botMap_eSum, map_mul bot (E s m le_rfl),
          mul_assoc (endStendhal Q Λ Λc ν ν₀ 1), ← mul_assoc (endBot Q Λ Λc ν ν₀ w), ← hc,
          ← mul_assoc (endStendhal Q Λ Λc ν ν₀ 1), ← mul_assoc (endStendhal Q Λ Λc ν ν₀ 1), he]
        simp only [mul_assoc]
      rw [l1, l2, neg_sub, map_sub, mul_sub]
    rw [key]
    exact exitSpan_mem_nullIdeal Q Λ Λc L hL s (neg_mem (slides_passEnd Q Λ Λc s hn w))

/-- **The relation (max2) in the model of a cap at the right end**, from the left pull-off
identity of `L`: below the cap generators at `s` with the black strand of colour `i` at `n`, the
strand pulled under the maximum to the right and back multiplies by the scalar of (max1). -/
theorem leftLoop_endModel
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) (v : L) :
    (Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n *
        (underRight N n * underLeft N n) * E s (n + 1) hn))) v : EndModel Q Λ Λc ν ν₀ L) =
      Ind.tmul (endGen Q Λ Λc ν ν₀ (bot (E s m le_rfl * passEnd Q Λ Λc ν ν₀ n * E s (n + 1) hn)))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hX := intertwinesOn_passElt Q Λ Λc L hL i s hn hs
  have h := congrArg (fun t => (op (bot (E s (n + 1) hn)) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (prependBlackTildeOp k Q Λc ν₀ i) (blockOp Q Λ Λc ν₀ i s n hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  rw [← loop_value Q Λ Λc i s hn hs, ← unit_value Q Λ Λc i s hn hs]
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ)) <;>
    simp only [← op_mul, mul_assoc] <;> rfl

end Model

end Categorification.Stendhal.CupCap
