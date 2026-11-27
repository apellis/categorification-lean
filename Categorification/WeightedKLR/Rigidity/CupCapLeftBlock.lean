/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapPassage
import Categorification.WeightedKLR.Rigidity.CupCapPullOffLeft

/-!
# The strands at the maximum with one black strand on their left

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Below the cap generators at a loading `s`
of `λ` and a position `n`, let the strand of `s` at `n` be black of colour `i`. The block
`[n, n + N]` of `λ⁺`, formed by this strand and the window of the maximum at `n + 1`, carries the
diagrams of `R((i, μ, μ*))`: `CupCap.leftBlock` is its block embedding, for the loadings of `λ⁺`
that agree with `s` outside the block. Adjoining the black strand on the left of a diagram at the
maximum and placing the result on the block is placing the diagram on the window at `n + 1`
(`CupCap.leftBlockMap_prepend`).

## Main definitions

* `CupCap.leftBlockSet`: the loadings of `λ⁺` agreeing with `s` outside the block.
* `CupCap.leftBlock`: the block embedding.
* `CupCap.leftBlockMap`: the diagrams of `R((i, μ, μ*))` on the block.

## Main results

* `CupCap.leftBlockMap_prepend`: prepending a black strand, then placing on the block.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} (i : I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν₀)
local notation "μB" => Multiset.map (cupColour (I := I) j hj) (stendhalWeight 2 νᵢ)

omit [DecidableEq I] in
theorem card_μB : Multiset.card μB = N + 1 := by
  rw [Multiset.card_map]
  simp [stendhalWeight]

omit [DecidableEq I] in
theorem leftBlock_le {n : ℕ} (hn : n + 1 ≤ m) : n + Multiset.card μB ≤ M := by
  rw [card_μB (j := j) (hj := hj), card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)]; omega

open Classical in
variable (j hj ν₀) in
/-- The loadings of `λ⁺` that agree with `s` outside the block `[n, n + N]` and carry the colours
of `(i, μ, μ*)` on it. -/
def leftBlockSet (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :=
  Finset.univ.filter fun u =>
    (∀ (p : ℕ) (hp : p < n) (hM : p < M), u.lbl ⟨p, hM⟩ = oldColour j hj (s.lbl ⟨p, by omega⟩)) ∧
    (∀ (p : ℕ) (hp : n + N < p) (hM : p < M),
      u.lbl ⟨p, hM⟩ = oldColour j hj (s.lbl ⟨p - N, by
        have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩)) ∧
    Finset.univ.val.map (fun a => u.1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) = μB

open Classical in
theorem leftBlock_labels (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hu : u ∈ leftBlockSet j hj ν₀ i s n hn) :
    Finset.univ.val.map (fun a => u.1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) = μB :=
  (Finset.mem_filter.1 hu).2.2.2

open Classical in
theorem leftBlock_stab (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (p : ℕ)
    (hp : p + 1 < Multiset.card μB) (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    u ∈ leftBlockSet j hj ν₀ i s n hn ↔ sadj M (n + p) • u ∈ leftBlockSet j hj ν₀ i s n hn := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hB := card_μB i (j := j) (hj := hj) (ν₀ := ν₀)
  have hfix : ∀ (q : ℕ) (hq : q < M), (q < n ∨ n + N < q) →
      (sadj M (n + p) • u).lbl ⟨q, hq⟩ = u.lbl ⟨q, hq⟩ := by
    intro q hq hq'
    change (sadj M (n + p) • u).1 _ = u.1 _
    rw [sadj_smul_apply]
    refine congrArg u.1 (Fin.ext ?_)
    rw [sadj_val_of_lt (by omega)]
    unfold swapNat
    simp only
    split_ifs <;> omega
  have hwin : Finset.univ.val.map (fun a => (sadj M (n + p) • u).1
      (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) =
      Finset.univ.val.map (fun a => u.1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) := by
    have h1 : (fun a => (sadj M (n + p) • u).1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) =
        (fun a => u.1 (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) ∘ (sadj (Multiset.card μB) p) := by
      funext a
      change (sadj M (n + p) • u).1 _ = u.1 _
      rw [sadj_smul_apply, sadj_windowPos n (leftBlock_le (j := j) (hj := hj) i hn) hp]
    rw [h1, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  simp only [leftBlockSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun q hq hq' => ?_, fun q hq hq' => ?_, hwin.trans h3⟩
    · rw [hfix q hq' (Or.inl hq)]; exact h1 q hq hq'
    · rw [hfix q hq' (Or.inr hq)]; exact h2 q hq hq'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun q hq hq' => ?_, fun q hq hq' => ?_, hwin.symm.trans h3⟩
    · rw [← hfix q hq' (Or.inl hq)]; exact h1 q hq hq'
    · rw [← hfix q hq' (Or.inr hq)]; exact h2 q hq hq'

variable (j hj ν₀) in
/-- **The block of the black strand at `n` and the window at `n + 1`**, below the cap generators
at `s` and `n + 1`. -/
def leftBlock (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    BlockEmb μB (stendhalWeight (ℓ + 2) (ν + ν₀)) (leftBlockSet j hj ν₀ i s n hn) :=
  BlockEmb.window (leftBlockSet j hj ν₀ i s n hn) n (leftBlock_le (j := j) (hj := hj) i hn)
    (leftBlock_labels i s hn) (leftBlock_stab i s hn)

omit [DecidableEq I] in
/-- The labels of a bottom loading at `n + 1` on the block: the black strand of `s` at `n`, then
the window. -/
theorem insertSeq_window (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀))
    (a : Fin (Multiset.card μB)) :
    (insertSeq s (n + 1) hn (Seq.map (cupColour j hj) t)).1
        (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a) =
      (Seq.map (cupColour j hj) (prependBlackLoading i ν₀ t)).1 a := by
  have hB := card_μB i (j := j) (hj := hj) (ν₀ := ν₀)
  change (insertSeq s (n + 1) hn _).lbl _ = (Seq.map _ _).lbl a
  rw [Seq.map_lbl]
  rcases Nat.eq_zero_or_pos a.val with ha | ha
  · rw [insertSeq_lbl_lt s hn _ ⟨n, by omega⟩ (by dsimp only; omega)
      (by simp [windowPos, ha]), hs, prependBlackLoading_lbl_zero i ν₀ t _ (by rw [Fin.val_cast]; exact ha)]
    rfl
  · obtain ⟨b, hb⟩ : ∃ b : Fin N, a.val = b.val + 1 := ⟨⟨a.val - 1, by omega⟩, by simp; omega⟩
    have hpos : Fin.cast (Multiset.card_map _ _) a = prependBlackPosition i ν₀ b :=
      Fin.ext (by rw [Fin.val_cast, prependBlackPosition_val, hb])
    rw [hpos, prependBlackLoading_lbl,
      insertSeq_lbl_win s hn _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩
        (by simp [windowPos, hb]; omega), Seq.map_lbl]
    rfl

open Classical in
theorem insertSeq_mem_leftBlockSet (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀)) :
    insertSeq s (n + 1) hn (Seq.map (cupColour j hj) t) ∈ leftBlockSet j hj ν₀ i s n hn := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  simp only [leftBlockSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun p hp hpM => insertSeq_lbl_lt s hn _ ⟨p, by omega⟩ (by dsimp only; omega) rfl,
    fun p hp hpM => insertSeq_lbl_ge s hn _ ⟨p - N, by omega⟩ (by dsimp only; omega)
      (by dsimp only; omega), ?_⟩
  rw [show (fun a => (insertSeq s (n + 1) hn (Seq.map (cupColour j hj) t)).1
      (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) =
      (Seq.map (cupColour j hj) (prependBlackLoading i ν₀ t)).1 from
    funext (insertSeq_window i s hn hs t)]
  exact (Seq.map (cupColour j hj) (prependBlackLoading i ν₀ t)).2

open Classical in
/-- **The fibre of the block at a prepended loading** is the bottom loading of the cap generators
at `n + 1`. -/
theorem leftBlock_F_prepend (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀)) :
    (leftBlock j hj ν₀ i s n hn).F (Seq.map (cupColour j hj) (prependBlackLoading i ν₀ t)) =
      {insertSeq s (n + 1) hn (Seq.map (cupColour j hj) t)} := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hB := card_μB i (j := j) (hj := hj) (ν₀ := ν₀)
  ext u
  simp only [leftBlock, BlockEmb.window, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, hw⟩
    simp only [leftBlockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨h1, h2, -⟩ := hu
    refine Subtype.ext (funext fun c => ?_)
    change u.lbl c = (insertSeq s (n + 1) hn _).lbl c
    rcases lt_or_ge c.val n with hc | hc
    · rw [h1 c.val hc c.2, insertSeq_lbl_lt s hn _ ⟨c.val, by omega⟩ (by dsimp only; omega) rfl]
    rcases lt_or_ge (n + N) c.val with hc' | hc'
    · rw [h2 c.val hc' c.2, insertSeq_lbl_ge s hn _ ⟨c.val - N, by omega⟩ (by dsimp only; omega)
        (by dsimp only; omega)]
    · have hcw : c = windowPos n (leftBlock_le (j := j) (hj := hj) i hn) ⟨c.val - n, by omega⟩ :=
        Fin.ext (by simp [windowPos]; omega)
      rw [hcw]
      exact (hw _).trans (insertSeq_window i s hn hs t _).symm
  · rintro rfl
    exact ⟨insertSeq_mem_leftBlockSet i s hn hs t, fun a => insertSeq_window i s hn hs t a⟩

section Placing

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)

local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin 2))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Ri" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 νᵢ)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))

open Classical in
variable (j hj) in
/-- **Diagrams of `R((i, μ, μ*))` on the block** below the cap generators at `s` and `n + 1`. -/
def leftBlockMap (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    Ri →ₐ[k] (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
      (leftBlockSet j hj ν₀ i s n hn)).Corner :=
  ((leftBlock j hj ν₀ i s n hn).hom (stendhalQ Q (plusLabels Λ Λc j hj))).comp
    (KLRAlgebra.relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := νᵢ) k Q Λ Λc))

variable (ν₀) in
/-- Adjoining a black strand of colour `i` on the left of a diagram at the maximum. -/
def prependKLR : Rc →+ Ri where
  toFun w := castKLR (stendhalQ Q Λc) (stendhalWeight_prependBlack i ν₀)
    (((blockR σᵢ (stendhalWeight 2 ν₀)).hom (stendhalQ Q Λc) w).val)
  map_zero' := by simp only [map_zero, Corner.val_zero]
  map_add' u v := by simp only [map_add, Corner.val_add]

theorem prependKLR_mul (u v : Rc) :
    prependKLR ν₀ i Q Λc (u * v) = prependKLR ν₀ i Q Λc u * prependKLR ν₀ i Q Λc v := by
  change castKLR _ _ (((blockR σᵢ _).hom _ (u * v)).val) =
    castKLR _ _ (((blockR σᵢ _).hom _ u).val) * castKLR _ _ (((blockR σᵢ _).hom _ v).val)
  rw [map_mul, Corner.val_mul, map_mul]

theorem prependKLR_e (t : Seq (stendhalWeight 2 ν₀)) :
    prependKLR ν₀ i Q Λc (KLRAlgebra.e t) = KLRAlgebra.e (prependBlackLoading i ν₀ t) := by
  have hf : (blockR σᵢ (stendhalWeight 2 ν₀)).F t = {(default : Seq σᵢ).append t} := by
    classical
    ext u
    change u ∈ Finset.univ.image (fun a : Seq σᵢ => a.append t) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg (·.append t) (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  change castKLR _ _ (((blockR σᵢ _).hom _ (KLRAlgebra.e t)).val) = _
  rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum, Finset.sum_singleton, castKLR_e]
  rfl

theorem prependKLR_x (b : Fin N) :
    prependKLR ν₀ i Q Λc (KLRAlgebra.x b) =
      KLRAlgebra.x (prependBlackPosition i ν₀ b) * prependKLR ν₀ i Q Λc 1 := by
  change castKLR _ _ (((blockR σᵢ _).hom _ (KLRAlgebra.x b)).val) =
    _ * castKLR _ _ (((blockR σᵢ _).hom _ 1).val)
  rw [BlockEmb.hom_x, val_polCorner, pol_X, map_mul, castKLR_x, map_one, Corner.val_one]
  rfl

theorem prependKLR_ψ {r : ℕ} (hr : r + 1 < N) :
    prependKLR ν₀ i Q Λc (KLRAlgebra.ψ r) =
      KLRAlgebra.ψ (r + 1) * prependKLR ν₀ i Q Λc 1 := by
  change castKLR _ _ (((blockR σᵢ _).hom _ (KLRAlgebra.ψ r)).val) =
    _ * castKLR _ _ (((blockR σᵢ _).hom _ 1).val)
  rw [BlockEmb.hom_ψ, BlockEmb.val_gψ _ hr, map_mul, castKLR_ψ, map_one, Corner.val_one]
  congr 2
  simp [blockR, add_comm]

open Classical in
theorem leftBlockMap_smul (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) (c : k)
    (z : Ri) :
    (leftBlockMap j hj i Q Λ Λc s n hn (c • z)).val =
      c • (leftBlockMap j hj i Q Λ Λc s n hn z).val := by
  rw [map_smul]; exact KLR.Corner.val_smul c _

open Classical in
theorem leftBlockMap_e (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (u : Seq (stendhalWeight 2 νᵢ)) :
    (leftBlockMap j hj i Q Λ Λc s n hn (KLRAlgebra.e u)).val =
      KLRAlgebra.eSum _ ((leftBlock j hj ν₀ i s n hn).F (Seq.map (cupColour j hj) u)) := by
  change (((leftBlock j hj ν₀ i s n hn).hom _) (KLRAlgebra.relabelHom _ (KLRAlgebra.e u))).val = _
  rw [KLRAlgebra.relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF]
  rfl

open Classical in
theorem leftBlockMap_x (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (a : Fin (Multiset.card (stendhalWeight 2 νᵢ))) (hM : n + a.val < M) :
    (leftBlockMap j hj i Q Λ Λc s n hn (KLRAlgebra.x a)).val =
      KLRAlgebra.x ⟨n + a.val, hM⟩ * KLRAlgebra.eSum _ (leftBlockSet j hj ν₀ i s n hn) := by
  change (((leftBlock j hj ν₀ i s n hn).hom _) (KLRAlgebra.relabelHom _ (KLRAlgebra.x a))).val = _
  rw [KLRAlgebra.relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X]
  rfl

open Classical in
theorem leftBlockMap_ψ (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m) {r : ℕ}
    (hr : r + 1 < N + 1) :
    (leftBlockMap j hj i Q Λ Λc s n hn (KLRAlgebra.ψ r)).val =
      KLRAlgebra.ψ (n + r) * KLRAlgebra.eSum _ (leftBlockSet j hj ν₀ i s n hn) := by
  change (((leftBlock j hj ν₀ i s n hn).hom _) (KLRAlgebra.relabelHom _ (KLRAlgebra.ψ r))).val = _
  rw [KLRAlgebra.relabelHom_ψ, BlockEmb.hom_ψ,
    BlockEmb.val_gψ _ (by rw [card_μB i (j := j) (hj := hj) (ν₀ := ν₀)]; exact hr)]
  rfl

theorem leftBlockMap_prepend_mul_one (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (z : Ri) :
    (leftBlockMap j hj i Q Λ Λc s n hn (z * prependKLR ν₀ i Q Λc 1)).val =
      (leftBlockMap j hj i Q Λ Λc s n hn z).val *
        (leftBlockMap j hj i Q Λ Λc s n hn (prependKLR ν₀ i Q Λc 1)).val := by
  rw [map_mul, Corner.val_mul]

theorem leftBlockMap_prepend_one (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    (leftBlockMap j hj i Q Λ Λc s n hn (prependKLR ν₀ i Q Λc 1)).val =
      KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn) := by
  classical
  rw [← KLRAlgebra.sum_e (Q := stendhalQ Q Λc) (ν := stendhalWeight 2 ν₀), map_sum, map_sum,
    Corner.val_sum, eSum_insertSet Q Λ Λc s hn]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [prependKLR_e, leftBlockMap_e, leftBlock_F_prepend i s hn hs, KLRAlgebra.eSum,
    Finset.sum_singleton]

/-- **Prepending the black strand, then placing on the block**, is placing on the window at
`n + 1`, when the strand of `s` at `n` is black of colour `i`. -/
theorem leftBlockMap_prepend (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (w : Rc) :
    (leftBlockMap j hj i Q Λ Λc s n hn (prependKLR ν₀ i Q Λc w)).val =
      insertMap Q Λ Λc s (n + 1) hn w := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hone := leftBlockMap_prepend_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc s hn hs
  induction w using KLRAlgebra.klr_induction with
  | hadd u v hu hv => rw [map_add, map_add, Corner.val_add, hu, hv, insertMap_add]
  | hmul u v hu hv => rw [prependKLR_mul, map_mul, Corner.val_mul, hu, hv, insertMap_mul]
  | hr c =>
    have hp : prependKLR ν₀ i Q Λc (algebraMap k Rc c) =
        algebraMap k Ri c * prependKLR ν₀ i Q Λc 1 := by
      change castKLR _ _ (((blockR σᵢ _).hom _ (algebraMap k Rc c)).val) =
        _ * castKLR _ _ (((blockR σᵢ _).hom _ 1).val)
      rw [AlgHom.commutes, Corner.val_algebraMap, map_mul, AlgEquiv.commutes, map_one,
        Corner.val_one]
    rw [hp, leftBlockMap_prepend_mul_one, AlgHom.commutes, Corner.val_algebraMap, mul_assoc,
      Corner.E_mul_val, hone, insertMap_algebraMap, Algebra.smul_def]
  | he t =>
    rw [prependKLR_e, leftBlockMap_e, leftBlock_F_prepend i s hn hs, KLRAlgebra.eSum,
      Finset.sum_singleton, insertMap_e]
  | hx b =>
    rw [prependKLR_x, leftBlockMap_prepend_mul_one,
      leftBlockMap_x i Q Λ Λc s hn _ (by rw [prependBlackPosition_val]; omega), mul_assoc,
      Corner.E_mul_val, hone, insertMap_x]
    congr 2
    exact Fin.ext (by simp only [prependBlackPosition_val]; omega)
  | hψ r =>
    by_cases hr : r + 1 < N
    · rw [prependKLR_ψ i Q Λc hr, leftBlockMap_prepend_mul_one,
        leftBlockMap_ψ i Q Λ Λc s hn (by omega), mul_assoc, Corner.E_mul_val, hone,
        insertMap_ψ s hn hr, show n + (r + 1) = n + 1 + r by omega]
    · rw [KLRAlgebra.ψ_eq_zero r (by omega), map_zero, map_zero, Corner.val_zero, insertMap,
        map_zero, Corner.val_zero]

end Placing

end Categorification.Stendhal.CupCap
