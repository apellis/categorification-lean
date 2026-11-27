/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLeftLoop
import Categorification.WeightedKLR.Rigidity.CupCapPullOff

/-!
# The strands at the maximum with one black strand on their right

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17 and Lemma 7.16. Below the cap generators
at a loading `s` of `λ` and a position `n`, let the strand of `s` at `n` be black of colour `i`.
In the bottom loading of the cap generators at `s` and `n`, the window of the maximum sits at
`[n, n + N)` and is followed by this black strand at `n + N`. The block `[n, n + N]` carries the
diagrams of `R((μ, μ*, i))`, with the new strand last. Its loadings and its block embedding are
those of `CupCap.leftBlock`: the loadings of `λ⁺` that agree with `s` outside the block, with the
colours of `(μ, μ*, i)` on it. Adjoining the black strand on the right of a diagram at the
maximum and placing the result on the block is placing the diagram on the window at `n`
(`CupCap.leftBlockMap_append`).

## Main definitions

* `CupCap.appendKLR`: adjoining a black strand on the right of a diagram at the maximum.

## Main results

* `CupCap.leftBlock_F_append`: the fibre of the block at an appended loading.
* `CupCap.leftBlockMap_append`: appending a black strand, then placing on the block.
* `CupCap.leftBlockMap_underLeft_underRight`: the loop of the new strand on the block.
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
/-- The labels of a bottom loading at `n` on the block: the window, then the black strand of `s`
at `n`. -/
theorem insertSeq_window_append (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀))
    (a : Fin (Multiset.card μB)) :
    (insertSeq s n (by omega) (Seq.map (cupColour j hj) t)).1
        (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a) =
      (Seq.map (cupColour j hj) (appendBlackLoading i ν₀ t)).1 a := by
  have hB := card_μB i (j := j) (hj := hj) (ν₀ := ν₀)
  change (insertSeq s n _ _).lbl _ = (Seq.map _ _).lbl a
  rw [Seq.map_lbl]
  rcases lt_or_ge a.val N with ha | ha
  · rw [appendBlackLoading_lbl_of_lt i ν₀ t _ (by rw [Fin.val_cast]; exact ha),
      insertSeq_lbl_win s _ _
        ⟨a.val, by rw [Multiset.card_map (cupColour j hj) (stendhalWeight 2 ν₀)]; exact ha⟩
        (by simp [windowPos]), Seq.map_lbl]
    rfl
  · have ha' : a.val = N := by omega
    rw [insertSeq_lbl_ge s _ _ ⟨n, by omega⟩ (le_refl n) (by simp [windowPos, ha']), hs,
      appendBlackLoading_lbl_of_eq i ν₀ t _ (by rw [Fin.val_cast]; exact ha')]
    rfl

open Classical in
theorem insertSeq_mem_leftBlockSet_append (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀)) :
    insertSeq s n (by omega) (Seq.map (cupColour j hj) t) ∈ leftBlockSet j hj ν₀ i s n hn := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  simp only [leftBlockSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun p hp hpM => insertSeq_lbl_lt s _ _ ⟨p, by omega⟩ (by dsimp only; omega) rfl,
    fun p hp hpM => insertSeq_lbl_ge s _ _ ⟨p - N, by omega⟩ (by dsimp only; omega)
      (by dsimp only; omega), ?_⟩
  rw [show (fun a => (insertSeq s n (by omega) (Seq.map (cupColour j hj) t)).1
      (windowPos n (leftBlock_le (j := j) (hj := hj) i hn) a)) =
      (Seq.map (cupColour j hj) (appendBlackLoading i ν₀ t)).1 from
    funext (insertSeq_window_append i s hn hs t)]
  exact (Seq.map (cupColour j hj) (appendBlackLoading i ν₀ t)).2

open Classical in
/-- **The fibre of the block at an appended loading** is the bottom loading of the cap generators
at `n`. -/
theorem leftBlock_F_append (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (t : Seq (stendhalWeight 2 ν₀)) :
    (leftBlock j hj ν₀ i s n hn).F (Seq.map (cupColour j hj) (appendBlackLoading i ν₀ t)) =
      {insertSeq s n (by omega) (Seq.map (cupColour j hj) t)} := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hB := card_μB i (j := j) (hj := hj) (ν₀ := ν₀)
  ext u
  simp only [leftBlock, BlockEmb.window, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, hw⟩
    simp only [leftBlockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨h1, h2, -⟩ := hu
    refine Subtype.ext (funext fun c => ?_)
    change u.lbl c = (insertSeq s n _ _).lbl c
    rcases lt_or_ge c.val n with hc | hc
    · rw [h1 c.val hc c.2, insertSeq_lbl_lt s _ _ ⟨c.val, by omega⟩ (by dsimp only; omega) rfl]
    rcases lt_or_ge (n + N) c.val with hc' | hc'
    · rw [h2 c.val hc' c.2, insertSeq_lbl_ge s _ _ ⟨c.val - N, by omega⟩ (by dsimp only; omega)
        (by dsimp only; omega)]
    · have hcw : c = windowPos n (leftBlock_le (j := j) (hj := hj) i hn) ⟨c.val - n, by omega⟩ :=
        Fin.ext (by simp [windowPos]; omega)
      rw [hcw]
      exact (hw _).trans (insertSeq_window_append i s hn hs t _).symm
  · rintro rfl
    exact ⟨insertSeq_mem_leftBlockSet_append i s hn hs t,
      fun a => insertSeq_window_append i s hn hs t a⟩

section Placing

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)

local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin 2))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Ri" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 νᵢ)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (ν₀) in
/-- Adjoining a black strand of colour `i` on the right of a diagram at the maximum. -/
def appendKLR : Rc →+ Ri where
  toFun w := castKLR (stendhalQ Q Λc) (stendhalWeight_addBlack i ν₀)
    (((blockL (stendhalWeight 2 ν₀) σᵢ).hom (stendhalQ Q Λc) w).val)
  map_zero' := by simp only [map_zero, Corner.val_zero]
  map_add' u v := by simp only [map_add, Corner.val_add]

theorem appendKLR_mul (u v : Rc) :
    appendKLR ν₀ i Q Λc (u * v) = appendKLR ν₀ i Q Λc u * appendKLR ν₀ i Q Λc v := by
  change castKLR _ _ (((blockL _ σᵢ).hom _ (u * v)).val) =
    castKLR _ _ (((blockL _ σᵢ).hom _ u).val) * castKLR _ _ (((blockL _ σᵢ).hom _ v).val)
  rw [map_mul, Corner.val_mul, map_mul]

theorem appendKLR_e (t : Seq (stendhalWeight 2 ν₀)) :
    appendKLR ν₀ i Q Λc (KLRAlgebra.e t) = KLRAlgebra.e (appendBlackLoading i ν₀ t) := by
  have hf : (blockL (stendhalWeight 2 ν₀) σᵢ).F t = {t.append (default : Seq σᵢ)} := by
    classical
    ext u
    change u ∈ Finset.univ.image (fun a : Seq σᵢ => t.append a) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg t.append (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  change castKLR _ _ (((blockL _ σᵢ).hom _ (KLRAlgebra.e t)).val) = _
  rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum, Finset.sum_singleton, castKLR_e]
  rfl

theorem appendKLR_x (b : Fin N) :
    appendKLR ν₀ i Q Λc (KLRAlgebra.x b) =
      KLRAlgebra.x ⟨b.val, (card_stendhalWeight_νᵢ (ν₀ := ν₀) i).symm ▸ Nat.lt_succ_of_lt b.2⟩ *
        appendKLR ν₀ i Q Λc 1 := by
  change castKLR _ _ (((blockL _ σᵢ).hom _ (KLRAlgebra.x b)).val) =
    _ * castKLR _ _ (((blockL _ σᵢ).hom _ 1).val)
  rw [BlockEmb.hom_x, val_polCorner, pol_X, map_mul, castKLR_x, map_one, Corner.val_one]
  rfl

theorem appendKLR_ψ {r : ℕ} (hr : r + 1 < N) :
    appendKLR ν₀ i Q Λc (KLRAlgebra.ψ r) = KLRAlgebra.ψ r * appendKLR ν₀ i Q Λc 1 := by
  change castKLR _ _ (((blockL _ σᵢ).hom _ (KLRAlgebra.ψ r)).val) =
    _ * castKLR _ _ (((blockL _ σᵢ).hom _ 1).val)
  rw [BlockEmb.hom_ψ, BlockEmb.val_gψ _ hr, map_mul, castKLR_ψ, map_one, Corner.val_one]
  congr 2
  simp [blockL]

theorem leftBlockMap_append_mul_one (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (z : Ri) :
    (leftBlockMap j hj i Q Λ Λc s n hn (z * appendKLR ν₀ i Q Λc 1)).val =
      (leftBlockMap j hj i Q Λ Λc s n hn z).val *
        (leftBlockMap j hj i Q Λ Λc s n hn (appendKLR ν₀ i Q Λc 1)).val := by
  rw [map_mul, Corner.val_mul]

theorem leftBlockMap_append_one (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    (leftBlockMap j hj i Q Λ Λc s n hn (appendKLR ν₀ i Q Λc 1)).val =
      KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (by omega)) := by
  classical
  rw [← KLRAlgebra.sum_e (Q := stendhalQ Q Λc) (ν := stendhalWeight 2 ν₀), map_sum, map_sum,
    Corner.val_sum, eSum_insertSet Q Λ Λc s (by omega)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [appendKLR_e, leftBlockMap_e, leftBlock_F_append i s hn hs, KLRAlgebra.eSum,
    Finset.sum_singleton]

/-- **Appending the black strand, then placing on the block**, is placing on the window at `n`,
when the strand of `s` at `n` is black of colour `i`. -/
theorem leftBlockMap_append (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (w : Rc) :
    (leftBlockMap j hj i Q Λ Λc s n hn (appendKLR ν₀ i Q Λc w)).val =
      insertMap Q Λ Λc s n (by omega) w := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hone := leftBlockMap_append_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc s hn hs
  induction w using KLRAlgebra.klr_induction with
  | hadd u v hu hv => rw [map_add, map_add, Corner.val_add, hu, hv, insertMap_add]
  | hmul u v hu hv => rw [appendKLR_mul, map_mul, Corner.val_mul, hu, hv, insertMap_mul]
  | hr c =>
    have hp : appendKLR ν₀ i Q Λc (algebraMap k Rc c) =
        algebraMap k Ri c * appendKLR ν₀ i Q Λc 1 := by
      change castKLR _ _ (((blockL _ σᵢ).hom _ (algebraMap k Rc c)).val) =
        _ * castKLR _ _ (((blockL _ σᵢ).hom _ 1).val)
      rw [AlgHom.commutes, Corner.val_algebraMap, map_mul, AlgEquiv.commutes, map_one,
        Corner.val_one]
    rw [hp, leftBlockMap_append_mul_one, AlgHom.commutes, Corner.val_algebraMap, mul_assoc,
      Corner.E_mul_val, hone, insertMap_algebraMap, Algebra.smul_def]
  | he t =>
    rw [appendKLR_e, leftBlockMap_e, leftBlock_F_append i s hn hs, KLRAlgebra.eSum,
      Finset.sum_singleton, insertMap_e]
  | hx b =>
    rw [appendKLR_x, leftBlockMap_append_mul_one]
    rw [leftBlockMap_x i Q Λ Λc s hn ⟨b.val, by rw [card_stendhalWeight_νᵢ (ν₀ := ν₀) i]; omega⟩
        (by dsimp only; omega)]
    rw [mul_assoc, Corner.E_mul_val, hone, insertMap_x]
  | hψ r =>
    by_cases hr : r + 1 < N
    · rw [appendKLR_ψ i Q Λc hr, leftBlockMap_append_mul_one,
        leftBlockMap_ψ i Q Λ Λc s hn (by omega), mul_assoc, Corner.E_mul_val, hone,
        insertMap_ψ s _ hr]
    · rw [KLRAlgebra.ψ_eq_zero r (by omega), map_zero, map_zero, Corner.val_zero, insertMap,
        map_zero, Corner.val_zero]

local notation "EL" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) (leftBlockSet j hj ν₀ i s n hn)

open Classical in
/-- **The loop of the new strand on the block**: the black strand at `n + N` pulled under the
window to the left end of the block and back. -/
theorem leftBlockMap_underLeft_underRight (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) :
    (leftBlockMap j hj i Q Λ Λc s n hn (underLeft N 0 * underRight N 0)).val =
      EL s n hn * (underLeft N n * underRight N n : Rp) := by
  have hr : (List.range' 0 N).map (n + ·) = List.range' n N := by
    rw [List.map_add_range', add_zero]
  have h1 := leftBlockMap_ψw (j := j) (hj := hj) Q Λ Λc i s hn (List.range' 0 N) fun p hp =>
    mem_range'_zero_of_succ_lt (ν₀ := ν₀) hp
  have h2 := leftBlockMap_ψw (j := j) (hj := hj) Q Λ Λc i s hn (List.range' 0 N).reverse
    fun p hp => mem_range'_zero_of_succ_lt (ν₀ := ν₀) (List.mem_reverse.1 hp)
  have hc := eSum_leftBlockSet_mul_ψw (j := j) (hj := hj) Q Λ Λc i s hn
    (List.range' 0 N).reverse fun p hp =>
      mem_range'_zero_of_succ_lt (ν₀ := ν₀) (List.mem_reverse.1 hp)
  rw [hr] at h1
  rw [List.map_reverse, hr] at h2 hc
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (leftBlockSet j hj ν₀ i s n hn)).eq
  rw [map_mul, Corner.val_mul, underRight, underLeft, h1, h2]
  calc EL s n hn * KLRAlgebra.ψw (List.range' n N).reverse *
        (EL s n hn * KLRAlgebra.ψw (List.range' n N)) =
        EL s n hn * (KLRAlgebra.ψw (List.range' n N).reverse * EL s n hn) *
          KLRAlgebra.ψw (List.range' n N) := by simp only [mul_assoc]
    _ = EL s n hn * (KLRAlgebra.ψw (List.range' n N).reverse *
          KLRAlgebra.ψw (List.range' n N)) := by
      rw [← hc, ← mul_assoc, hE, mul_assoc]

end Placing

end Categorification.Stendhal.CupCap
