/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent

/-!
# The strands at the maximum at the left end: the two blocks

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, the block decomposition (B3) with the black
block at the right end. Insert the two red strands `(μ, μ*)` before the red strands of `λ`
(`plusLabels Λ Λc 0`) and the strands at the maximum at the left end of a loading of `λ`. The
bottom loadings `insertSeq s 0 t` are the loadings of `λ⁺` whose first `N` strands form a loading
of the strands at the maximum and whose last `m` strands form a loading of `λ` (`frontSet`). Two
block embeddings into the corner of `frontSet` place a diagram at the maximum on the first `N`
strands (`frontMapKLR`) and a diagram of `λ` on the last `m` strands (`suffixMapKLR`); their
images commute (`commute_suffixMapKLR_frontMapKLR`), and `ι_{s,0}(x) = suffix(e(s)) · front(x)`
(`insertMap_eq_suffix_mul_front`). This is the mirror of `CupCap.endSet`, `CupCap.prefixMapKLR`
and `CupCap.endMapKLR`, with the window at position `0` in place of `m`.

## Main definitions

* `CupCap.frontSet`: the loadings `insertSeq s 0 t`.
* `CupCap.frontMapKLR`, `CupCap.suffixMapKLR`: the two block embeddings.

## Main results

* `CupCap.commute_suffixMapKLR_frontMapKLR`, `CupCap.insertMap_eq_suffix_mul_front`,
  `CupCap.frontMapKLR_eq_sum`, `CupCap.isRedOrdered_of_insertSeq_front`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section FrontBlock

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "z₀" => Nat.zero_le ℓ
local notation "zm" => Nat.zero_le (Multiset.card (stendhalWeight ℓ ν))
local notation "σ₀" => Multiset.map (cupColour (I := I) 0 (Nat.zero_le ℓ)) (stendhalWeight 2 ν₀)
local notation "μ₀" => Multiset.map (oldColour (I := I) 0 (Nat.zero_le ℓ)) (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (stendhalWeight (ℓ + 2) (ν + ν₀))

/-- The bottom loadings of the cap generators with the maximum at the left end of `λ`. -/
def frontSet : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :=
  Finset.univ.biUnion fun s : Seq (stendhalWeight ℓ ν) =>
    insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm

variable {ν ν₀}

omit [DecidableEq I] in
theorem card_σ₀ : Multiset.card σ₀ = N := Multiset.card_map _ _

omit [DecidableEq I] in
theorem card_μ₀ : Multiset.card μ₀ = m := Multiset.card_map _ _

theorem mem_frontSet {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))} :
    u ∈ frontSet ν ν₀ ↔ ∃ s t, insertSeq (j := 0) (hj := z₀) s 0 zm t = u := by
  simp [frontSet, insertSet]

theorem insertSeq_mem_frontSet (s : Seq (stendhalWeight ℓ ν)) (t : Seq σ₀) :
    insertSeq (j := 0) (hj := z₀) s 0 zm t ∈ frontSet ν ν₀ :=
  mem_frontSet.2 ⟨s, t, rfl⟩

omit [DecidableEq I] in
theorem front_window_le : 0 + Multiset.card σ₀ ≤ M := by
  rw [card_σ₀, card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)]; omega

omit [DecidableEq I] in
theorem suffix_window_le : N + Multiset.card μ₀ ≤ M := by
  rw [card_μ₀, card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)]; omega

theorem front_window_labels (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hu : u ∈ frontSet ν ν₀) :
    Finset.univ.val.map (fun a => u.1 (windowPos 0 front_window_le a)) = σ₀ := by
  obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
  conv_rhs => rw [← t.2]
  refine Multiset.map_congr rfl fun a _ => ?_
  exact insertSeq_lbl_win s zm t a rfl

theorem suffix_window_labels (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hu : u ∈ frontSet ν ν₀) :
    Finset.univ.val.map (fun a => u.1 (windowPos N suffix_window_le a)) = μ₀ := by
  obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
  conv_rhs => rw [← (Seq.map (oldColour (I := I) 0 z₀) s).2]
  refine Multiset.map_congr rfl fun a _ => ?_
  have ha : a.val < m := card_μ₀ (I := I) (ℓ := ℓ) (ν := ν) ▸ a.2
  exact insertSeq_lbl_ge s zm t ⟨a.val, ha⟩ (Nat.zero_le _)
    (by simp [windowPos]; omega)

theorem front_window_stab (p : ℕ) (hp : p + 1 < Multiset.card σ₀)
    (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    u ∈ frontSet ν ν₀ ↔ sadj M (0 + p) • u ∈ frontSet ν ν₀ := by
  constructor
  · intro hu
    obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
    rw [smul_insertSeq_new s zm t hp]
    exact insertSeq_mem_frontSet s _
  · intro hu
    obtain ⟨s, t, ht⟩ := mem_frontSet.1 hu
    rw [← KLRAlgebra.sadj_smul_smul (0 + p) u, ← ht, smul_insertSeq_new s zm t hp]
    exact insertSeq_mem_frontSet s _

theorem suffix_window_stab (p : ℕ) (_hp : p + 1 < Multiset.card μ₀)
    (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    u ∈ frontSet ν ν₀ ↔ sadj M (N + p) • u ∈ frontSet ν ν₀ := by
  have hc : crossPos 0 (Multiset.card σ₀) p = N + p := by
    rw [crossPos, ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_zero p)), card_σ₀]; omega
  constructor
  · intro hu
    obtain ⟨s, t, rfl⟩ := mem_frontSet.1 hu
    rw [← hc, smul_insertSeq_old s zm t (Or.inr (Nat.zero_le p))]
    exact insertSeq_mem_frontSet _ t
  · intro hu
    obtain ⟨s, t, ht⟩ := mem_frontSet.1 hu
    rw [← KLRAlgebra.sadj_smul_smul (N + p) u, ← ht, ← hc,
      smul_insertSeq_old s zm t (Or.inr (Nat.zero_le p))]
    exact insertSeq_mem_frontSet _ t

variable (ν ν₀)

/-- The block of the strands at the maximum, at the left end. -/
def frontWindow : BlockEmb σ₀ (stendhalWeight (ℓ + 2) (ν + ν₀)) (frontSet ν ν₀) :=
  BlockEmb.window (frontSet ν ν₀) 0 front_window_le front_window_labels front_window_stab

/-- The block of the strands of `λ`, at the right. -/
def suffixWindow : BlockEmb μ₀ (stendhalWeight (ℓ + 2) (ν + ν₀)) (frontSet ν ν₀) :=
  BlockEmb.window (frontSet ν ν₀) N suffix_window_le suffix_window_labels suffix_window_stab

/-- The diagrams of `λ` with the colours of `λ⁺`, for the red strands `(μ, μ*)` inserted first. -/
def suffixRelabel :
    SeqRelabel k (stendhalQ Q Λ) (stendhalQ Q (plusLabels Λ Λc 0 z₀)) (stendhalWeight ℓ ν) μ₀ :=
  SeqRelabel.ofInjectiveOf (oldColour_injective 0 z₀) _ _
    (fun a b _ => stendhalQ_oldColour Λ Λc 0 z₀ Q a b) _

/-- **A diagram at the maximum on the first `N` strands**, beside the identity on the strands of
`λ`. -/
def frontMapKLR (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) : Rp :=
  ((frontWindow ν ν₀).hom _
    (relabelHom (cupRelabel (j := 0) (hj := z₀) (ν₀ := ν₀) k Q Λ Λc) x)).val

/-- **A diagram of `λ` on the last `m` strands**, beside the identity on the strands at the
maximum. -/
def suffixMapKLR (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) : Rp :=
  ((suffixWindow ν ν₀).hom _ (relabelHom (suffixRelabel Q Λ Λc ν) a)).val

variable {Q Λ Λc ν ν₀}

theorem suffixMapKLR_mul (a b : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    suffixMapKLR Q Λ Λc ν ν₀ (a * b) = suffixMapKLR Q Λ Λc ν ν₀ a * suffixMapKLR Q Λ Λc ν ν₀ b := by
  unfold suffixMapKLR; rw [map_mul, map_mul]; rfl

theorem suffixMapKLR_add (a b : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    suffixMapKLR Q Λ Λc ν ν₀ (a + b) = suffixMapKLR Q Λ Λc ν ν₀ a + suffixMapKLR Q Λ Λc ν ν₀ b := by
  unfold suffixMapKLR; rw [map_add, map_add]; rfl

theorem suffixMapKLR_zero : suffixMapKLR Q Λ Λc ν ν₀ 0 = 0 := by
  unfold suffixMapKLR; rw [map_zero, map_zero]; rfl

theorem suffixMapKLR_smul (c : k) (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    suffixMapKLR Q Λ Λc ν ν₀ (c • a) = c • suffixMapKLR Q Λ Λc ν ν₀ a := by
  unfold suffixMapKLR
  rw [map_smul, AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

theorem frontMapKLR_mul (x y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (x * y) = frontMapKLR Q Λ Λc ν ν₀ x * frontMapKLR Q Λ Λc ν ν₀ y := by
  unfold frontMapKLR; rw [map_mul, map_mul]; rfl

theorem frontMapKLR_add (x y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (x + y) = frontMapKLR Q Λ Λc ν ν₀ x + frontMapKLR Q Λ Λc ν ν₀ y := by
  unfold frontMapKLR; rw [map_add, map_add]; rfl

theorem frontMapKLR_zero : frontMapKLR Q Λ Λc ν ν₀ 0 = 0 := by
  unfold frontMapKLR; rw [map_zero, map_zero]; rfl

theorem frontMapKLR_smul (c : k) (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ (c • x) = c • frontMapKLR Q Λ Λc ν ν₀ x := by
  unfold frontMapKLR
  rw [map_smul, AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

variable (Q Λ Λc ν ν₀) in
/-- **The two blocks commute.** -/
theorem commute_suffixMapKLR_frontMapKLR
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (suffixMapKLR Q Λ Λc ν ν₀ a) (frontMapKLR Q Λ Λc ν ν₀ x) := by
  have h := BlockEmb.commute_hom (Q := stendhalQ Q (plusLabels Λ Λc 0 z₀))
    (frontWindow ν ν₀) (suffixWindow ν ν₀) (by
      change 0 + Multiset.card σ₀ ≤ N
      rw [card_σ₀]; omega)
    (fun i l hl s => BlockEmb.window_F_sadj _ _ _ _ _ i (by
        have := suffix_window_le (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
        change N + l + 1 < M; omega)
      (Or.inr (by rw [card_σ₀]; omega))
      (suffix_window_stab l hl) s)
    (fun i l hl s => BlockEmb.window_F_sadj _ _ _ _ _ i (by
        have := front_window_le (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
        change 0 + l + 1 < M; omega)
      (Or.inl (by have := card_σ₀ (I := I) (ℓ := ℓ) (ν₀ := ν₀); change 0 + l + 1 < N; omega))
      (front_window_stab l hl) s)
    (relabelHom (cupRelabel (j := 0) (hj := z₀) (ν₀ := ν₀) k Q Λ Λc) x)
    (relabelHom (suffixRelabel Q Λ Λc ν) a)
  unfold Commute SemiconjBy suffixMapKLR frontMapKLR
  rw [← Corner.val_mul, ← Corner.val_mul, h.eq]

theorem suffixWindow_F (s : Seq (stendhalWeight ℓ ν)) :
    (suffixWindow ν ν₀).F (Seq.map (oldColour 0 z₀) s) =
      insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm := by
  ext u
  simp only [suffixWindow, BlockEmb.window, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hl⟩
    obtain ⟨s', t, rfl⟩ := mem_frontSet.1 hu
    have : s' = s := by
      apply Subtype.ext
      funext b
      have h1 := hl (Fin.cast (card_μ₀ (I := I) (ℓ := ℓ) (ν := ν)).symm b)
      rw [show (insertSeq s' 0 zm t).1 (windowPos N suffix_window_le
          (Fin.cast (card_μ₀ (I := I) (ℓ := ℓ) (ν := ν)).symm b)) =
          oldColour 0 z₀ (s'.lbl b) from
        insertSeq_lbl_ge s' zm t b (Nat.zero_le _) (by simp [windowPos]; omega)] at h1
      exact oldColour_injective 0 z₀ h1
    subst this
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
  · intro hu
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨insertSeq_mem_frontSet s t, fun a => ?_⟩
    have ha : a.val < m := card_μ₀ (I := I) (ℓ := ℓ) (ν := ν) ▸ a.2
    exact insertSeq_lbl_ge s zm t ⟨a.val, ha⟩ (Nat.zero_le _)
      (by simp [windowPos]; omega)

theorem insertSet_inter_frontWindow_F (s : Seq (stendhalWeight ℓ ν)) (t : Seq σ₀) :
    insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm ∩ (frontWindow ν ν₀).F t =
      {insertSeq s 0 zm t} := by
  ext u
  simp only [frontWindow, BlockEmb.window, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hu, -, hl⟩
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    apply Subtype.ext
    funext b
    rw [← hl b]
    exact (insertSeq_lbl_win s zm t' b rfl).symm
  · rintro rfl
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t), insertSeq_mem_frontSet s t,
      fun b => insertSeq_lbl_win s zm t b rfl⟩

theorem insertSet_subset_frontSet (s : Seq (stendhalWeight ℓ ν)) :
    insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm ⊆ frontSet ν ν₀ := by
  intro u hu
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  exact insertSeq_mem_frontSet s t

theorem insertSeq_mem_insertSet_front {s s' : Seq (stendhalWeight ℓ ν)} {t : Seq σ₀} :
    insertSeq (j := 0) (hj := z₀) s 0 zm t ∈
      insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s' 0 zm ↔ s' = s := by
  constructor
  · intro hu
    obtain ⟨t', -, ht⟩ := Finset.mem_image.1 hu
    exact eq_of_insertSeq_eq zm ht
  · rintro rfl
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)

theorem suffixMapKLR_e (s : Seq (stendhalWeight ℓ ν)) :
    suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) =
      KLRAlgebra.eSum _ (insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm) := by
  rw [suffixMapKLR, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF]
  exact congrArg _ (suffixWindow_F s)

theorem suffixMapKLR_x (a : Fin m) :
    suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.x a) =
      KLRAlgebra.x (⟨N + a.val, by
        have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩ : Fin M) *
        KLRAlgebra.eSum _ (frontSet ν ν₀) := by
  rw [suffixMapKLR, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X]
  congr 2

theorem suffixMapKLR_ψ {p : ℕ} (hp : p + 1 < m) :
    suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.ψ p) =
      KLRAlgebra.ψ (N + p) * KLRAlgebra.eSum _ (frontSet ν ν₀) := by
  rw [suffixMapKLR, relabelHom_ψ, BlockEmb.hom_ψ,
    BlockEmb.val_gψ _ (by rw [card_μ₀]; exact hp)]
  simp [suffixWindow, BlockEmb.window]

/-- **The diagrams at the maximum below the cap generators with the maximum at the left end**
are the diagrams at the maximum on the first `N` strands, cut by the loading of `λ`. -/
theorem insertMap_eq_suffix_mul_front (s : Seq (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    insertMap (j := 0) (hj := z₀) Q Λ Λc s 0 zm x =
      suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) * frontMapKLR Q Λ Λc ν ν₀ x := by
  have hE := suffixMapKLR_e (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) s
  have hEE : (suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s)) *
      suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) = suffixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) := by
    rw [← suffixMapKLR_mul, KLRAlgebra.e_mul_self]
  have hsub := insertSet_subset_frontSet (ν₀ := ν₀) s
  induction x using KLRAlgebra.klr_induction with
  | hadd u v hu hv =>
    rw [insertMap_add, hu, hv, frontMapKLR_add, mul_add]
  | hmul u v hu hv =>
    rw [insertMap_mul, hu, hv, frontMapKLR_mul, mul_assoc, ← mul_assoc (frontMapKLR _ _ _ _ _ u),
      ← (commute_suffixMapKLR_frontMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) u).eq, ← mul_assoc,
      ← mul_assoc, hEE, mul_assoc]
  | hr c =>
    rw [insertMap_algebraMap, frontMapKLR, AlgHom.commutes, AlgHom.commutes,
      Corner.val_algebraMap, hE, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      KLRAlgebra.eSum_mul_eSum, Finset.inter_eq_left.2 hsub, Algebra.smul_def]
  | he w =>
    rw [insertMap_e, frontMapKLR, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF,
      hE, KLRAlgebra.eSum_mul_eSum, insertSet_inter_frontWindow_F, KLRAlgebra.eSum,
      Finset.sum_singleton]
    rfl
  | hx b =>
    have hc := KLRAlgebra.pol_mul_eSum (Q := stendhalQ Q (plusLabels Λ Λc 0 z₀))
      (MvPolynomial.X ((frontWindow ν ν₀).pos (Fin.cast (cupRelabel (j := 0) (hj := z₀)
        (ν₀ := ν₀) k Q Λ Λc).card_eq b)))
      (insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm)
    rw [KLRAlgebra.pol_X] at hc
    rw [insertMap_x, frontMapKLR, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X, hE,
      ← mul_assoc, ← hc, mul_assoc, KLRAlgebra.eSum_mul_eSum, Finset.inter_eq_left.2 hsub]
    rfl
  | hψ p =>
    by_cases hp : p + 1 < N
    · rw [insertMap_ψ s zm hp, frontMapKLR, relabelHom_ψ, BlockEmb.hom_ψ,
        BlockEmb.val_gψ _ (by rw [card_σ₀]; exact hp), hE, ← mul_assoc]
      change _ = KLRAlgebra.eSum _ _ * KLRAlgebra.ψ (0 + p) * _
      rw [eSum_insertSet_mul_ψ s zm hp, mul_assoc, KLRAlgebra.eSum_mul_eSum,
        Finset.inter_eq_left.2 hsub]
    · rw [KLRAlgebra.ψ_eq_zero p (by omega), frontMapKLR_zero, mul_zero, insertMap, map_zero]
      rfl

variable (Q Λ Λc ν ν₀) in
theorem eSum_frontSet :
    (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc 0 z₀)) (frontSet ν ν₀) : Rp) =
      ∑ s : Seq (stendhalWeight ℓ ν),
        KLRAlgebra.eSum _ (insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm) := by
  rw [frontSet, KLRAlgebra.eSum, Finset.sum_biUnion]
  · rfl
  · intro s _ s' _ hss'
    refine Finset.disjoint_left.2 fun u hu hu' => hss' ?_
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    exact (insertSeq_mem_insertSet_front.1 hu').symm

/-- **A diagram at the maximum on the first `N` strands is the sum over the loadings of `λ` of
the diagrams at the maximum below the cap generators at position `0`.** -/
theorem frontMapKLR_eq_sum (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    frontMapKLR Q Λ Λc ν ν₀ x =
      ∑ s : Seq (stendhalWeight ℓ ν), insertMap (j := 0) (hj := z₀) Q Λ Λc s 0 zm x := by
  have h : KLRAlgebra.eSum _ (frontSet ν ν₀) * frontMapKLR Q Λ Λc ν ν₀ x =
      frontMapKLR Q Λ Λc ν ν₀ x := KLR.Corner.E_mul_val _
  rw [← h, eSum_frontSet, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [insertMap_eq_suffix_mul_front, suffixMapKLR_e]

omit [DecidableEq I] in
/-- In a red-ordered loading `insertSeq s 0 t`, the loading `s` of `λ` is red-ordered. -/
theorem isRedOrdered_of_insertSeq_front {s : Seq (stendhalWeight ℓ ν)} {t : Seq σ₀}
    (h : IsRedOrdered (insertSeq (j := 0) (hj := z₀) s 0 zm t)) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have h1 := insertSeq_lbl_ge s zm t (c := ⟨a.val + N, by omega⟩) a (Nat.zero_le _) rfl
  have h2 := insertSeq_lbl_ge s zm t (c := ⟨b.val + N, by omega⟩) b (Nat.zero_le _) rfl
  rw [ha] at h1
  rw [hb] at h2
  have := h _ _ _ _ (show (⟨a.val + N, by omega⟩ : Fin M) < ⟨b.val + N, by omega⟩ by
    rw [Fin.lt_def]; simp only; have := Fin.lt_def.1 hab; omega) h1 h2
  rw [Fin.lt_def] at this ⊢
  simpa [oldRed, insertPos] using this

end FrontBlock

end Categorification.Stendhal.CupCap
