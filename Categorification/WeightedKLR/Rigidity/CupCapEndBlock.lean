/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapSliding
import Categorification.KLR.BlockCommute
import Categorification.KLR.WindowBlock
import Categorification.KLR.ReindexSymmetries

/-!
# The cap at the right end of the red strands: the two blocks

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ` where the cap is
inserted to the right of all red strands of `λ`. The bottom loadings of the cap generators with
the maximum at the right end, `insertSeq s m t`, are the loadings of `λ⁺` whose first `m`
strands form a loading of `λ` and whose last `N` strands form a loading of the strands at the
maximum (`endSet`). Two block embeddings into the corner of `endSet` place a diagram of `λ` on the
first `m` strands (`prefixMapKLR`) and a diagram at the maximum on the last `N` strands
(`endMapKLR`); their images commute (`commute_prefixMapKLR_endMapKLR`), and together they give the
diagrams at the maximum below the cap generators: `ι_{s,m}(x) = prefix(e(s)) · end(x)`
(`insertMap_eq_prefix_mul_end`).

## Main definitions

* `CupCap.endSet`: the loadings `insertSeq s m t`.
* `CupCap.prefixMapKLR`, `CupCap.endMapKLR`: the two block embeddings.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section EndBlock

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "σ" => Multiset.map (cupColour (I := I) ℓ le_rfl) (stendhalWeight 2 ν₀)
local notation "μL" => Multiset.map (oldColour (I := I) ℓ le_rfl) (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))

/-- The bottom loadings of the cap generators with the maximum at the right end of `λ`. -/
def endSet : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :=
  Finset.univ.biUnion fun s : Seq (stendhalWeight ℓ ν) =>
    insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl

variable {ν ν₀}

omit [DecidableEq I] in
theorem card_σ : Multiset.card σ = N := Multiset.card_map _ _

omit [DecidableEq I] in
theorem card_μL : Multiset.card μL = m := Multiset.card_map _ _

theorem mem_endSet {u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))} :
    u ∈ endSet ν ν₀ ↔ ∃ s t, insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t = u := by
  simp [endSet, insertSet]

theorem insertSeq_mem_endSet (s : Seq (stendhalWeight ℓ ν)) (t : Seq σ) :
    insertSeq (j := ℓ) (hj := le_rfl) s m le_rfl t ∈ endSet ν ν₀ :=
  mem_endSet.2 ⟨s, t, rfl⟩

omit [DecidableEq I] in
theorem m_add_N : m + N = M := (card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)).symm

omit [DecidableEq I] in
theorem end_window_le : m + Multiset.card σ ≤ M := by
  rw [card_σ, m_add_N]

omit [DecidableEq I] in
theorem prefix_window_le : 0 + Multiset.card μL ≤ M := by
  rw [card_μL, ← m_add_N]; omega

theorem end_window_labels (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hu : u ∈ endSet ν ν₀) :
    Finset.univ.val.map (fun a => u.1 (windowPos m end_window_le a)) = σ := by
  obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
  conv_rhs => rw [← t.2]
  refine Multiset.map_congr rfl fun a _ => ?_
  exact insertSeq_lbl_win s le_rfl t a rfl

theorem prefix_window_labels (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hu : u ∈ endSet ν ν₀) :
    Finset.univ.val.map (fun a => u.1 (windowPos 0 prefix_window_le a)) = μL := by
  obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
  conv_rhs => rw [← (Seq.map (oldColour (I := I) ℓ le_rfl) s).2]
  refine Multiset.map_congr rfl fun a _ => ?_
  have ha : a.val < m := card_μL (I := I) (ℓ := ℓ) (ν := ν) ▸ a.2
  exact insertSeq_lbl_lt s le_rfl t ⟨a.val, ha⟩ ha (by simp [windowPos])

theorem end_window_stab (p : ℕ) (hp : p + 1 < Multiset.card σ)
    (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    u ∈ endSet ν ν₀ ↔ sadj M (m + p) • u ∈ endSet ν ν₀ := by
  constructor
  · intro hu
    obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
    rw [smul_insertSeq_new s le_rfl t hp]
    exact insertSeq_mem_endSet s _
  · intro hu
    obtain ⟨s, t, ht⟩ := mem_endSet.1 hu
    rw [← KLRAlgebra.sadj_smul_smul (m + p) u, ← ht, smul_insertSeq_new s le_rfl t hp]
    exact insertSeq_mem_endSet s _

theorem prefix_window_stab (p : ℕ) (hp : p + 1 < Multiset.card μL)
    (u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    u ∈ endSet ν ν₀ ↔ sadj M (0 + p) • u ∈ endSet ν ν₀ := by
  have hp' : p + 1 < m := card_μL (I := I) (ℓ := ℓ) (ν := ν) ▸ hp
  have hc : crossPos m (Multiset.card σ) p = 0 + p := by
    rw [crossPos, ite_eq_left (by omega : p < m), zero_add]
  constructor
  · intro hu
    obtain ⟨s, t, rfl⟩ := mem_endSet.1 hu
    rw [← hc, smul_insertSeq_old s le_rfl t (Or.inl hp')]
    exact insertSeq_mem_endSet _ t
  · intro hu
    obtain ⟨s, t, ht⟩ := mem_endSet.1 hu
    rw [← KLRAlgebra.sadj_smul_smul (0 + p) u, ← ht, ← hc,
      smul_insertSeq_old s le_rfl t (Or.inl hp')]
    exact insertSeq_mem_endSet _ t

variable (ν ν₀)

/-- The block of the strands at the maximum, at the right end. -/
def endWindow : BlockEmb σ (stendhalWeight (ℓ + 2) (ν + ν₀)) (endSet ν ν₀) :=
  BlockEmb.window (endSet ν ν₀) m end_window_le end_window_labels end_window_stab

/-- The block of the strands of `λ`, at the left. -/
def prefixWindow : BlockEmb μL (stendhalWeight (ℓ + 2) (ν + ν₀)) (endSet ν ν₀) :=
  BlockEmb.window (endSet ν ν₀) 0 prefix_window_le prefix_window_labels prefix_window_stab

/-- The diagrams of `λ` with the colours of `λ⁺`. -/
def oldRelabel :
    SeqRelabel k (stendhalQ Q Λ) (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight ℓ ν) μL :=
  SeqRelabel.ofInjectiveOf (oldColour_injective ℓ le_rfl) _ _
    (fun a b _ => stendhalQ_oldColour Λ Λc ℓ le_rfl Q a b) _

/-- **A diagram of `λ` on the first `m` strands**, beside the identity on the strands at the
maximum. -/
def prefixMapKLR (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) : Rp :=
  ((prefixWindow ν ν₀).hom _ (relabelHom (oldRelabel Q Λ Λc ν) a)).val

/-- **A diagram at the maximum on the last `N` strands**, beside the identity on the strands of
`λ`. -/
def endMapKLR (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) : Rp :=
  ((endWindow ν ν₀).hom _
    (relabelHom (cupRelabel (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) k Q Λ Λc) x)).val

variable {Q Λ Λc ν ν₀} in
theorem prefixMapKLR_mul (a b : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    prefixMapKLR Q Λ Λc ν ν₀ (a * b) = prefixMapKLR Q Λ Λc ν ν₀ a * prefixMapKLR Q Λ Λc ν ν₀ b := by
  unfold prefixMapKLR; rw [map_mul, map_mul]; rfl

variable {Q Λ Λc ν ν₀} in
theorem endMapKLR_mul (x y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ (x * y) = endMapKLR Q Λ Λc ν ν₀ x * endMapKLR Q Λ Λc ν ν₀ y := by
  unfold endMapKLR; rw [map_mul, map_mul]; rfl

variable {Q Λ Λc ν ν₀} in
theorem endMapKLR_add (x y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ (x + y) = endMapKLR Q Λ Λc ν ν₀ x + endMapKLR Q Λ Λc ν ν₀ y := by
  unfold endMapKLR; rw [map_add, map_add]; rfl

theorem commute_prefixMapKLR_endMapKLR (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (prefixMapKLR Q Λ Λc ν ν₀ a) (endMapKLR Q Λ Λc ν ν₀ x) := by
  have h := BlockEmb.commute_hom (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (prefixWindow ν ν₀) (endWindow ν ν₀) (by
      change 0 + Multiset.card μL ≤ m
      rw [card_μL]; omega)
    (fun i l hl s => BlockEmb.window_F_sadj _ _ _ _ _ i (by
        have := end_window_le (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
        change m + l + 1 < M; omega)
      (Or.inr (by rw [card_μL]; omega))
      (end_window_stab l hl) s)
    (fun i l hl s => BlockEmb.window_F_sadj _ _ _ _ _ i (by
        have := prefix_window_le (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
        change 0 + l + 1 < M; omega)
      (Or.inl (by have := card_μL (I := I) (ℓ := ℓ) (ν := ν); change 0 + l + 1 < m; omega))
      (prefix_window_stab l hl) s)
    (relabelHom (oldRelabel Q Λ Λc ν) a)
    (relabelHom (cupRelabel (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) k Q Λ Λc) x)
  unfold Commute SemiconjBy prefixMapKLR endMapKLR
  rw [← Corner.val_mul, ← Corner.val_mul, h.eq]

variable {ν ν₀}

theorem prefixWindow_F (s : Seq (stendhalWeight ℓ ν)) :
    (prefixWindow ν ν₀).F (Seq.map (oldColour ℓ le_rfl) s) =
      insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl := by
  ext u
  simp only [prefixWindow, BlockEmb.window, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hl⟩
    obtain ⟨s', t, rfl⟩ := mem_endSet.1 hu
    have : s' = s := by
      apply Subtype.ext
      funext b
      have h1 := hl (Fin.cast (card_μL (I := I) (ℓ := ℓ) (ν := ν)).symm b)
      rw [show (insertSeq s' m le_rfl t).1 (windowPos 0 prefix_window_le
          (Fin.cast (card_μL (I := I) (ℓ := ℓ) (ν := ν)).symm b)) =
          oldColour ℓ le_rfl (s'.lbl b) from
        insertSeq_lbl_lt s' le_rfl t b b.2 (by simp [windowPos])] at h1
      exact oldColour_injective ℓ le_rfl h1
    subst this
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
  · intro hu
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨insertSeq_mem_endSet s t, fun a => ?_⟩
    have ha : a.val < m := card_μL (I := I) (ℓ := ℓ) (ν := ν) ▸ a.2
    exact insertSeq_lbl_lt s le_rfl t ⟨a.val, ha⟩ ha (by simp [windowPos])

theorem insertSet_inter_endWindow_F (s : Seq (stendhalWeight ℓ ν)) (t : Seq σ) :
    insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl ∩ (endWindow ν ν₀).F t =
      {insertSeq s m le_rfl t} := by
  ext u
  simp only [endWindow, BlockEmb.window, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hu, -, hl⟩
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    apply Subtype.ext
    funext b
    rw [← hl b]
    exact (insertSeq_lbl_win s le_rfl t' b rfl).symm
  · rintro rfl
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t), insertSeq_mem_endSet s t,
      fun b => insertSeq_lbl_win s le_rfl t b rfl⟩

theorem prefixMapKLR_e (s : Seq (stendhalWeight ℓ ν)) :
    prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) =
      KLRAlgebra.eSum _ (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl) := by
  rw [prefixMapKLR, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF]
  exact congrArg _ (prefixWindow_F s)

/-- **The diagrams at the maximum below the cap generators with the maximum at the right end**
are the diagrams at the maximum on the last `N` strands, cut by the loading of `λ`. -/
theorem insertMap_eq_prefix_mul_end (s : Seq (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    insertMap (j := ℓ) (hj := le_rfl) Q Λ Λc s m le_rfl x =
      prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) * endMapKLR Q Λ Λc ν ν₀ x := by
  have hE := prefixMapKLR_e Q Λ Λc (ν₀ := ν₀) s
  have hEE : (prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s)) *
      prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) = prefixMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) := by
    rw [← prefixMapKLR_mul, KLRAlgebra.e_mul_self]
  have hsub : insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl ⊆ endSet ν ν₀ := by
    intro u hu
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    exact insertSeq_mem_endSet s t
  induction x using KLRAlgebra.klr_induction with
  | hadd u v hu hv =>
    rw [insertMap_add, hu, hv, endMapKLR_add, mul_add]
  | hmul u v hu hv =>
    rw [insertMap_mul, hu, hv, endMapKLR_mul, mul_assoc, ← mul_assoc (endMapKLR _ _ _ _ _ u),
      ← (commute_prefixMapKLR_endMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e s) u).eq, ← mul_assoc,
      ← mul_assoc, hEE, mul_assoc]
  | hr c =>
    rw [insertMap_algebraMap, endMapKLR, AlgHom.commutes, AlgHom.commutes, Corner.val_algebraMap,
      hE, ← mul_assoc, ← Algebra.commutes, mul_assoc, KLRAlgebra.eSum_mul_eSum,
      Finset.inter_eq_left.2 hsub, Algebra.smul_def]
  | he w =>
    rw [insertMap_e, endMapKLR, relabelHom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hE,
      KLRAlgebra.eSum_mul_eSum, insertSet_inter_endWindow_F, KLRAlgebra.eSum,
      Finset.sum_singleton]
    rfl
  | hx b =>
    have hc := KLRAlgebra.pol_mul_eSum (Q := stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
      (MvPolynomial.X ((endWindow ν ν₀).pos (Fin.cast (cupRelabel (j := ℓ) (hj := le_rfl)
        (ν₀ := ν₀) k Q Λ Λc).card_eq b)))
      (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)
    rw [KLRAlgebra.pol_X] at hc
    rw [insertMap_x, endMapKLR, relabelHom_x, BlockEmb.hom_x, val_polCorner, pol_X, hE,
      ← mul_assoc, ← hc, mul_assoc, KLRAlgebra.eSum_mul_eSum, Finset.inter_eq_left.2 hsub]
    rfl
  | hψ p =>
    by_cases hp : p + 1 < N
    · rw [insertMap_ψ s le_rfl hp, endMapKLR, relabelHom_ψ, BlockEmb.hom_ψ,
        BlockEmb.val_gψ _ (by rw [card_σ]; exact hp), hE, ← mul_assoc]
      change _ = KLRAlgebra.eSum _ _ * KLRAlgebra.ψ (m + p) * _
      rw [eSum_insertSet_mul_ψ s le_rfl hp, mul_assoc, KLRAlgebra.eSum_mul_eSum,
        Finset.inter_eq_left.2 hsub]
    · rw [KLRAlgebra.ψ_eq_zero p (by omega), ← map_zero (algebraMap k _)]
      rw [insertMap_algebraMap, endMapKLR, AlgHom.commutes, AlgHom.commutes,
        Corner.val_algebraMap, hE, map_zero, zero_smul, zero_mul, mul_zero]

end EndBlock

end Categorification.Stendhal.CupCap
