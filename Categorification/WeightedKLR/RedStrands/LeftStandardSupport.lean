/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel
import Categorification.WeightedKLR.RedStrands.BraidedIdentity
import Categorification.TypeA.Inversions
import Categorification.WeightedKLR.RedStrands.StandardBlocks

/-!
# Loading support of left standards

Webster, arXiv:1309.3796v2, Definition 5.1 and the loading support used in the
proof of Lemma 6.11. A red-ordered loading outside the lower order ideal of a
standard label has a loading idempotent that annihilates that standard.

A colored black count increases at some red strand for such a loading. Each
wiring to it admits a choice of reduced word passing through a strictly
higher loading. Expanding in the PBW spanning diagrams for these word choices
puts the corresponding corner in the higher trace of the standard.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- Exchanging adjacent black strands preserves Webster’s black counts. -/
theorem blackCount_sadj_black_black (s : Seq μ) {j : ℕ} (hj : j + 1 < m)
    {i i' : I} (h₁ : s.lbl ⟨j, by omega⟩ = .inl i) (h₂ : s.lbl ⟨j + 1, hj⟩ = .inl i')
    (r : Fin ℓ) (c : I) :
    blackCount (sadj m j • s) r c = blackCount s r c := by
  rw [blackCount_sadj]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro ha
  refine forall_congr' fun b => imp_congr_right fun hb => ?_
  have hb0 : b.val ≠ j := fun e => by
    rw [lbl_eq_of_val s (b := ⟨j, by omega⟩) e, h₁] at hb
    cases hb
  have hb1 : b.val ≠ j + 1 := fun e => by
    rw [lbl_eq_of_val s (b := ⟨j+1, hj⟩) e, h₂] at hb
    cases hb
  change (sadj m j a).val < (sadj m j b).val ↔ a.val < b.val
  rw [sadj_apply_of_ne b hb0 hb1, sadj_apply_val hj]
  split_ifs <;> omega

omit [DecidableEq I] in
private theorem reduced_append_of_descent {w : Perm (Fin m)} {j : ℕ}
    (hj : j + 1 < m) {ρ : List ℕ} (hρ : IsReduced m ρ)
    (hw : wordProd m ρ = w * sadj m j)
    (hd : length m (w * sadj m j) + 1 = length m w) :
    IsReduced m (ρ ++ [j]) ∧ wordProd m (ρ ++ [j]) = w := by
  have hp : wordProd m (ρ ++ [j]) = w := by
    rw [wordProd_append, wordProd_singleton, hw, mul_assoc, TypeA.sadj_mul_self, mul_one]
  refine ⟨⟨validWord_append.2 ⟨hρ.1, validWord_cons.2 ⟨hj, validWord_nil m⟩⟩, ?_⟩, hp⟩
  rw [List.length_append, List.length_singleton, hρ.2, hw, hp, hd]

/-- A black strand whose destination is left of every strand in the interval up to a red strand
can start its reduced diagram by passing left through that interval. The diagram has an
intermediate loading strictly above its source in Webster's order. -/
theorem exists_reduced_suffix_raises_of_black (s : Seq μ) (hs : IsRedOrdered s)
    (w : Perm (Fin m)) {r b : Fin m} {d : Fin ℓ} {i : I}
    (hr : s.lbl r = .inr d) (hb : s.lbl b = .inl i) (hrb : r < b)
    (hinterval : ∀ c, r ≤ c → c < b → w b < w c) :
    ∃ u v : List ℕ, IsReduced m (u ++ v) ∧ wordProd m (u ++ v) = w ∧
      IsRedOrdered (wordProd m v • s) ∧ StendhalLT s (wordProd m v • s) := by
  induction hlen : length m w using Nat.strong_induction_on generalizing s w b with
  | h n ih =>
    have hval : r.val < b.val := hrb
    let j := b.val - 1
    have hj : j + 1 < m := by dsimp [j]; omega
    let a : Fin m := ⟨j, by omega⟩
    have hb' : (⟨j + 1, hj⟩ : Fin m) = b := Fin.ext (by dsimp [j]; omega)
    have hab : a < b := by change j < b.val; dsimp [j]; omega
    have hra : r ≤ a := by change r.val ≤ j; dsimp [j]; omega
    have hdesc := hinterval a hra hab
    have hdesc' : w ⟨j + 1, hj⟩ < w ⟨j, by omega⟩ := by rw [hb']; exact hdesc
    have hshort := length_mul_sadj_of_gt hj hdesc'
    have hswap : sadj m j a = b := (sadj_apply_left hj).trans hb'
    have ht := isRedOrdered_sadj hs hj (Or.inr (by
      change (s.lbl ⟨j + 1, hj⟩).isLeft
      rw [hb', hb]
      rfl))
    cases ha : s.lbl a with
    | inr e =>
      obtain ⟨u, hu, hw⟩ := exists_reduced m (w * sadj m j)
      have hred : s.lbl ⟨j, by omega⟩ = .inr e := ha
      have hblack : s.lbl ⟨j + 1, hj⟩ = .inl i := by rw [hb', hb]
      have hraise := stendhalLT_sadj hj hred hblack (fun c hc => lbl_eq_inr_unique hc hred)
      exact ⟨u, [j], (reduced_append_of_descent hj hu hw hshort).1,
        (reduced_append_of_descent hj hu hw hshort).2,
        by simpa only [wordProd_singleton] using ht,
        by simpa only [wordProd_singleton] using hraise⟩
    | inl i' =>
      have hra' : r < a := lt_of_le_of_ne hra (fun h => by rw [← h, hr] at ha; cases ha)
      have hfix (c : Fin m) (hc : c < a) : sadj m j c = c :=
        sadj_apply_of_ne c (by change c.val < j at hc; omega) (by change c.val < j at hc; omega)
      have hred : (sadj m j • s).lbl r = .inr d := by rw [lbl_sadj, hfix _ hra', hr]
      have hblack : (sadj m j • s).lbl a = .inl i := by rw [lbl_sadj, hswap, hb]
      have hs' : length m (w * sadj m j) < n := by omega
      have hi' : ∀ c, r ≤ c → c < a → (w * sadj m j) a < (w * sadj m j) c := by
        intro c hrc hca
        rw [Perm.mul_apply, Perm.mul_apply, hswap, hfix _ hca]
        exact hinterval c hrc (hca.trans hab)
      obtain ⟨u, v, huv, hw, hOrdered, hRaise⟩ :=
        ih _ hs' (sadj m j • s) ht (w * sadj m j) hred hblack hra' hi' rfl
      have h := reduced_append_of_descent hj huv hw hshort
      have hm : wordProd m (v ++ [j]) • s = wordProd m v • (sadj m j • s) := by
        rw [wordProd_append, wordProd_singleton, mul_smul]
      have hcount := fun r c => blackCount_sadj_black_black s hj ha
        (show s.lbl ⟨j + 1, hj⟩ = .inl i by rw [hb', hb]) r c
      refine ⟨u, v ++ [j], by simpa only [List.append_assoc] using h.1,
        by simpa only [List.append_assoc] using h.2, hm ▸ hOrdered, ?_⟩
      rw [hm]
      exact ⟨fun r c => (hcount r c) ▸ hRaise.1 r c,
        fun hle => hRaise.2 (fun r c => (hcount r c).symm ▸ hle r c)⟩

omit [DecidableEq I] in
private theorem lbl_perm_smul (w : Perm (Fin m)) (s : Seq μ) (a : Fin m) :
    (w • s).lbl a = s.lbl (w⁻¹ a) := rfl

private theorem blackCount_eq_filtered (s : Seq μ) (r : Fin ℓ) (i : I) :
    blackCount s r i =
      (Finset.univ.filter fun a => s.lbl a = .inl i ∧ a < redPos s r).card := by
  unfold blackCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro _
  exact ⟨fun h => h _ (lbl_redPos s r), fun h b hb => eq_redPos hb ▸ h⟩

private theorem exists_leftgoing_black (s : Seq μ) (w : Perm (Fin m)) (r : Fin ℓ) (i : I)
    (h : blackCount s r i < blackCount (w • s) r i) :
    ∃ b, redPos s r < b ∧ w b < w (redPos s r) := by
  classical
  have hrw : redPos (w • s) r = w (redPos s r) :=
    (eq_redPos (s := w • s) (by simp [lbl_redPos])).symm
  rw [blackCount_eq_filtered, blackCount_eq_filtered, hrw] at h
  let T := Finset.univ.filter fun b : Fin m => s.lbl b = .inl i ∧ w b < w (redPos s r)
  have hT : T.card = (Finset.univ.filter fun a => (w • s).lbl a = .inl i ∧
      a < w (redPos s r)).card := by
    refine Finset.card_bij (fun b _ => w b) ?_ (fun _ _ _ _ he => w.injective he) ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [lbl_perm_smul] using hb'⟩
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      exact ⟨w⁻¹ a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [lbl_perm_smul] using ha'⟩, by simp⟩
  rw [← hT] at h
  have hnot : ¬ T ⊆ (Finset.univ.filter fun a => s.lbl a = .inl i ∧ a < redPos s r) :=
    fun hsub => (Nat.not_le_of_lt h) (Finset.card_le_card hsub)
  obtain ⟨b, hb, hb'⟩ := Finset.not_subset.1 hnot
  have hbT := (Finset.mem_filter.mp hb).2
  have hn : ¬ b < redPos s r := fun hlt => hb' (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hbT.1, hlt⟩)
  have hn' : redPos s r ≠ b := fun he => by
    rw [← he, lbl_redPos] at hbT
    cases hbT.1
  exact ⟨b, lt_of_le_of_ne (le_of_not_gt hn) hn', hbT.2⟩

/-- For a fixed red order, any wiring to a loading outside the source's lower order ideal
has a reduced representative factoring through a strictly higher loading. -/
theorem exists_reduced_suffix_raises_of_not_stendhalLE (s : Seq μ) (hs : IsRedOrdered s)
    (w : Perm (Fin m)) (ht : IsRedOrdered (w • s)) (hn : ¬ StendhalLE (w • s) s) :
    ∃ u v : List ℕ, IsReduced m (u ++ v) ∧ wordProd m (u ++ v) = w ∧
      IsRedOrdered (wordProd m v • s) ∧ StendhalLT s (wordProd m v • s) := by
  classical
  simp only [StendhalLE, not_forall, not_le] at hn
  obtain ⟨r, i, hi⟩ := hn
  let a := redPos s r
  let B := Finset.univ.filter fun b : Fin m => a < b ∧ w b < w a
  have hB : B.Nonempty := by
    obtain ⟨b, hba, hbw⟩ := exists_leftgoing_black s w r i hi
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba, hbw⟩⟩
  let b := B.min' hB
  obtain ⟨hab, hba⟩ := (Finset.mem_filter.mp (Finset.min'_mem B hB)).2
  have hred (c : Fin m) (e : Fin ℓ) (hc : s.lbl c = .inr e) (hat : a < c) : w a < w c := by
    have hlt := hs a c r e hat (lbl_redPos s r) hc
    have hra : (w • s).lbl (w a) = .inr r := by simpa [a, lbl_perm_smul] using lbl_redPos s r
    have hrc : (w • s).lbl (w c) = .inr e := by simpa [lbl_perm_smul] using hc
    rw [eq_redPos hra, eq_redPos hrc]
    exact (redPos_lt_iff ht).2 hlt
  cases hb : s.lbl b with
  | inr e => exact (not_lt_of_gt (hred b e hb hab) hba).elim
  | inl j =>
    refine exists_reduced_suffix_raises_of_black s hs w (lbl_redPos s r) hb hab ?_
    intro c hac hcb
    rcases hac.lt_or_eq with hac' | rfl
    · have hnot : ¬ w c < w a := fun hw => by
        have hcB : c ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac', hw⟩
        exact (not_le_of_gt hcb) (Finset.min'_le B c hcB)
      exact hba.trans_le (le_of_not_gt hnot)
    · exact hba

section LeftStandardSupport

open BraidedStendhalAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "A" => TensorProductAlgebra k Q Λ ν

private theorem orderedCorner_mem_leftUpper_of_not_stendhalLE
    (s t : Seq μ) (hs : IsRedOrdered s) (ht : IsRedOrdered t) (hn : ¬ StendhalLE t s)
    (a : A) : seqIdem Q Λ t ht * a * seqIdem Q Λ s hs ∈ leftUpper Q Λ s hs := by
  classical
  have hw (w : Perm (Fin m)) :
      ∃ ρ : List ℕ, (IsReduced m ρ ∧ wordProd m ρ = w) ∧
        (w • s = t → ∃ u v, ρ = u ++ v ∧ IsRedOrdered (wordProd m v • s) ∧
          StendhalLT s (wordProd m v • s)) := by
    by_cases h : w • s = t
    · obtain ⟨u, v, huv, hp, hOrder, hRaise⟩ :=
        exists_reduced_suffix_raises_of_not_stendhalLE s hs w (h.symm ▸ ht) (h.symm ▸ hn)
      exact ⟨u ++ v, ⟨huv, hp⟩, fun _ => ⟨u, v, rfl, hOrder, hRaise⟩⟩
    · obtain ⟨ρ, hρ, hp⟩ := exists_reduced m w
      exact ⟨ρ, ⟨hρ, hp⟩, fun he => False.elim (h he)⟩
  let ρ := fun w => (hw w).choose
  have hρ w : IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := (hw w).choose_spec.1
  let π := StendhalAlgebraAllOrders.ofKLR k Q Λ ν
  let pr := orderProjection Q Λ ν
  let q := TensorProductAlgebra.mk Q Λ ν
  let F : R →ₐ[k] A := q.comp (pr.comp π)
  have hq : Function.Surjective q := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective
  have hF : Function.Surjective F :=
    hq.comp ((orderProjection_surjective Q Λ ν).comp StendhalAlgebraAllOrders.ofKLR_surjective)
  have hE (z : Seq μ) (hz : IsRedOrdered z) : F (e z) = seqIdem Q Λ z hz := by
    change q (pr (π (e z))) = q (StendhalAlgebra.e z hz)
    congr 1
    exact Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem z).trans (ite_eq_left hz))
  obtain ⟨x, rfl⟩ := hF a
  let f : R →ₗ[k] A := F.toLinearMap.comp
    (LinearMap.mulLeft k (e t) ∘ₗ LinearMap.mulRight k (e s))
  have hmem : x ∈ Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ) (ν := μ) ρ)) := by
    rw [KLRAlgebra.span_stdElt ρ hρ]
    exact Submodule.mem_top
  have hbound : Submodule.span k (Set.range (KLRAlgebra.stdElt (Q := stendhalQ Q Λ) (ν := μ) ρ)) ≤
      Submodule.comap f ((leftUpper Q Λ s hs).restrictScalars k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨j, w, p⟩, rfl⟩
    let g : R := ψw (ρ w) * pol (MvPolynomial.monomial p 1) * e j
    change F (e t * (g * e s)) ∈ leftUpper Q Λ s hs
    have hgR : g * e s = if j = s then g else 0 := by
      dsimp only [g]
      rw [mul_assoc, e_mul_e]
      split_ifs <;> simp
    by_cases hj : j = s
    · subst j
      rw [hgR, ite_eq_left rfl]
      have hgL : e (w • s) * g = g := by
        have h : e (wordProd m (ρ w) • s) * g = g := e_mul_std _ _ _
        rwa [(hρ w).2] at h
      by_cases hws : w • s = t
      · have hgt : e t * g = g := by rwa [hws] at hgL
        rw [hgt]
        obtain ⟨u, v, huv, hOrder, hRaise⟩ := (hw w).choose_spec.2 hws
        let c : Seq μ := wordProd m v • s
        let z : R := ψw v * pol (MvPolynomial.monomial p 1) * e s
        have hcut : e c * z = z := e_mul_std _ _ _
        have hfactor : g = ψw u * (e c * z) := by
          dsimp [g]
          rw [show ρ w = u ++ v from huv, hcut, ψw_append]
          simp [z, mul_assoc]
        have hgen : F (e c * z) ∈ leftUpper Q Λ s hs := by
          apply Submodule.subset_span
          refine ⟨c, hOrder, F (ψw v * pol (MvPolynomial.monomial p 1)), hRaise, ?_⟩
          rw [map_mul, hE c hOrder, show F z =
            F (ψw v * pol (MvPolynomial.monomial p 1)) * seqIdem Q Λ s hs by
              dsimp [z]; rw [map_mul, hE s hs], mul_assoc]
        rw [hfactor, map_mul]
        exact Submodule.smul_mem _ (F (ψw u)) hgen
      · rw [← hgL, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hws), zero_mul, map_zero]
        exact zero_mem _
    · rw [hgR, ite_eq_right hj, mul_zero, map_zero]
      exact zero_mem _
  have hx := hbound hmem
  change F (e t * (x * e s)) ∈ leftUpper Q Λ s hs at hx
  rwa [map_mul, map_mul, hE t ht, hE s hs, ← mul_assoc] at hx

/-- Webster, arXiv:1309.3796v2, §5.1 and the loading support used in Lemma 6.11.
A loading outside the lower order ideal of a standard label annihilates its left standard. -/
theorem seqIdem_smul_leftStandard_eq_zero_of_not_stendhalLE
    {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (hn : ¬ StendhalLE t s)
    (v : leftStandard Q Λ s hs) : seqIdem Q Λ t ht • v = 0 := by
  obtain ⟨a, rfl⟩ := leftStandard_exists_smul_unit s hs v
  rw [smul_smul, leftStandardUnit, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact orderedCorner_mem_leftUpper_of_not_stendhalLE s t hs ht hn a

end LeftStandardSupport


end Categorification.Stendhal
