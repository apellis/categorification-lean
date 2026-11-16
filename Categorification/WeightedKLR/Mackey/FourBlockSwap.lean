/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockChamber

/-!
# The middle swap of a juxtaposition of four chambers

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. For chambers `A, B, C, D` of `a, b, c, d`, moving the strands of
the blocks `a` and `c` of `(A B)(C D)` to the left and then relabelling by `middleSwap a b c d`
gives the juxtaposition `(A C)(B D)`, read in `(a + b) + (c + d)`.

## Main definitions

* `Juxtapose.middleLeft a b c d`: the strands of the blocks `a` and `c`, as the set
  `blockLeft (a + b) (a + c) c` of strands sent into the first block by a shuffle of type `c`.

## Main results

* `Juxtapose.middleSwap_smul_shuffleTop`: `middleSwap • shuffleTop (middleLeft) (A B)(C D)` is
  `(A C)(B D)`.
-/

namespace Categorification.WeightedKLR

open FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace FullChamber

omit [DecidableEq I] in
/-- Relabelling by `g` a chamber separated by `W` gives a chamber separated by any `Y` with
`W = Y ∘ g`. -/
theorem IsSeparated.smul_of {ν : I →₀ ℕ} {W Y : Strand ν → Bool} {D : FullChamber Γ ν}
    (hD : IsSeparated W D) (g : ColPerm ν) (hW : ∀ s, W s = Y (g.1 s)) :
    IsSeparated Y (g • D) := by
  have h := hD.smul g
  have e : (fun t => W (g.1⁻¹ t)) = Y := funext fun t => by
    rw [hW]
    congr 1
    simp
  rwa [e] at h

end FullChamber

namespace StrandEmbedding

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem restrict_restrict {ν₁ ν₂ ν : I →₀ ℕ} (j : StrandEmbedding ν₁ ν₂)
    (j' : StrandEmbedding ν₂ ν) (C : FullChamber Γ ν) :
    j.restrict (j'.restrict C) = (j.comp j').restrict C := by
  refine Subtype.ext (funext fun h => ?_)
  rw [restrict_apply, restrict_apply, restrict_apply, hyp_comp]

end StrandEmbedding

namespace Juxtapose

variable (a b c d : I →₀ ℕ)

/-- The strands of the blocks `a` and `c` of `(a + b) + (c + d)`. -/
noncomputable abbrev middleLeft : Strand (a + b + (c + d)) → Bool := blockLeft (a + b) (a + c) ⇑c

omit [DecidableEq I] in
theorem middleRank_lt_add_iff (n p q r : ℕ) :
    (if r < n + p then decide (r < n + q - q) else decide (r < n + p + q)) =
      decide (middleRank n p q r < n + q) := by
  unfold middleRank
  split_ifs <;> simp only [decide_eq_decide] <;> omega

omit [DecidableEq I] in
theorem middleRank_lt_iff (n p q r : ℕ) :
    (decide (r < n + p) &&
        if r < n + p then decide (r < n + q - q) else decide (r < n + p + q)) =
      decide (middleRank n p q r < n) := by
  unfold middleRank
  by_cases h₁ : r < n <;> by_cases h₂ : r < n + p <;> by_cases h₃ : r < n + p + q <;>
    simp [h₁, h₂, h₃] <;> omega

omit [DecidableEq I] in
theorem middleRank_lt_add_add_iff (n p q r : ℕ) :
    (decide (r < n + p) ||
        if r < n + p then decide (r < n + q - q) else decide (r < n + p + q)) =
      decide (middleRank n p q r < n + q + p) := by
  unfold middleRank
  by_cases h₁ : r < n <;> by_cases h₂ : r < n + p <;> by_cases h₃ : r < n + p + q <;>
    simp [h₁, h₂, h₃] <;> omega

omit [DecidableEq I] in
/-- The strands of the blocks `a` and `c` are those sent by the middle swap below `a + c`. -/
theorem middleLeft_eq (t : Strand (a + b + (c + d))) :
    middleLeft a b c d t =
      decide ((((middleSwap a b c d).1 t).2.val) < a t.1 + c t.1) := by
  rw [middleSwap_apply]
  exact middleRank_lt_add_iff _ _ _ _

omit [DecidableEq I] in
/-- The strands of the block `a` are those sent by the middle swap below `a`. -/
theorem isLeft_and_middleLeft (t : Strand (a + b + (c + d))) :
    (decide (t.IsLeft (a + b)) && middleLeft a b c d t) =
      decide ((((middleSwap a b c d).1 t).2.val) < a t.1) := by
  rw [middleSwap_apply]
  exact middleRank_lt_iff _ _ _ _

omit [DecidableEq I] in
/-- The strands of the blocks `a`, `b`, `c` are those sent by the middle swap below
`a + c + b`. -/
theorem isLeft_or_middleLeft (t : Strand (a + b + (c + d))) :
    (decide (t.IsLeft (a + b)) || middleLeft a b c d t) =
      decide ((((middleSwap a b c d).1 t).2.val) < a t.1 + c t.1 + b t.1) := by
  rw [middleSwap_apply]
  exact middleRank_lt_add_add_iff _ _ _ _

omit [DecidableEq I] in
theorem middleLeft_of_eq_castStrand {t : Strand (a + b + (c + d))} {u : Strand (a + c + (b + d))}
    (hs : (middleSwap a b c d).1 t = castStrand (layout_eq a b c d) u) :
    middleLeft a b c d t = decide (u.2.val < a u.1 + c u.1) := by
  have hc : (t.1 : I) = u.1 := by
    rw [← castStrand_colour (layout_eq a b c d) u, ← hs]
    rfl
  rw [middleLeft_eq, hs, castStrand_rank, hc]

omit [DecidableEq I] in
/-- On a block on which `middleLeft` is constant and which the middle swap carries to the block
`J` of `(a + c) + (b + d)`, the relabelled shuffle reads the values of the juxtaposition. -/
theorem restrict_middleSwap_smul_shuffleTop {ν₁ : I →₀ ℕ}
    (J j' : StrandEmbedding ν₁ (a + b + (c + d)))
    (hρ : ∀ s, J s = (middleSwap a b c d).1 (j' s)) {z : Bool}
    (hZ : ∀ s, middleLeft a b c d (j' s) = z)
    (E : FullChamber Γ (a + b + (c + d))) (x : Hyp Γ ν₁) :
    (J.restrict (middleSwap a b c d • shuffleTop (middleLeft a b c d) E)).1 x =
      E.1 (j'.hyp x) := by
  rw [StrandEmbedding.restrict_apply, StrandEmbedding.smul_apply_hyp (j := j') hρ,
    StrandEmbedding.shuffleTop_apply_hyp fun s s' => (hZ s).trans (hZ s').symm]

omit [DecidableEq I] in
/-- **The middle swap of a juxtaposition of four chambers.** Moving the strands of the blocks
`a` and `c` of `(A B)(C D)` to the left and relabelling by `middleSwap a b c d` gives
`(A C)(B D)`, read in `(a + b) + (c + d)`. -/
theorem middleSwap_smul_shuffleTop (A : FullChamber Γ a) (B : FullChamber Γ b)
    (C : FullChamber Γ c) (D : FullChamber Γ d) :
    middleSwap a b c d • shuffleTop (middleLeft a b c d) (chamber (chamber A B) (chamber C D)) =
      castChamber (layout_eq a b c d) (chamber (chamber A C) (chamber B D)) := by
  have hE : IsSeparated (fun t => decide (t.IsLeft (a + b)))
      (chamber (chamber A B) (chamber C D)) := isSeparated_chamber _ _
  have h₁ : IsSeparated (fun t => decide (t.2.val < a t.1))
      (middleSwap a b c d • shuffleTop (middleLeft a b c d)
        (chamber (chamber A B) (chamber C D))) :=
    (isSeparated_shuffleTop_and hE).smul_of _ (isLeft_and_middleLeft a b c d)
  have h₂ : IsSeparated (fun t => decide (t.2.val < a t.1 + c t.1))
      (middleSwap a b c d • shuffleTop (middleLeft a b c d)
        (chamber (chamber A B) (chamber C D))) :=
    (isSeparated_sep (middleLeft a b c d) _ _).smul_of _ (middleLeft_eq a b c d)
  have h₃ : IsSeparated (fun t => decide (t.2.val < a t.1 + c t.1 + b t.1))
      (middleSwap a b c d • shuffleTop (middleLeft a b c d)
        (chamber (chamber A B) (chamber C D))) :=
    (isSeparated_shuffleTop_or hE).smul_of _ (isLeft_or_middleLeft a b c d)
  rw [← castChamber_castChamber (layout_eq a b c d) (middleSwap a b c d • _)]
  refine congrArg (castChamber (layout_eq a b c d)) ?_
  rw [castChamber_eq_restrict (layout_eq a b c d)]
  have hcast : ∀ (f : Strand (a + b + (c + d)) → Bool) (g : I → ℕ),
      (∀ t, f t = decide (t.2.val < g t.1)) → ∀ s : Strand (a + c + (b + d)),
        f (castStrandEmb (layout_eq a b c d) s) = decide (s.2.val < g s.1) := by
    intro f g hf s
    rw [hf, castStrandEmb_apply, castStrand_rank, castStrand_colour]
  have hR₁ := StrandEmbedding.isSeparated_restrict h₁ (hcast _ (fun i => a i) fun _ => rfl)
  have hR₂ := StrandEmbedding.isSeparated_restrict h₂
    (hcast _ (fun i => a i + c i) fun _ => rfl)
  have hR₃ := StrandEmbedding.isSeparated_restrict h₃
    (hcast _ (fun i => a i + c i + b i) fun _ => rfl)
  rw [eq_chamber_of_isSeparated hR₂]
  have hL := StrandEmbedding.isSeparated_restrict (j := leftEmb (a + c) (b + d))
    (X := fun s => decide (s.IsLeft a)) hR₁ fun _ => rfl
  have hRt := StrandEmbedding.isSeparated_restrict (j := rightEmb (a + c) (b + d))
    (X := fun s => decide (s.IsLeft b)) hR₃ fun s => by
      simp only [decide_eq_decide]
      show a s.1 + c s.1 + s.2.val < a s.1 + c s.1 + b s.1 ↔ s.2.val < b s.1
      omega
  rw [eq_chamber_of_isSeparated hL, eq_chamber_of_isSeparated hRt]
  simp only [StrandEmbedding.restrict_restrict]
  congr 2 <;> refine Subtype.ext (funext fun x => ?_)
  · rw [restrict_middleSwap_smul_shuffleTop a b c d _
      ((leftEmb a b).comp (leftEmb (a + b) (c + d)))
      (fun s => (middleSwap_inl_inl a b c d s).symm)
      (fun s => (middleLeft_of_eq_castStrand a b c d (middleSwap_inl_inl a b c d s)).trans
        (decide_eq_true (by show s.2.val < a s.1 + c s.1; have := s.2.2; omega))),
      StrandEmbedding.hyp_comp, chamber_left, chamber_left]
  · rw [restrict_middleSwap_smul_shuffleTop a b c d _
      ((leftEmb c d).comp (rightEmb (a + b) (c + d)))
      (fun s => (middleSwap_inr_inl a b c d s).symm)
      (fun s => (middleLeft_of_eq_castStrand a b c d (middleSwap_inr_inl a b c d s)).trans
        (decide_eq_true (by show a s.1 + s.2.val < a s.1 + c s.1; have := s.2.2; omega))),
      StrandEmbedding.hyp_comp, chamber_right, chamber_left]
  · rw [restrict_middleSwap_smul_shuffleTop a b c d _
      ((rightEmb a b).comp (leftEmb (a + b) (c + d)))
      (fun s => (middleSwap_inl_inr a b c d s).symm)
      (fun s => (middleLeft_of_eq_castStrand a b c d (middleSwap_inl_inr a b c d s)).trans
        (decide_eq_false (by show ¬ a s.1 + c s.1 + s.2.val < a s.1 + c s.1; omega))),
      StrandEmbedding.hyp_comp, chamber_left, chamber_right]
  · rw [restrict_middleSwap_smul_shuffleTop a b c d _
      ((rightEmb c d).comp (rightEmb (a + b) (c + d)))
      (fun s => (middleSwap_inr_inr a b c d s).symm)
      (fun s => (middleLeft_of_eq_castStrand a b c d (middleSwap_inr_inr a b c d s)).trans
        (decide_eq_false
          (by show ¬ a s.1 + c s.1 + (b s.1 + s.2.val) < a s.1 + c s.1; omega))),
      StrandEmbedding.hyp_comp, chamber_right, chamber_right]

end Juxtapose

end Categorification.WeightedKLR
