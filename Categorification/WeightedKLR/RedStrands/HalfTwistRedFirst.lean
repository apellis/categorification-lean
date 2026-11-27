/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnPBW
import Categorification.WeightedKLR.RedStrands.RedShuffleFactor
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.BraidedIdentity

set_option backward.isDefEq.respectTransparency false

/-!
# The half twist factors through a red-first slice

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14: by Proposition 6.4, any nonzero diagram of `𝔅_τ P^κ_i` can be drawn with a slice
in the middle where all black strands are right of all red strands, so the map
`π : 𝔅_τ P⁰ → 𝔅_τ P^κ_i` induced by `θ_κ` is surjective.

Here `𝔅_τ P^κ_i` is the cut `e(t) V e_κ` of the violated quotient `V`, for a red-ordered top
loading `t` and a bottom red order `κ` in which every pair of red strands is reversed (for
instance `κ = (ℓ, …, 1)`). For a permutation `w` of the strands with `w • t' = t`, one of two
things happens.

* No black strand lies left of a red strand at both ends. Then `w = τ_t⁻¹ (τ_t w)` with lengths
  adding, where `τ_t` moves the red strands of `t` to the left (`redShufflePerm`), so the
  diagram is `θ_t` followed by a diagram from the red-first loading `τ_t • t`.
* Some black strand `B` lies left of a red strand `R` at both ends. Then `w` has a reduced word
  through a slice whose leftmost strand is black: the strands left of `B` at both ends, then `B`,
  then the rest, each group in its bottom order (`violPerm`). No red strand lies left of `B` at
  both ends, since it would cross `R` neither at the top nor at the bottom, so this slice is
  violated and the diagram vanishes in `V`.

Choosing reduced words accordingly (`halfTwistWord`), the basis of Proposition 6.4 shows
`e(t) V e_κ = θ_t · e(τ_t • t) V e_κ` (`violCorner_le_map_redShuffle`).

## Main results

* `isRedReversed_of_redWord_reverse`: the bottom red order `(ℓ, …, 1)` reverses all red pairs.
* `violPerm_cross`, `isViolated_violPerm`: the violated slice.
* `halfTwistWord_spec`: the adapted words are reduced.
* `violCorner_le_map_redShuffle`: `e(t) V e_κ = θ_t · e(τ_t • t) V e_κ`.
-/

noncomputable section

namespace Categorification.Stendhal

open Equiv KLR TypeA

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

section Combinatorics

/-- Every pair of red strands of `t` appears in decreasing order of labels. -/
def IsRedReversed (t : Seq μ) : Prop :=
  ∀ a b (r r' : Fin ℓ), a < b → t.lbl a = .inr r → t.lbl b = .inr r' → r' < r

omit [DecidableEq I] in
/-- The red order `(ℓ, …, 1)` reverses every pair of red strands. -/
theorem isRedReversed_of_redWord_reverse (t : Seq μ)
    (h : redWord t = (List.finRange ℓ).reverse) : IsRedReversed t := by
  have hord : IsRedOrdered (Seq.redPerm Fin.revPerm t) := by
    rw [← redWord_eq_finRange_iff, BraidedStendhalAlgebra.redWord_redPerm, h]
    apply List.ext_getElem (by simp)
    intro n h₁ h₂
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_finRange, Fin.revPerm_apply]
    ext
    simp only [List.length_map, List.length_reverse, List.length_finRange] at h₁
    simp [Fin.rev]
    omega
  intro a b r r' hab ha hb
  have := hord a b (Fin.rev r) (Fin.rev r') hab (by simp [ha]) (by simp [hb])
  exact Fin.rev_lt_rev.1 this

variable (w : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))))
  (B : Fin (Multiset.card (stendhalWeight ℓ ν)))

/-- The sorting key of the violated slice: the strands left of `B` at both ends, then `B`, then
the rest, each group in its bottom order. -/
def violKey (X : Fin m) : ℕ :=
  if X < B ∧ w⁻¹ X < w⁻¹ B then (w⁻¹ X).val else if X = B then m else m + 1 + (w⁻¹ X).val

omit [DecidableEq I] in
theorem violKey_injective : Function.Injective (violKey w B) := by
  intro X Y h
  unfold violKey at h
  have h₁ := (w⁻¹ X).isLt
  have h₂ := (w⁻¹ Y).isLt
  split_ifs at h with hX hY hY' hX' hY'' hY''' <;>
    first
    | exact w⁻¹.injective (Fin.ext h)
    | (subst_vars; rfl)
    | omega
    | exact w⁻¹.injective (Fin.ext (by omega))

/-- The permutation sorting the strands of the top loading into the violated slice. -/
def violPerm : Perm (Fin m) :=
  (exists_perm_lt_iff _ (violKey_injective w B)).choose

omit [DecidableEq I] in
theorem violPerm_lt_iff (X Y : Fin m) :
    violPerm w B X < violPerm w B Y ↔ violKey w B X < violKey w B Y :=
  (exists_perm_lt_iff _ (violKey_injective w B)).choose_spec X Y

omit [DecidableEq I] in
/-- Every pair reversed by `violPerm` is crossed by `w`. -/
theorem violPerm_cross : ∀ X Y, Y < X → violPerm w B X < violPerm w B Y → w⁻¹ X < w⁻¹ Y := by
  intro X Y hYX h
  rw [violPerm_lt_iff] at h
  unfold violKey at h
  have hXY : w⁻¹ X ≠ w⁻¹ Y := fun he => (ne_of_lt hYX) (w⁻¹.injective he).symm
  split_ifs at h with hX hY hY' hX' hY'' hY'''
  · exact Fin.lt_def.2 h
  · -- `X` left of `B` at both ends, `Y` the strand `B`
    subst hY'; exact absurd (lt_trans hYX hX.1) (lt_irrefl _)
  · -- `X` left of `B` at both ends, `Y` in the rest
    have hYB : Y < B := lt_trans hYX hX.1
    have : w⁻¹ B < w⁻¹ Y := by
      rcases lt_or_gt_of_ne (fun he : w⁻¹ Y = w⁻¹ B => hY' (w⁻¹.injective he)) with h' | h'
      · exact absurd ⟨hYB, h'⟩ hY
      · exact h'
    exact lt_trans hX.2 this
  · have := (w⁻¹ Y).isLt; omega
  · omega
  · -- `X = B`, `Y` in the rest
    subst hX'
    rcases lt_or_gt_of_ne hXY with h' | h'
    · exact h'
    · exact absurd ⟨hYX, h'⟩ hY''
  · have := (w⁻¹ Y).isLt; omega
  · omega
  · exact Fin.lt_def.2 (by omega)

omit [DecidableEq I] in
/-- The violated slice: if `B` is black and left of a red strand `R` at both ends, and all red
pairs of the red-ordered top loading `t` are reversed at the bottom `t'`, the leftmost strand of
`violPerm w B • t` is black. -/
theorem isViolated_violPerm {t t' : Seq μ} (hw : w • t' = t) (ht : IsRedOrdered t)
    (ht' : IsRedReversed t') {R : Fin m} (hB : (t.lbl B).isLeft) (hR : (t.lbl R).isRight)
    (hBR : B < R) (hBR' : w⁻¹ B < w⁻¹ R) : IsViolated (violPerm w B • t) := by
  have h0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) B.isLt
  refine ⟨h0, ?_⟩
  set Z := (violPerm w B).symm ⟨0, h0⟩ with hZ
  change (t.lbl Z).isLeft
  have hl : ∀ X, t.lbl X = t'.lbl (w⁻¹ X) := fun X => by rw [← hw]; rfl
  have hmin : violKey w B Z ≤ violKey w B B := by
    by_contra hlt
    push Not at hlt
    have := (violPerm_lt_iff w B B Z).2 hlt
    rw [hZ, Equiv.apply_symm_apply] at this
    exact absurd this (Nat.not_lt_zero _)
  by_cases hZB : Z = B
  · rw [hZB]; exact hB
  have hS : Z < B ∧ w⁻¹ Z < w⁻¹ B := by
    by_contra hS
    have hZk : violKey w B Z = m + 1 + (w⁻¹ Z).val := by
      unfold violKey; rw [ite_eq_right_of_eq_false _ _ (eq_false hS), ite_eq_right_of_eq_false _ _ (eq_false hZB)]
    have hBk : violKey w B B = m := by
      unfold violKey
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => lt_irrefl _ h.1)), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    omega
  cases hZl : t.lbl Z with
  | inl _ => rfl
  | inr r =>
    exfalso
    obtain ⟨r', hr'⟩ : ∃ r', t.lbl R = .inr r' := by
      cases hRl : t.lbl R with
      | inl _ => rw [hRl] at hR; simp at hR
      | inr r' => exact ⟨r', rfl⟩
    have hrr : r < r' := ht Z R r r' (lt_trans hS.1 hBR) hZl hr'
    have hZR : w⁻¹ Z < w⁻¹ R := lt_trans hS.2 hBR'
    have := ht' _ _ r r' hZR (by rw [← hl]; exact hZl) (by rw [← hl]; exact hr')
    exact absurd hrr (lt_asymm this)

omit [DecidableEq I] in
/-- If the red-first factorization fails, some black strand is left of a red strand at both
ends. -/
theorem exists_black_left_of_not_cross (t : Seq μ)
    (h : ¬ ∀ X Y, Y < X → redShufflePerm t X < redShufflePerm t Y → w⁻¹ X < w⁻¹ Y) :
    ∃ B R, (t.lbl B).isLeft ∧ (t.lbl R).isRight ∧ B < R ∧ w⁻¹ B < w⁻¹ R := by
  push Not at h
  obtain ⟨X, Y, hYX, hτ, hw⟩ := h
  have hne : w⁻¹ Y ≠ w⁻¹ X := fun he => (ne_of_lt hYX) (w⁻¹.injective he)
  have hw' : w⁻¹ Y < w⁻¹ X := lt_of_le_of_ne hw hne
  rw [redShufflePerm_lt_iff] at hτ
  cases hX : t.lbl X with
  | inl i =>
    rw [redShuffleKey_black (by rw [hX]; rfl)] at hτ
    cases hY : t.lbl Y with
    | inl j =>
      rw [redShuffleKey_black (by rw [hY]; rfl)] at hτ
      exact absurd (Fin.lt_def.2 (by omega)) (lt_asymm hYX)
    | inr r =>
      rw [redShuffleKey_red (by rw [hY]; rfl)] at hτ
      have := Y.isLt
      omega
  | inr r =>
    cases hY : t.lbl Y with
    | inl j => exact ⟨Y, X, by rw [hY]; rfl, by rw [hX]; rfl, hYX, hw'⟩
    | inr r' =>
      rw [redShuffleKey_red (by rw [hX]; rfl), redShuffleKey_red (by rw [hY]; rfl)] at hτ
      exact absurd (Fin.lt_def.2 hτ) (lt_asymm hYX)

/-- The violated-slice condition for `w` at the top loading `t`. -/
def HasBlackLeft (t : Seq μ) (w : Perm (Fin m)) : Prop :=
  ∃ B R, (t.lbl B).isLeft ∧ (t.lbl R).isRight ∧ B < R ∧ w⁻¹ B < w⁻¹ R

open Classical in
/-- Reduced words adapted to the half twist at the top loading `t`: through the red-first slice
`τ_t • t` when possible, otherwise through the violated slice. -/
def halfTwistWord (t : Seq μ) (w : Perm (Fin m)) : List ℕ :=
  if ∀ X Y, Y < X → redShufflePerm t X < redShufflePerm t Y → w⁻¹ X < w⁻¹ Y then
    canWord m (redShufflePerm t)⁻¹ ++ canWord m (redShufflePerm t * w)
  else if h : HasBlackLeft t w then
    canWord m (violPerm w h.choose)⁻¹ ++ canWord m (violPerm w h.choose * w)
  else canWord m w

omit [DecidableEq I] in
/-- A length-additive factorization `w = τ⁻¹ (τ w)` gives a reduced word. -/
theorem isReduced_factor (w τ : Perm (Fin m))
    (h : ∀ X Y, Y < X → τ X < τ Y → w⁻¹ X < w⁻¹ Y) :
    IsReduced m (canWord m τ⁻¹ ++ canWord m (τ * w)) ∧
      wordProd m (canWord m τ⁻¹ ++ canWord m (τ * w)) = w := by
  have hw : wordProd m (canWord m τ⁻¹ ++ canWord m (τ * w)) = w := by
    rw [wordProd_append, wordProd_canWord, wordProd_canWord, ← mul_assoc, inv_mul_cancel,
      one_mul]
  refine ⟨IsReduced.append_of_length_eq (isReduced_canWord _ _) (isReduced_canWord _ _) ?_, hw⟩
  rw [hw, wordProd_canWord, wordProd_canWord, length_inv]
  exact length_eq_add_of_cross w _ h

omit [DecidableEq I] in
theorem halfTwistWord_spec (t : Seq μ) : IsReducedChoice (halfTwistWord (ν := ν) t) := by
  intro w
  unfold halfTwistWord
  split_ifs with h _
  · exact isReduced_factor w _ h
  · exact isReduced_factor w _ (violPerm_cross w _)
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

end Combinatorics

namespace BraidedStendhalAlgebra

open KLRAlgebra

variable {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ}

local notation "ι" => ofKLR k Q Λ ν

/-- The red/black shuffle `θ_t ∈ e(t) V e(τ_t • t)` in the violated quotient. -/
def violShuffle (t : Seq μ) : ViolQuotient k Q Λ ν :=
  violMk k Q Λ ν (ι (KLRAlgebra.e t * ψw (canWord m (redShufflePerm t)⁻¹) *
    KLRAlgebra.e (redShufflePerm t • t)))

/-- A diagram factoring through a middle idempotent. -/
private theorem violMk_basis_factor (hQ : KLRSymm Q) (t : Seq μ) (κ : List (Fin ℓ))
    (b : BlackIdx (ℓ := ℓ) ν) (htop : b.1.2.1 • b.1.1 = t) (hbot : redWord b.1.1 = κ)
    (τ : Perm (Fin m)) (hc : ∀ X Y, Y < X → τ X < τ Y → b.1.2.1⁻¹ X < b.1.2.1⁻¹ Y)
    (hword : halfTwistWord t b.1.2.1 = canWord m τ⁻¹ ++ canWord m (τ * b.1.2.1)) :
    violMk k Q Λ ν (basis (Λ := Λ) hQ (halfTwistWord t) (halfTwistWord_spec t) b) =
      violMk k Q Λ ν (ι (KLRAlgebra.e t * ψw (canWord m τ⁻¹) * KLRAlgebra.e (τ • t))) *
        violMk k Q Λ ν (ι (KLRAlgebra.e (τ • t)) *
          ι (ψw (canWord m (τ * b.1.2.1)) * pol (MvPolynomial.monomial b.1.2.2 1) *
            KLRAlgebra.e b.1.1) * redProj k Q Λ ν κ) := by
  have _ := hc
  have hr : (ψw (canWord m (τ * b.1.2.1)) * pol (MvPolynomial.monomial b.1.2.2 1) *
      KLRAlgebra.e b.1.1 : KLRAlgebra k (stendhalQ Q Λ) μ) * redIdem k Q Λ κ =
      ψw (canWord m (τ * b.1.2.1)) * pol (MvPolynomial.monomial b.1.2.2 1) *
        KLRAlgebra.e b.1.1 := by
    rw [mul_assoc, e_mul_redIdem, ite_eq_left_of_eq_true _ _ (eq_true hbot)]
  have hg := KLRAlgebra.e_ψw_e_mul_e_gen Q Λ (canWord m τ⁻¹) (canWord m (τ * b.1.2.1))
    (MvPolynomial.monomial b.1.2.2 1) t (τ • t) b.1.1 (by rw [wordProd_canWord, inv_inv])
    (by rw [wordProd_canWord, mul_inv_rev, mul_smul, inv_smul_smul,
      inv_smul_eq_iff.mpr htop.symm])
  have key : (ψw (canWord m τ⁻¹ ++ canWord m (τ * b.1.2.1)) *
      pol (MvPolynomial.monomial b.1.2.2 1) * KLRAlgebra.e b.1.1 :
        KLRAlgebra k (stendhalQ Q Λ) μ) =
      (KLRAlgebra.e t * ψw (canWord m τ⁻¹) * KLRAlgebra.e (τ • t)) *
        (KLRAlgebra.e (τ • t) * (ψw (canWord m (τ * b.1.2.1)) *
          pol (MvPolynomial.monomial b.1.2.2 1) * KLRAlgebra.e b.1.1) * redIdem k Q Λ κ) := by
    rw [mul_assoc (KLRAlgebra.e (τ • t)), hr, ← hg]
    simp only [mul_assoc]
  rw [basis_apply, hword, key]
  simp only [map_mul, redProj, mul_assoc]

/-- **The half twist factors through the red-first slice** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): for a red-ordered top loading `t` and a bottom red order `κ` reversing every red
pair, every element of `e(t) V e_κ` is `θ_t y` with `y ∈ e(τ_t • t) V e_κ`, where `τ_t • t` is
the red-first loading of `t`. -/
theorem violCorner_le_map_redShuffle (hQ : KLRSymm Q) (t : Seq μ) (ht : IsRedOrdered t)
    (κ : List (Fin ℓ)) (hκ : ∀ t' : Seq μ, redWord t' = κ → IsRedReversed t') :
    violCorner k Q Λ ν t κ ≤ (violCorner k Q Λ ν (redShufflePerm t • t) κ).map
      (LinearMap.mulLeft k (violShuffle (k := k) (Q := Q) (Λ := Λ) (ν := ν) t)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Submodule.span k (Set.range (basis (Λ := Λ) hQ (halfTwistWord t)
      (halfTwistWord_spec t))) := by
    rw [Module.Basis.span_eq]; trivial
  induction ha using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
    rw [basis_mul_redProj hQ _ (halfTwistWord_spec t)]
    split_ifs with hbot
    swap
    · simp
    rw [e_mul_basis hQ _ (halfTwistWord_spec t)]
    split_ifs with htop
    swap
    · simp
    set w := b.1.2.1
    have hrev := hκ _ hbot
    by_cases hcross : ∀ X Y, Y < X → redShufflePerm t X < redShufflePerm t Y → w⁻¹ X < w⁻¹ Y
    · have hword : halfTwistWord t w =
          canWord m (redShufflePerm t)⁻¹ ++ canWord m (redShufflePerm t * w) := by
        unfold halfTwistWord; rw [ite_eq_left_of_eq_true _ _ (eq_true hcross)]
      rw [violMk_basis_factor hQ t κ b htop hbot _ hcross hword]
      refine ⟨_, ⟨ι (ψw (canWord m (redShufflePerm t * w)) *
        pol (MvPolynomial.monomial b.1.2.2 1) * KLRAlgebra.e b.1.1), rfl⟩, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, violShuffle, mul_assoc]
      rfl
    · have hB : HasBlackLeft t w := exists_black_left_of_not_cross w t hcross
      set B := hB.choose
      have hword : halfTwistWord t w = canWord m (violPerm w B)⁻¹ ++
          canWord m (violPerm w B * w) := by
        unfold halfTwistWord; rw [ite_eq_right_of_eq_false _ _ (eq_false hcross), dite_eq_left_of_eq_true (eq_true hB)]
      obtain ⟨R, hBl, hRr, hBR, hBR'⟩ := hB.choose_spec
      rw [violMk_basis_factor hQ t κ b htop hbot _ (violPerm_cross w B) hword]
      have hv := isViolated_violPerm w B htop ht hrev hBl hRr hBR hBR'
      have h0 : violMk k Q Λ ν (ι (KLRAlgebra.e t * ψw (canWord m (violPerm w B)⁻¹) *
          KLRAlgebra.e (violPerm w B • t))) = 0 := by
        rw [map_mul, map_mul, violMk_e hv, mul_zero]
      rw [h0, zero_mul]
      exact Submodule.zero_mem _

end BraidedStendhalAlgebra

end Categorification.Stendhal
