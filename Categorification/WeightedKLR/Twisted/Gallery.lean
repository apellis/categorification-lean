/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Algebra
import Categorification.WeightedKLR.Gallery

/-!
# Galleries of words in the twisted gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.20
(the basis, whose proof is that of Theorem 2.8).

The step filtration and galleries of words of `Gallery.lean`, read on the arrangement of
positions and weights: a word `w` of hyperplanes, read from a chamber `C`, gives the gallery
`galList C w`, and reversing the hyperplanes through a codimension-two flat changes a gallery
by an element of lower filtration.

## Main definitions

* `TwChamber.flipH C h`: the chamber obtained from `C` by crossing `h` (or `C` itself).
* `TwChamber.flips C w`: the end of the gallery of `w` from `C`.
* `TwGalleryAlgebra.galList C w`: the gallery of `w` from `C`.
* `TwGalleryAlgebra.stepFilt n`: the step filtration.
-/

namespace Categorification.WeightedKLR

open MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace TwChamber

open FullChamber (flipSign)

open Classical in
/-- The full chamber obtained from `C` by crossing `h`; `C` itself if there is none. -/
noncomputable def flipH (C : TwChamber Γ ν) (h : Hyp Γ ν) : TwChamber Γ ν :=
  if hr : ∃ p, TwGeneric Γ p ∧ twSigns p = FullChamber.flipSign C.1 h then
    (⟨FullChamber.flipSign C.1 h, hr⟩ : TwChamber Γ ν) else C

omit [IsStrictOrderedRing 𝕜] in
theorem flipH_of {C : TwChamber Γ ν} {h : Hyp Γ ν}
    (hr : ∃ p, TwGeneric Γ p ∧ twSigns p = FullChamber.flipSign C.1 h) :
    C.flipH h = ⟨FullChamber.flipSign C.1 h, hr⟩ :=
  dite_eq_left_of_eq_true (eq_true hr)

omit [IsStrictOrderedRing 𝕜] in
theorem adjacent_iff_eq_flipSign {C C' : TwChamber Γ ν} {h : Hyp Γ ν} :
    C.Adjacent C' h ↔ C'.1 = FullChamber.flipSign C.1 h := by
  constructor
  · rintro ⟨h1, h2⟩
    funext x
    by_cases e : x = h
    · subst e
      simp only [FullChamber.flipSign, decide_true, Bool.xor_true]
      generalize C.1 x = u at h1
      generalize C'.1 x = u' at h1
      cases u <;> cases u' <;> simp_all
    · simp [FullChamber.flipSign, e, h2 x e]
  · intro e
    refine ⟨?_, fun x hx => ?_⟩
    · rw [e]; simp [FullChamber.flipSign]
    · rw [e]; simp [FullChamber.flipSign, hx]

omit [IsStrictOrderedRing 𝕜] in
theorem flipH_eq_of_adjacent {C C' : TwChamber Γ ν} {h : Hyp Γ ν} (hC : C.Adjacent C' h) :
    C.flipH h = C' := by
  have e := adjacent_iff_eq_flipSign.1 hC
  have hr : ∃ p, TwGeneric Γ p ∧ twSigns p = FullChamber.flipSign C.1 h := e ▸ C'.2
  rw [flipH_of hr]
  exact Subtype.ext e.symm

omit [IsStrictOrderedRing 𝕜] in
theorem adjacent_flipH_of_adjacent {C C' : TwChamber Γ ν} {h : Hyp Γ ν}
    (hC : C.Adjacent C' h) : C.Adjacent (C.flipH h) h := by
  rwa [flipH_eq_of_adjacent hC]

/-- The end of the gallery of the word `w` from `C`. -/
noncomputable def flips (C : TwChamber Γ ν) : List (Hyp Γ ν) → TwChamber Γ ν
  | [] => C
  | h :: w => flips (C.flipH h) w

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem flips_nil (C : TwChamber Γ ν) : C.flips [] = C := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem flips_cons (C : TwChamber Γ ν) (h : Hyp Γ ν) (w : List (Hyp Γ ν)) :
    C.flips (h :: w) = (C.flipH h).flips w := rfl

omit [IsStrictOrderedRing 𝕜] in
theorem flips_append (C : TwChamber Γ ν) (a b : List (Hyp Γ ν)) :
    C.flips (a ++ b) = (C.flips a).flips b := by
  induction a generalizing C with
  | nil => rfl
  | cons h a ih => exact ih _

end TwChamber

namespace TwGalleryAlgebra

open TwChamber

theorem t_eq (C C' : TwChamber Γ ν) :
    (t C C' : TwGalleryAlgebra k Γ ν) = e C' * t C C' * e C := by
  have := rel (TwGalRel.step_idem (k := k) C C')
  rw [map_mul, map_mul] at this
  exact this

theorem t_mul_e (C C' : TwChamber Γ ν) : (t C C' * e C : TwGalleryAlgebra k Γ ν) = t C C' := by
  conv_lhs => rw [t_eq, mul_assoc, e_mul_e, ite_eq_left rfl]
  rw [← t_eq]

theorem e_mul_t (C C' : TwChamber Γ ν) : (e C' * t C C' : TwGalleryAlgebra k Γ ν) = t C C' := by
  conv_lhs => rw [t_eq, ← mul_assoc, ← mul_assoc, e_mul_e, ite_eq_left rfl]
  rw [← t_eq]

theorem t_eq_zero {C C' : TwChamber Γ ν} (h : ∀ h : Hyp Γ ν, ¬C.Adjacent C' h) :
    (t C C' : TwGalleryAlgebra k Γ ν) = 0 := by
  have := rel (TwGalRel.step_zero (k := k) C C' h)
  rw [map_zero] at this
  exact this

variable (k) in
/-- The gallery of the word `w` from `C`: the steps across the hyperplanes of `w` in turn,
the first step rightmost. -/
noncomputable def galList : TwChamber Γ ν → List (Hyp Γ ν) → TwGalleryAlgebra k Γ ν
  | C, [] => e C
  | C, h :: w => galList (C.flipH h) w * t C (C.flipH h)

@[simp] theorem galList_nil (C : TwChamber Γ ν) : galList k C [] = e C := rfl

@[simp] theorem galList_cons (C : TwChamber Γ ν) (h : Hyp Γ ν) (w : List (Hyp Γ ν)) :
    galList k C (h :: w) = galList k (C.flipH h) w * t C (C.flipH h) := rfl

theorem galList_mul_e (C : TwChamber Γ ν) (w : List (Hyp Γ ν)) :
    galList k C w * e C = galList k C w := by
  cases w with
  | nil => rw [galList_nil, e_mul_e, ite_eq_left rfl]
  | cons h w => rw [galList_cons, mul_assoc, t_mul_e]

theorem e_mul_galList (C : TwChamber Γ ν) (w : List (Hyp Γ ν)) :
    e (C.flips w) * galList k C w = galList k C w := by
  induction w generalizing C with
  | nil => rw [galList_nil, flips_nil, e_mul_e, ite_eq_left rfl]
  | cons h w ih => rw [galList_cons, flips_cons, ← mul_assoc, ih]

theorem galList_append (C : TwChamber Γ ν) (a b : List (Hyp Γ ν)) :
    galList k C (a ++ b) = galList k (C.flips a) b * galList k C a := by
  induction a generalizing C with
  | nil => rw [List.nil_append, flips_nil, galList_nil, galList_mul_e]
  | cons h a ih => rw [List.cons_append, galList_cons, ih, galList_cons, flips_cons, mul_assoc]

/-! ### The step filtration -/

/-- The number of steps in a generator. -/
def TwGen.stepCount : TwGen k Γ ν → ℕ
  | .step _ _ => 1
  | _ => 0

variable (k Γ ν) in
/-- The product of a list of generators. -/
noncomputable def wordVal (l : List (TwGen k Γ ν)) : TwGalleryAlgebra k Γ ν :=
  (l.map fun g => mk k Γ ν (FreeAlgebra.ι k g)).prod

variable (k Γ ν) in
/-- The step filtration: the span of the products of generators with at most `n` steps. -/
noncomputable def stepFilt (n : ℕ) : Submodule k (TwGalleryAlgebra k Γ ν) :=
  Submodule.span k
    {x | ∃ l : List (TwGen k Γ ν), (l.map TwGen.stepCount).sum ≤ n ∧ wordVal k Γ ν l = x}

theorem stepFilt_mono {m n : ℕ} (h : m ≤ n) : stepFilt k Γ ν m ≤ stepFilt k Γ ν n :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem gen_mem_stepFilt (g : TwGen k Γ ν) :
    mk k Γ ν (FreeAlgebra.ι k g) ∈ stepFilt k Γ ν (TwGen.stepCount g) :=
  Submodule.subset_span ⟨[g], by simp, by simp [wordVal]⟩

theorem one_mem_stepFilt (n : ℕ) : (1 : TwGalleryAlgebra k Γ ν) ∈ stepFilt k Γ ν n :=
  Submodule.subset_span ⟨[], by simp, by simp [wordVal]⟩

theorem mul_mem_stepFilt {m n : ℕ} {x y : TwGalleryAlgebra k Γ ν} (hx : x ∈ stepFilt k Γ ν m)
    (hy : y ∈ stepFilt k Γ ν n) : x * y ∈ stepFilt k Γ ν (m + n) := by
  have : stepFilt k Γ ν m * stepFilt k Γ ν n ≤ stepFilt k Γ ν (m + n) := by
    rw [stepFilt, stepFilt, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, rfl⟩
    exact ⟨l ++ l', by simp only [List.map_append, List.sum_append]; omega,
      by simp [wordVal]⟩
  exact this (Submodule.mul_mem_mul hx hy)

theorem e_mem_stepFilt (C : TwChamber Γ ν) (n : ℕ) : (e C : TwGalleryAlgebra k Γ ν) ∈
    stepFilt k Γ ν n :=
  stepFilt_mono (Nat.zero_le n) (gen_mem_stepFilt (.idem C))

theorem poly_mem_stepFilt (f : PolyRing ν k) (n : ℕ) : (poly f : TwGalleryAlgebra k Γ ν) ∈
    stepFilt k Γ ν n :=
  stepFilt_mono (Nat.zero_le n) (gen_mem_stepFilt (.poly f))

theorem r_mem_stepFilt (g : ColPerm ν) (C : TwChamber Γ ν) (n : ℕ) :
    (r g C : TwGalleryAlgebra k Γ ν) ∈ stepFilt k Γ ν n :=
  stepFilt_mono (Nat.zero_le n) (gen_mem_stepFilt (.relabel g C))

theorem t_mem_stepFilt (C C' : TwChamber Γ ν) {n : ℕ} (hn : 1 ≤ n) :
    (t C C' : TwGalleryAlgebra k Γ ν) ∈ stepFilt k Γ ν n :=
  stepFilt_mono hn (gen_mem_stepFilt (.step C C'))

theorem galList_mem_stepFilt (C : TwChamber Γ ν) (w : List (Hyp Γ ν)) :
    galList k C w ∈ stepFilt k Γ ν w.length := by
  induction w generalizing C with
  | nil => exact e_mem_stepFilt C 0
  | cons h w ih => exact mul_mem_stepFilt (ih _) (t_mem_stepFilt _ _ le_rfl)

/-- Every element lies in some step of the filtration. -/
theorem exists_mem_stepFilt (x : TwGalleryAlgebra k Γ ν) : ∃ n, x ∈ stepFilt k Γ ν n := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨0, ?_⟩
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (one_mem_stepFilt 0)
  | grade1 g => exact ⟨_, gen_mem_stepFilt g⟩
  | mul a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [map_mul]; exact mul_mem_stepFilt hm hn⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨max m n, by
      rw [map_add]
      exact Submodule.add_mem _ (stepFilt_mono (le_max_left m n) hm)
        (stepFilt_mono (le_max_right m n) hn)⟩

@[simp] theorem mk_tfe (C : TwChamber Γ ν) : mk k Γ ν (tfe k Γ ν C) = e C := rfl
@[simp] theorem mk_tfp (f : PolyRing ν k) : mk k Γ ν (tfp k Γ ν f) = poly f := rfl
@[simp] theorem mk_tft (C C' : TwChamber Γ ν) : mk k Γ ν (tft k Γ ν C C') = t C C' := rfl
@[simp] theorem mk_tfr (g : ColPerm ν) (C : TwChamber Γ ν) : mk k Γ ν (tfr k Γ ν g C) = r g C :=
  rfl

/-! ### Reversing the hyperplanes through a codimension-two flat -/

/-- Steps across two independent hyperplanes commute. -/
theorem galList_square {C B B' D : TwChamber Γ ν} {h₁ h₂ : Hyp Γ ν} (hne : h₁ ≠ h₂)
    (hi : h₁.Independent h₂) (a₁ : C.Adjacent B h₁) (a₂ : B.Adjacent D h₂)
    (a₃ : C.Adjacent B' h₂) (a₄ : B'.Adjacent D h₁) :
    galList k C [h₁, h₂] = galList k C [h₂, h₁] := by
  simp only [galList_cons, galList_nil, flipH_eq_of_adjacent a₁, flipH_eq_of_adjacent a₂,
    flipH_eq_of_adjacent a₃, flipH_eq_of_adjacent a₄, e_mul_t]
  have := rel (TwGalRel.square (k := k) C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄)
  simp only [map_mul] at this
  exact this

theorem galList_hexagon₁ (H : TwHexagon Γ ν) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] = mk k Γ ν (H.gal₁ k Γ ν) := by
  simp only [galList_cons, galList_nil, flipH_eq_of_adjacent H.adj₀₁,
    flipH_eq_of_adjacent H.adj₁₂, flipH_eq_of_adjacent H.adj₂₃, e_mul_t, TwHexagon.gal₁, map_mul]
  rfl

theorem galList_hexagon₂ (H : TwHexagon Γ ν) :
    galList k H.A₀ [H.h₃, H.h₂, H.h₁] = mk k Γ ν (H.gal₂ k Γ ν) := by
  simp only [galList_cons, galList_nil, flipH_eq_of_adjacent H.adj₀₅,
    flipH_eq_of_adjacent H.adj₅₄, flipH_eq_of_adjacent H.adj₄₃, e_mul_t, TwHexagon.gal₂, map_mul]
  rfl

/-- Three walls through a codimension-two flat. -/
theorem galList_hex_walls (H : TwHexagon Γ ν) (h₁ : H.h₁.isLeft) (h₂ : H.h₂.isLeft)
    (h₃ : H.h₃.isLeft) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] = galList k H.A₀ [H.h₃, H.h₂, H.h₁] := by
  rw [galList_hexagon₁, galList_hexagon₂]
  exact rel (TwGalRel.hex_walls H h₁ h₂ h₃)

/-- Two walls and a diagonal crossed in the middle: the correction has no step. -/
theorem galList_hex_mid_diag (H : TwHexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₁ : H.h₁ = .inl w)
    (h₂ : H.h₂ = .inr d) (h₃ : H.h₃ = .inl (w.comap d.refl))
    (hσ : H.A₀.1 (.inl w) ≠ H.A₀.1 (.inl (w.comap d.refl))) (hA : d.refl • H.A₀ = H.A₃) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] - galList k H.A₀ [H.h₃, H.h₂, H.h₁] ∈
      stepFilt k Γ ν 0 := by
  rw [galList_hexagon₁, galList_hexagon₂, ← map_sub,
    rel (TwGalRel.hex_mid_diag H w d h₁ h₂ h₃ hσ hA), map_mul, mk_tfp, mk_tfr]
  exact mul_mem_stepFilt (m := 0) (n := 0) (poly_mem_stepFilt _ 0) (r_mem_stepFilt _ _ 0)

/-- Two walls and a diagonal crossed first or last. -/
theorem galList_hex_end_diag (H : TwHexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₂ : H.h₂ = .inl w)
    (hd : (H.h₁ = .inr d ∧ H.h₃ = .inl (w.comap d.refl)) ∨
      (H.h₁ = .inl (w.comap d.refl) ∧ H.h₃ = .inr d))
    (hσ : H.A₀.1 (.inl w) = H.A₀.1 (.inl (w.comap d.refl))) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] = galList k H.A₀ [H.h₃, H.h₂, H.h₁] := by
  rw [galList_hexagon₁, galList_hexagon₂]
  exact rel (TwGalRel.hex_end_diag H w d h₂ hd hσ)

/-- Three diagonals: the braid relation, with a correction of one step. -/
theorem galList_hex_diags (H : TwHexagon Γ ν) (d₁ d₂ d₃ : Diag ν) (u v w : Strand ν)
    (h₁ : H.h₁ = .inr d₁) (h₂ : H.h₂ = .inr d₂) (h₃ : H.h₃ = .inr d₃) (j₁ : d₁.Joins u v)
    (j₂ : d₂.Joins u w) (j₃ : d₃.Joins v w) (hA : d₂.refl • H.A₀ = H.A₃) :
    galList k H.A₀ [H.h₁, H.h₂, H.h₃] - galList k H.A₀ [H.h₃, H.h₂, H.h₁] ∈
      stepFilt k Γ ν 1 := by
  rw [galList_hexagon₁, galList_hexagon₂, ← map_sub,
    rel (TwGalRel.hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA)]
  split
  · rw [map_zero]; exact Submodule.zero_mem _
  · simp only [TwHexagon.loopCorrection, map_add, map_mul, mk_tfp, mk_tfr, mk_tft]
    refine Submodule.add_mem _ ?_ ?_ <;>
      exact mul_mem_stepFilt (m := 0) (n := 1)
        (mul_mem_stepFilt (m := 0) (n := 0) (poly_mem_stepFilt _ 0) (r_mem_stepFilt _ _ 0))
        (t_mem_stepFilt _ _ le_rfl)

/-! ### Commutation of generators -/

theorem e_mul_poly (C : TwChamber Γ ν) (f : PolyRing ν k) :
    (e C * poly f : TwGalleryAlgebra k Γ ν) = poly f * e C := by
  have := rel (TwGalRel.poly_idem (k := k) f C)
  rw [map_mul, map_mul] at this
  exact this.symm

theorem r_eq (g : ColPerm ν) (C : TwChamber Γ ν) :
    (r g C : TwGalleryAlgebra k Γ ν) = e (g • C) * r g C * e C := by
  have := rel (TwGalRel.relabel_idem (k := k) g C)
  rw [map_mul, map_mul] at this
  exact this

theorem e_mul_r (D : TwChamber Γ ν) (g : ColPerm ν) (C : TwChamber Γ ν) :
    (e D * r g C : TwGalleryAlgebra k Γ ν) = if D = g • C then r g C else 0 := by
  conv_lhs => rw [r_eq, ← mul_assoc, ← mul_assoc, e_mul_e]
  split_ifs with h
  · subst h; exact (r_eq g C).symm
  · rw [zero_mul, zero_mul]

theorem r_mul_r (g h : ColPerm ν) (C : TwChamber Γ ν) :
    (r g (h • C) * r h C : TwGalleryAlgebra k Γ ν) = r (g * h) C := by
  have := rel (TwGalRel.relabel_mul (k := k) g h C)
  rw [map_mul] at this
  exact this

theorem r_mul_poly (g : ColPerm ν) (C : TwChamber Γ ν) (f : PolyRing ν k) :
    (r g C * poly f : TwGalleryAlgebra k Γ ν) = poly (rename g.1 f) * r g C := by
  have := rel (TwGalRel.relabel_poly (k := k) g C f)
  rw [map_mul, map_mul] at this
  exact this

theorem r_one (C : TwChamber Γ ν) : (r 1 C : TwGalleryAlgebra k Γ ν) = e C :=
  rel (TwGalRel.relabel_one (k := k) C)

theorem r_mul_t (g : ColPerm ν) (C C' : TwChamber Γ ν) :
    (r g C' * t C C' : TwGalleryAlgebra k Γ ν) = t (g • C) (g • C') * r g C := by
  have := rel (TwGalRel.relabel_step (k := k) g C C')
  rw [map_mul, map_mul] at this
  exact this

theorem r_mul_e (g : ColPerm ν) (C : TwChamber Γ ν) :
    (r g C * e C : TwGalleryAlgebra k Γ ν) = r g C := by
  conv_lhs => rw [r_eq, mul_assoc, e_mul_e, ite_eq_left rfl]
  rw [← r_eq]

theorem r_mul_r_eq (h : ColPerm ν) (D : TwChamber Γ ν) (g : ColPerm ν) (E : TwChamber Γ ν) :
    (r h D * r g E : TwGalleryAlgebra k Γ ν) = if D = g • E then r (h * g) E else 0 := by
  rw [← r_mul_e h D, mul_assoc, e_mul_r]
  split_ifs with hD
  · subst hD; exact r_mul_r h g E
  · rw [mul_zero]

theorem poly_mul_poly (f g : PolyRing ν k) :
    (poly f * poly g : TwGalleryAlgebra k Γ ν) = poly (f * g) :=
  ((polyHom k Γ ν).map_mul f g).symm

theorem t_mul_poly_inl {C C' : TwChamber Γ ν} {w : Wall Γ ν} (h : C.Adjacent C' (.inl w))
    (f : PolyRing ν k) : (t C C' * poly f : TwGalleryAlgebra k Γ ν) = poly f * t C C' := by
  have := rel (TwGalRel.wall_poly (k := k) C C' w h f)
  rw [map_mul, map_mul] at this
  exact this

theorem t_mul_poly_inr {C C' : TwChamber Γ ν} {d : Diag ν} (h : C.Adjacent C' (.inr d))
    (f : PolyRing ν k) : (t C C' * poly f : TwGalleryAlgebra k Γ ν) =
      poly f * t C C' + poly (stepFactor Γ (d.twLeft C) (d.twRight C) f) * r d.refl C := by
  have := rel (TwGalRel.diag_poly (k := k) C C' d h f)
  rw [map_sub, map_mul, map_mul, map_mul] at this
  simp only [mk_tfp, mk_tft, mk_tfr] at this
  rw [← this]
  abel

/-! ### Spanning by chosen galleries

Fix for each pair of full chambers `C, E` a gallery `seg C E` from `C` to `E` of length
`len C E`. The span `segSpan seg len m` of the elements `poly f * r g E * seg C E` with
`len C E ≤ m` is stable under left multiplication by idempotents, polynomials and
relabellings. If moreover one more step `t E E' * seg C E` stays in `segSpan (m + 1)` whenever
`stepFilt m ≤ segSpan m`, then the chosen galleries span the gallery algebra over the
polynomials and relabellings (`stepFilt_le_segSpan`).
-/

section SegSpan

variable (seg : TwChamber Γ ν → TwChamber Γ ν → TwGalleryAlgebra k Γ ν)
  (len : TwChamber Γ ν → TwChamber Γ ν → ℕ)

/-- The span of `poly f * r g E * seg C E` over the pairs with `len C E ≤ m`. -/
noncomputable def segSpan (m : ℕ) : Submodule k (TwGalleryAlgebra k Γ ν) :=
  Submodule.span k
    {x | ∃ f g C E, len C E ≤ m ∧ (poly f * r g E * seg C E : TwGalleryAlgebra k Γ ν) = x}

variable {seg len}

theorem segSpan_mono {m n : ℕ} (h : m ≤ n) : segSpan seg len m ≤ segSpan seg len n :=
  Submodule.span_mono fun _ ⟨f, g, C, E, hl, hx⟩ => ⟨f, g, C, E, hl.trans h, hx⟩

theorem mem_segSpan_of_mul_mem {m n : ℕ} (a : TwGalleryAlgebra k Γ ν)
    (ha : ∀ f g C E, len C E ≤ m → a * (poly f * r g E * seg C E) ∈ segSpan seg len n)
    {x : TwGalleryAlgebra k Γ ν} (hx : x ∈ segSpan seg len m) : a * x ∈ segSpan seg len n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, C, E, hl, rfl⟩ := hx
    exact ha f g C E hl
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem gen_mem_segSpan {m : ℕ} (f : PolyRing ν k) (g : ColPerm ν) {C E : TwChamber Γ ν}
    (hl : len C E ≤ m) : (poly f * r g E * seg C E : TwGalleryAlgebra k Γ ν) ∈ segSpan seg len m :=
  Submodule.subset_span ⟨f, g, C, E, hl, rfl⟩

theorem poly_mul_mem_segSpan {m : ℕ} (f' : PolyRing ν k) {x : TwGalleryAlgebra k Γ ν}
    (hx : x ∈ segSpan seg len m) : poly f' * x ∈ segSpan seg len m := by
  refine mem_segSpan_of_mul_mem _ (fun f g C E hl => ?_) hx
  rw [← mul_assoc, ← mul_assoc, poly_mul_poly]
  exact gen_mem_segSpan _ _ hl

theorem e_mul_mem_segSpan {m : ℕ} (D : TwChamber Γ ν) {x : TwGalleryAlgebra k Γ ν}
    (hx : x ∈ segSpan seg len m) : e D * x ∈ segSpan seg len m := by
  refine mem_segSpan_of_mul_mem _ (fun f g C E hl => ?_) hx
  rw [← mul_assoc, ← mul_assoc, e_mul_poly, mul_assoc (poly f), e_mul_r]
  split_ifs
  · exact gen_mem_segSpan _ _ hl
  · rw [mul_zero, zero_mul]; exact Submodule.zero_mem _

theorem r_mul_mem_segSpan {m : ℕ} (h : ColPerm ν) (D : TwChamber Γ ν)
    {x : TwGalleryAlgebra k Γ ν} (hx : x ∈ segSpan seg len m) : r h D * x ∈ segSpan seg len m := by
  refine mem_segSpan_of_mul_mem _ (fun f g C E hl => ?_) hx
  rw [show r h D * (poly f * r g E * seg C E) = poly (rename h.1 f) * (r h D * r g E) * seg C E by
    rw [← mul_assoc, ← mul_assoc, r_mul_poly]; simp only [mul_assoc], r_mul_r_eq]
  split_ifs
  · exact gen_mem_segSpan _ _ hl
  · rw [mul_zero, zero_mul]; exact Submodule.zero_mem _

theorem t_mul_r_eq (g : ColPerm ν) (E E' : TwChamber Γ ν) :
    (t (g • E) E' * r g E : TwGalleryAlgebra k Γ ν) = r g (g⁻¹ • E') * t E (g⁻¹ • E') := by
  rw [r_mul_t, smul_inv_smul]

/-- One more step on a spanning element, given the same for the chosen galleries. -/
theorem t_mul_mem_segSpan {m : ℕ}
    (key : ∀ C E E₁, len C E ≤ m → t E E₁ * seg C E ∈ segSpan seg len (m + 1))
    (E'' E' : TwChamber Γ ν) {x : TwGalleryAlgebra k Γ ν} (hx : x ∈ segSpan seg len m) :
    t E'' E' * x ∈ segSpan seg len (m + 1) := by
  refine mem_segSpan_of_mul_mem _ (fun f g C E hl => ?_) hx
  rw [← t_mul_e, mul_assoc, ← mul_assoc (e E''), ← mul_assoc (e E''), e_mul_poly,
    mul_assoc (poly f), e_mul_r]
  split_ifs with hE
  swap
  · rw [mul_zero, zero_mul, mul_zero]; exact Submodule.zero_mem _
  subst hE
  have hstep : ∀ f' : PolyRing ν k, poly f' * (t (g • E) E' * r g E) * seg C E ∈
      segSpan seg len (m + 1) := by
    intro f'
    rw [t_mul_r_eq, mul_assoc, mul_assoc]
    exact poly_mul_mem_segSpan _ (r_mul_mem_segSpan _ _ (key C E _ hl))
  by_cases hadj : ∃ h, (g • E).Adjacent E' h
  · obtain ⟨h, hh⟩ := hadj
    cases h with
    | inl w =>
      rw [← mul_assoc, ← mul_assoc, t_mul_poly_inl hh, mul_assoc (poly f)]
      exact hstep f
    | inr d =>
      rw [← mul_assoc, ← mul_assoc, t_mul_poly_inr hh, add_mul, add_mul]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_assoc (poly f)]; exact hstep f
      · have h1 : r g E * seg C E ∈ segSpan seg len (m + 1) := by
          have := segSpan_mono (Nat.le_succ m)
            (gen_mem_segSpan (seg := seg) (len := len) (1 : PolyRing ν k) g hl)
          rwa [← polyHom_apply, map_one, one_mul] at this
        simpa only [mul_assoc] using poly_mul_mem_segSpan _ (r_mul_mem_segSpan d.refl (g • E) h1)
  · push Not at hadj
    rw [t_eq_zero hadj, zero_mul]; exact Submodule.zero_mem _

/-- The chosen galleries span: every element with at most `m` steps is a combination of
`poly f * r g E * seg C E` with `len C E ≤ m`. -/
theorem stepFilt_le_segSpan (hone : (1 : TwGalleryAlgebra k Γ ν) ∈ segSpan seg len 0)
    (key : ∀ m, stepFilt k Γ ν m ≤ segSpan seg len m →
      ∀ C E E₁, len C E ≤ m → t E E₁ * seg C E ∈ segSpan seg len (m + 1)) (m : ℕ) :
    stepFilt k Γ ν m ≤ segSpan seg len m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rw [stepFilt, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact segSpan_mono (Nat.zero_le m) hone
  | cons G l ihl =>
    simp only [List.map_cons, List.sum_cons] at hl
    rw [wordVal, List.map_cons, List.prod_cons, ← wordVal]
    cases G with
    | idem D => exact e_mul_mem_segSpan D (ihl (by simpa [TwGen.stepCount] using hl))
    | poly f => exact poly_mul_mem_segSpan f (ihl (by simpa [TwGen.stepCount] using hl))
    | relabel g D => exact r_mul_mem_segSpan g D (ihl (by simpa [TwGen.stepCount] using hl))
    | step C C' =>
      simp only [TwGen.stepCount] at hl
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' := ih m' (Nat.lt_succ_self m')
      have hx : wordVal k Γ ν l ∈ segSpan seg len m' :=
        hm' (Submodule.subset_span ⟨l, by omega, rfl⟩)
      exact t_mul_mem_segSpan (key m' hm') C C' hx

end SegSpan

end TwGalleryAlgebra

end Categorification.WeightedKLR
