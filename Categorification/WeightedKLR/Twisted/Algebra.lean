/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Relabel

/-!
# The twisted gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5 (the
category `P` before Proposition 2.20).

A morphism of `P` from `(x₀, ϑ₀)` to `(x₁, ϑ₁)` moves the strands and the weights at the
same time; we read it as a gallery of chambers of the arrangement of positions and weights
(`Twisted/Arrangement.lean`), whose hyperplanes are the walls `x_b - x_a - ϑ_e` and the
diagonals `x_{s'} - x_s`. The *twisted gallery algebra* `TwGalleryAlgebra k Γ ν` is presented
as the gallery algebra of a fixed weighting (`Algebra.lean`), with the chambers of the big
arrangement in place of the full chambers:

* idempotents `e C`, polynomials, steps `t C C'` across one hyperplane, relabellings `r g C`;
* the bigons, the polynomials past steps, the square relation for independent hyperplanes;
* one relation for each kind of codimension-two flat with three hyperplanes.

The codimension-two flats with three hyperplanes of the big arrangement are classified in
`Twisted/Blocks.lean` (`twTriple_of_finrank`): three diagonals on three strands of one colour,
or a diagonal `d` and two walls `W`, `W.comap d.refl` (Webster's relations (4a), (4b)). The
second kind includes, for a loop `e` at the colour of `d` of any weight, the flat
`x_a = x_b`, `ϑ_e = 0` where a strand would meet its own ghost; it is covered by the relations
`hex_mid_diag`, `hex_end_diag` as for any other edge. Three walls never meet in such a flat
(`TwRel.not_three_walls`); the relation `hex_walls` is kept so that the presentation is the
one of `GalleryAlgebra` read on the big arrangement.

## Main definitions

* `Diag.twLeft C d`, `Diag.twRight C d`: the strands of `d` to the left and right in `C`.
* `TwHexagon Γ ν`: two galleries of length three crossing the same three hyperplanes in
  opposite orders.
* `TwGalleryAlgebra k Γ ν`: the twisted gallery algebra.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The strand of the diagonal `d` to the left in the chamber `C`. -/
def Diag.twLeft (C : TwChamber Γ ν) (d : Diag ν) : Strand ν :=
  if C.1 (.inr d) then d.fst else d.snd

/-- The strand of the diagonal `d` to the right in the chamber `C`. -/
def Diag.twRight (C : TwChamber Γ ν) (d : Diag ν) : Strand ν :=
  if C.1 (.inr d) then d.snd else d.fst

variable (Γ ν) in
/-- Two galleries `A₀ → A₁ → A₂ → A₃` and `A₀ → A₅ → A₄ → A₃` crossing the distinct
hyperplanes `h₁, h₂, h₃`, respectively `h₃, h₂, h₁`. -/
structure TwHexagon where
  /-- The chambers. -/
  A₀ : TwChamber Γ ν
  /-- The chambers. -/
  A₁ : TwChamber Γ ν
  /-- The chambers. -/
  A₂ : TwChamber Γ ν
  /-- The chambers. -/
  A₃ : TwChamber Γ ν
  /-- The chambers. -/
  A₄ : TwChamber Γ ν
  /-- The chambers. -/
  A₅ : TwChamber Γ ν
  /-- The hyperplanes. -/
  h₁ : Hyp Γ ν
  /-- The hyperplanes. -/
  h₂ : Hyp Γ ν
  /-- The hyperplanes. -/
  h₃ : Hyp Γ ν
  ne₁₂ : h₁ ≠ h₂
  ne₁₃ : h₁ ≠ h₃
  ne₂₃ : h₂ ≠ h₃
  adj₀₁ : A₀.Adjacent A₁ h₁
  adj₁₂ : A₁.Adjacent A₂ h₂
  adj₂₃ : A₂.Adjacent A₃ h₃
  adj₀₅ : A₀.Adjacent A₅ h₃
  adj₅₄ : A₅.Adjacent A₄ h₂
  adj₄₃ : A₄.Adjacent A₃ h₁

/-! ### Generators and relations -/

variable (k Γ ν) in
/-- Generators of the twisted gallery algebra. -/
inductive TwGen : Type _
  | idem : TwChamber Γ ν → TwGen
  | poly : PolyRing ν k → TwGen
  | step : TwChamber Γ ν → TwChamber Γ ν → TwGen
  | relabel : ColPerm ν → TwChamber Γ ν → TwGen

section TwGalRel

variable (k Γ ν)

local notation "Fr" => FreeAlgebra k (TwGen k Γ ν)

/-- The idempotent `e C` in the free algebra. -/
noncomputable abbrev tfe (C : TwChamber Γ ν) : Fr := FreeAlgebra.ι k (TwGen.idem C)
/-- The polynomial `f` in the free algebra. -/
noncomputable abbrev tfp (f : PolyRing ν k) : Fr := FreeAlgebra.ι k (TwGen.poly f)
/-- The step from `C` to `C'` in the free algebra. -/
noncomputable abbrev tft (C C' : TwChamber Γ ν) : Fr := FreeAlgebra.ι k (TwGen.step C C')
/-- The relabelling `C → g • C` in the free algebra. -/
noncomputable abbrev tfr (g : ColPerm ν) (C : TwChamber Γ ν) : Fr :=
  FreeAlgebra.ι k (TwGen.relabel g C)

/-- The gallery `A₀ → A₁ → A₂ → A₃` of a hexagon. -/
noncomputable def TwHexagon.gal₁ (H : TwHexagon Γ ν) : Fr :=
  tft k Γ ν H.A₂ H.A₃ * tft k Γ ν H.A₁ H.A₂ * tft k Γ ν H.A₀ H.A₁

/-- The gallery `A₀ → A₅ → A₄ → A₃` of a hexagon. -/
noncomputable def TwHexagon.gal₂ (H : TwHexagon Γ ν) : Fr :=
  tft k Γ ν H.A₄ H.A₃ * tft k Γ ν H.A₅ H.A₄ * tft k Γ ν H.A₀ H.A₅

/-- The correction of the braid relation for three diagonals `{u, v}`, `{u, w}`, `{v, w}`
with a loop of polynomial `P` (Webster's relation (4c), labelled form). The first gallery
crosses `d₁ = {u, v}` first and `d₃ = {v, w}` last; the correction is a combination of the
one-step galleries `A₀ → A₁`, `A₀ → A₅` followed by relabellings to `A₃`. -/
noncomputable def TwHexagon.loopCorrection (H : TwHexagon Γ ν) (d₁ d₂ d₃ : Diag ν)
    (u v w : Strand ν) (P : MvPolynomial (Fin 2) k) : Fr :=
  let Puv : PolyRing ν k := loopFactor P u v
  let Puw : PolyRing ν k := loopFactor P u w
  let Pvw : PolyRing ν k := loopFactor P v w
  tfp k Γ ν (-(Puv * Puw - Pvw * Puw - Pvw * Puv)) * tfr k Γ ν (d₂.refl * d₁.refl) H.A₁ *
      tft k Γ ν H.A₀ H.A₁ +
    tfp k Γ ν (-(Puv * Puw + Puv * Pvw - Puw * Pvw)) * tfr k Γ ν (d₂.refl * d₃.refl) H.A₅ *
      tft k Γ ν H.A₀ H.A₅

/-- The defining relations of the twisted gallery algebra. -/
inductive TwGalRel : Fr → Fr → Prop
  /-- `e C e D = δ_{C D} e C`. -/
  | idem_mul (C D : TwChamber Γ ν) :
      TwGalRel (tfe k Γ ν C * tfe k Γ ν D) (if C = D then tfe k Γ ν C else 0)
  /-- `∑_C e C = 1`. -/
  | idem_sum : TwGalRel (∑ C, tfe k Γ ν C) 1
  /-- Polynomials form a subring. -/
  | poly_add (f g : PolyRing ν k) : TwGalRel (tfp k Γ ν (f + g)) (tfp k Γ ν f + tfp k Γ ν g)
  /-- Polynomials form a subring. -/
  | poly_mul (f g : PolyRing ν k) : TwGalRel (tfp k Γ ν (f * g)) (tfp k Γ ν f * tfp k Γ ν g)
  /-- Constant polynomials are scalars. -/
  | poly_C (c : k) : TwGalRel (tfp k Γ ν (C c)) (algebraMap k Fr c)
  /-- Polynomials preserve chambers. -/
  | poly_idem (f : PolyRing ν k) (C : TwChamber Γ ν) :
      TwGalRel (tfp k Γ ν f * tfe k Γ ν C) (tfe k Γ ν C * tfp k Γ ν f)
  /-- A step goes from `C` to `C'`. -/
  | step_idem (C C' : TwChamber Γ ν) :
      TwGalRel (tft k Γ ν C C') (tfe k Γ ν C' * tft k Γ ν C C' * tfe k Γ ν C)
  /-- Steps between non-adjacent chambers vanish. -/
  | step_zero (C C' : TwChamber Γ ν) (h : ∀ h : Hyp Γ ν, ¬C.Adjacent C' h) :
      TwGalRel (tft k Γ ν C C') 0
  /-- A relabelling goes from `C` to `g • C`. -/
  | relabel_idem (g : ColPerm ν) (C : TwChamber Γ ν) :
      TwGalRel (tfr k Γ ν g C) (tfe k Γ ν (g • C) * tfr k Γ ν g C * tfe k Γ ν C)
  /-- The trivial relabelling is the identity. -/
  | relabel_one (C : TwChamber Γ ν) : TwGalRel (tfr k Γ ν 1 C) (tfe k Γ ν C)
  /-- Relabellings compose. -/
  | relabel_mul (g h : ColPerm ν) (C : TwChamber Γ ν) :
      TwGalRel (tfr k Γ ν g (h • C) * tfr k Γ ν h C) (tfr k Γ ν (g * h) C)
  /-- Relabelling renames the variables. -/
  | relabel_poly (g : ColPerm ν) (C : TwChamber Γ ν) (f : PolyRing ν k) :
      TwGalRel (tfr k Γ ν g C * tfp k Γ ν f) (tfp k Γ ν (rename g.1 f) * tfr k Γ ν g C)
  /-- Relabelling is compatible with steps. -/
  | relabel_step (g : ColPerm ν) (C C' : TwChamber Γ ν) :
      TwGalRel (tfr k Γ ν g C' * tft k Γ ν C C') (tft k Γ ν (g • C) (g • C') * tfr k Γ ν g C)
  /-- The ghost bigon, Webster's relation (2). -/
  | wall_bigon (C C' : TwChamber Γ ν) (w : Wall Γ ν) (h : C.Adjacent C' (.inl w)) :
      TwGalRel (tft k Γ ν C' C * tft k Γ ν C C') (tfp k Γ ν w.factor * tfe k Γ ν C)
  /-- The strand bigon, Webster's relation (3): `0` without a loop, `2 P_i ψ` with one. -/
  | diag_bigon (C C' : TwChamber Γ ν) (d : Diag ν) (h : C.Adjacent C' (.inr d)) :
      TwGalRel (tft k Γ ν C' C * tft k Γ ν C C')
        (match Γ.loop d.fst.1 with
          | none => 0
          | some P => tfp k Γ ν (-2 * loopFactor P (d.twLeft C) (d.twRight C)) *
              tfr k Γ ν d.refl C' * tft k Γ ν C C')
  /-- Polynomials commute with steps across walls. -/
  | wall_poly (C C' : TwChamber Γ ν) (w : Wall Γ ν) (h : C.Adjacent C' (.inl w))
      (f : PolyRing ν k) :
      TwGalRel (tft k Γ ν C C' * tfp k Γ ν f) (tfp k Γ ν f * tft k Γ ν C C')
  /-- Polynomials past a step across a diagonal, Webster's relation (1). -/
  | diag_poly (C C' : TwChamber Γ ν) (d : Diag ν) (h : C.Adjacent C' (.inr d))
      (f : PolyRing ν k) :
      TwGalRel (tft k Γ ν C C' * tfp k Γ ν f - tfp k Γ ν f * tft k Γ ν C C')
        (tfp k Γ ν (stepFactor Γ (d.twLeft C) (d.twRight C) f) * tfr k Γ ν d.refl C)
  /-- Steps across independent hyperplanes commute. -/
  | square (C B B' D : TwChamber Γ ν) (h₁ h₂ : Hyp Γ ν) (hne : h₁ ≠ h₂)
      (hi : h₁.Independent h₂) (a₁ : C.Adjacent B h₁) (a₂ : B.Adjacent D h₂)
      (a₃ : C.Adjacent B' h₂) (a₄ : B'.Adjacent D h₁) :
      TwGalRel (tft k Γ ν B D * tft k Γ ν C B) (tft k Γ ν B' D * tft k Γ ν C B')
  /-- Three walls through a codimension-two flat. -/
  | hex_walls (H : TwHexagon Γ ν) (h₁ : H.h₁.isLeft) (h₂ : H.h₂.isLeft) (h₃ : H.h₃.isLeft) :
      TwGalRel (H.gal₁ k Γ ν) (H.gal₂ k Γ ν)
  /-- A strand of one colour crossing two strands of another colour through the ghost of a
  third strand, the diagonal crossed in the middle: Webster's relations (4a), (4b). -/
  | hex_mid_diag (H : TwHexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₁ : H.h₁ = .inl w)
      (h₂ : H.h₂ = .inr d) (h₃ : H.h₃ = .inl (w.comap d.refl))
      (hσ : H.A₀.1 (.inl w) ≠ H.A₀.1 (.inl (w.comap d.refl))) (hA : d.refl • H.A₀ = H.A₃) :
      TwGalRel (H.gal₁ k Γ ν - H.gal₂ k Γ ν)
        (tfp k Γ ν (stepFactor Γ (d.twLeft H.A₁) (d.twRight H.A₁) w.factor) * tfr k Γ ν d.refl H.A₀)
  /-- The same flat as `hex_mid_diag`, the diagonal crossed first or last: no correction. -/
  | hex_end_diag (H : TwHexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₂ : H.h₂ = .inl w)
      (hd : (H.h₁ = .inr d ∧ H.h₃ = .inl (w.comap d.refl)) ∨
        (H.h₁ = .inl (w.comap d.refl) ∧ H.h₃ = .inr d))
      (hσ : H.A₀.1 (.inl w) = H.A₀.1 (.inl (w.comap d.refl))) :
      TwGalRel (H.gal₁ k Γ ν) (H.gal₂ k Γ ν)
  /-- Three strands of one colour: the braid relation, with Webster's correction (4c) when
  there is a loop. -/
  | hex_diags (H : TwHexagon Γ ν) (d₁ d₂ d₃ : Diag ν) (u v w : Strand ν) (h₁ : H.h₁ = .inr d₁)
      (h₂ : H.h₂ = .inr d₂) (h₃ : H.h₃ = .inr d₃) (j₁ : d₁.Joins u v) (j₂ : d₂.Joins u w)
      (j₃ : d₃.Joins v w) (hA : d₂.refl • H.A₀ = H.A₃) :
      TwGalRel (H.gal₁ k Γ ν - H.gal₂ k Γ ν)
        (match Γ.loop u.1 with
          | none => 0
          | some P => H.loopCorrection k Γ ν d₁ d₂ d₃ u v w P)

end TwGalRel

variable (k Γ ν) in
/-- The twisted gallery algebra: galleries in the arrangement of positions and weights. -/
def TwGalleryAlgebra : Type _ := RingQuot (TwGalRel k Γ ν)

namespace TwGalleryAlgebra

noncomputable instance : Ring (TwGalleryAlgebra k Γ ν) := inferInstanceAs (Ring (RingQuot _))
noncomputable instance : Algebra k (TwGalleryAlgebra k Γ ν) :=
  inferInstanceAs (Algebra k (RingQuot _))

variable (k Γ ν) in
/-- The quotient map from the free algebra. -/
noncomputable def mk : FreeAlgebra k (TwGen k Γ ν) →ₐ[k] TwGalleryAlgebra k Γ ν :=
  RingQuot.mkAlgHom k (TwGalRel k Γ ν)

theorem mk_surjective : Function.Surjective (mk k Γ ν) :=
  RingQuot.mkAlgHom_surjective _ _

theorem rel {a b : FreeAlgebra k (TwGen k Γ ν)} (h : TwGalRel k Γ ν a b) : mk k Γ ν a = mk k Γ ν b :=
  RingQuot.mkAlgHom_rel k h

/-- The idempotent of a chamber. -/
noncomputable def e (C : TwChamber Γ ν) : TwGalleryAlgebra k Γ ν := mk k Γ ν (tfe k Γ ν C)

/-- A polynomial. -/
noncomputable def poly (f : PolyRing ν k) : TwGalleryAlgebra k Γ ν := mk k Γ ν (tfp k Γ ν f)

/-- The step from `C` to `C'` (zero unless they are adjacent). -/
noncomputable def t (C C' : TwChamber Γ ν) : TwGalleryAlgebra k Γ ν := mk k Γ ν (tft k Γ ν C C')

/-- The relabelling `C → g • C`. -/
noncomputable def r (g : ColPerm ν) (C : TwChamber Γ ν) : TwGalleryAlgebra k Γ ν :=
  mk k Γ ν (tfr k Γ ν g C)

theorem e_mul_e (C D : TwChamber Γ ν) :
    (e C * e D : TwGalleryAlgebra k Γ ν) = if C = D then e C else 0 := by
  have := rel (TwGalRel.idem_mul (k := k) (Γ := Γ) C D)
  rw [map_mul] at this
  rw [e, e, this]
  split_ifs <;> simp

theorem sum_e : ∑ C, (e C : TwGalleryAlgebra k Γ ν) = 1 := by
  have := rel (TwGalRel.idem_sum (k := k) (Γ := Γ) (ν := ν))
  rw [map_sum, map_one] at this
  exact this

variable (k Γ ν) in
/-- Polynomials, as an algebra map into the twisted gallery algebra. -/
noncomputable def polyHom : PolyRing ν k →ₐ[k] TwGalleryAlgebra k Γ ν where
  toFun := poly
  map_one' := by
    have := rel (TwGalRel.poly_C (k := k) (Γ := Γ) (ν := ν) 1)
    rw [AlgHom.commutes] at this
    rw [poly, ← C_1, this, map_one]
  map_mul' f g := by
    have := rel (TwGalRel.poly_mul (k := k) (Γ := Γ) f g)
    rw [map_mul] at this
    exact this
  map_zero' := by
    have := rel (TwGalRel.poly_C (k := k) (Γ := Γ) (ν := ν) 0)
    rw [AlgHom.commutes] at this
    rw [poly, ← C_0, this, map_zero]
  map_add' f g := by
    have := rel (TwGalRel.poly_add (k := k) (Γ := Γ) f g)
    rw [map_add] at this
    exact this
  commutes' c := by
    have := rel (TwGalRel.poly_C (k := k) (Γ := Γ) (ν := ν) c)
    rw [AlgHom.commutes] at this
    rw [← this, algebraMap_eq]
    rfl

@[simp] theorem polyHom_apply (f : PolyRing ν k) : polyHom k Γ ν f = poly f := rfl

end TwGalleryAlgebra

end Categorification.WeightedKLR
