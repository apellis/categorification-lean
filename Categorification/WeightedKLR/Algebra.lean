/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.PolyRep
import Categorification.WeightedKLR.Relabel

/-!
# The gallery algebra of the labelled arrangement

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1
(Definitions 2.3–2.5).

A weighted KLR diagram is read here as a gallery of full chambers of the labelled arrangement
(`Arrangement.lean`): strands keep their labels, so a crossing of two strands of one colour is a
step across a diagonal, followed by a relabelling (`Relabel.lean`) to return to the rank-ordered
region. The *gallery algebra* `GalleryAlgebra k Γ ν` has

* an idempotent `e C` for each full chamber `C`;
* the polynomials `poly f`, `f ∈ k[y_s : s ∈ Strand ν]` (dots are `poly (X s)`);
* a step `t C C'` across one hyperplane, from `C` to `C'`;
* a relabelling `r g C : C → g • C` for each colour-preserving permutation `g`,

subject to the local relations of Webster's Definition 2.4, read for labelled strands:

* bigons: across a wall `w`, `t C' C t C C' = Q_w e_C` (relation (2)); across a diagonal, `0`
  without a loop and `2 P_i ψ` with one (relation (3));
* polynomials past steps: they commute with wall steps, and past a diagonal step
  `t f - f t = Δ(f) r` with `Δ = ∂_{l r}` (no loop) or `P_i (1 - s_{l r})` (loop), the nilHecke
  relations (1);
* a square relation for two independent hyperplanes, and one relation for each kind of
  codimension-two flat with three hyperplanes: three walls (no correction), two walls and a
  diagonal (Webster's (4a), (4b): a correction `Δ(Q_e) r` when the diagonal is crossed in the
  middle), and three diagonals (the braid relation, with Webster's correction (4c) when there is a
  loop).

Each relation is stated with the hypotheses under which it holds in the polynomial
representation; these hypotheses are satisfied by the galleries around a codimension-two flat.

## Main definitions

* `Diag.left C d`, `Diag.right C d`: the strands of `d` to the left and right in `C`.
* `stepFactor Γ l r f`: `Δ_{l r}(f)`, the operator of a diagonal step applied to `f` up to the
  relabelling.
* `Hexagon Γ ν`: two galleries of length three crossing the same three hyperplanes in opposite
  orders.
* `GalleryAlgebra k Γ ν`: the gallery algebra.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-! ### Left and right strands of a diagonal -/

/-- The strand of the diagonal `d` to the left in the full chamber `C`. -/
def Diag.left (C : FullChamber Γ ν) (d : Diag ν) : Strand ν :=
  if C.1 (.inr d) then d.fst else d.snd

/-- The strand of the diagonal `d` to the right in the full chamber `C`. -/
def Diag.right (C : FullChamber Γ ν) (d : Diag ν) : Strand ν :=
  if C.1 (.inr d) then d.snd else d.fst

variable (Γ) in
/-- `Δ_{l r}(f)`: the divided difference `∂_{l r} f` if there is no loop at the colour of `l`,
and `P_i(y_l, y_r) (f - s_{l r} f)` if there is a loop with polynomial `P_i`. A diagonal step
`t` with `l` on the left before the step satisfies `t (f g) = f (t g) + Δ_{l r}(f) (s_{l r} g)`
in the polynomial representation. -/
noncomputable def stepFactor (l r : Strand ν) (f : PolyRing ν k) : PolyRing ν k :=
  match Γ.loop l.1 with
  | none => ddiff l r f
  | some P => loopFactor P l r * (f - rename (swap l r) f)

/-! ### Independent hyperplanes and hexagons -/

/-- The strands met by a hyperplane. -/
def Hyp.strands : Hyp Γ ν → Finset (Strand ν)
  | .inl w => {w.src, w.tgt}
  | .inr d => {d.fst, d.snd}

/-- Two hyperplanes whose steps commute: two walls, or two hyperplanes on disjoint strands. -/
def Hyp.Independent (h h' : Hyp Γ ν) : Prop :=
  (h.isLeft ∧ h'.isLeft) ∨ Disjoint h.strands h'.strands

variable (Γ ν) in
/-- Two galleries `A₀ → A₁ → A₂ → A₃` and `A₀ → A₅ → A₄ → A₃` crossing the distinct
hyperplanes `h₁, h₂, h₃`, respectively `h₃, h₂, h₁`. -/
structure Hexagon where
  /-- The chambers. -/
  A₀ : FullChamber Γ ν
  /-- The chambers. -/
  A₁ : FullChamber Γ ν
  /-- The chambers. -/
  A₂ : FullChamber Γ ν
  /-- The chambers. -/
  A₃ : FullChamber Γ ν
  /-- The chambers. -/
  A₄ : FullChamber Γ ν
  /-- The chambers. -/
  A₅ : FullChamber Γ ν
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

/-- The diagonal `d` is the hyperplane `x_a = x_b`. -/
def Diag.Joins (d : Diag ν) (a b : Strand ν) : Prop :=
  (d.fst = a ∧ d.snd = b) ∨ (d.fst = b ∧ d.snd = a)

/-! ### Generators and relations -/

variable (k Γ ν) in
/-- Generators of the gallery algebra. -/
inductive Gen : Type _
  | idem : FullChamber Γ ν → Gen
  | poly : PolyRing ν k → Gen
  | step : FullChamber Γ ν → FullChamber Γ ν → Gen
  | relabel : ColPerm ν → FullChamber Γ ν → Gen

section Rel

variable (k Γ ν)

local notation "Fr" => FreeAlgebra k (Gen k Γ ν)

/-- The idempotent `e C` in the free algebra. -/
noncomputable abbrev fe (C : FullChamber Γ ν) : Fr := FreeAlgebra.ι k (Gen.idem C)
/-- The polynomial `f` in the free algebra. -/
noncomputable abbrev fp (f : PolyRing ν k) : Fr := FreeAlgebra.ι k (Gen.poly f)
/-- The step from `C` to `C'` in the free algebra. -/
noncomputable abbrev ft (C C' : FullChamber Γ ν) : Fr := FreeAlgebra.ι k (Gen.step C C')
/-- The relabelling `C → g • C` in the free algebra. -/
noncomputable abbrev fr (g : ColPerm ν) (C : FullChamber Γ ν) : Fr :=
  FreeAlgebra.ι k (Gen.relabel g C)

/-- The gallery `A₀ → A₁ → A₂ → A₃` of a hexagon. -/
noncomputable def Hexagon.gal₁ (H : Hexagon Γ ν) : Fr :=
  ft k Γ ν H.A₂ H.A₃ * ft k Γ ν H.A₁ H.A₂ * ft k Γ ν H.A₀ H.A₁

/-- The gallery `A₀ → A₅ → A₄ → A₃` of a hexagon. -/
noncomputable def Hexagon.gal₂ (H : Hexagon Γ ν) : Fr :=
  ft k Γ ν H.A₄ H.A₃ * ft k Γ ν H.A₅ H.A₄ * ft k Γ ν H.A₀ H.A₅

/-- The correction of the braid relation for three diagonals `{u, v}`, `{u, w}`, `{v, w}`
with a loop of polynomial `P` (Webster's relation (4c), labelled form). The first gallery
crosses `d₁ = {u, v}` first and `d₃ = {v, w}` last; the correction is a combination of the
one-step galleries `A₀ → A₁`, `A₀ → A₅` followed by relabellings to `A₃`. -/
noncomputable def Hexagon.loopCorrection (H : Hexagon Γ ν) (d₁ d₂ d₃ : Diag ν)
    (u v w : Strand ν) (P : MvPolynomial (Fin 2) k) : Fr :=
  let Puv : PolyRing ν k := loopFactor P u v
  let Puw : PolyRing ν k := loopFactor P u w
  let Pvw : PolyRing ν k := loopFactor P v w
  fp k Γ ν (-(Puv * Puw - Pvw * Puw - Pvw * Puv)) * fr k Γ ν (d₂.refl * d₁.refl) H.A₁ *
      ft k Γ ν H.A₀ H.A₁ +
    fp k Γ ν (-(Puv * Puw + Puv * Pvw - Puw * Pvw)) * fr k Γ ν (d₂.refl * d₃.refl) H.A₅ *
      ft k Γ ν H.A₀ H.A₅

/-- The defining relations of the gallery algebra. -/
inductive Rel : Fr → Fr → Prop
  /-- `e C e D = δ_{C D} e C`. -/
  | idem_mul (C D : FullChamber Γ ν) :
      Rel (fe k Γ ν C * fe k Γ ν D) (if C = D then fe k Γ ν C else 0)
  /-- `∑_C e C = 1`. -/
  | idem_sum : Rel (∑ C, fe k Γ ν C) 1
  /-- Polynomials form a subring. -/
  | poly_add (f g : PolyRing ν k) : Rel (fp k Γ ν (f + g)) (fp k Γ ν f + fp k Γ ν g)
  /-- Polynomials form a subring. -/
  | poly_mul (f g : PolyRing ν k) : Rel (fp k Γ ν (f * g)) (fp k Γ ν f * fp k Γ ν g)
  /-- Constant polynomials are scalars. -/
  | poly_C (c : k) : Rel (fp k Γ ν (C c)) (algebraMap k Fr c)
  /-- Polynomials preserve chambers. -/
  | poly_idem (f : PolyRing ν k) (C : FullChamber Γ ν) :
      Rel (fp k Γ ν f * fe k Γ ν C) (fe k Γ ν C * fp k Γ ν f)
  /-- A step goes from `C` to `C'`. -/
  | step_idem (C C' : FullChamber Γ ν) :
      Rel (ft k Γ ν C C') (fe k Γ ν C' * ft k Γ ν C C' * fe k Γ ν C)
  /-- Steps between non-adjacent chambers vanish. -/
  | step_zero (C C' : FullChamber Γ ν) (h : ∀ h : Hyp Γ ν, ¬C.Adjacent C' h) :
      Rel (ft k Γ ν C C') 0
  /-- A relabelling goes from `C` to `g • C`. -/
  | relabel_idem (g : ColPerm ν) (C : FullChamber Γ ν) :
      Rel (fr k Γ ν g C) (fe k Γ ν (g • C) * fr k Γ ν g C * fe k Γ ν C)
  /-- The trivial relabelling is the identity. -/
  | relabel_one (C : FullChamber Γ ν) : Rel (fr k Γ ν 1 C) (fe k Γ ν C)
  /-- Relabellings compose. -/
  | relabel_mul (g h : ColPerm ν) (C : FullChamber Γ ν) :
      Rel (fr k Γ ν g (h • C) * fr k Γ ν h C) (fr k Γ ν (g * h) C)
  /-- Relabelling renames the variables. -/
  | relabel_poly (g : ColPerm ν) (C : FullChamber Γ ν) (f : PolyRing ν k) :
      Rel (fr k Γ ν g C * fp k Γ ν f) (fp k Γ ν (rename g.1 f) * fr k Γ ν g C)
  /-- Relabelling is compatible with steps. -/
  | relabel_step (g : ColPerm ν) (C C' : FullChamber Γ ν) :
      Rel (fr k Γ ν g C' * ft k Γ ν C C') (ft k Γ ν (g • C) (g • C') * fr k Γ ν g C)
  /-- The ghost bigon, Webster's relation (2). -/
  | wall_bigon (C C' : FullChamber Γ ν) (w : Wall Γ ν) (h : C.Adjacent C' (.inl w)) :
      Rel (ft k Γ ν C' C * ft k Γ ν C C') (fp k Γ ν w.factor * fe k Γ ν C)
  /-- The strand bigon, Webster's relation (3): `0` without a loop, `2 P_i ψ` with one. -/
  | diag_bigon (C C' : FullChamber Γ ν) (d : Diag ν) (h : C.Adjacent C' (.inr d)) :
      Rel (ft k Γ ν C' C * ft k Γ ν C C')
        (match Γ.loop d.fst.1 with
          | none => 0
          | some P => fp k Γ ν (-2 * loopFactor P (d.left C) (d.right C)) *
              fr k Γ ν d.refl C' * ft k Γ ν C C')
  /-- Polynomials commute with steps across walls. -/
  | wall_poly (C C' : FullChamber Γ ν) (w : Wall Γ ν) (h : C.Adjacent C' (.inl w))
      (f : PolyRing ν k) :
      Rel (ft k Γ ν C C' * fp k Γ ν f) (fp k Γ ν f * ft k Γ ν C C')
  /-- Polynomials past a step across a diagonal, Webster's relation (1). -/
  | diag_poly (C C' : FullChamber Γ ν) (d : Diag ν) (h : C.Adjacent C' (.inr d))
      (f : PolyRing ν k) :
      Rel (ft k Γ ν C C' * fp k Γ ν f - fp k Γ ν f * ft k Γ ν C C')
        (fp k Γ ν (stepFactor Γ (d.left C) (d.right C) f) * fr k Γ ν d.refl C)
  /-- Steps across independent hyperplanes commute. -/
  | square (C B B' D : FullChamber Γ ν) (h₁ h₂ : Hyp Γ ν) (hne : h₁ ≠ h₂)
      (hi : h₁.Independent h₂) (a₁ : C.Adjacent B h₁) (a₂ : B.Adjacent D h₂)
      (a₃ : C.Adjacent B' h₂) (a₄ : B'.Adjacent D h₁) :
      Rel (ft k Γ ν B D * ft k Γ ν C B) (ft k Γ ν B' D * ft k Γ ν C B')
  /-- Three walls through a codimension-two flat. -/
  | hex_walls (H : Hexagon Γ ν) (h₁ : H.h₁.isLeft) (h₂ : H.h₂.isLeft) (h₃ : H.h₃.isLeft) :
      Rel (H.gal₁ k Γ ν) (H.gal₂ k Γ ν)
  /-- A strand of one colour crossing two strands of another colour through the ghost of a
  third strand, the diagonal crossed in the middle: Webster's relations (4a), (4b). -/
  | hex_mid_diag (H : Hexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₁ : H.h₁ = .inl w)
      (h₂ : H.h₂ = .inr d) (h₃ : H.h₃ = .inl (w.comap d.refl))
      (hσ : H.A₀.1 (.inl w) ≠ H.A₀.1 (.inl (w.comap d.refl))) (hA : d.refl • H.A₀ = H.A₃) :
      Rel (H.gal₁ k Γ ν - H.gal₂ k Γ ν)
        (fp k Γ ν (stepFactor Γ (d.left H.A₁) (d.right H.A₁) w.factor) * fr k Γ ν d.refl H.A₀)
  /-- The same flat as `hex_mid_diag`, the diagonal crossed first or last: no correction. -/
  | hex_end_diag (H : Hexagon Γ ν) (w : Wall Γ ν) (d : Diag ν) (h₂ : H.h₂ = .inl w)
      (hd : (H.h₁ = .inr d ∧ H.h₃ = .inl (w.comap d.refl)) ∨
        (H.h₁ = .inl (w.comap d.refl) ∧ H.h₃ = .inr d))
      (hσ : H.A₀.1 (.inl w) = H.A₀.1 (.inl (w.comap d.refl))) :
      Rel (H.gal₁ k Γ ν) (H.gal₂ k Γ ν)
  /-- Three strands of one colour: the braid relation, with Webster's correction (4c) when
  there is a loop. -/
  | hex_diags (H : Hexagon Γ ν) (d₁ d₂ d₃ : Diag ν) (u v w : Strand ν) (h₁ : H.h₁ = .inr d₁)
      (h₂ : H.h₂ = .inr d₂) (h₃ : H.h₃ = .inr d₃) (j₁ : d₁.Joins u v) (j₂ : d₂.Joins u w)
      (j₃ : d₃.Joins v w) (hA : d₂.refl • H.A₀ = H.A₃) :
      Rel (H.gal₁ k Γ ν - H.gal₂ k Γ ν)
        (match Γ.loop u.1 with
          | none => 0
          | some P => H.loopCorrection k Γ ν d₁ d₂ d₃ u v w P)

end Rel

variable (k Γ ν) in
/-- The gallery algebra of the labelled arrangement. -/
def GalleryAlgebra : Type _ := RingQuot (Rel k Γ ν)

namespace GalleryAlgebra

noncomputable instance : Ring (GalleryAlgebra k Γ ν) := inferInstanceAs (Ring (RingQuot _))
noncomputable instance : Algebra k (GalleryAlgebra k Γ ν) :=
  inferInstanceAs (Algebra k (RingQuot _))

variable (k Γ ν) in
/-- The quotient map from the free algebra. -/
noncomputable def mk : FreeAlgebra k (Gen k Γ ν) →ₐ[k] GalleryAlgebra k Γ ν :=
  RingQuot.mkAlgHom k (Rel k Γ ν)

theorem mk_surjective : Function.Surjective (mk k Γ ν) :=
  RingQuot.mkAlgHom_surjective _ _

theorem rel {a b : FreeAlgebra k (Gen k Γ ν)} (h : Rel k Γ ν a b) : mk k Γ ν a = mk k Γ ν b :=
  RingQuot.mkAlgHom_rel k h

/-- The idempotent of a full chamber. -/
noncomputable def e (C : FullChamber Γ ν) : GalleryAlgebra k Γ ν := mk k Γ ν (fe k Γ ν C)

/-- A polynomial. -/
noncomputable def poly (f : PolyRing ν k) : GalleryAlgebra k Γ ν := mk k Γ ν (fp k Γ ν f)

/-- The step from `C` to `C'` (zero unless they are adjacent). -/
noncomputable def t (C C' : FullChamber Γ ν) : GalleryAlgebra k Γ ν := mk k Γ ν (ft k Γ ν C C')

/-- The relabelling `C → g • C`. -/
noncomputable def r (g : ColPerm ν) (C : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  mk k Γ ν (fr k Γ ν g C)

theorem e_mul_e (C D : FullChamber Γ ν) :
    (e C * e D : GalleryAlgebra k Γ ν) = if C = D then e C else 0 := by
  have := rel (Rel.idem_mul (k := k) (Γ := Γ) C D)
  rw [map_mul] at this
  rw [e, e, this]
  split_ifs <;> simp

theorem sum_e : ∑ C, (e C : GalleryAlgebra k Γ ν) = 1 := by
  have := rel (Rel.idem_sum (k := k) (Γ := Γ) (ν := ν))
  rw [map_sum, map_one] at this
  exact this

variable (k Γ ν) in
/-- Polynomials, as an algebra map into the gallery algebra. -/
noncomputable def polyHom : PolyRing ν k →ₐ[k] GalleryAlgebra k Γ ν where
  toFun := poly
  map_one' := by
    have := rel (Rel.poly_C (k := k) (Γ := Γ) (ν := ν) 1)
    rw [AlgHom.commutes] at this
    rw [poly, ← C_1, this, map_one]
  map_mul' f g := by
    have := rel (Rel.poly_mul (k := k) (Γ := Γ) f g)
    rw [map_mul] at this
    exact this
  map_zero' := by
    have := rel (Rel.poly_C (k := k) (Γ := Γ) (ν := ν) 0)
    rw [AlgHom.commutes] at this
    rw [poly, ← C_0, this, map_zero]
  map_add' f g := by
    have := rel (Rel.poly_add (k := k) (Γ := Γ) f g)
    rw [map_add] at this
    exact this
  commutes' c := by
    have := rel (Rel.poly_C (k := k) (Γ := Γ) (ν := ν) c)
    rw [AlgHom.commutes] at this
    rw [← this, algebraMap_eq]
    rfl

@[simp] theorem polyHom_apply (f : PolyRing ν k) : polyHom k Γ ν f = poly f := rfl

end GalleryAlgebra

end Categorification.WeightedKLR
