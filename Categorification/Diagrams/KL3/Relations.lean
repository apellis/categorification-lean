/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Basic
import Categorification.Diagrams.KLR.Basic
import Categorification.KLR.KL2.Datum

/-!
# The defining relations of the 2-category `U` of Khovanov–Lauda III

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1 (TeX label `def_Ucat`; the TeX source is the authoritative reading of the
pictures, which are `xy-pic` code). All diagrams are read bottom to top and are written in the
normal form of `Categorification.Diagrams.KL3.Basic`: a list of layers `(u, g, v)` (strands `u`,
a generator of shape `g`, strands `v`) with a fixed rightmost region. We write `E i = (true, i)`
(`up i`, an upward strand) and `F i = (false, i)` (`dn i`, a downward strand), and
`n = ⟨i, λ⟩ = RD.pair (RD.iY i) λ`.

## Diagrams

* Dots: `dots RD μ u l v m` (the `m`-fold composite of the dot on the strand `l`).
* Rotations of the upward dot (eq. (3.3), label `eq_cyclic_dot`): `rotDotR`, `rotDotL`.
* Rotations of the upward crossing by nested cups and caps (label `eq_cyclic_cross-gen`):
  `rotCrossR`, `rotCrossL`. The nested cups and caps are written out layer by layer, in the
  order of the units and counits of the composite biadjunctions of two-letter words used by the
  library (`biadjW_cons_left_unit`): outer cup first, inner cap first.
* The sideways crossings, *defined* in KL III by (labels `eq_crossl-gen`, `eq_crossr-gen`) as the
  first of the two displayed composites: `crossl RD i j μ : E_i F_j 1_μ ⟶ F_j E_i 1_μ` and
  `crossr RD i j μ : F_j E_i 1_μ ⟶ E_i F_j 1_μ`.
* Dotted bubbles with outer region `λ` (macros `cbub`, `ccbub`): the clockwise bubble
  `cwReal RD λ i m` (cup `1_λ → E F`, `m` dots on the downward strand, cap `E F → 1_λ`; the dot
  is drawn on the lower right arc) and the counterclockwise bubble `ccwReal RD λ i m` (cup
  `1_λ → F E`, `m` dots on the upward strand, cap `F E → 1_λ`; the dot is drawn on the upper
  right arc). The clockwise bubble with `m` dots has degree `2 d_i (m + 1 - n)`, the
  counterclockwise one `2 d_i (m + 1 + n)`.
* Fake bubbles (eq. `eq_infinite_Grass`): for a *label* `m ∈ ℤ`, `cwL RD k λ i m` and
  `ccwL RD k λ i m` are the bubbles with `m` dots when `m ≥ 0`. For `m < 0` of nonnegative degree
  they are the fake bubbles, defined inductively by the infinite Grassmannian relation
  `(∑_a ccw_a t^a)(∑_b cw_b t^b) = 1`, where `cw_b`, `ccw_a` are the bubbles of degree `2 d_i b`,
  `2 d_i a`, together with the convention that a bubble of degree zero is `1` (this is the
  degree-zero case of the Grassmannian relation, using the axiom that the real degree-zero
  bubble is `1`, and for `n = 0` it is KL III's "additional condition"). Fake bubbles occur only
  when the corresponding opposite bubbles in lower degree are real, so the recursion
  (`grassInv`) only uses real bubbles. Products of bubbles are composites in the free linear
  category; in `U` all endomorphisms of `1_λ` commute (interchange law), so their order is
  immaterial.

## Relations (`Rel`, `relation`)

With `λ` the outer region (KL III's label) unless stated otherwise:

* biadjointness (eqs. (3.1), (3.2), label `eq_biadjoint1`): the four zigzag relations are those
  of the pivotal extension (`Presentation.pivotal`); see `Categorification.Diagrams.KL3.Presentation`.
* `cycDotR`, `cycDotL` (eq. (3.3)): the downward dot equals both rotations of the upward dot.
* `cwNeg`, `ccwNeg` (eq. (3.4), label `eq_positivity_bubbles`): a clockwise bubble with
  `α < n - 1` dots and a counterclockwise bubble with `α < -n - 1` dots vanish.
* `cwOne`, `ccwOne`: the bubbles of degree zero equal `1` (`n ≥ 1`, resp. `n ≤ -1`).
* `curlR`, `curlL` (first display of item iv)): an upward strand with a curl on the right (left)
  is a sum of dotted strands times fake bubbles.
* `decompEF`, `decompFE` (label `eq_ident_decomp`): the identity of `E F 1_λ` (of `F E 1_λ`) is
  minus a double sideways crossing plus a double sum of cap–bubble–cup terms.
* `cycCrossR`, `cycCrossL` (label `eq_cyclic_cross-gen`, all `i, j`; for `i = j` it is listed
  among the `sl₂` relations): the downward crossing equals both rotations of the upward
  crossing.
* `downupEF`, `downupFE` (label `eq_downup_ij-gen`, `i ≠ j`): the double sideways crossings are
  identities.
* `klr μ r` (labels `eq_nil_rels`, `eq_nil_dotslide`, `eq_r2_ij-gen`, `eq_dot_slide_ij-gen`,
  `eq_r3_easy-gen`, `eq_r3_hard-gen`): the relations of `R(ν)` on upward strands, i.e. the
  relations `KLR.Diagram.relation k (klQ2 k C) r` of the diagrammatic KLR presentation
  (`Categorification.Diagrams.KLR.Basic`) with the KL II polynomials
  `Q_ij = u^{d_ij} + v^{d_ji}` (`KLR.klQ2`), placed on upward strands with rightmost region `μ`
  (`upLin`). With `d_ij = -⟨i, j_X⟩` this is exactly the list of KL III: `ψ² = 0` on `ii`,
  `ψ² = 1` or `x^{d_ij} + x^{d_ji}` on `ij`, the nilHecke and `i ≠ j` dot slides, and the
  triple-crossing relations with `∑_{a < d_ij} x_1^a x_3^{d_ij - 1 - a}`.

Sums follow KL III's convention: `∑_{f=0}^{α}` is empty for `α < 0`.

The only reading of a picture that is not forced by the TeX is the position of a dot on a bubble
or a cup/cap (the pictures are isotopy classes; KL III imposes cyclicity so that isotopic
diagrams agree). We place dots where the TeX draws them.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y)

/-- An upward strand `E_i`. -/
abbrev up (i : I) : Letter I := (true, i)

/-- A downward strand `F_i`. -/
abbrev dn (i : I) : Letter I := (false, i)

/-- `⟨i, λ⟩`. -/
abbrev ip (i : I) (lam : X) : ℤ := RD.pair (RD.iY i) lam

/-! ## Rotations of the upward dot (eq. (3.3)) -/

/-- The downward dot on `F_i` with rightmost region `μ` (KL III's downward dot
`Udown_{i, μ - i_X}`). -/
def downDot (i : I) (μ : X) : ob RD μ [dn i] ⟶ ob RD μ [dn i] :=
  mkD RD μ [([], .dot (dn i), [])] ⟨rfl, rfl⟩

/-- The upward dot rotated with the cup `1 → E F` on the right and the cap `F E → 1` on the left
(left-hand picture of eq. (3.3)). -/
def rotDotR (i : I) (μ : X) : ob RD μ [dn i] ⟶ ob RD μ [dn i] :=
  mkD RD μ [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])]
    ⟨rfl, rfl, rfl, rfl⟩

/-- The upward dot rotated with the cup `1 → F E` on the left and the cap `E F → 1` on the right
(right-hand picture of eq. (3.3)). -/
def rotDotL (i : I) (μ : X) : ob RD μ [dn i] ⟶ ob RD μ [dn i] :=
  mkD RD μ [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])]
    ⟨rfl, rfl, rfl, rfl⟩

/-! ## Rotations of the upward crossing (eq. `eq_cyclic_cross-gen`) -/

/-- The downward crossing `F_j F_i 1_μ ⟶ F_i F_j 1_μ`. -/
def downCross (j i : I) (μ : X) : ob RD μ [dn j, dn i] ⟶ ob RD μ [dn i, dn j] :=
  mkD RD μ [([], .cross false j i, [])] ⟨rfl, rfl⟩

/-- The upward crossing `E_j E_i ⟶ E_i E_j` rotated by nested cups on the right and nested caps
on the left (left-hand picture of `eq_cyclic_cross-gen`). -/
def rotCrossR (j i : I) (μ : X) : ob RD μ [dn j, dn i] ⟶ ob RD μ [dn i, dn j] :=
  mkD RD μ [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
      ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
      ([], .cap (up j), [dn i, dn j])]
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The upward crossing `E_j E_i ⟶ E_i E_j` rotated by nested cups on the left and nested caps
on the right (right-hand picture of `eq_cyclic_cross-gen`). -/
def rotCrossL (j i : I) (μ : X) : ob RD μ [dn j, dn i] ⟶ ob RD μ [dn i, dn j] :=
  mkD RD μ [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
      ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
      ([dn i, dn j], .cap (dn i), [])]
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Sideways crossings (eqs. `eq_crossl-gen`, `eq_crossr-gen`) -/

/-- The sideways crossing `E_i F_j 1_μ ⟶ F_j E_i 1_μ` (upward `i` from bottom left to top right,
downward `j` from top left to bottom right), defined as the upward crossing `E_j E_i ⟶ E_i E_j`
with a cup `1 → F_j E_j` on the bottom left and a cap `E_j F_j → 1` on the top right. -/
def crossl (i j : I) (μ : X) : ob RD μ [up i, dn j] ⟶ ob RD μ [dn j, up i] :=
  mkD RD μ [([], .cup (dn j), [up i, dn j]), ([dn j], .cross true j i, [dn j]),
      ([dn j, up i], .cap (dn j), [])]
    ⟨rfl, rfl, rfl, rfl⟩

/-- The sideways crossing `F_j E_i 1_μ ⟶ E_i F_j 1_μ` (upward `i` from bottom right to top left,
downward `j` from top right to bottom left), defined as the upward crossing `E_i E_j ⟶ E_j E_i`
with a cup `1 → E_j F_j` on the bottom right and a cap `F_j E_j → 1` on the top left. -/
def crossr (i j : I) (μ : X) : ob RD μ [dn j, up i] ⟶ ob RD μ [up i, dn j] :=
  mkD RD μ [([dn j, up i], .cup (up j), []), ([dn j], .cross true i j, [dn j]),
      ([], .cap (up j), [up i, dn j])]
    ⟨rfl, rfl, rfl, rfl⟩

/-! ## Bubbles -/

/-- The clockwise bubble with `m` dots in the region `λ` (macro `cbub`): the cup `1_λ → E_i F_i`,
`m` dots on the downward strand, the cap `E_i F_i → 1_λ`. -/
def cwReal (lam : X) (i : I) (m : ℕ) : ob RD lam [] ⟶ ob RD lam [] :=
  mkD RD lam ([([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []) ++
      [([], .cap (dn i), [])])
    (by
      refine SChain.append (SChain.append (t' := [up i, dn i]) ?_
        (SChain.replicate m [up i] (dn i) [])) ?_ <;> exact ⟨rfl, rfl⟩)

/-- The counterclockwise bubble with `m` dots in the region `λ` (macro `ccbub`): the cup
`1_λ → F_i E_i`, `m` dots on the upward strand, the cap `F_i E_i → 1_λ`. -/
def ccwReal (lam : X) (i : I) (m : ℕ) : ob RD lam [] ⟶ ob RD lam [] :=
  mkD RD lam ([([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), []) ++
      [([], .cap (up i), [])])
    (by
      refine SChain.append (SChain.append (t' := [dn i, up i]) ?_
        (SChain.replicate m [dn i] (up i) [])) ?_ <;> exact ⟨rfl, rfl⟩)

/-- The solution of `(∑_a c_a t^a)(∑_b x_b t^b) = 1` with `c_0 = 1`: `x_0 = 1`,
`x_{k+1} = -∑_{a ≤ k} c_{a+1} x_{k-a}`. -/
def grassInv {A : Type*} [Ring A] (c : ℕ → A) : ℕ → A
  | 0 => 1
  | k + 1 => -∑ a : Fin (k + 1), c (a.1 + 1) * grassInv c (k - a.1)
decreasing_by all_goals omega

theorem grassInv_zero {A : Type*} [Ring A] (c : ℕ → A) : grassInv c 0 = 1 := by
  rw [grassInv]

theorem grassInv_succ {A : Type*} [Ring A] (c : ℕ → A) (k : ℕ) :
    grassInv c (k + 1) = -∑ a : Fin (k + 1), c (a.1 + 1) * grassInv c (k - a.1) := by
  rw [grassInv]

variable (k : Type w) [CommRing k]

/-- Linear combinations of diagrams from `a` to `a`, as a ring. -/
abbrev LEnd (a : Obj (psig RD)) : Type _ := End (Free.of k a)

/-- The real clockwise bubble with label `m`, or `0` if `m < 0`. -/
def cwR (lam : X) (i : I) (m : ℤ) : LEnd RD k (ob RD lam []) :=
  if 0 ≤ m then LinDiagram.of (cwReal RD lam i m.toNat) else 0

/-- The real counterclockwise bubble with label `m`, or `0` if `m < 0`. -/
def ccwR (lam : X) (i : I) (m : ℤ) : LEnd RD k (ob RD lam []) :=
  if 0 ≤ m then LinDiagram.of (ccwReal RD lam i m.toNat) else 0

/-- The clockwise bubble with label `m ∈ ℤ` in the region `λ`: the real bubble with `m` dots if
`m ≥ 0`; if `m < 0` and its degree `2 d_i (m + 1 - n)` is nonnegative, the fake bubble of
degree index `m + 1 - n`, defined by the infinite Grassmannian relation from the real
counterclockwise bubbles (label `-n - 1 + a` for degree index `a`); `0` otherwise. -/
def cwL (lam : X) (i : I) (m : ℤ) : LEnd RD k (ob RD lam []) :=
  if 0 ≤ m then LinDiagram.of (cwReal RD lam i m.toNat)
  else if 0 ≤ m + 1 - ip RD i lam then
    grassInv (fun a => ccwR RD k lam i (-ip RD i lam - 1 + a)) (m + 1 - ip RD i lam).toNat
  else 0

/-- The counterclockwise bubble with label `m ∈ ℤ` in the region `λ`: the real bubble with `m`
dots if `m ≥ 0`; if `m < 0` and its degree `2 d_i (m + 1 + n)` is nonnegative, the fake bubble
of degree index `m + 1 + n`, defined by the infinite Grassmannian relation from the real
clockwise bubbles (label `n - 1 + b` for degree index `b`); `0` otherwise. -/
def ccwL (lam : X) (i : I) (m : ℤ) : LEnd RD k (ob RD lam []) :=
  if 0 ≤ m then LinDiagram.of (ccwReal RD lam i m.toNat)
  else if 0 ≤ m + 1 + ip RD i lam then
    grassInv (fun b => cwR RD k lam i (ip RD i lam - 1 + b)) (m + 1 + ip RD i lam).toNat
  else 0

/-! ## Bubbles next to strands -/

theorem whiskerOK_right (lam : X) (t : List (Letter I)) :
    (ob RD lam []).WhiskerOK (ob RD lam t) [] :=
  ⟨ok_wd RD lam t, endR_wd RD lam t, trivial⟩

theorem whisker_right_eq (lam : X) (t : List (Letter I)) :
    (ob RD lam []).whisker (ob RD lam t) [] = ob RD lam t :=
  Obj.ext rfl (by simp [Obj.whisker])

theorem whiskerOK_left (μ : X) (t : List (Letter I)) :
    (ob RD (wt RD μ t) []).WhiskerOK (ob RD (wt RD μ t) []) (wd RD μ t) :=
  ⟨trivial, rfl, ok_wd RD μ t⟩

theorem whisker_left_eq (μ : X) (t : List (Letter I)) :
    (ob RD (wt RD μ t) []).whisker (ob RD (wt RD μ t) []) (wd RD μ t) = ob RD μ t :=
  Obj.ext rfl (by simp [Obj.whisker])

/-- An endomorphism of `1_λ` placed to the right of the strands `t` (rightmost region `λ`). -/
def bubR (lam : X) (t : List (Letter I)) (b : LEnd RD k (ob RD lam [])) : LEnd RD k (ob RD lam t) :=
  LinDiagram.cast (LinDiagram.whisker b (ob RD lam t) [] (whiskerOK_right RD lam t))
    (whisker_right_eq RD lam t) (whisker_right_eq RD lam t)

/-- An endomorphism of `1_{μ + t_X}` placed to the left of the strands `t` (rightmost region
`μ`). -/
def bubL (μ : X) (t : List (Letter I)) (b : LEnd RD k (ob RD (wt RD μ t) [])) :
    LEnd RD k (ob RD μ t) :=
  LinDiagram.cast (LinDiagram.whisker b (ob RD (wt RD μ t) []) (wd RD μ t) (whiskerOK_left RD μ t))
    (whisker_left_eq RD μ t) (whisker_left_eq RD μ t)

/-! ## Curls (item iv), first display) -/

/-- An upward strand `E_i` with a curl on its right, outer region `λ` on the right. -/
def curlR (i : I) (lam : X) : ob RD lam [up i] ⟶ ob RD lam [up i] :=
  mkD RD lam [([up i], .cup (up i), []), ([], .cross true i i, [dn i]), ([up i], .cap (dn i), [])]
    ⟨rfl, rfl, rfl, rfl⟩

/-- An upward strand `E_i` with a curl on its left; the outer region `λ = μ + i_X` is on the
left. -/
def curlL (i : I) (μ : X) : ob RD μ [up i] ⟶ ob RD μ [up i] :=
  mkD RD μ [([], .cup (dn i), [up i]), ([dn i], .cross true i i, []), ([], .cap (up i), [up i])]
    ⟨rfl, rfl, rfl, rfl⟩

/-- Right-hand side of the right curl relation:
`-∑_{f=0}^{-n} (E_i with -n - f dots) ⊗ (clockwise bubble with label n - 1 + f)`. -/
def curlRHS (i : I) (lam : X) : LinDiagram k (ob RD lam [up i]) (ob RD lam [up i]) :=
  -∑ f ∈ Finset.range (-ip RD i lam + 1).toNat,
    bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + f)) ≫
      LinDiagram.of (dots RD lam [] (up i) [] (-ip RD i lam - f).toNat)

/-- Right-hand side of the left curl relation (`λ = μ + i_X`):
`∑_{g=0}^{n} (counterclockwise bubble with label -n - 1 + g) ⊗ (E_i with n - g dots)`. -/
def curlLHS (i : I) (μ : X) : LinDiagram k (ob RD μ [up i]) (ob RD μ [up i]) :=
  ∑ g ∈ Finset.range (ip RD i (wt RD μ [up i]) + 1).toNat,
    bubL RD k μ [up i] (ccwL RD k (wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)) ≫
      LinDiagram.of (dots RD μ [] (up i) [] (ip RD i (wt RD μ [up i]) - g).toNat)

/-! ## The decompositions of `1_{EF1_λ}` and `1_{FE1_λ}` (eq. `eq_ident_decomp`) -/

/-- `m` dots on the upward strand of `E_i F_i`, then the cap `E_i F_i → 1_λ`. -/
def dotCapEF (lam : X) (i : I) (m : ℕ) : ob RD lam [up i, dn i] ⟶ ob RD lam [] :=
  mkD RD lam (List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])])
    (by refine SChain.append (SChain.replicate m [] (up i) [dn i]) ?_; exact ⟨rfl, rfl⟩)

/-- The cup `1_λ → E_i F_i`, then `m` dots on the downward strand. -/
def cupDotEF (lam : X) (i : I) (m : ℕ) : ob RD lam [] ⟶ ob RD lam [up i, dn i] :=
  mkD RD lam ([([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []))
    (by
      refine SChain.append (t' := [up i, dn i]) ?_ (SChain.replicate m [up i] (dn i) [])
      exact ⟨rfl, rfl⟩)

/-- `m` dots on the downward strand of `F_i E_i`, then the cap `F_i E_i → 1_λ`. -/
def dotCapFE (lam : X) (i : I) (m : ℕ) : ob RD lam [dn i, up i] ⟶ ob RD lam [] :=
  mkD RD lam (List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])])
    (by refine SChain.append (SChain.replicate m [] (dn i) [up i]) ?_; exact ⟨rfl, rfl⟩)

/-- The cup `1_λ → F_i E_i`, then `m` dots on the upward strand. -/
def cupDotFE (lam : X) (i : I) (m : ℕ) : ob RD lam [] ⟶ ob RD lam [dn i, up i] :=
  mkD RD lam ([([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), []))
    (by
      refine SChain.append (t' := [dn i, up i]) ?_ (SChain.replicate m [dn i] (up i) [])
      exact ⟨rfl, rfl⟩)

/-- The sum in the decomposition of `1_{E_i F_i 1_λ}`:
`∑_{f=0}^{n-1} ∑_{g=0}^{f} (cap with f - g dots) (ccw bubble with label -n-1+g)
(cup with n - 1 - f dots)`. -/
def decompEFSum (i : I) (lam : X) :
    LinDiagram k (ob RD lam [up i, dn i]) (ob RD lam [up i, dn i]) :=
  ∑ f ∈ Finset.range (ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
    LinDiagram.of (dotCapEF RD lam i (f - g)) ≫ ccwL RD k lam i (-ip RD i lam - 1 + g) ≫
      LinDiagram.of (cupDotEF RD lam i ((ip RD i lam).toNat - 1 - f))

/-- The sum in the decomposition of `1_{F_i E_i 1_λ}`:
`∑_{f=0}^{-n-1} ∑_{g=0}^{f} (cap with f - g dots) (cw bubble with label n-1+g)
(cup with -n - 1 - f dots)`. -/
def decompFESum (i : I) (lam : X) :
    LinDiagram k (ob RD lam [dn i, up i]) (ob RD lam [dn i, up i]) :=
  ∑ f ∈ Finset.range (-ip RD i lam).toNat, ∑ g ∈ Finset.range (f + 1),
    LinDiagram.of (dotCapFE RD lam i (f - g)) ≫ cwL RD k lam i (ip RD i lam - 1 + g) ≫
      LinDiagram.of (cupDotFE RD lam i ((-ip RD i lam).toNat - 1 - f))

/-! ## `R(ν)` on upward strands -/

/-- Upward strands of the given colours. -/
abbrev ups (l : List I) : List (Letter I) := l.map up

/-- The shape of a KLR generator, on upward strands. -/
def upShape : KLR.Diagram.Gen I → Shape I
  | .dot c => .dot (up c)
  | .cross c d => .cross true c d

theorem upShape_dom (g : KLR.Diagram.Gen I) : (upShape g).dom = ups g.dom := by
  cases g <;> rfl

theorem upShape_cod (g : KLR.Diagram.Gen I) : (upShape g).cod = ups g.cod := by
  cases g <;> rfl

/-- A KLR layer placed on upward strands with rightmost region `μ`. -/
def upLay (μ : X) (L : Layer (KLR.Diagram.sig I)) : Layer (psig RD) :=
  lay RD μ (ups L.left) (upShape L.gen) (ups L.right)

theorem upLay_dom (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    (upLay RD μ L).dom = ob RD μ (ups L.dom.word) := by
  rw [upLay, lay_dom, upShape_dom]
  simp [List.map_append]

theorem upLay_cod (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    (upLay RD μ L).cod = ob RD μ (ups L.cod.word) := by
  rw [upLay, lay_cod, upShape_cod]
  simp [List.map_append]

theorem chain_up (μ : X) {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) :
    Chain (ob RD μ (ups a.word)) (ls.map (upLay RD μ)) (ob RD μ (ups b.word)) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨lay_valid RD _ _ _ _, upLay_dom RD μ L, by rw [upLay_cod]; exact ih hc⟩

/-- A KLR diagram placed on upward strands with rightmost region `μ`. -/
def upDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    ob RD μ (ups a.word) ⟶ ob RD μ (ups b.word) :=
  Diagram.mk ((Diagram.layers d).map (upLay RD μ)) (chain_up RD μ (Diagram.chain d))

@[simp] theorem layers_upDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    Diagram.layers (upDiag RD μ d) = (Diagram.layers d).map (upLay RD μ) := rfl

/-- A linear combination of KLR diagrams placed on upward strands with rightmost region `μ`. -/
def upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    LinDiagram k (ob RD μ (ups a.word)) (ob RD μ (ups b.word)) :=
  Finsupp.mapDomain (upDiag RD μ) f

/-! ## The relations -/

/-- The relations of Definition 3.1 other than the zigzag relations (see the module docstring).
The weight parameter is KL III's `λ` (the outer region, on the right unless stated otherwise);
for `curlL` it is the rightmost region `μ`, KL III's `λ` being `μ + i_X`; for `cycDot*`,
`cycCross*`, `downup*` and `klr` it is the rightmost region. -/
inductive Rel : Type (max u v)
  | cycDotR (i : I) (μ : X)
  | cycDotL (i : I) (μ : X)
  | cwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < ip RD i lam - 1)
  | ccwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -ip RD i lam - 1)
  | cwOne (i : I) (lam : X) (h : 1 ≤ ip RD i lam)
  | ccwOne (i : I) (lam : X) (h : ip RD i lam ≤ -1)
  | curlR (i : I) (lam : X)
  | curlL (i : I) (μ : X)
  | decompEF (i : I) (lam : X)
  | decompFE (i : I) (lam : X)
  | cycCrossR (j i : I) (μ : X)
  | cycCrossL (j i : I) (μ : X)
  | downupEF (i j : I) (h : i ≠ j) (μ : X)
  | downupFE (i j : I) (h : i ≠ j) (μ : X)
  | klr (μ : X) (r : KLR.Diagram.Rel I)

variable {RD}

/-- Bottom boundary of a relation. -/
def Rel.dom : Rel RD → Obj (psig RD)
  | .cycDotR i μ => ob RD μ [dn i]
  | .cycDotL i μ => ob RD μ [dn i]
  | .cwNeg _ lam _ _ => ob RD lam []
  | .ccwNeg _ lam _ _ => ob RD lam []
  | .cwOne _ lam _ => ob RD lam []
  | .ccwOne _ lam _ => ob RD lam []
  | .curlR i lam => ob RD lam [up i]
  | .curlL i μ => ob RD μ [up i]
  | .decompEF i lam => ob RD lam [up i, dn i]
  | .decompFE i lam => ob RD lam [dn i, up i]
  | .cycCrossR j i μ => ob RD μ [dn j, dn i]
  | .cycCrossL j i μ => ob RD μ [dn j, dn i]
  | .downupEF i j _ μ => ob RD μ [up i, dn j]
  | .downupFE i j _ μ => ob RD μ [dn i, up j]
  | .klr μ r => ob RD μ (ups (KLR.Diagram.Rel.dom r).word)

/-- Top boundary of a relation. -/
def Rel.cod : Rel RD → Obj (psig RD)
  | .cycDotR i μ => ob RD μ [dn i]
  | .cycDotL i μ => ob RD μ [dn i]
  | .cwNeg _ lam _ _ => ob RD lam []
  | .ccwNeg _ lam _ _ => ob RD lam []
  | .cwOne _ lam _ => ob RD lam []
  | .ccwOne _ lam _ => ob RD lam []
  | .curlR i lam => ob RD lam [up i]
  | .curlL i μ => ob RD μ [up i]
  | .decompEF i lam => ob RD lam [up i, dn i]
  | .decompFE i lam => ob RD lam [dn i, up i]
  | .cycCrossR j i μ => ob RD μ [dn i, dn j]
  | .cycCrossL j i μ => ob RD μ [dn i, dn j]
  | .downupEF i j _ μ => ob RD μ [up i, dn j]
  | .downupFE i j _ μ => ob RD μ [dn i, up j]
  | .klr μ r => ob RD μ (ups (KLR.Diagram.Rel.cod r).word)

open LinDiagram in
/-- The relations, as linear combinations of diagrams that are set to zero. -/
def relation : (r : Rel RD) → LinDiagram k r.dom r.cod
  | .cycDotR i μ => of (rotDotR RD i μ) - of (downDot RD i μ)
  | .cycDotL i μ => of (rotDotL RD i μ) - of (downDot RD i μ)
  | .cwNeg i lam α _ => of (cwReal RD lam i α)
  | .ccwNeg i lam α _ => of (ccwReal RD lam i α)
  | .cwOne i lam _ => of (cwReal RD lam i (ip RD i lam - 1).toNat) - of (𝟙 _)
  | .ccwOne i lam _ => of (ccwReal RD lam i (-ip RD i lam - 1).toNat) - of (𝟙 _)
  | .curlR i lam => of (curlR RD i lam) - curlRHS RD k i lam
  | .curlL i μ => of (curlL RD i μ) - curlLHS RD k i μ
  | .decompEF i lam => of (𝟙 _) + of (crossl RD i i lam ≫ crossr RD i i lam) - decompEFSum RD k i lam
  | .decompFE i lam => of (𝟙 _) + of (crossr RD i i lam ≫ crossl RD i i lam) - decompFESum RD k i lam
  | .cycCrossR j i μ => of (rotCrossR RD j i μ) - of (downCross RD j i μ)
  | .cycCrossL j i μ => of (rotCrossL RD j i μ) - of (downCross RD j i μ)
  | .downupEF i j _ μ => of (crossl RD i j μ ≫ crossr RD i j μ) - of (𝟙 _)
  | .downupFE i j _ μ => of (crossr RD j i μ ≫ crossl RD j i μ) - of (𝟙 _)
  | .klr μ r => upLin RD k μ (KLR.Diagram.relation k (KLR.klQ2 k C) r)

end Categorification.KL3.Diagram
