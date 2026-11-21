/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigma
import StringDiagrams.LayerMap.Generators

/-!
# The localization `U′` of the 2-category `U` (Webster, Definition 3.28)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.6,
Definition 3.28: `U′` is the localization of `U` obtained by inverting the dot `y : F_i → F_i`,
modulo the identification of fake bubbles with honest bubbles carrying negative numbers of
dots. As Webster notes after the definition, since fake bubbles are defined by the infinite
Grassmannian relation, this is the same as imposing that bubbles of negative degree vanish and
that the Grassmannian relation holds with all bubbles read honestly.

(§3.6 of v2 is absent from arXiv:1309.3796v3; see `docs/WeightedKLR/tensor-product-roadmap.md`
for the status of Lemma 3.29 and Propositions 3.30, 3.31.)

## Encoding

* `lsig RD`: the signature of `U` (`psig RD`) with one more generator for every downward colour
  `⟨F_i, μ⟩`, the inverse downward dot, with the boundaries of the downward dot.
* `incl RD : SigMap (psig RD) (lsig RD)`: the inclusion; it fixes regions and strands.
* `invDot RD μ u i v`: the inverse dot on the strand `F_i` between the strands `u` and `v`.
* `presLoc RD k`: the relations of `U` transported along `incl`, the two relations saying that
  `invDot` is a two-sided inverse of the downward dot, and for every label `m < 0` the relations
  saying that the honest clockwise (counterclockwise) bubble with `-m` inverse dots, placed on
  its downward arc, equals `cwL` (`ccwL`): the fake bubble when its degree is nonnegative and
  `0` otherwise.

Inverting the downward dot also inverts the upward dot, its rotation (KL III eq. (3.3)), so this
is the localization at `y` for both orientations. On a bubble the position of a dot is
immaterial by cyclicity, so placing the inverse dots on the downward arc is no choice.

## Main definitions

* `lsig`, `incl`, `invDot`, `cwNegHonest`, `ccwNegHonest`, `presLoc` (Definition 3.28).
* `toLoc RD k : (pres RD k).Presented ⥤ (presLoc RD k).Presented`, the localization functor.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-- The signature of `U′`: the generators of `U` and, for every `i` and `μ`, an inverse downward
dot on the colour `⟨F_i, μ⟩`. -/
def lsig : Signature.{v, max u v, max u v} where
  Region := X
  Colour := Col I X
  colourSrc := (psig RD).colourSrc
  colourTgt := (psig RD).colourTgt
  Gen := (psig RD).Gen ⊕ (I × X)
  dom
    | .inl g => (psig RD).dom g
    | .inr p => (psig RD).dom (.gen (.dot ⟨dn p.1, p.2⟩))
  cod
    | .inl g => (psig RD).cod g
    | .inr p => (psig RD).cod (.gen (.dot ⟨dn p.1, p.2⟩))
  left
    | .inl g => (psig RD).left g
    | .inr p => (psig RD).left (.gen (.dot ⟨dn p.1, p.2⟩))
  right
    | .inl g => (psig RD).right g
    | .inr p => (psig RD).right (.gen (.dot ⟨dn p.1, p.2⟩))

/-- The inclusion of the signature of `U` into that of `U′`. -/
def incl : SigMap (psig RD) (lsig RD) where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  word := id
  word_eq w := (List.map_id w).symm
  gen := Sum.inl
  dom _ := rfl
  cod _ := rfl
  left _ := rfl
  right _ := rfl

/-- The layer of the inverse dot on `F_i` between `u` and `v`, rightmost region `μ`. -/
def invDotLayer (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) : Layer (lsig RD) :=
  ⟨(wt RD μ (u ++ [dn i] ++ v) : X), wd RD (wt RD μ ([dn i] ++ v)) u, .inr (i, wt RD μ v),
    wd RD μ v⟩

theorem invDotLayer_valid (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (invDotLayer RD μ u i v).Valid := by
  have h := (incl RD).layer_valid (lay_valid RD μ u (.dot (dn i)) v)
  exact ⟨h.left_ok, h.left_end, h.dom_ok, h.dom_end, h.cod_ok, h.cod_end, h.right_ok⟩

theorem invDotLayer_dom (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (invDotLayer RD μ u i v).dom = (incl RD).obj (ob RD μ (u ++ [dn i] ++ v)) :=
  ((incl RD).toLayerMap.dom_eq (lay_valid RD μ u (.dot (dn i)) v)).trans
    (congrArg (incl RD).obj (lay_dom RD μ u (.dot (dn i)) v))

theorem invDotLayer_cod (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (invDotLayer RD μ u i v).cod = (incl RD).obj (ob RD μ (u ++ [dn i] ++ v)) :=
  ((incl RD).toLayerMap.cod_eq (lay_valid RD μ u (.dot (dn i)) v)).trans
    (congrArg (incl RD).obj (lay_cod RD μ u (.dot (dn i)) v))

/-- The inverse dot on the strand `F_i` between the strands `u` and `v`, with rightmost region
`μ`. -/
def invDot (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (incl RD).obj (ob RD μ (u ++ [dn i] ++ v)) ⟶ (incl RD).obj (ob RD μ (u ++ [dn i] ++ v)) :=
  Diagram.mk [invDotLayer RD μ u i v] ⟨invDotLayer_valid RD μ u i v, invDotLayer_dom RD μ u i v, invDotLayer_cod RD μ u i v⟩

/-- The inverse dot on a single strand `F_i` with right region `μ`. -/
def invDotF (i : I) (μ : X) : (incl RD).obj (ob RD μ [dn i]) ⟶ (incl RD).obj (ob RD μ [dn i]) :=
  invDot RD μ [] i []

variable (k : Type w) [CommRing k]

/-- The inclusion on linear combinations of diagrams. -/
def inclLin {a b : Obj (psig RD)} :
    LinDiagram k a b →ₗ[k] LinDiagram k ((incl RD).obj a) ((incl RD).obj b) :=
  Finsupp.lmapDomain k k (incl RD).toLayerMap.map

/-- The image of a diagram of `U`. -/
abbrev inclD {a b : Obj (psig RD)} (d : a ⟶ b) : (incl RD).obj a ⟶ (incl RD).obj b :=
  (incl RD).toLayerMap.map d

/-- The `n`-fold composite of an endomorphism. -/
def iterComp {𝒞 : Type*} [Category 𝒞] {a : 𝒞} (f : a ⟶ a) : ℕ → (a ⟶ a)
  | 0 => 𝟙 a
  | n + 1 => f ≫ iterComp f n

/-- The cup `1_λ → E_i F_i`. -/
def cupEF (lam : X) (i : I) : ob RD lam [] ⟶ ob RD lam [up i, dn i] :=
  mkD RD lam [([], .cup (up i), [])] ⟨rfl, rfl⟩

/-- The cap `E_i F_i → 1_λ`. -/
def capEF (lam : X) (i : I) : ob RD lam [up i, dn i] ⟶ ob RD lam [] :=
  mkD RD lam [([], .cap (dn i), [])] ⟨rfl, rfl⟩

/-- The cup `1_λ → F_i E_i`. -/
def cupFE (lam : X) (i : I) : ob RD lam [] ⟶ ob RD lam [dn i, up i] :=
  mkD RD lam [([], .cup (dn i), [])] ⟨rfl, rfl⟩

/-- The cap `F_i E_i → 1_λ`. -/
def capFE (lam : X) (i : I) : ob RD lam [dn i, up i] ⟶ ob RD lam [] :=
  mkD RD lam [([], .cap (up i), [])] ⟨rfl, rfl⟩

/-- The honest clockwise bubble in the region `λ` with `n` inverse dots on its downward arc,
i.e. with `-n` dots. -/
def cwNegHonest (lam : X) (i : I) (n : ℕ) :
    (incl RD).obj (ob RD lam []) ⟶ (incl RD).obj (ob RD lam []) :=
  inclD RD (cupEF RD lam i) ≫ iterComp (invDot RD lam [up i] i []) n ≫ inclD RD (capEF RD lam i)

/-- The honest counterclockwise bubble in the region `λ` with `n` inverse dots on its downward
arc, i.e. with `-n` dots. -/
def ccwNegHonest (lam : X) (i : I) (n : ℕ) :
    (incl RD).obj (ob RD lam []) ⟶ (incl RD).obj (ob RD lam []) :=
  inclD RD (cupFE RD lam i) ≫ iterComp (invDot RD lam [] i [up i]) n ≫ inclD RD (capFE RD lam i)

/-- The relations of `U′` beyond those of `U`. -/
inductive LocRel (I : Type u) (X : Type v)
  /-- `y⁻¹ y = 1` on `F_i`. -/
  | invLeft (i : I) (μ : X)
  /-- `y y⁻¹ = 1` on `F_i`. -/
  | invRight (i : I) (μ : X)
  /-- The honest clockwise bubble with `-(n+1)` dots is the fake bubble (or `0`). -/
  | cw (lam : X) (i : I) (n : ℕ)
  /-- The honest counterclockwise bubble with `-(n+1)` dots is the fake bubble (or `0`). -/
  | ccw (lam : X) (i : I) (n : ℕ)

/-- Boundary of a localization relation. -/
def LocRel.obj : LocRel I X → Obj (lsig RD)
  | .invLeft i μ => (incl RD).obj (ob RD μ [dn i])
  | .invRight i μ => (incl RD).obj (ob RD μ [dn i])
  | .cw lam _ _ => (incl RD).obj (ob RD lam [])
  | .ccw lam _ _ => (incl RD).obj (ob RD lam [])

/-- The localization relations. -/
def locRelation : (r : LocRel I X) → LinDiagram k (r.obj RD) (r.obj RD)
  | .invLeft i μ =>
      LinDiagram.of (invDotF RD i μ ≫ inclD RD (downDot RD i μ)) - 𝟙 _
  | .invRight i μ =>
      LinDiagram.of (inclD RD (downDot RD i μ) ≫ invDotF RD i μ) - 𝟙 _
  | .cw lam i n => LinDiagram.of (cwNegHonest RD lam i (n + 1)) -
      inclLin RD k (cwL RD k lam i (-((n : ℤ) + 1)))
  | .ccw lam i n => LinDiagram.of (ccwNegHonest RD lam i (n + 1)) -
      inclLin RD k (ccwL RD k lam i (-((n : ℤ) + 1)))

/-- **Webster, Definition 3.28**: the presentation of `U′`, the localization of `U` at the
downward dots with honest negative-dot bubbles identified with fake bubbles. -/
def presLoc : Presentation.{w, max u v} (lsig RD) k where
  Rel := (pres RD k).Rel ⊕ LocRel I X
  dom
    | .inl r => (incl RD).obj ((pres RD k).dom r)
    | .inr r => r.obj RD
  cod
    | .inl r => (incl RD).obj ((pres RD k).cod r)
    | .inr r => r.obj RD
  rel
    | .inl r => inclLin RD k ((pres RD k).rel r)
    | .inr r => locRelation RD k r

theorem inclLin_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    inclLin RD k (LinDiagram.of (R := k) d) = LinDiagram.of (inclD RD d) :=
  Finsupp.mapDomain_single

set_option backward.isDefEq.respectTransparency false in
theorem freeLift_incl_map {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (freeLift k ((incl RD).toLayerMap.toPresented (presLoc RD k) (fun _ => 1))).map f =
      (presLoc RD k).lin (inclLin RD k f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Functor.map_add, map_add, Presentation.lin_add, hf, hg]
  | single d a =>
    rw [show (Finsupp.single d a : LinDiagram k _ _) = a • LinDiagram.of d from
      by
        change Finsupp.single d a = a • Finsupp.single d (1 : k)
        rw [Finsupp.smul_single_one]]
    rw [Functor.map_smul, freeLift_map_of, LayerMap.toPresented_map]
    simp [Diagram.weight, inclLin_of]

/-- The localization functor `U → U′`. -/
def toLoc : (pres RD k).Presented ⥤ (presLoc RD k).Presented :=
  (incl RD).lift (pres RD k) (Q := presLoc RD k) (χ := fun _ => 1)
    (by rintro ((c | e) | c | c) <;> rfl) fun r => by
      rw [freeLift_incl_map]
      exact (presLoc RD k).lin_rel_self (.inl r)

instance : (toLoc RD k).Additive := by unfold toLoc; infer_instance

instance : (toLoc RD k).Linear k := by unfold toLoc; infer_instance

@[simp] theorem toLoc_obj (a : Obj (psig RD)) :
    (toLoc RD k).obj ((pres RD k).obj a) = (presLoc RD k).obj ((incl RD).obj a) := rfl

theorem toLoc_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (toLoc RD k).map ((pres RD k).lin f) = (presLoc RD k).lin (inclLin RD k f) := by
  unfold toLoc
  rw [SigMap.lift_lin, freeLift_incl_map]

set_option backward.isDefEq.respectTransparency false in
/-- In `U′` the inverse dot is a two-sided inverse of the downward dot. -/
theorem invDot_comp_downDot (i : I) (μ : X) :
    (presLoc RD k).diag (invDotF RD i μ) ≫ (presLoc RD k).diag (inclD RD (downDot RD i μ)) =
      𝟙 _ := by
  have h := (presLoc RD k).lin_rel_self (.inr (.invLeft i μ))
  change (presLoc RD k).lin (LinDiagram.of (invDotF RD i μ ≫ inclD RD (downDot RD i μ)) - 𝟙 _) = 0 at h
  rw [lin_sub, lin_of, sub_eq_zero, diag_comp] at h
  exact h.trans ((presLoc RD k).lin_id _)

set_option backward.isDefEq.respectTransparency false in
theorem downDot_comp_invDot (i : I) (μ : X) :
    (presLoc RD k).diag (inclD RD (downDot RD i μ)) ≫ (presLoc RD k).diag (invDotF RD i μ) =
      𝟙 _ := by
  have h := (presLoc RD k).lin_rel_self (.inr (.invRight i μ))
  change (presLoc RD k).lin (LinDiagram.of (inclD RD (downDot RD i μ) ≫ invDotF RD i μ) - 𝟙 _) = 0 at h
  rw [lin_sub, lin_of, sub_eq_zero, diag_comp] at h
  exact h.trans ((presLoc RD k).lin_id _)

set_option backward.isDefEq.respectTransparency false in
/-- In `U′` the honest clockwise bubble with `-(n+1)` dots is the image of the fake bubble with
label `-(n+1)` (which is `0` when its degree is negative). -/
theorem cwNegHonest_eq (lam : X) (i : I) (n : ℕ) :
    (presLoc RD k).diag (cwNegHonest RD lam i (n + 1)) =
      (toLoc RD k).map ((pres RD k).lin (cwL RD k lam i (-((n : ℤ) + 1)))) := by
  have h := (presLoc RD k).lin_rel_self (.inr (.cw lam i n))
  change (presLoc RD k).lin (LinDiagram.of (cwNegHonest RD lam i (n + 1)) -
    inclLin RD k (cwL RD k lam i (-((n : ℤ) + 1)))) = 0 at h
  rw [lin_sub, lin_of, sub_eq_zero] at h
  rw [h, toLoc_lin]

set_option backward.isDefEq.respectTransparency false in
/-- In `U′` the honest counterclockwise bubble with `-(n+1)` dots is the image of the fake
bubble with label `-(n+1)` (which is `0` when its degree is negative). -/
theorem ccwNegHonest_eq (lam : X) (i : I) (n : ℕ) :
    (presLoc RD k).diag (ccwNegHonest RD lam i (n + 1)) =
      (toLoc RD k).map ((pres RD k).lin (ccwL RD k lam i (-((n : ℤ) + 1)))) := by
  have h := (presLoc RD k).lin_rel_self (.inr (.ccw lam i n))
  change (presLoc RD k).lin (LinDiagram.of (ccwNegHonest RD lam i (n + 1)) -
    inclLin RD k (ccwL RD k lam i (-((n : ℤ) + 1)))) = 0 at h
  rw [lin_sub, lin_of, sub_eq_zero] at h
  rw [h, toLoc_lin]

end Categorification.KL3.Diagram
