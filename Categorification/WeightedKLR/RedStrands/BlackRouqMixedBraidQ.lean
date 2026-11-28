/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraid
import Categorification.Algebra.ResThreeStepEnd
import Categorification.KLR.CyclotomicAction.Square

/-!
# The braid relation with equal outer colours for black restriction and induction

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and §5.1;
Khovanov–Lauda I, §2.1; Brundan, arXiv:1501.00350v1, Definition 1.1, (1.4) for outer labels
`i, i` and middle label `j ≠ i` (the shape of `TwoRep.RouqUpKLR.braidQ`).

Each crossing on restrictions is right multiplication by a projected affine crossing
(`resCrossOfEq_val`), and each dot by a projected affine dot (`resDotOfEq_cover`, and after the
unit of the source block, `threeResActs_dot_zero`, `_one`, `_two`). Polynomials in the dots act
by the polynomials in the projected dots (`InductionAlong.ThreeResActs.ncEval`). Moving units
across the crossings (`CyclotomicAction.double_cross`) turns the difference of the two composites
into the KLR identity `KLRAlgebra.braidQ_identity` on the affine cover
(`KLRAlgebra.unit_mul_braidQ_cut`). This gives

* the relation on restrictions between arbitrary contents: `resCrossOfEq_braidQ`;
* its mate on inductions: `indCrossOfEq_braidQ`.

The hypotheses are `KLRSymm Q` and `i ≠ j`; no route hypothesis is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open CyclotomicAction

universe u v

variable {J : Type u} [DecidableEq J] {k : Type v} [CommRing k]
  {Q : J → J → MvPolynomial (Fin 2) k}

/-- **The braid identity with equal outer labels, cut by two-strand units**: the difference of
the products of the whiskered crossings of both sides of the relation agrees, after the unit of
the source block, with `Q̄_{ij}` at the three new dots. -/
theorem unit_mul_braidQ_cut (i j : J) (hij : i ≠ j) {l b c d e f : Multiset J}
    (h₁ : {i} + l = b) (h₂ : {j} + b = c) (h₃ : {i} + c = f) (h₄ : {i} + b = d)
    (h₅ : {j} + d = f) (h₆ : {j} + l = e) (h₇ : {i} + e = c) :
    tripleIncl Q i j i h₁ h₂ h₃ 1 *
        ((ψ (Multiset.card b) * lastIncl Q j h₅ (lastIncl Q i h₄ 1)) *
            lastIncl Q j h₅ (-(ψ (Multiset.card l) * lastIncl Q i h₄ (lastIncl Q i h₁ 1))) *
            (ψ (Multiset.card b) * lastIncl Q i h₃ (lastIncl Q j h₂ 1)) -
          lastIncl Q i h₃ (ψ (Multiset.card l) * lastIncl Q i h₇ (lastIncl Q j h₆ 1)) *
            -(ψ (Multiset.card e) * lastIncl Q i h₃ (lastIncl Q i h₇ 1)) *
            lastIncl Q i h₃ (ψ (Multiset.card l) * lastIncl Q j h₂ (lastIncl Q i h₁ 1))) =
      tripleIncl Q i j i h₁ h₂ h₃ 1 *
        pol (MvPolynomial.rename ![⟨Multiset.card l, by rw [card_triple h₁ h₂ h₃]; omega⟩,
          ⟨Multiset.card l + 1, by rw [card_triple h₁ h₂ h₃]; omega⟩,
          ⟨Multiset.card l + 2, by rw [card_triple h₁ h₂ h₃]; omega⟩] (qbar (Q i j))) := by
  have idem : ∀ {β β' : Multiset J} (x y z : J) (g₁ : {x} + l = β) (g₂ : {y} + β = β')
      (g₃ : {z} + β' = f),
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) *
        lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) =
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) := fun x y z g₁ g₂ g₃ => by
    rw [← map_mul, ← map_mul, ← map_mul, mul_one]
  have top : ∀ {β β' : Multiset J} (x y z : J) (g₁ : {x} + l = β) (g₂ : {y} + β = β')
      (g₃ : {z} + β' = f),
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) *
        lastIncl Q z g₃ (lastIncl Q y g₂ 1) =
      lastIncl Q z g₃ (lastIncl Q y g₂ (lastIncl Q x g₁ 1)) := fun x y z g₁ g₂ g₃ => by
    rw [← map_mul, ← map_mul, mul_one]
  have l1 : lastIncl Q i h₃ (lastIncl Q j h₂ (lastIncl Q i h₁ 1)) * ψ (Multiset.card b) =
      ψ (Multiset.card b) * lastIncl Q j h₅ (lastIncl Q i h₄ (lastIncl Q i h₁ 1)) :=
    double_cross Q i j h₂ h₃ h₄ h₅ (lastIncl Q i h₁ 1)
  have l2 : lastIncl Q j h₅ (lastIncl Q i h₄ (lastIncl Q i h₁ 1)) *
      lastIncl Q j h₅ (-ψ (Multiset.card l)) =
      lastIncl Q j h₅ (-ψ (Multiset.card l)) *
        lastIncl Q j h₅ (lastIncl Q i h₄ (lastIncl Q i h₁ 1)) := by
    rw [← map_mul, ← map_mul, mul_neg, neg_mul]
    exact congrArg (fun t => lastIncl Q j h₅ (-t)) (double_cross Q i i h₁ h₄ h₁ h₄ 1)
  have l3 : lastIncl Q j h₅ (lastIncl Q i h₄ (lastIncl Q i h₁ 1)) * ψ (Multiset.card b) =
      ψ (Multiset.card b) * lastIncl Q i h₃ (lastIncl Q j h₂ (lastIncl Q i h₁ 1)) :=
    double_cross Q j i h₄ h₅ h₂ h₃ (lastIncl Q i h₁ 1)
  have r1 : lastIncl Q i h₃ (lastIncl Q j h₂ (lastIncl Q i h₁ 1)) *
      lastIncl Q i h₃ (ψ (Multiset.card l)) =
      lastIncl Q i h₃ (ψ (Multiset.card l)) *
        lastIncl Q i h₃ (lastIncl Q i h₇ (lastIncl Q j h₆ 1)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (double_cross Q j i h₁ h₂ h₆ h₇ 1)
  have r2 : lastIncl Q i h₃ (lastIncl Q i h₇ (lastIncl Q j h₆ 1)) * -ψ (Multiset.card e) =
      -ψ (Multiset.card e) * lastIncl Q i h₃ (lastIncl Q i h₇ (lastIncl Q j h₆ 1)) := by
    rw [mul_neg, neg_mul]
    exact congrArg Neg.neg (double_cross Q i i h₇ h₃ h₇ h₃ (lastIncl Q j h₆ 1))
  have r3 : lastIncl Q i h₃ (lastIncl Q i h₇ (lastIncl Q j h₆ 1)) *
      lastIncl Q i h₃ (ψ (Multiset.card l)) =
      lastIncl Q i h₃ (ψ (Multiset.card l)) *
        lastIncl Q i h₃ (lastIncl Q j h₂ (lastIncl Q i h₁ 1)) := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (double_cross Q i j h₆ h₇ h₁ h₂ 1)
  have lhs := unit_mul_absorb_three l1 (top i i j h₁ h₄ h₅) l2 (idem i i j h₁ h₄ h₅) l3
    (top i j i h₁ h₂ h₃)
  have rhs := unit_mul_absorb_three r1 (idem j i i h₆ h₇ h₃) r2 (top j i i h₆ h₇ h₃) r3
    (idem i j i h₁ h₂ h₃)
  rw [card_lastIncl i h₁] at lhs
  rw [card_lastIncl j h₆] at rhs
  rw [← neg_mul (ψ (Multiset.card l)), map_mul (lastIncl Q j h₅), map_mul (lastIncl Q i h₃),
    map_mul (lastIncl Q i h₃), ← neg_mul (ψ (Multiset.card e))]
  refine Eq.trans ?_ (braidQ_identity (Q := Q) i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
  rw [mul_sub, mul_sub, card_lastIncl i h₁, card_lastIncl j h₆]
  congr 1
  · simp only [mul_assoc] at lhs ⊢
    exact lhs
  · simp only [mul_assoc] at rhs ⊢
    exact rhs

/-- After the unit of a three-strand block, the dots on the three new strands, written through
the last-strand inclusions, are the dots `x_{p}`, `x_{p+1}`, `x_{p+2}`. -/
theorem tripleIncl_one_mul_dot_zero (a b c : J) {l β β' m : Multiset J} (h₁ : {a} + l = β)
    (h₂ : {b} + β = β') (h₃ : {c} + β' = m) :
    tripleIncl Q a b c h₁ h₂ h₃ 1 * lastIncl Q c h₃ (lastIncl Q b h₂
        (x ⟨Multiset.card l, by rw [card_lastIncl a h₁]; omega⟩ * lastIncl Q a h₁ 1)) =
      tripleIncl Q a b c h₁ h₂ h₃ 1 *
        x ⟨Multiset.card l, by rw [card_triple h₁ h₂ h₃]; omega⟩ := by
  have hd := (isLeftBlock_lastIncl (Q := Q) a h₁).intertwines_dot
    ⟨Multiset.card l, by rw [card_lastIncl a h₁]; omega⟩ le_rfl 1
  have s1 := (isLeftBlock_lastIncl (Q := Q) a h₁).one_mul_dot_last b h₂
    ⟨Multiset.card l, by rw [card_lastIncl a h₁]; omega⟩ le_rfl
  have s2 := (isLeftBlock_double Q b a h₁ h₂).one_mul_dot_last c h₃
    ⟨Multiset.card l, by rw [card_lastIncl b h₂, card_lastIncl a h₁]; omega⟩ le_rfl
  have hU : tripleIncl Q a b c h₁ h₂ h₃ 1 * lastIncl Q c h₃ (lastIncl Q b h₂ (lastIncl Q a h₁ 1)) =
      tripleIncl Q a b c h₁ h₂ h₃ 1 := by
    change lastIncl Q c h₃ (lastIncl Q b h₂ (lastIncl Q a h₁ 1)) * _ = _
    rw [← map_mul, ← map_mul, ← map_mul, mul_one]
    rfl
  rw [← hd, map_mul, map_mul, ← mul_assoc, hU]
  change lastIncl Q c h₃ ((lastIncl Q b h₂).comp (lastIncl Q a h₁) 1) * _ = _
  rw [← map_mul, s1, map_mul]
  exact s2

theorem tripleIncl_one_mul_dot_one (a b c : J) {l β β' m : Multiset J} (h₁ : {a} + l = β)
    (h₂ : {b} + β = β') (h₃ : {c} + β' = m) :
    tripleIncl Q a b c h₁ h₂ h₃ 1 * lastIncl Q c h₃
        (x ⟨Multiset.card l + 1, by rw [card_lastIncl b h₂, card_lastIncl a h₁]; omega⟩ *
          lastIncl Q b h₂ 1) =
      tripleIncl Q a b c h₁ h₂ h₃ 1 *
        x ⟨Multiset.card l + 1, by rw [card_triple h₁ h₂ h₃]; omega⟩ := by
  have hβ : Multiset.card β = Multiset.card l + 1 := card_lastIncl a h₁
  have hd := (isLeftBlock_lastIncl (Q := Q) b h₂).intertwines_dot
    ⟨Multiset.card l + 1, by rw [card_lastIncl b h₂]; omega⟩ (by simp [hβ]) 1
  have s := (isLeftBlock_double Q b a h₁ h₂).one_mul_dot_last c h₃
    ⟨Multiset.card l + 1, by rw [card_lastIncl b h₂]; omega⟩ (by simp)
  have hU : tripleIncl Q a b c h₁ h₂ h₃ 1 * lastIncl Q c h₃ (lastIncl Q b h₂ 1) =
      tripleIncl Q a b c h₁ h₂ h₃ 1 := by
    change lastIncl Q c h₃ (lastIncl Q b h₂ (lastIncl Q a h₁ 1)) * _ = _
    rw [← map_mul, ← map_mul, mul_one]
    rfl
  rw [← hd, map_mul, ← mul_assoc, hU]
  exact s

theorem tripleIncl_one_mul_dot_two (a b c : J) {l β β' m : Multiset J} (h₁ : {a} + l = β)
    (h₂ : {b} + β = β') (h₃ : {c} + β' = m) :
    tripleIncl Q a b c h₁ h₂ h₃ 1 *
        (x ⟨Multiset.card l + 2, by rw [card_triple h₁ h₂ h₃]; omega⟩ * lastIncl Q c h₃ 1) =
      tripleIncl Q a b c h₁ h₂ h₃ 1 *
        x ⟨Multiset.card l + 2, by rw [card_triple h₁ h₂ h₃]; omega⟩ := by
  have hβ' : Multiset.card β' = Multiset.card l + 2 := by
    rw [card_lastIncl b h₂, card_lastIncl a h₁]
  have hd := (isLeftBlock_lastIncl (Q := Q) c h₃).intertwines_dot
    ⟨Multiset.card l + 2, by rw [card_triple h₁ h₂ h₃]; omega⟩ (by simp [hβ']) 1
  rw [← hd, ← mul_assoc, triple_one_mul_last]

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR KLRAlgebra CyclotomicAction
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

local notation "S" => affineCoverQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ
local notation "π" => affineTensorProjection (Q := Q) Λ

/-! ### Scalars and dots on triple restrictions -/

/-- A composite of three maps each sending scalars to scalars times the image of `1`. -/
theorem three_algebraMap_eq {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D] (φ₁ : A →ₙ+* B) (φ₂ : B →ₙ+* C)
    (φ₃ : C →ₙ+* D) (h₁ : ∀ c : k, φ₁ (algebraMap k A c) = algebraMap k B c * φ₁ 1)
    (h₂ : ∀ c : k, φ₂ (algebraMap k B c) = algebraMap k C c * φ₂ 1)
    (h₃ : ∀ c : k, φ₃ (algebraMap k C c) = algebraMap k D c * φ₃ 1) (c : k) :
    φ₃ (φ₂ (φ₁ (algebraMap k A c))) = algebraMap k D c * φ₃ (φ₂ (φ₁ 1)) := by
  rw [h₁, map_mul, h₂, map_mul, map_mul, h₃, mul_assoc, mul_assoc, ← map_mul φ₃ (φ₂ 1),
    ← map_mul φ₂ 1, one_mul, ← map_mul φ₃ 1, one_mul]

/-- The transported appending map sends scalars to scalars times the image of `1`. -/
theorem appendBlackOpOfEq_algebraMap (x : I) {μ β : Multiset I}
    (h : ({x} : Multiset I) + μ = β) (c : k) :
    appendBlackOpOfEq Q Λ x h (algebraMap k (T μ)ᵐᵒᵖ c) =
      algebraMap k (T β)ᵐᵒᵖ c * appendBlackOpOfEq Q Λ x h 1 := by
  rw [MulOpposite.algebraMap_apply, MulOpposite.algebraMap_apply, ← op_one,
    appendBlackOpOfEq_op, appendBlackOpOfEq_op, ← op_mul, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, map_smul, mul_smul_comm, mul_one]

variable (Q) in
/-- The dot on `Eᵢ` out of an arbitrary content acts by the projected affine dot on the new
strand times the unit of appending it. -/
theorem resDotOfEq_cover (x : I) {μ β : Multiset I} (h : ({x} : Multiset I) + μ = β)
    (M : ModuleCat.{u} (T β)ᵐᵒᵖ) (r : Res (appendBlackOpOfEq Q Λ x h) M) :
    ((((resDotOfEq Q Λ x h).app M).hom r).val : M) =
      op (π β (KLRAlgebra.x ⟨Multiset.card (stendhalWeight ℓ μ), by
          rw [card_lastIncl (Sum.inl x) (stendhalWeight_cons_eq x h)]; omega⟩ *
        lastIncl S (Sum.inl x) (stendhalWeight_cons_eq x h) 1)) • (r.val : M) := by
  subst h
  rw [resDotOfEq_val, appendedDot_eq_projection, ← map_one (π μ), appendBlack_projection,
    ← map_mul]
  rfl

omit [Field k] in
theorem op_smul_eq_of_fix {R N : Type*} [Ring R] [AddCommGroup N] [Module Rᵐᵒᵖ N] {u X Y : R}
    {n : N} (hn : op u • n = n) (h : u * X = u * Y) : op X • n = op Y • n := by
  rw [← hn, smul_smul, smul_smul, ← op_mul, ← op_mul, h]

/-- The dot on the first appended strand of a triple restriction acts, on elements, by the
projected affine dot `x_p`. -/
theorem threeResActs_dot_zero (x y z : I) {l w w' m : Multiset I}
    (e₁ : ({x} : Multiset I) + l = w) (e₂ : ({y} : Multiset I) + w = w')
    (e₃ : ({z} : Multiset I) + w' = m) :
    ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ x e₁) (φ₂ := appendBlackOpOfEq Q Λ y e₂)
      (φ₃ := appendBlackOpOfEq Q Λ z e₃)
      (Functor.whiskerLeft (blackEOfEq Q Λ z e₃ ⋙ blackEOfEq Q Λ y e₂) (resDotOfEq Q Λ x e₁))
      (π m (KLRAlgebra.x ⟨Multiset.card (stendhalWeight ℓ l), by
        rw [card_triple (stendhalWeight_cons_eq x e₁) (stendhalWeight_cons_eq y e₂)
          (stendhalWeight_cons_eq z e₃)]; omega⟩)) := fun M w => by
  have h := congrArg (fun t => (Res.val (Res.val t) : M))
    (resDotOfEq_cover Q Λ x e₁ ((blackEOfEq Q Λ z e₃ ⋙ blackEOfEq Q Λ y e₂).obj M) w)
  refine h.trans ?_
  rw [Res.val_smul, Res.val_smul, appendBlackOpOfEq_op, appendBlackAt_projection,
    appendBlackOpOfEq_op, appendBlackAt_projection]
  refine op_smul_eq_of_fix (res_three_val_fix Λ x y z e₁ e₂ e₃ M w) ?_
  rw [← map_mul, ← map_mul]
  exact congrArg (π m) (tripleIncl_one_mul_dot_zero _ _ _ _ _ _)

/-- The dot on the second appended strand of a triple restriction acts by `x_{p+1}`. -/
theorem threeResActs_dot_one (x y z : I) {l w w' m : Multiset I}
    (e₁ : ({x} : Multiset I) + l = w) (e₂ : ({y} : Multiset I) + w = w')
    (e₃ : ({z} : Multiset I) + w' = m) :
    ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ x e₁) (φ₂ := appendBlackOpOfEq Q Λ y e₂)
      (φ₃ := appendBlackOpOfEq Q Λ z e₃)
      (Functor.whiskerRight (Functor.whiskerLeft (blackEOfEq Q Λ z e₃) (resDotOfEq Q Λ y e₂))
        (blackEOfEq Q Λ x e₁))
      (π m (KLRAlgebra.x ⟨Multiset.card (stendhalWeight ℓ l) + 1, by
        rw [card_triple (stendhalWeight_cons_eq x e₁) (stendhalWeight_cons_eq y e₂)
          (stendhalWeight_cons_eq z e₃)]; omega⟩)) := fun M w => by
  have h := congrArg (fun t => (Res.val t : M))
    (resDotOfEq_cover Q Λ y e₂ ((blackEOfEq Q Λ z e₃).obj M) w.val)
  refine h.trans ?_
  rw [Res.val_smul, appendBlackOpOfEq_op, appendBlackAt_projection]
  refine op_smul_eq_of_fix (res_three_val_fix Λ x y z e₁ e₂ e₃ M w) ?_
  rw [← map_mul, ← map_mul]
  refine congrArg (π m) ((congrArg (fun t => _ * lastIncl S _ _ (KLRAlgebra.x t * _))
    (Fin.ext ?_)).trans (tripleIncl_one_mul_dot_one _ _ _ _ _ _))
  exact card_lastIncl (Sum.inl x) (stendhalWeight_cons_eq x e₁)

/-- The dot on the third appended strand of a triple restriction acts by `x_{p+2}`. -/
theorem threeResActs_dot_two (x y z : I) {l w w' m : Multiset I}
    (e₁ : ({x} : Multiset I) + l = w) (e₂ : ({y} : Multiset I) + w = w')
    (e₃ : ({z} : Multiset I) + w' = m) :
    ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ x e₁) (φ₂ := appendBlackOpOfEq Q Λ y e₂)
      (φ₃ := appendBlackOpOfEq Q Λ z e₃)
      (Functor.whiskerRight (Functor.whiskerRight (resDotOfEq Q Λ z e₃) (blackEOfEq Q Λ y e₂))
        (blackEOfEq Q Λ x e₁))
      (π m (KLRAlgebra.x ⟨Multiset.card (stendhalWeight ℓ l) + 2, by
        rw [card_triple (stendhalWeight_cons_eq x e₁) (stendhalWeight_cons_eq y e₂)
          (stendhalWeight_cons_eq z e₃)]; omega⟩)) := fun M w => by
  refine (resDotOfEq_cover Q Λ z e₃ M w.val.val).trans ?_
  refine op_smul_eq_of_fix (res_three_val_fix Λ x y z e₁ e₂ e₃ M w) ?_
  rw [← map_mul, ← map_mul]
  refine congrArg (π m) ((congrArg (fun t => _ * (KLRAlgebra.x t * _))
    (Fin.ext ?_)).trans (tripleIncl_one_mul_dot_two _ _ _ _ _ _))
  change Multiset.card (stendhalWeight ℓ w') = _
  rw [card_lastIncl (Sum.inl y) (stendhalWeight_cons_eq y e₂),
    card_lastIncl (Sum.inl x) (stendhalWeight_cons_eq x e₁)]

/-! ### The relation on restrictions -/

/-- **The braid relation with equal outer colours on restrictions** between arbitrary contents
(KL I, §2.1; Brundan, arXiv:1501.00350v1, (1.4) for outer labels `i, i` and middle label
`j ≠ i`): the mate form of `TwoRep.RouqUpKLR.braidQ`. The middle crossings have equal colours
and act by `-ψ`. -/
theorem resCrossOfEq_braidQ (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {l b c d e f : Multiset I} (h₁ : ({i} : Multiset I) + l = b)
    (h₂ : ({j} : Multiset I) + b = c) (h₃ : ({i} : Multiset I) + c = f)
    (h₄ : ({i} : Multiset I) + b = d) (h₅ : ({j} : Multiset I) + d = f)
    (h₆ : ({j} : Multiset I) + l = e) (h₇ : ({i} : Multiset I) + e = c) :
    (Functor.whiskerRight (resCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃) (blackEOfEq Q Λ i h₁) ≫
        Functor.whiskerLeft (blackEOfEq Q Λ j h₅) (resCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄) ≫
          Functor.whiskerRight (resCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) (blackEOfEq Q Λ i h₁) :
        End (blackEOfEq Q Λ i h₃ ⋙ blackEOfEq Q Λ j h₂ ⋙ blackEOfEq Q Λ i h₁)) -
      (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂) ≫
        Functor.whiskerRight (resCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) (blackEOfEq Q Λ j h₆) ≫
          Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇)) =
      KLR.ncEval (A := End (blackEOfEq Q Λ i h₃ ⋙ blackEOfEq Q Λ j h₂ ⋙ blackEOfEq Q Λ i h₁))
        ![Functor.whiskerLeft (blackEOfEq Q Λ i h₃ ⋙ blackEOfEq Q Λ j h₂) (resDotOfEq Q Λ i h₁),
          Functor.whiskerRight (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resDotOfEq Q Λ j h₂))
            (blackEOfEq Q Λ i h₁),
          Functor.whiskerRight (Functor.whiskerRight (resDotOfEq Q Λ i h₃) (blackEOfEq Q Λ j h₂))
            (blackEOfEq Q Λ i h₁)] (KLR.qbar (Q i j)) := by
  have hΦ := three_algebraMap_eq (appendBlackOpOfEq Q Λ i h₁) (appendBlackOpOfEq Q Λ j h₂)
    (appendBlackOpOfEq Q Λ i h₃) (appendBlackOpOfEq_algebraMap Λ i h₁)
    (appendBlackOpOfEq_algebraMap Λ j h₂) (appendBlackOpOfEq_algebraMap Λ i h₃)
  have hm := card_triple (stendhalWeight_cons_eq (ℓ := ℓ) i h₁) (stendhalWeight_cons_eq j h₂)
    (stendhalWeight_cons_eq i h₃)
  set p := Multiset.card (stendhalWeight ℓ l)
  let g : Fin 3 → Fin (Multiset.card (stendhalWeight ℓ f)) :=
    ![⟨p, by omega⟩, ⟨p + 1, by omega⟩, ⟨p + 2, by omega⟩]
  have hz : ∀ a, ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ i h₁)
      (φ₂ := appendBlackOpOfEq Q Λ j h₂) (φ₃ := appendBlackOpOfEq Q Λ i h₃)
      (![Functor.whiskerLeft (blackEOfEq Q Λ i h₃ ⋙ blackEOfEq Q Λ j h₂) (resDotOfEq Q Λ i h₁),
          Functor.whiskerRight (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resDotOfEq Q Λ j h₂))
            (blackEOfEq Q Λ i h₁),
          Functor.whiskerRight (Functor.whiskerRight (resDotOfEq Q Λ i h₃) (blackEOfEq Q Λ j h₂))
            (blackEOfEq Q Λ i h₁)] a) (π f (KLRAlgebra.x (g a))) := by
    intro a
    fin_cases a
    · exact threeResActs_dot_zero Λ i j i h₁ h₂ h₃
    · exact threeResActs_dot_one Λ i j i h₁ h₂ h₃
    · exact threeResActs_dot_two Λ i j i h₁ h₂ h₃
  have hR := ThreeResActs.ncEval hΦ hz (KLR.qbar (Q i j))
  have c1 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ i h₁) (φ₂ := appendBlackOpOfEq Q Λ j h₂)
      (φ₃ := appendBlackOpOfEq Q Λ i h₃) (ψ₁ := appendBlackOpOfEq Q Λ i h₁)
      (ψ₂ := appendBlackOpOfEq Q Λ i h₄) (ψ₃ := appendBlackOpOfEq Q Λ j h₅)
      (Functor.whiskerRight (resCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃) (blackEOfEq Q Λ i h₁))
      (π f (resCrossSign k j i • crossCoverElem Q Λ j i h₄ h₅)) :=
    fun M w => whiskerRight_resCrossOfEq_val Λ hsym j i i h₄ h₅ h₂ h₃ h₁ M w
  have c2 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ i h₁) (φ₂ := appendBlackOpOfEq Q Λ i h₄)
      (φ₃ := appendBlackOpOfEq Q Λ j h₅) (ψ₁ := appendBlackOpOfEq Q Λ i h₁)
      (ψ₂ := appendBlackOpOfEq Q Λ i h₄) (ψ₃ := appendBlackOpOfEq Q Λ j h₅)
      (Functor.whiskerLeft (blackEOfEq Q Λ j h₅) (resCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄))
      (π f (lastIncl S (Sum.inl j) (stendhalWeight_cons_eq j h₅)
        (resCrossSign k i i • crossCoverElem Q Λ i i h₁ h₄))) :=
    fun M w => whiskerLeft_resCrossOfEq_val Λ hsym i i j h₁ h₄ h₁ h₄ h₅ M w
  have c3 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ i h₁) (φ₂ := appendBlackOpOfEq Q Λ i h₄)
      (φ₃ := appendBlackOpOfEq Q Λ j h₅) (ψ₁ := appendBlackOpOfEq Q Λ i h₁)
      (ψ₂ := appendBlackOpOfEq Q Λ j h₂) (ψ₃ := appendBlackOpOfEq Q Λ i h₃)
      (Functor.whiskerRight (resCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) (blackEOfEq Q Λ i h₁))
      (π f (resCrossSign k i j • crossCoverElem Q Λ i j h₂ h₃)) :=
    fun M w => whiskerRight_resCrossOfEq_val Λ hsym i j i h₂ h₃ h₄ h₅ h₁ M w
  have d1 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ i h₁) (φ₂ := appendBlackOpOfEq Q Λ j h₂)
      (φ₃ := appendBlackOpOfEq Q Λ i h₃) (ψ₁ := appendBlackOpOfEq Q Λ j h₆)
      (ψ₂ := appendBlackOpOfEq Q Λ i h₇) (ψ₃ := appendBlackOpOfEq Q Λ i h₃)
      (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂))
      (π f (lastIncl S (Sum.inl i) (stendhalWeight_cons_eq i h₃)
        (resCrossSign k i j • crossCoverElem Q Λ i j h₆ h₇))) :=
    fun M w => whiskerLeft_resCrossOfEq_val Λ hsym i j i h₆ h₇ h₁ h₂ h₃ M w
  have d2 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ j h₆) (φ₂ := appendBlackOpOfEq Q Λ i h₇)
      (φ₃ := appendBlackOpOfEq Q Λ i h₃) (ψ₁ := appendBlackOpOfEq Q Λ j h₆)
      (ψ₂ := appendBlackOpOfEq Q Λ i h₇) (ψ₃ := appendBlackOpOfEq Q Λ i h₃)
      (Functor.whiskerRight (resCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) (blackEOfEq Q Λ j h₆))
      (π f (resCrossSign k i i • crossCoverElem Q Λ i i h₇ h₃)) :=
    fun M w => whiskerRight_resCrossOfEq_val Λ hsym i i j h₇ h₃ h₇ h₃ h₆ M w
  have d3 : ThreeResActs (φ₁ := appendBlackOpOfEq Q Λ j h₆) (φ₂ := appendBlackOpOfEq Q Λ i h₇)
      (φ₃ := appendBlackOpOfEq Q Λ i h₃) (ψ₁ := appendBlackOpOfEq Q Λ i h₁)
      (ψ₂ := appendBlackOpOfEq Q Λ j h₂) (ψ₃ := appendBlackOpOfEq Q Λ i h₃)
      (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇))
      (π f (lastIncl S (Sum.inl i) (stendhalWeight_cons_eq i h₃)
        (resCrossSign k j i • crossCoverElem Q Λ j i h₁ h₂))) :=
    fun M w => whiskerLeft_resCrossOfEq_val Λ hsym j i i h₁ h₂ h₆ h₇ h₃ M w
  have hL := (c1.comp (c2.comp c3)).sub (d1.comp (d2.comp d3))
  refine threeRes_end_ext fun M w => (hL M w).trans (Eq.trans ?_ (hR M w).symm)
  refine op_smul_eq_of_fix (res_three_val_fix Λ i j i h₁ h₂ h₃ M w) ?_
  have hY : KLR.ncEval (fun a => π f (KLRAlgebra.x (g (Fin.rev a))))
      (MvPolynomial.rename Fin.rev (KLR.qbar (Q i j))) =
      π f (pol (MvPolynomial.rename g (KLR.qbar (Q i j)))) := by
    rw [← ncEval_map, ncEval_eq_pol, MvPolynomial.rename_rename]
    have hg : ((fun a => g (Fin.rev a)) ∘ Fin.rev) = g := funext fun a => congrArg g (Fin.rev_rev a)
    rw [hg]
  rw [hY, resCrossSign_of_ne hij, resCrossSign_of_ne (Ne.symm hij), resCrossSign_self,
    one_smul, one_smul, one_smul, one_smul, neg_one_smul, neg_one_smul]
  simp only [← map_mul, ← map_sub]
  refine congrArg (π f) ?_
  have key := unit_mul_braidQ_cut (Q := S) (Sum.inl i) (Sum.inl j)
    (Sum.inl_injective.ne hij) (stendhalWeight_cons_eq i h₁) (stendhalWeight_cons_eq j h₂)
    (stendhalWeight_cons_eq i h₃) (stendhalWeight_cons_eq i h₄) (stendhalWeight_cons_eq j h₅)
    (stendhalWeight_cons_eq j h₆) (stendhalWeight_cons_eq i h₇)
  simp only [crossCoverElem, mul_assoc] at key ⊢
  exact key

/-! ### Mates on inductions -/

omit [Field k] in
/-- The mate of a transformation whiskered on the right is the whiskered mate. -/
theorem whiskerLeft_conjugateEquiv_symm_apply {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] {L₁ L₂ : ℬ ⥤ 𝒞} {R₁ R₂ : 𝒞 ⥤ ℬ} {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (α : R₁ ⟶ R₂) :
    Functor.whiskerLeft L ((conjugateEquiv adj₁ adj₂).symm α) =
      (conjugateEquiv (adj.comp adj₁) (adj.comp adj₂)).symm (Functor.whiskerRight α R) := by
  rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]

omit [Field k] in
/-- The mate of a transformation whiskered on the left is the whiskered mate. -/
theorem whiskerRight_conjugateEquiv_symm_apply {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] {L₁ L₂ : 𝒜 ⥤ ℬ} {R₁ R₂ : ℬ ⥤ 𝒜} {L : ℬ ⥤ 𝒞} {R : 𝒞 ⥤ ℬ} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (α : R₁ ⟶ R₂) :
    Functor.whiskerRight ((conjugateEquiv adj₁ adj₂).symm α) L =
      (conjugateEquiv (adj₁.comp adj) (adj₂.comp adj)).symm (Functor.whiskerLeft R α) := by
  rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]

/-- **The braid relation with equal outer colours on black inductions** between arbitrary
contents (KL I, §2.1; Brundan, arXiv:1501.00350v1, (1.4) for outer labels `i, i` and middle
label `j ≠ i`, the block form of `TwoRep.RouqUpKLR.braidQ`), the mate of
`resCrossOfEq_braidQ`. -/
theorem indCrossOfEq_braidQ (hsym : KLRSymm Q) (i j : I) (hij : i ≠ j)
    {l b c d e f : Multiset I} (h₁ : ({i} : Multiset I) + l = b)
    (h₂ : ({j} : Multiset I) + b = c) (h₃ : ({i} : Multiset I) + c = f)
    (h₄ : ({i} : Multiset I) + b = d) (h₅ : ({j} : Multiset I) + d = f)
    (h₆ : ({j} : Multiset I) + l = e) (h₇ : ({i} : Multiset I) + e = c) :
    (Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄) (blackFOfEq Q Λ j h₅) ≫
          Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃)) -
      (Functor.whiskerRight (indCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇) (blackFOfEq Q Λ i h₃) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ j h₆) (indCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) ≫
          Functor.whiskerRight (indCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂) (blackFOfEq Q Λ i h₃) :
        End (blackFOfEq Q Λ i h₁ ⋙ blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃)) =
      KLR.ncEval (A := End (blackFOfEq Q Λ i h₁ ⋙ blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃))
        ![Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
            (Functor.whiskerLeft (blackFOfEq Q Λ j h₂) (indDotOfEq Q Λ i h₃)),
          Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
            (Functor.whiskerRight (indDotOfEq Q Λ j h₂) (blackFOfEq Q Λ i h₃)),
          Functor.whiskerRight (indDotOfEq Q Λ i h₁)
            (blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃)] (KLR.qbar (Q i j)) := by
  set A := (blackAdjOfEq Q Λ i h₁).comp ((blackAdjOfEq Q Λ j h₂).comp (blackAdjOfEq Q Λ i h₃))
  have m0 : Functor.whiskerRight (indDotOfEq Q Λ i h₁)
      (blackFOfEq Q Λ j h₂ ⋙ blackFOfEq Q Λ i h₃) = (conjugateEquiv A A).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₃ ⋙ blackEOfEq Q Λ j h₂)
          (resDotOfEq Q Λ i h₁)) := by
    rw [indDotOfEq, whiskerRight_conjugateEquiv_symm_apply]
  have m1 : Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
      (Functor.whiskerRight (indDotOfEq Q Λ j h₂) (blackFOfEq Q Λ i h₃)) =
      (conjugateEquiv A A).symm (Functor.whiskerRight
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resDotOfEq Q Λ j h₂))
          (blackEOfEq Q Λ i h₁)) := by
    rw [whiskerRight_indDotOfEq_two Q Λ i j h₂ h₃, whiskerLeft_conjugateEquiv_symm_apply]
  have m2 : Functor.whiskerLeft (blackFOfEq Q Λ i h₁)
      (Functor.whiskerLeft (blackFOfEq Q Λ j h₂) (indDotOfEq Q Λ i h₃)) =
      (conjugateEquiv A A).symm (Functor.whiskerRight
        (Functor.whiskerRight (resDotOfEq Q Λ i h₃) (blackEOfEq Q Λ j h₂))
          (blackEOfEq Q Λ i h₁)) := by
    rw [whiskerLeft_indDotOfEq_two Q Λ i j h₂ h₃, whiskerLeft_conjugateEquiv_symm_apply]
  have hL : Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) ≫
      Functor.whiskerRight (indCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄) (blackFOfEq Q Λ j h₅) ≫
        Functor.whiskerLeft (blackFOfEq Q Λ i h₁) (indCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃) =
      (conjugateEquiv A A).symm
        (Functor.whiskerRight (resCrossOfEq Λ hsym j i h₄ h₅ h₂ h₃) (blackEOfEq Q Λ i h₁) ≫
          Functor.whiskerLeft (blackEOfEq Q Λ j h₅) (resCrossOfEq Λ hsym i i h₁ h₄ h₁ h₄) ≫
            Functor.whiskerRight (resCrossOfEq Λ hsym i j h₂ h₃ h₄ h₅) (blackEOfEq Q Λ i h₁)) := by
    rw [whiskerLeft_indCrossOfEq, whiskerRight_indCrossOfEq, whiskerLeft_indCrossOfEq]
    exact conjugateEquiv_symm_comp_three _ _ _ _ _ _ _
  have hR : Functor.whiskerRight (indCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇) (blackFOfEq Q Λ i h₃) ≫
      Functor.whiskerLeft (blackFOfEq Q Λ j h₆) (indCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) ≫
        Functor.whiskerRight (indCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂) (blackFOfEq Q Λ i h₃) =
      (conjugateEquiv A A).symm
        (Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym i j h₆ h₇ h₁ h₂) ≫
          Functor.whiskerRight (resCrossOfEq Λ hsym i i h₇ h₃ h₇ h₃) (blackEOfEq Q Λ j h₆) ≫
            Functor.whiskerLeft (blackEOfEq Q Λ i h₃) (resCrossOfEq Λ hsym j i h₁ h₂ h₆ h₇)) := by
    rw [whiskerRight_indCrossOfEq, whiskerLeft_indCrossOfEq, whiskerRight_indCrossOfEq]
    exact conjugateEquiv_symm_comp_three _ _ _ _ _ _ _
  rw [hL, hR]
  change conjugateEquivSymmLinear (k := k) A _ - conjugateEquivSymmLinear (k := k) A _ = _
  rw [← map_sub]
  change (conjugateEquiv A A).symm _ = _
  rw [resCrossOfEq_braidQ Λ hsym i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇, conjugateEquiv_symm_ncEval,
    rename_rev_three, qbar_rename_rev]
  congr 1
  funext a
  fin_cases a
  · exact m2.symm
  · exact m1.symm
  · exact m0.symm

end Categorification.Stendhal
