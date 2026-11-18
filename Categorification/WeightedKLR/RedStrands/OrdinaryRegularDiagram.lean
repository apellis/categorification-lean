/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DownwardCornerMap
import Categorification.Diagrams.KLR.Comparison
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Ordinary diagrams acting on summands of the regular tensor product algebra

In the last paragraph of Webster, arXiv:1309.3796v3, §4.6, Lemma 4.29, the
operator attached to an ordinary diagram is left multiplication. At two
individual boundary words this is a map between the corresponding right
ideals. Evaluation on the source boundary idempotent recovers its coefficient.
The cited injectivity argument is the one revised in version 3; arXiv:1309.3796v2,
§4.5, Lemma 4.28, argues via Lemma 4.26 instead.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory StringDiagrams KLR KLR.Diagram KLRAlgebra MulOpposite
open scoped Classical ModuleCat.Algebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w
variable {I : Type u} [DecidableEq I] {k : Type w} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => affineCoverQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => affineTensorProjection (Q := Q) Λ ν
local notation "D" => Tgt k R μ
local notation "E" => ε k R μ

/-- The summand of the tensor product algebra at an ordinary boundary: the
projective right ideal on its (possibly zero) boundary idempotent. -/
abbrev ordinaryRegularIdeal (a : D) := rIdeal (π (E a))

private def regularMap {a b : D} (f : a ⟶ b) :
    ordinaryRegularIdeal Q Λ ν a →ₗ[Tᵐᵒᵖ] ordinaryRegularIdeal Q Λ ν b where
  toFun z := ⟨π f.val * z.val, by
    change π (E b) * (π f.val * z.val) = _
    rw [← mul_assoc, ← map_mul, Tgt.ε_mul_val]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' r z := Subtype.ext (mul_assoc (π f.val) z.val r.unop).symm

/-- Left multiplication on boundary right ideals, functorially in arbitrary
affine KLR diagram words at the given content. -/
def ordinaryRegularFunctor : D ⥤ ModuleCat Tᵐᵒᵖ where
  obj a := ModuleCat.of _ (ordinaryRegularIdeal Q Λ ν a)
  map f := ModuleCat.ofHom (regularMap Q Λ ν f)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext z.property)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext (by
    change π (g.val * f.val) * z.val = π g.val * (π f.val * z.val)
    rw [map_mul, mul_assoc]))

instance : (ordinaryRegularFunctor Q Λ ν).Additive where
  map_add {a b f g} := ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext (by
    change π (f.val + g.val) * z.val = π f.val * z.val + π g.val * z.val
    rw [map_add, add_mul]))

instance : (ordinaryRegularFunctor Q Λ ν).Linear k where
  map_smul {a b} f c := ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext (by
    change π (c • f.val) * z.val = (π f.val * z.val) * algebraMap k T c
    rw [map_smul, smul_mul_assoc, Algebra.smul_def, Algebra.commutes]))

/-- Interpret any *presented ordinary diagram* on the regular summands. -/
abbrev ordinaryRegularDiagram :=
  evalFunctor k R μ ⋙ ordinaryRegularFunctor Q Λ ν

/-- Evaluation on the source boundary idempotent recovers the projected
algebra element, including for words at which the idempotent is zero. -/
theorem ordinaryRegularDiagram_eq_zero_iff {a b : Obj (sig (I ⊕ Fin ℓ))}
    (f : (pres k R).obj a ⟶ (pres k R).obj b) :
    (ordinaryRegularDiagram Q Λ ν).map f = 0 ↔ π ((evalFunctor k R μ).map f).val = 0 := by
  let x := (evalFunctor k R μ).map f
  let ea := π (E a)
  have hunit : ea * ea = ea := (map_mul π _ _).symm.trans (congrArg π (ε_mul_ε a))
  have he : π x.val * ea = π x.val :=
    (map_mul π _ _).symm.trans (congrArg π (Tgt.val_mul_ε x))
  constructor
  · intro h
    have hz := congrArg (fun g : (ordinaryRegularFunctor Q Λ ν).obj a ⟶
      (ordinaryRegularFunctor Q Λ ν).obj b => (g.hom ⟨ea, hunit⟩).val) h
    exact he.symm.trans hz
  · intro h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change π x.val * z.val = 0
    exact (congrArg (· * z.val) h).trans (zero_mul _)

/-- Every ordinary element is detected on at least one source and target
sequence summand of the regular representation. -/
theorem exists_regular_corner_ne_zero {x : T} (hx : x ≠ 0) :
    ∃ s t : Seq μ, π (e t) * x * π (e s) ≠ 0 := by
  classical
  by_contra! h
  have hsum : (∑ s : Seq μ, π (e s)) = 1 := by
    rw [← map_sum, sum_e, map_one]
  apply hx
  calc
    x = (∑ t : Seq μ, π (e t)) * x * (∑ s : Seq μ, π (e s)) := by rw [hsum, one_mul, mul_one]
    _ = 0 := by simp only [Finset.sum_mul, Finset.mul_sum, h, Finset.sum_const_zero]

end Categorification.Stendhal
