/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftRootStandard

/-!
# The reflection `S_α ≅ S^L_α` on classes

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
proof of Proposition 5.3. The class `[y]` of `y ∈ e_α T̃^λ` in Webster's standard module `S_α`
reflects to the vector `(flip(y) [e(s)])_s` of the left root standard module
`S^L_α = ⊕_s T^λ e(s) / U_s` (`rootReflect_mk`). The corner `e_α T̃^λ e_α` acts on classes by left
multiplication (`rootAction_mk`), so the reflected block action of Proposition 5.3 on a unit
vector `[e(s)]` of `S^L_α` is `(flip(c e(s)) [e(s')])_{s'}` for `c` the block diagram
(`rootReflectConj_rootAction_single`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "A" => StendhalAlgebra k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "mk" => TensorProductAlgebra.mk Q Λ ν

namespace StendhalAlgebra

variable {α : Fin ℓ → I → ℕ}

theorem reflectToLeftStandard_e_mul (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (y : A) : reflectToLeftStandard s hs (e s hs * y) = reflectToLeftStandard s hs y := by
  rw [reflectToLeftStandard_apply, reflectToLeftStandard_apply]
  congr 1
  apply Subtype.ext
  change tensorFlip (mk (e s hs * (e s hs * y))) = tensorFlip (mk (e s hs * y))
  rw [← mul_assoc, e_mul_e_self]

/-- `[flip(e(s) y)] = flip(y) [e(s)]`. -/
theorem reflectToLeftStandard_eq_smul (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (y : A) :
    reflectToLeftStandard s hs y = tensorFlip (mk y) • leftStandardUnit Q Λ s hs := by
  have hu : reflectToLeftStandard s hs (e s hs) = leftStandardUnit Q Λ s hs :=
    (standardModuleReflect_mk s hs _ _).symm.trans (standardModuleReflect_unit s hs)
  rw [← reflectToLeftStandard_e_mul, reflectToLeftStandard_mul, hu]

variable (Q Λ α) in
/-- The class `[y]` in `S_α` of an element `y = e_α y` of `T̃^λ`. -/
def rootStandardMk (y : A) (hy : rootIdem Q Λ α * y = y) : rootStandard (ν := ν) Q Λ α :=
  ⟨Submodule.Quotient.mk y, Submodule.mem_map_of_mem ((mem_span_rootIdem_iff y).2 hy)⟩

/-- **The reflection on classes**: `[y] ↦ (flip(y) [e(s)])_s`. -/
theorem rootReflect_mk (y : A) (hy : rootIdem Q Λ α * y = y) (s : RootSeq (ν := ν) α) :
    rootReflect Q Λ (rootStandardMk Q Λ α y hy) s =
      tensorFlip (mk y) • leftStandardUnit Q Λ s.1 (RootSeq.isRedOrdered α s) := by
  rw [rootReflect_apply, standardModuleReflect_apply, coe_rootStandardToPi_apply,
    show ((rootStandardMk Q Λ α y hy : rootStandard (ν := ν) Q Λ α) : A ⧸ rootUpper Q Λ α) =
      Submodule.Quotient.mk y from rfl, rootProj_mk, reflectQuotient_mk,
    reflectToLeftStandard_e_mul, reflectToLeftStandard_eq_smul]

theorem rootIdem_mul_corner_mul (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α).Corner)
    (y : A) : rootIdem Q Λ α * (c.1 * y) = c.1 * y := by
  rw [← mul_assoc, ((Subsemigroup.mem_corner_iff (isIdempotentElem_rootIdem α)).1 c.2).1]

/-- The corner acts on classes by left multiplication. -/
theorem rootAction_mk (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α).Corner)
    (y : A) (hy : rootIdem Q Λ α * y = y) :
    rootAction Q Λ α c (rootStandardMk Q Λ α y hy) =
      rootStandardMk Q Λ α (c.1 * y) (rootIdem_mul_corner_mul c y) :=
  Subtype.ext rfl

/-- The unit vector `[e(s)]` of `S^L_α` is the reflection of the class of `e(s)`. -/
theorem single_leftStandardUnit_eq (s : RootSeq (ν := ν) α) :
    Pi.single (M := fun s : RootSeq (ν := ν) α => leftStandard Q Λ s.1 (RootSeq.isRedOrdered α s))
      s (leftStandardUnit Q Λ s.1 (RootSeq.isRedOrdered α s)) =
      rootReflect Q Λ (rootStandardMk Q Λ α (e s.1 (RootSeq.isRedOrdered α s))
        (rootIdem_mul_rootSeq_e s)) := by
  funext s'
  rw [rootReflect_mk, tensorFlip_mk_e]
  by_cases h : s' = s
  · subst h
    rw [Pi.single_eq_same, leftStandardUnit, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (seqIdem_mul_self Q Λ _ _).symm
  · rw [Pi.single_eq_of_ne h, leftStandardUnit, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_ |>.symm
    have h0 : (TensorProductAlgebra.mk Q Λ ν (e s.1 (RootSeq.isRedOrdered α s)) •
        (⟨seqIdem Q Λ s'.1 (RootSeq.isRedOrdered α s'), seqIdem_mul_self Q Λ _ _⟩ :
          lIdeal (seqIdem Q Λ s'.1 (RootSeq.isRedOrdered α s'))) ) = 0 := by
      apply Subtype.ext
      change mk (e s.1 _) * mk (e s'.1 _) = 0
      rw [← map_mul, e_mul_e, ite_eq_right_of_eq_false _ _
        (eq_false fun h' => h (Subtype.ext h'.symm)), map_zero]
    rw [h0]
    exact Submodule.zero_mem _

/-- **The reflected corner action on a unit vector**: `c [e(s)] = (flip(c e(s)) [e(s')])_{s'}`. -/
theorem rootReflectConj_rootAction_single (hα : RootNonViolated (ν := ν) α)
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α).Corner)
    (s s' : RootSeq (ν := ν) α) :
    rootReflectConj Q Λ hα (rootAction Q Λ α c)
      (Pi.single (M := fun s : RootSeq (ν := ν) α =>
        leftStandard Q Λ s.1 (RootSeq.isRedOrdered α s))
        s (leftStandardUnit Q Λ s.1 (RootSeq.isRedOrdered α s))) s' =
      tensorFlip (mk (c.1 * e s.1 (RootSeq.isRedOrdered α s))) •
        leftStandardUnit Q Λ s'.1 (RootSeq.isRedOrdered α s') := by
  rw [single_leftStandardUnit_eq, ← rootReflectEquiv_apply hα, rootReflectConj_apply,
    rootReflectEquiv_apply, rootAction_mk, rootReflect_mk]

end StendhalAlgebra

end Categorification.Stendhal
