/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRoot

/-!
# Partial standard modules as left modules over `T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §6.1, proof
of Lemma 6.8, in the left-module form of `Stendhal.leftStandard`. The partial standardization
keeps the red cuts of every red strand except one: the loadings are compared by their block
root `adjacentBlockRoot a b`, which reads the black counts at every red strand, with the count at
`λ_b` for both labels `a` and `b`. For a red-ordered loading `s`, the submodule of the projective
`T^λ e(s)` is the left ideal spanned by the `e(t) c e(s)` with the root of `t` strictly above the
root of `s`, and the partial standard module is the quotient.

## Main definitions

* `leftPartialUpper`: the left ideal spanned by the `e(t) c e(s)` with a higher root.
* `leftPartialKernel`: its trace on `T^λ e(s)`.
* `leftPartialStandard`: the quotient `T^λ e(s) / leftPartialKernel`.

## Main results

* `leftPartialStandardLift`: a vector `z` with `e(t) c z = 0` for all `t` with a higher root
  gives the map `T^λ e(s) / leftPartialKernel → Z` sending `[e(s)]` to `e(s) z`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (a b : Fin ℓ)

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν

/-- The left ideal of `T^λ` spanned by the `e(t) c e(s)` whose root is strictly above the root
of `s`. -/
def leftPartialUpper (s : Seq μ) (hs : IsRedOrdered s) : Submodule A A :=
  Submodule.span A
    {z | ∃ (t : Seq μ) (ht : IsRedOrdered t) (c : A),
      adjacentBlockRoot a b s < adjacentBlockRoot a b t ∧
        z = seqIdem Q Λ t ht * c * seqIdem Q Λ s hs}

/-- The kernel of `T^λ e(s)` onto its partial standard module. -/
abbrev leftPartialKernel (s : Seq μ) (hs : IsRedOrdered s) :
    Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  (leftPartialUpper Q Λ a b s hs).comap (lIdeal (seqIdem Q Λ s hs)).subtype

/-- **The left partial standard module** `T^λ e(s) / leftPartialKernel`. -/
abbrev leftPartialStandard (s : Seq μ) (hs : IsRedOrdered s) : Type :=
  lIdeal (seqIdem Q Λ s hs) ⧸ leftPartialKernel Q Λ a b s hs

/-- The generator `[e(s)]` of the partial standard module. -/
def leftPartialStandardUnit (s : Seq μ) (hs : IsRedOrdered s) : leftPartialStandard Q Λ a b s hs :=
  Submodule.Quotient.mk ⟨seqIdem Q Λ s hs, seqIdem_mul_self Q Λ s hs⟩

variable {Q Λ a b}

theorem seqIdem_mul_mul_seqIdem_mem_leftPartialUpper {s t : Seq μ} (hs : IsRedOrdered s)
    (ht : IsRedOrdered t) (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b t) (c : A) :
    seqIdem Q Λ t ht * c * seqIdem Q Λ s hs ∈ leftPartialUpper Q Λ a b s hs :=
  Submodule.subset_span ⟨t, ht, c, hlt, rfl⟩

theorem leftPartialStandard_exists_smul_unit (s : Seq μ) (hs : IsRedOrdered s)
    (v : leftPartialStandard Q Λ a b s hs) :
    ∃ c : A, v = c • leftPartialStandardUnit Q Λ a b s hs := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  refine ⟨y, ?_⟩
  rw [leftPartialStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext y.2.symm

variable {Z : Type*} [AddCommGroup Z] [Module (TensorProductAlgebra k Q Λ ν) Z]

theorem leftPartialUpper_smul_eq_zero (s : Seq μ) (hs : IsRedOrdered s) (z : Z)
    (hz : ∀ (t : Seq μ) (ht : IsRedOrdered t) (c : A),
      adjacentBlockRoot a b s < adjacentBlockRoot a b t → (seqIdem Q Λ t ht * c) • z = 0)
    {w : A} (hw : w ∈ leftPartialUpper Q Λ a b s hs) : w • z = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, ht, c, hst, rfl⟩ := hw
    rw [mul_assoc]
    exact hz t ht _ hst
  | zero => exact zero_smul _ _
  | add _ _ _ _ h₁ h₂ => rw [add_smul, h₁, h₂, add_zero]
  | smul c _ _ h => rw [smul_eq_mul, mul_smul, h, smul_zero]

/-- **The universal property of the partial standard module**: if `e(t) c z = 0` whenever the
root of `t` lies strictly above the root of `s`, then `y ↦ y z` descends to the partial
standard module. -/
def leftPartialStandardLift (s : Seq μ) (hs : IsRedOrdered s) (z : Z)
    (hz : ∀ (t : Seq μ) (ht : IsRedOrdered t) (c : A),
      adjacentBlockRoot a b s < adjacentBlockRoot a b t → (seqIdem Q Λ t ht * c) • z = 0) :
    leftPartialStandard Q Λ a b s hs →ₗ[A] Z :=
  (leftPartialKernel Q Λ a b s hs).liftQ (lIdealEval s hs z)
    fun _ hy => leftPartialUpper_smul_eq_zero s hs z hz hy

theorem leftPartialStandardLift_unit (s : Seq μ) (hs : IsRedOrdered s) (z : Z)
    (hez : seqIdem Q Λ s hs • z = z)
    (hz : ∀ (t : Seq μ) (ht : IsRedOrdered t) (c : A),
      adjacentBlockRoot a b s < adjacentBlockRoot a b t → (seqIdem Q Λ t ht * c) • z = 0) :
    leftPartialStandardLift s hs z hz (leftPartialStandardUnit Q Λ a b s hs) = z := by
  change (seqIdem Q Λ s hs) • z = z
  exact hez

end Categorification.Stendhal
