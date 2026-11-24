/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedProjectiveResolution
import Categorification.WeightedKLR.RedStrands.LeftStandardModule

/-!
# Ordered support in left-standard projective resolutions

Webster, arXiv:1309.3796v2, Lemma 6.11, p. 65, uses projective terms supported
at higher loading labels. The higher standard filtrations of Corollary 5.21
give exactly the cover data for this construction.
-/

open CategoryTheory MulOpposite

noncomputable section

namespace Categorification.Stendhal

open KLR ModuleFiltration

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "Label" => {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}
set_option quotPrecheck false in
local notation "std" => fun s : Label => ModuleCat.of A (leftStandard Q Λ s.1 s.2)
set_option quotPrecheck false in
local notation "e" => fun s : Label => seqIdem Q Λ s.1 s.2
set_option quotPrecheck false in
local notation "above" => fun (s t : Label) => StendhalLT s.1 t.1
set_option quotPrecheck false in
local notation "U" s:arg =>
  (leftUpper Q Λ s.1 s.2).comap (lIdeal (seqIdem Q Λ s.1 s.2)).subtype

/-- The standard-stratification kernel filtrations give the ordered loading covers
used to build projective resolutions in Webster's Lemma 6.11. -/
def orderedStandardCovers
    (hU : ∀ s : Label, ∃ m : List Label, (∀ t ∈ m, above s t) ∧
      HasFiltration std m (ModuleCat.of A (U s))) :
    OrderedStandardCovers std e above where
  quotient s := (U s).mkQ
  surjective s := Submodule.mkQ_surjective (U s)
  projective s := by
    refine Module.Projective.of_split (lIdeal (seqIdem Q Λ s.1 s.2)).subtype
      { toFun := fun b => ⟨b * seqIdem Q Λ s.1 s.2, by
          change _ * _ = _
          rw [mul_assoc, seqIdem_mul_self]⟩
        map_add' := fun a b => Subtype.ext (add_mul a b _)
        map_smul' := fun a b => Subtype.ext (mul_assoc a b _) } ?_
    ext y
    exact y.2
  kernel s := by
    obtain ⟨m, hm, h⟩ := hU s
    refine ⟨m, hm, ?_⟩
    change HasFiltration std m (ModuleCat.of A (LinearMap.ker ((U s).mkQ)))
    rw [Submodule.ker_mkQ]
    exact h

/-- The resolution of a left loading standard over the standard-stratification kernel
filtration has higher loading support at each positive homological degree. -/
theorem exists_ordered_projectiveResolution_leftStandard
    (hU : ∀ s : Label, ∃ m : List Label, (∀ t ∈ m, above s t) ∧
      HasFiltration std m (ModuleCat.of A (U s))) (s : Label) :
    ∃ P : ProjectiveResolution (std s), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Label)
        (inc : ∀ j, lIdeal (e (label j)) →ₗ[A] P.complex.X (n + 1)),
        (∀ j, above s (label j)) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span A {y | ∃ j z, inc j z = y} := by
  let D := orderedStandardCovers Q Λ hU
  refine ⟨D.projectiveResolution s, ?_⟩
  exact D.projectiveResolution_loading_support s (by
    intro a b c hab hbc
    exact ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca =>
      hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩)

/-- Reflection along a ring isomorphism fixing the loading idempotents gives the
same higher loading support for the corresponding right standards. -/
theorem exists_ordered_projectiveResolution_reflectedLeftStandard
    (hU : ∀ s : Label, ∃ m : List Label, (∀ t ∈ m, above s t) ∧
      HasFiltration std m (ModuleCat.of A (U s)))
    (σ : A ≃+* Aᵐᵒᵖ) (hσ : ∀ c : Label, σ (e c) = op (e c)) (s : Label) :
    ∃ P : ProjectiveResolution ((ModuleCat.restrictScalars σ.symm.toRingHom).obj (std s)),
      ∀ n : ℕ, ∃ (J : Type) (label : J → Label)
        (inc : ∀ j, lIdeal (op (e (label j))) →ₗ[Aᵐᵒᵖ] P.complex.X (n + 1)),
        (∀ j, above s (label j)) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span Aᵐᵒᵖ {y | ∃ j z, inc j z = y} := by
  have he : (fun c : Label => σ (e c)) = fun c => op (e c) := funext hσ
  let D : OrderedStandardCovers (fun c => (ModuleCat.restrictScalars σ.symm.toRingHom).obj (std c))
      (fun c => op (e c)) above :=
    he ▸ (orderedStandardCovers Q Λ hU).transport σ
  refine ⟨D.projectiveResolution s, ?_⟩
  exact D.projectiveResolution_loading_support s (by
    intro a b c hab hbc
    exact ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca =>
      hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩)

end Categorification.Stendhal
