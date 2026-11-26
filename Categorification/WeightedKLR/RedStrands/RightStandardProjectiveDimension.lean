/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ProjectiveDimensionEquivalence
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.StandardProjectiveDimension
import Categorification.WeightedKLR.RedStrands.GradedRightStandardModule

/-!
# Right standard modules have finite projective dimension

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Corollary 5.22, for the standard modules `e(s) T / U_s` read as right modules. The left form
(`exists_hasProjectiveDimensionLT_stdModule`) transports along the coefficient equivalence
`loadingStandardLeftEquiv`, which reflects diagrams, first to the corner `e_λ V e_λ` and then,
through `violCornerEquiv`, to `T^λ`.

## Main results

* `exists_hasProjectiveDimensionLT_loadingStandard`: over the corner `e_λ V e_λ`.
* `exists_hasProjectiveDimensionLT_rightStandard`: over `T^λ`.

Both carry the route hypothesis `AllFiniteDeltaInjective` of Corollary 5.22.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR MulOpposite

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I}

local notation "ord" => List.finRange ℓ

include hρ in
/-- **Corollary 5.22, right form over the corner** (Webster, arXiv:1309.3796v2): for a
red-ordered loading `s`, the standard module `e(s) T / U_s` has finite projective dimension as a
right module over `e_λ V e_λ`. Route hypothesis: `AllFiniteDeltaInjective`, as for the left
form. -/
theorem exists_hasProjectiveDimensionLT_loadingStandard (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    ∃ N : ℕ, HasProjectiveDimensionLT
      (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s ord)) N := by
  obtain ⟨N, hN⟩ := exists_hasProjectiveDimensionLT_stdModule Q hQ hR hall
    (Λ ∘ ⇑(1 : Equiv.Perm (Fin ℓ))) ν ⟨s, hs⟩
  have h := hasProjectiveDimensionLT_of_semilinearEquiv
    (leftCoefficientEquiv (Λ := Λ) hρ hQ 1) (loadingStandardLeftEquiv hρ hQ 1 hs) N hN
  have key : ∀ (κ : List (Fin ℓ)) (t : KLR.Seq (stendhalWeight ℓ ν)), κ = ord → t = s →
      HasProjectiveDimensionLT
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ)) N →
      HasProjectiveDimensionLT
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord)ᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s ord)) N := by
    rintro _ _ rfl rfl h
    exact h
  exact ⟨N, key _ _ (by simp) (Seq.redPerm_one s) h⟩

/-- `rightCornerHom` as a ring isomorphism `(T^λ)ᵐᵒᵖ ≃ (e_λ V e_λ)ᵐᵒᵖ`. -/
def rightCornerEquiv : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ≃+*
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord)ᵐᵒᵖ :=
  { rightCornerHom (Λ := Λ) (ν := ν) hρ hQ with
    invFun := fun c => op (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ c.unop)
    left_inv := fun a => congrArg op
      ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).apply_symm_apply a.unop)
    right_inv := fun c => congrArg op
      ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm_apply_apply c.unop) }

/-- **Corollary 5.22, right form** (Webster, arXiv:1309.3796v2): for a red-ordered loading `s`,
the standard module `e(s) T / U_s` has finite projective dimension as a right `T^λ`-module.
Route hypothesis: `AllFiniteDeltaInjective`, as for the left form. -/
theorem exists_hasProjectiveDimensionLT_rightStandard (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    ∃ N : ℕ, HasProjectiveDimensionLT
      (ModuleCat.of (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (RightStandard Λ hρ hQ s)) N := by
  obtain ⟨N, hN⟩ := exists_hasProjectiveDimensionLT_loadingStandard (Λ := Λ) hρ hQ hR hall hs
  let φ : RightStandard Λ hρ hQ s ≃ₛₗ[(rightCornerEquiv (Λ := Λ) (ν := ν) hρ hQ :
      (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ →+*
        (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ord)ᵐᵒᵖ)]
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s ord :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => by rfl }
  exact ⟨N, hasProjectiveDimensionLT_of_semilinearEquiv _ φ N hN⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
