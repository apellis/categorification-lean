/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongCornerProjective
import Categorification.WeightedKLR.RedStrands.BraidedAppendIdentity
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

set_option backward.isDefEq.respectTransparency false

/-!
# The bimodule of `𝔈_i` at every red order is projective on both sides

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1. At a
red order `κ`, appending a black strand at the right restricts to a nonunital ring map
`appendCornerHom κ` from the corner of the quotient by violated idempotents for `ν` to the one
for `i + ν`. The functor `𝔈_i` on braided diagrams at the order `κ` is induction along this map;
its bimodule is the corner `R ψ(1)` of `InductionAlong`.

* `appendCorner_projective_left`: it is projective as a left module, being a direct summand of
  the regular module.
* `appendCorner_projective_right_finRange`: at the order `λ_1, …, λ_ℓ` it is projective as a
  right module. Under `violCornerEquiv` (`B_e ≃ T^λ`) the map is Webster's `T^λ → T^λ`
  adjoining a black strand (`violCornerEquiv_appendViol`), whose corner is projective by
  Theorem 4.31 (`projective_appendBlackCorner`).
* `appendCorner_projective_right`: the same at every ordering `κ` of the red labels, by
  relabelling the red strands (`violCornerRedPermEquiv`, `violRedPermEquiv_appendViol`).

These are the two projectivity inputs of the derived form of Proposition 6.7.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv InductionAlong MulOpposite

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace BraidedStendhalAlgebra

section Hom

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

/-- Appending a black strand at the right, restricted to the corners at the red order `κ` of the
quotients by violated idempotents. -/
noncomputable def appendCornerHom (κ : List (Fin ℓ)) :
    (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner →ₙ+*
      (isIdempotentElem_violMk_redProj k Q Λ ({i} + ν) κ).Corner where
  toFun x := ⟨appendViol Q Λ i ν x.1, appendViol_mem_corner Q Λ i ν κ x.2⟩
  map_mul' x y := Subtype.ext (map_mul (appendViol Q Λ i ν) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (appendViol Q Λ i ν))
  map_add' x y := Subtype.ext (map_add (appendViol Q Λ i ν) x.1 y.1)

@[simp] theorem appendCornerHom_val (κ : List (Fin ℓ))
    (x : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner) :
    (appendCornerHom Q Λ i ν κ x).1 = appendViol Q Λ i ν x.1 := rfl

/-- The bimodule of `𝔈_i` at a red order is a projective left module. -/
theorem appendCorner_projective_left (κ : List (Fin ℓ)) :
    Module.Projective (isIdempotentElem_violMk_redProj k Q Λ ({i} + ν) κ).Corner
      (Corner (appendCornerHom Q Λ i ν κ)) :=
  projective_corner_left _

end Hom

section Right

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {i : I} {ν : Multiset I}

/-- **The bimodule of `𝔈_i` is a projective right module at the order `λ_1, …, λ_ℓ`**
(arXiv:1309.3796v2, Theorem 4.31 through §6.1), for symmetric Rouquier polynomials `Q`. -/
theorem appendCorner_projective_right_finRange
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    {ρ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ({i} + ν)))) → List ℕ}
    (hρ : IsReducedChoice ρ) (hρ' : IsReducedChoice ρ') (hQ : KLRSymm Q)
    (C : QuantumGroup.CartanDatum I) (hR : IsRouquierQ C Q) :
    Module.Projective (isIdempotentElem_violMk_redProj k Q Λ ν (List.finRange ℓ)).Cornerᵐᵒᵖ
      (Corner (appendCornerHom Q Λ i ν (List.finRange ℓ))) := by
  have := projective_appendBlackCorner (Q := Q) (Λ := Λ) i ν C hR
  exact projective_corner_of_ringEquiv (φ' := appendBlackNU (Q := Q) (Λ := Λ) i ν)
    (violCornerEquiv hρ hQ) (violCornerEquiv hρ' hQ)
    (fun a => violCornerEquiv_appendViol hρ hρ' hQ a)

theorem violCornerRedPermEquiv_val {Λ' : Fin ℓ → I →₀ ℕ} (σ : Perm (Fin ℓ))
    (h : ∀ r, Λ' r = Λ (σ r)) (κ : List (Fin ℓ))
    (x : (isIdempotentElem_violMk_redProj k Q Λ' ν κ).Corner) :
    (violCornerRedPermEquiv σ h κ x).1 = violRedPermEquiv σ h x.1 := rfl

/-- Relabelling the red strands intertwines appending a black strand on the corners. -/
theorem violCornerRedPermEquiv_appendCornerHom (σ : Perm (Fin ℓ))
    (a : (isIdempotentElem_violMk_redProj k Q (Λ ∘ σ) ν (List.finRange ℓ)).Corner) :
    violCornerRedPermEquiv (Λ' := Λ ∘ σ) (ν := {i} + ν) σ (fun _ => rfl) (List.finRange ℓ)
      (appendCornerHom Q (Λ ∘ σ) i ν (List.finRange ℓ) a) =
      appendCornerHom Q Λ i ν ((List.finRange ℓ).map σ)
        (violCornerRedPermEquiv (Λ' := Λ ∘ σ) σ (fun _ => rfl) (List.finRange ℓ) a) := by
  apply Subtype.ext
  rw [violCornerRedPermEquiv_val, appendCornerHom_val, appendCornerHom_val,
    violCornerRedPermEquiv_val, violRedPermEquiv_appendViol]

/-- **The bimodule of `𝔈_i` is a projective right module at every ordering `κ` of the red
labels** (arXiv:1309.3796v2, Theorem 4.31 through §6.1), for symmetric Rouquier `Q`. -/
theorem appendCorner_projective_right
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    {ρ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ({i} + ν)))) → List ℕ}
    (hρ : IsReducedChoice ρ) (hρ' : IsReducedChoice ρ') (hQ : KLRSymm Q)
    (C : QuantumGroup.CartanDatum I) (hR : IsRouquierQ C Q)
    {κ : List (Fin ℓ)} (hκ : κ.Perm (List.finRange ℓ)) :
    Module.Projective (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ
      (Corner (appendCornerHom Q Λ i ν κ)) := by
  obtain ⟨σ, rfl⟩ := exists_perm_eq_map_finRange hκ
  have := appendCorner_projective_right_finRange (Λ := Λ ∘ σ) (i := i) hρ hρ' hQ C hR
  exact projective_corner_of_ringEquiv (φ' := appendCornerHom Q (Λ ∘ σ) i ν (List.finRange ℓ))
    (violCornerRedPermEquiv (Λ' := Λ ∘ σ) (ν := ν) σ (fun _ => rfl) (List.finRange ℓ)).symm
    (violCornerRedPermEquiv (Λ' := Λ ∘ σ) (ν := {i} + ν) σ (fun _ => rfl)
      (List.finRange ℓ)).symm (fun a => by
        rw [RingEquiv.symm_apply_eq, violCornerRedPermEquiv_appendCornerHom,
          RingEquiv.apply_symm_apply])

end Right

end BraidedStendhalAlgebra

end Categorification.Stendhal
