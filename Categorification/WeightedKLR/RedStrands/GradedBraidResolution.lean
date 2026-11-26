/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidFunctor
import Categorification.WeightedKLR.RedStrands.GradedBraidDerivedInjective
import Categorification.Algebra.DerivedKernelShift
import Categorification.Algebra.ProjectiveKProjective
import Categorification.Algebra.Graded.InduceShortExact
import Categorification.Algebra.Graded.EulerCharacteristic

/-!
# The braid functor along resolutions with vanishing `Tor`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Corollary 6.10. Call a finite-dimensional graded right `T^λ`-module `N` *braid-concentrated*
when its derived braid `N ⊗ᴸ B` has no cohomology outside degree zero (`BraidConcentrated`).
Projective modules are braid-concentrated (`braidConcentrated_of_projective`). In a short exact
sequence `0 → K → P → N → 0` with `P` and `N` braid-concentrated, `K` is braid-concentrated and
the braid functor `𝔅_σ = - ⊗_{T^λ} B` keeps the sequence exact (`braidConcentrated_kernel`). So
`𝔅_σ` preserves every short exact sequence of a finite projective resolution of a
braid-concentrated module (`preserved_of_braidConcentrated`), and the class of `𝔅_σ N` is the
alternating sum of the classes of `𝔅_σ P_j`.

## Main definitions and results

* `BraidConcentrated N`
* `braidConcentrated_of_projective`
* `braidConcentrated_kernel`
* `preserved_of_braidConcentrated`
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite CategoryTheory CategoryTheory.Limits
open DG DG.DegreeZero
open DG.DerivedCategory (cohomologyAddEquiv)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)

local notation "𝒞" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
  (List.finRange ℓ))
local notation "𝒞'" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
  (List.map σ (List.finRange ℓ)))
local notation "𝒳" => braidingBimodule k Q Λ ν (List.finRange ℓ) (List.map σ (List.finRange ℓ))
local notation "𝒯" => TensorProductAlgebra k Q Λ ν
local notation "𝒯σ" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "𝒢" => rouquierGrading Q hR Λ
local notation "𝒜" Ω => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Ω) ν)

/-- The inverse of `cornerOpRingHom`. -/
private def cornerOpRingHomInv : 𝒯ᵐᵒᵖ →+* 𝒞ᵐᵒᵖ where
  toFun t := op ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm t.unop)
  map_one' := by rw [MulOpposite.unop_one, map_one, MulOpposite.op_one]
  map_mul' c d := by rw [MulOpposite.unop_mul, map_mul, MulOpposite.op_mul]
  map_zero' := by rw [MulOpposite.unop_zero, map_zero, MulOpposite.op_zero]
  map_add' c d := by rw [MulOpposite.unop_add, map_add, MulOpposite.op_add]

private instance : RingHomInvPair (cornerOpRingHomInv (Λ := Λ) hρ hQ)
    (cornerOpRingHom (Λ := Λ) hρ hQ) :=
  ⟨by ext t; exact congrArg op (RingEquiv.apply_symm_apply _ t.unop),
   by ext c; exact congrArg op (RingEquiv.symm_apply_apply _ c.unop)⟩

private instance : RingHomInvPair (cornerOpRingHom (Λ := Λ) hρ hQ)
    (cornerOpRingHomInv (Λ := Λ) hρ hQ) :=
  RingHomInvPair.symm _ _

/-- A projective right `T^λ`-module is projective over the corner. -/
theorem projective_cornerRes (P : GFin (𝒜 Λ)) [Module.Projective 𝒯ᵐᵒᵖ P.carrier] :
    Module.Projective 𝒞ᵐᵒᵖ (CornerRes 𝒢 hρ hQ P) :=
  Module.Projective.of_equiv (σ := cornerOpRingHomInv (Λ := Λ) hρ hQ)
    (σ' := cornerOpRingHom (Λ := Λ) hρ hQ)
    (M := P.carrier)
    { toFun := fun p => p
      invFun := fun p => p
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun t p => by
        change t • p = cornerOpRingHom hρ hQ (cornerOpRingHomInv hρ hQ t) • p
        rw [RingHomInvPair.comp_apply_eq₂] }

variable [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
    (List.finRange ℓ)))ᵐᵒᵖ]
  [HasDerivedCategory.{w} (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
    (List.map σ (List.finRange ℓ))))ᵐᵒᵖ]

/-- The derived braid of the corner restriction of `N`. -/
abbrev derivedBraidObj (N : GFin (𝒜 Λ)) : DG.DerivedCategory.{w} 𝒞'ᵐᵒᵖ :=
  (braidingFunctor.{w} k Q Λ ν (List.finRange ℓ) (List.map σ (List.finRange ℓ))).obj
    (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor 𝒞ᵐᵒᵖ).obj
      (ModuleCat.of 𝒞ᵐᵒᵖ (CornerRes 𝒢 hρ hQ N))))

variable (Λ ν) in
/-- **Braid-concentrated modules**: the derived braid `N ⊗ᴸ B` has no cohomology outside degree
zero. -/
def BraidConcentrated (N : GFin (𝒜 Λ)) : Prop :=
  ∀ n : ℤ, n ≠ 0 → IsZero ((DG.DerivedCategory.homologyFunctor (A := 𝒞'ᵐᵒᵖ) ℤ n).obj
    (derivedBraidObj.{w} hρ hQ σ hR N))

set_option backward.isDefEq.respectTransparency false in
/-- **Projective modules are braid-concentrated.** -/
theorem braidConcentrated_of_projective (P : GFin (𝒜 Λ)) [Module.Projective 𝒯ᵐᵒᵖ P.carrier] :
    BraidConcentrated.{w} Λ ν hρ hQ σ hR P := by
  intro n hn
  have := projective_cornerRes hρ hQ hR P
  let M := OpBimodule 𝒞 𝒳
  let e := derivedTensorObjIso (A := 𝒞'ᵐᵒᵖ) (B := 𝒞ᵐᵒᵖ) (M := M)
    («P» := DGModuleCat.of 𝒞ᵐᵒᵖ (InDegreeZero (CornerRes 𝒢 hρ hQ P)))
    (show IsKProjective 𝒞ᵐᵒᵖ (InDegreeZero (CornerRes 𝒢 hρ hQ P)) from
      InDegreeZero.isKProjective)
  let Z := DGModuleCat.of 𝒞'ᵐᵒᵖ
    (TensorProductOver 𝒞ᵐᵒᵖ (InDegreeZero M) (InDegreeZero (CornerRes 𝒢 hρ hQ P)))
  have hZ : IsZero ((DG.DerivedCategory.homologyFunctor (A := 𝒞'ᵐᵒᵖ) ℤ n).obj
      (DG.DerivedCategory.Q.obj Z)) := by
    let : Subsingleton (cocycles Z n) := ⟨fun x y => by
      apply Subtype.ext
      have hx := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp x.2).1
      have hy := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp y.2).1
      exact hx.trans hy.symm⟩
    let : Subsingleton (cohomology Z n) := (cohomology.mk_surjective Z n).subsingleton
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)
  exact hZ.of_iso ((DG.DerivedCategory.homologyFunctor ℤ n).mapIso e)

end Categorification.Stendhal.BraidedStendhalAlgebra
