/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorDegrees
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor
import Categorification.Algebra.ProjectiveKProjective

/-!
# Ambient acyclicity of the outgoing label-two exterior term

The complementary exterior term is the actual regular ideal of an
idempotent. In degree zero it is K-projective, so ambient derived tensor
with it has homology only in degree zero for every right coefficient.
-/

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable (k : Type) [Field k]
local notation "T" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "p" => labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal p

/-- The outgoing exterior term is projective over the actual two-red algebra. -/
theorem labelTwoLeftExterior_projective : Module.Projective T P := by
  have hp := (isIdempotentElem_labelTwoLeftExteriorProjector (parameter k)).eq
  refine Module.Projective.of_split (P).subtype
    { toFun := fun a => ⟨a * p, by
        change (a * p) * p = a * p
        rw [mul_assoc, hp]⟩
      map_add' := fun a b => Subtype.ext (add_mul a b p)
      map_smul' := fun a b => Subtype.ext (mul_assoc a b p) } ?_
  ext a
  exact a.2

variable [HasDerivedCategory.{w,0}
  (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))]
  [HasDerivedCategory.{w,0} k]
variable (N : Type) [AddCommGroup N] [Module k N]
  [Module (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))ᵐᵒᵖ N]
  [SMulCommClass k (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))ᵐᵒᵖ N]

/-- The derived tensor with the actual outgoing exterior term has no
homology away from zero, for every right coefficient. -/
theorem labelTwoLeftExterior_derivedTensorHomology_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := k) ℤ n).obj
      ((derivedTensor k T N).obj (Q.obj (DGModuleCat.of T (InDegreeZero P))))) := by
  let : Module.Projective T P := labelTwoLeftExterior_projective k
  let K := DGModuleCat.of T (InDegreeZero P)
  have hK : IsKProjective.{0} T (InDegreeZero P) := InDegreeZero.isKProjective
  apply isZero_derivedTensorHomology_of_loading_annihilation (M := N)
    hK (𝟙 K) DGModuleHom.isQuasiIso_id _ n hn
  intro i hi u hu
  have h : (u : InDegreeZero P) = 0 :=
    ((InDegreeZero.mem_grading_iff _).mp hu).resolve_left hi
  rw [h]
  exact Submodule.zero_mem _

end
end Categorification.Stendhal.LabelTwo
