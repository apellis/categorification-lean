/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedOrderedStandardResolution
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# Ordered covers of Webster's partial standards

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21). The retained-cut
kernel filtrations construct projective resolutions of the actual partial
standards. To apply the braid we require the higher loading labels to be
strictly above every inverse-braid coefficient layer after relabelling.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν


local notation "Label" => {s : Seq μ // IsRedOrdered s}
set_option quotPrecheck false in
local notation "e" s:arg => orderedLoadingIdemAt Q Λ κ (Seq.redPerm σ s.1) (redWord_relabel σ s.2)
set_option quotPrecheck false in
local notation "S" a:arg b:arg s:arg => blockPartialStandardAt Q Λ (Seq.redPerm σ s.1)
  a b κ (redWord_relabel σ s.2)
set_option quotPrecheck false in
local notation "K" a:arg b:arg s:arg => blockLoadingKernelAt Q Λ (Seq.redPerm σ s.1)
  a b κ (redWord_relabel σ s.2)

private def opLoadingIdealEquiv {R : Type} [Ring R] (c : R) : lIdeal (op c) ≃ₗ[Rᵐᵒᵖ] rIdeal c where
  toFun x := ⟨x.1.unop, congrArg unop x.2⟩
  invFun x := ⟨op x.1, congrArg op x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The retained-cut kernel in the common ordered corner. -/
def blockPartialKernelObj (a b : Fin ℓ) (s : Label) : ModuleCat Cᵐᵒᵖ := by
  let P := rIdeal (e s)
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Cᵐᵒᵖ P := Submodule.module P
  let J : Submodule Cᵐᵒᵖ P := K a b s
  let : AddCommGroup J := Submodule.addCommGroup J
  exact ModuleCat.of Cᵐᵒᵖ J

private def blockPartialCoverMap (a b : Fin ℓ) (s : Label) :
    lIdeal (op (e s)) →ₗ[Cᵐᵒᵖ] S a b s := by
  let P := rIdeal (e s)
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Cᵐᵒᵖ P := Submodule.module P
  let J : Submodule Cᵐᵒᵖ P := K a b s
  change lIdeal (op (e s)) →ₗ[Cᵐᵒᵖ] P ⧸ J
  exact J.mkQ.comp (opLoadingIdealEquiv (e s)).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- A retained-kernel filtration by partial standards constructs their ordered covers. -/
def blockPartialStandardOrderedCovers (a b : Fin ℓ) (higher : Label → Label → Prop)
    (hK : ∀ s : Label, ∃ m : List Label, (∀ t ∈ m, higher s t) ∧
      ModuleFiltration.HasFiltration (fun t => S a b t) m
        (blockPartialKernelObj σ (Q := Q) (Λ := Λ) a b s)) :
    ModuleFiltration.OrderedStandardCovers (fun s => S a b s) (fun s => op (e s)) higher where
  quotient s := blockPartialCoverMap σ (Q := Q) (Λ := Λ) a b s
  surjective s := by
    let P := rIdeal (e s)
    let : AddCommGroup P := Submodule.addCommGroup P
    let : Module Cᵐᵒᵖ P := Submodule.module P
    let J : Submodule Cᵐᵒᵖ P := K a b s
    exact J.mkQ_surjective.comp (opLoadingIdealEquiv (e s)).surjective
  projective s := by
    have he : IsIdempotentElem (e s) := isIdempotentElem_violLoadingIdem (redWord_relabel σ s.2)
    have : Module.Projective Cᵐᵒᵖ (rIdeal (e s)) := rIdeal_projective he
    exact Module.Projective.of_equiv (opLoadingIdealEquiv (e s)).symm
  kernel s := by
    obtain ⟨m, hm, h⟩ := hK s
    refine ⟨m, hm, ?_⟩
    let E := opLoadingIdealEquiv (e s)
    let P := rIdeal (e s)
    let : AddCommGroup P := Submodule.addCommGroup P
    let : Module Cᵐᵒᵖ P := Submodule.module P
    let J : Submodule Cᵐᵒᵖ P := K a b s
    let : AddCommGroup J := Submodule.addCommGroup J
    let q := blockPartialCoverMap σ (Q := Q) (Λ := Λ) a b s
    let F : LinearMap.ker q ≃ₗ[Cᵐᵒᵖ] J :=
      { toFun x := ⟨E x.1, (Submodule.Quotient.mk_eq_zero J).mp x.2⟩
        invFun y := ⟨E.symm y.1, by
          change J.mkQ (E (E.symm y.1)) = 0
          rw [E.apply_symm_apply]
          exact (Submodule.Quotient.mk_eq_zero J).mpr y.2⟩
        map_add' x y := Subtype.ext (map_add E x.1 y.1)
        map_smul' r x := Subtype.ext (map_smul E r x.1)
        left_inv x := Subtype.ext (E.symm_apply_apply x.1)
        right_inv y := Subtype.ext (E.apply_symm_apply y.1) }
    exact h.of_equiv F.symm

include hρ hQ in
/-- The retained-cut filtrations give the partial-standard vanishing used in (6.21)
when each higher loading is above every reflected coefficient label. -/
theorem blockPartialStandardAt_braid_homology_vanish_of_ordered_kernels
    (a b : Fin ℓ) (higher : Label → Label → Prop)
    (htrans : ∀ r s t, higher r s → higher s t → higher r t)
    (hK : ∀ s : Label, ∃ m : List Label, (∀ t ∈ m, higher s t) ∧
      ModuleFiltration.HasFiltration (fun t => S a b t) m
        (blockPartialKernelObj σ (Q := Q) (Λ := Λ) a b s))
    (κ' : List (Fin ℓ))
    [HasDerivedCategory.{w, 0} Cᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ')ᵐᵒᵖ]
    {m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s}}
    (hf : ModuleFiltration.HasFiltration
      (fun c => ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) c.1 κ)) m
      (ModuleCat.of Cᵐᵒᵖ (braidingBimodule k Q Λ ν κ' κ)))
    (s : Label)
    (horder : ∀ t, higher s t → ∀ c ∈ m, StendhalLT ((Seq.redPermEquiv σ).symm c.1) t.1)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ')ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν κ κ').obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of Cᵐᵒᵖ (InDegreeZero (S a b s)))))) := by
  let D := blockPartialStandardOrderedCovers σ (Q := Q) (Λ := Λ) a b higher hK
  apply braid_homology_vanish_of_reflected_filtration_loading_support hρ hQ σ κ' hf
    (D.projectiveResolution s) _ n hn
  intro j
  obtain ⟨J, label, inc, hl, hspan⟩ := D.projectiveResolution_loading_support s htrans j
  exact ⟨J, label, inc, fun i => horder _ (hl i), hspan⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
