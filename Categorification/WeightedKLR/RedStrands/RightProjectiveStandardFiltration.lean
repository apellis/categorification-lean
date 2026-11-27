/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltration

/-!
# Right loading projectives have standard filtrations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.21 (v2: Proposition 5.20), for the right loading projectives `e(t) e_κ V e_κ`
over the corner at a red order `κ = σ(1, …, ℓ)`. The coefficient equivalence
`leftCoefficientEquiv`, which relabels the red strands and reflects diagrams, carries the left
projective `T^{λ ∘ σ} e(s)` to the right projective `e(σ s) e_κ V e_κ`
(`loadingProjectiveLeftEquiv`) and the left standard module `S_s` to the loading standard at
`σ s` (`loadingStandardLeftEquiv`), so the left standard filtration of Proposition 5.21
transports (`exists_hasFiltration_loadingProjective`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite ModuleFiltration

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "μ" => stendhalWeight ℓ ν

/-- A semilinear equivalence `X ≃ₛₗ[φ] Y` as a linear equivalence onto the restriction of `Y`. -/
def linearEquivRestrictScalars {R S : Type} [Ring R] [Ring S] (φ : R ≃+* S) {X Y : Type}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y] (e : X ≃ₛₗ[(φ : R →+* S)] Y) :
    X ≃ₗ[R] (ModuleCat.restrictScalars (φ : R →+* S)).obj (ModuleCat.of S Y) where
  toFun x := e x
  invFun y := e.symm y
  map_add' x y := e.map_add x y
  map_smul' r x := by
    change e (r • x) = φ r • e x
    exact e.map_smulₛₗ r x
  left_inv := e.left_inv
  right_inv := e.right_inv

include hρ hQ in
/-- **Right loading projectives have standard filtrations** (Webster, arXiv:1309.3796v3,
Proposition 5.21, right form at the red order `κ = σ(1, …, ℓ)`): if every left projective of
`T^{λ ∘ σ}` has a filtration by standard modules, then the right projective `e(σ s) e_κ V e_κ`
has a filtration by the loading standards at `σ t`, for red-ordered loadings `t`. -/
theorem exists_hasFiltration_loadingProjective
    (hstd : HasStandardFiltrations Q (Λ ∘ σ)) {s : Seq μ} (hs : IsRedOrdered s) :
    ∃ m : List {t : Seq μ // IsRedOrdered t},
      HasFiltration (fun t => ModuleCat.of Cᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1) κ)) m
        (ModuleCat.of Cᵐᵒᵖ
          (rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)))) := by
  obtain ⟨m, hm⟩ := hstd ν s hs
  let F := leftCoefficientEquiv (Λ := Λ) hρ hQ σ
  refine ⟨m, ?_⟩
  have h := hm.restrictScalars (F : Cᵐᵒᵖ →+* TensorProductAlgebra k Q (Λ ∘ σ) ν)
  exact HasFiltration.mono (fun t =>
      ⟨(linearEquivRestrictScalars F (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2)).symm⟩)
    (h.of_equiv (linearEquivRestrictScalars F
      (loadingProjectiveLeftEquiv (Λ := Λ) hρ hQ σ hs)).symm)

end Categorification.Stendhal.BraidedStendhalAlgebra
