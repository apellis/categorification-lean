/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightProjectiveStandardFiltration
import Categorification.Algebra.OrderedProjectiveResolution

set_option backward.isDefEq.respectTransparency false

/-!
# Ordered covers of right loading standards

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 5.22 (v2: Corollary 5.21) in right-module form, at the red order
`κ = σ(1, …, ℓ)`: the right projective `e(σ t) e_κ V e_κ` maps onto the loading standard at
`σ t`, and the kernel has a filtration by the loading standards at `σ c` with `c` strictly above
`t` (`exists_cover_violLoadingStandard`). The left ordered covers of `T^{λ ∘ σ}` transport along
the coefficient equivalence `leftCoefficientEquiv`, as for the standard filtrations of
`exists_hasFiltration_loadingProjective`.
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
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν

private def lIdealOpEquivRIdeal {R : Type} [Ring R] (c : R) : lIdeal (op c) ≃ₗ[Rᵐᵒᵖ] rIdeal c where
  toFun x := ⟨x.1.unop, congrArg unop x.2⟩
  invFun x := ⟨op x.1, congrArg op x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

include hρ hQ in
/-- **Ordered covers of right loading standards** (Webster, arXiv:1309.3796v3, Corollary 5.22,
right form at the red order `κ = σ(1, …, ℓ)`): given the ordered covers of the left standards of
`T^{λ ∘ σ}` (Corollary 5.22), for every red-ordered `t` there is a short exact sequence
`0 → K → e(σ t) e_κ V e_κ → S_{σ t} → 0` of right modules over the corner, with `K` filtered by
the loading standards at `σ c` for `c` strictly above `t`. -/
theorem exists_cover_violLoadingStandard
    (D : OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {t : Seq μ} (ht : IsRedOrdered t) :
    ∃ (K : ModuleCat.{0} Cᵐᵒᵖ)
      (i : K →ₗ[Cᵐᵒᵖ] rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)))
      (q : rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)) →ₗ[Cᵐᵒᵖ]
        ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ),
      Function.Injective i ∧ Function.Surjective q ∧ Function.Exact i q ∧
      ∃ l : List {c : Seq μ // IsRedOrdered c}, (∀ c ∈ l, StendhalLT t c.1) ∧
        HasFiltration (fun c => ModuleCat.of Cᵐᵒᵖ
          (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ c.1) κ)) l K := by
  let F := leftCoefficientEquiv (Λ := Λ) hρ hQ σ
  let D1 := D.transport F.symm
  let hE : ∀ c : {s : Seq μ // IsRedOrdered s},
      (ModuleCat.restrictScalars F.symm.symm.toRingHom).obj
        (ModuleCat.of T (leftStandard Q (Λ ∘ σ) c.1 c.2)) ≃ₗ[Cᵐᵒᵖ]
        ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ c.1) κ) :=
    fun c => (linearEquivRestrictScalars F (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ c.2)).symm
  let D2 := D1.congrLayers hE
  let c0 : {s : Seq μ // IsRedOrdered s} := ⟨t, ht⟩
  let f := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)
  have hidem : op f = F.symm (seqIdem Q (Λ ∘ σ) t ht) := by
    rw [RingEquiv.eq_symm_apply]
    exact leftCoefficientEquiv_loadingIdem hρ hQ σ ht
  let e : rIdeal f ≃ₗ[Cᵐᵒᵖ] lIdeal (F.symm (seqIdem Q (Λ ∘ σ) t ht)) :=
    (lIdealOpEquivRIdeal f).symm.trans (LinearEquiv.ofEq _ _ (congrArg lIdeal hidem))
  let q0 := D2.quotient c0
  obtain ⟨l, hl, hf⟩ := D2.kernel c0
  refine ⟨_, e.symm.toLinearMap ∘ₗ (LinearMap.ker q0).subtype, q0 ∘ₗ e.toLinearMap,
    e.symm.injective.comp Subtype.val_injective, (D2.surjective c0).comp e.surjective, ?_,
    l, hl, hf⟩
  intro y
  constructor
  · intro hy
    refine ⟨⟨e y, hy⟩, ?_⟩
    change e.symm (e y) = y
    exact e.symm_apply_apply y
  · rintro ⟨x, rfl⟩
    change q0 (e (e.symm x.1)) = 0
    rw [e.apply_symm_apply]
    exact x.2

end Categorification.Stendhal.BraidedStendhalAlgebra
