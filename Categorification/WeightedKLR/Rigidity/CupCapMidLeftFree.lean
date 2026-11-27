/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCapBasisApply

/-!
# The comparison map for the left freeness of `K̃^{λ⁺}_λ`

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j`. The route goes through the left
freeness of `K̃^{λ⁺}_λ`: the map

  `Θ : ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g) → K̃^{λ⁺}_λ`, `a ⊗ v ↦ a · (v γ_g)`,

over the generators `g` without dots (`MidShuffle`: a loading `s` of `λ`, a loading `t` at the
maximum and a window shuffle `u`), is bijective. This file works in the model
`L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` (`midCapModelEquiv`), with the left action of `T̃^λ`
given by the KLR relations on the model (`midLeftAlg`), and constructs `Θ` as a left
`T̃^λ`-linear map (`midTheta`).

## Main definitions

* `MidShuffle`: the generators of the corner at the window without dots.
* `MidLeftModel`: the model as a left `T̃^λ`-module.
* `midLeftGen`: the element `v γ_g` of the model, `k`-linear in `v`.
* `midTheta`: the comparison map `Θ`, left `T̃^λ`-linear.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "T" => StendhalAlgebra k Q Λ ν

variable (j hj ν ν₀) in
/-- **The generators without dots** of the corner at the window before `λ_{j+1}`: a loading `s`
of `λ`, a loading `t` at the maximum and a window shuffle `u`. These index the summands of the
left freeness of `K̃^{λ⁺}_λ`. -/
abbrev MidShuffle : Type := {g : MidGen j hj ν ν₀ // g.d = 0}

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

variable (L hL) in
/-- **The model of `K̃^{λ⁺}_λ` as a left `T̃^λ`-module**, through the action `midLeftAlg` given
by the KLR relations on the model. -/
def MidLeftModel (_hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Type _ := MidModel j hj Q Λ Λc ν ν₀ L

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : AddCommGroup (MidLeftModel L hL hR) :=
  inferInstanceAs (AddCommGroup (MidModel j hj Q Λ Λc ν ν₀ L))

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Module k (MidLeftModel L hL hR) :=
  inferInstanceAs (Module k (MidModel j hj Q Λ Λc ν ν₀ L))

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : Module T (MidLeftModel L hL hR) :=
  Module.compHom (MidModel j hj Q Λ Λc ν ν₀ L) (midLeftAlg L hL hR).toRingHom

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem midLeftModel_smul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : T)
    (y : MidLeftModel L hL hR) :
    a • y = (midLeftAlg L hL hR a (y : MidModel j hj Q Λ Λc ν ν₀ L) : MidLeftModel L hL hR) :=
  rfl

instance (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) : IsScalarTower k T (MidLeftModel L hL hR) where
  smul_assoc c a y := by
    rw [midLeftModel_smul, midLeftModel_smul, map_smul, LinearMap.smul_apply]

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

variable (L hL ρ₃) in
/-- **The element `v γ_g` of the model**, for `v ∈ L e(t_g)`, as a `k`-linear map. -/
def midLeftGen (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidShuffle j hj ν ν₀) :
    BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1) →ₗ[k] MidLeftModel L hL hR where
  toFun v := (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g.1) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L)
  map_add' v v' := by
    rw [Submodule.coe_add, Ind.tmul_add]
  map_smul' c v := by
    rw [Submodule.coe_smul, ← smul_tmul_midModel]
    rfl

theorem midLeftGen_apply (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidShuffle j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1)) :
    midLeftGen L hL ρ₃ hR g v =
      (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g.1) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L) :=
  rfl

variable (Q Λ Λc L) in
/-- **The summand `T̃^λ e(s_g) ⊗_k L e(t_g)`** of the source of `Θ`. -/
abbrev MidLeftSummand (g : MidShuffle j hj ν ν₀) : Type _ :=
  Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.1.s g.1.hs} ⊗[k]
    BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1)

variable (L hL ρ₃) in
/-- The bilinear map `(a, v) ↦ a · (v γ_g)` of a summand. -/
def midThetaBil (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidShuffle j hj ν ν₀) :
    Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.1.s g.1.hs} →ₗ[T]
      BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1) →ₗ[k] MidLeftModel L hL hR :=
  LinearMap.mk₂' T k (fun a v => (a : T) • midLeftGen L hL ρ₃ hR g v)
    (fun a a' v => by rw [Submodule.coe_add, add_smul])
    (fun c a v => by rw [Submodule.coe_smul, smul_eq_mul, mul_smul])
    (fun a v v' => by rw [map_add, smul_add])
    (fun c a v => by rw [map_smul, smul_comm])

variable (L hL ρ₃) in
/-- **The comparison map** `Θ : ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g) → K̃^{λ⁺}_λ`,
`a ⊗ v ↦ a · (v γ_g)`, in the model, left `T̃^λ`-linear. -/
def midTheta [DecidableEq (MidShuffle j hj ν ν₀)] (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    (DirectSum (MidShuffle j hj ν ν₀) (MidLeftSummand Q Λ Λc L)) →ₗ[T] MidLeftModel L hL hR :=
  DirectSum.toModule T (MidShuffle j hj ν ν₀) (MidLeftModel L hL hR) fun g =>
    AlgebraTensorModule.lift (midThetaBil L hL ρ₃ hR g)

theorem midTheta_of_tmul [DecidableEq (MidShuffle j hj ν ν₀)]
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidShuffle j hj ν ν₀)
    (a : Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.1.s g.1.hs})
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1)) :
    midTheta L hL ρ₃ hR (DirectSum.lof T _ (MidLeftSummand Q Λ Λc L) g (a ⊗ₜ v)) =
      (midLeftAlg L hL hR (a : T)
        (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g.1) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L) :
        MidLeftModel L hL hR) := by
  rw [midTheta, DirectSum.toModule_lof]
  rfl

end Categorification.Stendhal.CupCap

/-! ### The comparison map on the idempotents -/

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

/-- The idempotent `e(s)` of `T̃^λ` is the image of the KLR idempotent. -/
theorem topMap_e_of_isRedOrdered (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    topMap k Q Λ ν (KLRAlgebra.e s) = StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) s hs :=
  Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- The idempotent of `s` placed above the maximum fixes the diagram of a generator of top `s`. -/
theorem midIdem_mul_midGenKLR (g : MidGen j hj ν ν₀) :
    midIdem j hj Q Λ Λc ν ν₀ g.s * midGenKLR Q Λ Λc ρ₃ g = midGenKLR Q Λ Λc ρ₃ g := by
  simp only [midGenKLR, ← mul_assoc]
  rw [midIdem, midSeq, eSum_mul_e_insertSeq]

theorem midGenCorner_eq_midGen (g : MidGen j hj ν ν₀) :
    midGenCorner Q Λ Λc ρ₃ g = midGen j hj Q Λ Λc ν ν₀ (midGenElt Q Λ Λc ρ₃ g) :=
  Subtype.ext (by
    change op _ = op (midStendhal j hj Q Λ Λc ν ν₀ 1 * _)
    rw [midStendhal_one_mul_midGenElt])

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **`e(s)` fixes `v γ_g`** for a generator `g` of top `s`. -/
theorem midLeftAlg_e_tmul_midGenCorner (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (g : MidGen j hj ν ν₀) (v : L) :
    midLeftAlg L hL hR (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.s g.hs)
        (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) v) =
      Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) v := by
  rw [← topMap_e_of_isRedOrdered, midLeftAlg_topMap, midKLRAct_e, midGenCorner_eq_midGen,
    midEnd_tmul_midGen L hL, midGenElt, ← map_mul, midIdem_mul_midGenKLR]

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Step 1: `Θ (e(s_g) ⊗ v) = v γ_g`**, the element of the basis of the model of index
`(g, v)`. -/
theorem midTheta_e_tmul [DecidableEq (MidShuffle j hj ν ν₀)]
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidShuffle j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g.1)) :
    midTheta L hL ρ₃ hR (DirectSum.lof (StendhalAlgebra k Q Λ ν) _ (MidLeftSummand Q Λ Λc L) g
        (⟨_, Submodule.subset_span rfl⟩ ⊗ₜ v)) = midLeftGen L hL ρ₃ hR g v := by
  rw [midTheta_of_tmul]
  exact midLeftAlg_e_tmul_midGenCorner hR g.1 (v : L)

end Categorification.Stendhal.CupCap
