/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutKappa

/-!
# The exchange map of Lemma 7.19 (T) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19, trace half, at the cut at the `j`-th red strand. The
mate (`TensorMate.mate`) of the isomorphism `κ : K^σ ⊗_T S ≅ S₊ ⊗_E K_b` of (K) at the cut
(`kappaCut`) is the exchange map `Φ : S₊^∨ ⊗_{T⁺} K^σ → K_b ⊗_D S^∨` (`exchangeCut`), a map of
`E`–`T` bimodules. Defining `Φ` as this mate is the natural reading of Webster's "a variation"
of the argument for (K).

## Main definitions

* `Stendhal.CupCap.exchangeCut`, with `Stendhal.CupCap.exchangeCut_op_smul`.

## Route hypotheses

Those of `kCutPhiEquiv`: `hL`, `hR`, `hP`, `hPL`, `hκ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite TensorRepresented
open scoped TensorProduct DG.TensorProductOver.RightAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I) (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Dc" => cutFactorAlgebra Q (cutLabels j hj Λ) θ γ
set_option hygiene false in
local notation "Tc" => TensorProductAlgebra k Q Λ (θ + γ)
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "PF" => PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ
set_option hygiene false in
local notation "Kb" => KappaKb j hj Q Λ Λc θ γ ν₀ L'

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure. -/
private abbrev pfNonAssocSemiringM : NonAssocSemiring PF := Semiring.toNonAssocSemiring

attribute [local instance high] pfNonAssocSemiringM

set_option hygiene false in
local notation "Kσ" => ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L')
set_option hygiene false in
local notation "Sb" => KappaS j hj Q Λ θ γ hQ
set_option hygiene false in
local notation "Spb" => KappaSp j hj Q Λ Λc θ γ ν₀ hQ

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : CapCoef Q Λc ν₀ L'), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L') hL)
  (hP : PullOff k Q Λc ν₀ (CapCoef Q Λc ν₀ L')) (hPL : PullOffLeft k Q Λc ν₀ (CapCoef Q Λc ν₀ L'))
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

instance : Module.Projective Dcᵐᵒᵖ Sb := (isFinProj_kappaSFunctor j hj Q Λ θ γ hQ).projective
instance : Module.Finite Dcᵐᵒᵖ Sb := (isFinProj_kappaSFunctor j hj Q Λ θ γ hQ).finite
instance : Module.Projective PFᵐᵒᵖ Spb :=
  (isFinProj_kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).projective
instance : Module.Finite PFᵐᵒᵖ Spb := (isFinProj_kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).finite

/-- The left `E`-module `S₊^∨ ⊗_{T⁺} K^σ`, through `S₊^∨` (stated with the ring structure of `E`,
which instance search does not unify with its semiring structure). -/
instance moduleDualTensorCap : Module PF (DG.TensorProductOver Tp (RightDualModule PF Spb) Kσ) :=
  @DG.TensorProductOver.instModule Tp (RightDualModule PF Spb) Kσ _ _ _ _ _ PF _ _ _

/-- The left `E`-module `K_b ⊗_D S^∨`, through `K_b`. -/
instance moduleKbTensorDual : Module PF (DG.TensorProductOver Dc Kb (RightDualModule Dc Sb)) :=
  @DG.TensorProductOver.instModule Dc Kb (RightDualModule Dc Sb) _ _ _ _ _ PF _ _ _

/-- **The exchange map at the cut** `Φ : S₊^∨ ⊗_{T⁺} K^σ → K_b ⊗_D S^∨`, the mate of the
isomorphism `κ` of Lemma 7.19 (K) at the cut (`TensorMate.mate`). This is the natural reading of
Webster's "a variation" of the argument for (K), in the proof of the trace half of Lemma 7.19. -/
def exchangeCut : DG.TensorProductOver Tp (RightDualModule PF Spb) Kσ →ₗ[PF]
    DG.TensorProductOver Dc Kb (RightDualModule Dc Sb) :=
  TensorMate.mateLinear Dc (kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ).toAddMonoidHom
    (kappaCut_smul j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ)

/-- **`Φ` is right `T`-linear.** -/
theorem exchangeCut_op_smul (b : Tc)
    (y : DG.TensorProductOver Tp (RightDualModule PF Spb) Kσ) :
    exchangeCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ (op b • y) =
      op b • exchangeCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ y :=
  TensorMate.mate_op_smul Dc (kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ).toAddMonoidHom
    (kappaCut_smul j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ)
    (kappaCut_op_smul j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ) b y

end Categorification.Stendhal.CupCap
