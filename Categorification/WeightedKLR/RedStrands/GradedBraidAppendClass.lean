/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidAppend
import Categorification.WeightedKLR.RedStrands.BraidedAppendGrading

/-!
# `Fᵢ ∘ 𝔅_σ` and `𝔅_σ ∘ Fᵢ` on right sequence projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7, for `Fᵢ`, graded. The composite bimodule `B ⊗_{T^{λ ∘ σ}_ν} e' T^{λ ∘ σ}_{ν+i}`
of `Fᵢ ∘ 𝔅_σ` is identified, with its grading, with the corner `φ(e_λ) V_{ν+i} e_{σλ}`
(`braidAppendEquiv`), where `φ` appends a black strand. Cutting this corner by `φ(e(t))` on the
left is cutting the braiding bimodule `B_{ν+i}` by `e(t i)`, so `Fᵢ ∘ 𝔅_σ` and `𝔅_σ ∘ Fᵢ` have
the same Hom polynomials against right sequence projectives, on right sequence projectives
(`projectiveHomPolynomial_rightBlackInd_braidFunctor`).

## Main definitions and results

* `braidAppendBimod` : the corner `φ(e_λ) V_{ν+i} e_{σλ}` as a graded bimodule.
* `braidAppendEquiv` : `B ⊗_{T^{λ ∘ σ}_ν} e' T^{λ ∘ σ}_{ν+i} ≅ φ(e_λ) V_{ν+i} e_{σλ}`.
* `projectiveHomPolynomial_rightBlackInd_braidFunctor` :
  `gdim HOM(P_s, Fᵢ 𝔅_σ P_t) = gdim HOM(P_s, 𝔅_σ Fᵢ P_t)`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite InductionAlong DirectSum

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {i : I} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ({i} + ν)))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hρ' : IsReducedChoice ρ') (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))
  {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option quotPrecheck false in
local notation "κ" => (List.finRange ℓ).map σ
local notation "ord" => List.finRange ℓ
set_option quotPrecheck false in
local notation "Mc" => Corner (appendBlackOp Q (Λ ∘ σ) i ν)
set_option quotPrecheck false in
local notation "Tσ" => TensorProductAlgebra k Q (Λ ∘ σ) ν
set_option quotPrecheck false in
local notation "Tσ'" => TensorProductAlgebra k Q (Λ ∘ σ) νᵢ
set_option quotPrecheck false in
local notation "𝒜σ" => oppositeGrade (tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) ν)
set_option quotPrecheck false in
local notation "𝒜σ'" => oppositeGrade (tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) νᵢ)
set_option quotPrecheck false in
local notation "𝒜" => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Λ) ν)
set_option quotPrecheck false in
local notation "𝒜'" => oppositeGrade (tensorProductGrade (rouquierGrading Q hR Λ) νᵢ)
set_option quotPrecheck false in
local notation "cornerGr" => Graded.submodule (𝒜σ')
  (lIdeal (appendBlackOp Q (Λ ∘ σ) i ν 1))

/-! ### The corner of `Fᵢ` as a graded bimodule -/

section CornerInstances

variable (Ω : Fin ℓ → I →₀ ℕ) (i ν)

instance : IsScalarTower k (TensorProductAlgebra k Q Ω νᵢ)ᵐᵒᵖ (Corner (appendBlackOp Q Ω i ν)) where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

instance : IsScalarTower k (TensorProductAlgebra k Q Ω ν)ᵐᵒᵖᵐᵒᵖ (Corner (appendBlackOp Q Ω i ν)) where
  smul_assoc c r z := Subtype.ext (by
    change z.val * appendBlackOp Q Ω i ν (c • r.unop) = c • (z.val * appendBlackOp Q Ω i ν r.unop)
    rw [appendBlackOp_smul, mul_smul_comm])

theorem finite_appendBlackCorner [Module.Finite k (TensorProductAlgebra k Q Ω νᵢ)] :
    Module.Finite k (Corner (appendBlackOp Q Ω i ν)) :=
  Module.Finite.of_injective ((lIdeal (appendBlackOp Q Ω i ν 1)).subtype.restrictScalars k)
    Subtype.val_injective

end CornerInstances

/-- The corner `e' T^{λ ∘ σ}_{ν+i}`, read in the opposite algebra, as a graded projective. -/
def appendCornerProj : GProj (𝒜σ') :=
  GProj.ofIdempotent (appendBlackOp Q (Λ ∘ σ) i ν 1) (unit_mul_unit _)
    (appendBlackOp_mem_grade (rouquierGrading Q hR (Λ ∘ σ)) i ν SetLike.GradedOne.one_mem)

instance appendCornerDecomposition : Decomposition (cornerGr) :=
  (appendCornerProj (i := i) (ν := ν) σ hR).decomposition

instance appendCorner_gradedSMul_right : SetLike.GradedSMul (oppositeGrade (𝒜σ)) (cornerGr) where
  smul_mem {l d} r z hr hz := by
    change z.val * appendBlackOp Q (Λ ∘ σ) i ν r.unop ∈ (𝒜σ') (l + d)
    rw [show l + d = d + l from add_comm l d]
    exact SetLike.GradedMul.mul_mem (A := 𝒜σ') hz
      (appendBlackOp_mem_grade (rouquierGrading Q hR (Λ ∘ σ)) i ν hr)

instance appendCorner_gradedSMul_left : SetLike.GradedSMul (𝒜σ') (cornerGr) :=
  (appendCornerProj (i := i) (ν := ν) σ hR).gradedSMul

/-- `Fᵢ` on graded right `T^{λ ∘ σ}`-modules is tensoring with the graded bimodule
`e' T^{λ ∘ σ}_{ν+i}`. -/
def rightBlackIndIsoInduce [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)]
    (N : GFin (𝒜σ)) :
    letI := finite_appendBlackCorner (Q := Q) (Ω := Λ ∘ σ) (i := i) (ν := ν)
    (rightBlackInd (rouquierGrading Q hR (Λ ∘ σ)) i ν N).Iso (GFin.induce (𝒜σ) (𝒜σ') (cornerGr) N) :=
  letI := finite_appendBlackCorner (Q := Q) (Ω := Λ ∘ σ) (i := i) (ν := ν)
  GradedEquiv.ofPreserves (LinearEquiv.refl _ _) fun _ _ h => h

/-! ### The composite bimodule as a corner -/

set_option quotPrecheck false in
local notation "F̃" => (appendViol Q Λ i ν).comp (identityCornerMap Q Λ ν hρ hQ)

variable (Q Λ i ν) in
/-- The corner `φ(e_λ) V_{ν+i} e_{σλ}`, a bimodule over `T^λ_ν` (through `φ`) and
`T^{λ ∘ σ}_{ν+i}`. -/
abbrev braidAppendBimod : Type :=
  RectBimod ((appendViol Q Λ i ν).comp (identityCornerMap Q Λ ν hρ hQ))
    (permCornerMap Q Λ νᵢ hρ' hQ σ)

variable (Q Λ i ν) in
/-- The auxiliary grading of `φ(e_λ) V_{ν+i} e_{σλ}`. -/
abbrev braidAppendGrading : ℤ → Submodule k (braidAppendBimod Q Λ i ν hρ hρ' hQ σ) :=
  RectBimod.grading (violAuxiliaryGrade (ν := νᵢ) (rouquierGrading Q hR Λ)) (F̃)
    (permCornerMap Q Λ νᵢ hρ' hQ σ)

theorem appendIdentityCorner_one_mem :
    (F̃) 1 ∈ violAuxiliaryGrade (ν := νᵢ) (rouquierGrading Q hR Λ) 0 :=
  appendViol_mem_violAuxiliaryGrade i _
    ((identityCornerMap_one hρ hQ).symm ▸ redProj_mem_violAuxiliaryGrade _ ord)

/-- The auxiliary grading of `φ(e_λ) V_{ν+i} e_{σλ}` is a decomposition. -/
@[instance_reducible] def braidAppendDecomposition :
    Decomposition (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR) :=
  RectBimod.decomposition _ (appendIdentityCorner_one_mem hρ hQ hR)
    ((permCornerMap_one hρ' hQ σ).symm ▸ redProj_mem_violAuxiliaryGrade _ κ)

theorem braidAppend_gradedSMul_left :
    SetLike.GradedSMul (oppositeGrade (𝒜)) (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR) :=
  RectBimod.gradedSMul_left _ fun _ _ ht =>
    appendViol_mem_violAuxiliaryGrade i _ (identityCornerMap_mem_grade hρ hQ _ ht)

theorem braidAppend_gradedSMul_right :
    SetLike.GradedSMul (𝒜σ') (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR) :=
  RectBimod.gradedSMul_right _ fun _ _ hu => permCornerMap_mem_grade hρ' hQ σ hR hu

/-! ### The graded equivalence -/

local notation "myT" => BalancedTensor k (Tσ')ᵐᵒᵖ (Tσ)ᵐᵒᵖ Mc (braidBimod Q Λ ν hρ hQ σ)

theorem braidAppendMult_tmul (m : Mc) (b : braidBimod Q Λ ν hρ hQ σ) :
    braidAppendMult i hρ hρ' hQ σ (BalancedTensor.tmul m b) =
      appendViol Q Λ i ν (RectBimod.val _ _ b) * permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop :=
  rfl

theorem braidAppendMult_mem_left (y : myT) :
    (F̃) 1 * braidAppendMult i hρ hρ' hQ σ y = braidAppendMult i hρ hρ' hQ σ y := by
  have e1 : (F̃) 1 = appendViol Q Λ i ν (violMk k Q Λ ν (redProj k Q Λ ν ord)) := by
    rw [NonUnitalAlgHom.comp_apply, identityCornerMap_one]
  rw [e1]
  exact (braidAppendMult_mem hρ hρ' hQ σ y).1

theorem braidAppendMult_mem_right (y : myT) :
    braidAppendMult i hρ hρ' hQ σ y * permCornerMap Q Λ νᵢ hρ' hQ σ 1 =
      braidAppendMult i hρ hρ' hQ σ y := by
  rw [permCornerMap_one hρ' hQ σ]
  exact (braidAppendMult_mem hρ hρ' hQ σ y).2

/-- The multiplication `m ⊗ b ↦ φ(b) m` into the corner. -/
def braidAppendBimodBil : Mc →ₗ[k] braidBimod Q Λ ν hρ hQ σ →ₗ[k]
    braidAppendBimod Q Λ i ν hρ hρ' hQ σ :=
  LinearMap.mk₂ k
    (fun m b => RectBimod.mk (braidAppendBil i hρ hρ' hQ σ m b)
      ⟨braidAppendMult_mem_left hρ hρ' hQ σ (BalancedTensor.tmul m b),
        braidAppendMult_mem_right hρ hρ' hQ σ (BalancedTensor.tmul m b)⟩)
    (fun m m' b => RectBimod.ext ((braidAppendBil i hρ hρ' hQ σ).map_add₂ m m' b))
    (fun c m b => RectBimod.ext ((braidAppendBil i hρ hρ' hQ σ).map_smul₂ c m b))
    (fun m b b' => RectBimod.ext (map_add (braidAppendBil i hρ hρ' hQ σ m) b b'))
    (fun c m b => RectBimod.ext (map_smul (braidAppendBil i hρ hρ' hQ σ m) c b))

theorem val_braidAppendBimodBil (m : Mc) (b : braidBimod Q Λ ν hρ hQ σ) :
    RectBimod.val _ _ (braidAppendBimodBil (Λ := Λ) (i := i) hρ hρ' hQ σ m b) =
      braidAppendBil i hρ hρ' hQ σ m b := rfl

/-- The multiplication map into `φ(e_λ) V_{ν+i} e_{σλ}`, as a map of left
`(T^{λ ∘ σ}_{ν+i})ᵐᵒᵖ`-modules. -/
def braidAppendLinear : myT →ₗ[(Tσ')ᵐᵒᵖ] braidAppendBimod Q Λ i ν hρ hρ' hQ σ :=
  BalancedTensor.liftB (braidAppendBimodBil (Λ := Λ) (i := i) hρ hρ' hQ σ)
    (fun m a b => RectBimod.ext (braidAppendBil_balanced hρ hρ' hQ σ m a b))
    (fun c m b => RectBimod.ext (by
      change appendViol Q Λ i ν (RectBimod.val _ _ b) *
          permCornerMap Q Λ νᵢ hρ' hQ σ (m.1.unop * c.unop) =
        appendViol Q Λ i ν (RectBimod.val _ _ b) * permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop *
          permCornerMap Q Λ νᵢ hρ' hQ σ c.unop
      rw [map_mul, mul_assoc]))

theorem val_braidAppendLinear (y : myT) :
    RectBimod.val _ _ (braidAppendLinear (Λ := Λ) (i := i) hρ hρ' hQ σ y) =
      braidAppendMult i hρ hρ' hQ σ y := by
  have h : (RectBimod.val _ _).comp
      ((braidAppendLinear (Λ := Λ) (i := i) hρ hρ' hQ σ).restrictScalars k) =
        braidAppendMult i hρ hρ' hQ σ :=
    BalancedTensor.ext fun _ _ => rfl
  exact LinearMap.congr_fun h y

end Categorification.Stendhal.BraidedStendhalAlgebra
