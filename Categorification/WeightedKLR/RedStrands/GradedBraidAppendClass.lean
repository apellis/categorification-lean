/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidAppend
import Categorification.WeightedKLR.RedStrands.BraidedAppendGrading
import Categorification.KLR.Prop31G0

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

include hQ hρ in
theorem braidAppendLinear_bijective :
    Function.Bijective (braidAppendLinear (Λ := Λ) (i := i) hρ hρ' hQ σ) := by
  refine ⟨fun y y' h => braidAppendMult_injective (hρ' := hρ') hρ hQ σ ?_, fun z => ?_⟩
  · rw [← val_braidAppendLinear, ← val_braidAppendLinear, h]
  · have hz := RectBimod.mem z
    have e1 : (F̃) 1 = appendViol Q Λ i ν (violMk k Q Λ ν (redProj k Q Λ ν ord)) := by
      rw [NonUnitalAlgHom.comp_apply, identityCornerMap_one]
    rw [e1, permCornerMap_one hρ' hQ σ] at hz
    obtain ⟨y, hy⟩ := braidAppendMult_surjective (Λ := Λ) (i := i) hρ hρ' hQ σ hz
    exact ⟨y, RectBimod.ext (by rw [val_braidAppendLinear, hy])⟩

/-- **The composite bimodule of `Fᵢ ∘ 𝔅_σ` is the corner `φ(e_λ) V_{ν+i} e_{σλ}`**
(Webster, arXiv:1309.3796v2, §6.1, Proposition 6.7, for `Fᵢ`). -/
def braidAppendEquiv : myT ≃ₗ[(Tσ')ᵐᵒᵖ] braidAppendBimod Q Λ i ν hρ hρ' hQ σ :=
  LinearEquiv.ofBijective (braidAppendLinear (Λ := Λ) (i := i) hρ hρ' hQ σ)
    (braidAppendLinear_bijective hρ hρ' hQ σ)

theorem val_braidAppendEquiv (y : myT) :
    RectBimod.val _ _ (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ y) =
      braidAppendMult i hρ hρ' hQ σ y :=
  val_braidAppendLinear hρ hρ' hQ σ y

theorem braidAppendEquiv_isBimoduleHom :
    BalancedTensor.IsBimoduleHom (A := (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)
      (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ).toLinearMap := by
  intro a y
  apply RectBimod.ext
  change RectBimod.val _ _ (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ (op a • y)) =
    (F̃) a.unop * RectBimod.val _ _ (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ y)
  rw [val_braidAppendEquiv, val_braidAppendEquiv]
  have h : (braidAppendMult i hρ hρ' hQ σ).comp
      ((BalancedTensor.mapRight (BalancedTensor.rmul (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ
        (braidBimod Q Λ ν hρ hQ σ) (op a))).restrictScalars k) =
      (LinearMap.mulLeft k ((F̃) a.unop)).comp (braidAppendMult i hρ hρ' hQ σ) := by
    refine BalancedTensor.ext fun m b => ?_
    change appendViol Q Λ i ν (identityCornerMap Q Λ ν hρ hQ a.unop * RectBimod.val _ _ b) *
        permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop =
      appendViol Q Λ i ν (identityCornerMap Q Λ ν hρ hQ a.unop) *
        (appendViol Q Λ i ν (RectBimod.val _ _ b) * permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop)
    rw [map_mul, mul_assoc]
  exact LinearMap.congr_fun h y

theorem braidAppendEquiv_mem {d : ℤ} {y : myT}
    (hy : y ∈ balancedGrading (Tσ')ᵐᵒᵖ (Tσ)ᵐᵒᵖ (cornerGr)
      (braidBimodGrading Q Λ ν hρ hQ σ hR) d) :
    braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ y ∈
      braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR d := by
  refine balancedGrading_map_mem (fun d => braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR d)
    ((braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ).toLinearMap.restrictScalars k)
    (fun a b m x hm hx => ?_) hy
  change RectBimod.val _ _ (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ
    (BalancedTensor.tmul m x)) ∈ violAuxiliaryGrade (ν := νᵢ) (rouquierGrading Q hR Λ) (a + b)
  rw [val_braidAppendEquiv, braidAppendMult_tmul, add_comm a b]
  exact SetLike.GradedMul.mul_mem (A := violAuxiliaryGrade (ν := νᵢ) (rouquierGrading Q hR Λ))
    (appendViol_mem_violAuxiliaryGrade i _ hx) (permCornerMap_mem_grade hρ' hQ σ hR hm)

/-! ### Hom polynomials on right sequence projectives -/

section Projective

include hρ hQ in
theorem finite_braidAppendBimod [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) ν)]
    [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)] : Module.Finite k (braidAppendBimod Q Λ i ν hρ hρ' hQ σ) := by
  have := finite_appendBlackCorner (Q := Q) (Ω := Λ ∘ σ) (i := i) (ν := ν)
  have := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ σ
  have := finite_balancedTensor (k := k) (B := (Tσ')ᵐᵒᵖ) (A := (Tσ)ᵐᵒᵖ) (M := Mc)
    (braidBimod Q Λ ν hρ hQ σ)
  exact Module.Finite.equiv ((braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ).restrictScalars k)

/-- On right sequence projectives, `gdim HOM(e(s) T^{λ ∘ σ}_{ν+i}, Fᵢ 𝔅_σ (e(t) T^λ_ν))` is the
graded dimension of the cut `φ(e(t)) V_{ν+i} e(s)` of the composite corner. -/
theorem projectiveHomPolynomial_rightBlackInd_braidFunctor_eq_cut
    [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) ν)]
    [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)]
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t)
    (s : Seq (stendhalWeight ℓ νᵢ)) (hs : IsRedOrdered s) :
    projectiveHomPolynomial (𝒜σ')
        (rightBlackInd (rouquierGrading Q hR (Λ ∘ σ)) i ν
          (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR
            (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin))
        (K0.of (rightSequenceProj (rouquierGrading Q hR (Λ ∘ σ)) s hs)) =
      gdimPoly (idem (idem (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR)
          (op (TensorProductAlgebra.mk Q (Λ ∘ σ) νᵢ (StendhalAlgebra.e s hs))))
        (op (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))))) := by
  let := braidBimodDecomposition (Λ := Λ) (ν := ν) hρ hQ σ hR
  let := braidBimod_gradedSMul_left (Λ := Λ) (ν := ν) hρ hQ σ hR
  let := braidBimod_gradedSMul_right (Λ := Λ) (ν := ν) hρ hQ σ hR
  let := finite_braidBimod (Λ := Λ) (ν := ν) hρ hQ σ
  let := finite_appendBlackCorner (Q := Q) (Ω := Λ ∘ σ) (i := i) (ν := ν)
  let := braidAppendDecomposition (Λ := Λ) (i := i) (ν := ν) hρ hρ' hQ σ hR
  let := braidAppend_gradedSMul_left (Λ := Λ) (i := i) (ν := ν) hρ hρ' hQ σ hR
  let := braidAppend_gradedSMul_right (Λ := Λ) (i := i) (ν := ν) hρ hρ' hQ σ hR
  let := finite_braidAppendBimod (Λ := Λ) (i := i) (ν := ν) hρ hρ' hQ σ
  let := compDecomposition (C := (Tσ')ᵐᵒᵖ) (𝒜σ) (braidBimodGrading Q Λ ν hρ hQ σ hR) (cornerGr)
  let := compGradedSMul (B := (Tσ)ᵐᵒᵖ) (𝒜σ') (braidBimodGrading Q Λ ν hρ hQ σ hR) (cornerGr)
  let := compGradedSMulRight (B := (Tσ)ᵐᵒᵖ) (C := (Tσ')ᵐᵒᵖ) (𝒜)
    (braidBimodGrading Q Λ ν hρ hQ σ hR) (cornerGr)
  let := finite_balancedTensor (k := k) (B := (Tσ')ᵐᵒᵖ) (A := (Tσ)ᵐᵒᵖ) (M := Mc)
    (braidBimod Q Λ ν hρ hQ σ)
  have hes := congrArg op (isIdempotentElem_mk_e (Q := Q) (Λ := Λ ∘ σ) s hs)
  have hes0 : _ ∈ (𝒜σ') 0 :=
    mk_e_mem_tensorProductGrade (rouquierGrading Q hR (Λ ∘ σ)) νᵢ s hs
  let P := (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin
  let X := GFin.induce (𝒜) (𝒜σ') (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR) P
  have h1 : projectiveHomPolynomial (𝒜σ')
        (rightBlackInd (rouquierGrading Q hR (Λ ∘ σ)) i ν
          (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR P))
        (K0.of (rightSequenceProj (rouquierGrading Q hR (Λ ∘ σ)) s hs)) =
      projectiveHomPolynomial (𝒜σ') X
        (K0.of (rightSequenceProj (rouquierGrading Q hR (Λ ∘ σ)) s hs)) := by
    refine (projectiveHomPolynomial_ofIdempotent (𝒜σ') _ hes hes0).trans
      (Eq.trans ?_ (projectiveHomPolynomial_ofIdempotent (𝒜σ') X hes hes0).symm)
    refine (gdimPoly_idem_congr' (rightBlackIndIsoInduce σ hR _)).trans ?_
    refine (gdimPoly_idem_congr' (GFin.induceInduceIso (𝒜) (𝒜σ) (𝒜σ')
      (braidBimodGrading Q Λ ν hρ hQ σ hR) (cornerGr) P)).trans ?_
    exact gdimPoly_idem_congr' (GFin.induceCongrLeft
      (braidAppendEquiv (Λ := Λ) (i := i) hρ hρ' hQ σ)
      (braidAppendEquiv_isBimoduleHom hρ hρ' hQ σ)
      (fun _ _ hm => braidAppendEquiv_mem hρ hρ' hQ σ hR hm) P)
  rw [h1]
  exact projectiveHomPolynomial_induce_ofIdempotent (𝒜) (𝒜σ')
    (braidAppendGrading Q Λ i ν hρ hρ' hQ σ hR) (congrArg op (isIdempotentElem_mk_e t ht))
    (show _ ∈ (𝒜) 0 from mk_e_mem_tensorProductGrade (rouquierGrading Q hR Λ) ν t ht)
    hes hes0

end Projective

end Categorification.Stendhal.BraidedStendhalAlgebra
