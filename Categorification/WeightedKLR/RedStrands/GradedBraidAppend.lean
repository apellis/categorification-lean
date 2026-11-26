/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidFunctor
import Categorification.WeightedKLR.RedStrands.BraidedAppendDerivedOp
import Categorification.WeightedKLR.RedStrands.BraidedAppendIdentity
import Categorification.WeightedKLR.RedStrands.RightBlackInduction

/-!
# The braiding bimodule followed by `Fᵢ`, as a corner

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7, for `Fᵢ`. In the composite `Fᵢ ∘ 𝔅_σ` on right modules, the bimodule is
`B ⊗_{T^{λ ∘ σ}_ν} e' T^{λ ∘ σ}_{ν+i}`, and multiplication `b ⊗ x ↦ φ(b) x` identifies it with
the corner `φ(e_λ) V_{ν+i} e_{σλ}`, where `φ` appends a black strand (`braidAppendMult`). This is
the bijection `firstEquivF`, which is stated for the corners of `V` at red orders, read for the
tensor product algebras `T^λ` and `T^{λ ∘ σ}` through `violCornerEquiv` and the relabelling of
the red strands.

## Main definitions and results

* `permCornerEquiv σ` : `T^{λ ∘ σ}_ν ≅ e_{σλ} V_ν e_{σλ}`.
* `braidAppendMult` : the multiplication `B ⊗ e' T^{λ ∘ σ}_{ν+i} → V_{ν+i}`.
* `braidAppendMult_injective`, `braidAppendMult_surjective` : it is a bijection onto
  `φ(e_λ) V_{ν+i} e_{σλ}`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {i : I} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ({i} + ν)))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hρ' : IsReducedChoice ρ') (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option quotPrecheck false in
local notation "κ" => (List.finRange ℓ).map σ

/-! ### Appending a black strand on the corner maps -/

include hρ hρ' in
theorem identityCornerMap_appendBlack (t : TensorProductAlgebra k Q Λ ν) :
    identityCornerMap Q Λ νᵢ hρ' hQ (Stendhal.appendBlack Q Λ i ν t) =
      appendViol Q Λ i ν (identityCornerMap Q Λ ν hρ hQ t) := by
  have h := violCornerEquiv_appendViol (i := i) hρ hρ' hQ ((violCornerEquiv hρ hQ).symm t)
  rw [RingEquiv.apply_symm_apply] at h
  rw [identityCornerMap_apply, identityCornerMap_apply, ← h]
  exact congrArg Subtype.val ((violCornerEquiv hρ' hQ).symm_apply_apply _)

include hρ hρ' in
theorem permCornerMap_appendBlack (u : TensorProductAlgebra k Q (Λ ∘ σ) ν) :
    permCornerMap Q Λ νᵢ hρ' hQ σ (Stendhal.appendBlack Q (Λ ∘ σ) i ν u) =
      appendViol Q Λ i ν (permCornerMap Q Λ ν hρ hQ σ u) := by
  rw [permCornerMap_apply, permCornerMap_apply,
    identityCornerMap_appendBlack (Λ := Λ ∘ σ) hρ hρ' hQ, violRedPermEquiv_appendViol]

/-! ### The tensor product algebra `T^{λ ∘ σ}` as the corner at `σλ` -/

variable (ν) in
/-- `T^{λ ∘ σ}_ν ≅ e_{σλ} V_ν e_{σλ}`: `violCornerEquiv` for `λ ∘ σ`, then the relabelling of the
red strands. -/
def permCornerEquiv :
    TensorProductAlgebra k Q (Λ ∘ σ) ν ≃+* (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner :=
  (violCornerEquiv (Λ := Λ ∘ σ) hρ hQ).symm.trans
    (violCornerRedPermEquiv (Λ' := Λ ∘ σ) σ (fun _ => rfl) (List.finRange ℓ))

theorem permCornerEquiv_val (u : TensorProductAlgebra k Q (Λ ∘ σ) ν) :
    (permCornerEquiv ν hρ hQ σ u).1 = permCornerMap Q Λ ν hρ hQ σ u := rfl

include hρ' in
theorem permCornerEquiv_appendBlack (u : TensorProductAlgebra k Q (Λ ∘ σ) ν) :
    permCornerEquiv νᵢ hρ' hQ σ (Stendhal.appendBlack Q (Λ ∘ σ) i ν u) =
      appendCornerHom Q Λ i ν κ (permCornerEquiv ν hρ hQ σ u) :=
  Subtype.ext (by
    rw [permCornerEquiv_val, appendCornerHom_val, permCornerEquiv_val,
      permCornerMap_appendBlack hρ hρ' hQ σ])

include hρ' in
theorem permCornerEquiv_symm_appendCornerHom
    (x : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Corner) :
    (permCornerEquiv νᵢ hρ' hQ σ).symm (appendCornerHom Q Λ i ν κ x) =
      Stendhal.appendBlack Q (Λ ∘ σ) i ν ((permCornerEquiv ν hρ hQ σ).symm x) := by
  rw [RingEquiv.symm_apply_eq, permCornerEquiv_appendBlack hρ hρ' hQ σ,
    RingEquiv.apply_symm_apply]

/-! ### Comparing the two tensor products -/

set_option quotPrecheck false in
local notation "Fc" => InductionAlong.Corner (appendCornerOpHom Q Λ i ν κ)
set_option quotPrecheck false in
local notation "BS" => ↥(braidingBimodule k Q Λ ν (List.finRange ℓ) κ)
set_option quotPrecheck false in
local notation "Mc" => InductionAlong.Corner (appendBlackOp Q (Λ ∘ σ) i ν)
set_option quotPrecheck false in
local notation "ψ" => permCornerEquiv ν hρ hQ σ
set_option quotPrecheck false in
local notation "ψ'" => permCornerEquiv νᵢ hρ' hQ σ

include hρ in
theorem permCornerEquiv_symm_mem_corner (f : Fc) :
    op ((ψ').symm f.1.unop) ∈ lIdeal (appendBlackOp Q (Λ ∘ σ) i ν 1) := by
  change op _ * appendBlackOp Q (Λ ∘ σ) i ν (op 1) = op _
  rw [appendBlackOp_op, ← op_mul]
  congr 1
  apply (ψ').injective
  rw [map_mul, RingEquiv.apply_symm_apply, permCornerEquiv_appendBlack hρ hρ' hQ σ, map_one]
  exact Subtype.ext (phi_mul_fval f)

variable (i) in
include hρ hρ' in
/-- `F_{σλ} → e' T^{λ ∘ σ}_{ν+i}`, through `permCornerEquiv`. -/
def cornerOfF (f : Fc) : Mc :=
  ⟨op ((ψ').symm f.1.unop), permCornerEquiv_symm_mem_corner hρ hρ' hQ σ f⟩

include hρ in
theorem permCornerEquiv_mem_cornerOp (m : Mc) :
    op (ψ' m.1.unop) ∈ lIdeal (appendCornerOpHom Q Λ i ν κ 1) := by
  change op _ * op (appendCornerHom Q Λ i ν κ 1) = op _
  rw [← op_mul]
  congr 1
  have hm : Stendhal.appendBlack Q (Λ ∘ σ) i ν 1 * m.1.unop = m.1.unop :=
    congrArg unop m.2
  have h1 : appendCornerHom Q Λ i ν κ 1 = ψ' (Stendhal.appendBlack Q (Λ ∘ σ) i ν 1) := by
    rw [permCornerEquiv_appendBlack hρ hρ' hQ σ, (permCornerEquiv ν hρ hQ σ).map_one]
  rw [h1, ← map_mul, hm]

variable (i) in
include hρ hρ' in
/-- `e' T^{λ ∘ σ}_{ν+i} → F_{σλ}`, the inverse of `cornerOfF`. -/
def fOfCorner (m : Mc) : Fc :=
  ⟨op (ψ' m.1.unop), permCornerEquiv_mem_cornerOp hρ hρ' hQ σ m⟩

theorem cornerOfF_fOfCorner (m : Mc) :
    cornerOfF i hρ hρ' hQ σ (fOfCorner i hρ hρ' hQ σ m) = m :=
  Subtype.ext (congrArg op ((ψ').symm_apply_apply m.1.unop))

theorem cornerOfF_add (f f' : Fc) :
    cornerOfF i hρ hρ' hQ σ (f + f') = cornerOfF i hρ hρ' hQ σ f + cornerOfF i hρ hρ' hQ σ f' :=
  Subtype.ext (congrArg op (map_add (ψ').symm f.1.unop f'.1.unop))

theorem cornerOfF_op_smul (a : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ) (f : Fc) :
    cornerOfF i hρ hρ' hQ σ (op a • f) =
      op (op ((ψ).symm a.unop)) • cornerOfF i hρ hρ' hQ σ f := by
  apply Subtype.ext
  change op ((ψ').symm (appendCornerHom Q Λ i ν κ a.unop * f.1.unop)) =
    op ((ψ').symm f.1.unop) * appendBlackOp Q (Λ ∘ σ) i ν (op ((ψ).symm a.unop))
  rw [map_mul, permCornerEquiv_symm_appendCornerHom hρ hρ' hQ σ, appendBlackOp_op, ← op_mul]

variable (Q Λ ν) in
include hρ hQ in
/-- `B(λ, σλ) → B`, the identity on underlying elements. -/
def braidBimodOfBS (b : BS) : braidBimod Q Λ ν hρ hQ σ :=
  RectBimod.mk b.1 ⟨by rw [identityCornerMap_one]; exact b.2.1,
    by rw [permCornerMap_one]; exact b.2.2⟩

theorem braidBimodOfBS_add (b b' : BS) :
    braidBimodOfBS Q Λ ν hρ hQ σ (b + b') =
      braidBimodOfBS Q Λ ν hρ hQ σ b + braidBimodOfBS Q Λ ν hρ hQ σ b' :=
  RectBimod.ext rfl

theorem braidBimodOfBS_smul (a : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ) (b : BS) :
    braidBimodOfBS Q Λ ν hρ hQ σ (a • b) = op ((ψ).symm a.unop) • braidBimodOfBS Q Λ ν hρ hQ σ b :=
  RectBimod.ext (by
    rw [RectBimod.val_smul_right, unop_op, ← permCornerEquiv_val, RingEquiv.apply_symm_apply]
    rfl)

theorem exists_braidBimodOfBS (x : braidBimod Q Λ ν hρ hQ σ) :
    ∃ b : BS, braidBimodOfBS Q Λ ν hρ hQ σ b = x := by
  have hx := RectBimod.mem x
  rw [identityCornerMap_one, permCornerMap_one] at hx
  exact ⟨⟨_, hx⟩, RectBimod.ext rfl⟩

/-! ### The multiplication map -/

variable (i) in
/-- The multiplication `b ⊗ x ↦ φ(b) x` on the composite bimodule
`B ⊗_{T^{λ ∘ σ}_ν} e' T^{λ ∘ σ}_{ν+i}`. -/
def braidAppendBil :
    Mc →ₗ[k] braidBimod Q Λ ν hρ hQ σ →ₗ[k] ViolQuotient k Q Λ νᵢ :=
  LinearMap.mk₂ k
    (fun m b => appendViol Q Λ i ν (RectBimod.val _ _ b) * permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop)
    (fun m m' b => by
      change _ * permCornerMap Q Λ νᵢ hρ' hQ σ (m.1.unop + m'.1.unop) = _
      rw [map_add, mul_add])
    (fun c m b => by
      change _ * permCornerMap Q Λ νᵢ hρ' hQ σ (c • m.1.unop) = _
      rw [map_smul, mul_smul_comm])
    (fun m b b' => by rw [map_add, map_add, add_mul])
    (fun c m b => by rw [map_smul, map_smul, smul_mul_assoc])

theorem braidAppendBil_balanced (m : Mc) (a : (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ)
    (b : braidBimod Q Λ ν hρ hQ σ) :
    braidAppendBil i hρ hρ' hQ σ (op a • m) b = braidAppendBil i hρ hρ' hQ σ m (a • b) := by
  change appendViol Q Λ i ν (RectBimod.val _ _ b) *
      permCornerMap Q Λ νᵢ hρ' hQ σ (Stendhal.appendBlack Q (Λ ∘ σ) i ν a.unop * m.1.unop) =
    appendViol Q Λ i ν (RectBimod.val _ _ b * permCornerMap Q Λ ν hρ hQ σ a.unop) *
      permCornerMap Q Λ νᵢ hρ' hQ σ m.1.unop
  rw [map_mul, permCornerMap_appendBlack hρ hρ' hQ σ, map_mul, mul_assoc]

variable (i) in
/-- **The multiplication map** `B ⊗_{T^{λ ∘ σ}_ν} e' T^{λ ∘ σ}_{ν+i} → V_{ν+i}`,
`b ⊗ x ↦ φ(b) x`, for the composite `Fᵢ ∘ 𝔅_σ` on right modules. -/
def braidAppendMult :
    BalancedTensor k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)ᵐᵒᵖ
        (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ Mc (braidBimod Q Λ ν hρ hQ σ) →ₗ[k]
      ViolQuotient k Q Λ νᵢ :=
  BalancedTensor.lift (braidAppendBil i hρ hρ' hQ σ) (braidAppendBil_balanced hρ hρ' hQ σ)

local notation "myT" => BalancedTensor k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)ᵐᵒᵖ
  (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ Mc (braidBimod Q Λ ν hρ hQ σ)

/-- The pure tensors of the comparison map, for a fixed first factor. -/
def firstTensorFCompareRight (f : Fc) : BS →+ myT :=
  AddMonoidHom.mk' (fun b => BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ f)
      (braidBimodOfBS Q Λ ν hρ hQ σ b))
    (fun b b' => by rw [braidBimodOfBS_add, BalancedTensor.tmul_add])

/-- The pure tensors of the comparison map. -/
def firstTensorFCompareBil : Fc →+ BS →+ myT :=
  AddMonoidHom.mk' (firstTensorFCompareRight (Λ := Λ) (i := i) hρ hρ' hQ σ) (fun f f' =>
    AddMonoidHom.ext fun b => by
      change BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ (f + f')) _ =
        BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ f) _ +
          BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ f') _
      rw [cornerOfF_add, BalancedTensor.add_tmul])

theorem firstTensorFCompareBil_apply (f : Fc) (b : BS) :
    firstTensorFCompareBil (Λ := Λ) (i := i) hρ hρ' hQ σ f b = BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ f)
      (braidBimodOfBS Q Λ ν hρ hQ σ b) := rfl

theorem firstTensorFCompareBil_balanced (a : (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ)
    (f : Fc) (b : BS) :
    firstTensorFCompareBil (Λ := Λ) (i := i) hρ hρ' hQ σ (op a • f) b = firstTensorFCompareBil (Λ := Λ) (i := i) hρ hρ' hQ σ f (a • b) := by
  rw [firstTensorFCompareBil_apply, firstTensorFCompareBil_apply, cornerOfF_op_smul,
    braidBimodOfBS_smul, BalancedTensor.op_smul_tmul]

/-- The comparison from the tensor product of `firstEquivF`. -/
def firstTensorFCompare : firstTensorF (k := k) Q Λ i ν (List.finRange ℓ) κ →+ myT :=
  DG.TensorProductOver.lift (firstTensorFCompareBil (Λ := Λ) (i := i) hρ hρ' hQ σ)
    (firstTensorFCompareBil_balanced hρ hρ' hQ σ)

theorem braidAppendMult_firstTensorFCompare (x : firstTensorF (k := k) Q Λ i ν (List.finRange ℓ) κ) :
    braidAppendMult i hρ hρ' hQ σ (firstTensorFCompare (Λ := Λ) (i := i) hρ hρ' hQ σ x) =
      firstMultF Q Λ i ν (List.finRange ℓ) κ x := by
  have h : (braidAppendMult i hρ hρ' hQ σ).toAddMonoidHom.comp
      (firstTensorFCompare (Λ := Λ) (i := i) hρ hρ' hQ σ) =
        firstMultF Q Λ i ν (List.finRange ℓ) κ := by
    refine DG.TensorProductOver.addHom_ext fun f b => ?_
    change appendViol Q Λ i ν (show BS from b).1 *
        permCornerMap Q Λ νᵢ hρ' hQ σ ((ψ').symm (show Fc from f).1.unop) =
      appendViol Q Λ i ν (show BS from b).1 * (show Fc from f).1.unop.1
    rw [← permCornerEquiv_val, RingEquiv.apply_symm_apply]
  exact DFunLike.congr_fun h x

theorem firstTensorFCompare_surjective :
    Function.Surjective (firstTensorFCompare (Λ := Λ) (i := i) hρ hρ' hQ σ) := by
  intro y
  induction y using BalancedTensor.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m b =>
    obtain ⟨b, rfl⟩ := exists_braidBimodOfBS hρ hQ σ b
    refine ⟨DG.TensorProductOver.tmul _ (show InDegreeZero Fc from fOfCorner i hρ hρ' hQ σ m)
      (show InDegreeZero (OpBimodule _ BS) from b), ?_⟩
    change BalancedTensor.tmul (cornerOfF i hρ hρ' hQ σ (fOfCorner i hρ hρ' hQ σ m)) _ = _
    rw [cornerOfF_fOfCorner]
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/-! ### Bijectivity -/

variable {hρ'} in
include hQ hρ in
theorem braidAppendMult_injective :
    Function.Injective (braidAppendMult (Λ := Λ) i hρ hρ' hQ σ) := by
  intro y y' h
  obtain ⟨x, rfl⟩ := firstTensorFCompare_surjective hρ hρ' hQ σ y
  obtain ⟨x', rfl⟩ := firstTensorFCompare_surjective hρ hρ' hQ σ y'
  rw [braidAppendMult_firstTensorFCompare, braidAppendMult_firstTensorFCompare] at h
  rw [firstMultF_injective (List.finRange ℓ) κ hQ hρ h]

theorem braidAppendMult_mem (y : BalancedTensor k (TensorProductAlgebra k Q (Λ ∘ σ) νᵢ)ᵐᵒᵖ
      (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ Mc (braidBimod Q Λ ν hρ hQ σ)) :
    braidAppendMult i hρ hρ' hQ σ y ∈ cornerBimodule
      (appendViol Q Λ i ν (violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ))))
      (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ)) := by
  obtain ⟨x, rfl⟩ := firstTensorFCompare_surjective hρ hρ' hQ σ y
  rw [braidAppendMult_firstTensorFCompare]
  exact firstMultF_mem x

include hQ hρ in
theorem braidAppendMult_surjective {z : ViolQuotient k Q Λ νᵢ}
    (hz : z ∈ cornerBimodule
      (appendViol Q Λ i ν (violMk k Q Λ ν (redProj k Q Λ ν (List.finRange ℓ))))
      (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ))) :
    ∃ y, braidAppendMult (Λ := Λ) i hρ hρ' hQ σ y = z := by
  obtain ⟨x, hx⟩ := firstMultF_surjective (List.finRange ℓ) κ hQ hρ hz
  exact ⟨firstTensorFCompare (Λ := Λ) (i := i) hρ hρ' hQ σ x, by rw [braidAppendMult_firstTensorFCompare, hx]⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
