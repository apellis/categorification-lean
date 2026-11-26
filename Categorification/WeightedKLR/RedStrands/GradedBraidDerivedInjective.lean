/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidingBimodule
import Categorification.Algebra.DerivedRightTensorInjective
import Categorification.Algebra.DerivedTensorFiltration

/-!
# The braid functor on modules and the derived braid functor in degree zero

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Definition 6.6. The braiding bimodule `B` read over the tensor product algebras
(`braidBimod`) and over the corners of the quotient by violated idempotents
(`braidingBimodule`) has the same underlying elements; the identification of `T^λ` with the
corner at the order `λ_1, …, λ_ℓ` (`violCornerEquiv`) turns a right `T^λ`-module `N` into a right
module over the corner (`CornerRes N`). Then `N ⊗_{T^λ} B` is the ordinary tensor of the derived
braid functor (`braidTensorCornerEquiv`), and a module map whose derived braid is injective in
degree zero has injective ordinary braid (`injective_mapRight_braidBimod_of_mono`). This is the
input for the exactness of the braid functor along resolutions in the proof of Corollary 6.10.

## Main definitions and results

* `CornerRes N` : a right `T^λ`-module as a right module over the corner of `V` at `λ`.
* `braidTensorCornerEquiv` : `N ⊗_{T^λ} B ≃ N ⊗_{e_λ V e_λ} e_λ V e_{σλ}`.
* `injective_mapRight_braidBimod_of_mono`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite CategoryTheory DG DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "ord" => List.finRange ℓ
local notation "hO" => isIdempotentElem_violMk_redProj k Q Λ ν (List.finRange ℓ)
local notation "hS" => isIdempotentElem_violMk_redProj k Q Λ ν (List.map σ (List.finRange ℓ))
local notation "𝒞" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
  (List.finRange ℓ))
local notation "𝒞'" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν
  (List.map σ (List.finRange ℓ)))
local notation "𝒳" => braidingBimodule k Q Λ ν (List.finRange ℓ) (List.map σ (List.finRange ℓ))
local notation "𝒯" => TensorProductAlgebra k Q Λ ν

/-! ### Scalars on the braiding bimodule -/

/-- `k` acts on `e_λ V e_{σλ}` through the corner. -/
instance braidingBimoduleModuleK : Module k 𝒳 := Module.compHom 𝒳 (algebraMap k 𝒞)

theorem braidingBimodule_val_smul_k (c : k) (x : 𝒳) : ((c • x : 𝒳) : ViolQuotient k Q Λ ν) =
    c • (x : ViolQuotient k Q Λ ν) := by
  change (c • violMk k Q Λ ν (redProj k Q Λ ν ord)) * x.1 = _
  rw [smul_mul_assoc, x.2.1]

instance braidingBimoduleTower : IsScalarTower k 𝒞 𝒳 where
  smul_assoc c r x := Subtype.ext (by
    rw [braidingBimodule_val_smul_k, cornerBimodule.coe_smul_left, cornerBimodule.coe_smul_left]
    change (c • r.1) * x.1 = _
    rw [smul_mul_assoc])

instance braidingBimoduleComm : SMulCommClass 𝒞 k 𝒳 where
  smul_comm r c x := Subtype.ext (by
    rw [cornerBimodule.coe_smul_left, braidingBimodule_val_smul_k, braidingBimodule_val_smul_k,
      cornerBimodule.coe_smul_left, mul_smul_comm])

/-! ### The corner restriction of a right `T^λ`-module -/

include hρ hQ in
/-- `T^λ` is the corner of `V` at `λ`, on opposite rings. -/
def cornerOpRingHom : 𝒞ᵐᵒᵖ →+* 𝒯ᵐᵒᵖ where
  toFun c := op (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ c.unop)
  map_one' := by rw [unop_one, map_one, op_one]
  map_mul' c d := by rw [unop_mul, map_mul, op_mul]
  map_zero' := by rw [unop_zero, map_zero, op_zero]
  map_add' c d := by rw [MulOpposite.unop_add, map_add, MulOpposite.op_add]

theorem cornerOpRingHom_op (c : 𝒞) :
    cornerOpRingHom hρ hQ (op c) = op (violCornerEquiv hρ hQ c) := rfl

theorem violCornerEquiv_algebraMap (c : k) :
    violCornerEquiv hρ hQ (algebraMap k 𝒞 c) = algebraMap k 𝒯 c := by
  rw [← RingEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [violCornerEquiv_symm_algebraMap_val hρ hQ]
  change c • violMk k Q Λ ν (redProj k Q Λ ν ord) = _
  rw [Algebra.smul_def]

variable {G : GradingDatum (stendhalQ Q Λ)}

variable (G) in
include hρ hQ in
/-- **A right `T^λ`-module as a right module over the corner of `V` at `λ`.** -/
@[nolint unusedArguments]
def CornerRes (_ : IsReducedChoice ρ) (_ : KLRSymm Q)
    (N : GFin (oppositeGrade (tensorProductGrade G ν))) : Type := N.carrier

namespace CornerRes

variable (N : GFin (oppositeGrade (tensorProductGrade G ν)))

instance : AddCommGroup (CornerRes G hρ hQ N) := inferInstanceAs (AddCommGroup N.carrier)

instance : Module k (CornerRes G hρ hQ N) := inferInstanceAs (Module k N.carrier)

instance : Module 𝒞ᵐᵒᵖ (CornerRes G hρ hQ N) :=
  Module.compHom N.carrier (cornerOpRingHom hρ hQ)

theorem smul_def (c : 𝒞ᵐᵒᵖ) (n : CornerRes G hρ hQ N) :
    c • n = (cornerOpRingHom hρ hQ c • (show N.carrier from n) : N.carrier) := rfl

instance : SMulCommClass k 𝒞ᵐᵒᵖ (CornerRes G hρ hQ N) where
  smul_comm c r n := by
    change c • (cornerOpRingHom hρ hQ r • (show N.carrier from n)) =
      cornerOpRingHom hρ hQ r • (c • (show N.carrier from n))
    rw [← algebraMap_smul 𝒯ᵐᵒᵖ c, ← mul_smul, ← algebraMap_smul 𝒯ᵐᵒᵖ c, ← mul_smul,
      Algebra.commutes]

theorem op_algebraMap_smul (c : k) (n : CornerRes G hρ hQ N) :
    op (algebraMap k 𝒞 c) • n = c • n := by
  change cornerOpRingHom hρ hQ (op (algebraMap k 𝒞 c)) • (show N.carrier from n) = c • (show N.carrier from n)
  rw [cornerOpRingHom_op, violCornerEquiv_algebraMap, ← MulOpposite.algebraMap_apply,
    algebraMap_smul]

/-- A map of right `T^λ`-modules as a map of right modules over the corner. -/
def map {N N' : GFin (oppositeGrade (tensorProductGrade G ν))} (f : N.carrier →ₗ[𝒯ᵐᵒᵖ] N'.carrier) :
    CornerRes G hρ hQ N →ₗ[𝒞ᵐᵒᵖ] CornerRes G hρ hQ N' where
  toFun := f
  map_add' := f.map_add
  map_smul' c n := f.map_smul (cornerOpRingHom hρ hQ c) n

end CornerRes

/-! ### The two readings of the braiding bimodule -/

include hρ hQ in
/-- `e_λ V e_{σλ}` and `braidBimod` have the same elements. -/
def braidingBimoduleEquiv : 𝒳 ≃ₗ[k] braidBimod Q Λ ν hρ hQ σ where
  toFun x := RectBimod.mk x.1 (by rw [identityCornerMap_one, permCornerMap_one]; exact x.2)
  invFun b := ⟨RectBimod.val _ _ b, by
    have := RectBimod.mem b
    rwa [identityCornerMap_one, permCornerMap_one] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := RectBimod.ext (by
    rw [RectBimod.val_mk, braidingBimodule_val_smul_k]
    rfl)

theorem val_braidingBimoduleEquiv (x : 𝒳) :
    RectBimod.val _ _ (braidingBimoduleEquiv hρ hQ σ x) = x.1 := rfl

theorem braidingBimoduleEquiv_smul (c : 𝒞) (x : 𝒳) :
    braidingBimoduleEquiv hρ hQ σ (c • x) =
      (op (op (violCornerEquiv hρ hQ c)) : (𝒯ᵐᵒᵖ)ᵐᵒᵖ) • braidingBimoduleEquiv hρ hQ σ x := by
  apply RectBimod.ext
  rw [RectBimod.val_smul_left, val_braidingBimoduleEquiv, val_braidingBimoduleEquiv,
    cornerBimodule.coe_smul_left]
  change c.1 * x.1 = identityCornerMap Q Λ ν hρ hQ (violCornerEquiv hρ hQ c) * x.1
  rw [identityCornerMap_apply, RingEquiv.symm_apply_apply]

theorem braidingBimoduleEquiv_symm_smul (c : 𝒞) (b : braidBimod Q Λ ν hρ hQ σ) :
    (braidingBimoduleEquiv hρ hQ σ).symm ((op (op (violCornerEquiv hρ hQ c)) : (𝒯ᵐᵒᵖ)ᵐᵒᵖ) • b) =
      c • (braidingBimoduleEquiv hρ hQ σ).symm b :=
  Subtype.ext (by
    change identityCornerMap Q Λ ν hρ hQ (violCornerEquiv hρ hQ c) * RectBimod.val _ _ b =
      c.1 * RectBimod.val _ _ b
    rw [identityCornerMap_apply, RingEquiv.symm_apply_apply])

/-! ### The ordinary braid as the degree-zero derived braid -/

local notation "𝒯σ" => TensorProductAlgebra k Q (Λ ∘ σ) ν

variable (N : GFin (oppositeGrade (tensorProductGrade G ν)))

/-- The forward map `n ⊗ x ↦ x ⊗ n`. -/
private def braidTensorTo :
    BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳 →ₗ[k]
      BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ (braidBimod Q Λ ν hρ hQ σ) N.carrier :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ (braidBimod Q Λ ν hρ hQ σ) N.carrier).flip.compl₂
      (braidingBimoduleEquiv hρ hQ σ).toLinearMap)
    (fun n c x => by
      change BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ x)
          (cornerOpRingHom hρ hQ (op c) • (show N.carrier from n)) =
        BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ (c • x)) (show N.carrier from n)
      rw [cornerOpRingHom_op, ← BalancedTensor.op_smul_tmul, braidingBimoduleEquiv_smul])

private theorem braidTensorFrom_balanced_corner (b : braidBimod Q Λ ν hρ hQ σ) (c : 𝒞)
    (n : N.carrier) :
    (BalancedTensor.tmul (show CornerRes G hρ hQ N from n)
        ((braidingBimoduleEquiv hρ hQ σ).symm
          ((op (op (violCornerEquiv hρ hQ c)) : (𝒯ᵐᵒᵖ)ᵐᵒᵖ) • b)) :
        BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳) =
      BalancedTensor.tmul
        (show CornerRes G hρ hQ N from (op (violCornerEquiv hρ hQ c) • n : N.carrier))
        ((braidingBimoduleEquiv hρ hQ σ).symm b) := by
  refine (congrArg (BalancedTensor.tmul (show CornerRes G hρ hQ N from n))
    (braidingBimoduleEquiv_symm_smul hρ hQ σ c b)).trans ?_
  have hn : (show CornerRes G hρ hQ N from (op (violCornerEquiv hρ hQ c) • n : N.carrier)) =
      (op c : 𝒞ᵐᵒᵖ) • (show CornerRes G hρ hQ N from n) := by
    rw [CornerRes.smul_def, cornerOpRingHom_op]
  rw [hn, BalancedTensor.op_smul_tmul]

private theorem braidTensorFrom_balanced (b : braidBimod Q Λ ν hρ hQ σ) (a : 𝒯ᵐᵒᵖ)
    (n : N.carrier) :
    (BalancedTensor.tmul (show CornerRes G hρ hQ N from n)
        ((braidingBimoduleEquiv hρ hQ σ).symm (op a • b)) :
        BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳) =
      BalancedTensor.tmul (show CornerRes G hρ hQ N from (a • n : N.carrier))
        ((braidingBimoduleEquiv hρ hQ σ).symm b) := by
  obtain ⟨c, hc⟩ : ∃ c, op (violCornerEquiv hρ hQ c) = a :=
    ⟨(violCornerEquiv hρ hQ).symm a.unop, by rw [RingEquiv.apply_symm_apply, op_unop]⟩
  subst hc
  exact braidTensorFrom_balanced_corner hρ hQ σ N b c n

/-- The inverse map `x ⊗ n ↦ n ⊗ x`. -/
private def braidTensorFrom :
    BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ (braidBimod Q Λ ν hρ hQ σ) N.carrier →ₗ[k]
      BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳 :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k k 𝒞 (CornerRes G hρ hQ N) 𝒳).flip.comp
      (braidingBimoduleEquiv hρ hQ σ).symm.toLinearMap)
    (fun b a n => braidTensorFrom_balanced hρ hQ σ N b a n)

private theorem braidTensorTo_tmul (n : CornerRes G hρ hQ N) (x : 𝒳) :
    braidTensorTo hρ hQ σ N (BalancedTensor.tmul n x) =
      BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ x) (show N.carrier from n) := rfl

private theorem braidTensorFrom_tmul (b : braidBimod Q Λ ν hρ hQ σ) (n : N.carrier) :
    braidTensorFrom hρ hQ σ N (BalancedTensor.tmul b n) =
      BalancedTensor.tmul (show CornerRes G hρ hQ N from n)
        ((braidingBimoduleEquiv hρ hQ σ).symm b) := rfl

/-- **`N ⊗_{T^λ} B` is the ordinary tensor of the derived braid functor**:
`N ⊗_{T^λ} B ≃ N ⊗_{e_λ V e_λ} e_λ V e_{σλ}`. -/
def braidTensorCornerEquiv :
    BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳 ≃ₗ[k]
      BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ (braidBimod Q Λ ν hρ hQ σ) N.carrier :=
  LinearEquiv.ofLinearMap (braidTensorTo hρ hQ σ N) (braidTensorFrom hρ hQ σ N)
    (BalancedTensor.ext fun b n => by
      rw [LinearMap.comp_apply, braidTensorFrom_tmul, braidTensorTo_tmul,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])
    (BalancedTensor.ext fun n x => by
      rw [LinearMap.comp_apply, braidTensorTo_tmul, braidTensorFrom_tmul,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])

theorem braidTensorCornerEquiv_tmul (n : CornerRes G hρ hQ N) (x : 𝒳) :
    braidTensorCornerEquiv hρ hQ σ N (BalancedTensor.tmul n x) =
      BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ x) (show N.carrier from n) := rfl

theorem braidTensorCornerEquiv_symm_tmul (x : 𝒳) (n : N.carrier) :
    (braidTensorCornerEquiv hρ hQ σ N).symm
        (BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ x) n) =
      BalancedTensor.tmul (show CornerRes G hρ hQ N from n) x := by
  rw [LinearEquiv.symm_apply_eq]
  rfl

universe w

include hρ hQ in
set_option backward.isDefEq.respectTransparency false in
/-- **The ordinary braid of a module map is injective when its derived braid is injective in
degree zero.** -/
theorem injective_mapRight_braidBimod_of_mono [HasDerivedCategory.{w} 𝒞ᵐᵒᵖ]
    [HasDerivedCategory.{w} 𝒞'ᵐᵒᵖ] {N N' : GFin (oppositeGrade (tensorProductGrade G ν))}
    (f : N.carrier →ₗ[𝒯ᵐᵒᵖ] N'.carrier)
    (h : Mono ((DG.DerivedCategory.homologyFunctor (A := 𝒞'ᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor.{w} k Q Λ ν (List.finRange ℓ) (List.map σ (List.finRange ℓ))).map
        (DG.DerivedCategory.Q.map ((degreeZeroModuleFunctor 𝒞ᵐᵒᵖ).map
          (ModuleCat.ofHom (CornerRes.map hρ hQ f))))))) :
    Function.Injective (BalancedTensor.mapRight (k := k) (B := 𝒯σᵐᵒᵖ)
      (M := braidBimod Q Λ ν hρ hQ σ) f) := by
  let μ : BalancedTensor k k 𝒞 (CornerRes G hρ hQ N) 𝒳 →+
      BalancedTensor k k 𝒞 (CornerRes G hρ hQ N') 𝒳 :=
    ((braidTensorCornerEquiv hρ hQ σ N').symm.toLinearMap.comp
      (((BalancedTensor.mapRight (k := k) (B := 𝒯σᵐᵒᵖ)
        (M := braidBimod Q Λ ν hρ hQ σ) f).restrictScalars k).comp
        (braidTensorCornerEquiv hρ hQ σ N).toLinearMap)).toAddMonoidHom
  have hinj := injective_of_mono_derivedRightTensorHomology (k := k) (C := 𝒞) (C' := 𝒞')
    («X» := 𝒳) (N := CornerRes G hρ hQ N) («P» := CornerRes G hρ hQ N')
    (CornerRes.op_algebraMap_smul hρ hQ N) (CornerRes.op_algebraMap_smul hρ hQ N')
    ((degreeZeroModuleFunctor 𝒞ᵐᵒᵖ).map (ModuleCat.ofHom (CornerRes.map hρ hQ f))) μ
    (fun n x => by
      change (braidTensorCornerEquiv hρ hQ σ N').symm
        (BalancedTensor.tmul (braidingBimoduleEquiv hρ hQ σ x) (f n)) = _
      rw [braidTensorCornerEquiv_symm_tmul]
      rfl) h
  intro y y' hyy
  apply (braidTensorCornerEquiv hρ hQ σ N).symm.injective
  apply hinj
  change (braidTensorCornerEquiv hρ hQ σ N').symm (BalancedTensor.mapRight f
      (braidTensorCornerEquiv hρ hQ σ N ((braidTensorCornerEquiv hρ hQ σ N).symm y))) =
    (braidTensorCornerEquiv hρ hQ σ N').symm (BalancedTensor.mapRight f
      (braidTensorCornerEquiv hρ hQ σ N ((braidTensorCornerEquiv hρ hQ σ N).symm y')))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hyy]

end Categorification.Stendhal.BraidedStendhalAlgebra
