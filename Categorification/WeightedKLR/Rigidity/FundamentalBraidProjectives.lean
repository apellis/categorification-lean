/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleResolution
import Categorification.WeightedKLR.Rigidity.FundamentalBraidCorners
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity

/-!
# Fundamental projectives in the diagonal braid corner

The projective resolution used in Webster, arXiv:1309.3796v2,
Proposition 7.11 is a resolution over the two-red tensor product
algebra. The diagonal-corner equivalence of §6 carries its loading
idempotents and its mixed crossing maps to the diagrams in the source
ring of the derived braid.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra MulOpposite DG
open scoped DG.DegreeZero
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "R" => KLRAlgebra ℚ (stendhalQ Q wt) μ
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "P" => redProj ℚ Q wt ν (List.finRange 2)
local notation "E" => StendhalAlgebraAllOrders.redOrderedIdem ℚ Q wt ν

private theorem symmQ : KLRSymm Q := fun i j h => (h (Subsingleton.elim i j)).elim

/-- The source-ring comparison for the fundamental braid in Webster v2,
Proposition 7.11, using the canonical reduced words. -/
def fundamentalBraidSourceEquiv : K ≃+* T := violCornerEquiv wordSpec symmQ

/-- Project an affine diagram to the diagonal red corner, then impose violation. -/
def diagonalDiagram (z : R) : K :=
  violCornerHom ℚ Q wt ν (cornerMk (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν z))

/-- Both presentations project an arbitrary affine source diagram to
the same tensor product algebra element (Webster v2, §6 and Proposition 7.11). -/
theorem fundamentalBraidSourceEquiv_diagram (z : R) :
    fundamentalBraidSourceEquiv (diagonalDiagram z) =
      project (StendhalAlgebraAllOrders.ofKLR ℚ Q wt ν z) := by
  refine (violCornerEquiv_violCornerHom (Λ := wt) wordSpec symmQ (cornerMk (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν z))).trans ?_
  apply congrArg (TensorProductAlgebra.mk Q wt ν)
  apply Subtype.ext
  rw [identityCornerHom_val,cornerMk_val,map_mul,map_mul,toAllOrders_ofKLR]
  change _ = StendhalAlgebraAllOrders.ofKLR ℚ Q wt ν z * E
  have hp : toAllOrders ℚ Q wt ν P = E := toAllOrders_redIdem
  rw [hp,(redOrderedIdem_commute Q wt ν _).eq,mul_assoc,(StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).eq]

/-- The source equivalence identifies both source principal projectors of
the middle resolution with their tensor product algebra projectors. -/
theorem fundamentalBraidSourceEquiv_loadings :
    fundamentalBraidSourceEquiv (diagonalDiagram (e middle)) = middleIdem ∧
    fundamentalBraidSourceEquiv (diagonalDiagram (e terminal)) = terminalIdem :=
  ⟨fundamentalBraidSourceEquiv_diagram _,fundamentalBraidSourceEquiv_diagram _⟩

/-- The same source equivalence reads the differentials of the fundamental
resolution as the two oriented mixed crossing diagrams. -/
theorem fundamentalBraidSourceEquiv_crossings :
    fundamentalBraidSourceEquiv (diagonalDiagram (ψ 1 * e middle)) =
      project (StendhalAlgebraAllOrders.ψ 1) * middleIdem ∧
    fundamentalBraidSourceEquiv (diagonalDiagram (ψ 1 * e terminal)) =
      project (StendhalAlgebraAllOrders.ψ 1) * terminalIdem := by
  rw [fundamentalBraidSourceEquiv_diagram,fundamentalBraidSourceEquiv_diagram]
  constructor <;> simp only [map_mul] <;> rfl

private theorem orderedMiddle : redWord middle = List.finRange 2 := by decide +kernel
private theorem orderedTerminal : redWord terminal = List.finRange 2 := by decide +kernel
local notation "M" => (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) orderedMiddle)
local notation "L" => (violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) orderedTerminal)

private theorem diagonal_loading (s : Seq μ) (hs : redWord s = List.finRange 2) :
    diagonalDiagram (e s) = violLoadingIdem (k := ℚ) (Q := Q) (Λ := wt) hs := by
  apply Subtype.ext
  exact congrArg (violMk ℚ Q wt ν) (cornerMk_e_val hs)

private theorem middle_img : fundamentalBraidSourceEquiv M = middleIdem := by
  rw [← diagonal_loading]
  exact fundamentalBraidSourceEquiv_loadings.1

private theorem terminal_img : fundamentalBraidSourceEquiv L = terminalIdem := by
  rw [← diagonal_loading]
  exact fundamentalBraidSourceEquiv_loadings.2

private def idealEquiv {S U : Type*} [Ring S] [Ring U] (φ : S ≃+* U) {p : S} {q : U}
    (hq : φ p = q) : rIdeal p ≃+ rIdeal q where
  toFun x := ⟨φ x.val,by rw [mem_rIdeal,← hq,← map_mul,show p * x.val = x.val from x.property]⟩
  invFun y := ⟨φ.symm y.val,by apply φ.injective; rw [map_mul,φ.apply_symm_apply,hq]; exact y.property⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.val)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add _ _ _)

private abbrev mEquiv := idealEquiv fundamentalBraidSourceEquiv middle_img
private abbrev tEquiv := idealEquiv fundamentalBraidSourceEquiv terminal_img

private def sourceMap {p q : K} {p' q' : T} (hp : fundamentalBraidSourceEquiv p = p')
    (hq : fundamentalBraidSourceEquiv q = q') (u : K) (f : rIdeal p' →ₗ[Tᵐᵒᵖ] rIdeal q')
    (h : ∀ x, (f x).val = fundamentalBraidSourceEquiv u * x.val) :
    rIdeal p →ₗ[Kᵐᵒᵖ] rIdeal q where
  toFun x := ⟨u * x.val,by
    apply fundamentalBraidSourceEquiv.injective
    simp only [map_mul,hq]
    have h' := (f (idealEquiv fundamentalBraidSourceEquiv hp x)).property
    change q' * (f _).val = (f _).val at h'
    rw [h] at h'
    exact h'⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (mul_assoc u x.val a.unop).symm

local notation "u" => diagonalDiagram (ψ 1 * e middle)
local notation "v" => diagonalDiagram (ψ 1 * e terminal)

/-- The first differential on the principal projectives over the source
ring of the fundamental braid (Webster v2, Proposition 7.11). -/
def braidSourceD₂ : rIdeal M →ₗ[Kᵐᵒᵖ] rIdeal L :=
  sourceMap middle_img terminal_img u fundamentalResolutionMap (fun x => by
    rw [fundamentalBraidSourceEquiv_crossings.1]; rfl)

/-- The second differential in the source projective resolution, from the
terminal to the middle loading. -/
def braidSourceD₁ : rIdeal L →ₗ[Kᵐᵒᵖ] rIdeal M :=
  sourceMap terminal_img middle_img v terminalToMiddle (fun x => by
    rw [fundamentalBraidSourceEquiv_crossings.2]; rfl)

private theorem d₂_comm (x : rIdeal M) :
    tEquiv (braidSourceD₂ x) = fundamentalResolutionMap (mEquiv x) := by
  apply Subtype.ext
  change fundamentalBraidSourceEquiv (u * x.val) = _ * fundamentalBraidSourceEquiv x.val
  rw [map_mul,fundamentalBraidSourceEquiv_crossings.1]

private theorem d₁_comm (x : rIdeal L) :
    mEquiv (braidSourceD₁ x) = terminalToMiddle (tEquiv x) := by
  apply Subtype.ext
  change fundamentalBraidSourceEquiv (v * x.val) = _ * fundamentalBraidSourceEquiv x.val
  rw [map_mul,fundamentalBraidSourceEquiv_crossings.2]

/-- The augmentation of the diagonal source projective onto Webster's
middle simple, under the diagonal source-ring equivalence. -/
def braidSourceAug : rIdeal M →+ (rIdeal middleIdem ⧸ middleCutTrace) :=
  middleCutTrace.mkQ.toAddMonoidHom.comp mEquiv.toAddMonoidHom

/-- The middle simple over the source order ring of the derived braid. -/
def braidSourceMiddleHead : ModuleCat Kᵐᵒᵖ :=
  (ModuleCat.restrictScalars fundamentalBraidSourceEquiv.toRingHom.op).obj
    (ModuleCat.of Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace))

/-- The augmentation is linear over the diagonal braid source ring. -/
def braidSourceMiddleAugmentation : rIdeal M →ₗ[Kᵐᵒᵖ] braidSourceMiddleHead where
  toFun x := braidSourceAug x
  map_add' x y := braidSourceAug.map_add _ _
  map_smul' a x := by
    change middleCutTrace.mkQ (mEquiv (a • x)) = fundamentalBraidSourceEquiv.toRingHom.op a • middleCutTrace.mkQ (mEquiv x)
    rw [← map_smul]
    apply congrArg middleCutTrace.mkQ
    apply Subtype.ext
    exact map_mul fundamentalBraidSourceEquiv x.val a.unop

/-- The mixed crossings form the same exact projective resolution on the
diagonal ring used by the derived braid in Webster v2, Proposition 7.11.
The augmentation is onto the middle head of its tensor product algebra. -/
theorem fundamentalBraidSourceResolution :
    Module.Projective Kᵐᵒᵖ (rIdeal M) ∧ Module.Projective Kᵐᵒᵖ (rIdeal L) ∧
      Function.Injective braidSourceD₂ ∧ Function.Exact braidSourceD₂ braidSourceD₁ ∧
      Function.Exact braidSourceD₁ braidSourceMiddleAugmentation ∧ Function.Surjective braidSourceMiddleAugmentation := by
  refine ⟨rIdeal_projective (isIdempotentElem_violLoadingIdem orderedMiddle),
    rIdeal_projective (isIdempotentElem_violLoadingIdem orderedTerminal),?_,?_,?_,
    middleCutTrace.mkQ_surjective.comp mEquiv.surjective⟩
  · intro x y h
    exact mEquiv.injective (fundamentalResolutionMap_injective ((d₂_comm x).symm.trans
      ((congrArg tEquiv h).trans (d₂_comm y))))
  · intro x
    constructor
    · intro hx
      have hy : terminalToMiddle (tEquiv x) = 0 := (d₁_comm x).symm.trans ((congrArg mEquiv hx).trans (map_zero _))
      obtain ⟨y,he⟩ := (middleProjectiveResolution.2.2.2.1 (tEquiv x)).mp hy
      obtain ⟨z,rfl⟩ := mEquiv.surjective y
      exact ⟨z,tEquiv.injective ((d₂_comm _).trans he)⟩
    · rintro ⟨y,rfl⟩
      apply mEquiv.injective
      rw [d₁_comm,d₂_comm,map_zero]
      exact (middleProjectiveResolution.2.2.2.1 _).mpr ⟨_,rfl⟩
  · intro x
    change middleCutTrace.mkQ (mEquiv x) = 0 ↔ _
    rw [middleProjectiveResolution.2.2.2.2.1 (mEquiv x)]
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨z,rfl⟩ := tEquiv.surjective y
      exact ⟨z,mEquiv.injective ((d₁_comm _).trans hy)⟩
    · rintro ⟨y,rfl⟩
      exact ⟨tEquiv y,(d₁_comm y).symm⟩

/-- The value of an ordered mixed-crossing diagram in the source braid corner. -/
theorem diagonalMixed_val (s : Seq μ) (hs : redWord s = List.finRange 2)
    (ht : redWord (sadj (Multiset.card μ) 1 • s) = List.finRange 2) :
    (diagonalDiagram (ψ 1 * e s)).val = braidProject (ψ 1) * braidProject (e s) := by
  rw [← map_mul]
  apply congrArg (violMk ℚ Q wt ν)
  change P * BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (ψ 1 * e s) * P = _
  have hl : P * BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (ψ 1 * e s) =
      BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (ψ 1 * e s) := by
    rw [ψ_mul_e,map_mul,← mul_assoc,redProj_mul_e,ite_eq_left ht]
  rw [hl,map_mul,mul_assoc,e_mul_redProj,ite_eq_left hs]
  exact (map_mul _ _ _).symm

private abbrev braid := InDegreeZero (OpBimodule K (braidingBimodule ℚ Q wt ν (List.finRange 2) [1,0]))
abbrev braidTensorMiddle := TensorProductOver Kᵐᵒᵖ braid (InDegreeZero (rIdeal M))
abbrev braidTensorTerminal := TensorProductOver Kᵐᵒᵖ braid (InDegreeZero (rIdeal L))

abbrev braidTensorD₂ : braidTensorMiddle →+ braidTensorTerminal :=
  TensorProductOver.map (A := Kᵐᵒᵖ) (LinearMap.id : braid →ₗ[(Kᵐᵒᵖ)ᵐᵒᵖ] braid) braidSourceD₂
abbrev braidTensorD₁ : braidTensorTerminal →+ braidTensorMiddle :=
  TensorProductOver.map (A := Kᵐᵒᵖ) (LinearMap.id : braid →ₗ[(Kᵐᵒᵖ)ᵐᵒᵖ] braid) braidSourceD₁
abbrev braidTensorMiddleEquiv := loadingProjectiveTensorEquiv (k := ℚ) (Q := Q) (Λ := wt) (κ := [1,0]) orderedMiddle
abbrev braidTensorTerminalEquiv := loadingProjectiveTensorEquiv (k := ℚ) (Q := Q) (Λ := wt) (κ := [1,0]) orderedTerminal

/-- Under the projective tensor comparison, tensoring the two fundamental
source differentials with the braid gives left multiplication by the mixed
crossing on the whole crossed cuts (Webster v2, Proposition 7.11). -/
theorem fundamentalBraidSourceResolution_tensor :
    (∀ z : braidTensorMiddle,
      (braidTensorTerminalEquiv (braidTensorD₂ z)).val =
        braidProject (ψ 1) * (braidTensorMiddleEquiv z).val) ∧
    (∀ z : braidTensorTerminal,
      (braidTensorMiddleEquiv (braidTensorD₁ z)).val =
        braidProject (ψ 1) * (braidTensorTerminalEquiv z).val) := by
  constructor <;> intro z
  · induction z using TensorProductOver.induction_on with
    | zero => simp
    | tmul b x =>
      change (u).val * x.val.val * b.val = braidProject (ψ 1) * (x.val.val * b.val)
      have hx : braidProject (e middle) * x.val.val = x.val.val :=
        congrArg Subtype.val x.property
      rw [diagonalMixed_val middle orderedMiddle (by decide +kernel),mul_assoc _ _ x.val.val,hx,mul_assoc]
    | add x y hx hy => simp only [map_add,Submodule.coe_add,mul_add,hx,hy]
  · induction z using TensorProductOver.induction_on with
    | zero => simp
    | tmul b x =>
      change (v).val * x.val.val * b.val = braidProject (ψ 1) * (x.val.val * b.val)
      have hx : braidProject (e terminal) * x.val.val = x.val.val :=
        congrArg Subtype.val x.property
      rw [diagonalMixed_val terminal orderedTerminal (by decide +kernel),mul_assoc _ _ x.val.val,hx,mul_assoc]
    | add x y hx hy => simp only [map_add,Submodule.coe_add,mul_add,hx,hy]

end Categorification.Stendhal.FundamentalCorner
