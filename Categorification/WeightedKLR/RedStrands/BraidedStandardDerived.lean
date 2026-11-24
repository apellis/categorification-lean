/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.Induction.Restriction
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.ProjectiveKProjective

/-!
# The derived braiding on a loading projective

Webster, arXiv:1309.3796v2, §6.1, Definition 6.6 and the proof of Proposition 6.9, Figure 5.
The derived tensor product of a loading projective `e(s) T` with the braid bimodule is computed
on the projective itself. The ordinary balanced tensor identifies with `e(s) B` by
multiplication. For the two-red edge move, this cut is the loading standard at the swapped
order, by `violLoadingStandardEquivBraidCorner`. This computation is ungraded.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory DG KLR Equiv MulOpposite CornerEndomorphism
open scoped DG.DegreeZero

universe w

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "q" => violMk k Q Λ ν
local notation:max "E" s:arg => q (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation:max "Pκ" κ:arg => q (redProj k Q Λ ν κ)

/-- The loading idempotent in the violated corner for its red order. -/
noncomputable def violLoadingIdem {s : Seq μ} {κ' : List (Fin ℓ)} (hs : redWord s = κ') : C κ' :=
  ⟨E s, (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν κ')).2 ⟨by
    rw [← map_mul, redProj_mul_e, ite_eq_left hs], by
    rw [← map_mul, e_mul_redProj, ite_eq_left hs]⟩⟩

theorem isIdempotentElem_violLoadingIdem {s : Seq μ} {κ' : List (Fin ℓ)} (hs : redWord s = κ') :
    IsIdempotentElem (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs) := by
  apply Subtype.ext
  change E s * E s = E s
  rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_e, ite_eq_left rfl]

section Tensor

variable {s : Seq (stendhalWeight ℓ ν)} {κ' κ : List (Fin ℓ)} (hs : redWord s = κ')

local notation "f" => violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs
local notation "M" => InDegreeZero (OpBimodule (C κ') (braidingBimodule k Q Λ ν κ' κ))
local notation "N" => InDegreeZero (rIdeal f)
local notation "Y" => violCorner k Q Λ ν s κ
local notation "X" => TensorProductOver (C κ')ᵐᵒᵖ M N

private noncomputable def loadingTensorMul : M →+ N →+ Y where
  toFun b :=
    { toFun := fun p => ⟨p.1.val * b.1, mem_violCorner_iff.2 ⟨by
        rw [← mul_assoc]
        exact congrArg (fun z : C κ' => z.val * b.1) p.2,
        by rw [mul_assoc, (mem_cornerBimodule.1 b.2).2]⟩⟩
      map_zero' := Subtype.ext (zero_mul _)
      map_add' := fun p p' => Subtype.ext (add_mul p.1.val p'.1.val b.1) }
  map_zero' := AddMonoidHom.ext fun p => Subtype.ext (mul_zero p.1.val)
  map_add' b b' := AddMonoidHom.ext fun p => Subtype.ext (mul_add p.1.val b.1 b'.1)

private noncomputable def loadingTensorProduct : X →+ Y :=
  TensorProductOver.lift (loadingTensorMul hs) fun a b p =>
    Subtype.ext (mul_assoc p.1.val a.unop.val b.1).symm

private noncomputable def braidCutInclusion : Y →+ M where
  toFun y := ⟨y.1, mem_cornerBimodule.2 ⟨by
      have h := (mem_violCorner_iff.1 y.2).1
      have hp : Pκ κ' * E s = E s :=
        corner_mul_left (isIdempotentElem_violMk_redProj k Q Λ ν κ') f
      calc
        Pκ κ' * y.1 = Pκ κ' * (E s * y.1) := congrArg (Pκ κ' * ·) h.symm
        _ = y.1 := by rw [← mul_assoc, hp, h], (mem_violCorner_iff.1 y.2).2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ordinary balanced tensor of the loading projective with `B(κ', κ)` is the cut
`e(s) B(κ', κ)`. The forward map multiplies, and the inverse inserts `e(s)` in the tensor. -/
noncomputable def loadingProjectiveTensorEquiv : X ≃ₗ[(C κ)ᵐᵒᵖ] Y := by
  let p₀ : N := ⟨f, isIdempotentElem_violLoadingIdem hs⟩
  let g : Y →+ X := ((TensorProductOver.tmulAddHom (C κ')ᵐᵒᵖ M N).flip p₀).comp
    (braidCutInclusion hs)
  have hg : g.comp (loadingTensorProduct hs) = AddMonoidHom.id X := by
    apply TensorProductOver.addHom_ext
    intro b p
    change TensorProductOver.tmul (C κ')ᵐᵒᵖ (op (op p.1) • b) p₀ =
      TensorProductOver.tmul (C κ')ᵐᵒᵖ b p
    rw [TensorProductOver.op_smul_tmul]
    congr 1
    exact Subtype.ext p.2
  refine { loadingTensorProduct hs with
    invFun := g
    left_inv := DFunLike.congr_fun hg
    right_inv := fun y => Subtype.ext (mem_violCorner_iff.1 y.2).1
    map_smul' := ?_ }
  intro a x
  have h : (loadingTensorProduct hs).comp (DistribSMul.toAddMonoidHom X a) =
      (DistribSMul.toAddMonoidHom Y a).comp (loadingTensorProduct hs) :=
    TensorProductOver.addHom_ext fun b p => Subtype.ext (mul_assoc p.1.val b.1 a.unop.val).symm
  exact DFunLike.congr_fun h x

theorem loadingProjectiveTensorEquiv_tmul (b : M) (p : N) :
    (loadingProjectiveTensorEquiv hs (TensorProductOver.tmul (C κ')ᵐᵒᵖ b p)).1 = p.1.val * b.1 :=
  rfl

end Tensor

section Derived

variable {s : Seq (stendhalWeight ℓ ν)} {κ' κ : List (Fin ℓ)}

/-- Webster, arXiv:1309.3796v2, §6.1, Definition 6.6 and the projective tensor step in the
proof of Proposition 6.9. Applying the ungraded braiding functor to `e(s) T` in degree zero
returns `e(s) B(κ', κ)` in degree zero. No projectivity of the braid bimodule is required. -/
noncomputable def braidingFunctorObjLoadingProjectiveIso (hs : redWord s = κ')
    [HasDerivedCategory.{w} (C κ')ᵐᵒᵖ] [HasDerivedCategory.{w} (C κ)ᵐᵒᵖ] :
    (braidingFunctor.{w} k Q Λ ν κ' κ).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (C κ')ᵐᵒᵖ
          (InDegreeZero ↥(rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs))))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (C κ)ᵐᵒᵖ (InDegreeZero (violCorner k Q Λ ν s κ))) := by
  let T := C κ'
  let T' := C κ
  let f : T := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs
  letI := rIdeal_projective (isIdempotentElem_violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs)
  let M := OpBimodule T (braidingBimodule k Q Λ ν κ' κ)
  let Y := violCorner k Q Λ ν s κ
  let U := DGModuleCat.of Tᵐᵒᵖ (InDegreeZero (rIdeal f))
  let W := DGModuleCat.of T'ᵐᵒᵖ (InDegreeZero Y)
  let tensorDG := DGModuleCat.tensorFunctor (B := Tᵐᵒᵖ) T'ᵐᵒᵖ (InDegreeZero M)
  let e : TensorProductOver Tᵐᵒᵖ (InDegreeZero M) (InDegreeZero (rIdeal f)) ≃ᵈᵍ[T'ᵐᵒᵖ]
      InDegreeZero Y := DGModuleEquiv.ofDegreeZero (loadingProjectiveTensorEquiv hs)
    (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
    TensorProductOver.d_inDegreeZero InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)
  exact derivedTensorObjIso (A := T'ᵐᵒᵖ) (B := Tᵐᵒᵖ) (M := M) (P := U)
    (show IsKProjective Tᵐᵒᵖ (InDegreeZero (rIdeal f)) from InDegreeZero.isKProjective) ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv (M := tensorDG.obj U) (N := W) e)

end Derived

section TwoRed

variable {Λ₂ : Fin 2 → I →₀ ℕ}
local notation "m₂" => Multiset.card (stendhalWeight 2 ν)
local notation "C₂" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ₂) (ν := ν)

omit [DecidableEq I] in
/-- In the two-red Figure 5 move, the first red of `t` becomes the last red of `s`, and
its second red becomes the first strand of `s`. -/
theorem EdgeBraid.redWord_source_twoRed {s t : Seq (stendhalWeight 2 ν)} {r d : Fin 2}
    {g : Perm (Fin m₂)} (h1 : 1 < m₂) (ht₀ : t.lbl ⟨0, by omega⟩ = .inr r)
    (ht₁ : t.lbl ⟨1, h1⟩ = .inr d) (hb : EdgeBraid (show 0 < m₂ by omega) r g s t) :
    redWord s = [d, r] := by
  have hs₀ : s.lbl ⟨0, by omega⟩ = .inr d := by
    rw [← hb.smul_eq, lbl_smul]
    have hg : g⁻¹ (⟨0, by omega⟩ : Fin m₂) = ⟨1, h1⟩ :=
      Fin.ext (hb.shift _ (by dsimp; omega))
    rw [hg, ht₁]
  have hne : d ≠ r := by
    rintro rfl
    have h := congrArg Fin.val (lbl_inj_of_inr t d ht₀ ht₁)
    contradiction
  obtain ⟨L, hL⟩ := exists_redWord_eq_cons (by omega) hs₀
  have hp : (redWord s).Perm [d, r] := by
    apply (List.perm_ext_iff_of_nodup (redWord_nodup _) (by simp [hne])).2
    intro x
    refine ⟨fun _ => ?_, fun _ => mem_redWord s x⟩
    have hx : x = d ∨ x = r := by
      have := x.isLt
      have := d.isLt
      have := r.isLt
      simp only [Fin.ext_iff] at hne ⊢
      omega
    simpa using hx
  rw [hL] at hp ⊢
  rw [hp.cons_inv.eq_singleton]

/-- Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9, Figure 5: the ungraded derived braiding
of the lower loading projective is the swapped loading standard in cohomological degree zero.
The comparison with the braid cut uses the Figure 5 map `violLoadingStandardEquivBraidCorner`.
This statement uses the loading projective and loading standard, not the exterior-projective
standardization functor, and does not address the internal shift. -/
noncomputable def braidingFunctorObjFigureFiveIso
    {ρ : Perm (Fin m₂) → List ℕ} (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)
    {s t : Seq (stendhalWeight 2 ν)} {r d : Fin 2} {g : Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t.lbl ⟨0, by omega⟩ = .inr r) (ht₁ : t.lbl ⟨1, h1⟩ = .inr d)
    (hb : EdgeBraid (show 0 < m₂ by omega) r g s t)
    [HasDerivedCategory.{w} (C₂ [d, r])ᵐᵒᵖ] [HasDerivedCategory.{w} (C₂ [r, d])ᵐᵒᵖ] :
    (braidingFunctor.{w} k Q Λ₂ ν [d, r] [r, d]).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (C₂ [d, r])ᵐᵒᵖ
          (InDegreeZero ↥(rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ₂)
            (hb.redWord_source_twoRed h1 ht₀ ht₁)))))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (C₂ [r, d])ᵐᵒᵖ
        (InDegreeZero (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ₂) t [r, d]))) :=
  braidingFunctorObjLoadingProjectiveIso (hb.redWord_source_twoRed h1 ht₀ ht₁) ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv (DGModuleEquiv.ofDegreeZero
      (show InDegreeZero (violCorner k Q Λ₂ ν s [r, d]) ≃ₗ[(C₂ [r, d])ᵐᵒᵖ]
          InDegreeZero (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ₂) t [r, d]) from
        (violLoadingStandardEquivBraidCorner hρ hQ h1 ht₀ ht₁ hb).symm)
      (fun hx hn => ((InDegreeZero.mem_grading_iff _).1 hx).resolve_left hn)
      (InDegreeZero.d_apply _) InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)))

end TwoRed

end Categorification.Stendhal.BraidedStendhalAlgebra
