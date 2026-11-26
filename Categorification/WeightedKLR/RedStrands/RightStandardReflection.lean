/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.GradedRightStandardModule
import Categorification.WeightedKLR.RedStrands.LeftStandardGFin
import Categorification.WeightedKLR.RedStrands.ReflectionFlip
import Categorification.Algebra.Graded.RightTwistCharacter

/-!
# Right standard modules as reflected left standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1,
Definition 5.1. For a loading `s` of the red order `(1, …, ℓ)`, the standard module
`e(s) T / U_s`, a graded right `T^λ`-module, is the right twist of the graded left standard
module `T e(s) / U_s` by horizontal reflection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite Categorification.Graded RedBlock

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- Relabelling the red strands along the identity permutation is the identity. -/
theorem redPermAlgEquiv_one (x : BraidedStendhalAlgebra k Q Λ ν) :
    redPermAlgEquiv (Λ' := Λ) (1 : Perm (Fin ℓ)) (fun _ => rfl) x = x := by
  obtain ⟨u, rfl⟩ := ofKLR_surjective x
  unfold redPermAlgEquiv
  rw [relabelAlgEquiv_ofKLR]
  congr 1
  let R := SeqRelabel.ofRedPerm (k := k) (Q := Q) (Λ' := Λ) (Λ := Λ) (ν := ν)
    (1 : Perm (Fin ℓ)) (fun _ => rfl)
  have h : KLRAlgebra.relabelHom R = AlgHom.id k _ := by
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | idem i =>
      change KLRAlgebra.relabelHom R (KLRAlgebra.e i) = KLRAlgebra.e i
      rw [KLRAlgebra.relabelHom_e]
      exact congrArg KLRAlgebra.e (Seq.redPerm_one i)
    | dot a =>
      change KLRAlgebra.relabelHom R (KLRAlgebra.x a) = KLRAlgebra.x a
      rw [KLRAlgebra.relabelHom_x]
      rfl
    | cross j =>
      change KLRAlgebra.relabelHom R (KLRAlgebra.ψ j) = KLRAlgebra.ψ j
      rw [KLRAlgebra.relabelHom_ψ]
  exact DFunLike.congr_fun h u

theorem violRedPermEquiv_one (x : ViolQuotient k Q Λ ν) :
    violRedPermEquiv (Λ' := Λ) (1 : Perm (Fin ℓ)) (fun _ => rfl) x = x := by
  obtain ⟨y, rfl⟩ := violMk_surjective x
  rw [violRedPermEquiv_violMk, redPermAlgEquiv_one]

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

/-- At the identity permutation, the coefficient change of `loadingStandardLeftEquiv` is the
corner identification `violCornerEquiv` followed by horizontal reflection. -/
theorem leftCoefficientEquiv_one_op
    {c : ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ))}
    {d : (isIdempotentElem_violRedProj k Q Λ ν).Corner} (h : d.1 = c.1) :
    leftCoefficientEquiv (Λ := Λ) hρ hQ 1 (op c) =
      tensorFlip (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ d) := by
  change tensorFlip (violCornerRedPermTensorEquiv (Λ₀ := Λ) hρ hQ 1 c) = _
  congr 1
  let e := violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ ⇑(1 : Perm (Fin ℓ))) (Λ := Λ)
    (ν := ν) 1 (fun _ => rfl) (List.finRange ℓ)
  change violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ (e.symm c) = _
  congr 1
  apply Subtype.ext
  have hv := congrArg Subtype.val (e.apply_symm_apply c)
  change violRedPermEquiv (Λ' := Λ) (1 : Perm (Fin ℓ)) (fun _ => rfl) (e.symm c).1 = c.1 at hv
  rw [violRedPermEquiv_one] at hv
  exact hv.trans h.symm

section Congr

variable {t t' : Seq (stendhalWeight ℓ ν)} {κ κ' : List (Fin ℓ)}

/-- Corner elements at equal orders. -/
def cornerCast (hκ : κ = κ') (c : ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) :
    ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ' := by
  subst hκ
  exact c

@[simp] theorem cornerCast_val (hκ : κ = κ')
    (c : ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ) : (cornerCast hκ c).1 = c.1 := by
  subst hκ
  rfl

/-- Loading standards at equal loadings and orders. -/
def loadingStandardCongr (ht : t = t') (hκ : κ = κ') :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ ≃+
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t' κ' := by
  subst ht hκ
  exact AddEquiv.refl _

theorem loadingStandardCongr_smul (ht : t = t') (hκ : κ = κ')
    (c : (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ)
    (c' : (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ')ᵐᵒᵖ)
    (hc : c'.unop.1 = c.unop.1) (x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ) :
    loadingStandardCongr ht hκ (c • x) = c' • loadingStandardCongr ht hκ x := by
  subst ht hκ
  obtain rfl : c' = c := congrArg op (Subtype.ext hc)
  rfl

theorem loadingStandardCongr_mk (ht : t = t') (hκ : κ = κ') (y : violCorner k Q Λ ν t κ)
    (y' : violCorner k Q Λ ν t' κ') (hy : y'.1 = y.1) :
    loadingStandardCongr ht hκ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y' := by
  subst ht hκ
  obtain rfl : y' = y := Subtype.ext hy
  rfl

end Congr

section Unit

variable {t : Seq (stendhalWeight ℓ ν)} {κ : List (Fin ℓ)}

/-- The idempotent `e(t)` in the cut `e(t) V e_κ`, for a loading `t` of the order `κ`. -/
def loadingUnitCorner (ht : redWord t = κ) : violCorner k Q Λ ν t κ :=
  ⟨(violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht).1, mem_violCorner_iff.2
    ⟨congrArg Subtype.val (isIdempotentElem_violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht),
      ((Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν κ)).1
        (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) ht).2).2⟩⟩

/-- The generator `[e(t)]` of the loading standard `e(t) V e_κ / U_t`. -/
def loadingUnit (ht : redWord t = κ) : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ :=
  Submodule.Quotient.mk (loadingUnitCorner ht)

theorem loadingUnit_mem_zero (G : KLR.GradingDatum (stendhalQ Q Λ)) (ht : redWord t = κ) :
    loadingUnit (k := k) (Q := Q) (Λ := Λ) ht ∈ loadingStandardGrade G t κ 0 :=
  Graded.mem_map_of_mem _ (loadingMkK t κ) (Graded.mem_comap.2
    (Graded.mem_map_of_mem _ (violMk k Q Λ ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR k Q Λ ν).toLinearMap (G.e_mem_grade t))))

theorem loadingStandardCongr_loadingUnit {t' : Seq (stendhalWeight ℓ ν)} {κ' : List (Fin ℓ)}
    (h : t = t') (hκ : κ = κ') (ht : redWord t = κ) (ht' : redWord t' = κ') :
    loadingStandardCongr h hκ (loadingUnit (k := k) (Q := Q) (Λ := Λ) ht) = loadingUnit ht' :=
  loadingStandardCongr_mk h hκ _ _ (by subst h; rfl)

end Unit

/-- At the identity permutation, `loadingStandardLeftEquiv` matches the generators. -/
theorem loadingStandardLeftEquiv_one_unit {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hs
        (loadingUnit (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 hs)) =
      leftStandardUnit Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs := by
  change Submodule.Quotient.mk (⟨leftCoefficientEquiv (Λ := Λ) hρ hQ 1
    (op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel 1 hs))), _⟩ :
      lIdeal (seqIdem Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs)) = _
  exact congrArg Submodule.Quotient.mk (Subtype.ext (leftCoefficientEquiv_loadingIdem hρ hQ 1 hs))

section Twist

variable (G : KLR.GradingDatum (stendhalQ Q Λ)) (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)

theorem map_one_finRange : List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ) = List.finRange ℓ := by
  simp

/-- The coefficient change at the identity sends the reflection of `a` to the corner element
`violCornerEquiv⁻¹ a`. -/
theorem leftCoefficientEquiv_one_symm_flip (a : TensorProductAlgebra k Q Λ ν) :
    (leftCoefficientEquiv (Λ := Λ) hρ hQ 1).symm (tensorFlip a) =
      op (cornerCast (map_one_finRange (ℓ := ℓ)).symm
        ((violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm a)) := by
  rw [RingEquiv.symm_apply_eq, leftCoefficientEquiv_one_op hρ hQ
    (d := (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ).symm a)
    (cornerCast_val _ _).symm]
  exact congrArg tensorFlip (RingEquiv.apply_symm_apply _ a).symm

/-- **The right standard module is the reflected left standard module** (Webster,
arXiv:1309.3796v2, Definition 5.1): for a loading `s` of the red order `(1, …, ℓ)`,
`e(s) T / U_s ≅ (T e(s) / U_s)^ψ` as right `T^λ`-modules, where `ψ` is horizontal reflection. -/
def rightStandardTwistEquiv {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    Twist (tensorReflection (ν := ν) G hsymm) (leftStandard Q Λ s hs) ≃ₗ[
      (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] RightStandard Λ hρ hQ s :=
  let φ := loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hs
  let φ' : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm 1 s)
      (List.map ⇑(1 : Perm (Fin ℓ)) (List.finRange ℓ)) ≃+ leftStandard Q Λ s hs :=
    φ.toAddEquiv
  let c := loadingStandardCongr (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm_one s)
    (map_one_finRange (ℓ := ℓ))
  let o : Twist (tensorReflection (ν := ν) G hsymm) (leftStandard Q Λ s hs) ≃+
      leftStandard Q Λ s hs :=
    (Twist.of (k := k) (ψ := tensorReflection (ν := ν) G hsymm)
      (M := leftStandard Q Λ s hs)).symm.toAddEquiv
  { (o.trans φ'.symm).trans c with
    map_smul' := fun a z => by
      change c (φ.symm (tensorReflection (ν := ν) G hsymm a.unop • o z)) =
        rightCornerHom (Λ := Λ) (ν := ν) hρ hQ a • c (φ.symm (o z))
      rw [LinearEquiv.map_smulₛₗ, tensorReflection_apply]
      change c ((leftCoefficientEquiv (Λ := Λ) hρ hQ 1).symm (tensorFlip a.unop) • _) = _
      rw [leftCoefficientEquiv_one_symm_flip]
      exact loadingStandardCongr_smul (k := k) (Q := Q) (Λ := Λ) _ _ _
        (rightCornerHom (Λ := Λ) (ν := ν) hρ hQ a) (cornerCast_val _ _).symm _ }

theorem rightStandardTwistEquiv_unit {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    (ht : redWord s = List.finRange ℓ) :
    rightStandardTwistEquiv hρ hQ G hsymm hs (Twist.of (leftStandardUnit Q Λ s hs)) =
      loadingUnit (k := k) (Q := Q) (Λ := Λ) ht := by
  change loadingStandardCongr (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm_one s)
    (map_one_finRange (ℓ := ℓ))
      ((loadingStandardLeftEquiv (Λ := Λ) hρ hQ 1 hs).symm
        (leftStandardUnit Q (Λ ∘ ⇑(1 : Perm (Fin ℓ))) s hs)) = _
  rw [(LinearEquiv.symm_apply_eq _).2 (loadingStandardLeftEquiv_one_unit hρ hQ hs).symm]
  exact loadingStandardCongr_loadingUnit _ _ _ _

/-- **The graded right standard module is the reflected graded left standard module**
(Webster, arXiv:1309.3796v2, Definition 5.1): for a loading `s` of the red order `(1, …, ℓ)`,
`(T e(s) / U_s)^ψ ≅ e(s) T / U_s` as graded right `T^λ`-modules. -/
def rightStandardGradedEquiv {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    (ht : redWord s = List.finRange ℓ) :
    twistGrading (tensorReflection (ν := ν) G hsymm) (gradedLeftStandard G s hs) ≃ᵍ[
      (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
      (show ℤ → Submodule k (RightStandard Λ hρ hQ s) from
        loadingStandardGrade G s (List.finRange ℓ)) :=
  letI := loadingStandardDecomposition G s (List.finRange ℓ) ht
  letI := gradedLeftStandardDecomposition G s hs
  GradedEquiv.ofGenerator (𝒜 := oppositeGrade (tensorProductGrade G ν))
    (Twist.of (leftStandardUnit Q Λ s hs))
    (fun d x hx => by
      obtain ⟨b, hb, hbx⟩ := gradedLeftStandard_exists_smul_unit G s hs hx
      refine ⟨op (tensorReflection (ν := ν) G hsymm b),
        show _ ∈ tensorProductGrade G ν d from (tensorReflection (ν := ν) G hsymm).mem_grade hb,
        ?_⟩
      rw [Twist.op_smul_of, GradedAntiInvolution.invol, hbx]
      rfl)
    (rightStandardTwistEquiv hρ hQ G hsymm hs)
    (by
      rw [rightStandardTwistEquiv_unit hρ hQ G hsymm hs ht]
      exact loadingUnit_mem_zero G ht)

variable [Module.Finite k (TensorProductAlgebra k Q Λ ν)]

/-- The graded isomorphism `rightStandardGradedEquiv` between finite-dimensional modules. -/
def rightStandardIso {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    (ht : redWord s = List.finRange ℓ) :
    ((leftStandardGFin G s hs).rightTwist (tensorReflection (ν := ν) G hsymm)).Iso
      (rightStandard hρ hQ s G ht) :=
  rightStandardGradedEquiv hρ hQ G hsymm hs ht

end Twist

end Categorification.Stendhal.BraidedStendhalAlgebra
