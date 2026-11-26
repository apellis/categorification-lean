/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidStandardFiltration
import Categorification.WeightedKLR.RedStrands.ViolCornerRelabelFiltration
import Categorification.WeightedKLR.RedStrands.BraidingBimoduleLoadingFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# The braid of a sequence projective is a cut

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. For a loading `t` of the identity red order, `𝔅_σ (e(t) T^λ) = e(t) T^λ ⊗ B` is
the cut `e(t) V e_{σλ}` of the braiding bimodule (`braidRightSequenceCutEquiv`), as a right module
over the corner at `σλ`, which is `T^{λ ∘ σ}` after relabelling. So a standard filtration of
`𝔅_σ (e(t) T^λ)` is a filtration of the cut by the loading standards of red order `σλ`
(`exists_hasFiltration_violCorner_of_braidFunctor`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite ModuleFiltration BalancedTensor

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)

local notation "ord" => List.finRange ℓ
local notation "μ" => stendhalWeight ℓ ν

include hρ hQ in
/-- The image of a loading idempotent of the identity red order in `V` is `e(t)`. -/
theorem identityCornerMap_mk_e (t : Seq μ) (ht : IsRedOrdered t) :
    identityCornerMap Q Λ ν hρ hQ (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) =
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) := by
  rw [identityCornerMap_apply, ← stendhalTensorProjection_e, ← violCornerEquiv_diagonal hρ hQ,
    RingEquiv.symm_apply_apply]
  change violMk k Q Λ ν (redProj k Q Λ ν ord * ofKLR k Q Λ ν (KLRAlgebra.e t) *
    redProj k Q Λ ν ord) = _
  rw [redProj_mul_e_mul_redProj ord ((redWord_eq_finRange_iff t).2 ht)]

variable {𝔠 : QuantumGroup.CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (σ : Perm (Fin ℓ))

local notation "C'" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
local notation "𝔐" => braidBimod Q Λ ν hρ hQ σ

section

theorem isIdempotentElem_op_mk_e {t : Seq μ} (ht : IsRedOrdered t) :
    IsIdempotentElem (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))) :=
  congrArg op (isIdempotentElem_mk_e t ht)

include hρ hQ in
theorem mem_violCorner_of_idemSubspace {t : Seq μ} (ht : IsRedOrdered t)
    (z : idemSubspace k 𝔐 (op (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))))) :
    RectBimod.val _ _ (z : 𝔐) ∈ violCorner k Q Λ ν t ((List.finRange ℓ).map σ) := by
  refine (mem_violCorner_iff (s := t) (κ := (List.finRange ℓ).map σ)).2 ⟨?_, ?_⟩
  · have h := congrArg (RectBimod.val _ _) (mem_idemSubspace.1 z.2)
    rw [RectBimod.val_smul_left] at h
    change identityCornerMap Q Λ ν hρ hQ (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) *
      _ = _ at h
    rw [identityCornerMap_mk_e hρ hQ t ht] at h
    rw [← h, ← mul_assoc, ← map_mul, ← map_mul, KLRAlgebra.e_mul_e]
    simp only [↓reduceIte]
  · rw [← permCornerMap_one hρ hQ σ]
    exact (RectBimod.mem (z : 𝔐)).2

include hρ hQ in
theorem mem_idemSubspace_of_violCorner {t : Seq μ} (ht : IsRedOrdered t)
    (y : violCorner k Q Λ ν t ((List.finRange ℓ).map σ)) :
    ∃ h, RectBimod.mk (f := identityCornerMap Q Λ ν hρ hQ) (g := permCornerMap Q Λ ν hρ hQ σ)
      y.1 h ∈ idemSubspace k 𝔐 (op (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)))) := by
  have hy := (mem_violCorner_iff (s := t) (κ := (List.finRange ℓ).map σ)).1 y.2
  have hl : identityCornerMap Q Λ ν hρ hQ
      (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) * y.1 = y.1 := by
    rw [identityCornerMap_mk_e hρ hQ t ht]; exact hy.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hl, ← mul_assoc, ← map_mul, one_mul]
  · rw [permCornerMap_one hρ hQ σ]; exact hy.2
  · rw [mem_idemSubspace]
    exact RectBimod.ext hl

end

local notation "𝔅" => (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ
local notation "𝔄" => (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ

theorem idealRid_symm_apply {t : Seq μ} (ht : IsRedOrdered t)
    (z : idemSubspace k 𝔐 (op (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))))) :
    (idealRid 𝔅 (isIdempotentElem_op_mk_e (Q := Q) (Λ := Λ) (ν := ν) ht)).symm z =
      tmul (z : 𝔐) ⟨op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)), by
        rw [mem_leftIdeal, (isIdempotentElem_op_mk_e (Q := Q) (Λ := Λ) (ν := ν) ht).eq]⟩ :=
  rfl

local notation "𝔗" t:arg ht:arg => BalancedTensor k 𝔅 𝔄 𝔐
  (leftIdeal (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht))))

/-- `e(t) V e_{σλ} → e(t) T^λ ⊗ B`, `y ↦ y ⊗ e(t)`. -/
def cutToBraid {t : Seq μ} (ht : IsRedOrdered t) (y : violCorner k Q Λ ν t ((List.finRange ℓ).map σ)) :
    𝔗 t ht :=
  (idealRid 𝔅 (isIdempotentElem_op_mk_e (Q := Q) (Λ := Λ) (ν := ν) ht)).symm
    ⟨RectBimod.mk y.1 (mem_idemSubspace_of_violCorner hρ hQ σ ht y).1,
      (mem_idemSubspace_of_violCorner hρ hQ σ ht y).2⟩

/-- `e(t) T^λ ⊗ B → e(t) V e_{σλ}`, `a ⊗ b ↦ a b`. -/
def braidToCut {t : Seq μ} (ht : IsRedOrdered t) (x : 𝔗 t ht) :
    violCorner k Q Λ ν t ((List.finRange ℓ).map σ) :=
  ⟨RectBimod.val _ _ (idealRid 𝔅 (isIdempotentElem_op_mk_e (Q := Q) (Λ := Λ) (ν := ν) ht) x : 𝔐),
    mem_violCorner_of_idemSubspace hρ hQ σ ht _⟩

theorem braidToCut_cutToBraid {t : Seq μ} (ht : IsRedOrdered t)
    (y : violCorner k Q Λ ν t ((List.finRange ℓ).map σ)) :
    braidToCut hρ hQ σ ht (cutToBraid hρ hQ σ ht y) = y := by
  apply Subtype.ext
  change RectBimod.val _ _ ((idealRid 𝔅 _ ((idealRid 𝔅 _).symm _) :
    idemSubspace k 𝔐 _) : 𝔐) = y.1
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem cutToBraid_braidToCut {t : Seq μ} (ht : IsRedOrdered t) (x : 𝔗 t ht) :
    cutToBraid hρ hQ σ ht (braidToCut hρ hQ σ ht x) = x := by
  change (idealRid 𝔅 _).symm _ = x
  rw [LinearEquiv.symm_apply_eq]
  rfl

theorem braidToCut_add {t : Seq μ} (ht : IsRedOrdered t) (x x' : 𝔗 t ht) :
    braidToCut hρ hQ σ ht (x + x') = braidToCut hρ hQ σ ht x + braidToCut hρ hQ σ ht x' := by
  apply Subtype.ext
  change RectBimod.val _ _ ((idealRid 𝔅 _ (x + x') : idemSubspace k 𝔐 _) : 𝔐) = _
  rw [map_add]
  rfl

theorem cutToBraid_smul {t : Seq μ} (ht : IsRedOrdered t) (c : (C ((List.finRange ℓ).map σ))ᵐᵒᵖ)
    (y : violCorner k Q Λ ν t ((List.finRange ℓ).map σ)) :
    cutToBraid hρ hQ σ ht (c • y) = (cornerOpRingHom (Λ := Λ ∘ σ) hρ hQ
      (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ ord c)) • cutToBraid hρ hQ σ ht y := by
  rw [cutToBraid, cutToBraid, idealRid_symm_apply, idealRid_symm_apply, smul_tmul']
  congr 1
  apply RectBimod.ext
  rw [RectBimod.val_smul_right]
  change (c • y).1 = y.1 * _
  rw [violCorner_smul_val, permCornerMap_apply, identityCornerMap_apply]
  congr 1
  rw [cornerRelabelOp_val σ ord c, show ∀ x, (cornerOpRingHom (Λ := Λ ∘ σ) hρ hQ x).unop =
    violCornerEquiv hρ hQ x.unop from fun _ => rfl, RingEquiv.symm_apply_apply]

variable [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
  [Module.Finite k (TensorProductAlgebra k Q (Λ ∘ σ) ν)]

/-- The braid `𝔅_σ (e(t) T^λ)`, restricted to the corner at the identity red order of `λ ∘ σ`. -/
abbrev braidRightSequenceCut (t : Seq μ) (ht : IsRedOrdered t) : Type :=
  CornerRes (rouquierGrading Q hR (Λ ∘ σ)) hρ hQ
    (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR
      (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin)

/-- **The braid of a sequence projective is a cut** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11): `𝔅_σ (e(t) T^λ) = e(t) T^λ ⊗ B ≅ e(t) V e_{σλ}` for a loading `t` of the identity
red order, as right modules over the corner at `σλ` (through the relabelling of the corners). -/
def braidRightSequenceCutEquiv (t : Seq μ) (ht : IsRedOrdered t) :
    (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ ord :
        (C ((List.finRange ℓ).map σ))ᵐᵒᵖ →+* (C' ord)ᵐᵒᵖ)).obj
      (ModuleCat.of (C' ord)ᵐᵒᵖ (braidRightSequenceCut (Λ := Λ) (ν := ν) hρ hQ hR σ t ht))
      ≃ₗ[(C ((List.finRange ℓ).map σ))ᵐᵒᵖ]
      ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (violCorner k Q Λ ν t ((List.finRange ℓ).map σ)) where
  toFun x := braidToCut hρ hQ σ ht x
  invFun y := cutToBraid hρ hQ σ ht y
  left_inv x := cutToBraid_braidToCut hρ hQ σ ht x
  right_inv y := braidToCut_cutToBraid hρ hQ σ ht y
  map_add' x x' := braidToCut_add hρ hQ σ ht x x'
  map_smul' c x := by
    rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def, CornerRes.smul_def]
    conv_lhs => rw [← cutToBraid_braidToCut hρ hQ σ ht x]
    erw [← cutToBraid_smul, braidToCut_cutToBraid]

/-- **Standard filtrations of braided sequence projectives are filtrations of cuts** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11): if `𝔅_σ (e(t) T^λ)` has a standard filtration, the cut
`e(t) V e_{σλ}` has a filtration by the loading standards of red order `σλ`. -/
theorem exists_hasFiltration_violCorner_of_braidFunctor (t : Seq μ) (ht : IsRedOrdered t)
    (h : HasCornerStandardFiltration (Λ ∘ σ) ν hρ hQ hR
      (braidFunctor (Λ := Λ) (ν := ν) hρ hQ σ hR
        (rightSequenceProj (rouquierGrading Q hR Λ) t ht).toGFin)) :
    ∃ m : List {s : Seq μ // redWord s = (List.finRange ℓ).map σ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 ((List.finRange ℓ).map σ))) m
        (ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
          (violCorner k Q Λ ν t ((List.finRange ℓ).map σ))) :=
  exists_hasFiltration_of_cornerRelabel σ (braidRightSequenceCutEquiv hρ hQ hR σ t ht) h

end Categorification.Stendhal.BraidedStendhalAlgebra
