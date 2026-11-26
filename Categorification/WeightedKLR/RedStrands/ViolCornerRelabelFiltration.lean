/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightStandardRelabel
import Categorification.WeightedKLR.RedStrands.BraidedRelabel

/-!
# Relabelling standard filtrations of cuts

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. Relabelling the red strands along `σ` (`λ'_r = λ_{σ r}`) identifies the cut
`e(t) V^{λ ∘ σ} e_κ` with `e(σ t) V^λ e_{σ κ}`, intertwining the right actions of the corners
through `violCornerRedPermEquiv`, and carries loading standards to loading standards
(`loadingStandardRelabel`). So a filtration of a cut by loading standards relabels to one of the
relabelled cut (`exists_hasFiltration_violCorner_relabel`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (σ : Perm (Fin ℓ))

local notation "μ" => stendhalWeight ℓ ν
local notation "f" => violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ
  (fun _ => rfl)
local notation "C'" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- Relabelling the corners, on opposite rings: `(e_{σκ} V e_{σκ})ᵒᵖ → (e_κ V^{λ∘σ} e_κ)ᵒᵖ`. -/
def cornerRelabelOp (κ : List (Fin ℓ)) : (C (κ.map σ))ᵐᵒᵖ ≃+* (C' κ)ᵐᵒᵖ :=
  (violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ (fun _ => rfl)
    κ).symm.op

theorem cornerRelabelOp_val (κ : List (Fin ℓ)) (c : (C (κ.map σ))ᵐᵒᵖ) :
    c.unop.1 = f (cornerRelabelOp σ κ c).unop.1 :=
  (congrArg Subtype.val ((violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ)
    (ν := ν) σ (fun _ => rfl) κ).apply_symm_apply c.unop)).symm

/-- `violCornerRelabel` as a linear equivalence over the relabelled corner. -/
def violCornerRelabelEquiv (t : Seq μ) (κ : List (Fin ℓ)) :
    (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
        (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).obj
      (ModuleCat.of (C' κ)ᵐᵒᵖ (violCorner k Q (Λ ∘ σ) ν t κ)) ≃ₗ[(C (κ.map σ))ᵐᵒᵖ]
      ModuleCat.of (C (κ.map σ))ᵐᵒᵖ (violCorner k Q Λ ν (Seq.redPerm σ t) (κ.map σ)) where
  toFun y := violCornerRelabel σ t κ y
  invFun y := (violCornerRelabel σ t κ).symm y
  left_inv y := (violCornerRelabel σ t κ).symm_apply_apply y
  right_inv y := (violCornerRelabel σ t κ).apply_symm_apply y
  map_add' y z := map_add (violCornerRelabel σ t κ) y z
  map_smul' c y := by
    apply Subtype.ext
    change f ((cornerRelabelOp σ κ c • (show violCorner k Q (Λ ∘ σ) ν t κ from y)).1) =
      (violCornerRelabel σ t κ y).1 * c.unop.1
    rw [violCorner_smul_val, map_mul, ← cornerRelabelOp_val]
    rfl

/-- `loadingStandardRelabel` as a linear equivalence over the relabelled corner. -/
def loadingStandardRelabelEquiv {s : Seq μ} {κ : List (Fin ℓ)} (hκ : redWord s = κ) :
    (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
        (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).obj
      (ModuleCat.of (C' κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ))
      ≃ₗ[(C (κ.map σ))ᵐᵒᵖ]
      ModuleCat.of (C (κ.map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) (κ.map σ)) where
  toFun y := loadingStandardRelabel σ hκ y
  invFun y := (loadingStandardRelabel σ hκ).symm y
  left_inv y := (loadingStandardRelabel σ hκ).symm_apply_apply y
  right_inv y := (loadingStandardRelabel σ hκ).apply_symm_apply y
  map_add' y z := map_add (loadingStandardRelabel σ hκ) y z
  map_smul' c y :=
    loadingStandardRelabel_smul σ hκ (cornerRelabelOp σ κ c) c (cornerRelabelOp_val σ κ c) y

/-- **Relabelling a standard filtration** along a relabelling equivalence: if `Y` is the
restriction of `X` along `cornerRelabelOp σ κ` and `X` is filtered by the loading standards of
`V^{λ ∘ σ}` at `κ`, then `Y` is filtered by the loading standards of `V^λ` at `σ κ`. -/
theorem exists_hasFiltration_of_cornerRelabel {κ : List (Fin ℓ)} {X : ModuleCat.{0} (C' κ)ᵐᵒᵖ}
    {Y : ModuleCat.{0} (C (κ.map σ))ᵐᵒᵖ}
    (e : (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
        (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).obj X ≃ₗ[(C (κ.map σ))ᵐᵒᵖ] Y)
    (h : ∃ m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C' κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s.1 κ)) m X) :
    ∃ m : List {s : Seq μ // redWord s = κ.map σ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C (κ.map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 (κ.map σ))) m Y := by
  obtain ⟨m, hm⟩ := h
  let g : {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s} →
      {s : Seq μ // redWord s = κ.map σ ∧ ¬ IsViolated s} := fun s =>
    ⟨Seq.redPerm σ s.1, by rw [redWord_redPerm, s.2.1], by
      rw [isViolated_redPerm]; exact s.2.2⟩
  have h1 := (hm.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
    (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).of_equiv e
  refine ⟨m.flatMap fun s => [g s], h1.bind fun s => HasFiltration.single ?_⟩
  exact loadingStandardRelabelEquiv σ s.2.1

/-- **Relabelling a standard filtration of a cut** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11): a filtration of `e(t) V^{λ ∘ σ} e_κ` by loading standards relabels to one of
`e(σ t) V^λ e_{σ κ}`. -/
theorem exists_hasFiltration_violCorner_relabel {t : Seq μ} {κ : List (Fin ℓ)}
    (h : ∃ m : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C' κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s.1 κ)) m
        (ModuleCat.of (C' κ)ᵐᵒᵖ (violCorner k Q (Λ ∘ σ) ν t κ))) :
    ∃ m : List {s : Seq μ // redWord s = κ.map σ ∧ ¬ IsViolated s},
      HasFiltration (fun s => ModuleCat.of (C (κ.map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 (κ.map σ))) m
        (ModuleCat.of (C (κ.map σ))ᵐᵒᵖ (violCorner k Q Λ ν (Seq.redPerm σ t) (κ.map σ))) :=
  exists_hasFiltration_of_cornerRelabel σ (violCornerRelabelEquiv σ t κ) h

end Categorification.Stendhal.BraidedStendhalAlgebra
