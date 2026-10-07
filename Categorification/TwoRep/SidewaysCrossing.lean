/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclicCross

/-!
# The sideways crossings (CL (4.16))

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, end of §4.2, eq. (4.16): after Lemma 4.2 the two sideways crossings (defined up
to a scalar by Lemma 3.12) are fixed as the upward crossing with one strand bent:

* `E F 1_n → F E 1_n`: the upward crossing with a cup `1 → F E` on the bottom left and a cap
  `E F → 1` on the top right, i.e. the **mate of the crossing under the right adjunctions**
  `E 1_m ⊣ R_m` (Rouquier's and Brundan's `σ`; `StrongSl2.grSigma`);
* `F E 1_n → E F 1_n`: the upward crossing with a cup `1 → E F` on the bottom right and a cap
  `F E → 1` on the top left, i.e. the **mate of the crossing under the left adjunctions**
  `R_m ⊣ E 1_m` (`StrongSl2.sideL`).

In the graded-Hom bicategory, with `E 1_n = grE r`, `R_n = grR r` (`n = wt r`), the two sideways
crossings at the object `r + 1` (weight `n + 2`) are 2-morphisms
`σ : R_r E_r ⟶ E_{r+1} R_{r+1}` (degree `-2`) and `σ' : E_{r+1} R_{r+1} ⟶ R_r E_r` (degree `2`);
in Mathlib's diagrammatic order `R_r ≫ E_r` is CL's `E F 1_{n+2}`.

Both are instances of Mathlib's `Bicategory.mateEquiv`:
`grSigma r = mateEquiv (grAdj r) (grAdj (r+1)) τ` (`StrongSl2.grSigma_eq_mateEquiv`) and
`sideL A₁ A₂ = (mateEquiv A₁ A₂).symm τ` by definition. Under (BB_w) we use the normalized left
adjunctions `BBw.leftAdjN` of CL §4.1 (`StrongSl2.BBw.sideL`).

## Main declarations

* generic: `RightwardCrossing.sigma_eq_mateEquiv`, `mateEquiv_symm_eq_comp`;
  `GradedHomBicat.isHomogeneous_mateEquiv_symm`, `GradedHomBicat.isHomogeneous_mateEquiv`;
* `StrongSl2.grSigma_eq_mateEquiv`, `StrongSl2.sideL`, `StrongSl2.isHomogeneous_sideL`;
* `StrongSl2.BBw.sideL`: CL's leftward sideways crossing (4.16), of degree `2`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Generic

variable {C : Type u} [Bicategory.{w, v} C]

/-- The rightward crossing `σ` is the mate of the crossing under the right adjunctions. -/
theorem RightwardCrossing.sigma_eq_mateEquiv {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c}
    {R₁ : b ⟶ a} {R₂ : c ⟶ b} (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    RightwardCrossing.sigma adj₂.unit τ adj₁.counit = mateEquiv adj₁ adj₂ τ := by
  rw [RightwardCrossing.sigma_def, mateEquiv_apply']
  bicategory

/-- The inverse mate with all associators and unitors written out. -/
theorem mateEquiv_symm_eq_comp {c d e f : C} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d}
    {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    (β : r₁ ≫ g ⟶ h ≫ r₂) :
    (mateEquiv adj₁ adj₂).symm β = (λ_ (g ≫ l₂)).inv ≫ adj₁.unit ▷ (g ≫ l₂) ≫
      (α_ l₁ r₁ (g ≫ l₂)).hom ≫ l₁ ◁ (α_ r₁ g l₂).inv ≫ l₁ ◁ β ▷ l₂ ≫
      l₁ ◁ (α_ h r₂ l₂).hom ≫ l₁ ◁ h ◁ adj₂.counit ≫ l₁ ◁ (ρ_ h).hom := by
  rw [mateEquiv_symm_apply']
  bicategory

/-- The mate with all associators and unitors written out. -/
theorem mateEquiv_eq_comp {c d e f : C} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d}
    {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ α = (ρ_ (r₁ ≫ g)).inv ≫ (r₁ ≫ g) ◁ adj₂.unit ≫
      (α_ r₁ g (l₂ ≫ r₂)).hom ≫ r₁ ◁ (α_ g l₂ r₂).inv ≫ r₁ ◁ α ▷ r₂ ≫
      r₁ ◁ (α_ l₁ h r₂).hom ≫ (α_ r₁ l₁ (h ≫ r₂)).inv ≫ adj₁.counit ▷ (h ≫ r₂) ≫
      (λ_ (h ≫ r₂)).hom := by
  rw [mateEquiv_apply']
  bicategory

end Generic

section GradedHom

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

namespace GradedHomBicat

open GradedHomCat

/-- **The inverse mate preserves homogeneity**, adding the degrees of the unit of the first and
the counit of the second adjunction. -/
theorem isHomogeneous_mateEquiv_symm {c d e f : GradedHomBicat B} {g : c ⟶ e} {h : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    {u v : ℤ} (hu : IsHomogeneous adj₁.unit u) (hv : IsHomogeneous adj₂.counit v)
    {β : r₁ ≫ g ⟶ h ≫ r₂} {e' : ℤ} (hβ : IsHomogeneous β e') :
    IsHomogeneous ((mateEquiv adj₁ adj₂).symm β) (u + e' + v) := by
  rw [mateEquiv_symm_eq_comp]
  exact ((isHomogeneous_leftUnitor_inv _).comp ((isHomogeneous_whiskerRight hu _).comp
    ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _
      (isHomogeneous_associator_inv _ _ _)).comp ((isHomogeneous_whiskerLeft _
        (isHomogeneous_whiskerRight hβ _)).comp ((isHomogeneous_whiskerLeft _
          (isHomogeneous_associator_hom _ _ _)).comp ((isHomogeneous_whiskerLeft _
            (isHomogeneous_whiskerLeft _ hv)).comp (isHomogeneous_whiskerLeft _
              (isHomogeneous_rightUnitor_hom _)) rfl) rfl) rfl) rfl) rfl) rfl) rfl).of_eq
    (by ring)

/-- **The mate preserves homogeneity**, adding the degrees of the unit of the second and the
counit of the first adjunction. -/
theorem isHomogeneous_mateEquiv {c d e f : GradedHomBicat B} {g : c ⟶ e} {h : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    {u v : ℤ} (hu : IsHomogeneous adj₂.unit u) (hv : IsHomogeneous adj₁.counit v)
    {α : g ≫ l₂ ⟶ l₁ ≫ h} {e' : ℤ} (hα : IsHomogeneous α e') :
    IsHomogeneous (mateEquiv adj₁ adj₂ α) (u + e' + v) := by
  rw [mateEquiv_eq_comp]
  exact ((isHomogeneous_rightUnitor_inv _).comp ((isHomogeneous_whiskerLeft _ hu).comp
    ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _
      (isHomogeneous_associator_inv _ _ _)).comp ((isHomogeneous_whiskerLeft _
        (isHomogeneous_whiskerRight hα _)).comp ((isHomogeneous_whiskerLeft _
          (isHomogeneous_associator_hom _ _ _)).comp ((isHomogeneous_associator_inv _ _ _).comp
            ((isHomogeneous_whiskerRight hv _).comp (isHomogeneous_leftUnitor_hom _) rfl) rfl)
              rfl) rfl) rfl) rfl) rfl) rfl).of_eq (by ring)

end GradedHomBicat

end GradedHom

/-! ## The sideways crossings of a strong 2-representation of `sl₂` -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat

variable (S : StrongSl2 k B)

/-- **CL (4.16), rightward sideways crossing**: `σ = grSigma r` is the mate of the crossing under
the right adjunctions `E 1_m ⊣ R_m`. -/
theorem grSigma_eq_mateEquiv (r : ℤ) :
    S.grSigma r = mateEquiv (S.grAdj r) (S.grAdj (r + 1)) (S.grCross r) :=
  RightwardCrossing.sigma_eq_mateEquiv (S.grAdj r) (S.grAdj (r + 1)) (S.grCross r)

/-- **CL (4.16), leftward sideways crossing** `F E 1_{n+2} → E F 1_{n+2}` (`n = wt r`): the mate
of the crossing on `E E 1_n` under left adjunctions `R_n ⊣ E 1_n`, `R_{n+2} ⊣ E 1_{n+2}`. -/
def sideL {r : ℤ} (A₁ : S.grR r ⊣ S.grE r) (A₂ : S.grR (r + 1) ⊣ S.grE (r + 1)) :
    S.grE (r + 1) ≫ S.grR (r + 1) ⟶ S.grR r ≫ S.grE r :=
  (mateEquiv A₁ A₂).symm (S.grCross r)

/-- The leftward sideways crossing is homogeneous of degree `2`, for left adjunctions with
homogeneous units and counits of the degrees of `BBw.leftAdjN`. -/
theorem isHomogeneous_sideL {r : ℤ} (A₁ : S.grR r ⊣ S.grE r)
    (A₂ : S.grR (r + 1) ⊣ S.grE (r + 1)) (hu : IsHomogeneous A₁.unit (-(2 * S.wt r + 2)))
    (hc : IsHomogeneous A₂.counit (2 * S.wt (r + 1) + 2)) :
    IsHomogeneous (S.sideL A₁ A₂) 2 :=
  (isHomogeneous_mateEquiv_symm A₁ A₂ hu hc (isHomogeneous_of₂ _ _)).of_eq
    (by rw [S.wt_add_one]; ring)

variable {S} [GradedBicategory.IsLinear B k] [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)]

/-- **CL's leftward sideways crossing (4.16)** under (BB_w), for the normalized left adjunctions
`BBw.leftAdjN` of CL §4.1. -/
def BBw.sideL [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) (r : ℤ) :
    S.grE (r + 1) ≫ S.grR (r + 1) ⟶ S.grR r ≫ S.grE r :=
  S.sideL (hS.leftAdjN r) (hS.leftAdjN (r + 1))

theorem BBw.isHomogeneous_sideL [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw)
    (r : ℤ) : IsHomogeneous (hS.sideL r) 2 :=
  S.isHomogeneous_sideL _ _ (hS.leftAdjN_spec r).1 (hS.leftAdjN_spec (r + 1)).2.1

end StrongSl2

end Categorification.TwoRep
