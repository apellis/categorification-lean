/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongKLR

/-!
# Cyclicity of crossings (right rotation) in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, `eq_almost_cyclic` (KL III `eq_cyclic_cross-gen`, left-hand picture): in the
model of `Categorification.TwoRep.ModelQStrong`, the upward crossing `E_j E_i ⟶ E_i E_j` rotated by
nested cups on the right and nested caps on the left is `t_{ij}` times the downward crossing, for
all labels `i`, `j` (`QStrong.cycCrossR_gen`: the relation `cycCrossR j i μ` of `presCL`,
`CL.relationCL`, for the scalars `Sc` of the model, read with its own outer regions). The downward crossing of the
model is defined as `t_{ij}⁻¹` times the mate of the upward one (`QStrong.crossDnQ`), so this is
the identification of the rotated diagram with the mate.

## Main results

* `rot2G_aux`, `rot2G_key`: the rotation of a 2-morphism between two different pairs of strands
  by nested cups and caps is its mate under the composite adjunctions (compare `rot2_key`, the
  case of an endomorphism);
* `QStrong.cycCrossR_gen`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u u₁

/-! ## Rotation of a 2-morphism between different pairs of strands -/

section Rot

open StringDiagrams Diagrams.BicatInterp

theorem rot2G_aux {C : Type*} [Bicategory C] {a b b' c : C} {r₁ : a ⟶ b} {e₁ : b ⟶ a}
    {r₂ : b ⟶ c} {e₂ : c ⟶ b} {s₁ : a ⟶ b'} {f₁ : b' ⟶ a} {s₂ : b' ⟶ c} {f₂ : c ⟶ b'}
    (adjB₁ : r₁ ⊣ e₁) (adjB₂ : r₂ ⊣ e₂) (adjT₁ : s₁ ⊣ f₁) (adjT₂ : s₂ ⊣ f₂)
    (x : f₂ ≫ f₁ ⟶ e₂ ≫ e₁) :
    𝟙 a ◁ (adjT₁.unit ▷ (r₁ ≫ r₂)) ≫
        ((λ_ _).hom ≫ (α_ s₁ f₁ (r₁ ≫ r₂)).hom ≫ s₁ ◁ (λ_ (f₁ ≫ (r₁ ≫ r₂))).inv) ≫
        s₁ ◁ (adjT₂.unit ▷ (f₁ ≫ (r₁ ≫ r₂))) ≫
        (s₁ ◁ (α_ s₂ f₂ (f₁ ≫ (r₁ ≫ r₂))).hom ≫ (α_ s₁ s₂ (f₂ ≫ (f₁ ≫ (r₁ ≫ r₂)))).inv ≫
          (s₁ ≫ s₂) ◁ (α_ f₂ f₁ (r₁ ≫ r₂)).inv) ≫
        (s₁ ≫ s₂) ◁ (x ▷ (r₁ ≫ r₂)) ≫
        ((s₁ ≫ s₂) ◁ (α_ e₂ e₁ (r₁ ≫ r₂)).hom ≫ (α_ (s₁ ≫ s₂) e₂ (e₁ ≫ (r₁ ≫ r₂))).inv ≫
          ((s₁ ≫ s₂) ≫ e₂) ◁ (α_ e₁ r₁ r₂).inv) ≫
        ((s₁ ≫ s₂) ≫ e₂) ◁ (adjB₁.counit ▷ r₂) ≫
        (((s₁ ≫ s₂) ≫ e₂) ◁ (λ_ r₂).hom ≫ (α_ (s₁ ≫ s₂) e₂ r₂).hom ≫
          (s₁ ≫ s₂) ◁ (ρ_ (e₂ ≫ r₂)).inv) ≫
        (s₁ ≫ s₂) ◁ (adjB₂.counit ▷ 𝟙 c) =
      𝟙 a ◁ ((λ_ (r₁ ≫ r₂)).hom ≫ (ρ_ (r₁ ≫ r₂)).inv) ≫
        𝟙 a ◁ ((Bicategory.conjugateEquiv (adjT₁.comp adjT₂) (adjB₁.comp adjB₂)).symm x ▷ 𝟙 c) ≫
          ((λ_ _).hom ≫ (s₁ ≫ s₂) ◁ (λ_ (𝟙 c)).inv) := by
  rw [Bicategory.conjugateEquiv_symm_apply']
  simp only [Bicategory.Adjunction.comp_unit, Bicategory.Adjunction.comp_counit,
    Bicategory.Adjunction.compUnit, Bicategory.Adjunction.compCounit]
  bicategory

variable {S : Signature} {D : Type*} [Bicategory D] (M : Model S D)

/-- **The rotation of a generator on two strands in normal form** (compare `rot2_key`), for a
2-morphism `x` between different pairs of strands: nested cups on the right (units of the
adjunctions `adjT₁`, `adjT₂` of the new strands), `x`, nested caps on the left (counits of the
adjunctions `adjB₁`, `adjB₂` of the old strands), all conjugated by images of free 2-morphisms,
equal the left mate of `x`. -/
theorem rot2G_key {a b b' c : FB S} {r₁ : a ⟶ b} {e₁ : b ⟶ a} {r₂ : b ⟶ c} {e₂ : c ⟶ b}
    {s₁ : a ⟶ b'} {f₁ : b' ⟶ a} {s₂ : b' ⟶ c} {f₂ : c ⟶ b'}
    (adjB₁ : M.lift.map r₁ ⊣ M.lift.map e₁) (adjB₂ : M.lift.map r₂ ⊣ M.lift.map e₂)
    (adjT₁ : M.lift.map s₁ ⊣ M.lift.map f₁) (adjT₂ : M.lift.map s₂ ⊣ M.lift.map f₂)
    (x : M.lift.map f₂ ≫ M.lift.map f₁ ⟶ M.lift.map e₂ ≫ M.lift.map e₁)
    {p₁ d₁ c₁ : a ⟶ a} {q₁ : a ⟶ c} (σp₁ : p₁ ≅ 𝟙 a) (σq₁ : q₁ ≅ r₁ ≫ r₂) (σd₁ : d₁ ≅ 𝟙 a)
    (σc₁ : c₁ ≅ s₁ ≫ f₁) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adjT₁.unit)
    {p₂ : a ⟶ b'} {q₂ : b' ⟶ c} {d₂ c₂ : b' ⟶ b'} (σp₂ : p₂ ≅ s₁) (σq₂ : q₂ ≅ f₁ ≫ (r₁ ≫ r₂))
    (σd₂ : d₂ ≅ 𝟙 b') (σc₂ : c₂ ≅ s₂ ≫ f₂) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = adjT₂.unit)
    {p₃ q₃ : a ⟶ c} {d₃ c₃ : c ⟶ a} (σp₃ : p₃ ≅ s₁ ≫ s₂) (σq₃ : q₃ ≅ r₁ ≫ r₂)
    (σd₃ : d₃ ≅ f₂ ≫ f₁) (σc₃ : c₃ ≅ e₂ ≫ e₁) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = x)
    {p₄ : a ⟶ b} {q₄ : b ⟶ c} {d₄ c₄ : b ⟶ b} (σp₄ : p₄ ≅ (s₁ ≫ s₂) ≫ e₂) (σq₄ : q₄ ≅ r₂)
    (σd₄ : d₄ ≅ e₁ ≫ r₁) (σc₄ : c₄ ≅ 𝟙 b) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hg₄ : M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom = adjB₁.counit)
    {p₅ : a ⟶ c} {q₅ d₅ c₅ : c ⟶ c} (σp₅ : p₅ ≅ s₁ ≫ s₂) (σq₅ : q₅ ≅ 𝟙 c)
    (σd₅ : d₅ ≅ e₂ ≫ r₂) (σc₅ : c₅ ≅ 𝟙 c) (g₅ : M.lift.map d₅ ⟶ M.lift.map c₅)
    (hg₅ : M.lift.map₂ σd₅.inv ≫ g₅ ≫ M.lift.map₂ σc₅.hom = adjB₂.counit)
    {p₆ : a ⟶ a} {q₆ : c ⟶ c} {d₆ c₆ : a ⟶ c} (σp₆ : p₆ ≅ 𝟙 a) (σq₆ : q₆ ≅ 𝟙 c)
    (σd₆ : d₆ ≅ r₁ ≫ r₂) (σc₆ : c₆ ≅ s₁ ≫ s₂) (g₆ : M.lift.map d₆ ⟶ M.lift.map c₆)
    (hg₆ : M.lift.map₂ σd₆.inv ≫ g₆ ≫ M.lift.map₂ σc₆.hom =
      (Bicategory.conjugateEquiv (adjT₁.comp adjT₂) (adjB₁.comp adjB₂)).symm x)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ P₅ Q₅ Q P₆ Q₆ : a ⟶ c}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₄ : Q₄ ⟶ P₅)
    (A₅ : P₅ ⟶ p₅ ≫ (d₅ ≫ q₅)) (B₅ : p₅ ≫ (c₅ ≫ q₅) ⟶ Q₅) (E₅ : Q₅ ⟶ Q)
    (F₀ : P ⟶ P₆) (A₆ : P₆ ⟶ p₆ ≫ (d₆ ≫ q₆)) (B₆ : p₆ ≫ (c₆ ≫ q₆) ⟶ Q₆) (F₁ : Q₆ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ ≫
            (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₄ ≫
              (M.lift.map₂ A₅ ≫ midK M p₅ q₅ g₅ ≫ M.lift.map₂ B₅) ≫ M.lift.map₂ E₅ =
      M.lift.map₂ F₀ ≫ (M.lift.map₂ A₆ ≫ midK M p₆ q₆ g₆ ≫ M.lift.map₂ B₆) ≫
        M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃, midK_canon M σp₄ σq₄ σd₄ σc₄ g₄, hg₄,
    midK_canon M σp₅ σq₅ σd₅ σc₅ g₅, hg₅, midK_canon M σp₆ σq₆ σd₆ σc₆ g₆, hg₆]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (𝟙 a) (r₁ ≫ r₂) (x := 𝟙 a) (y := s₁ ≫ f₁) adjT₁.unit ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ s₁ f₁ (r₁ ≫ r₂)).hom ≫ s₁ ◁ (λ_ (f₁ ≫ (r₁ ≫ r₂))).inv) ≫
      midK M s₁ (f₁ ≫ (r₁ ≫ r₂)) (x := 𝟙 b') (y := s₂ ≫ f₂) adjT₂.unit ≫
      M.lift.map₂ (s₁ ◁ (α_ s₂ f₂ (f₁ ≫ (r₁ ≫ r₂))).hom ≫
        (α_ s₁ s₂ (f₂ ≫ (f₁ ≫ (r₁ ≫ r₂)))).inv ≫ (s₁ ≫ s₂) ◁ (α_ f₂ f₁ (r₁ ≫ r₂)).inv) ≫
      midK M (s₁ ≫ s₂) (r₁ ≫ r₂) (x := f₂ ≫ f₁) (y := e₂ ≫ e₁) x ≫
      M.lift.map₂ ((s₁ ≫ s₂) ◁ (α_ e₂ e₁ (r₁ ≫ r₂)).hom ≫
        (α_ (s₁ ≫ s₂) e₂ (e₁ ≫ (r₁ ≫ r₂))).inv ≫ ((s₁ ≫ s₂) ≫ e₂) ◁ (α_ e₁ r₁ r₂).inv) ≫
      midK M ((s₁ ≫ s₂) ≫ e₂) r₂ (x := e₁ ≫ r₁) (y := 𝟙 b) adjB₁.counit ≫
      M.lift.map₂ (((s₁ ≫ s₂) ≫ e₂) ◁ (λ_ r₂).hom ≫ (α_ (s₁ ≫ s₂) e₂ r₂).hom ≫
        (s₁ ≫ s₂) ◁ (ρ_ (e₂ ≫ r₂)).inv) ≫
      midK M (s₁ ≫ s₂) (𝟙 c) (x := e₂ ≫ r₂) (y := 𝟙 c) adjB₂.counit =
      M.lift.map₂ (𝟙 a ◁ ((λ_ (r₁ ≫ r₂)).hom ≫ (ρ_ (r₁ ≫ r₂)).inv)) ≫
        midK M (𝟙 a) (𝟙 c) (x := r₁ ≫ r₂) (y := s₁ ≫ s₂)
          ((Bicategory.conjugateEquiv (adjT₁.comp adjT₂) (adjB₁.comp adjB₂)).symm x) ≫
          M.lift.map₂ ((λ_ _).hom ≫ (s₁ ≫ s₂) ◁ (λ_ (𝟙 c)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      lift_map₂_rightUnitor_inv, lift_map_comp]
    exact rot2G_aux adjB₁ adjB₂ adjT₁ adjT₂ x
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ s₁ f₁ (r₁ ≫ r₂)).hom ≫
      s₁ ◁ (λ_ (f₁ ≫ (r₁ ≫ r₂))).inv),
    lift_map₂_eq M _ (s₁ ◁ (α_ s₂ f₂ (f₁ ≫ (r₁ ≫ r₂))).hom ≫
      (α_ s₁ s₂ (f₂ ≫ (f₁ ≫ (r₁ ≫ r₂)))).inv ≫ (s₁ ≫ s₂) ◁ (α_ f₂ f₁ (r₁ ≫ r₂)).inv),
    lift_map₂_eq M _ ((s₁ ≫ s₂) ◁ (α_ e₂ e₁ (r₁ ≫ r₂)).hom ≫
      (α_ (s₁ ≫ s₂) e₂ (e₁ ≫ (r₁ ≫ r₂))).inv ≫ ((s₁ ≫ s₂) ≫ e₂) ◁ (α_ e₁ r₁ r₂).inv),
    lift_map₂_eq M _ (((s₁ ≫ s₂) ≫ e₂) ◁ (λ_ r₂).hom ≫ (α_ (s₁ ≫ s₂) e₂ r₂).hom ≫
      (s₁ ≫ s₂) ◁ (ρ_ (e₂ ≫ r₂)).inv), reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

end Rot

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, Limits.HasZeroObject (a ⟶ b)] [∀ a b : B, Limits.HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable {S : QStrong B C RD k Q} (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

theorem dual_up_g (i : I) : Letter.dual (up i) = dn i := rfl

theorem condDn2 (j i : I) (μ : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ (ob RD μ [dn j, dn i]) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩

theorem sh_ud (i : I) (r : X) :
    sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + r) = r := by
  rw [sh_up, sh_dn]; abel

theorem sh_ud' (i j : I) (r : X) :
    sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + r)) =
      sh RD ((false, j) : Letter I) + r := by
  rw [sh_up, sh_dn, sh_dn]; abel

theorem sh_dd (i j : I) (r : X) :
    sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + r) =
      sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + r) :=
  add_left_comm _ _ _

theorem midK_smul {S' : Signature} (M : Model S' (GradedHomBicat B)) {a b c d : FB S'}
    (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c} (t : k) (g : M.lift.map x ⟶ M.lift.map y) :
    midK M p q (t • g) = t • midK M p q g := by
  rw [midK, midK, GradedHomBicat.smul_whiskerRight]
  exact GradedHomBicat.whiskerLeft_smul _ _ _

theorem crossQ_congr (j i : I) {l n n' m n₂ n₂' : X} (hn : n = n₂) (hn' : n' = n₂')
    (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX j = m) (h₃ : l + RD.iX j = n') (h₄ : n' + RD.iX i = m)
    (h₁' : l + RD.iX i = n₂) (h₂' : n₂ + RD.iX j = m) (h₃' : l + RD.iX j = n₂')
    (h₄' : n₂' + RD.iX i = m)
    (e₁ : S.Eg i h₁' ≫ S.Eg j h₂' = S.Eg i h₁ ≫ S.Eg j h₂)
    (e₂ : S.Eg j h₃ ≫ S.Eg i h₄ = S.Eg j h₃' ≫ S.Eg i h₄') :
    eqToHom e₁ ≫ S.crossQ j i h₁ h₂ h₃ h₄ ≫ eqToHom e₂ = S.crossQ j i h₁' h₂' h₃' h₄' := by
  subst hn hn'
  simp

theorem adjL_counit_congr (i : I) {x y y' : X} (hy : y = y') (h : x + RD.iX i = y)
    (h' : x + RD.iX i = y') (e : S.Eg i h' ≫ S.Rg i h' = S.Eg i h ≫ S.Rg i h) :
    eqToHom e ≫ (adjL (S := S) i h).counit = (adjL (S := S) i h').counit := by
  subst hy
  simp

set_option maxHeartbeats 20000000 in
/-- **`Q`-cyclicity of mixed crossings, right rotation** (CL `eq_almost_cyclic`, KL III
`eq_cyclic_cross-gen`, left-hand picture): the upward crossing `E_j E_i ⟶ E_i E_j` rotated by
nested cups on the right and nested caps on the left is `t_{ij}` times the downward crossing, in
the model. -/
theorem cycCrossR_gen (j i : I) (μ : X) :
    (((Sc.t i j)⁻¹ : kˣ) : k) •
        (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ).functor.map
          (rotCrossR RD j i μ) =
      (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ).functor.map
        (downCross RD j i μ) := by
  have hc : Cond (S := psig RD) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ
      (ob RD μ [dn j, dn i]) := condDn2 j i μ
  have hc' : Cond (S := psig RD) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ
      (ob RD μ [dn i, dn j]) :=
    ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc'))).1
  set_option backward.isDefEq.respectTransparency false in
  simp only [Linear.smul_comp, Linear.comp_smul]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, rotCrossR, downCross, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up_g]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize g1 : sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = y at *
  obtain rfl : y = sh RD ((false, j) : Letter I) + μ := by rw [← g1, sh_up, sh_dn]; abel
  generalize g2 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← g2, sh_up, sh_dn]; abel
  generalize g3 : sh RD ((true, i) : Letter I) + (sh RD ((true, j) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ))) = z at *
  obtain rfl : μ = z := by rw [← g3, sh_up, sh_up, sh_dn, sh_dn]; abel
  generalize g4 : sh RD ((true, j) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = w at *
  obtain rfl : w = sh RD ((false, i) : Letter I) + μ := by rw [← g4, sh_up, sh_dn, sh_dn]; abel
  generalize g5 : sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = v at *
  obtain rfl : v = sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ) := by rw [← g5]; abel
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3,
    layerI_pos _ _ _ _ ?c4, layerI_pos _ _ _ _ ?c5, layerI_pos _ _ _ _ ?c6]
  case c1 | c2 | c3 | c4 | c5 | c6 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g, inv_dual, Letter.dual, sh_up, sh_dn] <;> (repeat' constructor) <;> abel
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w3 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w4 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w5 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w6 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross_g, sig0_cod_cross_g,
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, sig0_colourTgt_g, sig0_colourSrc_g]
    set_option backward.isDefEq.respectTransparency false in
    erw [genImg_cross_false (S := S) Sc j i μ _ _ _ _ _ rfl]
    set_option backward.isDefEq.respectTransparency false in
    simp only [crossDnQ]
    set_option backward.isDefEq.respectTransparency false in
    rw [midK_smul]
    set_option backward.isDefEq.respectTransparency false in
    simp only [Linear.smul_comp, Linear.comp_smul]
    refine congrArg ((((Sc.t i j)⁻¹ : kˣ) : k) • ·) ?_
    refine rot2G_key S.model
      (r₁ := FreeBicategory.Hom.of (⟨⟨(false, i), μ⟩, rfl, rfl⟩ :
        rq (S := psig RD) μ ⟶ rq (sh RD ((false, i) : Letter I) + μ)))
      (e₁ := FreeBicategory.Hom.of (⟨⟨(true, i), sh RD ((false, i) : Letter I) + μ⟩, rfl,
          sh_ud i μ⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + μ) ⟶ rq μ))
      (r₂ := FreeBicategory.Hom.of (⟨⟨(false, j), sh RD ((false, i) : Letter I) + μ⟩, rfl, rfl⟩ :
        rq (S := psig RD) (sh RD ((false, i) : Letter I) + μ) ⟶ rq (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))))
      (e₂ := FreeBicategory.Hom.of (⟨⟨(true, j), (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))⟩, rfl,
          sh_ud j (sh RD ((false, i) : Letter I) + μ)⟩ :
        rq (S := psig RD) (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ)) ⟶ rq (sh RD ((false, i) : Letter I) + μ)))
      (s₁ := FreeBicategory.Hom.of (⟨⟨(false, j), μ⟩, rfl, rfl⟩ :
        rq (S := psig RD) μ ⟶ rq (sh RD ((false, j) : Letter I) + μ)))
      (f₁ := FreeBicategory.Hom.of (⟨⟨(true, j), sh RD ((false, j) : Letter I) + μ⟩, rfl,
          sh_ud j μ⟩ :
        rq (S := psig RD) (sh RD ((false, j) : Letter I) + μ) ⟶ rq μ))
      (s₂ := FreeBicategory.Hom.of (⟨⟨(false, i), sh RD ((false, j) : Letter I) + μ⟩, rfl,
          sh_dd i j μ⟩ :
        rq (S := psig RD) (sh RD ((false, j) : Letter I) + μ) ⟶ rq (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))))
      (f₂ := FreeBicategory.Hom.of (⟨⟨(true, i), (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))⟩, rfl,
          sh_ud' i j μ⟩ :
        rq (S := psig RD) (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ)) ⟶ rq (sh RD ((false, j) : Letter I) + μ)))
      (adjL (S := S) i (x := sh RD ((false, i) : Letter I) + μ) (y := μ) (dn_reg i rfl rfl))
      (adjL (S := S) j (x := sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))
        (y := sh RD ((false, i) : Letter I) + μ) (dn_reg j rfl rfl))
      (adjL (S := S) j (x := sh RD ((false, j) : Letter I) + μ) (y := μ) (dn_reg j rfl rfl))
      (adjL (S := S) i (x := sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))
        (y := sh RD ((false, j) : Letter I) + μ) (dn_reg i rfl (sh_dd i j μ)))
      (S.crossQ j i (by simp only [sh_dn, rq]; abel) (by simp only [sh_dn, rq]; abel)
        (by simp only [sh_dn, rq]; abel) (by simp only [sh_dn, rq]; abel))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc1)) _)
      _ ?hg1
      (Iso.refl _) (α_ _ _ _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc2)) _)
      _ ?hg2
      (Iso.refl _) (Iso.refl _) (eqToIso ?d3) (eqToIso ?c3) _ ?hg3
      (Iso.refl _) (Iso.refl _) (eqToIso ?d4) (Iso.refl _) _ ?hg4
      (Iso.refl _) (Iso.refl _) (eqToIso ?d5) (Iso.refl _) _ ?hg5
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hc1 => exact congrArg (Col.mk ((false, j) : Letter I)) (sh_ud j μ)
    case hc2 => exact congrArg (Col.mk ((false, i) : Letter I)) (sh_ud' i j μ)
    case d3 =>
      exact comp_of_congr (sh_ud' i j μ) rfl (congrArg (Col.mk ((true, j) : Letter I)) (sh_ud' i j μ))
    case c3 =>
      exact comp_of_congr (sh_ud j (sh RD ((false, i) : Letter I) + μ)) rfl
        (congrArg (Col.mk ((true, i) : Letter I)) (sh_ud j (sh RD ((false, i) : Letter I) + μ)))
    case d4 =>
      exact comp_of_congr (sh_ud i μ) rfl (congrArg (Col.mk ((false, i) : Letter I)) (sh_ud i μ))
    case d5 =>
      exact comp_of_congr (sh_ud j (sh RD ((false, i) : Letter I) + μ)) rfl
        (congrArg (Col.mk ((false, j) : Letter I)) (sh_ud j (sh RD ((false, i) : Letter I) + μ)))
    case hg1 | hg2 =>
      simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp, whiskerRightIso_hom,
        eqToIso.hom, lift_map₂_whiskerRight, lift_map₂_eqToHom]
      erw [eqToHom_refl, id_whiskerRight, Category.comp_id]
      rfl
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact S.crossQ_congr j i (sh_ud' i j μ) (sh_ud j (sh RD ((false, i) : Letter I) + μ))
        _ _ _ _ _ _ _ _ _ _
    case hg4 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id, eqToIso.inv,
        lift_map₂_eqToHom]
      exact adjL_counit_congr (S := S) i (sh_ud i μ) _ _ _
    case hg5 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id, eqToIso.inv,
        lift_map₂_eqToHom]
      exact adjL_counit_congr (S := S) j (sh_ud j (sh RD ((false, i) : Letter I) + μ)) _ _ _
    case hg6 =>
      rw [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id,
        Category.id_comp, Category.comp_id]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sig0_dom_cross_g,
    sig0_cod_cross_g, sh_ud', sh_dd]

end QStrong

end Model

end Categorification.TwoRep
