/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2Curls

/-!
# The decompositions of `1_{EF}` and `1_{FE}` in the `sl₂` model of `U`

The decompositions of the identity of `E F 1_λ` and `F E 1_λ` (KL III `decompEF`, `decompFE`; CL
arXiv:1111.1431v3 §2.6, `eq_ident_decomp-nleqz` and the displays for `n > 0`, `n = 0`, with
`r_i = 1`) hold in the `sl₂` model of `Categorification.TwoRep.ModelSl2`, in every region of the
right parity (`StrongSl2.rel_decompEF`, `StrongSl2.rel_decompFE`). They are CL's decompositions for
the normalized left adjunctions (`BBw.decompEF`, `BBw.decompFE`, CL Prop. 5.2, Cor. 5.3, Lemma 5.4)
read through the interpretation:

* the sideways crossings `crossl`, `crossr` go to the mate `σ` of the crossing under the
  adjunctions `E ⊣ R` and to the inverse mate `σ'` under the normalized left adjunctions
  (`img_crossl`, `img_crossr`), by the normal forms `sideR_key`, `sideL_key`;
* the dotted caps and cups go to `capD`, `cupD`, `ccapD`, `ccupD` (`img_dotCapEF`,
  `img_cupDotEF`, `img_dotCapFE`, `img_cupDotFE`, with the dots of the downward strands moved to
  the upward strands by `cup_mate`, `cap_mate`), and the fake bubbles to the fake bubbles
  (`bubHom_cwL`, `bubHom_ccwL`);
* the sums of KL III are CL's sums after reindexing (`decompEF_model`, `decompFE_model`).

## Main results

* `BicatInterp.sideR_key`, `BicatInterp.sideL_key`;
* `StrongSl2.img_crossl`, `StrongSl2.img_crossr`;
* `StrongSl2.rel_decompEF`, `StrongSl2.rel_decompFE`.
-/

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ v₁ v₂

variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C] (M : Model S C)

omit M in
/-- The mate of `w` under right adjunctions, read as the composite "cup on the left, `w`, cap on
the right" of three whiskered layers. -/
theorem sideR_aux {a b c : C} {E : a ⟶ b} {R : b ⟶ a} {E' : b ⟶ c} {R' : c ⟶ b}
    (adj₁ : E ⊣ R) (adj₂ : E' ⊣ R') (w : E ≫ E' ⟶ E ≫ E') :
    (R ≫ E) ◁ (adj₂.unit ▷ 𝟙 b) ≫
        ((R ≫ E) ◁ (ρ_ (E' ≫ R')).hom ≫ (α_ R E (E' ≫ R')).hom ≫ R ◁ (α_ E E' R').inv) ≫
        R ◁ (w ▷ R') ≫
        (R ◁ (α_ E E' R').hom ≫ (α_ R E (E' ≫ R')).inv ≫ (λ_ _).inv) ≫
        𝟙 b ◁ (adj₁.counit ▷ (E' ≫ R')) =
      ((R ≫ E) ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ (R ≫ E)).hom) ≫ mateEquiv adj₁ adj₂ w ≫
        ((λ_ (E' ≫ R')).inv ≫ (λ_ (𝟙 b ≫ (E' ≫ R'))).inv) := by
  rw [mateEquiv_apply']
  bicategory

omit M in
/-- The mate of `w` under left adjunctions, read as the composite "cup on the right, `w`, cap on
the left" of three whiskered layers. -/
theorem sideL_aux {a b c : C} {R : b ⟶ a} {E : a ⟶ b} {R' : c ⟶ b} {E' : b ⟶ c}
    (A₁ : R ⊣ E) (A₂ : R' ⊣ E') (w : E ≫ E' ⟶ E ≫ E') :
    𝟙 b ◁ (A₁.unit ▷ (E' ≫ R')) ≫
        ((λ_ _).hom ≫ (α_ R E (E' ≫ R')).hom ≫ R ◁ (α_ E E' R').inv) ≫
        R ◁ (w ▷ R') ≫
        (R ◁ (α_ E E' R').hom ≫ (α_ R E (E' ≫ R')).inv ≫ (R ≫ E) ◁ (ρ_ (E' ≫ R')).inv) ≫
        (R ≫ E) ◁ (A₂.counit ▷ 𝟙 b) =
      ((λ_ (𝟙 b ≫ (E' ≫ R'))).hom ≫ (λ_ (E' ≫ R')).hom) ≫ (mateEquiv A₁ A₂).symm w ≫
        ((ρ_ (R ≫ E)).inv ≫ (R ≫ E) ◁ (λ_ (𝟙 b)).inv) := by
  rw [mateEquiv_symm_apply']
  bicategory

/-- **A sideways crossing in normal form (right adjunctions)**: two strands `r ≫ e` with a cup
(the unit of `F e' ⊣ F r'`) on their left, a generator image `w` on `e ≫ e'`, and a cap (the counit
of `F e ⊣ F r`) on the right, all conjugated by images of free 2-morphisms, is the mate of `w`. -/
theorem sideR_key {x y z : FB S} {r : x ⟶ y} {e : y ⟶ x} {e' : x ⟶ z} {r' : z ⟶ x}
    (adj₁ : M.lift.map e ⊣ M.lift.map r) (adj₂ : M.lift.map e' ⊣ M.lift.map r')
    (w : M.lift.map e ≫ M.lift.map e' ⟶ M.lift.map e ≫ M.lift.map e')
    {p₁ q₁ d₁ c₁ : x ⟶ x} (σp₁ : p₁ ≅ r ≫ e) (σq₁ : q₁ ≅ 𝟙 x) (σd₁ : d₁ ≅ 𝟙 x)
    (σc₁ : c₁ ≅ e' ≫ r') (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj₂.unit)
    {p₂ : x ⟶ y} {q₂ : z ⟶ x} {d₂ c₂ : y ⟶ z} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r')
    (σd₂ : d₂ ≅ e ≫ e') (σc₂ : c₂ ≅ e ≫ e') (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ q₃ d₃ c₃ : x ⟶ x} (σp₃ : p₃ ≅ 𝟙 x) (σq₃ : q₃ ≅ e' ≫ r') (σd₃ : d₃ ≅ r ≫ e)
    (σc₃ : c₃ ≅ 𝟙 x) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = adj₁.counit)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ x}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ r ≫ e) (F₁ : e' ≫ r' ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ mateEquiv adj₁ adj₂ w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (r ≫ e) (𝟙 x) (x := 𝟙 x) (y := e' ≫ r') adj₂.unit ≫
      M.lift.map₂ ((r ≫ e) ◁ (ρ_ (e' ≫ r')).hom ≫ (α_ r e (e' ≫ r')).hom ≫
        r ◁ (α_ e e' r').inv) ≫
      midK M r r' (x := e ≫ e') (y := e ≫ e') w ≫
      M.lift.map₂ (r ◁ (α_ e e' r').hom ≫ (α_ r e (e' ≫ r')).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 x) (e' ≫ r') (x := r ≫ e) (y := 𝟙 x) adj₁.counit =
      M.lift.map₂ ((r ≫ e) ◁ (λ_ (𝟙 x)).hom ≫ (ρ_ (r ≫ e)).hom) ≫ mateEquiv adj₁ adj₂ w ≫
        M.lift.map₂ ((λ_ (e' ≫ r')).inv ≫ (λ_ (𝟙 x ≫ (e' ≫ r'))).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map_comp]
    exact sideR_aux adj₁ adj₂ w
  rw [lift_map₂_eq M _ ((r ≫ e) ◁ (ρ_ (e' ≫ r')).hom ≫ (α_ r e (e' ≫ r')).hom ≫
      r ◁ (α_ e e' r').inv),
    lift_map₂_eq M _ (r ◁ (α_ e e' r').hom ≫ (α_ r e (e' ≫ r')).inv ≫ (λ_ _).inv),
    reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  erw [Category.assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ F₀, lift_map₂_eq M _ F₁]

/-- **A sideways crossing in normal form (left adjunctions)**: two strands `e' ≫ r'` with a cup
(the unit of `F r ⊣ F e`) on their right, a generator image `w` on `e ≫ e'`, and a cap (the counit
of `F r' ⊣ F e'`) on the left, all conjugated by images of free 2-morphisms, is the inverse mate of
`w`. -/
theorem sideL_key {x y z : FB S} {r : x ⟶ y} {e : y ⟶ x} {e' : x ⟶ z} {r' : z ⟶ x}
    (A₁ : M.lift.map r ⊣ M.lift.map e) (A₂ : M.lift.map r' ⊣ M.lift.map e')
    (w : M.lift.map e ≫ M.lift.map e' ⟶ M.lift.map e ≫ M.lift.map e')
    {p₁ q₁ d₁ c₁ : x ⟶ x} (σp₁ : p₁ ≅ 𝟙 x) (σq₁ : q₁ ≅ e' ≫ r') (σd₁ : d₁ ≅ 𝟙 x)
    (σc₁ : c₁ ≅ r ≫ e) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = A₁.unit)
    {p₂ : x ⟶ y} {q₂ : z ⟶ x} {d₂ c₂ : y ⟶ z} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r')
    (σd₂ : d₂ ≅ e ≫ e') (σc₂ : c₂ ≅ e ≫ e') (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ q₃ d₃ c₃ : x ⟶ x} (σp₃ : p₃ ≅ r ≫ e) (σq₃ : q₃ ≅ 𝟙 x) (σd₃ : d₃ ≅ e' ≫ r')
    (σc₃ : c₃ ≅ 𝟙 x) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = A₂.counit)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ x}
    (E₀ : P ⟶ P₁) (A₁' : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂' : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃' : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ e' ≫ r') (F₁ : r ≫ e ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁' ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂' ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃' ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ (mateEquiv A₁ A₂).symm w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (𝟙 x) (e' ≫ r') (x := 𝟙 x) (y := r ≫ e) A₁.unit ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ r e (e' ≫ r')).hom ≫ r ◁ (α_ e e' r').inv) ≫
      midK M r r' (x := e ≫ e') (y := e ≫ e') w ≫
      M.lift.map₂ (r ◁ (α_ e e' r').hom ≫ (α_ r e (e' ≫ r')).inv ≫
        (r ≫ e) ◁ (ρ_ (e' ≫ r')).inv) ≫
        midK M (r ≫ e) (𝟙 x) (x := e' ≫ r') (y := 𝟙 x) A₂.counit =
      M.lift.map₂ ((λ_ (𝟙 x ≫ (e' ≫ r'))).hom ≫ (λ_ (e' ≫ r')).hom) ≫
        (mateEquiv A₁ A₂).symm w ≫
        M.lift.map₂ ((ρ_ (r ≫ e)).inv ≫ (r ≫ e) ◁ (λ_ (𝟙 x)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map_comp]
    exact sideL_aux A₁ A₂ w
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ r e (e' ≫ r')).hom ≫ r ◁ (α_ e e' r').inv),
    lift_map₂_eq M _ (r ◁ (α_ e e' r').hom ≫ (α_ r e (e' ≫ r')).inv ≫
      (r ≫ e) ◁ (ρ_ (e' ≫ r')).inv),
    reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  erw [Category.assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ F₀, lift_map₂_eq M _ F₁]

end Categorification.Diagrams.BicatInterp

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

variable {S : StrongSl2 k B} (hS : S.BBw)

attribute [local irreducible] KL3.Diagram.sh

set_option maxHeartbeats 4000000 in
/-- The image of the sideways crossing `crossl` (`E F → F E`): the mate of the crossing under the
adjunctions `E ⊣ R` (CL's `σ`). -/
theorem img_crossl (lam : ℤ) :
    eqToHom (objI_pos _ _ (cond_up_dn lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (crossl sl2RootDatum () () lam) ≫
        eqToHom (objI_pos _ _ (cond_dn_up lam)) =
      mateEquiv (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam))
        (S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam))
        (S.gCross (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, crossl, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up', dual_dn']
  generalize_proofs
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + lam) = x at *
  have hxl : x = lam := by rw [← hx]; exact sh_true_sh_false () lam
  subst hxl
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3]
  case c1 | c2 | c3 =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sh_false_sh_true, sig0_colourSrc', sig0_colourTgt', sig0_dom_cross', hx]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w3 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross', sig0_cod_cross',
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up', dual_dn', sig0_colourTgt',
      sig0_colourSrc']
    refine (sideR_key S.model
      (r := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl, hx⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (e' := FreeBicategory.Hom.of (⟨⟨up (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (up ()) + x)))
      (r' := FreeBicategory.Hom.of (⟨⟨dn (), sh sl2RootDatum (up ()) + x⟩, rfl,
          sh_false_sh_true () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + x) ⟶ rq x))
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (S.gAdjE (S.qi x) (S.qi (sh sl2RootDatum (up ()) + x)) (S.qi_sh_true () x))
      (S.gCross (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x)
        (S.qi (sh sl2RootDatum (up ()) + x)) (S.qi_sh_false () x) (S.qi_sh_true () x))
      (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
      (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
      (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 =>
      first
        | rfl
        | exact comp_of_congr rfl (congrArg (Col.mk (up ())) (sh_false_sh_true () _)) rfl
        | exact comp_of_congr hx rfl (congrArg (Col.mk (up ())) hx)
        | exact comp_of_congr rfl (congrArg (Col.mk (dn ())) hx) rfl
    case hg1 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact genImg_cup_false hS () _ _ _ _ _ _ _
    case hg2 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact gCross_congr _ _ _ _ (congrArg S.qi hx) _ _ _ _ _ _
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact genImg_cap_false hS () _ _ _ _ _ _ _
    case fin =>
      simp only [PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, hx, sig0_dom_cross',
    sig0_cod_cross', sh_false_sh_true, sh_true_sh_false]

set_option maxHeartbeats 4000000 in
/-- The image of the sideways crossing `crossr` (`F E → E F`): the inverse mate of the crossing
under the normalized left adjunctions `R ⊣ E` (CL's `σ'`, (4.16)). -/
theorem img_crossr (lam : ℤ) :
    eqToHom (objI_pos _ _ (cond_dn_up lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (crossr sl2RootDatum () () lam) ≫
        eqToHom (objI_pos _ _ (cond_up_dn lam)) =
      (mateEquiv (gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam))
        (gAdjL hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam))).symm
        (S.gCross (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, crossr, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up', dual_dn']
  generalize_proofs
  generalize hx : sh sl2RootDatum (up ()) + (sh sl2RootDatum (dn ()) + lam) = x at *
  have hxl : x = lam := by rw [← hx]; exact sh_true_sh_false () lam
  subst hxl
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3]
  case c1 | c2 | c3 =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sh_false_sh_true, sig0_colourSrc', sig0_colourTgt', sig0_dom_cross', hx]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w2 _]
  set_option backward.isDefEq.respectTransparency false in
  try erw [eqToHom_word ?w3 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross', sig0_cod_cross',
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up', dual_dn', sig0_colourTgt',
      sig0_colourSrc']
    refine (sideL_key S.model
      (r := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl, hx⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (e' := FreeBicategory.Hom.of (⟨⟨up (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (up ()) + x)))
      (r' := FreeBicategory.Hom.of (⟨⟨dn (), sh sl2RootDatum (up ()) + x⟩, rfl,
          sh_false_sh_true () x⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + x) ⟶ rq x))
      (gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x))
      (gAdjL hS (S.qi x) (S.qi (sh sl2RootDatum (up ()) + x)) (S.qi_sh_true () x))
      (S.gCross (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x)
        (S.qi (sh sl2RootDatum (up ()) + x)) (S.qi_sh_false () x) (S.qi_sh_true () x))
      (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
      (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
      (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 =>
      first
        | rfl
        | exact comp_of_congr rfl (congrArg (Col.mk (up ())) (sh_false_sh_true () _)) rfl
        | exact comp_of_congr hx rfl (congrArg (Col.mk (up ())) hx)
        | exact comp_of_congr rfl (congrArg (Col.mk (dn ())) hx) rfl
    case hg1 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact genImg_cup_true hS () _ _ _ _ _ _ _
    case hg2 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact gCross_congr _ _ _ _ (congrArg S.qi hx) _ _ _ _ _ _
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact genImg_cap_true hS () _ _ _ _ _ _ _
    case fin =>
      simp only [PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      congr 1
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, hx, sig0_dom_cross',
    sig0_cod_cross', sh_false_sh_true, sh_true_sh_false]

set_option maxHeartbeats 2000000 in
/-- The image of a dot on the upward strand of `E F`. -/
theorem img_dotUp_UD (lam : ℤ) :
    eqToHom (objI_pos _ _ (cond_up_dn lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .dot (up ()), [dn ()])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ (cond_up_dn lam)) =
      S.gRc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) ◁
        S.gDot (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact cond_up_dn lam
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model (whiskerLeftIso _ (ρ_ _)) (whiskerLeftIso _ (ρ_ _)) _ _ _ _ _
      (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_right]
      simp only [lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      erw [genImg_dot_true hS]
      rfl
    case e => rfl
    case e' => rfl
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false,
    sh_false_sh_true, sig0_dom_dot']

set_option maxHeartbeats 2000000 in
/-- The image of a dot on the downward strand of `F E`. -/
theorem img_dotDn_DU (lam : ℤ) :
    eqToHom (objI_pos _ _ (cond_dn_up lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map
          (mkD sl2RootDatum lam [([], .dot (dn ()), [up ()])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ (cond_dn_up lam)) =
      S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ◁
        gDotR hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact cond_dn_up lam
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model (whiskerLeftIso _ (ρ_ _)) (whiskerLeftIso _ (ρ_ _)) _ _ _ _ _
      (eqToHom ?e) (eqToHom ?e')).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_right]
      simp only [lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      erw [genImg_dot_false hS]
      rfl
    case e => rfl
    case e' => rfl
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, sh_true_sh_false,
    sh_false_sh_true, sig0_dom_dot']

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dotCapEF_eq (lam : ℤ) (m : ℕ) :
    dotCapEF sl2RootDatum lam () m =
      dots sl2RootDatum lam [] (up ()) [dn ()] m ≫
        mkD sl2RootDatum lam [([], .cap (dn ()), [])] ⟨rfl, rfl⟩ := by
  unfold dotCapEF dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupDotEF_eq (lam : ℤ) (m : ℕ) :
    cupDotEF sl2RootDatum lam () m =
      mkD sl2RootDatum lam [([], .cup (up ()), [])] ⟨rfl, rfl⟩ ≫
        dots sl2RootDatum lam [up ()] (dn ()) [] m := by
  unfold cupDotEF dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem dotCapFE_eq (lam : ℤ) (m : ℕ) :
    dotCapFE sl2RootDatum lam () m =
      dots sl2RootDatum lam [] (dn ()) [up ()] m ≫
        mkD sl2RootDatum lam [([], .cap (up ()), [])] ⟨rfl, rfl⟩ := by
  unfold dotCapFE dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cupDotFE_eq (lam : ℤ) (m : ℕ) :
    cupDotFE sl2RootDatum lam () m =
      mkD sl2RootDatum lam [([], .cup (dn ()), [])] ⟨rfl, rfl⟩ ≫
        dots sl2RootDatum lam [dn ()] (up ()) [] m := by
  unfold cupDotFE dots
  set_option backward.isDefEq.respectTransparency false in
  rw [mkD_comp]

theorem img_dotCapEF (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_up_dn lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (dotCapEF sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_nil lam)) =
      S.gRc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) ◁
          powComp (S.gDot (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
            (S.qi_sh_false () lam)) m ≫
        (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [dotCapEF_eq, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_up_dn lam)) (objI_pos _ _ (cond_up_dn lam))
      (objI_pos _ _ (cond_nil lam)), img_capDn hS lam (cond_up_dn lam) (cond_nil lam)]
  erw [img_dots hS lam [] (up ()) [dn ()] (cond_up_dn lam) m, img_dotUp_UD hS lam]
  rw [whiskerLeft_powComp]

theorem img_cupDotEF (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (cupDotEF sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_up_dn lam)) =
      (gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit ≫
        powComp (gDotR hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)) m ▷
          S.gEc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  rw [cupDotEF_eq, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_up_dn lam))
      (objI_pos _ _ (cond_up_dn lam)), img_cupUp hS lam (cond_nil lam) (cond_up_dn lam)]
  erw [img_dots hS lam [up ()] (dn ()) [] (cond_up_dn lam) m, img_dotDn_UD hS lam (cond_up_dn lam)]
  rw [← powComp_whiskerRight]

theorem img_dotCapFE (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_dn_up lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (dotCapFE sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_nil lam)) =
      S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ◁
          powComp (gDotR hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
            (S.qi_sh_true () lam)) m ≫
        (gAdjL hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [dotCapFE_eq, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_dn_up lam)) (objI_pos _ _ (cond_dn_up lam))
      (objI_pos _ _ (cond_nil lam)), img_capUp hS lam (cond_dn_up lam) (cond_nil lam)]
  erw [img_dots hS lam [] (dn ()) [up ()] (cond_dn_up lam) m, img_dotDn_DU hS lam]
  rw [whiskerLeft_powComp]

theorem img_cupDotFE (lam : ℤ) (m : ℕ) :
    eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
        (interp (genImg hS) lam lam).functor.map (cupDotFE sl2RootDatum lam () m) ≫
        eqToHom (objI_pos _ _ (cond_dn_up lam)) =
      (S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).unit ≫
        powComp (S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)) m ▷
          S.gRc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  rw [cupDotFE_eq, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_dn_up lam))
      (objI_pos _ _ (cond_dn_up lam)), img_cupDn hS lam (cond_nil lam) (cond_dn_up lam)]
  erw [img_dots hS lam [dn ()] (up ()) [] (cond_dn_up lam) m, img_dotUp_DU hS lam (cond_dn_up lam)]
  rw [← powComp_whiskerRight]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- A cup followed by mates of dots on the left adjoint, as dots on the right adjoint. -/
theorem cup_mate {C : Type*} [Bicategory C] {a b : C} {R : b ⟶ a} {E : a ⟶ b} (A : R ⊣ E)
    (x : E ⟶ E) (m : ℕ) :
    A.unit ≫ powComp ((Bicategory.conjugateEquiv A A).symm x) m ▷ E =
      A.unit ≫ R ◁ powComp x m := by
  rw [← conjugateEquiv_symm_powComp, ← unit_whiskerLeft_conjugateEquiv, Equiv.apply_symm_apply]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- Mates of dots on the left adjoint followed by a cap, as dots on the right adjoint. -/
theorem cap_mate {C : Type*} [Bicategory C] {a b : C} {R : b ⟶ a} {E : a ⟶ b} (A : R ⊣ E)
    (x : E ⟶ E) (m : ℕ) :
    E ◁ powComp ((Bicategory.conjugateEquiv A A).symm x) m ≫ A.counit =
      powComp x m ▷ R ≫ A.counit := by
  rw [← conjugateEquiv_symm_powComp, ← conjugateEquiv_whiskerRight_counit, Equiv.apply_symm_apply]

/-- The decomposition of `1_{EF}` at the level of the model (CL `eq_ident_decomp`, KL III
`decompEF`, with `r_i = 1`), for the objects `a`, `b = a + 1`, `c = b + 1`, `b` of weight `n`. -/
theorem decompEF_model (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n : ℤ) (hn : S.wt b = n) :
    𝟙 _ + mateEquiv (S.gAdjE a b h) (S.gAdjE b c h') (S.gCross a b c h h') ≫
        (mateEquiv (gAdjL hS a b h) (gAdjL hS b c h')).symm (S.gCross a b c h h') -
      ∑ f ∈ Finset.range n.toNat, ∑ g ∈ Finset.range (f + 1),
        (S.gRc a b h ◁ powComp (S.gDot a b h) (f - g) ≫ (S.gAdjE a b h).counit) ≫
          mccwL hS a b c h h' n (-n - 1 + g) ≫
            ((gAdjL hS a b h).unit ≫ powComp (gDotR hS a b h) (n.toNat - 1 - f) ▷ S.gEc a b h) =
      0 := by
  subst h h' hn
  have hσ : mateEquiv (S.gAdjE a (a + 1) rfl) (S.gAdjE (a + 1) (a + 1 + 1) rfl)
      (S.gCross a (a + 1) (a + 1 + 1) rfl rfl) = S.grSigma a := (S.grSigma_eq_mateEquiv a).symm
  have hs : (mateEquiv (gAdjL hS a (a + 1) rfl) (gAdjL hS (a + 1) (a + 1 + 1) rfl)).symm
      (S.gCross a (a + 1) (a + 1 + 1) rfl rfl) = hS.sideL a := by
    rw [BBw.sideL, StrongSl2.sideL]
    congr 1
  have hcap : ∀ m : ℕ, S.gRc a (a + 1) rfl ◁ powComp (S.gDot a (a + 1) rfl) m ≫
      (S.gAdjE a (a + 1) rfl).counit = S.capD a m := fun m => rfl
  have hcup : ∀ m : ℕ, (gAdjL hS a (a + 1) rfl).unit ≫ powComp (gDotR hS a (a + 1) rfl) m ▷
      S.gEc a (a + 1) rfl = S.cupD (hS.leftAdjN a) m := fun m => cup_mate _ _ m
  rw [hσ, hs]
  simp only [hcap, hcup, mccwL_eq]
  rcases le_or_gt 0 (S.wt (a + 1)) with hn | hn
  · obtain ⟨_, h2⟩ := hS.decompEF hn
    set N := (S.wt (a + 1)).toNat with hN
    have hsum : ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1),
        S.capD a (f - g) ≫ hS.ccwL a (-S.wt (a + 1) - 1 + g) ≫ S.cupD (hS.leftAdjN a) (N - 1 - f) =
        ∑ j ∈ Finset.range N, hS.compK a j ≫ S.cupD (hS.leftAdjN a) j := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [BBw.compK, Preadditive.sum_comp, ← hN,
        show N - 1 - j + 1 = N - j by omega, show N - 1 - (N - 1 - j) = j by omega]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [Finset.mem_range] at hg
      rw [Category.assoc, show N - 1 - j - g = N - 1 - j - g from rfl]
    have key : 𝟙 (S.grR a ≫ S.grE a) + S.grSigma a ≫ hS.sideL a -
        ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1),
          S.capD a (f - g) ≫ hS.ccwL a (-S.wt (a + 1) - 1 + g) ≫
            S.cupD (hS.leftAdjN a) (N - 1 - f) = 0 := by
      rw [hsum, ← h2]
      abel
    exact key
  · have h1 := (hS.decompFE (q := a) hn.le).1
    have key : 𝟙 (S.grR a ≫ S.grE a) + S.grSigma a ≫ hS.sideL a -
        ∑ f ∈ Finset.range (S.wt (a + 1)).toNat, ∑ g ∈ Finset.range (f + 1),
          S.capD a (f - g) ≫ hS.ccwL a (-S.wt (a + 1) - 1 + g) ≫
            S.cupD (hS.leftAdjN a) ((S.wt (a + 1)).toNat - 1 - f) = 0 := by
      rw [show (S.wt (a + 1)).toNat = 0 by omega, Finset.range_zero, Finset.sum_empty, h1]
      abel
    exact key

/-- The decomposition of `1_{FE}` at the level of the model (CL `eq_ident_decomp-nleqz`, KL III
`decompFE`, with `r_i = 1`), for the objects `a`, `b = a + 1`, `c = b + 1`, `b` of weight `n`. -/
theorem decompFE_model (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n : ℤ) (hn : S.wt b = n) :
    𝟙 _ + (mateEquiv (gAdjL hS a b h) (gAdjL hS b c h')).symm (S.gCross a b c h h') ≫
        mateEquiv (S.gAdjE a b h) (S.gAdjE b c h') (S.gCross a b c h h') -
      ∑ f ∈ Finset.range (-n).toNat, ∑ g ∈ Finset.range (f + 1),
        (S.gEc b c h' ◁ powComp (gDotR hS b c h') (f - g) ≫ (gAdjL hS b c h').counit) ≫
          mcwL hS a b c h h' n (n - 1 + g) ≫
            ((S.gAdjE b c h').unit ≫ powComp (S.gDot b c h') ((-n).toNat - 1 - f) ▷
              S.gRc b c h') =
      0 := by
  subst h h' hn
  have hσ : mateEquiv (S.gAdjE a (a + 1) rfl) (S.gAdjE (a + 1) (a + 1 + 1) rfl)
      (S.gCross a (a + 1) (a + 1 + 1) rfl rfl) = S.grSigma a := (S.grSigma_eq_mateEquiv a).symm
  have hs : (mateEquiv (gAdjL hS a (a + 1) rfl) (gAdjL hS (a + 1) (a + 1 + 1) rfl)).symm
      (S.gCross a (a + 1) (a + 1 + 1) rfl rfl) = hS.sideL a := by
    rw [BBw.sideL, StrongSl2.sideL]
    congr 1
  have hcap : ∀ m : ℕ, S.gEc (a + 1) (a + 1 + 1) rfl ◁
      powComp (gDotR hS (a + 1) (a + 1 + 1) rfl) m ≫ (gAdjL hS (a + 1) (a + 1 + 1) rfl).counit =
      S.ccapD (hS.leftAdjN (a + 1)) m := fun m => cap_mate _ _ m
  have hcup : ∀ m : ℕ, (S.gAdjE (a + 1) (a + 1 + 1) rfl).unit ≫
      powComp (S.gDot (a + 1) (a + 1 + 1) rfl) m ▷ S.gRc (a + 1) (a + 1 + 1) rfl =
      S.ccupD a m := fun m => rfl
  rw [hσ, hs]
  simp only [hcap, hcup, mcwL_eq]
  rcases le_or_gt (S.wt (a + 1)) 0 with hn | hn
  · obtain ⟨_, h2⟩ := hS.decompFE hn
    set N := (-S.wt (a + 1)).toNat with hN
    have hsum : ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1),
        S.ccapD (hS.leftAdjN (a + 1)) (f - g) ≫ hS.cwL a (S.wt (a + 1) - 1 + g) ≫
          S.ccupD a (N - 1 - f) =
        ∑ j ∈ Finset.range N, hS.compKN a j ≫ S.ccupD a j := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [BBw.compKN, Preadditive.sum_comp, ← hN,
        show N - 1 - j + 1 = N - j by omega, show N - 1 - (N - 1 - j) = j by omega]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [Category.assoc]
    have key : 𝟙 (S.grE (a + 1) ≫ S.grR (a + 1)) + hS.sideL a ≫ S.grSigma a -
        ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1),
          S.ccapD (hS.leftAdjN (a + 1)) (f - g) ≫ hS.cwL a (S.wt (a + 1) - 1 + g) ≫
            S.ccupD a (N - 1 - f) = 0 := by
      rw [hsum, ← h2]
      abel
    exact key
  · have h1 := (hS.decompEF (q := a) hn.le).1
    have key : 𝟙 (S.grE (a + 1) ≫ S.grR (a + 1)) + hS.sideL a ≫ S.grSigma a -
        ∑ f ∈ Finset.range (-S.wt (a + 1)).toNat, ∑ g ∈ Finset.range (f + 1),
          S.ccapD (hS.leftAdjN (a + 1)) (f - g) ≫ hS.cwL a (S.wt (a + 1) - 1 + g) ≫
            S.ccupD a ((-S.wt (a + 1)).toNat - 1 - f) = 0 := by
      rw [show (-S.wt (a + 1)).toNat = 0 by omega, Finset.range_zero, Finset.sum_empty, h1]
      abel
    exact key

/-- The image of a term of the sum in the decomposition of `1_{EF}`. -/
theorem img_decompEF_term (lam : ℤ) (f g : ℕ) :
    eqToHom (objI_pos _ _ (cond_up_dn lam)).symm ≫
        (freeLift k (interp (genImg hS) lam lam).functor).map
          (LinDiagram.of (dotCapEF sl2RootDatum lam () (f - g)) ≫
            KL3.Diagram.ccwL sl2RootDatum k lam () (-ip sl2RootDatum () lam - 1 + g) ≫
              LinDiagram.of (cupDotEF sl2RootDatum lam () ((ip sl2RootDatum () lam).toNat - 1 - f))) ≫
        eqToHom (objI_pos _ _ (cond_up_dn lam)) =
      (S.gRc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam) ◁
          powComp (S.gDot (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
            (S.qi_sh_false () lam)) (f - g) ≫
        (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)).counit) ≫
        mccwL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)
          lam (-lam - 1 + g) ≫
        ((gAdjL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit ≫
          powComp (gDotR hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
            (S.qi_sh_false () lam)) (lam.toNat - 1 - f) ▷
            S.gEc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)) := by
  set_option backward.isDefEq.respectTransparency false in
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_up_dn lam)) (objI_pos _ _ (cond_nil lam))
      (objI_pos _ _ (cond_up_dn lam)),
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_nil lam))
      (objI_pos _ _ (cond_up_dn lam)),
    freeLift_map_of, freeLift_map_of, img_dotCapEF, img_cupDotEF, ← bubHom_apply, bubHom_ccwL,
    ip_sl2]

/-- The image of a term of the sum in the decomposition of `1_{FE}`. -/
theorem img_decompFE_term (lam : ℤ) (f g : ℕ) :
    eqToHom (objI_pos _ _ (cond_dn_up lam)).symm ≫
        (freeLift k (interp (genImg hS) lam lam).functor).map
          (LinDiagram.of (dotCapFE sl2RootDatum lam () (f - g)) ≫
            KL3.Diagram.cwL sl2RootDatum k lam () (ip sl2RootDatum () lam - 1 + g) ≫
              LinDiagram.of (cupDotFE sl2RootDatum lam () ((-ip sl2RootDatum () lam).toNat - 1 - f))) ≫
        eqToHom (objI_pos _ _ (cond_dn_up lam)) =
      (S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ◁
          powComp (gDotR hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
            (S.qi_sh_true () lam)) (f - g) ≫
        (gAdjL hS (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)).counit) ≫
        mcwL hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)
          lam (lam - 1 + g) ≫
        ((S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).unit ≫
          powComp (S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
            (S.qi_sh_true () lam)) ((-lam).toNat - 1 - f) ▷
            S.gRc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)) := by
  set_option backward.isDefEq.respectTransparency false in
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    conj_comp_conj (objI_pos _ _ (cond_dn_up lam)) (objI_pos _ _ (cond_nil lam))
      (objI_pos _ _ (cond_dn_up lam)),
    conj_comp_conj (objI_pos _ _ (cond_nil lam)) (objI_pos _ _ (cond_nil lam))
      (objI_pos _ _ (cond_dn_up lam)),
    freeLift_map_of, freeLift_map_of, img_dotCapFE, img_cupDotFE, ← bubHom_apply, bubHom_cwL,
    ip_sl2]

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem conj_comp_conj' {D : Type*} [Category D] {X X' Y Y' Z Z' : D} (p : X = X') (q : Y = Y')
    (r : Z = Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    eqToHom p.symm ≫ f ≫ g ≫ eqToHom r =
      (eqToHom p.symm ≫ f ≫ eqToHom q) ≫ (eqToHom q.symm ≫ g ≫ eqToHom r) := by
  simp

set_option maxHeartbeats 4000000 in
/-- **The decomposition of `1_{EF}` in the `sl₂` model** (KL III `decompEF`; CL
`eq_ident_decomp` with `r_i = 1`), read with the outer regions `λ`, `λ`, in the regions of the right
parity. -/
theorem rel_decompEF' {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg hS) lam lam).functor).map
      (LinDiagram.of (𝟙 _) + LinDiagram.of (crossl sl2RootDatum () () lam ≫
          crossr sl2RootDatum () () lam) - decompEFSum sl2RootDatum k () lam) = 0 := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_up_dn lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_up_dn lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sub, Functor.map_add, freeLift_map_of, freeLift_map_of,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add,
    Preadditive.add_comp, Limits.comp_zero, Limits.zero_comp, Category.id_comp,
    Category.assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [conj_comp_conj' (objI_pos _ _ (cond_up_dn lam)) (objI_pos _ _ (cond_dn_up lam))
      (objI_pos _ _ (cond_up_dn lam)), img_crossl, img_crossr]
  erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
  unfold decompEFSum
  set_option backward.isDefEq.respectTransparency false in
  simp only [Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl
    (fun g _ => img_decompEF_term hS lam f g))]
  erw [ip_sl2]
  exact decompEF_model hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
    (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam) lam
    (wt_qi hpar)

set_option maxHeartbeats 4000000 in
/-- **The decomposition of `1_{FE}` in the `sl₂` model** (KL III `decompFE`; CL
`eq_ident_decomp-nleqz` with `r_i = 1`), read with the outer regions `λ`, `λ`, in the regions of
the right parity. -/
theorem rel_decompFE' {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg hS) lam lam).functor).map
      (LinDiagram.of (𝟙 _) + LinDiagram.of (crossr sl2RootDatum () () lam ≫
          crossl sl2RootDatum () () lam) - decompFESum sl2RootDatum k () lam) = 0 := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_dn_up lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_dn_up lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sub, Functor.map_add, freeLift_map_of, freeLift_map_of,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add,
    Preadditive.add_comp, Limits.comp_zero, Limits.zero_comp, Category.id_comp,
    Category.assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [conj_comp_conj' (objI_pos _ _ (cond_dn_up lam)) (objI_pos _ _ (cond_up_dn lam))
      (objI_pos _ _ (cond_dn_up lam)), img_crossl, img_crossr]
  erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
  unfold decompFESum
  set_option backward.isDefEq.respectTransparency false in
  simp only [Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl
    (fun g _ => img_decompFE_term hS lam f g))]
  erw [ip_sl2]
  exact decompFE_model hS (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
    (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam) lam
    (wt_qi hpar)

/-- **The decomposition of `1_{EF}` in the `sl₂` model**, read with its own outer regions (KL III
`decompEF`, the relation of `U` with bottom boundary `E F 1_λ`). -/
theorem rel_decompEF {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg hS) (KL3.Diagram.wt sl2RootDatum lam [up (), dn ()] : ℤ)
        lam).functor).map
      (LinDiagram.of (𝟙 _) + LinDiagram.of (crossl sl2RootDatum () () lam ≫
          crossr sl2RootDatum () () lam) - decompEFSum sl2RootDatum k () lam) = 0 := by
  have e : KL3.Diagram.wt sl2RootDatum lam [up (), dn ()] = lam := sh_true_sh_false () lam
  rw [e]
  exact rel_decompEF' hS hpar

/-- **The decomposition of `1_{FE}` in the `sl₂` model**, read with its own outer regions (KL III
`decompFE`, the relation of `U` with bottom boundary `F E 1_λ`). -/
theorem rel_decompFE {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg hS) (KL3.Diagram.wt sl2RootDatum lam [dn (), up ()] : ℤ)
        lam).functor).map
      (LinDiagram.of (𝟙 _) + LinDiagram.of (crossr sl2RootDatum () () lam ≫
          crossl sl2RootDatum () () lam) - decompFESum sl2RootDatum k () lam) = 0 := by
  have e : KL3.Diagram.wt sl2RootDatum lam [dn (), up ()] = lam := sh_false_sh_true () lam
  rw [e]
  exact rel_decompFE' hS hpar

end StrongSl2

end Model

end Categorification.TwoRep
