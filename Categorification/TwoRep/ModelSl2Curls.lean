/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2Bubbles

/-!
# The curl relations in the `sl₂` model of `U`

The curl relations of KL III's `U` (`curlR`, `curlL`; CL arXiv:1111.1431v3 §2.6,
`eq_reduction-ngeqz`, `eq_reduction-nleqz` and the display for `n = 0`, with `r_i = 1`) hold in the
`sl₂` model of `Categorification.TwoRep.ModelSl2`, in every region of the right parity
(`StrongSl2.rel_curlR`, `StrongSl2.rel_curlL`). They are the curl relations of CL §5.3 for the
normalized left adjunctions (`curlG_eq`, `curlE_eq`, `curlG_eq_zero`,
`curlE_eq_zero`), read through the interpretation:

* the image of a curl diagram is a curl `curlG` / `curlEG` of the crossing (`img_curlR`,
  `img_curlL`), by the normal forms `curl_key`, `curlL_key`;
* the images of linear combinations of diagrams from `1_λ` to itself form a ring homomorphism
  `bubHom` to `End(𝟙)`, which commutes with the infinite Grassmannian recursion
  (`map_grassInv`), so it sends KL III's fake bubbles to the fake bubbles of the model
  (`bubHom_cwL`, `bubHom_ccwL`; `mcwL_eq`, `mccwL_eq` identify these with `cwLN`, `ccwLN`);
* bubbles placed next to a strand go to whiskered bubbles (`img_bubR`, `img_bubL`), by the image
  of a whiskered linear combination of diagrams (`BicatInterp.conj_freeLift_whisker`).

## Main results

* `BicatInterp.curl_key`, `BicatInterp.curlL_key`, `BicatInterp.conj_freeLift_whisker`;
* `StrongSl2.bubHom`, `StrongSl2.map_grassInv`, `StrongSl2.bubHom_cwL`, `StrongSl2.bubHom_ccwL`;
* `StrongSl2.rel_curlR`, `StrongSl2.rel_curlL`.
-/

noncomputable section

set_option linter.unusedSimpArgs false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams
open Categorification.TwoRep (curlG curlEG)

universe w₁ w₂ u₀ u₁ u₂ v₁ v₂

variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C] (M : Model S C)

omit M in
/-- The curl of `w`, read as the composite "cup on the right, `w`, cap" of three whiskered
layers, in an arbitrary bicategory. -/
theorem curl_aux {a b c : C} {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (w : E ≫ E' ⟶ E ≫ E') :
    𝟙 b ◁ (u ▷ E') ≫ ((λ_ _).hom ≫ (α_ R E E').hom ≫ R ◁ (ρ_ (E ≫ E')).inv) ≫
        R ◁ (w ▷ 𝟙 c) ≫ (R ◁ (ρ_ (E ≫ E')).hom ≫ (α_ R E E').inv ≫ (λ_ _).inv) ≫
          𝟙 b ◁ (eps ▷ E') =
      ((λ_ _).hom ≫ (λ_ E').hom) ≫ curlG u eps w ≫ ((λ_ E').inv ≫ (λ_ _).inv) := by
  unfold curlG
  bicategory

/-- **A curl in normal form**: a strand `e'` with a cup (`u`, on the new strands `r`, `e`) on
its right, a generator image `w` on `e ≫ e'`, and a cap (`eps`) closing `r ≫ e`, all conjugated
by images of free 2-morphisms, is the curl `curlG u eps w`. -/
theorem curl_key {x y z : FB S} {r : x ⟶ y} {e : y ⟶ x} {e' : x ⟶ z}
    (u : 𝟙 (M.lift.obj x) ⟶ M.lift.map r ≫ M.lift.map e)
    (eps : M.lift.map r ≫ M.lift.map e ⟶ 𝟙 (M.lift.obj x))
    (w : M.lift.map e ≫ M.lift.map e' ⟶ M.lift.map e ≫ M.lift.map e')
    {p₁ d₁ c₁ : x ⟶ x} {q₁ : x ⟶ z} (σp₁ : p₁ ≅ 𝟙 x) (σq₁ : q₁ ≅ e') (σd₁ : d₁ ≅ 𝟙 x)
    (σc₁ : c₁ ≅ r ≫ e) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = u)
    {p₂ : x ⟶ y} {q₂ : z ⟶ z} {d₂ c₂ : y ⟶ z} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ 𝟙 z)
    (σd₂ : d₂ ≅ e ≫ e') (σc₂ : c₂ ≅ e ≫ e') (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ d₃ c₃ : x ⟶ x} {q₃ : x ⟶ z} (σp₃ : p₃ ≅ 𝟙 x) (σq₃ : q₃ ≅ e') (σd₃ : d₃ ≅ r ≫ e)
    (σc₃ : c₃ ≅ 𝟙 x) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = eps)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ z}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ e') (F₁ : e' ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ curlG u eps w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (𝟙 x) e' (x := 𝟙 x) (y := r ≫ e) u ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ r e e').hom ≫ r ◁ (ρ_ (e ≫ e')).inv) ≫
      midK M r (𝟙 z) (x := e ≫ e') (y := e ≫ e') w ≫
        M.lift.map₂ (r ◁ (ρ_ (e ≫ e')).hom ≫ (α_ r e e').inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 x) e' (x := r ≫ e) (y := 𝟙 x) eps =
      M.lift.map₂ ((λ_ _).hom ≫ (λ_ e').hom) ≫ curlG u eps w ≫
        M.lift.map₂ ((λ_ e').inv ≫ (λ_ _).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      lift_map₂_rightUnitor_inv, lift_map₂_rightUnitor_hom, lift_map_comp]
    exact curl_aux u eps w
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ r e e').hom ≫ r ◁ (ρ_ (e ≫ e')).inv),
    lift_map₂_eq M _ (r ◁ (ρ_ (e ≫ e')).hom ≫ (α_ r e e').inv ≫ (λ_ _).inv), reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

omit M in
/-- The curl `curlEG` of `w`, read as the composite "cup on the left, `w`, cap" of three whiskered
layers, in an arbitrary bicategory. -/
theorem curlL_aux {a b c : C} {Em : a ⟶ b} {Ep : b ⟶ c} {Rp : c ⟶ b} (u : 𝟙 b ⟶ Ep ≫ Rp)
    (eps : Ep ≫ Rp ⟶ 𝟙 b) (w : Em ≫ Ep ⟶ Em ≫ Ep) :
    Em ◁ (u ▷ 𝟙 b) ≫ (Em ◁ (ρ_ (Ep ≫ Rp)).hom ≫ (α_ Em Ep Rp).inv ≫ (λ_ _).inv) ≫
        𝟙 a ◁ (w ▷ Rp) ≫ ((λ_ _).hom ≫ (α_ Em Ep Rp).hom ≫ Em ◁ (ρ_ (Ep ≫ Rp)).inv) ≫
          Em ◁ (eps ▷ 𝟙 b) =
      (Em ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ Em).hom) ≫ curlEG u eps w ≫
        ((ρ_ Em).inv ≫ Em ◁ (λ_ (𝟙 b)).inv) := by
  unfold curlEG
  bicategory

/-- **A left curl in normal form**: a strand `em` with a cup (`u`, on the new strands `ep`, `rp`)
on its left, a generator image `w` on `em ≫ ep`, and a cap (`eps`) closing `ep ≫ rp`, all
conjugated by images of free 2-morphisms, is the curl `curlEG u eps w`. -/
theorem curlL_key {x y z : FB S} {em : x ⟶ y} {ep : y ⟶ z} {rp : z ⟶ y}
    (u : 𝟙 (M.lift.obj y) ⟶ M.lift.map ep ≫ M.lift.map rp)
    (eps : M.lift.map ep ≫ M.lift.map rp ⟶ 𝟙 (M.lift.obj y))
    (w : M.lift.map em ≫ M.lift.map ep ⟶ M.lift.map em ≫ M.lift.map ep)
    {p₁ : x ⟶ y} {q₁ d₁ c₁ : y ⟶ y} (σp₁ : p₁ ≅ em) (σq₁ : q₁ ≅ 𝟙 y) (σd₁ : d₁ ≅ 𝟙 y)
    (σc₁ : c₁ ≅ ep ≫ rp) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = u)
    {p₂ : x ⟶ x} {q₂ : z ⟶ y} {d₂ c₂ : x ⟶ z} (σp₂ : p₂ ≅ 𝟙 x) (σq₂ : q₂ ≅ rp)
    (σd₂ : d₂ ≅ em ≫ ep) (σc₂ : c₂ ≅ em ≫ ep) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ : x ⟶ y} {q₃ d₃ c₃ : y ⟶ y} (σp₃ : p₃ ≅ em) (σq₃ : q₃ ≅ 𝟙 y) (σd₃ : d₃ ≅ ep ≫ rp)
    (σc₃ : c₃ ≅ 𝟙 y) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = eps)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ y}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ em) (F₁ : em ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ curlEG u eps w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M em (𝟙 y) (x := 𝟙 y) (y := ep ≫ rp) u ≫
      M.lift.map₂ (em ◁ (ρ_ (ep ≫ rp)).hom ≫ (α_ em ep rp).inv ≫ (λ_ _).inv) ≫
      midK M (𝟙 x) rp (x := em ≫ ep) (y := em ≫ ep) w ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ em ep rp).hom ≫ em ◁ (ρ_ (ep ≫ rp)).inv) ≫
        midK M em (𝟙 y) (x := ep ≫ rp) (y := 𝟙 y) eps =
      M.lift.map₂ (em ◁ (λ_ (𝟙 y)).hom ≫ (ρ_ em).hom) ≫ curlEG u eps w ≫
        M.lift.map₂ ((ρ_ em).inv ≫ em ◁ (λ_ (𝟙 y)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      lift_map₂_rightUnitor_inv, lift_map₂_rightUnitor_hom, lift_map_comp]
    exact curlL_aux u eps w
  rw [lift_map₂_eq M _ (em ◁ (ρ_ (ep ≫ rp)).hom ≫ (α_ em ep rp).inv ≫ (λ_ _).inv),
    lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ em ep rp).hom ≫ em ◁ (ρ_ (ep ≫ rp)).inv),
    reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

section LinearWhisker

open CategoryTheory.Limits
open scoped ZeroObject

variable {R : Type*} [CommRing R] [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear R]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear R]
  [∀ a b : C, Limits.HasZeroObject (a ⟶ b)]

variable {M}

set_option backward.isDefEq.respectTransparency false in
/-- **The image of a whiskered linear combination of diagrams**: the image of `u ⊗ f ⊗ v`, after
transport to images of words, is the image of `f` whiskered by the images of `v` and `u`,
conjugated by the splittings of the words. -/
theorem conj_freeLift_whisker (G : GenImg M) {s t : S.Region} {a b u : Obj S}
    {v : List S.Colour} (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s)
    (hvv : S.ok t v) (hw : a.WhiskerOK u v) (ha : Cond s t a) (hb : Cond s t b)
    (hwa : Cond u.start (S.endR t v) (a.whisker u v))
    (hwb : Cond u.start (S.endR t v) (b.whisker u v)) (f : LinDiagram R a b) :
    eqToHom (objI_pos _ _ hwa).symm ≫
        (freeLift R (interp G u.start (S.endR t v)).functor).map (LinDiagram.whisker f u v hw) ≫
        eqToHom (objI_pos _ _ hwb) =
      M.lift.map₂ (splitW hu hue hvv a ha).hom ≫
        midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
          (eqToHom (objI_pos _ _ ha).symm ≫ (freeLift R (interp G s t).functor).map f ≫
            eqToHom (objI_pos _ _ hb)) ≫
        M.lift.map₂ (splitW hu hue hvv b hb).inv := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [LinDiagram.whisker_zero, Functor.map_zero, Functor.map_zero]
    simp only [Limits.zero_comp, Limits.comp_zero, midK_zero]
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, Functor.map_add, Functor.map_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add, midK_add, hf, hg]
  | single d r =>
    rw [freeLift_map_whisker_single, freeLift_map_single]
    simp only [Linear.smul_comp, Linear.comp_smul, midK_smul]
    congr 1
    exact mapChain_whisker G hu hue hvv d.1 _ rfl a (a.whisker u v) b rfl d.2
      (Diagram.whisker d u v hw).2 ha hb hwa hwb _ _

end LinearWhisker

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

variable (S : StrongSl2 k B)

attribute [local irreducible] KL3.Diagram.sh

set_option maxHeartbeats 4000000 in
/-- The image of the right curl `curlR` (KL III; CL `eq_reduction-*`): the curl `curlG` of the
crossing, closed with the left cup and the right cap. -/
theorem img_curlR (lam : ℤ)
    (hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + lam) lam
      (ob sl2RootDatum lam [up ()])) :
    eqToHom (objI_pos _ _ hc).symm ≫
        (interp (genImg S) (sh sl2RootDatum (up ()) + lam) lam).functor.map
          (KL3.Diagram.curlR sl2RootDatum () lam) ≫
        eqToHom (objI_pos _ _ hc) =
      curlG (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit
        (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).counit
        (S.gCross (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, KL3.Diagram.curlR, mkD, Diagram.layers_mk,
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
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_cross', hx]
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
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up', sig0_colourTgt', sig0_colourSrc']
    refine (curl_key S.model
      (r := FreeBicategory.Hom.of (⟨⟨dn (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (dn ()) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (dn ()) + x⟩, rfl, hx⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (dn ()) + x) ⟶ rq x))
      (e' := FreeBicategory.Hom.of (⟨⟨up (), x⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) x ⟶ rq (sh sl2RootDatum (up ()) + x)))
      (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x)).unit
      (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x) (S.qi_sh_false () x)).counit
      (S.gCross (S.qi (sh sl2RootDatum (dn ()) + x)) (S.qi x)
        (S.qi (sh sl2RootDatum (up ()) + x)) (S.qi_sh_false () x) (S.qi_sh_true () x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (eqToIso (comp_of_congr rfl (congrArg (Col.mk (dn ())) hx) rfl)) _ ?hg1
      (Iso.refl _) (Iso.refl _)
      (eqToIso ?hd2) (eqToIso ?hc2) _ ?hg2
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case hg1 =>
      simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp, eqToIso.hom,
        lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.comp_id]
      exact genImg_cup_true S () _ _ _ _ _ _ _
    case hd2 | hc2 =>
      exact comp_of_congr hx rfl (congrArg (Col.mk (up ())) hx)
    case hg2 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      exact S.gCross_congr _ _ _ _ (congrArg S.qi hx) _ _ _ _ _ _
    case hg3 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      exact genImg_cap_false S () _ _ _ _ _ _ _
    case fin =>
      simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, hx, sig0_dom_cross',
    sig0_cod_cross']

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem ip_sl2 (lam : ℤ) : ip sl2RootDatum () lam = lam := by
  simp [ip, sl2RootDatum]

/-- The images of the linear combinations of diagrams from `1_λ` to itself, as a ring
homomorphism to the endomorphisms of `𝟙` at the object of `λ`. -/
def bubHom (lam : ℤ) : LEnd sl2RootDatum k (ob sl2RootDatum lam []) →+*
    End (𝟙 (of (S.obj (S.qi lam)))) where
  toFun f := (eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
    (freeLift k (interp (genImg S) lam lam).functor).map f ≫
      eqToHom (objI_pos _ _ (cond_nil lam)) : _)
  map_one' := by
    change eqToHom _ ≫ (freeLift k (interp (genImg S) lam lam).functor).map (𝟙 _) ≫
      eqToHom _ = 𝟙 _
    set_option backward.isDefEq.respectTransparency false in
    rw [CategoryTheory.Functor.map_id]
    set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.add_comp, Preadditive.comp_add]
  map_mul' f g := by
    change eqToHom _ ≫ (freeLift k (interp (genImg S) lam lam).functor).map (g ≫ f) ≫
      eqToHom _ = (eqToHom _ ≫ _ ≫ eqToHom _) ≫ (eqToHom _ ≫ _ ≫ eqToHom _)
    set_option backward.isDefEq.respectTransparency false in
    rw [CategoryTheory.Functor.map_comp]
    set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.add_comp, Preadditive.comp_add]
  map_zero' := by
    change eqToHom _ ≫ (freeLift k (interp (genImg S) lam lam).functor).map 0 ≫
      eqToHom _ = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_zero]
    set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.add_comp, Preadditive.comp_add]
  map_add' f g := by
    change eqToHom _ ≫ (freeLift k (interp (genImg S) lam lam).functor).map (f + g) ≫
      eqToHom _ = (eqToHom _ ≫ _ ≫ eqToHom _) + (eqToHom _ ≫ _ ≫ eqToHom _)
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_add]
    set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.add_comp, Preadditive.comp_add]

theorem bubHom_apply (lam : ℤ) (f : LEnd sl2RootDatum k (ob sl2RootDatum lam [])) :
    bubHom S lam f = (eqToHom (objI_pos _ _ (cond_nil lam)).symm ≫
      (freeLift k (interp (genImg S) lam lam).functor).map f ≫
        eqToHom (objI_pos _ _ (cond_nil lam)) : _) := rfl

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The infinite Grassmannian recursion commutes with ring homomorphisms. -/
theorem map_grassInv {A A' : Type*} [Ring A] [Ring A'] (φ : A →+* A') (c : ℕ → A) (n : ℕ) :
    φ (Categorification.KL3.Diagram.grassInv c n) =
      Categorification.TwoRep.grassInv (fun j => φ (c j)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [Categorification.KL3.Diagram.grassInv_zero, Categorification.TwoRep.grassInv_zero,
        map_one]
    | succ n =>
      rw [Categorification.KL3.Diagram.grassInv_succ, Categorification.TwoRep.grassInv_succ,
        map_neg, map_sum, ← Fin.sum_univ_eq_sum_range
          (fun a => φ (c (a + 1)) * Categorification.TwoRep.grassInv (fun j => φ (c j)) (n - a))]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ih _ (by omega)]

theorem bubHom_cwReal (lam : ℤ) (j : ℕ) :
    bubHom S lam (LinDiagram.of (cwReal sl2RootDatum lam () j)) =
      (gAdjL S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam) (S.qi_sh_false () lam)).unit ≫
        powComp (gDotR S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)) j ▷ S.gEc (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
            (S.qi_sh_false () lam) ≫
        (S.gAdjE (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi_sh_false () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [bubHom_apply, freeLift_map_of]
  exact img_cwReal S lam j

theorem bubHom_ccwReal (lam : ℤ) (j : ℕ) :
    bubHom S lam (LinDiagram.of (ccwReal sl2RootDatum lam () j)) =
      (S.gAdjE (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam)).unit ≫
        powComp (S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)) j ▷ S.gRc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
            (S.qi_sh_true () lam) ≫
        (gAdjL S (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam)).counit := by
  set_option backward.isDefEq.respectTransparency false in
  rw [bubHom_apply, freeLift_map_of]
  exact img_ccwReal S lam j

/-- The clockwise bubble with `j` dots of the model, between the objects `a`, `b = a + 1`. -/
def mcw (a b : ℤ) (h : a + 1 = b) (j : ℕ) : End (𝟙 (of (S.obj b))) :=
  (gAdjL S a b h).unit ≫ powComp (gDotR S a b h) j ▷ S.gEc a b h ≫ (S.gAdjE a b h).counit

/-- The counter-clockwise bubble with `j` dots of the model, between the objects `b`,
`c = b + 1`. -/
def mccw (b c : ℤ) (h : b + 1 = c) (j : ℕ) : End (𝟙 (of (S.obj b))) :=
  (S.gAdjE b c h).unit ≫ powComp (S.gDot b c h) j ▷ S.gRc b c h ≫ (gAdjL S b c h).counit

/-- The clockwise bubble with label `m ∈ ℤ` of the model at the object `b` of weight `n`. -/
def mcwL (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n m : ℤ) : End (𝟙 (of (S.obj b))) :=
  if 0 ≤ m then mcw S a b h m.toNat
  else if 0 ≤ m + 1 - n then
    Categorification.TwoRep.grassInv
      (fun x => if 0 ≤ -n - 1 + (x : ℤ) then mccw S b c h' (-n - 1 + (x : ℤ)).toNat else 0)
      (m + 1 - n).toNat
  else 0

theorem mcwL_eq (a m : ℤ) :
    mcwL S a (a + 1) (a + 1 + 1) rfl rfl (S.wt (a + 1)) m = S.cwLN a m := by
  unfold mcwL mcw mccw
  simp only [cwImg_eq, ccwImg_eq, StrongSl2.cwL, StrongSl2.ccwR]

theorem bubHom_cwL (lam m : ℤ) :
    bubHom S lam (KL3.Diagram.cwL sl2RootDatum k lam () m) =
      mcwL S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
        (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)
        lam m := by
  unfold KL3.Diagram.cwL mcwL
  simp only [ip_sl2]
  split_ifs with h1 h2
  · exact bubHom_cwReal S lam _
  · rw [map_grassInv]
    congr 1
    funext x
    unfold KL3.Diagram.ccwR
    split_ifs
    · exact bubHom_ccwReal S lam _
    · exact map_zero _
  · exact map_zero _

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The image of a retyped linear combination of diagrams. -/
theorem freeLift_map_cast' {D : Type*} [Category D] [Preadditive D] [Linear k D]
    (F : Obj (psig sl2RootDatum) ⥤ D) {a b a' b' : Obj (psig sl2RootDatum)}
    (f : LinDiagram k a b) (ha : a = a') (hb : b = b') :
    (freeLift k F).map (LinDiagram.cast f ha hb) =
      eqToHom (congrArg F.obj ha.symm) ≫ (freeLift k F).map f ≫ eqToHom (congrArg F.obj hb) := by
  subst ha hb
  simp only [LinDiagram.cast_rfl, eqToHom_refl, Category.id_comp]
  exact (Category.comp_id _).symm

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem bubL_aux {C : Type*} [Bicategory C] {a c : C} (E : a ⟶ c) (g : 𝟙 a ⟶ 𝟙 a) :
    (λ_ E).inv ≫ (λ_ (𝟙 a ≫ E)).inv ≫ 𝟙 a ◁ (g ▷ E) ≫ (λ_ (𝟙 a ≫ E)).hom ≫ (λ_ E).hom =
      (λ_ E).inv ≫ g ▷ E ≫ (λ_ E).hom := by
  simp

set_option maxHeartbeats 2000000 in
/-- The image of an endomorphism of `1_λ` placed to the right of an upward strand. -/
theorem img_bubR (lam : ℤ)
    (hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + lam) lam
      (ob sl2RootDatum lam [up ()]))
    (b : LEnd sl2RootDatum k (ob sl2RootDatum lam [])) :
    eqToHom (objI_pos _ _ hc).symm ≫
        (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + lam) lam).functor).map
          (bubR sl2RootDatum k lam [up ()] b) ≫
        eqToHom (objI_pos _ _ hc) =
      (λ_ (S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam))).inv ≫
        bubHom S lam b ▷
          S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ≫
        (λ_ (S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam))).hom := by
  have hu : (psig sl2RootDatum).ok (ob sl2RootDatum lam [up ()]).start
      (ob sl2RootDatum lam [up ()]).word := hc.1
  have hw : (ob sl2RootDatum lam []).WhiskerOK (ob sl2RootDatum lam [up ()]) [] :=
    whiskerOK_right sl2RootDatum lam [up ()]
  have hwa : Cond (S := psig sl2RootDatum) (ob sl2RootDatum lam [up ()]).start
      ((psig sl2RootDatum).endR lam [])
      ((ob sl2RootDatum lam []).whisker (ob sl2RootDatum lam [up ()]) []) :=
    (cond_nil lam).whisker hu rfl trivial
  have key := conj_freeLift_whisker (genImg S) (s := lam) (t := lam) (v := []) hu rfl trivial hw
    (cond_nil lam) (cond_nil lam) hwa hwa b
  unfold bubR
  set_option backward.isDefEq.respectTransparency false in
  rw [freeLift_map_cast']
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · set_option backward.isDefEq.respectTransparency false in
    rw [lift_map₂_eq S.model (splitW _ _ _ _ _).hom ((λ_ _).inv ≫ (λ_ _).inv),
      lift_map₂_eq S.model (splitW _ _ _ _ _).inv ((λ_ _).hom ≫ (λ_ _).hom)]
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_leftUnitor_inv, lift_map₂_leftUnitor_hom,
      Category.assoc]
    exact bubL_aux _ _

set_option maxHeartbeats 2000000 in
/-- The image of a dot on an upward strand. -/
theorem img_dotUp (lam : ℤ)
    (hc : Cond (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + lam) lam
      (ob sl2RootDatum lam [up ()])) :
    eqToHom (objI_pos _ _ hc).symm ≫
        (interp (genImg S) (sh sl2RootDatum (up ()) + lam) lam).functor.map
          (mkD sl2RootDatum lam [([], .dot (up ()), [])] ⟨rfl, rfl⟩) ≫
        eqToHom (objI_pos _ _ hc) =
      S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  case c1 => exact hc
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  try rw [eqToHom_word ?w1 _]
  · unfold coreC core
    refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _)) _ _ _ _ _ (eqToHom ?e)
      (eqToHom ?e')).trans ?main
    case main =>
      set_option backward.isDefEq.respectTransparency false in
      rw [layerAt_whole]
      simp only [lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      erw [genImg_dot_true S]
      rfl
    case e => rfl
    case e' => rfl
  all_goals simp [Layer.cod, Layer.dom, ob, sig0_dom_dot']

/-- The right curl relation at the level of the model (CL `eq_reduction-*`, KL III `curlR`, with
`r_i = 1`), for the objects `a`, `b = a + 1`, `c = b + 1`, `b` of weight `n`. -/
theorem curlG_model (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n : ℤ) (hn : S.wt b = n) :
    curlG (gAdjL S a b h).unit (S.gAdjE a b h).counit (S.gCross a b c h h') =
      -∑ f ∈ Finset.range (-n + 1).toNat,
        ((λ_ (S.gEc b c h')).inv ≫ mcwL S a b c h h' n (n - 1 + f) ▷ S.gEc b c h' ≫
          (λ_ (S.gEc b c h')).hom) ≫ powComp (S.gDot b c h') (-n - f).toNat := by
  subst h h' hn
  simp only [mcwL_eq]
  dsimp only [gAdjL_rfl, gAdjE_rfl, gCross_rfl, gEc_rfl, gDot_rfl]
  rw [grAdj_counit]
  rcases le_or_gt (S.wt (a + 1)) 0 with hn | hn
  · refine (S.curlG_eq hn).trans ?_
    rw [show (-S.wt (a + 1) + 1).toNat = (-S.wt (a + 1)).toNat + 1 by omega]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mem_range] at hf
    rw [show (-S.wt (a + 1) - f).toNat = (-S.wt (a + 1)).toNat - f by omega]
    rfl
  · refine (S.curlG_eq_zero hn).trans ?_
    rw [show (-S.wt (a + 1) + 1).toNat = 0 by omega, Finset.range_zero]
    exact (neg_eq_zero.2 Finset.sum_empty).symm

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cond_up (lam : ℤ) :
    Cond (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + lam) lam
      (ob sl2RootDatum lam [up ()]) :=
  ⟨⟨rfl, trivial⟩, rfl, rfl⟩

/-- The image of a term of the right-hand side of the right curl relation. -/
theorem img_curlRHS_term (lam : ℤ) (f : ℕ) :
    eqToHom (objI_pos _ _ (cond_up lam)).symm ≫
        (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + lam) lam).functor).map
          (bubR sl2RootDatum k lam [up ()]
              (KL3.Diagram.cwL sl2RootDatum k lam () (ip sl2RootDatum () lam - 1 + f)) ≫
            LinDiagram.of (dots sl2RootDatum lam [] (up ()) [] (-ip sl2RootDatum () lam - f).toNat)) ≫
        eqToHom (objI_pos _ _ (cond_up lam)) =
      ((λ_ (S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam))).inv ≫
        mcwL S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
          (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)
          lam (lam - 1 + f) ▷
          S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam) ≫
        (λ_ (S.gEc (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam))
          (S.qi_sh_true () lam))).hom) ≫
        powComp (S.gDot (S.qi lam) (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_true () lam))
          (-lam - f).toNat := by
  set_option backward.isDefEq.respectTransparency false in
  rw [CategoryTheory.Functor.map_comp, conj_comp_conj (objI_pos _ _ (cond_up lam))
      (objI_pos _ _ (cond_up lam)) (objI_pos _ _ (cond_up lam)), img_bubR S lam (cond_up lam),
    bubHom_cwL,
    freeLift_map_of, ip_sl2]
  erw [img_dots S lam [] (up ()) [] (cond_up lam), img_dotUp S lam (cond_up lam)]

/-- **The right curl relation in the `sl₂` model** (KL III `curlR`; CL `eq_reduction-ngeqz`,
`eq_reduction-nleqz` with `r_i = 1`), in the regions of the right parity. -/
theorem rel_curlR {lam : ℤ} (hpar : ∃ q : ℤ, lam = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + lam) lam).functor).map
      (LinDiagram.of (KL3.Diagram.curlR sl2RootDatum () lam) -
        KL3.Diagram.curlRHS sl2RootDatum k () lam) = 0 := by
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_up lam)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_up lam)))).1
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sub, freeLift_map_of]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Limits.comp_zero, Limits.zero_comp,
    Category.assoc]
  rw [sub_eq_zero, img_curlR S lam (cond_up lam)]
  unfold KL3.Diagram.curlRHS
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_neg, Functor.map_sum]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.sum_comp,
    Preadditive.comp_sum, Category.assoc, img_curlRHS_term]
  rw [ip_sl2]
  refine (curlG_model S _ _ _ _ _ lam (S.wt_qi hpar)).trans ?_
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc]

set_option maxHeartbeats 4000000 in
/-- The image of the left curl `curlL` (KL III; CL `eq_reduction-*`): the curl `curlEG` of the
crossing, closed with the right cup and the left cap. -/
theorem img_curlL (μ : ℤ) :
    eqToHom (objI_pos _ _ (cond_up μ)).symm ≫
        (interp (genImg S) (sh sl2RootDatum (up ()) + μ) μ).functor.map
          (KL3.Diagram.curlL sl2RootDatum () μ) ≫
        eqToHom (objI_pos _ _ (cond_up μ)) =
      curlEG (S.gAdjE (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)))
          (S.qi_sh_true () _)).unit
        (gAdjL S (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)))
          (S.qi_sh_true () _)).counit
        (S.gCross (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ))) (S.qi_sh_true () μ)
          (S.qi_sh_true () _)) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, KL3.Diagram.curlL, mkD, Diagram.layers_mk,
    layList_cons, layList_nil, Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom, dual_up', dual_dn']
  generalize_proofs
  generalize hy : sh sl2RootDatum (dn ()) +
    (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)) = y at *
  have hyμ : y = sh sl2RootDatum (up ()) + μ := by rw [← hy]; exact sh_false_sh_true () _
  subst hyμ
  rw [layerI_pos _ _ _ _ ?c1, layerI_pos _ _ _ _ ?c2, layerI_pos _ _ _ _ ?c3]
  case c1 | c2 | c3 =>
    refine ⟨?_, ?_, rfl⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, inv_dual, sh_true_sh_false, Letter.dual,
        sig0_colourSrc', sig0_colourTgt', sig0_dom_cross', hy]
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
    refine (curlL_key S.model
      (em := FreeBicategory.Hom.of (⟨⟨up (), μ⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) μ ⟶ rq (sh sl2RootDatum (up ()) + μ)))
      (ep := FreeBicategory.Hom.of (⟨⟨up (), sh sl2RootDatum (up ()) + μ⟩, rfl, rfl⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + μ) ⟶
          rq (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ))))
      (rp := FreeBicategory.Hom.of (⟨⟨dn (), sh sl2RootDatum (up ()) +
          (sh sl2RootDatum (up ()) + μ)⟩, rfl, sh_false_sh_true () _⟩ :
        rq (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)) ⟶
          rq (sh sl2RootDatum (up ()) + μ)))
      (S.gAdjE (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)))
          (S.qi_sh_true () _)).unit
      (gAdjL S (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ)))
          (S.qi_sh_true () _)).counit
      (S.gCross (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ))) (S.qi_sh_true () μ)
          (S.qi_sh_true () _))
      (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
      (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
      (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case e4 => exact comp_of_congr rfl (congrArg (Col.mk (up ())) (sh_false_sh_true () _)) rfl
    case e1 | e2 | e3 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 => rfl
    case hg1 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      exact genImg_cup_false S () _ _ _ _ _ _ _
    case hg2 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      exact genImg_cross_true S _ _ _ _ _ _ _ _ _
    case hg3 =>
      simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, eqToHom_refl, PrelaxFunctor.map₂_id, Category.id_comp,
        Category.comp_id]
      exact genImg_cap_true S () _ _ _ _ _ _ _
    case fin =>
      simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  all_goals simp [Layer.cod, Layer.dom, ob, inv_dual, Letter.dual, hy, sig0_dom_cross',
    sig0_cod_cross']

/-- The counter-clockwise bubble with label `m ∈ ℤ` of the model at the object `b` of weight
`n`. -/
def mccwL (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n m : ℤ) : End (𝟙 (of (S.obj b))) :=
  if 0 ≤ m then mccw S b c h' m.toNat
  else if 0 ≤ m + 1 + n then
    Categorification.TwoRep.grassInv
      (fun x => if 0 ≤ n - 1 + (x : ℤ) then mcw S a b h (n - 1 + (x : ℤ)).toNat else 0)
      (m + 1 + n).toNat
  else 0

theorem mccwL_eq (a m : ℤ) :
    mccwL S a (a + 1) (a + 1 + 1) rfl rfl (S.wt (a + 1)) m = S.ccwLN a m := by
  unfold mccwL mcw mccw
  simp only [cwImg_eq, ccwImg_eq, StrongSl2.ccwL, StrongSl2.cwR]

theorem mccwL_congr {a a' : ℤ} (ha : a = a') (b c : ℤ) (h : a + 1 = b) (h₂ : a' + 1 = b)
    (h' : b + 1 = c) (n m : ℤ) : mccwL S a b c h h' n m = mccwL S a' b c h₂ h' n m := by
  subst ha; rfl

theorem bubHom_ccwL (lam m : ℤ) :
    bubHom S lam (KL3.Diagram.ccwL sl2RootDatum k lam () m) =
      mccwL S (S.qi (sh sl2RootDatum (dn ()) + lam)) (S.qi lam)
        (S.qi (sh sl2RootDatum (up ()) + lam)) (S.qi_sh_false () lam) (S.qi_sh_true () lam)
        lam m := by
  unfold KL3.Diagram.ccwL mccwL
  simp only [ip_sl2]
  split_ifs with h1 h2
  · exact bubHom_ccwReal S lam _
  · rw [map_grassInv]
    congr 1
    funext x
    unfold KL3.Diagram.cwR
    split_ifs
    · exact bubHom_cwReal S lam _
    · exact map_zero _
  · exact map_zero _

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem bubR_aux {C : Type*} [Bicategory C] {a c : C} (E : a ⟶ c) (g : 𝟙 c ⟶ 𝟙 c) :
    (ρ_ E).inv ≫ E ◁ (λ_ (𝟙 c)).inv ≫ E ◁ (g ▷ 𝟙 c) ≫ E ◁ (λ_ (𝟙 c)).hom ≫ (ρ_ E).hom =
      (ρ_ E).inv ≫ E ◁ g ≫ (ρ_ E).hom := by
  simp only [← Bicategory.whiskerLeft_comp_assoc]
  simp

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- A bubble on the target side of a strand commutes with endomorphisms of the strand. -/
theorem rbub_comm {C : Type*} [Bicategory C] {a c : C} {E : a ⟶ c} (g : 𝟙 c ⟶ 𝟙 c)
    (f : E ⟶ E) :
    ((ρ_ E).inv ≫ E ◁ g ≫ (ρ_ E).hom) ≫ f = f ≫ (ρ_ E).inv ≫ E ◁ g ≫ (ρ_ E).hom := by
  simp only [Category.assoc]
  rw [← rightUnitor_naturality, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

set_option maxHeartbeats 2000000 in
/-- The image of an endomorphism of `1_{μ + i_X}` placed to the left of an upward strand. -/
theorem img_bubL (μ : ℤ)
    (b : LEnd sl2RootDatum k (ob sl2RootDatum (KL3.Diagram.wt sl2RootDatum μ [up ()]) [])) :
    eqToHom (objI_pos _ _ (cond_up μ)).symm ≫
        (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + μ) μ).functor).map
          (bubL sl2RootDatum k μ [up ()] b) ≫
        eqToHom (objI_pos _ _ (cond_up μ)) =
      (ρ_ (S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ)) (S.qi_sh_true () μ))).inv ≫
        S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ)) (S.qi_sh_true () μ) ◁
          bubHom S (sh sl2RootDatum (up ()) + μ) b ≫
        (ρ_ (S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi_sh_true () μ))).hom := by
  have hw : (ob sl2RootDatum (KL3.Diagram.wt sl2RootDatum μ [up ()]) []).WhiskerOK
      (ob sl2RootDatum (KL3.Diagram.wt sl2RootDatum μ [up ()]) [])
      (wd sl2RootDatum μ [up ()]) :=
    whiskerOK_left sl2RootDatum μ [up ()]
  have hwa : Cond (S := psig sl2RootDatum) (sh sl2RootDatum (up ()) + μ)
      ((psig sl2RootDatum).endR (sh sl2RootDatum (up ()) + μ) (wd sl2RootDatum μ [up ()]))
      ((ob sl2RootDatum (KL3.Diagram.wt sl2RootDatum μ [up ()]) []).whisker
        (ob sl2RootDatum (KL3.Diagram.wt sl2RootDatum μ [up ()]) [])
        (wd sl2RootDatum μ [up ()])) :=
    (cond_nil (sh sl2RootDatum (up ()) + μ)).whisker
      (u := ob sl2RootDatum (sh sl2RootDatum (up ()) + μ) []) trivial rfl (cond_up μ).1
  have key := conj_freeLift_whisker (genImg S) (s := sh sl2RootDatum (up ()) + μ)
    (t := sh sl2RootDatum (up ()) + μ) (u := ob sl2RootDatum (sh sl2RootDatum (up ()) + μ) [])
    (v := wd sl2RootDatum μ [up ()]) trivial rfl (cond_up μ).1 hw
    (cond_nil _) (cond_nil _) hwa hwa b
  unfold bubL
  set_option backward.isDefEq.respectTransparency false in
  rw [freeLift_map_cast']
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · set_option backward.isDefEq.respectTransparency false in
    rw [lift_map₂_eq S.model (splitW _ _ _ _ _).hom ((ρ_ _).inv ≫ _ ◁ (λ_ _).inv),
      lift_map₂_eq S.model (splitW _ _ _ _ _).inv (_ ◁ (λ_ _).hom ≫ (ρ_ _).hom)]
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_rightUnitor_inv,
      lift_map₂_rightUnitor_hom, lift_map₂_whiskerLeft, lift_map₂_leftUnitor_inv,
      lift_map₂_leftUnitor_hom, Category.assoc]
    exact bubR_aux _ _

/-- The left curl relation at the level of the model (CL `eq_reduction-*`, KL III `curlL`, with
`r_i = 1`), for the objects `a`, `b = a + 1`, `c = b + 1`, `b` of weight `n`. -/
theorem curlE_model (a b c : ℤ) (h : a + 1 = b) (h' : b + 1 = c) (n : ℤ) (hn : S.wt b = n) :
    curlE (S.gAdjE b c h') (gAdjL S b c h') (S.gCross a b c h h') =
      ∑ g ∈ Finset.range (n + 1).toNat,
        ((ρ_ (S.gEc a b h)).inv ≫ S.gEc a b h ◁ mccwL S a b c h h' n (-n - 1 + g) ≫
          (ρ_ (S.gEc a b h)).hom) ≫ powComp (S.gDot a b h) (n - g).toNat := by
  subst h h' hn
  simp only [mccwL_eq]
  rcases le_or_gt 0 (S.wt (a + 1)) with hn | hn
  · refine (S.curlE_eq hn).trans ?_
    rw [show (S.wt (a + 1) + 1).toNat = (S.wt (a + 1)).toNat + 1 by omega]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.mem_range] at hg
    rw [show (S.wt (a + 1) - g).toNat = (S.wt (a + 1)).toNat - g by omega]
    exact (rbub_comm _ _).symm
  · refine (S.curlE_eq_zero hn).trans ?_
    rw [show (S.wt (a + 1) + 1).toNat = 0 by omega, Finset.range_zero]
    exact Finset.sum_empty.symm

/-- The image of a term of the right-hand side of the left curl relation. -/
theorem img_curlLHS_term (μ : ℤ) (g : ℕ) :
    eqToHom (objI_pos _ _ (cond_up μ)).symm ≫
        (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + μ) μ).functor).map
          (bubL sl2RootDatum k μ [up ()]
              (KL3.Diagram.ccwL sl2RootDatum k (KL3.Diagram.wt sl2RootDatum μ [up ()]) ()
                (-ip sl2RootDatum () (KL3.Diagram.wt sl2RootDatum μ [up ()]) - 1 + g)) ≫
            LinDiagram.of (dots sl2RootDatum μ [] (up ()) []
              (ip sl2RootDatum () (KL3.Diagram.wt sl2RootDatum μ [up ()]) - g).toNat)) ≫
        eqToHom (objI_pos _ _ (cond_up μ)) =
      ((ρ_ (S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ)) (S.qi_sh_true () μ))).inv ≫
        S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ)) (S.qi_sh_true () μ) ◁
          mccwL S (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ))
            (S.qi (sh sl2RootDatum (up ()) + (sh sl2RootDatum (up ()) + μ))) (S.qi_sh_true () μ)
            (S.qi_sh_true () _) (sh sl2RootDatum (up ()) + μ)
            (-(sh sl2RootDatum (up ()) + μ) - 1 + g) ≫
        (ρ_ (S.gEc (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ))
          (S.qi_sh_true () μ))).hom) ≫
        powComp (S.gDot (S.qi μ) (S.qi (sh sl2RootDatum (up ()) + μ)) (S.qi_sh_true () μ))
          (sh sl2RootDatum (up ()) + μ - g).toNat := by
  set_option backward.isDefEq.respectTransparency false in
  rw [CategoryTheory.Functor.map_comp, conj_comp_conj (objI_pos _ _ (cond_up μ))
      (objI_pos _ _ (cond_up μ)) (objI_pos _ _ (cond_up μ)), img_bubL S μ,
    freeLift_map_of]
  erw [bubHom_ccwL, ip_sl2]
  erw [img_dots S μ [] (up ()) [] (cond_up μ), img_dotUp S μ (cond_up μ)]
  rw [mccwL_congr S (congrArg S.qi (sh_false_sh_true () μ))]
  rfl

/-- **The left curl relation in the `sl₂` model** (KL III `curlL`; CL `eq_reduction-ngeqz`,
`eq_reduction-nleqz` with `r_i = 1`), in the regions of the right parity. -/
theorem rel_curlL {μ : ℤ} (hpar : ∃ q : ℤ, μ = S.n₀ + 2 * q) :
    (freeLift k (interp (genImg S) (sh sl2RootDatum (up ()) + μ) μ).functor).map
      (LinDiagram.of (KL3.Diagram.curlL sl2RootDatum () μ) -
        KL3.Diagram.curlLHS sl2RootDatum k () μ) = 0 := by
  have hpar' : ∃ q : ℤ, sh sl2RootDatum (up ()) + μ = S.n₀ + 2 * q := by
    obtain ⟨q, rfl⟩ := hpar
    exact ⟨q + 1, by simp only [sh, sgn_true, sl2RootDatum, one_smul]; ring⟩
  apply (cancel_epi (eqToHom (objI_pos _ _ (cond_up μ)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (cond_up μ)))).1
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sub, freeLift_map_of]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Limits.comp_zero, Limits.zero_comp,
    Category.assoc]
  rw [sub_eq_zero, img_curlL S μ]
  unfold KL3.Diagram.curlLHS
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sum]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [Finset.sum_congr rfl (fun g _ => img_curlLHS_term S μ g)]
  erw [ip_sl2]
  refine (curlE_model S _ _ _ _ _ _ (S.wt_qi hpar')).trans ?_
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc]
  rfl

end StrongSl2

end Model

end Categorification.TwoRep
