/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpKLR
import Categorification.TwoRep.RouqInterp
import Categorification.Diagrams.CL.Presentation
import Categorification.Diagrams.KL3.Upward

/-!
# Concrete mixed upward KLR equations for the admissible interpreter

The source package is `RouqUpKLR`; `BrundanUpKLR` uses the full ungraded polynomials
from Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2)--(1.4).
The conclusions use the actual `admissibleMap (S.genImg Sc)` in the original Hom
category. The polynomial calculation is an endomorphism-algebra map, not a target
relation supplied as a hypothesis.

`up_sqNe`, `up_slideLNe`, `up_slideRNe`, `up_braid`, and `up_braidQ` evaluate the
corresponding KLR relations. The `klr_*_rel` corollaries apply to `CL.relationCL`;
`klr_braidQ_rel` explicitly requires `Sc.r c = 1`. The same scalar package alone
would not prove soundness for arbitrary `r`. `brundan_sqNe` and `brundan_braidQ`
retain the unrestricted source coefficients; `BrundanUpKLR.toCL` is the separate
homogeneous-coefficient specialization.

This proves only the mixed upward slice. Mixed crossing cyclicity, bubbles, curls,
decompositions, aggregate `presNM` soundness, quotient descent and horizontal
coherence remain separate. Nothing here proves the full Brundan comparison.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
private theorem chain3_transport {T : Signature} {D : Type*} [Bicategory D]
    (M : Model T D) {a b c d : FB T} {W₀ W₁ W₁' W₂ W₂' W₃ P Q P₁ Q₁ P₂ Q₂ P₃ Q₃ : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB T} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁')
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB T} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂')
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (X : P ⟶ W₀) (Z₁ : W₁ ⟶ W₁') (Z₂ : W₂ ⟶ W₂') (Y : W₃ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ X ≫ (layerAt M τ₁ τ₁' g₁ ≫ M.lift.map₂ Z₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ M.lift.map₂ Z₂ ≫ layerAt M τ₃ τ₃' g₃) ≫
        M.lift.map₂ Y := by
  calc _ = M.lift.map₂ (E₀ ≫ A₁) ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (B₁ ≫ E₁ ≫ A₂) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (B₂ ≫ E₂ ≫ A₃) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ (B₃ ≫ E₃) := by
          simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    _ = M.lift.map₂ (X ≫ τ₁.inv) ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ (τ₁'.hom ≫ Z₁ ≫ τ₂.inv) ≫
        midK M p₂ q₂ g₂ ≫ M.lift.map₂ (τ₂'.hom ≫ Z₂ ≫ τ₃.inv) ≫ midK M p₃ q₃ g₃ ≫
          M.lift.map₂ (τ₃'.hom ≫ Y) := by
          rw [lift_map₂_eq M (E₀ ≫ A₁) (X ≫ τ₁.inv),
            lift_map₂_eq M (B₁ ≫ E₁ ≫ A₂) (τ₁'.hom ≫ Z₁ ≫ τ₂.inv),
            lift_map₂_eq M (B₂ ≫ E₂ ≫ A₃) (τ₂'.hom ≫ Z₂ ≫ τ₃.inv),
            lift_map₂_eq M (B₃ ≫ E₃) (τ₃'.hom ≫ Y)]
    _ = _ := by simp only [layerAt, PrelaxFunctor.map₂_comp, Category.assoc]

universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
private theorem up_dom_cross («ε» : Bool) (i j : I) (μ : X) :
    (sig0 RD).dom (.cross «ε» i j μ) = wd RD μ [(«ε», i), («ε», j)] := rfl

private theorem up_cod_cross («ε» : Bool) (i j : I) (μ : X) :
    (sig0 RD).cod (.cross «ε» i j μ) = wd RD μ [(«ε», j), («ε», i)] := rfl

private abbrev upEnd {D : Type*} [Category D] {Z : D} (f : Z ⟶ Z) : End Z := f
/-- Conjugation by an isomorphism, as an algebra homomorphism of endomorphism algebras. -/
private def upIsoConj {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞} (e : Z ≅ Z') :
    End Z →ₐ[k] End Z' where
  toFun φ := upEnd (e.inv ≫ φ ≫ e.hom)
  map_one' := by
    show e.inv ≫ 𝟙 Z ≫ e.hom = 𝟙 Z'
    simp
  map_mul' φ ψ := by
    show e.inv ≫ (ψ ≫ φ) ≫ e.hom = (e.inv ≫ ψ ≫ e.hom) ≫ (e.inv ≫ φ ≫ e.hom)
    simp
  map_zero' := by
    show e.inv ≫ (0 : Z ⟶ Z) ≫ e.hom = 0
    simp
  map_add' φ ψ := by
    show e.inv ≫ ((φ : Z ⟶ Z) + (ψ : Z ⟶ Z)) ≫ e.hom =
      (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z') + (e.inv ≫ ψ ≫ e.hom : Z' ⟶ Z')
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show e.inv ≫ (r • 𝟙 Z) ≫ e.hom = r • 𝟙 Z'
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]

private theorem upIsoConj_apply {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞}
    (e : Z ≅ Z') (φ : End Z) : upIsoConj (k := k) e φ = upEnd (e.inv ≫ φ ≫ e.hom) := rfl

namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh

theorem condUp (l : List I) (μ : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD μ (ups l) : X) μ (ob RD μ (ups l)) :=
  ⟨ok_wd RD μ _, endR_wd RD μ _, rfl⟩

def readUp {a b : Obj (KLR.Diagram.sig I)} (μ : X) (f : a ⟶ b) :=
  (S.interp Sc (wt RD μ (ups a.word)) μ).map
    (ObjectProperty.homMk (X := ⟨ob RD μ (ups a.word), condUp a.word μ⟩)
      (Y := ⟨ob RD μ (ups b.word), (condUp a.word μ).chain (Diagram.chain (upDiag RD μ f))⟩)
      (upDiag RD μ f))

theorem readUp_D0 (c d : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.D0 c d) =
      S.E d (cross_up_reg d μ) ◁ S.dot c (cross_up_reg c _) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 => exact whiskerLeftIso _ (ρ_ _)
    case t1' => exact whiskerLeftIso _ (ρ_ _)
    erw [layerAt_right]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    change (S.E d (cross_up_reg d μ) ◁ S.dot c (cross_up_reg c _)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  all_goals rfl

theorem readUp_D1 (c d : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.D1 c d) =
      S.dot d (cross_up_reg d μ) ▷ S.E c (cross_up_reg c _) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 => exact λ_ _
    case t1' => exact λ_ _
    erw [layerAt_left]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    change (S.dot d (cross_up_reg d μ) ▷ S.E c (cross_up_reg c _)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  all_goals rfl

theorem readUp_X2X2 (c d : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c) =
      S.cross c d (cross_up_reg d μ) (cross_up_reg c _)
        (cross_up_reg c μ) (cross_up_swap c d rfl) ≫
      S.cross d c (cross_up_reg c μ) (cross_up_swap c d rfl)
        (cross_up_reg d μ) (cross_up_reg c _) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain2_key S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 | t1' | t2 | t2' => exact (λ_ _) ≪≫ (ρ_ _)
    erw [layerAt_whole, layerAt_whole]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    change (_ ≫ _) ≫ 𝟙 _ = _
    erw [Category.comp_id]
    rfl
  all_goals rfl

set_option maxHeartbeats 2000000 in
theorem readUp_slideL {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q) (c d : I) (h : c ≠ d) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D0 d c) =
      S.readUp Sc μ (KLR.Diagram.D1 c d ≫ KLR.Diagram.X2 c d) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  change (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _) =
    (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain2_key S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _),
      chain2_key S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 | t1' | t4 | t4' => exact (λ_ _) ≪≫ (ρ_ _)
    case t2 | t2' => exact whiskerLeftIso _ (ρ_ _)
    case t3 | t3' => exact λ_ _
    erw [layerAt_whole, layerAt_right, layerAt_left]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id, Category.comp_id]
    exact (H.slide_right c d h _ _ _ _).symm
  all_goals rfl

set_option maxHeartbeats 2000000 in
theorem readUp_slideR {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q) (c d : I) (h : c ≠ d) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.D0 c d ≫ KLR.Diagram.X2 c d) =
      S.readUp Sc μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.D1 d c) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  change (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _) =
    (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _)
  erw [eqToHom_word ?e0 _, eqToHom_word ?e1 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain2_key S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _),
      chain2_key S.model ?t3 ?t3' _ ?t4 ?t4' _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t2 | t2' | t3 | t3' => exact (λ_ _) ≪≫ (ρ_ _)
    case t1 | t1' => exact whiskerLeftIso _ (ρ_ _)
    case t4 | t4' => exact λ_ _
    erw [layerAt_whole, layerAt_right, layerAt_left]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id, Category.comp_id]
    exact (H.slide_left c d h _ _ _ _)
  all_goals rfl
omit [AdditiveWhiskering B] in
private theorem up_braid_cast {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q) (c d e : I) (hb : c ≠ e)
    {l w₁ w₂ w₂' w₃ w₃' w₄ w₅ w₅' w₆ m : X}
    (e1 : l + RD.iX e = w₁) (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m)
    (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m) (e6 : l + RD.iX c = w₄)
    (e7 : w₄ + RD.iX e = w₃) (e8 : w₄ + RD.iX d = w₅) (e9 : w₅ + RD.iX e = m)
    (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX e = w₂) (e12 : w₆ + RD.iX c = w₅)
    (e7' : w₄ + RD.iX e = w₃') (e5' : w₃' + RD.iX d = m) (e11' : w₆ + RD.iX e = w₂')
    (e3' : w₂' + RD.iX c = m) (e12' : w₆ + RD.iX c = w₅') (e9' : w₅' + RD.iX e = m)
    (hw₂ : w₂' = w₂) (hw₃ : w₃' = w₃) (hw₅ : w₅' = w₅)
    (p₁ : (S.E c e6 ≫ S.E e e7) ≫ S.E d e5 = (S.E c e6 ≫ S.E e e7') ≫ S.E d e5')
    (p₂ : (S.E d e10 ≫ S.E e e11) ≫ S.E c e3 = (S.E d e10 ≫ S.E e e11') ≫ S.E c e3')
    (p₃ : (S.E d e10 ≫ S.E c e12') ≫ S.E e e9' = (S.E d e10 ≫ S.E c e12) ≫ S.E e e9) :
    ((α_ (S.E e e1) (S.E d e2) (S.E c e3)).hom ≫ S.E e e1 ◁ S.cross c d e2 e3 e4 e5 ≫
        (α_ (S.E e e1) (S.E c e4) (S.E d e5)).inv) ≫
      S.cross c e e1 e4 e6 e7 ▷ S.E d e5 ≫ eqToHom p₁ ≫
        ((α_ (S.E c e6) (S.E e e7') (S.E d e5')).hom ≫
          S.E c e6 ◁ S.cross d e e7' e5' e8 e9 ≫ (α_ (S.E c e6) (S.E d e8) (S.E e e9)).inv) =
    S.cross d e e1 e2 e10 e11 ▷ S.E c e3 ≫ eqToHom p₂ ≫
      ((α_ (S.E d e10) (S.E e e11') (S.E c e3')).hom ≫
        S.E d e10 ◁ S.cross c e e11' e3' e12' e9' ≫
          (α_ (S.E d e10) (S.E c e12') (S.E e e9')).inv) ≫
        eqToHom p₃ ≫ S.cross c d e10 e12 e6 e8 ▷ S.E e e9 := by
  subst hw₂ hw₃ hw₅
  simp only [eqToHom_refl, Category.id_comp]
  have h := H.braid c d e hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  apply (cancel_epi (α_ (S.E e e1) (S.E d e2) (S.E c e3)).inv).1
  apply (cancel_mono (α_ (S.E c e6) (S.E d e8) (S.E e e9)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at h ⊢
  exact h
set_option maxHeartbeats 4000000 in
theorem readUp_braid {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d e : I) (hb' : c ≠ e) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.braidL c d e) =
      S.readUp Sc μ (KLR.Diagram.braidR c d e) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  change (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, d) + (sh RD (true, e) + μ))), [],
        PivotalGen.gen (Gen0.cross true c d (sh RD (true, e) + μ)), [⟨(true, e), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, d) + (sh RD (true, c) + (sh RD (true, e) + μ))), [⟨(true, d), sh RD (true, c) + (sh RD (true, e) + μ)⟩],
        PivotalGen.gen (Gen0.cross true c e μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, d) + (sh RD (true, e) + (sh RD (true, c) + μ))), [],
        PivotalGen.gen (Gen0.cross true d e (sh RD (true, c) + μ)), [⟨(true, c), μ⟩]⟩) _ _ ≫ eqToHom _) =
    (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, d) + (sh RD (true, e) + μ))), [⟨(true, c), sh RD (true, d) + (sh RD (true, e) + μ)⟩],
        PivotalGen.gen (Gen0.cross true d e μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, e) + (sh RD (true, d) + μ))), [],
        PivotalGen.gen (Gen0.cross true c e (sh RD (true, d) + μ)), [⟨(true, d), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, e) + (sh RD (true, c) + (sh RD (true, d) + μ))), [⟨(true, e), sh RD (true, c) + (sh RD (true, d) + μ)⟩],
        PivotalGen.gen (Gen0.cross true c d μ), []⟩) _ _ ≫ eqToHom _)
  generalize_proofs
  generalize h1 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) = x1 at *
  obtain rfl :
      x1 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h1]; abel
  generalize h2 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x2 at *
  obtain rfl :
      x2 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h2]; abel
  generalize h3 :
      sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x3 at *
  obtain rfl :
      x3 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h3]; abel
  generalize h4 :
      sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x4 at *
  obtain rfl :
      x4 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h4]; abel
  generalize h5 :
      sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x5 at *
  obtain rfl :
      x5 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, e) : Letter I) + μ)) := by
    rw [← h5]; abel
  generalize h6 : sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x6 at *
  obtain rfl :
      x6 = sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
    rw [← h6]; abel
  generalize h7 : sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) + μ) = x7 at *
  obtain rfl :
      x7 = sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
    rw [← h7]; abel
  generalize h8 : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x8 at *
  obtain rfl :
      x8 = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
    rw [← h8]; abel
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _, eqToHom_word ?w2 _,
    eqToHom_word ?w3 _, eqToHom_word ?w4 _, eqToHom_word ?w5 _]
  all_goals try rfl
  case w2 =>
    change [Col.mk (true, d) (sh RD (true, c) + (sh RD (true, e) + μ)),
      Col.mk (true, e) (sh RD (true, c) + μ), Col.mk (true, c) μ] =
      [Col.mk (true, d) (sh RD (true, e) + (sh RD (true, c) + μ)),
      Col.mk (true, e) (sh RD (true, c) + μ), Col.mk (true, c) μ]
    rw [add_left_comm (sh RD (true, c)) (sh RD (true, e)) μ]
  case w4 =>
    change [Col.mk (true, c) (sh RD (true, d) + (sh RD (true, e) + μ)),
      Col.mk (true, e) (sh RD (true, d) + μ), Col.mk (true, d) μ] =
      [Col.mk (true, c) (sh RD (true, e) + (sh RD (true, d) + μ)),
      Col.mk (true, e) (sh RD (true, d) + μ), Col.mk (true, d) μ]
    rw [add_left_comm (sh RD (true, d)) (sh RD (true, e)) μ]
  case w5 =>
    change [Col.mk (true, e) (sh RD (true, c) + (sh RD (true, d) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ] =
      [Col.mk (true, e) (sh RD (true, d) + (sh RD (true, c) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ]
    rw [add_left_comm (sh RD (true, c)) (sh RD (true, d)) μ]
  unfold coreC core
  dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
    List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
    Signature.endR, psig_colourTgt, psig_colourSrc,
    Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
    Signature.pivotal_left_gen, Signature.pivotal_right_gen]
  erw [chain3_transport S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _) (eqToHom ?z1) (𝟙 _),
    chain3_transport S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (eqToHom ?z2) (eqToHom ?z3) (𝟙 _)]
  case t1 | t1' | t3 | t3' | t5 | t5' =>
    exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
  case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
  case z1 =>
    dsimp only [Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      up_dom_cross, up_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.endR, psig_colourTgt, psig_colourSrc]
    generalize_proofs
    generalize hx : sh RD ((true, e) : Letter I) + (sh RD ((true, c) : Letter I) + μ) = x at *
    obtain rfl : x = sh RD ((true, c) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z2 =>
    dsimp only [Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      up_dom_cross, up_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.endR, psig_colourTgt, psig_colourSrc]
    generalize_proofs
    generalize hx : sh RD ((true, e) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl : x = sh RD ((true, d) : Letter I) + (sh RD ((true, e) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z3 =>
    dsimp only [Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      up_dom_cross, up_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.endR, psig_colourTgt, psig_colourSrc]
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl : x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  repeat erw [layerAt_right_assoc]
  repeat erw [layerAt_left]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  repeat erw [lift_map₂_eqToHom]
  erw [Category.comp_id, Category.comp_id]
  exact (S.up_braid_cast H c d e hb' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (add_left_comm _ _ _) (add_left_comm _ _ _) (add_left_comm _ _ _) _ _ _)
theorem readUp_E0 (c d e : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.E0 c d e) =
      (S.E e (cross_up_reg e μ) ≫ S.E d (cross_up_reg d _)) ◁ S.dot c (cross_up_reg c _) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (𝟙 _) (𝟙 _)]
    case t1 => exact whiskerLeftIso _ (ρ_ _)
    case t1' => exact whiskerLeftIso _ (ρ_ _)
    erw [layerAt_right]
    simp only [PrelaxFunctor.map₂_id, Category.id_comp]
    change ((S.E e (cross_up_reg e μ) ≫ S.E d (cross_up_reg d _)) ◁ S.dot c (cross_up_reg c _)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  all_goals rfl

theorem readUp_E1 (c d e : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.E1 c d e) =
      (α_ (S.E e (cross_up_reg e μ)) (S.E d (cross_up_reg d _)) (S.E c (cross_up_reg c _))).hom ≫ S.E e (cross_up_reg e μ) ◁ (S.dot d (cross_up_reg d _) ▷ S.E c (cross_up_reg c _)) ≫ (α_ (S.E e (cross_up_reg e μ)) (S.E d (cross_up_reg d _)) (S.E c (cross_up_reg c _))).inv := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (α_ _ _ _).hom (α_ _ _ _).inv]
    case t1 => exact Iso.refl _
    case t1' => exact Iso.refl _
    erw [layerAt_mid]
    simp only [lift_map₂_associator_hom, lift_map₂_associator_inv]
    rfl
  all_goals rfl

theorem readUp_E2 (c d e : I) (μ : X) :
    S.readUp Sc μ (KLR.Diagram.E2 c d e) =
      (α_ (S.E e (cross_up_reg e μ)) (S.E d (cross_up_reg d _)) (S.E c (cross_up_reg c _))).hom ≫ S.dot e (cross_up_reg e μ) ▷ (S.E d (cross_up_reg d _) ≫ S.E c (cross_up_reg c _)) ≫ (α_ (S.E e (cross_up_reg e μ)) (S.E d (cross_up_reg d _)) (S.E c (cross_up_reg c _))).inv := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ = _
  erw [eqToHom_word ?e0 _]
  · unfold coreC core
    dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
      List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
      Signature.endR, psig_colourTgt, psig_colourSrc,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen]
    erw [chain1_key S.model ?t1 ?t1' _ _ _ _ _ (α_ _ _ _).hom (α_ _ _ _).inv]
    case t1 => exact λ_ _
    case t1' => exact λ_ _
    erw [layerAt_left]
    simp only [lift_map₂_associator_hom, lift_map₂_associator_inv]
    rfl
  all_goals rfl
/-- The endomorphism algebra of one upward word, interpreted admissibly. -/
def upEndAlg (l : List I) (μ : X) :
    End (Free.of k (KLR.Diagram.ob l)) →ₐ[k]
      End (S.model.word (KL3.Diagram.wt RD μ (ups l) : X) (wd RD μ (ups l)) μ
        (condUp (RD := RD) l μ).1 (condUp (RD := RD) l μ).2.1) where
  toFun f := admissibleMap (S.genImg Sc) (condUp l μ) (condUp l μ) (upLin RD k μ f)
  map_one' := by
    change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ (LinDiagram.of (𝟙 _))) = _
    rw [upLin_of]
    have h : upDiag RD μ (𝟙 (KLR.Diagram.ob l)) = 𝟙 _ := by apply Diagram.ext; rfl
    erw [h, admissibleMap_of]
    exact (S.interp Sc _ μ).map_id _
  map_mul' f g := by
    have hu : ∀ {a b c : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) (g : LinDiagram k b c),
        upLin RD k μ (f ≫ g) =
          upLin RD k μ f ≫ upLin RD k μ g := by
      intro a b c f g
      unfold upLin
      induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
      | zero => erw [Limits.zero_comp, Finsupp.mapDomain_zero, Finsupp.mapDomain_zero, Limits.zero_comp]
      | add f f' hf hf' => erw [Preadditive.add_comp, Finsupp.mapDomain_add, hf, hf', Finsupp.mapDomain_add, Preadditive.add_comp]
      | single f x =>
        induction g using (Finsupp.induction_linear (ι := b ⟶ c) (M := k)) with
        | zero => erw [Limits.comp_zero, Finsupp.mapDomain_zero, Finsupp.mapDomain_zero, Limits.comp_zero]
        | add g g' hg hg' => erw [Preadditive.comp_add, Finsupp.mapDomain_add, hg, hg', Finsupp.mapDomain_add, Preadditive.comp_add]
        | single g y =>
          erw [Free.single_comp_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, Free.single_comp_single]
          congr 1
          apply Diagram.ext
          simp only [layers_upDiag, Diagram.layers_comp, List.map_append]
    change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ (g ≫ f)) = _
    erw [hu, admissibleMap_comp (S.genImg Sc) (condUp l μ) (condUp l μ) (condUp l μ)]
    rfl
  map_zero' := by change admissibleMap (S.genImg Sc) _ _ ((Finsupp.lmapDomain k k (upDiag RD μ)) 0) = _; erw [map_zero]; rfl
  map_add' f g := by
    change (admissibleMap (S.genImg Sc) (condUp l μ) (condUp l μ))
      ((Finsupp.lmapDomain k k (upDiag RD μ)) (f + g)) = _
    erw [map_add, map_add]
    rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ (r • LinDiagram.of (𝟙 _))) = _
    erw [upLin_smul, map_smul, upLin_of]
    have h : upDiag RD μ (𝟙 (KLR.Diagram.ob l)) = 𝟙 _ := by apply Diagram.ext; rfl
    erw [h, admissibleMap_of]
    exact congrArg (r • ·) ((S.interp Sc _ μ).map_id _)

@[simp] theorem upEndAlg_of (l : List I) (μ : X) (f : KLR.Diagram.ob l ⟶ KLR.Diagram.ob l) :
    S.upEndAlg Sc l μ (LinDiagram.of f) = S.readUp Sc μ f := by
  change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ (LinDiagram.of f)) = _
  erw [upLin_of, admissibleMap_of]
  rfl

set_option maxHeartbeats 2000000 in
/-- The mixed quadratic relation evaluates to the source square equation. -/
theorem up_sqNe {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ) (condUp [c, d] μ)
      (upLin RD k μ (KLR.Diagram.relation k Q (.sqNe c d h))) = 0 := by
  change S.upEndAlg Sc [c, d] μ (KLR.Diagram.relation k Q (.sqNe c d h)) = 0
  unfold KLR.Diagram.relation KLR.Diagram.lpoly
  erw [map_sub, AlgHom.map_ncEval]
  simp only [upEndAlg_of]
  rw [readUp_X2X2]
  have hv : (fun a => S.readUp Sc μ (![KLR.Diagram.D0 c d, KLR.Diagram.D1 c d] a)) =
      ![S.E d (cross_up_reg d μ) ◁ S.dot c (cross_up_reg c _),
        S.dot d (cross_up_reg d μ) ▷ S.E c (cross_up_reg c _)] := by
    funext a
    fin_cases a
    · exact S.readUp_D0 Sc c d μ
    · exact S.readUp_D1 Sc c d μ
  rw [hv]
  exact sub_eq_zero.2 (H.square c d h _ _ _ _)
omit [AdditiveWhiskering B] in
private theorem up_braidQ_cast {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d : I) (hcd : c ≠ d)
    {l w₁ w₂ w₂' w₃ w₅' w₆ m : X}
    (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m)
    (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m)
    (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e11' : w₆ + RD.iX c = w₂')
    (e3' : w₂' + RD.iX c = m) (e12' : w₆ + RD.iX c = w₅') (e9' : w₅' + RD.iX c = m)
    (hw₂ : w₂' = w₂) (hw₅ : w₅' = w₂)
    (p₂ : (S.E d e10 ≫ S.E c e11) ≫ S.E c e3 = (S.E d e10 ≫ S.E c e11') ≫ S.E c e3')
    (p₃ : (S.E d e10 ≫ S.E c e12') ≫ S.E c e9' = (S.E d e10 ≫ S.E c e11) ≫ S.E c e3) :
    upEnd (((α_ (S.E c e1) (S.E d e2) (S.E c e3)).hom ≫ S.E c e1 ◁ S.cross c d e2 e3 e4 e5 ≫
        (α_ (S.E c e1) (S.E c e4) (S.E d e5)).inv) ≫
      S.cross c c e1 e4 e1 e4 ▷ S.E d e5 ≫
        ((α_ (S.E c e1) (S.E c e4) (S.E d e5)).hom ≫
          S.E c e1 ◁ S.cross d c e4 e5 e2 e3 ≫ (α_ (S.E c e1) (S.E d e2) (S.E c e3)).inv)) -
    upEnd (S.cross d c e1 e2 e10 e11 ▷ S.E c e3 ≫ eqToHom p₂ ≫
      ((α_ (S.E d e10) (S.E c e11') (S.E c e3')).hom ≫
        S.E d e10 ◁ S.cross c c e11' e3' e12' e9' ≫
          (α_ (S.E d e10) (S.E c e12') (S.E c e9')).inv) ≫
        eqToHom p₃ ≫ S.cross c d e10 e11 e1 e2 ▷ S.E c e3) =
    KLR.ncEval ![upEnd ((S.E c e1 ≫ S.E d e2) ◁ S.dot c e3),
        upEnd ((α_ (S.E c e1) (S.E d e2) (S.E c e3)).hom ≫
          S.E c e1 ◁ (S.dot d e2 ▷ S.E c e3) ≫ (α_ (S.E c e1) (S.E d e2) (S.E c e3)).inv),
        upEnd ((α_ (S.E c e1) (S.E d e2) (S.E c e3)).hom ≫
          S.dot c e1 ▷ (S.E d e2 ≫ S.E c e3) ≫ (α_ (S.E c e1) (S.E d e2) (S.E c e3)).inv)]
      (KLR.qbar (Q c d)) := by
  subst hw₂ hw₅
  simp only [eqToHom_refl, Category.id_comp]
  have key := congrArg (upIsoConj (k := k) (α_ (S.E c e1) (S.E d e2) (S.E c e3)).symm)
    (H.braidQ c d hcd e1 e2 e3 e4 e5 e10 e11)
  rw [map_sub, AlgHom.map_ncEval] at key
  simp only [upIsoConj_apply, Iso.symm_inv, Iso.symm_hom] at key
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    · simp only [Category.assoc]
    · simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id]
  · congr 1
    funext t
    fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [comp_whiskerLeft]
    · rfl
    · rfl
set_option maxHeartbeats 6000000 in
/-- The divided-difference braid relation evaluates to Brundan's source equation. -/
theorem up_braidQ {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d, c] μ) (condUp [c, d, c] μ)
      (upLin RD k μ (KLR.Diagram.relation k Q (.braidQ c d h))) = 0 := by
  change S.upEndAlg Sc [c, d, c] μ (KLR.Diagram.relation k Q (.braidQ c d h)) = 0
  unfold KLR.Diagram.relation KLR.Diagram.lpoly
  erw [map_sub, map_sub, AlgHom.map_ncEval, sub_eq_zero]
  simp only [upEndAlg_of]
  have hv : (fun a => S.readUp Sc μ
      (![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c] a)) =
      ![upEnd ((S.E c (cross_up_reg c μ) ≫ S.E d (cross_up_reg d _)) ◁
          S.dot c (cross_up_reg c _)),
        upEnd ((α_ (S.E c (cross_up_reg c μ)) (S.E d (cross_up_reg d _))
          (S.E c (cross_up_reg c _))).hom ≫
          S.E c (cross_up_reg c μ) ◁ (S.dot d (cross_up_reg d _) ▷ S.E c (cross_up_reg c _)) ≫
          (α_ (S.E c (cross_up_reg c μ)) (S.E d (cross_up_reg d _))
            (S.E c (cross_up_reg c _))).inv),
        upEnd ((α_ (S.E c (cross_up_reg c μ)) (S.E d (cross_up_reg d _))
          (S.E c (cross_up_reg c _))).hom ≫
          S.dot c (cross_up_reg c μ) ▷ (S.E d (cross_up_reg d _) ≫ S.E c (cross_up_reg c _)) ≫
          (α_ (S.E c (cross_up_reg c μ)) (S.E d (cross_up_reg d _))
            (S.E c (cross_up_reg c _))).inv)] := by
    funext a
    fin_cases a
    · exact S.readUp_E0 Sc c d c μ
    · exact S.readUp_E1 Sc c d c μ
    · exact S.readUp_E2 Sc c d c μ
  rw [hv]
  clear hv
  change upEnd (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, d) + (sh RD (true, c) + μ))), [],
        PivotalGen.gen (Gen0.cross true c d (sh RD (true, c) + μ)), [⟨(true, c), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, d) + (sh RD (true, c) + (sh RD (true, c) + μ))), [⟨(true, d), sh RD (true, c) + (sh RD (true, c) + μ)⟩],
        PivotalGen.gen (Gen0.cross true c c μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, d) + (sh RD (true, c) + (sh RD (true, c) + μ))), [],
        PivotalGen.gen (Gen0.cross true d c (sh RD (true, c) + μ)), [⟨(true, c), μ⟩]⟩) _ _ ≫ eqToHom _) -
    upEnd (eqToHom _ ≫ coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, d) + (sh RD (true, c) + μ))), [⟨(true, c), sh RD (true, d) + (sh RD (true, c) + μ)⟩],
        PivotalGen.gen (Gen0.cross true d c μ), []⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, c) + (sh RD (true, d) + μ))), [],
        PivotalGen.gen (Gen0.cross true c c (sh RD (true, d) + μ)), [⟨(true, d), μ⟩]⟩) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc)
      (L := ⟨(sh RD (true, c) + (sh RD (true, c) + (sh RD (true, d) + μ))), [⟨(true, c), sh RD (true, c) + (sh RD (true, d) + μ)⟩],
        PivotalGen.gen (Gen0.cross true c d μ), []⟩) _ _ ≫ eqToHom _) = _
  generalize_proofs
  generalize h1 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x1 at *
  obtain rfl :
      x1 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h1]; abel
  generalize h4 :
      sh RD ((true, c) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x4 at *
  obtain rfl :
      x4 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h4]; abel
  generalize h6 : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x6 at *
  obtain rfl :
      x6 = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
    rw [← h6]; abel
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _, eqToHom_word ?w2 _,
    eqToHom_word ?w3 _]
  all_goals try rfl
  case w2 =>
    change [Col.mk (true, c) (sh RD (true, d) + (sh RD (true, c) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ] =
      [Col.mk (true, c) (sh RD (true, c) + (sh RD (true, d) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ]
    rw [add_left_comm (sh RD (true, d)) (sh RD (true, c)) μ]
  case w3 =>
    change [Col.mk (true, c) (sh RD (true, c) + (sh RD (true, d) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ] =
      [Col.mk (true, c) (sh RD (true, d) + (sh RD (true, c) + μ)),
      Col.mk (true, c) (sh RD (true, d) + μ), Col.mk (true, d) μ]
    rw [add_left_comm (sh RD (true, c)) (sh RD (true, d)) μ]
  unfold coreC core
  dsimp only [upLay, KLR.Diagram.lay, lay, upShape, Shape.gen, ups,
    List.map_cons, List.map_nil, wt_cons, wt_nil, wd_cons, wd_nil,
    Signature.endR, psig_colourTgt, psig_colourSrc,
    Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
    Signature.pivotal_left_gen, Signature.pivotal_right_gen]
  erw [chain3_transport S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _) (eqToHom ?z1) (𝟙 _),
    chain3_transport S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (eqToHom ?z2) (eqToHom ?z3) (𝟙 _)]
  case t1 | t1' | t3 | t3' | t5 | t5' =>
    exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
  case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
  case z1 => rfl
  case z2 =>
    dsimp only [Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      up_dom_cross, up_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.endR, psig_colourTgt, psig_colourSrc]
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl : x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z3 =>
    dsimp only [Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
      up_dom_cross, up_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.endR, psig_colourTgt, psig_colourSrc]
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl : x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  repeat erw [layerAt_right_assoc]
  repeat erw [layerAt_left]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  repeat erw [lift_map₂_eqToHom]
  erw [Category.comp_id, Category.comp_id]
  erw [eqToHom_refl, Category.id_comp]
  exact S.up_braidQ_cast H c d h _ _ _ _ _ _ _ _ _ _ _
    (add_left_comm _ _ _) (add_left_comm _ _ _) _ _
/-- The first mixed slide is killed by the concrete admissible interpretation. -/
theorem up_slideLNe {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ)
      ((condUp [c, d] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.X2 c d))))
      (upLin RD k μ (KLR.Diagram.relation k Q (.slideLNe c d h))) = 0 := by
  unfold KLR.Diagram.relation
  erw [upLin_sub, upLin_of, upLin_of, map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.2 (S.readUp_slideL Sc H c d h μ)

/-- The second mixed slide is killed by the concrete admissible interpretation. -/
theorem up_slideRNe {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ)
      ((condUp [c, d] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.X2 c d))))
      (upLin RD k μ (KLR.Diagram.relation k Q (.slideRNe c d h))) = 0 := by
  unfold KLR.Diagram.relation
  erw [upLin_sub, upLin_of, upLin_of, map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.2 (S.readUp_slideR Sc H c d h μ)

/-- The braid with distinct outer labels has no correction term. -/
theorem up_braid {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (c d e : I) (h : c ≠ e) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d, e] μ)
      ((condUp [c, d, e] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.braidL c d e))))
      (upLin RD k μ (KLR.Diagram.relation k Q (.braid c d e (fun he => h he.1)))) = 0 := by
  unfold KLR.Diagram.relation
  erw [upLin_sub, upLin_of, upLin_of, map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.2 (S.readUp_braid Sc H c d e h μ)
/-- Brundan's square equation, with every source deformation coefficient retained. -/
theorem brundan_sqNe (H : BrundanUpKLR S Sc) (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ) (condUp [c, d] μ)
      (upLin RD k μ (KLR.Diagram.relation k (brundanQ Sc) (.sqNe c d h))) = 0 :=
  S.up_sqNe Sc H c d h μ

/-- Brundan's corrected braid equation, using the same concrete generator images. -/
theorem brundan_braidQ (H : BrundanUpKLR S Sc) (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d, c] μ) (condUp [c, d, c] μ)
      (upLin RD k μ (KLR.Diagram.relation k (brundanQ Sc) (.braidQ c d h))) = 0 :=
  S.up_braidQ Sc H c d h μ
/-- The actual CL mixed upward `sqNe` relation. -/
theorem klr_sqNe_rel (H : RouqUpKLR S (CL.qCL Sc)) (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ)
      (condUp [c, d] μ)
      (CL.relationCL RD k Sc (.klr μ (.sqNe c d h))) = 0 :=
  S.up_sqNe Sc H c d h μ

/-- The actual CL mixed upward `slideLNe` relation. -/
theorem klr_slideLNe_rel (H : RouqUpKLR S (CL.qCL Sc)) (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ)
      ((condUp [c, d] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.X2 c d))))
      (CL.relationCL RD k Sc (.klr μ (.slideLNe c d h))) = 0 :=
  S.up_slideLNe Sc H c d h μ

/-- The actual CL mixed upward `slideRNe` relation. -/
theorem klr_slideRNe_rel (H : RouqUpKLR S (CL.qCL Sc)) (c d : I) (h : c ≠ d) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d] μ)
      ((condUp [c, d] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.X2 c d))))
      (CL.relationCL RD k Sc (.klr μ (.slideRNe c d h))) = 0 :=
  S.up_slideRNe Sc H c d h μ

/-- The actual CL mixed upward `braid` relation. -/
theorem klr_braid_rel (H : RouqUpKLR S (CL.qCL Sc)) (c d e : I) (h : c ≠ e) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d, e] μ)
      ((condUp [c, d, e] μ).chain (Diagram.chain (upDiag RD μ (KLR.Diagram.braidL c d e))))
      (CL.relationCL RD k Sc (.klr μ (.braid c d e (fun he => h he.1)))) = 0 :=
  S.up_braid Sc H c d e h μ

/-- The actual CL corrected braid relation, in the source normalization `r_c = 1`.
Merely supplying a scalar package with arbitrary `r` does not prove this equation. -/
theorem klr_braidQ_rel (H : RouqUpKLR S (CL.qCL Sc))
    (c d : I) (h : c ≠ d) (hr : Sc.r c = 1) (μ : X) :
    admissibleMap (S.genImg Sc) (condUp [c, d, c] μ) (condUp [c, d, c] μ)
      (CL.relationCL RD k Sc (.klr μ (.braidQ c d h))) = 0 := by
  change admissibleMap (S.genImg Sc) _ _ (upLin RD k μ
    (LinDiagram.of (KLR.Diagram.braidL c d c) - LinDiagram.of (KLR.Diagram.braidR c d c) -
      (Sc.r c : k) • KLR.Diagram.lpoly k
        ![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c]
        (KLR.qbar (CL.qCL Sc c d)))) = 0
  rw [hr, Units.val_one, one_smul]
  exact S.up_braidQ Sc H c d h μ
end RouqFamily
end Categorification.TwoRep
