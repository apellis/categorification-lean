/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongKLR
import Categorification.Diagrams.CL.RescaleBasic
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# The quadratic KLR relation in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2 (4), (2.10): in the model of
`Categorification.TwoRep.ModelQStrong` (normalized dots `r_i⁻¹ x`), for `c ≠ d` the double
crossing on `E_c E_d 1_μ` is `Q'_{cd}(x_c, x_d)` with `Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)`
(`CL.Rescale.scaleP`), i.e. the KLR relation `sqNe` for the polynomials `Q'` placed on upward
strands is killed (`QStrong.klr_sqNe`). The polynomial `Q_{cd}` is assumed homogeneous of degree
`-2 (α_c, α_d)` for the dot degrees (as CL's `Q_{ij}` are, `CL.qCL_isWeightedHomogeneous`), since
condition (2.10) of a `Q`-strong 2-representation only involves this homogeneous component
(`homogEval2`).

## Main results

* `of₂_homogEval2`: the homogeneous evaluation of a polynomial in two commuting shifted
  endomorphisms, in the graded-Hom bicategory, is `KLR.ncEval`;
* `QStrong.crossQ_sq`: CL (2.10) in the graded-Hom bicategory, for the normalized dots;
* `QStrong.conj_D0`, `conj_D1`, `conj_X2X2`: the images of the dots and of the double crossing on
  two upward strands;
* `QStrong.klr_sqNe`.

The polynomial `Q'(x₀, x₁)` in the diagrams is transported to the model by the algebra
homomorphisms of endomorphism algebras induced by linear functors (`functorEndAlg`) and by
transports (`conjAlg`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

/-! ## Polynomials in shifted endomorphisms -/

section PolyGr

/-- A morphism `X ⟶ X` as an element of the endomorphism monoid `End X`. -/
abbrev toEnd {𝒞 : Type*} [Category 𝒞] {Z : 𝒞} (φ : Z ⟶ Z) : End Z := φ

variable {a b : B} {f : a ⟶ b}

theorem of₂_shCast {g : a ⟶ b} {m n : ℤ} (η : ShiftedHom f g m) (h : m = n) :
    of₂ n (shCast η h) = of₂ m η := by
  subst h; rfl

theorem of₂_mk₀ {g : a ⟶ b} (n : ℤ) (h : n = 0) (η : f ⟶ g) :
    of₂ n (ShiftedHom.mk₀ n h η) = incl₂ η := by
  subst h; rfl

theorem of₂_shPow {d : ℤ} (x : ShiftedHom f f d) (n : ℕ) :
    toEnd (of₂ ((n : ℤ) * d) (shPow x n)) = toEnd (of₂ d x) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact (of₂_mk₀ _ _ (𝟙 f)).trans (incl₂_id f)
  | succ n ih =>
    have e : of₂ (((n + 1 : ℕ) : ℤ) * d) (shPow x (n + 1)) =
        of₂ _ (shPow x n) ≫ of₂ d x := (of₂_comp_of₂ _ _ _).symm
    rw [e, pow_succ', ← ih]
    rfl

theorem of₂_shMono2 {d₁ d₂ : ℤ} (x : ShiftedHom f f d₁) (y : ShiftedHom f f d₂) (p q : ℕ) :
    of₂ _ (shMono2 x y p q) =
      (toEnd (of₂ d₁ x) ^ p : End (of₁ f)) ≫ (toEnd (of₂ d₂ y) ^ q : End (of₁ f)) := by
  rw [shMono2, ← of₂_comp_of₂, ← of₂_shPow x p, ← of₂_shPow y q]

theorem of₂_sum {g : a ⟶ b} {n : ℤ} {ι : Type*} (T : Finset ι) (η : ι → ShiftedHom f g n) :
    of₂ n (∑ t ∈ T, η t) = ∑ t ∈ T, of₂ n (η t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert t T ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht, of₂_add, ih]

/-- The degree-`deg` part of `P(x, y)` for a polynomial `P` all of whose monomials have degree
`deg`, in the graded-Hom bicategory: the evaluation of `P` at the (commuting) images of `x`, `y`. -/
theorem of₂_homogEval2 {d₁ d₂ : ℤ} (P : MvPolynomial (Fin 2) k) (x : ShiftedHom f f d₁)
    (y : ShiftedHom f f d₂) (deg : ℤ)
    (hP : ∀ m ∈ P.support, (m 0 : ℤ) * d₁ + (m 1 : ℤ) * d₂ = deg)
    (hxy : Commute (toEnd (of₂ d₁ x)) (toEnd (of₂ d₂ y))) :
    toEnd (of₂ deg (homogEval2 k P x y deg)) =
      KLR.ncEval ![toEnd (of₂ d₁ x), toEnd (of₂ d₂ y)] P := by
  rw [homogEval2, of₂_sum, KLR.ncEval, Finsupp.sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  split_ifs with hm'
  swap
  · exact absurd (hP m hm) hm'
  rw [of₂_smul, of₂_shCast, of₂_shMono2, ← Algebra.smul_def]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one]
  rw [((hxy.pow_left (m 0)).pow_right (m 1)).eq]
  rfl

end PolyGr

/-! ## Generic lemmas -/

section Generic

open StringDiagrams Diagrams.BicatInterp

/-- **One layer in normal form** (no transports). -/
theorem chain1_key' {S' : Signature} {D : Type*} [Bicategory D] (M : Model S' D)
    {a b c d : FB S'} {W W' P Q : a ⟶ d} {p : a ⟶ b} {q : c ⟶ d} {x y : b ⟶ c}
    (τ : p ≫ (x ≫ q) ≅ W) (τ' : p ≫ (y ≫ q) ≅ W') (g : M.lift.map x ⟶ M.lift.map y)
    (A₁ : P ⟶ p ≫ (x ≫ q)) (B₁ : p ≫ (y ≫ q) ⟶ Q) (X : P ⟶ W) (Y : W' ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p q g ≫ M.lift.map₂ B₁ =
      M.lift.map₂ X ≫ layerAt M τ τ' g ≫ M.lift.map₂ Y := by
  have h := chain1_key M τ τ' g (𝟙 _) A₁ B₁ (𝟙 _) X Y
  simpa only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id] using h

/-- Conjugation by a transport along an equality of objects, as an algebra isomorphism of
endomorphism algebras. -/
def conjAlg {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞} (e : Z = Z') :
    End Z →ₐ[k] End Z' := by
  subst e; exact AlgHom.id k _

theorem conjAlg_apply {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞}
    (e : Z = Z') (φ : End Z) :
    conjAlg (k := k) e φ = toEnd (eqToHom e.symm ≫ φ ≫ eqToHom e) := by
  subst e; simp [conjAlg]

variable (RD) in
/-- The functor placing KLR diagrams on upward strands with rightmost region `μ`. -/
def upDF (μ : X) : Obj (KLR.Diagram.sig I) ⥤ Obj (psig RD) where
  obj a := ob RD μ (ups a.word)
  map d := upDiag RD μ d
  map_id _ := Diagram.ext (by simp)
  map_comp _ _ := Diagram.ext (by simp)

variable (RD k) in
/-- `upDF` followed by the embedding into the free `k`-linear category. -/
abbrev upDFL (μ : X) : Obj (KLR.Diagram.sig I) ⥤ CategoryTheory.Free k (Obj (psig RD)) :=
  upDF RD μ ⋙ CategoryTheory.Free.embedding k (Obj (psig RD))

set_option backward.isDefEq.respectTransparency false in
variable (RD) in
theorem freeLift_upDFL (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    (freeLift k (upDFL k RD μ)).map f = upLin RD k μ f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero]; exact Finsupp.mapDomain_zero.symm
  | add f g hf hg => rw [Functor.map_add, hf, hg]; exact Finsupp.mapDomain_add.symm
  | single d r =>
    rw [freeLift_map_single, upLin, Finsupp.mapDomain_single]
    change r • Finsupp.single (upDiag RD μ d) (1 : k) = _
    rw [Finsupp.smul_single_one]

end Generic

namespace QStrong

/-! ## The relations in the graded-Hom bicategory -/

section GrQ

variable (S : QStrong B C RD k Q)

theorem commute_whisker {a' b' c' : GradedHomBicat B} {f : a' ⟶ b'} {g : b' ⟶ c'}
    (η : f ⟶ f) (θ : g ⟶ g) : Commute (toEnd (f ◁ θ)) (toEnd (η ▷ g)) :=
  (whisker_exchange η θ).symm

/-- **CL (2.10)** in the graded-Hom bicategory, for the normalized dots: for `c ≠ d`,
`τ_{dc} τ_{cd} = Q'_{cd}(x_c, x_d)` on `E_c E_d 1_λ`, where `Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)`
(`x_c` the normalized dot on the left strand, labelled `c`). The polynomial `Q_{cd}` is assumed
homogeneous of degree `-2 (α_c, α_d)` for the dot degrees `(α_c, α_c)`, `(α_d, α_d)`. -/
theorem crossQ_sq (c d : I) (h : c ≠ d)
    (hQ : ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    {l n m n' : X} (h₁ : l + RD.iX d = n) (h₂ : n + RD.iX c = m) (h₃ : l + RD.iX c = n')
    (h₄ : n' + RD.iX d = m) :
    toEnd (S.crossQ c d h₁ h₂ h₃ h₄ ≫ S.crossQ d c h₃ h₄ h₁ h₂) =
      KLR.ncEval ![toEnd (S.Eg d h₁ ◁ S.dotQ c h₂), toEnd (S.dotQ d h₁ ▷ S.Eg c h₂)]
        (CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d)) := by
  have e := congrArg (of₂ (-2 * C.dot c d)) (S.klr.cross_sq c d h h₁ h₂ h₃ h₄)
  rw [← CL.Rescale.ncEval_smul]
  calc toEnd (S.crossQ c d h₁ h₂ h₃ h₄ ≫ S.crossQ d c h₃ h₄ h₁ h₂) =
        toEnd (of₂ (-2 * C.dot c d) (homogEval2 k (Q c d)
          (shWhiskerLeft (S.E d h₁) (S.dot c h₂)) (shWhiskerRight (S.dot d h₁) (S.E c h₂))
          (-2 * C.dot c d))) := by
        rw [← e, crossQ, crossQ, of₂_comp_of₂]
    _ = _ := by
        rw [of₂_homogEval2 _ _ _ _ hQ]
        · congr 1
          funext t
          fin_cases t
          · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, dotQ,
              GradedHomBicat.whiskerLeft_smul, smul_smul, ← whiskerLeft_of₂]
            rw [Units.mul_inv, one_smul]
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, dotQ]
            erw [GradedHomBicat.smul_whiskerRight, smul_smul, Units.mul_inv, one_smul,
              of₂_whiskerRight]
        · rw [← whiskerLeft_of₂, ← of₂_whiskerRight]
          exact commute_whisker _ _

end GrQ

/-! ## The relations on upward strands -/

section Up

variable {S : QStrong B C RD k Q} (hsl : ∀ i, C.dot i i = 2) (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

theorem upDiag_D0_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.D0 c d) =
      mkD RD μ [([], .dot (up c), [up d])] ⟨rfl, rfl⟩ := by
  rfl

theorem upDiag_D1_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.D1 c d) =
      mkD RD μ [([up c], .dot (up d), [])] ⟨rfl, rfl⟩ := by
  rfl

theorem upDiag_X2X2_g (c d : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c) =
      mkD RD μ [([], .cross true c d, []), ([], .cross true d c, [])] ⟨rfl, rfl, rfl⟩ := by
  rfl

theorem condUp2 (c d : I) (μ : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d] : X) μ (ob RD μ [up c, up d]) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩

set_option maxHeartbeats 2000000 in
/-- The image of the dot on the left strand of `E_c E_d 1_μ`. -/
theorem conj_D0 (c d : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp2 c d μ)).symm ≫
        (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.D0 c d)) ≫ eqToHom (objI_pos _ _ (condUp2 c d μ)) =
      S.Eg d (cross_up_reg d μ) ◁ S.dotQ c (cross_up_reg c _) := by
  rw [upDiag_D0_g]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_dot_g])
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_dot_g, sig0_cod_dot_g, wd_cons, wd_nil, wt_cons, wt_nil, sig0_colourTgt_g,
    sig0_colourSrc_g]
  rw [chain1_key' S.model ?t1 ?t1' _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact whiskerLeftIso _ (ρ_ _)
  case t1' => exact whiskerLeftIso _ (ρ_ _)
  erw [layerAt_right]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
/-- The image of the dot on the right strand of `E_c E_d 1_μ`. -/
theorem conj_D1 (c d : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp2 c d μ)).symm ≫
        (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.D1 c d)) ≫ eqToHom (objI_pos _ _ (condUp2 c d μ)) =
      S.dotQ d (cross_up_reg d μ) ▷ S.Eg c (cross_up_reg c _) := by
  rw [upDiag_D1_g]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_dot_g])
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_dot_g, sig0_cod_dot_g, wd_cons, wd_nil, wt_cons, wt_nil, sig0_colourTgt_g,
    sig0_colourSrc_g]
  rw [chain1_key' S.model ?t1 ?t1' _ _ _ (𝟙 _) (𝟙 _)]
  case t1 => exact λ_ _
  case t1' => exact λ_ _
  erw [layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
/-- The image of the double crossing on `E_c E_d 1_μ`. -/
theorem conj_X2X2 (c d : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp2 c d μ)).symm ≫
        (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.X2 c d ≫ KLR.Diagram.X2 d c)) ≫
        eqToHom (objI_pos _ _ (condUp2 c d μ)) =
      S.crossQ c d (cross_up_reg d μ) (cross_up_reg c _) (cross_up_reg c μ)
          (by simp only [sh_up]; abel) ≫
        S.crossQ d c (cross_up_reg c μ) (by simp only [sh_up]; abel) (cross_up_reg d μ)
          (cross_up_reg c _) := by
  rw [upDiag_X2X2_g]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g, add_left_comm])
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, wd_cons, wd_nil, wt_cons, wt_nil, sig0_colourTgt_g,
    sig0_colourSrc_g]
  rw [chain2_key' S.model ?t1 ?t1' _ ?t2 ?t2' _ _ _ _ _ (𝟙 _) (𝟙 _)]
  case t1 | t1' | t2 | t2' => exact (λ_ _) ≪≫ (ρ_ _)
  erw [layerAt_whole, layerAt_whole]
  set_option backward.isDefEq.respectTransparency false in
  simp only [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
/-- **CL (2.10)** in the model: for `c ≠ d` the KLR relation `ψ² = Q'_{cd}(x₀, x₁)` on
`E_c E_d 1_μ`, for the normalized dots, with `Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)`, read with
its own outer regions. -/
theorem klr_sqNe (c d : I) (h : c ≠ d)
    (hQ : ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d) (μ : X) :
    (freeLift k (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor).map
      (upLin RD k μ (KLR.Diagram.relation k
        (fun i j => CL.Rescale.scaleP ![(S.rQ i : k), (S.rQ j : k)] (Q i j)) (.sqNe c d h))) =
      0 := by
  set_option backward.isDefEq.respectTransparency false in
  rw [KLR.Diagram.relation, upLin_sub, upLin_of, Functor.map_sub, freeLift_map_of, sub_eq_zero,
    ← freeLift_upDFL, ← Functor.comp_map]
  set G := freeLift k (upDFL k RD μ) ⋙
    freeLift k (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor
  have hG : ∀ f : End (CategoryTheory.Free.of k (KLR.Diagram.ob [c, d])),
      G.map f = functorEndAlg k G _ f := fun _ => rfl
  rw [hG, AlgHom.map_ncEval]
  apply (cancel_epi (eqToHom (objI_pos _ _ (condUp2 c d μ)).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ (condUp2 c d μ)))).1
  have hc : ∀ φ : End (objI S.model (KL3.Diagram.wt RD μ [up c, up d] : X) μ
      (ob RD μ [up c, up d])),
      eqToHom (objI_pos _ _ (condUp2 c d μ)).symm ≫ φ ≫ eqToHom (objI_pos _ _ (condUp2 c d μ)) =
        conjAlg (k := k) (objI_pos _ _ (condUp2 c d μ)) φ := fun φ => (conjAlg_apply _ φ).symm
  simp only [Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [conj_X2X2, hc, AlgHom.map_ncEval]
  have hGof : ∀ D : KLR.Diagram.ob [c, d] ⟶ KLR.Diagram.ob [c, d],
      functorEndAlg k G _ (LinDiagram.of D) =
        (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [up c, up d] : X) μ).functor.map
          (upDiag RD μ D) := by
    intro D
    change (freeLift k _).map ((freeLift k (upDFL k RD μ)).map (LinDiagram.of D)) = _
    rw [freeLift_map_of]
    erw [freeLift_map_of]
    rfl
  have hent : (fun a => conjAlg (k := k) (objI_pos _ _ (condUp2 c d μ))
      (functorEndAlg k G _ (LinDiagram.of (![KLR.Diagram.D0 c d, KLR.Diagram.D1 c d] a)))) =
      ![toEnd (S.Eg d (cross_up_reg d μ) ◁ S.dotQ c (cross_up_reg c _)),
        toEnd (S.dotQ d (cross_up_reg d μ) ▷ S.Eg c (cross_up_reg c _))] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [conjAlg_apply, hGof]
      exact conj_D0 (S := S) hsl Sc c d μ
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [conjAlg_apply, hGof]
      exact conj_D1 (S := S) hsl Sc c d μ
  rw [hent]
  exact S.crossQ_sq c d h hQ _ _ _ _

end Up

end QStrong

end Model

end Categorification.TwoRep
