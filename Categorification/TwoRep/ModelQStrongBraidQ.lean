/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongPoly

/-!
# The deformed braid relation in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2 (4), (2.14): in the model of
`Categorification.TwoRep.ModelQStrong` (normalized dots `r_i⁻¹ x`), for `c ≠ d` the KLR relation
`braidQ` with bottom labels `c d c`, `ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = Q̄'_{cd}(x₀, x₁, x₂)`, holds for the
rescaled polynomials `Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)` (`QStrong.klr_braidQ`). The divided
difference `Q̄_{cd}` is assumed homogeneous of the degree of the relation (as for CL's `Q_{ij}`,
`CL.qbar_qCL_isWeightedHomogeneous`); for `(α_c, α_d) = 0` it then vanishes and the relation is
the braid relation (2.13).

## Main results

* `of₂_homogEval3`: the homogeneous evaluation of a polynomial in three pairwise commuting
  shifted endomorphisms in the graded-Hom bicategory;
* `QStrong.crossQ_braid_corr`: CL (2.14) in the graded-Hom bicategory, for the normalized dots
  (using `CL.Rescale.qbar_scaleP`: `Q̄[Q(u x₀, v x₁)] = u · Q̄[Q](u x₀, v x₁, u x₂)`);
* `QStrong.conj_E0`, `conj_E1`, `conj_E2`: the images of the dots on three upward strands;
* `QStrong.crossQ_braidQ_cast`: the relation in the form produced by the interpretation of the
  braid diagrams (transports between equal intermediate weights);
* `QStrong.klr_braidQ`.
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

/-! ## Polynomials in three shifted endomorphisms -/

section PolyGr3

variable {a b : B} {f : a ⟶ b}

theorem of₂_shMono3 {d₁ d₂ d₃ : ℤ} (x : ShiftedHom f f d₁) (y : ShiftedHom f f d₂)
    (z : ShiftedHom f f d₃) (p q r : ℕ) :
    of₂ _ (shMono3 x y z p q r) =
      ((toEnd (of₂ d₁ x) ^ p : End (of₁ f)) ≫ (toEnd (of₂ d₂ y) ^ q : End (of₁ f))) ≫
        (toEnd (of₂ d₃ z) ^ r : End (of₁ f)) := by
  rw [shMono3, ← of₂_comp_of₂, of₂_shMono2, ← of₂_shPow z r]

/-- The homogeneous evaluation of a polynomial in three pairwise commuting shifted
endomorphisms, in the graded-Hom bicategory (compare `of₂_homogEval2`). -/
theorem of₂_homogEval3 {d₁ d₂ d₃ : ℤ} (P : MvPolynomial (Fin 3) k) (x : ShiftedHom f f d₁)
    (y : ShiftedHom f f d₂) (z : ShiftedHom f f d₃) (deg : ℤ)
    (hP : ∀ m ∈ P.support, (m 0 : ℤ) * d₁ + (m 1 : ℤ) * d₂ + (m 2 : ℤ) * d₃ = deg)
    (hxy : Commute (toEnd (of₂ d₁ x)) (toEnd (of₂ d₂ y)))
    (hxz : Commute (toEnd (of₂ d₁ x)) (toEnd (of₂ d₃ z)))
    (hyz : Commute (toEnd (of₂ d₂ y)) (toEnd (of₂ d₃ z))) :
    toEnd (of₂ deg (homogEval3 k P x y z deg)) =
      KLR.ncEval ![toEnd (of₂ d₁ x), toEnd (of₂ d₂ y), toEnd (of₂ d₃ z)] P := by
  rw [homogEval3, of₂_sum, KLR.ncEval, Finsupp.sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  split_ifs with hm'
  swap
  · exact absurd (hP m hm) hm'
  rw [of₂_smul, of₂_shCast, of₂_shMono3, ← Algebra.smul_def]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  change toEnd (of₂ d₃ z) ^ m 2 * (toEnd (of₂ d₂ y) ^ m 1 * toEnd (of₂ d₁ x) ^ m 0) = _
  have h1 := (hxy.pow_left (m 0)).pow_right (m 1)
  have h2 := (hxz.pow_left (m 0)).pow_right (m 2)
  have h3 := (hyz.pow_left (m 1)).pow_right (m 2)
  rw [← mul_assoc, ← h3.eq, mul_assoc, ← h2.eq, ← mul_assoc, ← h1.eq, mul_assoc]

end PolyGr3

/-! ## Generic algebra -/

section Alg

/-- Conjugation by an isomorphism, as an algebra homomorphism of endomorphism algebras. -/
def isoConjAlg {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞} (e : Z ≅ Z') :
    End Z →ₐ[k] End Z' where
  toFun φ := toEnd (e.inv ≫ φ ≫ e.hom)
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

theorem isoConjAlg_apply {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞}
    (e : Z ≅ Z') (φ : End Z) : isoConjAlg (k := k) e φ = toEnd (e.inv ≫ φ ≫ e.hom) := rfl

theorem ncEval_C_mul' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) (x : k)
    (p : MvPolynomial (Fin n) k) : KLR.ncEval y (MvPolynomial.C x * p) = x • KLR.ncEval y p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [MvPolynomial.C_mul_monomial, CL.Rescale.ncEval_monomial, CL.Rescale.ncEval_monomial,
      map_mul, Algebra.smul_def, mul_assoc]
  | add p q hp hq => rw [mul_add, CL.Rescale.ncEval_add, hp, hq, CL.Rescale.ncEval_add, smul_add]

theorem ncEval_zero' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) :
    KLR.ncEval y (0 : MvPolynomial (Fin n) k) = 0 := by
  have h := CL.Rescale.ncEval_add y (0 : MvPolynomial (Fin n) k) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

end Alg

section Mid

open StringDiagrams Diagrams.BicatInterp

/-- **Three adjacent layers in normal form**, fully reassociated. -/
theorem chain3_key_flat {S' : Signature} {D : Type*} [Bicategory D] (M : Model S' D)
    {a b c d : FB S'} {W₀ W₁ W₂ W₃ P Q₁ Q₂ Q : a ⟶ d}
    {p₁ : a ⟶ b} {q₁ : c ⟶ d} {x₁ y₁ : b ⟶ c} (τ₁ : p₁ ≫ (x₁ ≫ q₁) ≅ W₀)
    (τ₁' : p₁ ≫ (y₁ ≫ q₁) ≅ W₁) (g₁ : M.lift.map x₁ ⟶ M.lift.map y₁)
    {b₂ c₂ : FB S'} {p₂ : a ⟶ b₂} {q₂ : c₂ ⟶ d} {x₂ y₂ : b₂ ⟶ c₂} (τ₂ : p₂ ≫ (x₂ ≫ q₂) ≅ W₁)
    (τ₂' : p₂ ≫ (y₂ ≫ q₂) ≅ W₂) (g₂ : M.lift.map x₂ ⟶ M.lift.map y₂)
    {b₃ c₃ : FB S'} {p₃ : a ⟶ b₃} {q₃ : c₃ ⟶ d} {x₃ y₃ : b₃ ⟶ c₃} (τ₃ : p₃ ≫ (x₃ ≫ q₃) ≅ W₂)
    (τ₃' : p₃ ≫ (y₃ ≫ q₃) ≅ W₃) (g₃ : M.lift.map x₃ ⟶ M.lift.map y₃)
    (A₁ : P ⟶ p₁ ≫ (x₁ ≫ q₁)) (B₁ : p₁ ≫ (y₁ ≫ q₁) ⟶ Q₁)
    (A₂ : Q₁ ⟶ p₂ ≫ (x₂ ≫ q₂)) (B₂ : p₂ ≫ (y₂ ≫ q₂) ⟶ Q₂)
    (A₃ : Q₂ ⟶ p₃ ≫ (x₃ ≫ q₃)) (B₃ : p₃ ≫ (y₃ ≫ q₃) ⟶ Q)
    (X : P ⟶ W₀) (Y : W₃ ⟶ Q) :
    M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁ ≫
        M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂ ≫
          M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃ =
      M.lift.map₂ X ≫ layerAt M τ₁ τ₁' g₁ ≫ layerAt M τ₂ τ₂' g₂ ≫ layerAt M τ₃ τ₃' g₃ ≫
        M.lift.map₂ Y := by
  have h := chain3_key_mid M τ₁ τ₁' g₁ τ₂ τ₂' g₂ τ₃ τ₃' g₃ A₁ B₁ (𝟙 _) A₂ B₂ (𝟙 _) A₃ B₃ X Y
  simp only [PrelaxFunctor.map₂_id, Category.id_comp] at h
  exact h

end Mid

namespace QStrong

section GrQ3

variable (S : QStrong B C RD k Q)

/-- The composite "left, right, left crossing" of the braid relation for bottom labels `c d c`
in the graded-Hom bicategory. -/
abbrev braidLRLQ (c d : I) {l w₁ w₂ w₃ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX d = w₂)
    (e3 : w₂ + RD.iX c = m) (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m) :
    S.Eg c e1 ≫ S.Eg d e2 ≫ S.Eg c e3 ⟶ S.Eg c e1 ≫ S.Eg d e2 ≫ S.Eg c e3 :=
  S.Eg c e1 ◁ S.crossQ c d e2 e3 e4 e5 ≫
    ((α_ (S.Eg c e1) (S.Eg c e4) (S.Eg d e5)).inv ≫ S.crossQ c c e1 e4 e1 e4 ▷ S.Eg d e5 ≫
      (α_ (S.Eg c e1) (S.Eg c e4) (S.Eg d e5)).hom) ≫
    S.Eg c e1 ◁ S.crossQ d c e4 e5 e2 e3

/-- The composite "right, left, right crossing" of the braid relation for bottom labels `c d c`
in the graded-Hom bicategory. -/
abbrev braidRLRQ (c d : I) {l w₁ w₂ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX d = w₂)
    (e3 : w₂ + RD.iX c = m) (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX c = w₂) :
    S.Eg c e1 ≫ S.Eg d e2 ≫ S.Eg c e3 ⟶ S.Eg c e1 ≫ S.Eg d e2 ≫ S.Eg c e3 :=
  ((α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).inv ≫ S.crossQ d c e1 e2 e10 e11 ▷ S.Eg c e3 ≫
      (α_ (S.Eg d e10) (S.Eg c e11) (S.Eg c e3)).hom) ≫
    S.Eg d e10 ◁ S.crossQ c c e11 e3 e11 e3 ≫
    ((α_ (S.Eg d e10) (S.Eg c e11) (S.Eg c e3)).inv ≫ S.crossQ c d e10 e11 e1 e2 ▷ S.Eg c e3 ≫
      (α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).hom)

theorem braidLRLQ_eq (c d : I) {l w₁ w₂ w₃ m : X} (e1 : l + RD.iX c = w₁)
    (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m) (e4 : w₁ + RD.iX c = w₃)
    (e5 : w₃ + RD.iX d = m) :
    S.braidLRLQ c d e1 e2 e3 e4 e5 = of₂ (-(C.dot c d + C.dot c c + C.dot d c))
      (S.braidLRL c d c e1 e2 e3 e4 e5 e1 e4 e2 e3) := by
  simp only [KLRGens.braidLRL, KLRGens.crossL, KLRGens.crossR, ← of₂_comp_of₂, Category.assoc]
  simp only [braidLRLQ, crossQ, whiskerLeft_of₂, of₂_whiskerRight, associator_hom_eq,
    associator_inv_eq, incl₂_eq_of₂, Category.assoc]

theorem braidRLRQ_eq (c d : I) {l w₁ w₂ w₆ m : X} (e1 : l + RD.iX c = w₁)
    (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m) (e10 : l + RD.iX d = w₆)
    (e11 : w₆ + RD.iX c = w₂) :
    S.braidRLRQ c d e1 e2 e3 e10 e11 = of₂ (-(C.dot c d + C.dot c c + C.dot d c))
      (S.braidRLR c d c e1 e2 e3 e1 e2 e3 e10 e11 e11) := by
  simp only [KLRGens.braidRLR, KLRGens.crossL, KLRGens.crossR, ← of₂_comp_of₂, Category.assoc]
  simp only [crossQ, whiskerLeft_of₂, of₂_whiskerRight, associator_hom_eq,
    associator_inv_eq, incl₂_eq_of₂]

theorem commute_whiskerLeft {a' b' c' : GradedHomBicat B} (f : a' ⟶ b') {g : b' ⟶ c'}
    {φ ψ : g ⟶ g} (h : Commute (toEnd φ) (toEnd ψ)) :
    Commute (toEnd (f ◁ φ)) (toEnd (f ◁ ψ)) := by
  change f ◁ ψ ≫ f ◁ φ = f ◁ φ ≫ f ◁ ψ
  rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  exact congrArg (f ◁ ·) h.eq

/-- **CL (2.14)** in the graded-Hom bicategory, for the normalized dots: for `(α_c, α_d) < 0`, on
`E_c E_d E_c 1_λ`, `LRL - RLR = Q̄'_{cd}(x_left, x_middle, x_right)` with
`Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)`. The divided difference `Q̄_{cd}` is assumed homogeneous of
the degree of the relation. -/
theorem crossQ_braid_corr (c d : I) (hcd : C.dot c d < 0)
    (hQ : ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d +
      (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    {l w₁ w₂ w₃ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX d = w₂)
    (e3 : w₂ + RD.iX c = m) (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m)
    (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX c = w₂) :
    toEnd (S.braidLRLQ c d e1 e2 e3 e4 e5) - toEnd (S.braidRLRQ c d e1 e2 e3 e10 e11) =
      KLR.ncEval ![toEnd (S.Eg c e1 ◁ S.Eg d e2 ◁ S.dotQ c e3),
          toEnd (S.Eg c e1 ◁ S.dotQ d e2 ▷ S.Eg c e3),
          toEnd (S.dotQ c e1 ▷ (S.Eg d e2 ≫ S.Eg c e3))]
        (KLR.qbar (CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))) := by
  have h := congrArg (of₂ (-(C.dot c d + C.dot c c + C.dot d c)))
    (S.klr.braid_corr c d hcd e1 e2 e3 e4 e5 e10 e11)
  rw [of₂_smul, of₂_sub, ← braidLRLQ_eq, ← braidRLRQ_eq] at h
  have h' : S.braidLRLQ c d e1 e2 e3 e4 e5 - S.braidRLRQ c d e1 e2 e3 e10 e11 =
      (S.rQ c : k) • of₂ (-(C.dot c d + C.dot c c + C.dot d c)) (homogEval3 k (KLR.qbar (Q c d))
        (shWhiskerLeft (S.E c e1) (shWhiskerLeft (S.E d e2) (S.dot c e3)))
        (shWhiskerLeft (S.E c e1) (shWhiskerRight (S.dot d e2) (S.E c e3)))
        (shWhiskerRight (S.dot c e1) (S.E d e2 ≫ S.E c e3))
        (-(C.dot c d + C.dot c c + C.dot d c))) := by
    rw [← h, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  change toEnd (S.braidLRLQ c d e1 e2 e3 e4 e5 - S.braidRLRQ c d e1 e2 e3 e10 e11) = _
  rw [h']
  change (S.rQ c : k) • toEnd (of₂ _ _) = _
  rw [of₂_homogEval3 _ _ _ _ _ hQ]
  · rw [CL.Rescale.qbar_scaleP, ncEval_C_mul', ← CL.Rescale.ncEval_smul]
    congr 2
    funext t
    fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, dotQ,
        GradedHomBicat.whiskerLeft_smul, smul_smul, ← whiskerLeft_of₂]
      rw [Units.mul_inv, one_smul]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, dotQ]
      simp only [GradedHomBicat.smul_whiskerRight, GradedHomBicat.whiskerLeft_smul, smul_smul,
        ← whiskerLeft_of₂, ← of₂_whiskerRight]
      rw [Units.mul_inv, one_smul]
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, dotQ]
      simp only [GradedHomBicat.smul_whiskerRight, smul_smul, ← of₂_whiskerRight]
      rw [Units.mul_inv, one_smul]
      rfl
  · simp only [← whiskerLeft_of₂, ← of₂_whiskerRight]
    exact commute_whiskerLeft _ (commute_whisker _ _)
  · simp only [← whiskerLeft_of₂, ← of₂_whiskerRight]
    exact commute_whisker _ _
  · simp only [← whiskerLeft_of₂, ← of₂_whiskerRight]
    exact commute_whisker _ _

/-- The deformed braid relation (CL (2.14), bottom labels `c d c`) in the form produced by the
interpretation of the braid diagrams (compare `crossQ_braid_cast`). -/
theorem crossQ_braidQ_cast (c d : I) (hcd : C.dot c d < 0)
    (hQ : ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d +
      (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    {l w₁ w₂ w₂' w₃ w₅' w₆ m : X}
    (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX d = w₂) (e3 : w₂ + RD.iX c = m)
    (e4 : w₁ + RD.iX c = w₃) (e5 : w₃ + RD.iX d = m)
    (e10 : l + RD.iX d = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e11' : w₆ + RD.iX c = w₂')
    (e3' : w₂' + RD.iX c = m) (e12' : w₆ + RD.iX c = w₅') (e9' : w₅' + RD.iX c = m)
    (hw₂ : w₂' = w₂) (hw₅ : w₅' = w₂)
    (p₂ : (S.Eg d e10 ≫ S.Eg c e11) ≫ S.Eg c e3 = (S.Eg d e10 ≫ S.Eg c e11') ≫ S.Eg c e3')
    (p₃ : (S.Eg d e10 ≫ S.Eg c e12') ≫ S.Eg c e9' = (S.Eg d e10 ≫ S.Eg c e11) ≫ S.Eg c e3) :
    toEnd (((α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).hom ≫ S.Eg c e1 ◁ S.crossQ c d e2 e3 e4 e5 ≫
        (α_ (S.Eg c e1) (S.Eg c e4) (S.Eg d e5)).inv) ≫
      S.crossQ c c e1 e4 e1 e4 ▷ S.Eg d e5 ≫
        ((α_ (S.Eg c e1) (S.Eg c e4) (S.Eg d e5)).hom ≫
          S.Eg c e1 ◁ S.crossQ d c e4 e5 e2 e3 ≫ (α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).inv)) -
    toEnd (S.crossQ d c e1 e2 e10 e11 ▷ S.Eg c e3 ≫ eqToHom p₂ ≫
      ((α_ (S.Eg d e10) (S.Eg c e11') (S.Eg c e3')).hom ≫
        S.Eg d e10 ◁ S.crossQ c c e11' e3' e12' e9' ≫
          (α_ (S.Eg d e10) (S.Eg c e12') (S.Eg c e9')).inv) ≫
        eqToHom p₃ ≫ S.crossQ c d e10 e11 e1 e2 ▷ S.Eg c e3) =
    KLR.ncEval ![toEnd ((S.Eg c e1 ≫ S.Eg d e2) ◁ S.dotQ c e3),
        toEnd ((α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).hom ≫
          S.Eg c e1 ◁ (S.dotQ d e2 ▷ S.Eg c e3) ≫ (α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).inv),
        toEnd ((α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).hom ≫
          S.dotQ c e1 ▷ (S.Eg d e2 ≫ S.Eg c e3) ≫ (α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).inv)]
      (KLR.qbar (CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))) := by
  subst hw₂ hw₅
  simp only [eqToHom_refl, Category.id_comp]
  have key := congrArg (isoConjAlg (k := k) (α_ (S.Eg c e1) (S.Eg d e2) (S.Eg c e3)).symm)
    (S.crossQ_braid_corr c d hcd hQ e1 e2 e3 e4 e5 e10 e11)
  rw [map_sub, AlgHom.map_ncEval] at key
  simp only [isoConjAlg_apply, Iso.symm_inv, Iso.symm_hom] at key
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    · simp only [braidLRLQ, Category.assoc]
    · simp only [braidRLRQ, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id]
  · congr 1
    funext t
    fin_cases t
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [comp_whiskerLeft]
    · rfl
    · rfl

end GrQ3

/-! ## Dots on three upward strands -/

section Up3

variable {S : QStrong B C RD k Q} (hsl : ∀ i, C.dot i i = 2) (hS : S.BBw) (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

theorem condUp3 (c d e : I) (μ : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ
      (ob RD μ [up c, up d, up e]) :=
  ⟨⟨rfl, rfl, rfl, trivial⟩, rfl, rfl⟩

theorem upDiag_E0_g (c d e : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.E0 c d e) =
      mkD RD μ [([], .dot (up c), [up d, up e])] ⟨rfl, rfl⟩ := by
  rfl

theorem upDiag_E1_g (c d e : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.E1 c d e) =
      mkD RD μ [([up c], .dot (up d), [up e])] ⟨rfl, rfl⟩ := by
  rfl

theorem upDiag_E2_g (c d e : I) (μ : X) :
    upDiag RD μ (KLR.Diagram.E2 c d e) =
      mkD RD μ [([up c, up d], .dot (up e), [])] ⟨rfl, rfl⟩ := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The image of the dot on the left strand of `E_c E_d E_e 1_μ`. -/
theorem conj_E0 (c d e : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp3 c d e μ)).symm ≫
        (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.E0 c d e)) ≫ eqToHom (objI_pos _ _ (condUp3 c d e μ)) =
      (S.Eg e (cross_up_reg e μ) ≫ S.Eg d (cross_up_reg d _)) ◁ S.dotQ c (cross_up_reg c _) := by
  rw [upDiag_E0_g]
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
/-- The image of the dot on the middle strand of `E_c E_d E_e 1_μ`. -/
theorem conj_E1 (c d e : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp3 c d e μ)).symm ≫
        (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.E1 c d e)) ≫ eqToHom (objI_pos _ _ (condUp3 c d e μ)) =
      (α_ (S.Eg e (cross_up_reg e μ)) (S.Eg d (cross_up_reg d _)) (S.Eg c (cross_up_reg c _))).hom ≫
        S.Eg e (cross_up_reg e μ) ◁ (S.dotQ d (cross_up_reg d _) ▷ S.Eg c (cross_up_reg c _)) ≫
        (α_ (S.Eg e (cross_up_reg e μ)) (S.Eg d (cross_up_reg d _))
          (S.Eg c (cross_up_reg c _))).inv := by
  rw [upDiag_E1_g]
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
  rw [chain1_key' S.model (Iso.refl _) (Iso.refl _) _ _ _ ?X ?Y]
  case X => exact (α_ _ _ _).hom
  case Y => exact (α_ _ _ _).inv
  erw [layerAt_mid]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lift_map₂_associator_hom, lift_map₂_associator_inv]
  rfl

set_option maxHeartbeats 2000000 in
/-- The image of the dot on the right strand of `E_c E_d E_e 1_μ`. -/
theorem conj_E2 (c d e : I) (μ : X) :
    eqToHom (objI_pos _ _ (condUp3 c d e μ)).symm ≫
        (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up e] : X) μ).functor.map
          (upDiag RD μ (KLR.Diagram.E2 c d e)) ≫ eqToHom (objI_pos _ _ (condUp3 c d e μ)) =
      (α_ (S.Eg e (cross_up_reg e μ)) (S.Eg d (cross_up_reg d _)) (S.Eg c (cross_up_reg c _))).hom ≫
        S.dotQ e (cross_up_reg e μ) ▷ (S.Eg d (cross_up_reg d _) ≫ S.Eg c (cross_up_reg c _)) ≫
        (α_ (S.Eg e (cross_up_reg e μ)) (S.Eg d (cross_up_reg d _))
          (S.Eg c (cross_up_reg c _))).inv := by
  rw [upDiag_E2_g]
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
  rw [chain1_key' S.model ?t1 ?t1' _ _ _ ?X ?Y]
  case t1 => exact λ_ _
  case t1' => exact λ_ _
  case X => exact (α_ _ _ _).hom
  case Y => exact (α_ _ _ _).inv
  erw [layerAt_left]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lift_map₂_associator_hom, lift_map₂_associator_inv]
  rfl

set_option maxHeartbeats 10000000 in
/-- **CL (2.14)** in the model: for `c ≠ d` the KLR relation `braidQ` (bottom labels `c d c`) for
the polynomials `Q'_{cd}(u, v) = Q_{cd}(r_c u, r_d v)` on upward strands is killed, read with its
own outer regions. The divided difference `Q̄_{cd}` is assumed homogeneous of the degree of the
relation. -/
theorem klr_braidQ (c d : I) (h : c ≠ d)
    (hQ : ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d +
      (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c)) (μ : X) :
    (freeLift k (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up c] : X)
      μ).functor).map
      (upLin RD k μ (KLR.Diagram.relation k
        (fun i j => CL.Rescale.scaleP ![(S.rQ i : k), (S.rQ j : k)] (Q i j)) (.braidQ c d h))) =
      0 := by
  by_cases hcd : C.dot c d < 0
  swap
  · have hq : KLR.qbar (Q c d) = 0 := by
      ext m
      by_contra hm
      have := hQ m (MvPolynomial.mem_support_iff.2 hm)
      rw [hsl c, hsl d, C.symm d c] at this
      have h0 : 0 ≤ C.dot c d := le_of_not_gt hcd
      have h1 : (0 : ℤ) ≤ (m 0 : ℤ) * 2 + (m 1 : ℤ) * 2 + (m 2 : ℤ) * 2 := by positivity
      omega
    have hq' : KLR.qbar (CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d)) = 0 := by
      rw [CL.Rescale.qbar_scaleP, hq, map_zero, mul_zero]
    have hz : KLR.Diagram.lpoly k
        ![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c]
        (0 : MvPolynomial (Fin 3) k) = 0 := by
      exact ncEval_zero' (A := End (CategoryTheory.Free.of k (KLR.Diagram.ob [c, d, c]))) _
    set_option backward.isDefEq.respectTransparency false in
    rw [KLR.Diagram.relation, hq', hz, sub_zero, upLin_sub, upLin_of, upLin_of, Functor.map_sub,
      freeLift_map_of, freeLift_map_of]
    exact klr_braid_gen' hsl hS Sc c d c (fun h' => hcd h'.2) μ
  set_option backward.isDefEq.respectTransparency false in
  rw [KLR.Diagram.relation, upLin_sub, upLin_sub, upLin_of, upLin_of, Functor.map_sub,
    Functor.map_sub, freeLift_map_of, freeLift_map_of, sub_eq_zero,
    ← freeLift_upDFL, ← Functor.comp_map]
  set G := freeLift k (upDFL k RD μ) ⋙
    freeLift k (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up c] : X) μ).functor
  have hG : ∀ f : End (CategoryTheory.Free.of k (KLR.Diagram.ob [c, d, c])),
      G.map f = functorEndAlg k G _ f := fun _ => rfl
  have hGof : ∀ D : KLR.Diagram.ob [c, d, c] ⟶ KLR.Diagram.ob [c, d, c],
      functorEndAlg k G _ (LinDiagram.of D) =
        (interp (genImg hsl hS Sc) (KL3.Diagram.wt RD μ [up c, up d, up c] : X) μ).functor.map
          (upDiag RD μ D) := by
    intro D
    change (freeLift k _).map ((freeLift k (upDFL k RD μ)).map (LinDiagram.of D)) = _
    rw [freeLift_map_of]
    erw [freeLift_map_of]
    rfl
  have hent : (fun a => conjAlg (k := k) (objI_pos _ _ (condUp3 c d c μ))
      (functorEndAlg k G _ (LinDiagram.of
        (![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c] a)))) =
      ![toEnd ((S.Eg c (cross_up_reg c μ) ≫ S.Eg d (cross_up_reg d _)) ◁
          S.dotQ c (cross_up_reg c _)),
        toEnd ((α_ (S.Eg c (cross_up_reg c μ)) (S.Eg d (cross_up_reg d _))
          (S.Eg c (cross_up_reg c _))).hom ≫
          S.Eg c (cross_up_reg c μ) ◁ (S.dotQ d (cross_up_reg d _) ▷ S.Eg c (cross_up_reg c _)) ≫
          (α_ (S.Eg c (cross_up_reg c μ)) (S.Eg d (cross_up_reg d _))
            (S.Eg c (cross_up_reg c _))).inv),
        toEnd ((α_ (S.Eg c (cross_up_reg c μ)) (S.Eg d (cross_up_reg d _))
          (S.Eg c (cross_up_reg c _))).hom ≫
          S.dotQ c (cross_up_reg c μ) ▷ (S.Eg d (cross_up_reg d _) ≫ S.Eg c (cross_up_reg c _)) ≫
          (α_ (S.Eg c (cross_up_reg c μ)) (S.Eg d (cross_up_reg d _))
            (S.Eg c (cross_up_reg c _))).inv)] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [conjAlg_apply, hGof]
      exact conj_E0 hsl hS Sc c d c μ
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [conjAlg_apply, hGof]
      exact conj_E1 hsl hS Sc c d c μ
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [conjAlg_apply, hGof]
      exact conj_E2 hsl hS Sc c d c μ
  rw [hG]
  have hc : Cond (S := psig RD) (KL3.Diagram.wt RD μ [up c, up d, up c] : X) μ
      (ob RD μ [up c, up d, up c]) := condUp3 c d c μ
  apply (cancel_epi (eqToHom (objI_pos _ _ hc).symm)).1
  apply (cancel_mono (eqToHom (objI_pos _ _ hc))).1
  have hcj : ∀ φ : End (objI S.model (KL3.Diagram.wt RD μ [up c, up d, up c] : X) μ
      (ob RD μ [up c, up d, up c])),
      eqToHom (objI_pos _ _ hc).symm ≫ φ ≫ eqToHom (objI_pos _ _ hc) =
        conjAlg (k := k) (objI_pos _ _ hc) φ := fun φ => (conjAlg_apply _ φ).symm
  conv_rhs => rw [Category.assoc, hcj]
  rw [AlgHom.map_ncEval, AlgHom.map_ncEval, hent]
  rw [upDiag_braidL_g, upDiag_braidR_g]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Preadditive.sub_comp, Preadditive.comp_sub]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Interpretation.functor_map, mkD, Diagram.layers_mk, layList_cons, layList_nil,
    Interpretation.mapChain]
  set_option backward.isDefEq.respectTransparency false in
  simp only [lay, Shape.gen, wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append,
    List.cons_append, Shape.dom]
  dsimp only [up] at *
  generalize_proofs
  generalize h1 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x1 at *
  obtain rfl :
      x1 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h1]; abel
  generalize h2 :
      sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) = x2 at *
  obtain rfl :
      x2 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h2]; abel
  generalize h4 :
      sh RD ((true, c) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x4 at *
  obtain rfl :
      x4 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h4]; abel
  generalize h5 :
      sh RD ((true, c) : Letter I) + (sh RD ((true, c) : Letter I) +
        (sh RD ((true, d) : Letter I) + μ)) = x5 at *
  obtain rfl :
      x5 = sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) +
        (sh RD ((true, c) : Letter I) + μ)) := by
    rw [← h5]; abel
  generalize h6 : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x6 at *
  obtain rfl :
      x6 = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
    rw [← h6]; abel
  generalize h8 : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x8 at *
  obtain rfl :
      x8 = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
    rw [← h8]; abel
  rw [layerI_pos _ _ _ _ ?c1]
  try rw [layerI_pos _ _ _ _ ?c2]
  try rw [layerI_pos _ _ _ _ ?c3]
  try rw [layerI_pos _ _ _ _ ?c4]
  try rw [layerI_pos _ _ _ _ ?c5]
  try rw [layerI_pos _ _ _ _ ?c6]
  all_goals try (refine ⟨?_, ?_, ?_⟩ <;>
      simp [Signature.ok, Signature.endR, Layer.dom, sig0_colourSrc_g, sig0_colourTgt_g,
        sig0_dom_cross_g] <;> abel)
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  unfold coreC core
  dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_gen,
    Signature.pivotal_cod_gen, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, wd_cons, wd_nil, wt_cons,
    wt_nil, sig0_colourTgt_g, sig0_colourSrc_g]
  simp only [Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w0 _]
  set_option backward.isDefEq.respectTransparency false in
  rw [eqToHom_word ?w1 _]
  case w0 | w1 =>
    simp [Layer.cod, Layer.dom, sig0_cod_cross_g, sig0_dom_cross_g, add_left_comm]
  rw [chain3_key_flat S.model ?t1 ?t1' _ ?t2 ?t2' _ ?t3 ?t3' _ _ _ _ _ _ _ (𝟙 _) (𝟙 _),
    chain3_keyZ12 S.model ?t4 ?t4' _ ?t5 ?t5' _ ?t6 ?t6' _ _ _ _ _ _ _ _ _ (𝟙 _) (eqToHom ?z2)
      (eqToHom ?z3) (𝟙 _)]
  case t1 | t1' | t3 | t3' | t5 | t5' =>
    exact whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm
  case t2 | t2' | t4 | t4' | t6 | t6' => exact λ_ _
  case z2 =>
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl :
        x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  case z3 =>
    generalize_proofs
    generalize hx : sh RD ((true, c) : Letter I) + (sh RD ((true, d) : Letter I) + μ) = x at *
    obtain rfl :
        x = sh RD ((true, d) : Letter I) + (sh RD ((true, c) : Letter I) + μ) := by
      rw [← hx]; abel
    rfl
  repeat erw [layerAt_right_assoc]
  repeat erw [layerAt_left]
  simp only [lift_map₂_eqToHom, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  exact S.crossQ_braidQ_cast c d hcd hQ _ _ _ _ _ _ _ _ _ _ _ (add_left_comm _ _ _)
    (add_left_comm _ _ _) _ _

end Up3

end QStrong

end Model

end Categorification.TwoRep
