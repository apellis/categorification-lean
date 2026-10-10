/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpKLR
import Categorification.TwoRep.RouqInterp

/-!
# Right-adjunction mixed pitchfork and corrected braid

The cup pitchfork `RouqFamily.mixedSigma_cup` and the mate form of the
repeated-outer-colour mixed braid `RouqFamily.mixedSigma_braidQ` follow from the
original source crossing, right adjunctions and upward braid relation. These
are the moves of Brundan, arXiv:1501.00350v1, Lemma 2.1, (2.2) and (2.4), used
in the proof of Lemma 5.2. The correction is retained as an actual right mate
of the evaluated divided difference, with every weight and associator explicit.

For `BrundanUpKLR S P`, specialize `Q` to `brundanQ P`. The theorem
`brundanQ_qbar` expands its unrestricted rectangular coefficients; it does not
replace the source polynomial by the degree-filtered `CL.qCL P`. The coefficient
of the leading divided difference is `P.t i j`, not `P.t j i`. The `p = 0`
correction vanishes because the inner sum is empty, without any homogeneity
hypothesis. No target relation, mixed cyclicity or extra finiteness axiom is
assumed.

These are precursors, not Lemma 5.2 or all-weight mixed crossing cyclicity.
The inversion and dotted bubble/curl reductions, the scalar-corrected rotations
and their actual admissible CL relation consumers remain to be proved. No
aggregate presentation soundness or quotient descent is asserted.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {B : Type u} [Bicategory.{w, v} B]

/-- The cup pitchfork for the right mate, with both regions explicit. -/
theorem rightMate_cup_pitchfork {a b c d : B} {g : a ⟶ c} {h : b ⟶ d}
    {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (x : g ≫ l₂ ⟶ l₁ ≫ h) :
    (λ_ g).inv ≫ A₁.unit ▷ g ≫ (α_ l₁ r₁ g).hom ≫
      l₁ ◁ mateEquiv A₁ A₂ x =
    (ρ_ g).inv ≫ g ◁ A₂.unit ≫ (α_ g l₂ r₂).inv ≫
      x ▷ r₂ ≫ (α_ l₁ h r₂).hom := by
  have H := (mateEquiv_eq_iff A₁ A₂ x (mateEquiv A₁ A₂ x)).mp rfl
  simpa only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply,
    Category.assoc] using H

/-- Right mates commute with postcomposition on the unbent edge. -/
theorem rightMate_post {a b c d : B} {g : a ⟶ c} {h h' : b ⟶ d}
    {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (x : g ≫ l₂ ⟶ l₁ ≫ h) (y : h ⟶ h') :
    mateEquiv A₁ A₂ (x ≫ l₁ ◁ y) = mateEquiv A₁ A₂ x ≫ y ▷ r₂ := by
  simp only [mateEquiv_apply', whiskerLeft_comp, comp_whiskerRight]
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ A₂.unit ⊗≫ r₁ ◁ x ▷ r₂ ⊗≫
        (((r₁ ≫ l₁) ◁ y ≫ A₁.counit ▷ h') ▷ r₂) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

/-- Right mates commute with precomposition on the unbent edge. -/
theorem rightMate_pre {a b c d : B} {g g' : a ⟶ c} {h : b ⟶ d}
    {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (x : g' ≫ l₂ ⟶ l₁ ≫ h) (y : g ⟶ g') :
    mateEquiv A₁ A₂ (y ▷ l₂ ≫ x) = r₁ ◁ y ≫ mateEquiv A₁ A₂ x := by
  simp only [mateEquiv_apply', whiskerLeft_comp, comp_whiskerRight]
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ (g ◁ A₂.unit ≫ y ▷ (l₂ ≫ r₂)) ⊗≫
        r₁ ◁ x ▷ r₂ ⊗≫ A₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

variable [∀ a b : B, Preadditive (a ⟶ b)]
variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
variable {RD : RootDatum C X Y}

/-- The divided difference of Brundan's rectangular polynomial, with no
homogeneity restriction on `s`. This is the polynomial in the bent braid (2.4). -/
theorem brundanQ_qbar (P : CL.CLScalars C k) {i j : I} (hd : C.dot i j ≠ 0) :
    KLR.qbar (brundanQ P i j) =
      MvPolynomial.C (P.t i j : k) *
        ∑ r ∈ Finset.range (C.dij i j),
          MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (C.dij i j - 1 - r) +
      ∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
        MvPolynomial.C (P.s i j p q) * MvPolynomial.X 1 ^ q *
          ∑ r ∈ Finset.range p,
            MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (p - 1 - r) := by
  classical
  rw [brundanQ, ite_eq_right hd, KLR.qbar_add, KLR.qbar_add, CL.qbar_sum]
  have e₁ : (MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ C.dij i j :
      MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ C.dij i j *
        MvPolynomial.X 1 ^ 0 := by rw [pow_zero, mul_one]
  have e₂ : (MvPolynomial.C (P.t j i : k) * MvPolynomial.X 1 ^ C.dij j i :
      MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t j i : k) * MvPolynomial.X 0 ^ 0 *
        MvPolynomial.X 1 ^ C.dij j i := by rw [pow_zero, mul_one]
  rw [e₁, e₂, CL.qbar_C_mul_X_pow_mul_X_pow, CL.qbar_C_mul_X_pow_mul_X_pow]
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [CL.qbar_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact CL.qbar_C_mul_X_pow_mul_X_pow _ p q

namespace RouqFamily
variable (S : RouqFamily (B := B) RD)
/-- The source sideways crossing, using only the prescribed right adjunctions. -/
def mixedSigma (i j : I) {a b c d : X} (hj : a + RD.iX j = b)
    (hi' : b + RD.iX i = d) (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
    S.F i hi ≫ S.E j hj ⟶ S.E j hj' ≫ S.F i hi' :=
  mateEquiv (S.adj i hi) (S.adj i hi') (S.cross i j hj hi' hi hj')

/-- The right-adjunction cup pitchfork for the actual source crossing. -/
theorem mixedSigma_cup (i j : I) {a b c d : X} (hj : a + RD.iX j = b)
    (hi' : b + RD.iX i = d) (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d) :
    (λ_ (S.E j hj)).inv ≫ (S.adj i hi).unit ▷ S.E j hj ≫
      (α_ (S.E i hi) (S.F i hi) (S.E j hj)).hom ≫
      S.E i hi ◁ S.mixedSigma i j hj hi' hi hj' =
    (ρ_ (S.E j hj)).inv ≫ S.E j hj ◁ (S.adj i hi').unit ≫
      (α_ (S.E j hj) (S.E i hi') (S.F i hi')).inv ≫
      S.cross i j hj hi' hi hj' ▷ S.F i hi' ≫
      (α_ (S.E i hi) (S.E j hj') (S.F i hi')).hom :=
  rightMate_cup_pitchfork (S.adj i hi) (S.adj i hi') (S.cross i j hj hi' hi hj')

variable [AdditiveWhiskering B]

/-- The repeated-outer-colour mixed braid, obtained by bending the source braid.
The sideways crossings are the actual right mates, not additional generators. -/
theorem mixedSigma_braidQ {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Q) (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c) :
    ((α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).inv ≫
      S.mixedSigma i i h₁ h₄ h₁ h₄ ▷ S.E j h₂ ≫
      (α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).hom ≫
      S.E i h₄ ◁ S.mixedSigma i j h₂ h₃ h₄ h₅ ≫
      (α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫
      S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃) -
    (S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ ≫
      (α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).inv ≫
      S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
      (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).hom ≫
      S.E j h₂ ◁ S.mixedSigma i i h₇ h₃ h₇ h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).inv) =
    mateEquiv (S.adj i h₁) (S.adj i h₃)
      ((α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).hom ≫
        KLR.ncEval (A := End (S.E i h₁ ≫ (S.E j h₂ ≫ S.E i h₃)))
          ![S.E i h₁ ◁ (S.E j h₂ ◁ S.dot i h₃),
            S.E i h₁ ◁ (S.dot j h₂ ▷ S.E i h₃),
            S.dot i h₁ ▷ (S.E j h₂ ≫ S.E i h₃)] (KLR.qbar (Q i j))) := by
  have hl := mateEquiv_vcomp (S.adj i h₁) (S.adj i h₄) (S.adj i h₃)
    (S.cross i i h₁ h₄ h₁ h₄) (S.cross i j h₂ h₃ h₄ h₅)
  have hr := mateEquiv_vcomp (S.adj i h₁) (S.adj i h₇) (S.adj i h₃)
    (S.cross i j h₆ h₇ h₁ h₂) (S.cross i i h₇ h₃ h₇ h₃)
  have hp := rightMate_post (S.adj i h₁) (S.adj i h₃)
    (leftAdjointSquare.vcomp (S.cross i i h₁ h₄ h₁ h₄)
      (S.cross i j h₂ h₃ h₄ h₅)) (S.cross j i h₄ h₅ h₂ h₃)
  have hq := rightMate_pre (S.adj i h₁) (S.adj i h₃)
    (leftAdjointSquare.vcomp (S.cross i j h₆ h₇ h₁ h₂)
      (S.cross i i h₇ h₃ h₇ h₃)) (S.cross j i h₁ h₂ h₆ h₇)
  rw [hl] at hp
  rw [hr] at hq
  simp only [rightAdjointSquare.vcomp, Category.assoc] at hp hq
  simp only [mixedSigma]
  rw [← hp, ← hq]
  have hadd : ∀ (x y : (S.E i h₁ ≫ S.E j h₂) ≫ S.E i h₃ ⟶
      S.E i h₁ ≫ (S.E j h₂ ≫ S.E i h₃)),
      mateEquiv (S.adj i h₁) (S.adj i h₃) (x - y) =
        mateEquiv (S.adj i h₁) (S.adj i h₃) x -
          mateEquiv (S.adj i h₁) (S.adj i h₃) y := by
    intro x y
    simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
      Adjunction.homEquiv₂_apply, RightwardCrossing.sub_whiskerRight'',
      RightwardCrossing.whiskerLeft_sub'', Preadditive.comp_sub, Preadditive.sub_comp]
  rw [← hadd]
  apply congrArg (mateEquiv (S.adj i h₁) (S.adj i h₃))
  rw [← H.braidQ i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇, Preadditive.comp_sub]
  congr 1 <;> simp only [leftAdjointSquare.vcomp, Category.assoc, Iso.hom_inv_id_assoc]

end RouqFamily
end Categorification.TwoRep
