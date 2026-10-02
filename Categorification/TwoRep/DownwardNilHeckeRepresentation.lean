import Categorification.TwoRep.DownwardNilHeckeBraid

/-!
# The nilHecke representation on actual downward words

`fWordNilHeckeHom n r` maps the existing polynomial-operator algebra `NH_(n+1)`
into the endomorphism algebra of the actual `n + 1`-factor downward word.
Dots are counted from the right, crossings are uniformly scaled by `-rQ⁻¹`,
and multiplication in `End` is reversed categorical composition.
The componentwise module and linear-category instances below supply the natural
`k`-algebra structure on this existing endomorphism ring; they add no hypotheses
beyond linearity of the Hom categories and their shift functors.

The separate `fEmptyNilHeckeHom r` treats `NH_0` on the identity 1-morphism at
`S.obj r`; it does not reinterpret `fWord 0 r`, which still has one factor.
All supplied adjunctions and graded coherence/linearity hypotheses remain explicit.
No faithfulness, automatic biadjointness, or unrestricted Cautis–Lauda result is asserted.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open GradedHomBicat
universe w v u

namespace GradedHomCat
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  (k : Type*) [Field k] [Linear k C]

/-- The natural componentwise scalar action on finite-sum graded morphisms. -/
instance homModule (X Y : GradedHomCat C) : Module k (X ⟶ Y) :=
  inferInstanceAs (Module k (GHom X.as Y.as))

/-- Homogeneous inclusion respects the componentwise scalar action. -/
theorem homOf_smul {X Y : C} (d : ℤ) (c : k) (f : ShiftedHom X Y d) :
    homOf d (c • f) = c • homOf d f :=
  DirectSum.of_smul _ _ _ _

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- Composition is linear for the natural finite-sum scalar action. -/
instance linear : Linear k (GradedHomCat C) where
  homModule X Y := homModule k X Y
  smul_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ c f g
    induction f using hom_induction with
    | zero => simp
    | add f f' hf hf' => simp only [smul_add, Preadditive.add_comp, hf, hf']
    | homOf a f =>
      induction g using hom_induction with
      | zero => simp
      | add g g' hg hg' => simp only [Preadditive.comp_add, hg, hg', smul_add]
      | homOf b g =>
        rw [← homOf_smul, homOf_comp_homOf _ _ rfl, homOf_comp_homOf _ _ rfl,
          ShiftedHom.smul_comp', homOf_smul]
  comp_smul := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f c g
    induction f using hom_induction with
    | zero => simp
    | add f f' hf hf' => simp only [Preadditive.add_comp, hf, hf', smul_add]
    | homOf a f =>
      induction g using hom_induction with
      | zero => simp
      | add g g' hg hg' => simp only [smul_add, Preadditive.comp_add, hg, hg']
      | homOf b g =>
        rw [← homOf_smul, homOf_comp_homOf _ _ rfl, homOf_comp_homOf _ _ rfl,
          ShiftedHom.comp_smul', homOf_smul]
end GradedHomCat

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]
/-- Hom categories inherit the natural graded-sum linear structure. -/
instance GradedHomBicat.homLinear (k : Type*) [Field k]
    [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]
    (a b : GradedHomBicat B) : Linear k (a ⟶ b) :=
  inferInstanceAs (Linear k (GradedHomCat (a.as ⟶ b.as)))

namespace StrongSl2
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] (S : StrongSl2 k B)

/-- The nilHecke algebra acts on the actual nonempty downward word. -/
def fWordNilHeckeHom (n : ℕ) (r : ℤ) :
    NilHecke.nilHecke k (n + 1) →ₐ[k] End (of₁ (S.fWord n r)) :=
  KLR.NilHecke.lift (S.fWord_isNilHeckeFamily n r)

/-- Polynomial generators act by the existing right-counted homogeneous dots. -/
@[simp] theorem fWordNilHeckeHom_mulX (n : ℕ) (r : ℤ) (a : Fin (n + 1)) :
    S.fWordNilHeckeHom n r
      ⟨NilHecke.mulX k (n + 1) a, NilHecke.mulX_mem a⟩ =
      of₂ 2 (S.fWordDot n r a.val) :=
  KLR.NilHecke.lift_mulX (S.fWord_isNilHeckeFamily n r) a

/-- Divided differences act by the existing normalized crossings, including zero extension. -/
@[simp] theorem fWordNilHeckeHom_dd (n j : ℕ) (r : ℤ) :
    S.fWordNilHeckeHom n r
      ⟨NilHecke.dd k (n + 1) j, NilHecke.dd_mem j⟩ =
      of₂ (-2) (S.fWordNormalizedCross n r j) :=
  KLR.NilHecke.lift_dd (S.fWord_isNilHeckeFamily n r) j

/-- The crossing evaluation with the scalar normalization made explicit. -/
theorem fWordNilHeckeHom_dd_eq (n j : ℕ) (r : ℤ) :
    S.fWordNilHeckeHom n r
      ⟨NilHecke.dd k (n + 1) j, NilHecke.dd_mem j⟩ =
      of₂ (-2) (-((S.rQ : k)⁻¹) • S.fWordCross n r j) :=
  S.fWordNilHeckeHom_dd n j r

/-- The actual generator evaluations uniquely determine this algebra homomorphism. -/
theorem fWordNilHeckeHom_unique (n : ℕ) (r : ℤ)
    (φ : NilHecke.nilHecke k (n + 1) →ₐ[k] End (of₁ (S.fWord n r)))
    (hx : ∀ a : Fin (n + 1),
      φ ⟨NilHecke.mulX k (n + 1) a, NilHecke.mulX_mem a⟩ =
        of₂ 2 (S.fWordDot n r a.val))
    (hd : ∀ j : ℕ, φ ⟨NilHecke.dd k (n + 1) j, NilHecke.dd_mem j⟩ =
        of₂ (-2) (S.fWordNormalizedCross n r j)) :
    φ = S.fWordNilHeckeHom n r := by
  apply KLR.NilHecke.algHom_ext
  · intro a
    exact (hx a).trans (S.fWordNilHeckeHom_mulX n r a).symm
  · intro j
    exact (hd j).trans (S.fWordNilHeckeHom_dd n j r).symm

omit [GradedBicategory.IsLinear B k] in
/-- The empty family acts on the identity 1-morphism, not on the one-factor word. -/
private theorem fEmpty_isNilHeckeFamily (r : ℤ) :
    KLR.NilHecke.IsNilHeckeFamily (B := End (of₁ (𝟙 (S.obj r)))) 0
      (fun a => Fin.elim0 a) (fun _ => 0) where
  x_comm a := Fin.elim0 a
  d_x_comm _ a := Fin.elim0 a
  d_comm _ _ _ := by simp
  d_sq _ := by simp
  braid _ := by simp
  x_d_sub _ h := by omega
  d_x_sub _ h := by omega
  d_zero _ _ := rfl

/-- The zero-factor nilHecke algebra acts on the genuine identity 1-morphism. -/
def fEmptyNilHeckeHom (r : ℤ) :
    NilHecke.nilHecke k 0 →ₐ[k] End (of₁ (𝟙 (S.obj r))) :=
  KLR.NilHecke.lift (S.fEmpty_isNilHeckeFamily r)

/-- Every zero-factor divided difference has zero image. There are no dot generators. -/
@[simp] theorem fEmptyNilHeckeHom_dd (r : ℤ) (j : ℕ) :
    S.fEmptyNilHeckeHom r ⟨NilHecke.dd k 0 j, NilHecke.dd_mem j⟩ = 0 :=
  KLR.NilHecke.lift_dd (S.fEmpty_isNilHeckeFamily r) j

/-- Scalars act on the empty word by scalar multiples of its identity 2-morphism. -/
@[simp] theorem fEmptyNilHeckeHom_algebraMap (r : ℤ) (c : k) :
    S.fEmptyNilHeckeHom r (algebraMap k (NilHecke.nilHecke k 0) c) =
      c • 𝟙 (of₁ (𝟙 (S.obj r))) := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  rfl

end StrongSl2
end Categorification.TwoRep
