/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Curls
import Categorification.Diagrams.BicatInterp
import Categorification.Diagrams.KL3.Presentation
import Categorification.QuantumGroup.UDotKL3

/-!
# The `sl₂` model of Khovanov–Lauda's `U` in the graded-Hom bicategory

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 5.5 for `g = sl₂`: a strong 2-representation of `sl₂` satisfying
(BB_w) gives a 2-representation of `U_Q(sl₂)`. This file sets up the data of that 2-functor on the
signature `psig sl2RootDatum` of KL III's `U` (`Categorification.Diagrams.KL3.Basic`), as a model
in the graded-Hom bicategory `K^•` in the sense of `Categorification.Diagrams.BicatInterp`, with
the dots normalized to `r_i = 1`:

* the region of weight `λ` goes to the object `q λ = (λ - n₀) / 2` of the string (only the
  weights `λ ≡ n₀ (mod 2)` matter);
* an upward strand goes to `E 1_λ = grE`, a downward strand to its right adjoint `grR`
  (`R = F⟨n + 1⟩`), transported along the equalities of indices (`Ec`, `Rc`);
* the upward dot and crossing go to the normalized dot `grDotN` and the crossing `grCross`; the
  cups and caps go to the units and counits of the right adjunctions `E ⊣ R` (`grAdj`) and of the
  normalized left adjunctions `R ⊣ E` (`BBw.leftAdjN`), following the table of
  `Categorification.Diagrams.KL3.Basic`; the downward dot and crossing go to the mates of the upward
  ones under the left adjunctions (the rotations `rotDotR`, `rotCrossR` of KL III).

The hom categories of `K^•` have zero objects and additive and linear whiskering
(`GradedHomBicat.hasZeroObject` and the instances below), as `BicatInterp` requires.

## Main definitions

* `StrongSl2.qi`, `StrongSl2.gEc`, `StrongSl2.gRc`: indices and transported strands;
* `StrongSl2.model`: the model of the signature `psig sl2RootDatum` in `K^•`;
* `StrongSl2.gAdjE`, `gAdjL`, `gDot`, `gCross`, `gDotR`, `gCrossR`: the transported adjunctions,
  dots and crossings;
* `StrongSl2.genImg`: the images of the generators.

The verification of the defining relations of `U` for this model (and hence the 2-functor of
CL Theorem 5.5) is not part of this file.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Zero objects and linear whiskering in the graded-Hom bicategory -/

namespace GradedHomCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

theorem isZero_mk {X : C} (h : IsZero X) : IsZero (mk X : GradedHomCat C) := by
  rw [IsZero.iff_id_eq_zero, id_eq, h.eq_of_src (𝟙 X) 0, ShiftedHom.mk₀_zero, homOf_zero]

open scoped ZeroObject in
instance hasZeroObject [HasZeroObject C] : HasZeroObject (GradedHomCat C) :=
  ⟨⟨mk 0, isZero_mk (isZero_zero C)⟩⟩

end GradedHomCat

namespace GradedHomBicat

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

instance hasZeroObject [∀ a b : B, HasZeroObject (a ⟶ b)] (a b : GradedHomBicat B) :
    HasZeroObject (a ⟶ b) :=
  inferInstanceAs (HasZeroObject (GradedHomCat (a.as ⟶ b.as)))

instance precomp_additive (a b c : GradedHomBicat B) (f : a ⟶ b) : (precomp c f).Additive :=
  ⟨fun {_ _} η θ => whiskerLeft_add f η θ⟩

instance postcomp_additive (a b c : GradedHomBicat B) (g : b ⟶ c) : (postcomp a g).Additive :=
  ⟨fun {_ _} η θ => add_whiskerRight η θ g⟩

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]

instance precomp_linear (a b c : GradedHomBicat B) (f : a ⟶ b) : (precomp c f).Linear k :=
  ⟨fun {_ _} η r => whiskerLeft_smul f r η⟩

instance postcomp_linear (a b c : GradedHomBicat B) (g : b ⟶ c) : (postcomp a g).Linear k :=
  ⟨fun {_ _} η r => smul_whiskerRight r η g⟩

end GradedHomBicat

/-! ## The model -/

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

namespace StrongSl2

variable (S : StrongSl2 k B)

/-- The index `q λ = (λ - n₀) / 2` of the object of weight `λ` of the string. (Irreducible, so
that unification never evaluates the integer division.) -/
@[irreducible] def qi (lam : ℤ) : ℤ := (lam - S.n₀) / 2

theorem qi_sh_true (i : Unit) (lam : ℤ) :
    S.qi lam + 1 = S.qi (sh sl2RootDatum ((true, i) : Letter Unit) + lam) := by
  unfold qi
  simp only [sh, sgn_true, sl2RootDatum, one_smul]
  omega

theorem qi_sh_false (i : Unit) (lam : ℤ) :
    S.qi (sh sl2RootDatum ((false, i) : Letter Unit) + lam) + 1 = S.qi lam := by
  unfold qi
  simp only [sh, sgn_false, sl2RootDatum, neg_smul, one_smul]
  omega

variable [GradedBicategory.ShiftCoherence B]

/-- `E 1_n` between the objects of indices `a` and `b = a + 1`, in the graded-Hom bicategory. -/
def gEc (a b : ℤ) (h : a + 1 = b) : of (S.obj a) ⟶ of (S.obj b) := by
  subst h; exact S.grE a

/-- `R_n = (E 1_n)_R` between the objects of indices `b = a + 1` and `a`. -/
def gRc (a b : ℤ) (h : a + 1 = b) : of (S.obj b) ⟶ of (S.obj a) := by
  subst h; exact S.grR a

@[simp] theorem gEc_rfl (a : ℤ) : S.gEc a (a + 1) rfl = S.grE a := rfl

@[simp] theorem gRc_rfl (a : ℤ) : S.gRc a (a + 1) rfl = S.grR a := rfl

/-- The image of a strand between regions `x` (right) and `y` (left): `E` for an upward strand,
`R` for a downward one. -/
def strandImg : (c : Col Unit ℤ) → (x y : ℤ) → c.r = x → sh sl2RootDatum c.l + c.r = y →
    (of (S.obj (S.qi x)) ⟶ of (S.obj (S.qi y)))
  | ⟨(true, i), r⟩, x, y, hx, hy => S.gEc _ _ (by subst hx hy; exact S.qi_sh_true i r)
  | ⟨(false, i), r⟩, x, y, hx, hy => S.gRc _ _ (by subst hx hy; exact S.qi_sh_false i r)

/-- **The `sl₂` model** of the signature of `U` in the graded-Hom bicategory. -/
def model : Model (psig sl2RootDatum) (GradedHomBicat B) where
  obj lam := of (S.obj (S.qi lam))
  strandAt c x y hx hy := S.strandImg c x y hx hy

@[simp] theorem model_obj (lam : ℤ) : S.model.obj lam = of (S.obj (S.qi lam)) := rfl

theorem model_strandAt_true (i : Unit) (r x y : ℤ) (hx : r = x)
    (hy : sh sl2RootDatum ((true, i) : Letter Unit) + r = y) :
    S.model.strandAt ⟨(true, i), r⟩ x y hx hy =
      S.gEc (S.qi x) (S.qi y) (by subst hx hy; exact S.qi_sh_true i r) := rfl

theorem model_strandAt_false (i : Unit) (r x y : ℤ) (hx : r = x)
    (hy : sh sl2RootDatum ((false, i) : Letter Unit) + r = y) :
    S.model.strandAt ⟨(false, i), r⟩ x y hx hy =
      S.gRc (S.qi y) (S.qi x) (by subst hx hy; exact S.qi_sh_false i r) := rfl

theorem sh_false_sh_true (i : Unit) (r : ℤ) :
    sh sl2RootDatum ((false, i) : Letter Unit) + (sh sl2RootDatum ((true, i) : Letter Unit) + r) =
      r := by
  simp only [sh, sgn_false, sgn_true, sl2RootDatum, neg_smul, one_smul]; ring

theorem sh_true_sh_false (i : Unit) (r : ℤ) :
    sh sl2RootDatum ((true, i) : Letter Unit) + (sh sl2RootDatum ((false, i) : Letter Unit) + r) =
      r := by
  simp only [sh, sgn_false, sgn_true, sl2RootDatum, neg_smul, one_smul]; ring

variable [GradedBicategory.IsLinear B k] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)]

/-- The right adjunction `E ⊣ R` (`grAdj`), transported. -/
def gAdjE (a b : ℤ) (h : a + 1 = b) : S.gEc a b h ⊣ S.gRc a b h := by
  subst h; exact S.grAdj a

/-- The normalized dot (`r_i = 1`), transported. -/
def gDot (a b : ℤ) (h : a + 1 = b) : S.gEc a b h ⟶ S.gEc a b h := by
  subst h; exact S.grDotN a

/-- The crossing on `E E 1_n`, transported. -/
def gCross (a b c : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
    S.gEc a b h₁ ≫ S.gEc b c h₂ ⟶ S.gEc a b h₁ ≫ S.gEc b c h₂ := by
  subst h₁ h₂; exact S.grCross a

variable {S} (hS : S.BBw)

/-- The normalized left adjunction `R ⊣ E` (`BBw.leftAdjN`), transported. -/
def gAdjL (a b : ℤ) (h : a + 1 = b) : S.gRc a b h ⊣ S.gEc a b h := by
  subst h; exact hS.leftAdjN a

/-- The downward dot: the mate of the dot under the left adjunction (the rotation `rotDotR`). -/
def gDotR (a b : ℤ) (h : a + 1 = b) : S.gRc a b h ⟶ S.gRc a b h :=
  (Bicategory.conjugateEquiv (gAdjL hS a b h) (gAdjL hS a b h)).symm (S.gDot a b h)

/-- The downward crossing: the mate of the crossing under the left adjunctions (the rotation
`rotCrossR`). -/
def gCrossR (a b c : ℤ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
    S.gRc b c h₂ ≫ S.gRc a b h₁ ⟶ S.gRc b c h₂ ≫ S.gRc a b h₁ :=
  (Bicategory.conjugateEquiv ((gAdjL hS b c h₂).comp (gAdjL hS a b h₁))
    ((gAdjL hS b c h₂).comp (gAdjL hS a b h₁))).symm (S.gCross a b c h₁ h₂)

/-- **The images of the generators** of `U` in the `sl₂` model. -/
def genImg : GenImg S.model where
  gen g := match g with
    | .gen (.dot ⟨(true, i), r⟩) => fun _ _ _ _ =>
        (λ_ _).hom ≫ S.gDot _ _ (S.qi_sh_true i r) ≫ (λ_ _).inv
    | .gen (.dot ⟨(false, i), r⟩) => fun _ _ _ _ =>
        (λ_ _).hom ≫ gDotR hS _ _ (S.qi_sh_false i r) ≫ (λ_ _).inv
    | .gen (.cross true i j ν) => fun _ _ _ _ =>
        (λ_ _).hom ▷ _ ≫ S.gCross _ _ _ (S.qi_sh_true j ν) (S.qi_sh_true i _) ≫ (λ_ _).inv ▷ _
    | .gen (.cross false () () ν) => fun _ _ _ _ => by
        refine (λ_ _).hom ▷ _ ≫ ?_ ≫ (λ_ _).inv ▷ _
        exact gCrossR hS _ _ _ (S.qi_sh_false () _) (S.qi_sh_false () ν)
    | .cup ⟨(true, i), r⟩ => fun _ _ _ _ =>
        (gAdjL hS _ _ (S.qi_sh_true i r)).unit ≫ (λ_ _).inv ▷ _
    | .cup ⟨(false, i), r⟩ => fun _ _ _ _ =>
        (S.gAdjE _ _ (S.qi_sh_false i r)).unit ≫ (λ_ _).inv ▷ _
    | .cap ⟨(true, i), r⟩ => fun _ _ _ _ =>
        (λ_ _).hom ▷ _ ≫ (gAdjL hS _ _ (S.qi_sh_true i r)).counit
    | .cap ⟨(false, i), r⟩ => fun _ _ _ _ =>
        (λ_ _).hom ▷ _ ≫ (S.gAdjE _ _ (S.qi_sh_false i r)).counit

end StrongSl2

end Model

end Categorification.TwoRep
