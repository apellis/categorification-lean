/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0UDot

/-!
# Associativity and unit isomorphisms of the composition in `U̇`; the ring `K₀(U̇)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.4,
Definition 3.21 (the composition functors `U̇(λ, λ') × U̇(λ', λ'') → U̇(λ, λ'')`), and §3.6
(TeX `\subsection{$K_0(\dot{\cal{U}})$ and homomorphism $\gamma$}`, label `subsec_KzeroU`):
"Composition bifunctors […] induce `ℤ[q, q⁻¹]`-bilinear maps
`K₀(U̇(λ, λ')) ⊗ K₀(U̇(λ', λ'')) → K₀(U̇(λ, λ''))` turning `K₀(U̇)` into a `ℤ[q, q⁻¹]`-linear
additive category with objects `λ ∈ X`. Alternatively, we may view `K₀(U̇)` as a non-unital
`ℤ[q, q⁻¹]`-algebra […] with a family of idempotents `[1_λ]`."

For a presentation `P` of an even signature with a grading, the composition functor
`hcompDot : U̇(l, m) × U̇(m, n) ⥤ U̇(l, n)` (`Categorification.Diagrams.KL3.KaroubiHcomp`) is
associative and unital up to natural isomorphism *on objects*, which is all that `K₀` needs:

* `hcomp_assoc`: the horizontal composition of 2-morphisms of the presented (strict) bicategory
  is associative up to the identifications `(x y) z = x (y z)` of words;
* `hcompDotAssoc A B C : (A B) C ≅ A (B C)` in `U̇(l, o)`;
* `hcompDotIdLeft`, `hcompDotIdRight`: `1_l A ≅ A`, `A 1_m ≅ A`, where `1_l = objOf (𝟙 l) 0`
  is the identity 1-morphism (the empty word) with shift `0`;
* `K0U.mul_assoc`: **the product of `K₀(U̇)` is associative**;
* `K0U.one_mul`, `K0U.mul_one`: the classes `[1_λ]` are two-sided units for the product (on
  the appropriate blocks), so `K₀(U̇)` is a `ℤ[q, q⁻¹]`-linear category with objects the
  regions, i.e. an idempotented `ℤ[q, q⁻¹]`-algebra with idempotents `[1_λ]`.

The coherence of these isomorphisms (pentagon, triangle, naturality) is not needed for `K₀` and
is not formalized.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

universe w v u₀ u₁ u₂

namespace GradedBicat

open StringDiagrams Presentation

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k]
  {P : Presentation.{w, v} S k} {deg : S.Gen → ℤ} {l m n o : P.Bicat}

/-! ## Associativity and unitality of the horizontal composition of 2-morphisms -/

section Hcomp

variable {x x' : Bicat.Hom l m} {y y' : Bicat.Hom m n} {z z' : Bicat.Hom n o}

theorem wRAt_wRAt (f : P.obj x.obj ⟶ P.obj x'.obj) :
    P.wRAt l.region (P.wRAt l.region f y.obj x.start_eq x'.start_eq) z.obj x.start_eq
        x'.start_eq =
      eqToHom (congrArg P.obj (Obj.tensor_assoc x.obj y.obj z.obj)) ≫
        P.wRAt l.region f (y.obj.tensor z.obj) x.start_eq x'.start_eq ≫
          eqToHom (congrArg P.obj (Obj.tensor_assoc x'.obj y.obj z.obj)).symm := by
  rw [P.wRAt_tensor (x.composable y) (y.composable z)]
  simp

/-- **Associativity of the horizontal composition** in the presented bicategory:
`(f ∘ g) ∘ h = f ∘ (g ∘ h)`, up to the identifications `(x y) z = x (y z)` of words. -/
theorem hcomp_assoc (f : P.obj x.obj ⟶ P.obj x'.obj) (g : P.obj y.obj ⟶ P.obj y'.obj)
    (h : P.obj z.obj ⟶ P.obj z'.obj) :
    P.hcomp l.region (P.hcomp l.region f g x.start_eq x'.start_eq) h x.start_eq x'.start_eq =
      eqToHom (congrArg P.obj (Obj.tensor_assoc x.obj y.obj z.obj)) ≫
        P.hcomp l.region f (P.hcomp m.region g h y.start_eq y'.start_eq) x.start_eq
          x'.start_eq ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc x'.obj y'.obj z'.obj)).symm := by
  simp only [hcomp]
  rw [P.wRAt_comp (a := x.obj.tensor y.obj) (a' := x'.obj.tensor y.obj)
      (a'' := x'.obj.tensor y'.obj) x.start_eq x'.start_eq x'.start_eq, wRAt_wRAt,
    P.wRAt_wL (x'.composable y) (y.composable z) g x'.start_eq y.start_eq y'.start_eq,
    P.wL_tensor (x'.composable y') (y'.composable z), P.wL_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- `𝟙 ∘ g = g` up to `1 x = x`. -/
theorem hcomp_id_left (g : P.obj y.obj ⟶ P.obj y'.obj) :
    P.hcomp m.region (𝟙 (P.obj (Bicat.Hom.id m).obj)) g rfl rfl =
      eqToHom (congrArg P.obj (Obj.nil_tensor y.start_eq)) ≫ g ≫
        eqToHom (congrArg P.obj (Obj.nil_tensor y'.start_eq)).symm := by
  rw [hcomp, P.wRAt_id (r := m.region) (a := (Bicat.Hom.id m).obj) rfl _
    ((Bicat.Hom.id m).composable y).ok_endR, Category.id_comp]
  exact P.wL_nil g y.wf y.start_eq y'.start_eq

/-- `f ∘ 𝟙 = f` up to `x 1 = x`. -/
theorem hcomp_id_right (f : P.obj x.obj ⟶ P.obj x'.obj) :
    P.hcomp l.region f (𝟙 (P.obj (Bicat.Hom.id m).obj)) x.start_eq x'.start_eq =
      eqToHom (congrArg P.obj (Obj.tensor_nil x.obj m.region)) ≫ f ≫
        eqToHom (congrArg P.obj (Obj.tensor_nil x'.obj m.region)).symm := by
  rw [hcomp, P.wL_id_of_composable (x'.composable (Bicat.Hom.id m)), Category.comp_id]
  exact P.wRAt_nil f x.wf x.endR_eq x.start_eq x'.start_eq

end Hcomp

/-! ## The associator and unitors on objects of `U̇` -/

section Iso

variable [S.IsEven] (deg)

/-- **The associativity isomorphism `(A B) C ≅ A (B C)`** in `U̇(l, o)`, for the composition
functor `hcompDot` of KL III Definition 3.21. -/
def hcompDotAssoc (A : UDotHom P deg l m) (B : UDotHom P deg m n) (C : UDotHom P deg n o) :
    (hcompDot deg).obj ((hcompDot deg).obj (A, B), C) ≅
      (hcompDot deg).obj (A, (hcompDot deg).obj (B, C)) :=
  udIso _ _ (Equiv.prodAssoc _ _ _)
    (fun _ => Bicat.Hom.ext (Obj.tensor_assoc _ _ _).symm)
    (fun _ => by
      simp only [hcompDot, karProd, matBi, hcompGr, Equiv.prodAssoc_apply]
      ring)
    (fun i j => by
      obtain ⟨⟨a, b⟩, c⟩ := i
      obtain ⟨⟨a', b'⟩, c'⟩ := j
      show P.hcomp l.region (A.p a a').1 (P.hcomp m.region (B.p b b').1 (C.p c c').1 _ _) _ _ =
        _ ≫ P.hcomp l.region (P.hcomp l.region (A.p a a').1 (B.p b b').1 _ _) (C.p c c').1 _ _ ≫ _
      rw [hcomp_assoc]
      simp)

/-- The identity 1-morphism `1_l` of `l` (the empty word) with shift `0`, as an object of
`U̇(l, l)`. -/
abbrev oneDot (l : P.Bicat) : UDotHom P deg l l := objOf (Bicat.Hom.id l) 0

/-- **The left unit isomorphism `1_l A ≅ A`** in `U̇(l, m)`. -/
def hcompDotIdLeft (A : UDotHom P deg l m) : (hcompDot deg).obj (oneDot deg l, A) ≅ A :=
  udIso _ _ (Equiv.punitProd _)
    (fun _ => Bicat.Hom.ext (Obj.nil_tensor (Bicat.Hom.start_eq _)).symm)
    (fun _ => by
      show (A.X.X _).t = 0 + (A.X.X _).t
      rw [zero_add]; rfl)
    (fun i j => by
      obtain ⟨⟨⟩, a⟩ := i
      obtain ⟨⟨⟩, a'⟩ := j
      show (A.p a a').1 = _ ≫ P.hcomp l.region ((𝟙 (Mat_.embedding _ |>.obj _) :
        (Mat_.embedding (GrObj P deg l l)).obj ⟨Bicat.Hom.id l, 0⟩ ⟶ _) PUnit.unit PUnit.unit).1
          (A.p a a').1 _ _ ≫ _
      rw [Mat_.id_apply_self, GrObj.id_val]
      erw [hcomp_id_left]
      simp)

/-- **The right unit isomorphism `A 1_m ≅ A`** in `U̇(l, m)`. -/
def hcompDotIdRight (A : UDotHom P deg l m) : (hcompDot deg).obj (A, oneDot deg m) ≅ A :=
  udIso _ _ (Equiv.prodPUnit _)
    (fun _ => Bicat.Hom.ext (Obj.tensor_nil _ _).symm)
    (fun _ => by
      show (A.X.X _).t = (A.X.X _).t + 0
      rw [add_zero]; rfl)
    (fun i j => by
      obtain ⟨a, ⟨⟩⟩ := i
      obtain ⟨a', ⟨⟩⟩ := j
      show (A.p a a').1 = _ ≫ P.hcomp l.region (A.p a a').1 ((𝟙 (Mat_.embedding _ |>.obj _) :
        (Mat_.embedding (GrObj P deg m m)).obj ⟨Bicat.Hom.id m, 0⟩ ⟶ _) PUnit.unit
          PUnit.unit).1 _ _ ≫ _
      rw [Mat_.id_apply_self, GrObj.id_val]
      erw [hcomp_id_right]
      simp)

end Iso

/-! ## `K₀(U̇)` is an idempotented ring -/

namespace K0U

open SplitK0

variable [S.IsEven]

/-- **Associativity of the product of `K₀(U̇)`** (KL III §3.6): `(x y) z = x (y z)`, from the
isomorphisms `(A B) C ≅ A (B C)` of `U̇`. -/
theorem mul_assoc (x : K0U P deg l m) (y : K0U P deg m n) (z : K0U P deg n o) :
    mul (mul x y) z = mul x (mul y z) := by
  induction x using SplitK0.induction_on generalizing y z with
  | of A =>
    induction y using SplitK0.induction_on generalizing z with
    | of B =>
      induction z using SplitK0.induction_on with
      | of C =>
        rw [mul_of, mul_of, mul_of, mul_of]
        exact of_iso (hcompDotAssoc deg A B C)
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | neg z hz => simp only [map_neg, hz]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, AddMonoidHom.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, AddMonoidHom.neg_apply, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

/-- The class `[1_l] ∈ K₀(U̇(l, l))` of the identity 1-morphism. -/
abbrev one (l : P.Bicat) : K0U P deg l l := cl (oneDot deg l)

/-- **`[1_l] x = x`**. -/
theorem one_mul (x : K0U P deg l m) : mul (one l) x = x := by
  induction x using SplitK0.induction_on with
  | of A => rw [mul_of]; exact of_iso (hcompDotIdLeft deg A)
  | zero => simp
  | add x x' hx hx' => rw [map_add, hx, hx']
  | neg x hx => rw [map_neg, hx]

/-- **`x [1_m] = x`**. -/
theorem mul_one (x : K0U P deg l m) : mul x (one m) = x := by
  induction x using SplitK0.induction_on with
  | of A => rw [mul_of]; exact of_iso (hcompDotIdRight deg A)
  | zero => simp
  | add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => rw [map_neg, AddMonoidHom.neg_apply, hx]

/-- The product is `ℤ[q, q⁻¹]`-linear in the first variable. -/
theorem mul_smul_left (p : LaurentPolynomial ℤ) (x : K0U P deg l m) (y : K0U P deg m n) :
    mul (p • x) y = p • mul x y := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, AddMonoidHom.add_apply, hp, hp', add_smul]
  | C_mul_T n a =>
    rw [mul_smul, SplitK0.C_smul, mul_smul, SplitK0.C_smul, map_zsmul, AddMonoidHom.smul_apply,
      mul_shift_left]

/-- The product is `ℤ[q, q⁻¹]`-linear in the second variable. -/
theorem mul_smul_right (p : LaurentPolynomial ℤ) (x : K0U P deg l m) (y : K0U P deg m n) :
    mul x (p • y) = p • mul x y := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', add_smul]
  | C_mul_T n a =>
    rw [mul_smul, SplitK0.C_smul, mul_smul, SplitK0.C_smul, map_zsmul, mul_shift_right]

end K0U

end GradedBicat

end Categorification
