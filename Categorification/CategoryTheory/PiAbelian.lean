/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Products of abelian categories

For a family `C i` of abelian categories, the product category `∀ i, C i` is abelian, with
kernels, cokernels and the abelian structure computed componentwise; if every `C i` is
`k`-linear, so is the product.

This is the ambient category of the weak `sl₂`-categorification on finite-dimensional modules
over the tensor product algebras of Webster, arXiv:1309.3796v2, §5, which collects the module
categories of the algebras `T^λ_ν` for the weights `ν` of one `i`-string (Chuang–Rouquier,
arXiv:math/0407205v2, §5.1.1).

## Main definitions

* `CategoryTheory.Pi.preadditive`, `CategoryTheory.Pi.abelian`, `CategoryTheory.Pi.linear`.
* `CategoryTheory.Pi.preservesLimit_eval`, `CategoryTheory.Pi.preservesColimit_eval`:
  evaluation at a coordinate preserves the componentwise limits and colimits.
* `CategoryTheory.Pi.preservesHomology_eval`: evaluation at a coordinate is exact; in
  particular it preserves monomorphisms, epimorphisms and short exact sequences.
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

namespace Pi

universe w v u

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]

section Preadditive

variable [∀ i, Preadditive (C i)]

/-- The product of preadditive categories is preadditive, with componentwise addition. -/
instance preadditive : Preadditive (∀ i, C i) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ i, X i ⟶ Y i))
  add_comp _ _ _ _ _ _ := funext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := funext fun _ => Preadditive.comp_add _ _ _ _ _ _

@[simp]
lemma add_apply {X Y : ∀ i, C i} (f g : X ⟶ Y) (i : I) : (f + g) i = f i + g i := rfl

@[simp]
lemma neg_apply {X Y : ∀ i, C i} (f : X ⟶ Y) (i : I) : (-f) i = -f i := rfl

@[simp]
lemma zero_apply' {X Y : ∀ i, C i} (i : I) : (0 : X ⟶ Y) i = 0 := rfl

@[simp]
lemma smul_apply {X Y : ∀ i, C i} (n : ℤ) (f : X ⟶ Y) (i : I) : (n • f) i = n • f i := rfl

instance (i : I) : (eval C i).Additive where

end Preadditive

section Linear

variable (k : Type*) [Semiring k] [∀ i, Preadditive (C i)] [∀ i, Linear k (C i)]

/-- The product of `k`-linear categories is `k`-linear. -/
instance linear : Linear k (∀ i, C i) where
  homModule X Y := _root_.Pi.module I (fun i => X i ⟶ Y i) k
  smul_comp _ _ _ _ _ _ := funext fun _ => Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := funext fun _ => Linear.comp_smul _ _ _ _ _ _

@[simp]
lemma smul_apply' {X Y : ∀ i, C i} (c : k) (f : X ⟶ Y) (i : I) : (c • f) i = c • f i := rfl

instance (i : I) : (eval C i).Linear k where

end Linear

section Limits

variable {J : Type*} [Category* J] {F : J ⥤ ∀ i, C i}

/-- The component at `i` of a cone over `F : J ⥤ ∀ i, C i`. -/
@[simps]
def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

/-- The component at `i` of a cocone over `F : J ⥤ ∀ i, C i`. -/
@[simps]
def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

/-- A family of cones over the components assembles to a cone over `F`. -/
@[simps]
def coneOfConeCompEval (c : ∀ i, Cone (F ⋙ eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun _ _ f => funext fun i => (c i).π.naturality f }

/-- A family of cocones over the components assembles to a cocone over `F`. -/
@[simps]
def coconeOfCoconeCompEval (c : ∀ i, Cocone (F ⋙ eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun _ _ f => funext fun i => (c i).ι.naturality f }

/-- Componentwise limit cones assemble to a limit cone. -/
def coneOfConeEvalIsLimit {c : ∀ i, Cone (F ⋙ eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := funext fun i => (P i).fac (coneCompEval s i) j
  uniq s m w := funext fun i =>
    (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

/-- Componentwise colimit cocones assemble to a colimit cocone. -/
def coconeOfCoconeEvalIsColimit {c : ∀ i, Cocone (F ⋙ eval C i)} (P : ∀ i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := funext fun i => (P i).fac (coconeCompEval s i) j
  uniq s m w := funext fun i =>
    (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

lemma hasLimit_of_hasLimit_comp_eval (F : J ⥤ ∀ i, C i) [∀ i, HasLimit (F ⋙ eval C i)] :
    HasLimit F :=
  ⟨⟨⟨_, coneOfConeEvalIsLimit fun _ => limit.isLimit _⟩⟩⟩

lemma hasColimit_of_hasColimit_comp_eval (F : J ⥤ ∀ i, C i)
    [∀ i, HasColimit (F ⋙ eval C i)] : HasColimit F :=
  ⟨⟨⟨_, coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _⟩⟩⟩

/-- Evaluation at a coordinate preserves limits that exist componentwise. -/
instance preservesLimit_eval (F : J ⥤ ∀ i, C i) [∀ i, HasLimit (F ⋙ eval C i)] (i : I) :
    PreservesLimit F (eval C i) :=
  preservesLimit_of_preserves_limit_cone (coneOfConeEvalIsLimit fun _ => limit.isLimit _)
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ eval C i)) (Cone.ext (Iso.refl _)
      fun _ => (Category.id_comp _).symm))

/-- Evaluation at a coordinate preserves colimits that exist componentwise. -/
instance preservesColimit_eval (F : J ⥤ ∀ i, C i) [∀ i, HasColimit (F ⋙ eval C i)]
    (i : I) : PreservesColimit F (eval C i) :=
  preservesColimit_of_preserves_colimit_cocone
    (coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _)
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ eval C i))
      (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _))

end Limits

section Abelian

variable [∀ i, Abelian (C i)]

instance hasFiniteProducts : HasFiniteProducts (∀ i, C i) :=
  ⟨fun _ => ⟨fun _ => hasLimit_of_hasLimit_comp_eval _⟩⟩

instance hasKernels : HasKernels (∀ i, C i) :=
  ⟨fun _ => hasLimit_of_hasLimit_comp_eval _⟩

instance hasCokernels : HasCokernels (∀ i, C i) :=
  ⟨fun _ => hasColimit_of_hasColimit_comp_eval _⟩

instance (i : I) {X Y : ∀ i, C i} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) (eval C i) :=
  preservesLimit_eval _ i

instance (i : I) {X Y : ∀ i, C i} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (eval C i) :=
  preservesColimit_eval _ i

instance isIso_coimageImageComparison {X Y : ∀ i, C i} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) := by
  rw [isIso_pi_iff]
  intro i
  have h := Arrow.isIso_iff_isIso_of_isIso
    (Abelian.PreservesCoimageImageComparison.iso (eval C i) f).inv
  exact h.1 (inferInstanceAs (IsIso (Abelian.coimageImageComparison (f i))))

/-- The product of abelian categories is abelian. -/
instance abelian : Abelian (∀ i, C i) :=
  Abelian.ofCoimageImageComparisonIsIso

instance preservesMonomorphisms_eval (i : I) : (eval C i).PreservesMonomorphisms :=
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels (eval C i)

instance preservesEpimorphisms_eval (i : I) : (eval C i).PreservesEpimorphisms :=
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels (eval C i)

/-- Evaluation at a coordinate preserves homology. -/
instance preservesHomology_eval (i : I) : (eval C i).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (eval C i)

/-- A short exact sequence in the product is short exact in each coordinate. -/
theorem shortExact_eval {S : ShortComplex (∀ i, C i)} (hS : S.ShortExact) (i : I) :
    (S.map (eval C i)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (eval C i)

end Abelian

end Pi

end CategoryTheory
