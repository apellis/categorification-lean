/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Weight dg models of homogeneous projective resolutions

A degree-preserving augmented chain of graded modules gives a diagram of
complexes on the weight category. Exactness of the underlying augmented
chain gives a dg quasi-isomorphism, as needed in Webster,
arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification
open CategoryTheory DG
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]

local notation "W" => WeightCategory R
local notation "A" => wgrading (M := R)

structure WeightGradedTerm (R : Type) [Ring R] [InternalGrading R] [BigradedDGRing R] where
  obj : ModuleCat R
  grade : ℤ → AddSubgroup obj
  decomp : DirectSum.Decomposition grade
  smul_mem : ∀ {i j : ℤ} {a : R} {x : obj}, a ∈ wgrading i → x ∈ grade j → a • x ∈ grade (i+j)

variable (P : ℕ → WeightGradedTerm R)
  (δ : ∀ n, (P (n+1)).obj →ₗ[R] (P n).obj)
  (hδ : ∀ n j {x : (P (n+1)).obj}, x ∈ (P (n+1)).grade j → δ n x ∈ (P n).grade j)
  (hcomp : ∀ n (x : (P (n+2)).obj), δ n (δ (n+1) x) = 0)

private def weightChainTerm (Z : W) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ ((P n).grade Z.as)

private def weightRestrictedMap {M N : WeightGradedTerm R} (Z : W)
    (f : M.obj →ₗ[R] N.obj)
    (hf : ∀ j {x : M.obj}, x ∈ M.grade j → f x ∈ N.grade j) :
    ModuleCat.of ℤ (M.grade Z.as) ⟶ ModuleCat.of ℤ (N.grade Z.as) :=
  ModuleCat.ofHom (f.toAddMonoidHom.domRestrict (M.grade Z.as)
    |>.codRestrict (N.grade Z.as) (fun x => hf Z.as x.property)
    |>.toIntLinearMap)

private def weightChainDifferential (Z : W) (n : ℕ) :
    weightChainTerm P Z (n+1) ⟶ weightChainTerm P Z n :=
  weightRestrictedMap Z (δ n) (hδ n)

private def weightChain (Z : W) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (weightChainTerm P Z) (weightChainDifferential P δ hδ Z)
    (fun n => ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (hcomp n x.val)))

private def weightChainActionTerm {X Y : W} (a : X ⟶ Y) (n : ℕ) :
    weightChainTerm P X n ⟶ weightChainTerm P Y n :=
  ModuleCat.ofHom (({
    toFun := fun x => ⟨a.val • x.val, by
      have h := (P n).smul_mem a.property x.property
      rwa [show Y.as - X.as + X.as = Y.as by omega] at h⟩
    map_zero' := Subtype.ext (smul_zero _)
    map_add' := fun x y => Subtype.ext (smul_add _ _ _) } :
    ((P n).grade X.as) →+ ((P n).grade Y.as)).toIntLinearMap)

private def weightChainAction {X Y : W} (a : X ⟶ Y) :
    weightChain P δ hδ hcomp X ⟶ weightChain P δ hδ hcomp Y where
  f n := weightChainActionTerm P a n
  comm' n m hn := by
    change m + 1 = n at hn
    subst n
    simp only [weightChain, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext ((δ m).map_smul a.val x.val)

def weightDiagramOfGradedChain : W ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj := weightChain P δ hδ hcomp
  map := weightChainAction P δ hδ hcomp
  map_id X := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (one_smul R x.val)
  map_comp a b := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (mul_smul b.val a.val x.val)

instance : (weightDiagramOfGradedChain P δ hδ hcomp).Additive where
  map_add {_X _Y} a b := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (add_smul a.val b.val x.val)

private theorem weightPreimage {M N : WeightGradedTerm R}
    (f : M.obj →ₗ[R] N.obj)
    (hf : ∀ j {x : M.obj}, x ∈ M.grade j → f x ∈ N.grade j)
    {j : ℤ} {y : N.obj} (hy : y ∈ N.grade j) (h : ∃ x, f x = y) :
    ∃ x ∈ M.grade j, f x = y := by
  let _ := M.decomp
  let _ := N.decomp
  let _ : DGAddCommGroup M.obj := {
    grading := M.grade
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  let _ : DGAddCommGroup N.obj := {
    grading := N.grade
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  obtain ⟨x, hx⟩ := h
  refine ⟨(DirectSum.decompose M.grade x j).val, (DirectSum.decompose M.grade x j).property, ?_⟩
  have hmap : ((DirectSum.decompose N.grade (f x) j).val : N.obj) =
      f (DirectSum.decompose M.grade x j).val :=
    coe_decompose_map_of_map_mem f.toAddMonoidHom (fun h => hf _ h) x j
  rw [← hmap, hx, DirectSum.decompose_of_mem_same _ hy]

private theorem weightRestrictedMap_exact {L M N : WeightGradedTerm R} (Z : W)
    (f : L.obj →ₗ[R] M.obj) (g : M.obj →ₗ[R] N.obj)
    (hf : ∀ j {x : L.obj}, x ∈ L.grade j → f x ∈ M.grade j)
    (hg : ∀ j {x : M.obj}, x ∈ M.grade j → g x ∈ N.grade j)
    (he : Function.Exact f g) :
    Function.Exact (weightRestrictedMap Z f hf) (weightRestrictedMap Z g hg) := by
  intro y
  constructor
  · intro hy
    have hgy : g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx, hfx⟩ := weightPreimage f hf y.property ((he y.val).mp hgy)
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (he.apply_apply_eq_zero x.val)

private theorem weightChain_exactAt (Z : W) (n : ℕ)
    (he : Function.Exact (δ (n+1)) (δ n)) :
    (weightChain P δ hδ hcomp Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', weightChain,
    ChainComplex.of_d]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact weightRestrictedMap_exact Z (δ (n+1)) (δ n) (hδ (n+1)) (hδ n) he

variable (T : WeightGradedTerm R) (q : (P 0).obj →ₗ[R] T.obj)
  (hq : ∀ j {x : (P 0).obj}, x ∈ (P 0).grade j → q x ∈ T.grade j)
  (hzero : ∀ x : (P 1).obj, q (δ 0 x) = 0)

private def weightTermFunctor : W ⥤ ModuleCat ℤ where
  obj Z := ModuleCat.of ℤ (T.grade Z.as)
  map a := weightChainActionTerm (fun _ => T) a 0
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (one_smul R x.val))
  map_comp a b := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (mul_smul b.val a.val x.val))

private instance : (weightTermFunctor T).Additive where
  map_add {_X _Y} a b :=
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (add_smul a.val b.val x.val))

private def weightChainAugmentation (Z : W) :
    weightChain P δ hδ hcomp Z ⟶ (ChainComplex.single₀ _).obj ((weightTermFunctor T).obj Z) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨weightRestrictedMap Z q hq, by
    simp only [weightChain]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (hzero x.val))⟩

/-- The weightwise chain augmentation to a graded module concentrated in degree zero. -/
def weightGradedChainAugmentation :
    weightDiagramOfGradedChain P δ hδ hcomp ⟶ weightTermFunctor T ⋙ ChainComplex.single₀ _ where
  app Z := weightChainAugmentation P δ hδ hcomp T q hq hzero Z
  naturality {X Y} a := by
    apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    change (weightChainAction P δ hδ hcomp a ≫ weightChainAugmentation P δ hδ hcomp T q hq hzero Y).f 0 =
      (weightChainAugmentation P δ hδ hcomp T q hq hzero X ≫
        ((ChainComplex.single₀ _).map ((weightTermFunctor T).map a))).f 0
    simp only [HomologicalComplex.comp_f, weightChainAugmentation]
    change _ = weightRestrictedMap X q hq ≫ ((ChainComplex.single₀ _).map ((weightTermFunctor T).map a)).f 0
    rw [ChainComplex.single₀_map_f_zero]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (q.map_smul a.val x.val))

private theorem weightRestrictedMap_surjective (Z : W) (hs : Function.Surjective q) :
    Function.Surjective (weightRestrictedMap Z q hq) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := weightPreimage q hq x.property (hs x.val)
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

theorem weightGradedChainAugmentation_quasiIso (Z : W)
    (he : ∀ n, Function.Exact (δ (n+1)) (δ n))
    (he₀ : Function.Exact (δ 0) q) (hs : Function.Surjective q) :
    QuasiIso ((weightGradedChainAugmentation P δ hδ hcomp T q hq hzero).app Z) := by
  change QuasiIso (weightChainAugmentation P δ hδ hcomp T q hq hzero Z)
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · let U := ShortComplex.mk
        (weightRestrictedMap Z (δ 0) (hδ 0)) (weightRestrictedMap Z q hq)
        (ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (hzero x.val)))
      refine (ShortComplex.exact_and_epi_g_iff_of_iso (S₂ := U) ?_).2 ⟨?_, ?_⟩
      · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · change weightRestrictedMap Z (δ 0) (hδ 0) = (weightChain P δ hδ hcomp Z).d 1 0
          rfl
        · change weightRestrictedMap Z q hq = (weightChainAugmentation P δ hδ hcomp T q hq hzero Z).f 0
          unfold weightChainAugmentation
          erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
      · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mpr
          (weightRestrictedMap_exact Z (δ 0) q (hδ 0) hq he₀)
      · exact (ModuleCat.epi_iff_surjective _).mpr
          (weightRestrictedMap_surjective P T q hq Z hs)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact weightChain_exactAt P δ hδ hcomp Z n (he n)
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The dg model of a weight-preserving chain, with chain degree n placed at -n. -/
def weightDgModuleOfGradedChain : CatModule W :=
  diagramWeightModuleOfComplex (weightDiagramOfGradedChain P δ hδ hcomp ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℤ))

/-- The target grading, as a dg module concentrated in cohomological degree zero. -/
def weightDgModuleOfGradedTerm : CatModule W :=
  diagramWeightModuleOfComplex (weightTermFunctor T ⋙ ChainComplex.single₀ (ModuleCat ℤ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℤ))

/-- The homogeneous augmentation in dg form. -/
def weightDgGradedChainAugmentation :
    weightDgModuleOfGradedChain P δ hδ hcomp ⟶ weightDgModuleOfGradedTerm T :=
  diagramWeightModuleOfComplexMap (Functor.whiskerRight
    (weightGradedChainAugmentation P δ hδ hcomp T q hq hzero)
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℤ)))

/-- Homogeneous exactness of the chain, together with surjectivity of its
augmentation, makes its dg augmentation a quasi-isomorphism. -/
theorem weightDgGradedChainAugmentation_quasiIso
    (he : ∀ n, Function.Exact (δ (n+1)) (δ n))
    (he₀ : Function.Exact (δ 0) q) (hs : Function.Surjective q) :
    CatModule.IsQuasiIso (weightDgGradedChainAugmentation P δ hδ hcomp T q hq hzero) := by
  apply diagramWeightModuleOfComplexMap_isQuasiIso
  intro Z
  let _ := weightGradedChainAugmentation_quasiIso P δ hδ hcomp T q hq hzero Z he he₀ hs
  change QuasiIso (HomologicalComplex.extendMap
    ((weightGradedChainAugmentation P δ hδ hcomp T q hq hzero).app Z)
    ComplexShape.embeddingDownNat)
  infer_instance

section Coordinates

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]
  (P : ℕ → WeightGradedTerm R)
  (δ : ∀ n, (P (n+1)).obj →ₗ[R] (P n).obj)
  (hδ : ∀ n j {x : (P (n+1)).obj}, x ∈ (P (n+1)).grade j → δ n x ∈ (P n).grade j)
  (hc : ∀ n (x : (P (n+2)).obj), δ n (δ (n+1) x) = 0)

def weightCochainOfGradedChain : WeightComplexDiagram R ℤ :=
  weightDiagramOfGradedChain P δ hδ hc ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℤ)

instance : (weightCochainOfGradedChain P δ hδ hc).Additive := by
  unfold weightCochainOfGradedChain
  infer_instance

theorem weightCochainOfGradedChain_positive_isZero (X : WeightCategory R) (n : ℤ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero (((weightCochainOfGradedChain P δ hδ hc).obj X).X n) := by
  change CategoryTheory.Limits.IsZero
    ((((weightDiagramOfGradedChain P δ hδ hc).obj X).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  change -(i : ℤ) = n at hi
  omega

/-- The component in cohomological degree minus n is the nth chain term
restricted to the indicated internal weight. -/
def weightCochainOfGradedChain_coordinate (X : WeightCategory R) (n : ℕ) :
    ((weightCochainOfGradedChain P δ hδ hc).obj X).X (-(n : ℤ)) ≅
      ModuleCat.of ℤ ((P n).grade X.as) :=
  ((weightDiagramOfGradedChain P δ hδ hc).obj X).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl

/-- The coordinate identification respects the action of homogeneous arrows. -/
theorem weightCochainOfGradedChain_coordinate_act {X Y : WeightCategory R} (a : X ⟶ Y) (n : ℕ)
    (x : ((weightCochainOfGradedChain P δ hδ hc).obj X).X (-(n : ℤ))) :
    (weightCochainOfGradedChain_coordinate P δ hδ hc Y n).hom
      (((weightCochainOfGradedChain P δ hδ hc).map a).f (-(n : ℤ)) x) =
      (⟨a.val • ((weightCochainOfGradedChain_coordinate P δ hδ hc X n).hom x).val, by
        have h := (P n).smul_mem a.property
          ((weightCochainOfGradedChain_coordinate P δ hδ hc X n).hom x).property
        rwa [show Y.as - X.as + X.as = Y.as by omega] at h⟩ : (P n).grade Y.as) := by
  let j := ComplexShape.embeddingDownNat.extendFunctorCompEvalIso
    (ModuleCat ℤ) (i := n) (i' := -(n : ℤ)) rfl
  have h := j.hom.naturality ((weightDiagramOfGradedChain P δ hδ hc).map a)
  exact congrArg (fun f => f x) h

end Coordinates

end Categorification
