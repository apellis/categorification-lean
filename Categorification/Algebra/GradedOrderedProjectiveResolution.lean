/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedProjectiveResolution
import Categorification.Algebra.GradedLoadingCovers

/-!
# Graded ordered standard resolutions

In Webster, arXiv:1309.3796v2, Lemma 6.11, all positive terms in a
standard's resolution use projectives from strictly higher loadings.
Starting at the specified homogeneous loading quotient, the construction
compares each homogeneous syzygy with the corresponding ordinary ordered
syzygy by Schanuel's lemma. The auxiliary projectives use strictly higher
loadings too. This permits choosing every next term as a sum of homogeneous
loading generators, with a separate shift for each generator weight.
-/

namespace Categorification.ModuleFiltration

universe u
open DirectSum

open CategoryTheory

noncomputable section

variable {R : Type u} [Ring R] {Label : Type u} {S : Label → ModuleCat.{u} R}
  {e : Label → R} {above : Label → Label → Prop}
  (data : OrderedStandardCovers S e above) (s : Label)
  (A : ℤ → AddSubgroup R) [DirectSum.Decomposition A]

private abbrev allowed (s : Label) := {i // above s i}
private abbrev allowedIdem (s : Label) : allowed (above := above) s → R := fun i => e i.val

private theorem fixedLoadingSpan_of_maps {M : Type u} [AddCommGroup M] [Module R M]
    (he : ∀ i, IsIdempotentElem (e i)) {J : Type*} (label : J → Label)
    (higher : ∀ j, above s (label j)) (inc : ∀ j, lIdeal (e (label j)) →ₗ[R] M)
    (hspan : ∀ x : M, x ∈ Submodule.span R {y | ∃ j z, inc j z = y}) :
    FixedLoadingSpan (allowedIdem (e := e) (above := above) s) M := by
  intro x
  let P := Submodule.span R {y : M | ∃ i : allowed (above := above) s, e i.val • y = y}
  have hs : Submodule.span R {y | ∃ j z, inc j z = y} ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, a, rfl⟩
    let v : lIdeal (e (label j)) := ⟨_, (he _).eq⟩
    have hv : e (label j) • inc j v = inc j v := by
      rw [← map_smul]
      exact congrArg (inc j) (Subtype.ext (he _).eq)
    have ha : a.val • v = a := Subtype.ext a.property
    rw [← ha, map_smul]
    exact P.smul_mem _ (Submodule.subset_span ⟨⟨label j, higher j⟩, hv⟩)
  exact hs (hspan x)

/-- The internal grading on the next kernel is retained through each resolution step. -/
structure GradedLoadingSyzygy (A : ℤ → AddSubgroup R) where
  obj : ModuleCat.{u} R
  grade : ℤ → AddSubgroup obj
  decomp : DirectSum.Decomposition grade
  smul_mem : ∀ ⦃i j : ℤ⦄ ⦃a : R⦄ ⦃x : obj⦄, a ∈ A i → x ∈ grade j → a • x ∈ grade (i+j)

private abbrev supports := FixedLoadingSpan (allowedIdem (e := e) (above := above) s)

private structure StableLoadingSyzygy (n : ℕ) where
  graded : GradedLoadingSyzygy A
  left : ModuleCat.{u} R
  right : ModuleCat.{u} R
  projectiveLeft : Module.Projective R left
  projectiveRight : Module.Projective R right
  supportLeft : supports (e := e) (above := above) s left
  supportRight : supports (e := e) (above := above) s right
  stable : (graded.obj × left) ≃ₗ[R] (data.resolutionSyzygy s (n+1) × right)

omit [DirectSum.Decomposition A] in
private theorem stableLoadingSyzygy_support
    (htrans : ∀ a b c, above a b → above b c → above a c)
    (he : ∀ i, IsIdempotentElem (e i)) (n : ℕ) (X : StableLoadingSyzygy data s A n) :
    supports (e := e) (above := above) s X.graded.obj := by
  obtain ⟨J, label, inc, higher, hspan⟩ := data.syzygy_loading_support s htrans n
  exact FixedLoadingSpan.of_stableEquiv _ X.stable
    (fixedLoadingSpan_of_maps s he label higher inc hspan) X.supportRight

variable (hmul : ∀ ⦃i j : ℤ⦄ ⦃a b : R⦄, a ∈ A i → b ∈ A j → a * b ∈ A (i+j))
variable (he₀ : ∀ i, e i ∈ A 0)
variable (he : ∀ i, IsIdempotentElem (e i))
variable (htrans : ∀ a b c, above a b → above b c → above a c)

private def nextStableLoadingSyzygy (n : ℕ) (X : StableLoadingSyzygy data s A n) :
    StableLoadingSyzygy data s A (n+1) := by
  classical
  let I := allowedIdem (e := e) (above := above) s
  let G := X.graded.grade
  letI : DirectSum.Decomposition G := X.graded.decomp
  let P := ⨁ t : HomogeneousLoadingGenerators G I, lIdeal (I t.1)
  let W := homogeneousLoadingCoverGrade G I A
  letI : DirectSum.Decomposition W :=
    homogeneousLoadingCoverGrade_decomposition G I A hmul (fun i => he₀ i.val)
  let f : P →ₗ[R] X.graded.obj := homogeneousLoadingCover G I
  have hf : Function.Surjective f := homogeneousLoadingCover_surjective_of_fixed G I
    (fun i => he i.val) (fun i {_ _} hx => by simpa using X.graded.smul_mem (he₀ i.val) hx)
    (stableLoadingSyzygy_support data s A htrans he n X)
  have hmap : ∀ ⦃j : ℤ⦄ ⦃x : P⦄, x ∈ W j → f x ∈ G j :=
    fun {_ _} h => homogeneousLoadingCover_preserves_grade G I A X.graded.smul_mem h
  let g := data.resolutionCover s (n+1)
  letI : Module.Projective R P := homogeneousLoadingCover_projective G I (fun i => data.projective i.val)
  letI : Module.Projective R (data.resolutionProjective s (n+1)) := data.resolutionProjective_projective s (n+1)
  letI : Module.Projective R X.left := X.projectiveLeft
  letI : Module.Projective R X.right := X.projectiveRight
  let N := kernelGrading W f
  let next : GradedLoadingSyzygy A := {
    obj := ModuleCat.of R (LinearMap.ker f)
    grade := N
    decomp := kernelGrading_decomposition W G f hmap
    smul_mem := fun {_ _ _ _} ha hx => homogeneousLoadingCoverGrade_smul G I A hmul ha hx }
  have hsOld : supports (e := e) (above := above) s (data.resolutionProjective s (n+1)) := by
    obtain ⟨J, label, inc, higher, hspan⟩ := data.projectiveResolution_loading_support s htrans n
    exact fixedLoadingSpan_of_maps s he label higher inc hspan
  exact {
    graded := next
    left := ModuleCat.of R ((data.resolutionProjective s (n+1)) × X.right)
    right := ModuleCat.of R (P × X.left)
    projectiveLeft := projectiveProduct
    projectiveRight := projectiveProduct
    supportLeft := hsOld.prod _ X.supportRight
    supportRight := (homogeneousLoadingCover_fixedSpan G I (fun i => he i.val)).prod _ X.supportLeft
    stable := Classical.choice
      (exists_stable_kernelEquiv X.stable f g hf (data.resolutionCover_surjective s (n+1))) }

variable (T : ℤ → AddSubgroup (S s)) [DirectSum.Decomposition T]
variable (hq : ∀ ⦃n : ℤ⦄ ⦃x : lIdeal (e s)⦄, x.val ∈ A n → data.quotient s x ∈ T n)

private def firstStableLoadingSyzygy : StableLoadingSyzygy data s A 0 := by
  let L := loadingIdealGrading A (e s)
  letI : DirectSum.Decomposition L := loadingIdealGrading_decomposition A hmul (e s) (he₀ s)
  let f := data.quotient s
  let G := kernelGrading L f
  have hfp : ∀ ⦃n : ℤ⦄ ⦃x : lIdeal (e s)⦄, x ∈ L n → f x ∈ T n := hq
  have hproj : Module.Projective R PUnit.{u+1} := by
    apply Module.Projective.of_lifting_property
    intro M N _ _ _ _ g q hg
    refine ⟨0, LinearMap.ext ?_⟩
    intro x
    rw [Subsingleton.elim x 0]
    rw [map_zero, map_zero]
  have hsp : supports (e := e) (above := above) s PUnit.{u+1} := by
    intro x
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  exact {
    graded := {
      obj := ModuleCat.of R (LinearMap.ker f)
      grade := G
      decomp := kernelGrading_decomposition L T f hfp
      smul_mem := fun {_ _ _ _} ha hx => hmul ha hx }
    left := ModuleCat.of R PUnit.{u+1}
    right := ModuleCat.of R PUnit.{u+1}
    projectiveLeft := hproj
    projectiveRight := hproj
    supportLeft := hsp
    supportRight := hsp
    stable := LinearEquiv.refl R _ }

private def stableLoadingResolution : (n : ℕ) → StableLoadingSyzygy data s A n
  | 0 => firstStableLoadingSyzygy data s A hmul he₀ T hq
  | n+1 => nextStableLoadingSyzygy data s A hmul he₀ he htrans n
      (stableLoadingResolution n)

/-- Successive graded kernels in the ordered loading resolution. The first term
is the literal kernel of the specified homogeneous loading quotient. -/
def gradedLoadingResolutionSyzygy (n : ℕ) : GradedLoadingSyzygy A :=
  (stableLoadingResolution data s A hmul he₀ he htrans T hq n).graded


private abbrev G (n : ℕ) :=
  (gradedLoadingResolutionSyzygy data s A hmul he₀ he htrans T hq n).grade

private abbrev I := allowedIdem (e := e) (above := above) s

/-- The positive terms are literal sums indexed by a strictly higher loading,
a generator weight, and a fixed vector in the current kernel. -/
def gradedLoadingResolutionPositive (n : ℕ) : GradedLoadingSyzygy A := by
  classical
  let Γ := G data s A hmul he₀ he htrans T hq n
  let ι := I (e := e) (above := above) s
  exact {
    obj := ModuleCat.of R (⨁ t : HomogeneousLoadingGenerators Γ ι, lIdeal (ι t.1))
    grade := homogeneousLoadingCoverGrade Γ ι A
    decomp := homogeneousLoadingCoverGrade_decomposition Γ ι A hmul (fun i => he₀ i.val)
    smul_mem := fun {_ _ _ _} ha hx => homogeneousLoadingCoverGrade_smul Γ ι A hmul ha hx }

/-- The map from a positive term to its current homogeneous syzygy. -/
def gradedLoadingResolutionCover (n : ℕ) :
    (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj →ₗ[R]
      (gradedLoadingResolutionSyzygy data s A hmul he₀ he htrans T hq n).obj :=
  homogeneousLoadingCover (G data s A hmul he₀ he htrans T hq n) (I (e := e) (above := above) s)

theorem gradedLoadingResolutionCover_mem (n : ℕ) {j : ℤ}
    {x : (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj}
    (hx : x ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).grade j) :
    gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq n x ∈
      (gradedLoadingResolutionSyzygy data s A hmul he₀ he htrans T hq n).grade j :=
  homogeneousLoadingCover_preserves_grade _ _ A
    (gradedLoadingResolutionSyzygy data s A hmul he₀ he htrans T hq n).smul_mem hx

theorem gradedLoadingResolutionCover_surjective (n : ℕ) :
    Function.Surjective (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq n) := by
  let X := stableLoadingResolution data s A hmul he₀ he htrans T hq n
  let : DirectSum.Decomposition X.graded.grade := X.graded.decomp
  exact homogeneousLoadingCover_surjective_of_fixed X.graded.grade (I (e := e) (above := above) s)
    (fun i => he i.val) (fun i {_ _} hx => by simpa using X.graded.smul_mem (he₀ i.val) hx)
    (stableLoadingSyzygy_support data s A htrans he n X)

/-- The positive terms remain projective after forgetting their internal grading. -/
theorem gradedLoadingResolutionPositive_projective (n : ℕ) :
    Module.Projective R (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj :=
  homogeneousLoadingCover_projective _ _ (fun i => data.projective i.val)

/-- The projective in degree zero is the source loading with its unshifted
scalar grading. -/
def gradedLoadingResolutionZero : GradedLoadingSyzygy A where
  obj := ModuleCat.of R (lIdeal (e s))
  grade := loadingIdealGrading A (e s)
  decomp := loadingIdealGrading_decomposition A hmul (e s) (he₀ s)
  smul_mem := fun {_ _ _ _} ha hx => hmul ha hx

/-- Each later kernel is inserted into the preceding loading-projective term. -/
def gradedLoadingResolutionDifferential (n : ℕ) :
    (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq (n+1)).obj →ₗ[R]
      (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj :=
  (LinearMap.ker (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq n)).subtype.comp
    (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq (n+1))

theorem gradedLoadingResolutionDifferential_mem (n : ℕ) {j : ℤ}
    {x : (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq (n+1)).obj}
    (hx : x ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq (n+1)).grade j) :
    gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq n x ∈
      (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).grade j :=
  gradedLoadingResolutionCover_mem data s A hmul he₀ he htrans T hq (n+1) hx

theorem gradedLoadingResolutionDifferential_exact_cover (n : ℕ) :
    Function.Exact (gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq n)
      (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := gradedLoadingResolutionCover_surjective data s A hmul he₀ he htrans T hq (n+1)
      ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  · rintro ⟨v,rfl⟩
    exact (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq (n+1) v).property

theorem gradedLoadingResolutionDifferential_exact (n : ℕ) :
    Function.Exact (gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq (n+1))
      (gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq n) := by
  intro x
  have hx : gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq n x = 0 ↔
      gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq (n+1) x = 0 := by
    let K := LinearMap.ker (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq n)
    let y : K := gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq (n+1) x
    change K.subtype y = 0 ↔ y = 0
    rw [← map_zero K.subtype, (Submodule.injective_subtype _).eq_iff]
  rw [hx]
  exact gradedLoadingResolutionDifferential_exact_cover data s A hmul he₀ he htrans T hq (n+1) x


/-- The first differential lands in the original loading ideal. -/
def gradedLoadingResolutionFirstDifferential :
    (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq 0).obj →ₗ[R]
      (gradedLoadingResolutionZero (e := e) s A hmul he₀).obj :=
  (LinearMap.ker (data.quotient s)).subtype.comp
    (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq 0)

theorem gradedLoadingResolutionFirstDifferential_mem {j : ℤ}
    {x : (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq 0).obj}
    (hx : x ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq 0).grade j) :
    gradedLoadingResolutionFirstDifferential data s A hmul he₀ he htrans T hq x ∈
      (gradedLoadingResolutionZero (e := e) s A hmul he₀).grade j :=
  gradedLoadingResolutionCover_mem data s A hmul he₀ he htrans T hq 0 hx

theorem gradedLoadingResolutionFirstDifferential_exact :
    Function.Exact (gradedLoadingResolutionFirstDifferential data s A hmul he₀ he htrans T hq)
      (data.quotient s) := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := gradedLoadingResolutionCover_surjective data s A hmul he₀ he htrans T hq 0
      ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  · rintro ⟨v,rfl⟩
    exact (gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq 0 v).property

theorem gradedLoadingResolutionSecondDifferential_exact :
    Function.Exact (gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq 0)
      (gradedLoadingResolutionFirstDifferential data s A hmul he₀ he htrans T hq) := by
  intro x
  have hx : gradedLoadingResolutionFirstDifferential data s A hmul he₀ he htrans T hq x = 0 ↔
      gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq 0 x = 0 := by
    let K := LinearMap.ker (data.quotient s)
    let y : K := gradedLoadingResolutionCover data s A hmul he₀ he htrans T hq 0 x
    change K.subtype y = 0 ↔ y = 0
    rw [← map_zero K.subtype, (Submodule.injective_subtype _).eq_iff]
  rw [hx]
  exact gradedLoadingResolutionDifferential_exact_cover data s A hmul he₀ he htrans T hq 0 x


/-- Each internal component is additively generated by transports of fixed
homogeneous generators from strictly higher loadings. -/
theorem gradedLoadingResolutionPositive_support (n : ℕ) (j : ℤ)
    (x : (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj)
    (hx : x ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).grade j) :
    x ∈ AddSubgroup.closure {y | ∃ (i : Label) (_ : above s i) (k : ℤ)
      (g : (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).obj),
      g ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).grade k ∧
      e i • g = g ∧ ∃ a : A (j-k), a.val • g = y} := by
  classical
  let Γ := G data s A hmul he₀ he htrans T hq n
  let ι := I (e := e) (above := above) s
  let J := HomogeneousLoadingGenerators Γ ι
  let L : J → Type u := fun t => lIdeal (ι t.1)
  change (x : ⨁ t : J, L t) ∈ _
  conv in (x : ⨁ t : J, L t) => rw [← DirectSum.sum_support_of x]
  apply AddSubgroup.sum_mem
  intro t _
  let z : L t := ⟨ι t.1, (he t.1.val).eq⟩
  let g := DirectSum.lof R J L t z
  have hg : g ∈ (gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n).grade t.2.1 := by
    change ∀ t', (g t').val ∈ A (t.2.1-t'.2.1)
    intro t'
    simp only [g, DirectSum.lof_eq_of]
    by_cases ht : t = t'
    · subst t'
      rw [DirectSum.of_eq_same, sub_self]
      exact he₀ t.1.val
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)]
      exact zero_mem _
  have hfix : e t.1.val • g = g := by
    dsimp [g]
    rw [← map_smul]
    exact congrArg (DirectSum.lof R J L t) (Subtype.ext (he t.1.val).eq)
  let y : ⨁ i : J, L i := x
  let v : L t := y t
  have hv : v.val ∈ A (j-t.2.1) := hx t
  exact AddSubgroup.subset_closure ⟨t.1.val, t.1.property, t.2.1, g, hg, hfix,
    ⟨v.val, hv⟩, by
      change v.val • DirectSum.lof R J L t z = DirectSum.of L t v
      rw [← map_smul, DirectSum.lof_eq_of]
      exact congrArg (DirectSum.of L t) (Subtype.ext v.property)⟩


/-- All terms in chain indexing, with degree zero anchored at the chosen loading. -/
def gradedLoadingResolutionTerm : ℕ → GradedLoadingSyzygy A
  | 0 => gradedLoadingResolutionZero (e := e) s A hmul he₀
  | n+1 => gradedLoadingResolutionPositive data s A hmul he₀ he htrans T hq n

/-- The adjacent maps in chain indexing. -/
def gradedLoadingResolutionChainMap (n : ℕ) :
    (gradedLoadingResolutionTerm data s A hmul he₀ he htrans T hq (n+1)).obj →ₗ[R]
      (gradedLoadingResolutionTerm data s A hmul he₀ he htrans T hq n).obj :=
  match n with
  | 0 => gradedLoadingResolutionFirstDifferential data s A hmul he₀ he htrans T hq
  | m+1 => gradedLoadingResolutionDifferential data s A hmul he₀ he htrans T hq m

theorem gradedLoadingResolutionChainMap_mem (n : ℕ) {j : ℤ}
    {x : (gradedLoadingResolutionTerm data s A hmul he₀ he htrans T hq (n+1)).obj}
    (hx : x ∈ (gradedLoadingResolutionTerm data s A hmul he₀ he htrans T hq (n+1)).grade j) :
    gradedLoadingResolutionChainMap data s A hmul he₀ he htrans T hq n x ∈
      (gradedLoadingResolutionTerm data s A hmul he₀ he htrans T hq n).grade j := by
  cases n with
  | zero => exact gradedLoadingResolutionFirstDifferential_mem data s A hmul he₀ he htrans T hq hx
  | succ n => exact gradedLoadingResolutionDifferential_mem data s A hmul he₀ he htrans T hq n hx

theorem gradedLoadingResolutionChainMap_exact (n : ℕ) :
    Function.Exact (gradedLoadingResolutionChainMap data s A hmul he₀ he htrans T hq (n+1))
      (gradedLoadingResolutionChainMap data s A hmul he₀ he htrans T hq n) := by
  cases n with
  | zero => exact gradedLoadingResolutionSecondDifferential_exact data s A hmul he₀ he htrans T hq
  | succ n => exact gradedLoadingResolutionDifferential_exact data s A hmul he₀ he htrans T hq n

theorem gradedLoadingResolutionChainMap_augmentation_exact :
    Function.Exact (gradedLoadingResolutionChainMap data s A hmul he₀ he htrans T hq 0)
      (data.quotient s) :=
  gradedLoadingResolutionFirstDifferential_exact data s A hmul he₀ he htrans T hq


end

end Categorification.ModuleFiltration
