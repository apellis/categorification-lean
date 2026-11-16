/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleLeading
import Categorification.WeightedKLR.Mackey.ShuffleDegree
import Categorification.WeightedKLR.GalleryBasis.Graded
import Categorification.Algebra.Graded.Tensor

/-!
# The graded form of the corner isomorphism of the Mackey filtration

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19 (after
Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18): the subquotient of the Mackey filtration
of shuffle type `μ` is the balanced tensor product over the middle parabolic, **shifted** by the
degree of the diagram exchanging the two middle blocks. This file makes the isomorphism
`Juxtapose.middleCornerEquiv` graded, for every grading datum `G` (`WeightedKLR.GradingDatum`).

The gradings are the evident ones.

* Webster's algebra `W_ν` is graded by `x ∈ W_ν(n) ↔ x ∈ A_ν(n)` (`GradingDatum.klrGrade`).
* The bimodules `(W_{a+c} ⊗ W_{b+d}) e'` and `e (W_{a+b} ⊗ W_{c+d})` carry the tensor product
  grading restricted to them, and `MiddleTensor` the induced grading of the balanced tensor
  product (`Juxtapose.middleGrading`); the juxtaposed corner carries the restriction
  (`Juxtapose.middleCornerGrading`).
* The steps of the Mackey filtration are spanned by homogeneous basis vectors, so they are
  homogeneous (`GalleryAlgebra.decompose_mem_mackeyFilt`), and the subquotient `S / S'` carries
  the image grading (`GalleryAlgebra.mackeySubquotientGrading`), with degree projections
  (`GalleryAlgebra.mackeySubquotientProj`).

The descended map `middleTensorMap` raises degrees by
`middleShift G a b c d = ∑_{i, j} b_i c_j pairDeg i j` (`Juxtapose.middleTensorMap_mem_grading`,
from `GalleryAlgebra.typeInductionAux_mem_grade` and `GradingDatum.shuffleDeg_middleLeft`). Since
the juxtaposed corner is spanned by homogeneous vectors and the subquotient has degree
projections, the inverse preserves degrees as well (`Graded.symm_mem_of_proj`).

## Conventions

With the grading datum `GradingDatum.ofStanding` of Webster's standing hypothesis our degrees are
twice those of Webster's v4 grading, and `middleShift` is `-(b · c)` for the symmetric form
`i · j = ⟨i, j⟩ + ⟨j, i⟩`, twice Webster's `-⟨μ, μ'⟩` read with the symmetric pairing of roots
(see `Categorification/WeightedKLR/Mackey/ShuffleDegree.lean`). The shift is **up** in the sense
of `Graded.shift`: `(M{a})_n = M_{n - a}`.

## Main results

* `Graded.GradedEquiv.ofProjections`: a linear isomorphism raising degrees by `a`, out of a module
  spanned by homogeneous elements into a module with degree projections, is a graded isomorphism
  from the shift by `a`.
* `Juxtapose.middleTensorMap_mem_grading`: the descended map raises degrees by `middleShift`.
* `Juxtapose.middleCornerGradedEquiv`, `Juxtapose.middleCornerGradedEquivIic`: **Webster,
  Theorem 2.19, graded**: the juxtaposed corner shifted by `middleShift` is isomorphic, as a
  graded module, to the subquotient of shuffle type `c` of the Mackey filtration.
-/

namespace Categorification.Graded

variable {k M N : Type*} [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N]

/-- **The inverse of a degree-raising isomorphism raises degrees back.** Let `e : M ≃ N` send
`M_n` into `N_{n+a}`, let `M` be the sum of its graded pieces and let `N` have linear maps
`p n` which are the identity on `N_n` and vanish on `N_{n'}`, `n' ≠ n`. Then `e⁻¹` sends `N_n`
into `M_{n-a}`. -/
theorem symm_mem_of_proj (e : M ≃ₗ[k] N) {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {a : ℤ} (he : ∀ ⦃n : ℤ⦄ ⦃x : M⦄, x ∈ ℳ n → e x ∈ 𝒩 (n + a)) (hℳ : ⨆ n, ℳ n = ⊤)
    (p : ℤ → N →ₗ[k] N) (hp : ∀ ⦃n : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n → p n y = y)
    (hp' : ∀ ⦃n n' : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n' → n' ≠ n → p n y = 0) {n : ℤ} {y : N}
    (hy : y ∈ 𝒩 n) : e.symm y ∈ ℳ (n - a) := by
  have key : ∀ x : M, ∃ x' ∈ ℳ (n - a), e x' = p n (e x) := by
    intro x
    have hx : x ∈ ⨆ m, ℳ m := hℳ ▸ Submodule.mem_top
    refine Submodule.iSup_induction ℳ
      (motive := fun x => ∃ x' ∈ ℳ (n - a), e x' = p n (e x)) hx ?_ ?_ ?_
    · intro m x hxm
      by_cases h : m + a = n
      · have hm : m = n - a := by omega
        exact ⟨x, hm ▸ hxm, (hp (h ▸ he hxm)).symm⟩
      · exact ⟨0, zero_mem _, by rw [map_zero, hp' (he hxm) h]⟩
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro x y ⟨x', hx', h1⟩ ⟨y', hy', h2⟩
      exact ⟨x' + y', add_mem hx' hy', by rw [map_add, map_add, map_add, h1, h2]⟩
  obtain ⟨x', hx', h⟩ := key (e.symm y)
  rw [LinearEquiv.apply_symm_apply, hp hy] at h
  rw [← h, LinearEquiv.symm_apply_apply]
  exact hx'

/-- **A degree-raising isomorphism is a graded isomorphism from the shift.** A linear
isomorphism `e : M ≃ N` sending `M_n` into `N_{n+a}`, with `M` the sum of its graded pieces and
`N` with degree projections, is a graded isomorphism `M{a} ≃ N`. -/
def GradedEquiv.ofProjections (e : M ≃ₗ[k] N) {ℳ : ℤ → Submodule k M}
    {𝒩 : ℤ → Submodule k N} (a : ℤ) (he : ∀ ⦃n : ℤ⦄ ⦃x : M⦄, x ∈ ℳ n → e x ∈ 𝒩 (n + a))
    (hℳ : ⨆ n, ℳ n = ⊤) (p : ℤ → N →ₗ[k] N) (hp : ∀ ⦃n : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n → p n y = y)
    (hp' : ∀ ⦃n n' : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n' → n' ≠ n → p n y = 0) :
    Categorification.Graded.shift ℳ a ≃ᵍ[k] 𝒩 where
  toLinearEquiv := e
  map_mem' d x hx := by
    have := he (n := d - a) (x := x) hx
    rwa [sub_add_cancel] at this
  symm_map_mem' _ _ hy := symm_mem_of_proj e he hℳ p hp hp' hy

@[simp] theorem GradedEquiv.ofProjections_apply (e : M ≃ₗ[k] N) {ℳ : ℤ → Submodule k M}
    {𝒩 : ℤ → Submodule k N} (a : ℤ) (he : ∀ ⦃n : ℤ⦄ ⦃x : M⦄, x ∈ ℳ n → e x ∈ 𝒩 (n + a))
    (hℳ : ⨆ n, ℳ n = ⊤) (p : ℤ → N →ₗ[k] N) (hp : ∀ ⦃n : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n → p n y = y)
    (hp' : ∀ ⦃n n' : ℤ⦄ ⦃y : N⦄, y ∈ 𝒩 n' → n' ≠ n → p n y = 0) (x : M) :
    GradedEquiv.ofProjections e a he hℳ p hp hp' x = e x := rfl

end Categorification.Graded

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose _root_.Categorification.Graded

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

attribute [local instance] ColPerm.fintype

namespace GradingDatum

variable (G : GradingDatum Γ)

/-- The grading of Webster's algebra `W_ν`, restricted from the gallery algebra. -/
noncomputable def klrGrade (ν : I →₀ ℕ) (n : ℤ) : Submodule k (WeightedKLRAlgebra k Γ ν) :=
  (G.grade ν n).comap (IsIdempotentElem.cornerVal (R := k) isIdempotentElem_rankIdem)

theorem mem_klrGrade {ν : I →₀ ℕ} {n : ℤ} {x : WeightedKLRAlgebra k Γ ν} :
    x ∈ G.klrGrade ν n ↔ x.1 ∈ G.grade ν n := Iff.rfl

end GradingDatum

namespace GalleryAlgebra

variable {ν : I →₀ ℕ}
  {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b)) (G : GradingDatum Γ)

/-- The vectors of the corner basis of Webster, Theorem 2.8, are homogeneous. -/
theorem cornerBasis_homogeneous (D C : FullChamber Γ ν) (x : ColPerm ν × (Strand ν →₀ ℕ)) :
    ∃ n, (cornerBasis hP hD hZ hΓ hW hL D C x : GalleryAlgebra k Γ ν) ∈ G.grade ν n := by
  obtain ⟨g, m⟩ := x
  refine ⟨G.segDeg P C (g⁻¹ • D) + Finsupp.weight G.wt m, ?_⟩
  rw [cornerBasis_apply]
  exact G.r_mul_galList_mul_poly_mem_grade g (g⁻¹ • D) C _ m

/-- **The steps of the Mackey filtration are homogeneous**: they are spanned by homogeneous
basis vectors. -/
theorem decompose_mem_mackeyFilt (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S : Set (I → ℕ))
    {x : GalleryAlgebra k Γ ν} (hx : x ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) (n : ℤ) :
    (DirectSum.decompose (G.grade ν) x n : GalleryAlgebra k Γ ν) ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S :=
  decompose_mem_span_of_homogeneous (G.grade ν)
    (by rintro _ ⟨i, rfl⟩; exact cornerBasis_homogeneous hP hD hZ hΓ hW hL G D C i.1) hx n

/-- The grading of the subquotient `S / S'` of the Mackey filtration: the image of the
homogeneous elements of the step `S`. -/
noncomputable def mackeySubquotientGrading (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    (S' S : Set (I → ℕ)) (n : ℤ) :
    Submodule k (MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S) :=
  ((G.grade ν n).comap (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S).subtype).map
    (Submodule.mkQ _)

/-- The degree `n` projection on the step `S` of the Mackey filtration. -/
noncomputable def mackeyFiltProj (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S : Set (I → ℕ))
    (n : ℤ) :
    mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S →ₗ[k] mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S :=
  ((GradedAlgebra.proj (G.grade ν) n).comp (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S).subtype)
    |>.codRestrict _ fun x => decompose_mem_mackeyFilt hP hD hZ hΓ hW hL G ν' ν₁ D C S x.2 n

/-- The degree `n` projection on the subquotient `S / S'` of the Mackey filtration. -/
noncomputable def mackeySubquotientProj (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    (S' S : Set (I → ℕ)) (n : ℤ) :
    MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S :=
  Submodule.mapQ _ _ (mackeyFiltProj hP hD hZ hΓ hW hL G ν' ν₁ D C S n) fun _ hx =>
    decompose_mem_mackeyFilt hP hD hZ hΓ hW hL G ν' ν₁ D C S' hx n

theorem mackeySubquotientProj_of_mem (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    (S' S : Set (I → ℕ)) ⦃n : ℤ⦄ ⦃y : MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S⦄
    (hy : y ∈ mackeySubquotientGrading hP hD hZ hΓ hW hL G ν' ν₁ D C S' S n) :
    mackeySubquotientProj hP hD hZ hΓ hW hL G ν' ν₁ D C S' S n y = y := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  refine congrArg (Submodule.mkQ _) (Subtype.ext ?_)
  exact DirectSum.decompose_of_mem_same (G.grade ν) hx

theorem mackeySubquotientProj_of_mem_ne (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    (S' S : Set (I → ℕ)) ⦃n n' : ℤ⦄ ⦃y : MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S⦄
    (hy : y ∈ mackeySubquotientGrading hP hD hZ hΓ hW hL G ν' ν₁ D C S' S n') (h : n' ≠ n) :
    mackeySubquotientProj hP hD hZ hΓ hW hL G ν' ν₁ D C S' S n y = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  refine (congrArg (Submodule.mkQ _) (Subtype.ext ?_)).trans (map_zero _)
  exact DirectSum.decompose_of_mem_ne (G.grade ν) hx h

end GalleryAlgebra

namespace Juxtapose

variable (G : GradingDatum Γ) {a b c d : I →₀ ℕ}

/-- The degree shift of the subquotient of shuffle type `c` for the layout `a b c d`:
`∑_{i, j} b_i c_j pairDeg i j`, the degree of the diagram moving the block `c` past the
block `b`. -/
noncomputable def middleShift (a b c d : I →₀ ℕ) : ℤ :=
  ∑ i : (a + b + (c + d)).support, ∑ j : (a + b + (c + d)).support,
    (b i * c j : ℤ) * G.pairDeg i j

/-- The grading of `(W_{a+c} ⊗ W_{b+d}) e'`, restricted from the tensor product grading. -/
noncomputable def middleTopGrading (a b c d : I →₀ ℕ) (n : ℤ) :
    Submodule k (MiddleTop k Γ a b c d) :=
  (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) n).comap
    ((middleTopSub k Γ a b c d).subtype.restrictScalars k)

/-- The grading of `e (W_{a+b} ⊗ W_{c+d})`, restricted from the tensor product grading. -/
noncomputable def middleBotGrading (a b c d : I →₀ ℕ) (n : ℤ) :
    Submodule k (MiddleBot k Γ a b c d) :=
  (tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) n).comap
    (middleBotSub k Γ a b c d).subtype

/-- The grading of the balanced tensor product `MiddleTensor` of the middle parabolic, induced
by the gradings of the two bimodules. -/
noncomputable def middleGrading (a b c d : I →₀ ℕ) :
    ℤ → Submodule k (MiddleTensor k Γ a b c d) :=
  balancedGrading (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (MiddleAlg k Γ a b c d) (middleTopGrading G a b c d) (middleBotGrading G a b c d)

/-- **The degree shift of the shuffle type `c`, on tensors**: for `t` of degree `i` and `y` of
degree `j`, `e L ι(t) ψ_c ι(y) e R` has degree `i + middleShift + j`. -/
theorem typeInductionAux_middle_mem_grade (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (L R : FullChamber Γ (a + b + (c + d))) {i j : ℤ}
    {t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)}
    (ht : t ∈ tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) i)
    {y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)}
    (hy : y ∈ tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) j) :
    typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) L R
        (middleLeft a b c d) (t ⊗ₜ y) ∈
      G.grade (a + b + (c + d)) (i + middleShift G a b c d + j) := by
  set F := typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d))
    (layout_eq a b c d) L R (middleLeft a b c d)
  refine tensorGrading_map_mem _ _ (fun j' => G.grade _ (i + middleShift G a b c d + j'))
    (F ∘ₗ TensorProduct.mk k _ _ t) (fun j₁ j₂ y₁ y₂ hy₁ hy₂ => ?_) hy
  refine tensorGrading_map_mem _ _
    (fun i' => G.grade _ (i' + middleShift G a b c d + (j₁ + j₂)))
    (F ∘ₗ (TensorProduct.mk k _ _).flip (y₁ ⊗ₜ y₂)) (fun i₁ i₂ x₁ x₂ hx₁ hx₂ => ?_) ht
  have := typeInductionAux_mem_grade G hD hZ (rfl : a + b + (c + d) = a + b + (c + d))
    (layout_eq a b c d) L R (middleLeft a b c d) hx₁ hx₂ hy₁ hy₂
  rw [GradingDatum.shuffleDeg_middleLeft a b c d G] at this
  exact this

section Descent

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  {L R : FullChamber Γ (a + b + (c + d))} (hR : R.IsRankOrdered) (hL' : L.IsRankOrdered)
  {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S)

/-- **The descended map raises degrees by `middleShift`** (Webster, arXiv:1209.2463v4,
Theorem 2.19): `x ⊗ y ↦ [e L ι(x) ψ_c ι(y) e R]` sends the degree `n` part of `MiddleTensor`
into the degree `n + middleShift` part of the subquotient `S / S'`. -/
theorem middleTensorMap_mem_grading (hS' : Set.Iio ⇑c ⊆ S') {n : ℤ}
    {x : MiddleTensor k Γ a b c d} (hx : x ∈ middleGrading G a b c d n) :
    middleTensorMap hP hD hZ hΓ hW hL hR hL' hS hcS hS' x ∈
      mackeySubquotientGrading hP hD hZ hΓ hW hL G (a + b) (a + c) L R S' S
        (n + middleShift G a b c d) := by
  refine balancedGrading_map_mem
    (fun n' => mackeySubquotientGrading hP hD hZ hΓ hW hL G (a + b) (a + c) L R S' S
      (n' + middleShift G a b c d)) _ (fun i j t y ht hy => ?_) hx
  rw [middleTensorMap_tmul, typeInductionMap_apply]
  refine Submodule.mem_map_of_mem (f := Submodule.mkQ _) ?_
  have := typeInductionAux_middle_mem_grade G hD hZ L R ht hy
  rwa [show i + middleShift G a b c d + j = i + j + middleShift G a b c d by ring] at this

end Descent

section Corner

variable {L' : FullChamber Γ (a + c)} {L'' : FullChamber Γ (b + d)}
  {R' : FullChamber Γ (a + b)} {R'' : FullChamber Γ (c + d)}

/-- The coset generators `c_u` are homogeneous. -/
theorem rowGen_homogeneous {ν' ν'' : I →₀ ℕ} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (p : RowGen Γ ν' ν'') : ∃ n, rowGen k hD hZ p ∈ G.klrGrade (ν' + ν'') n :=
  ⟨_, CoactionGrading.mul_mem_grade _ (G.r_mem_grade _ _) (G.galList_mem_grade _ _)⟩

variable (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered) (hR' : R'.IsRankOrdered)
  (hR'' : R''.IsRankOrdered)

/-- The grading of the juxtaposed corner `(e L' ⊗ e L'') MiddleTensor (e R' ⊗ e R'')`,
restricted from `MiddleTensor`. -/
noncomputable def middleCornerGrading :
    ℤ → Submodule k (LinearMap.range (middleCornerMap (rankE k hL' ⊗ₜ rankE k hL'')
      (rankE k hR' ⊗ₜ rankE k hR''))) :=
  Graded.comap (middleGrading G a b c d) (LinearMap.range _).subtype

variable {P₃ : FullChamber Γ (a + b) → FullChamber Γ (a + b) →
    (Strand (a + b) → 𝕜) × (Strand (a + b) → 𝕜)}
  (hP₃ : ∀ C E, IsChamberSegment C E (P₃ C E))
  {P₄ : FullChamber Γ (c + d) → FullChamber Γ (c + d) →
    (Strand (c + d) → 𝕜) × (Strand (c + d) → 𝕜)}
  (hP₄ : ∀ C E, IsChamberSegment C E (P₄ C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW₃ : ∀ w : Wall Γ (a + b), IsRegular (w.factor (k := k)))
  (hW₄ : ∀ w : Wall Γ (c + d), IsRegular (w.factor (k := k)))
  (hL₃ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b)), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  (hL₄ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (c + d)), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- The vectors of the spanning family of the juxtaposed corner are homogeneous. -/
theorem middleCornerVec_homogeneous (i : MiddleCornerIdx Γ L' L'') :
    ∃ n, middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'' i ∈
      middleGrading G a b c d n := by
  obtain ⟨n₁, h₁⟩ := rowGen_homogeneous G hD hZ (⟨⟨L', hL'⟩, i.1.1⟩ : RowGen Γ a c)
  obtain ⟨n₂, h₂⟩ := rowGen_homogeneous G hD hZ (⟨⟨L'', hL''⟩, i.1.2⟩ : RowGen Γ b d)
  obtain ⟨n₃, h₃⟩ := cornerBasis_homogeneous hP₃ hD hZ hΓ hW₃ hL₃ G _ R' i.2.1
  obtain ⟨n₄, h₄⟩ := cornerBasis_homogeneous hP₄ hD hZ hΓ hW₄ hL₄ G _ R'' i.2.2
  exact ⟨n₁ + n₂ + (n₃ + n₄), tmul_mem_balancedGrading (tmul_mem_tensorGrading h₁ h₂)
    (tmul_mem_tensorGrading (ℳ := G.klrGrade (a + b)) (𝒩 := G.klrGrade (c + d)) h₃ h₄)⟩

end Corner

section Isomorphism

variable {L' : FullChamber Γ (a + c)} {L'' : FullChamber Γ (b + d)}
  {R' : FullChamber Γ (a + b)} {R'' : FullChamber Γ (c + d)}
  {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))),
    Γ.loop s.1 = some Q → s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

include hD hZ hΓ hW hL in
/-- **The juxtaposed corner is spanned by homogeneous vectors**: it is the sum of its graded
pieces. -/
theorem iSup_middleCornerGrading (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered)
    (hR' : R'.IsRankOrdered) (hR'' : R''.IsRankOrdered) :
    ⨆ n, middleCornerGrading G hL' hL'' hR' hR'' n = ⊤ := by
  classical
  choose P₁ hP₁ using fun C E : FullChamber Γ (a + c) => exists_isChamberSegment hD hZ C E
  choose P₂ hP₂ using fun C E : FullChamber Γ (b + d) => exists_isChamberSegment hD hZ C E
  choose P₃ hP₃ using fun C E : FullChamber Γ (a + b) => exists_isChamberSegment hD hZ C E
  choose P₄ hP₄ using fun C E : FullChamber Γ (c + d) => exists_isChamberSegment hD hZ C E
  have hW' := isRegular_factor_layout hW
  have hL'₀ := isRegular_loopFactor_layout hL
  have hW₁ := isRegular_factor_of_embedding (leftEmb (a + c) (b + d)) hW'
  have hW₂ := isRegular_factor_of_embedding (rightEmb (a + c) (b + d)) hW'
  have hW₃ := isRegular_factor_of_embedding (leftEmb (a + b) (c + d)) hW
  have hW₄ := isRegular_factor_of_embedding (rightEmb (a + b) (c + d)) hW
  have hL₁ := isRegular_loopFactor_of_embedding (leftEmb (a + c) (b + d)) hL'₀
  have hL₂ := isRegular_loopFactor_of_embedding (rightEmb (a + c) (b + d)) hL'₀
  have hL₃ := isRegular_loopFactor_of_embedding (leftEmb (a + b) (c + d)) hL
  have hL₄ := isRegular_loopFactor_of_embedding (rightEmb (a + b) (c + d)) hL
  set π := middleCornerMap (rankE k hL' ⊗ₜ rankE k hL'') (rankE k hR' ⊗ₜ rankE k hR'')
  have hle := range_middleCornerMap_le_span (hP₁ := hP₁) (hP₂ := hP₂) (hW₁ := hW₁)
    (hW₂ := hW₂) (hL₁ := hL₁) (hL₂ := hL₂) hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR''
  have key : ∀ x ∈ Submodule.span k (Set.range
      (middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'')),
      ∃ hx : x ∈ LinearMap.range π,
        (⟨x, hx⟩ : LinearMap.range π) ∈ ⨆ n, middleCornerGrading G hL' hL'' hR' hR'' n := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨n, hn⟩ := middleCornerVec_homogeneous G hL' hL'' hR' hR'' hP₃ hP₄ hD hZ hΓ hW₃
        hW₄ hL₃ hL₄ i
      exact ⟨middleCornerVec_mem_range hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'' i,
        Submodule.mem_iSup_of_mem n hn⟩
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add y z _ _ hy hz =>
      obtain ⟨hy₁, hy₂⟩ := hy
      obtain ⟨hz₁, hz₂⟩ := hz
      exact ⟨add_mem hy₁ hz₁, add_mem hy₂ hz₂⟩
    | smul r y _ hy =>
      obtain ⟨hy₁, hy₂⟩ := hy
      exact ⟨Submodule.smul_mem _ r hy₁, Submodule.smul_mem _ r hy₂⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨_, h⟩ := key x (hle hx)
  exact h

include hP hΓ hW hL in
/-- **Webster, Theorem 2.19, graded, for the step of shuffle type `c`.** The isomorphism
`middleCornerEquiv` from the juxtaposed corner `(e L' ⊗ e L'') MiddleTensor (e R' ⊗ e R'')` onto
the subquotient `S / S'` of the Mackey filtration of `e (L' L'') * A * e (R' R'')` is a graded
isomorphism from the juxtaposed corner shifted up by `middleShift G a b c d`
`= ∑_{i, j} b_i c_j pairDeg i j`, for every grading datum `G`. The hypotheses are those of
`middleCornerEquiv`. -/
noncomputable def middleCornerGradedEquiv (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered)
    (hR' : R'.IsRankOrdered) (hR'' : R''.IsRankOrdered) {S' S : Set (I → ℕ)}
    (hS : IsLowerSet S) (hcS : ⇑c ∈ S) (hS' : Set.Iio ⇑c ⊆ S') (hcS' : ⇑c ∉ S')
    (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c) :
    Graded.shift (middleCornerGrading G hL' hL'' hR' hR'') (middleShift G a b c d) ≃ᵍ[k]
      mackeySubquotientGrading hP hD hZ hΓ hW hL G (a + b) (a + c)
        (castChamber (layout_eq a b c d) (chamber L' L'')) (chamber R' R'') S' S :=
  GradedEquiv.ofProjections
    (middleCornerEquiv hP hD hZ hΓ hW hL hL' hL'' hR' hR'' hS hcS hS' hcS' hc)
    (middleShift G a b c d)
    (fun _ _ hx => middleTensorMap_mem_grading G hP hD hZ hΓ hW hL _ _ hS hcS hS' hx)
    (iSup_middleCornerGrading G hD hZ hΓ hW hL hL' hL'' hR' hR'')
    (mackeySubquotientProj hP hD hZ hΓ hW hL G _ _ _ _ S' S)
    (mackeySubquotientProj_of_mem hP hD hZ hΓ hW hL G _ _ _ _ S' S)
    (mackeySubquotientProj_of_mem_ne hP hD hZ hΓ hW hL G _ _ _ _ S' S)

theorem middleCornerGradedEquiv_apply (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered)
    (hR' : R'.IsRankOrdered) (hR'' : R''.IsRankOrdered) {S' S : Set (I → ℕ)}
    (hS : IsLowerSet S) (hcS : ⇑c ∈ S) (hS' : Set.Iio ⇑c ⊆ S') (hcS' : ⇑c ∉ S')
    (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c) (x) :
    middleCornerGradedEquiv G hP hD hZ hΓ hW hL hL' hL'' hR' hR'' hS hcS hS' hcS' hc x =
      middleCornerEquiv hP hD hZ hΓ hW hL hL' hL'' hR' hR'' hS hcS hS' hcS' hc x := rfl

include hP hΓ hW hL in
/-- **Webster, Theorem 2.19, graded**, for the subquotient `Iic c / Iio c` of shuffle type `c`:
the juxtaposed corner shifted up by `middleShift G a b c d` is isomorphic as a graded module to
the subquotient of the Mackey filtration of `e (L' L'') * A * e (R' R'')`. -/
noncomputable def middleCornerGradedEquivIic (hL' : L'.IsRankOrdered)
    (hL'' : L''.IsRankOrdered) (hR' : R'.IsRankOrdered) (hR'' : R''.IsRankOrdered) :
    Graded.shift (middleCornerGrading G hL' hL'' hR' hR'') (middleShift G a b c d) ≃ᵍ[k]
      mackeySubquotientGrading hP hD hZ hΓ hW hL G (a + b) (a + c)
        (castChamber (layout_eq a b c d) (chamber L' L'')) (chamber R' R'')
        (Set.Iio ⇑c) (Set.Iic ⇑c) :=
  middleCornerGradedEquiv G hP hD hZ hΓ hW hL hL' hL'' hR' hR'' (isLowerSet_Iic _)
    (Set.mem_Iic.2 le_rfl) subset_rfl (fun h => lt_irrefl _ (Set.mem_Iio.1 h))
    (fun _ h h' => (Set.mem_Iic.1 h).eq_or_lt.resolve_right h')

end Isomorphism

end Juxtapose

end Categorification.WeightedKLR
