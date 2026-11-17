/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.KLR.SpacedComparison
import Categorification.WeightedKLR.Local.Chambers
import Categorification.WeightedKLR.Local.Operators

/-!
# Local charts of weighted KLR gallery algebras

Supporting the absolute-irreducibility input of roadmap A for B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
Theorem 2.19. A local chart is checked in the faithful polynomial representation
of Proposition 2.7, so that the relations of Definition 2.4 descend automatically.
The geometric chart at a point uses only the hyperplanes incident with that point.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

section CornerRepresentation

variable {k A V : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] (ρ : A →ₐ[k] Module.End k V)
  {e : A} (he : IsIdempotentElem e)

/-- Restrict a representation of `A` to the image of an idempotent. This is the
polynomial space of the chamber star in the local-chart construction. -/
def cornerRepresentation : he.Corner →ₐ[k] Module.End k (LinearMap.range (ρ e)) := by
  let F : he.Corner →ₗ[k] Module.End k (LinearMap.range (ρ e)) :=
    { toFun := fun x =>
        { toFun := fun v => ⟨ρ x.1 v.1, ⟨ρ x.1 v.1, by
            rw [← Module.End.mul_apply, ← map_mul,
              (Subsemigroup.mem_corner_iff he).1 x.2 |>.1]⟩⟩
          map_add' := fun v w => Subtype.ext (map_add _ _ _)
          map_smul' := fun c v => Subtype.ext (map_smul _ _ _) }
      map_add' := fun x y => LinearMap.ext fun v => Subtype.ext (by
        change ρ (x.1 + y.1) v.1 = _
        rw [map_add, LinearMap.add_apply]
        rfl)
      map_smul' := fun c x => LinearMap.ext fun v => Subtype.ext (by
        change ρ (c • x.1) v.1 = _
        rw [map_smul, LinearMap.smul_apply]
        rfl) }
  refine AlgHom.ofLinearMap F ?_ ?_
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    obtain ⟨w, hw⟩ := v.2
    change ρ e v.1 = v.1
    rw [← hw, ← Module.End.mul_apply, ← map_mul, he.eq]
  · intro x y
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ (x.1 * y.1) v.1 = ρ x.1 (ρ y.1 v.1)
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem cornerRepresentation_apply (x : he.Corner)
    (v : LinearMap.range (ρ e)) :
    (cornerRepresentation ρ he x v).1 = ρ x.1 v.1 := rfl

/-- Faithfulness is preserved on the idempotent corner after restricting to its
polynomial summands (Webster Proposition 2.7, in the local chart). -/
theorem cornerRepresentation_injective (hρ : Function.Injective ρ) :
    Function.Injective (cornerRepresentation ρ he) := by
  intro x y h
  apply Subtype.ext
  apply hρ
  apply LinearMap.ext
  intro v
  have h' := congrArg
    (fun f : Module.End k (LinearMap.range (ρ e)) => (f ⟨ρ e v, ⟨v, rfl⟩⟩).1) h
  change ρ x.1 (ρ e v) = ρ y.1 (ρ e v) at h'
  rwa [← Module.End.mul_apply, ← map_mul, (Subsemigroup.mem_corner_iff he).1 x.2 |>.2,
    ← Module.End.mul_apply, ← map_mul, (Subsemigroup.mem_corner_iff he).1 y.2 |>.2] at h'

end CornerRepresentation

section ChamberSummands

open GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}
  {ι : Type*} [Fintype ι] (J : ι → FullChamber Γ ν)

/-- The idempotent selecting the chambers of a chart. -/
def chamberIdem : GalleryAlgebra k Γ ν := ∑ i, e (J i)

theorem chamberIdem_mul_e (hJ : Function.Injective J) (i : ι) :
    chamberIdem (k := k) J * e (J i) = e (J i) := by
  classical
  simp [chamberIdem, Finset.sum_mul, e_mul_e, hJ.eq_iff]

theorem e_mul_chamberIdem (hJ : Function.Injective J) (i : ι) :
    e (J i) * chamberIdem (k := k) J = e (J i) := by
  classical
  simp [chamberIdem, Finset.mul_sum, e_mul_e, hJ.eq_iff]

theorem chamberIdem_idempotent (hJ : Function.Injective J) :
    IsIdempotentElem (chamberIdem (k := k) J) := by
  classical
  show chamberIdem J * chamberIdem J = chamberIdem (k := k) J
  simp only [chamberIdem, Finset.sum_mul]
  change (∑ i, e (J i) * chamberIdem J) = chamberIdem (k := k) J
  simp only [e_mul_chamberIdem J hJ]
  rfl

theorem chamberIdem_mul_poly (f : PolyRing ν k) :
    chamberIdem J * poly f = poly f * chamberIdem J := by
  classical
  simp only [chamberIdem, Finset.sum_mul, Finset.mul_sum, e_mul_poly]

theorem chamberIdem_mul_t (hJ : Function.Injective J) (i j : ι) :
    chamberIdem (k := k) J * t (J i) (J j) = t (J i) (J j) := by
  rw [← e_mul_t, ← mul_assoc, chamberIdem_mul_e J hJ]

theorem t_mul_chamberIdem (hJ : Function.Injective J) (i j : ι) :
    t (J i) (J j) * chamberIdem (k := k) J = t (J i) (J j) := by
  rw [← t_mul_e, mul_assoc, e_mul_chamberIdem J hJ]

/-- Extend a collection of polynomial summands by zero to the original chambers. -/
def chamberIncl : (ι → PolyRing ν k) →ₗ[k] (FullChamber Γ ν → PolyRing ν k) := by
  classical
  exact ∑ i, (LinearMap.single k (fun _ : FullChamber Γ ν => PolyRing ν k) (J i)).comp
    (LinearMap.proj i)

/-- Read off the polynomial summands selected by the chart. -/
def chamberProj : (FullChamber Γ ν → PolyRing ν k) →ₗ[k] (ι → PolyRing ν k) :=
  LinearMap.pi fun i => LinearMap.proj (J i)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] [Fintype ι] in
@[simp] theorem chamberProj_apply (v : FullChamber Γ ν → PolyRing ν k) (i : ι) :
    chamberProj J v i = v (J i) := rfl

omit [IsStrictOrderedRing 𝕜] in
theorem chamberIncl_apply (v : ι → PolyRing ν k) :
    chamberIncl J v = ∑ i, Pi.single (J i) (v i) := by
  classical
  simp only [chamberIncl, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.single_apply,
    LinearMap.proj_apply]

omit [IsStrictOrderedRing 𝕜] in
theorem chamberProj_incl (hJ : Function.Injective J) (v : ι → PolyRing ν k) :
    chamberProj J (chamberIncl J v) = v := by
  classical
  funext i
  rw [chamberProj_apply, chamberIncl_apply, Finset.sum_apply, Finset.sum_eq_single i]
  · exact Pi.single_eq_same _ _
  · intro j _ hji
    exact Pi.single_eq_of_ne (fun h => hji (hJ h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [IsStrictOrderedRing 𝕜] in
theorem chamberIncl_at (hJ : Function.Injective J) (v : ι → PolyRing ν k) (i : ι) :
    chamberIncl J v (J i) = v i :=
  congrFun (chamberProj_incl J hJ v) i

theorem chamberIncl_proj (hΓ : Γ.PSymm) (v : FullChamber Γ ν → PolyRing ν k) :
    chamberIncl J (chamberProj J v) = galleryRep k hΓ (chamberIdem J) v := by
  classical
  rw [chamberIncl_apply]
  simp only [chamberIdem, map_sum, LinearMap.sum_apply, galleryRep_e, blk_apply,
    LinearMap.id_apply, chamberProj_apply]

theorem galleryRep_chamberIdem_apply (hJ : Function.Injective J) (hΓ : Γ.PSymm)
    (v : FullChamber Γ ν → PolyRing ν k) (i : ι) :
    galleryRep k hΓ (chamberIdem J) v (J i) = v (J i) := by
  have h := congrFun (chamberProj_incl J hJ (chamberProj J v)) i
  rw [chamberIncl_proj] at h
  exact h

theorem galleryRep_chamberIdem_incl (hJ : Function.Injective J) (hΓ : Γ.PSymm)
    (v : ι → PolyRing ν k) :
    galleryRep k hΓ (chamberIdem J) (chamberIncl J v) = chamberIncl J v := by
  rw [← chamberIncl_proj, chamberProj_incl J hJ]

/-- Sandwich an arbitrary original operator into the selected chamber corner. -/
def chamberSandwich (hJ : Function.Injective J) (x : GalleryAlgebra k Γ ν) :
    (chamberIdem_idempotent (k := k) J hJ).Corner :=
  ⟨chamberIdem J * x * chamberIdem J, ⟨x, rfl⟩⟩

/-- The selected polynomial summands are the image of the chart idempotent. -/
def chamberRangeEquiv (hJ : Function.Injective J) (hΓ : Γ.PSymm) :
    (ι → PolyRing ν k) ≃ₗ[k]
      LinearMap.range (galleryRep k hΓ (chamberIdem J)) where
  toFun v := ⟨chamberIncl J v, ⟨chamberIncl J v, by
    rw [← chamberIncl_proj, chamberProj_incl J hJ]⟩⟩
  invFun v := chamberProj J v.1
  left_inv v := chamberProj_incl J hJ v
  right_inv v := Subtype.ext (by
    change chamberIncl J (chamberProj J v.1) = v.1
    rw [chamberIncl_proj]
    obtain ⟨w, hw⟩ := v.2
    rw [← hw, ← Module.End.mul_apply, ← map_mul, (chamberIdem_idempotent J hJ).eq])
  map_add' v w := Subtype.ext (map_add (chamberIncl J) v w)
  map_smul' c v := Subtype.ext (map_smul (chamberIncl J) c v)

/-- The chart corner acts on its polynomial summands. -/
def chamberRepresentation (hJ : Function.Injective J) (hΓ : Γ.PSymm) :
    (chamberIdem_idempotent (k := k) J hJ).Corner →ₐ[k]
      Module.End k (ι → PolyRing ν k) :=
  ((chamberRangeEquiv J hJ hΓ).symm.conjAlgEquiv k).toAlgHom.comp
    (cornerRepresentation (galleryRep k hΓ) (chamberIdem_idempotent J hJ))

theorem chamberRepresentation_apply (hJ : Function.Injective J) (hΓ : Γ.PSymm)
    (x : (chamberIdem_idempotent (k := k) J hJ).Corner)
    (v : ι → PolyRing ν k) (i : ι) :
    chamberRepresentation J hJ hΓ x v i =
      galleryRep k hΓ x.1 (chamberIncl J v) (J i) := rfl

theorem chamberRepresentation_sandwich (hJ : Function.Injective J) (hΓ : Γ.PSymm)
    (x : GalleryAlgebra k Γ ν) (v : ι → PolyRing ν k) (i : ι) :
    chamberRepresentation J hJ hΓ (chamberSandwich J hJ x) v i =
      galleryRep k hΓ x (chamberIncl J v) (J i) := by
  rw [chamberRepresentation_apply]
  change galleryRep k hΓ (chamberIdem J * x * chamberIdem J) (chamberIncl J v) (J i) = _
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    galleryRep_chamberIdem_incl J hJ hΓ, galleryRep_chamberIdem_apply J hJ hΓ]

/-- The chart corner representation is faithful whenever the original polynomial
representation is faithful. -/
theorem chamberRepresentation_injective (hJ : Function.Injective J) (hΓ : Γ.PSymm)
    (hρ : Function.Injective (galleryRep k hΓ (ν := ν))) :
    Function.Injective (chamberRepresentation J hJ hΓ) :=
  ((chamberRangeEquiv J hJ hΓ).symm.conjAlgEquiv k).injective.comp
    (cornerRepresentation_injective (galleryRep k hΓ) (chamberIdem_idempotent J hJ) hρ)

end ChamberSummands

end Categorification.WeightedKLR.Local

namespace Categorification.WeightedKLR.GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}
  {B D : Type*} [Ring B] [Algebra k B] [Ring D] [Algebra k D]

/-- Construct a chart from generator images whose operators agree with an existing
representation. Injectivity of the target representation checks all relations of
Webster Definition 2.4 at once. The generator intertwining is an explicit hypothesis
of this supporting construction, not a hypothesis of the simple-module theorem. -/
def liftOfFaithfulRepresentation (ρ : B →ₐ[k] D) (hρ : Function.Injective ρ)
    (φ : GalleryAlgebra k Γ ν →ₐ[k] D) (g : Gen k Γ ν → B)
    (hg : ∀ a, ρ (g a) = φ (mk k Γ ν (FreeAlgebra.ι k a))) :
    GalleryAlgebra k Γ ν →ₐ[k] B := by
  let F : FreeAlgebra k (Gen k Γ ν) →ₐ[k] B := FreeAlgebra.lift k g
  have hF : ρ.comp F = φ.comp (mk k Γ ν) := by
    apply FreeAlgebra.hom_ext
    funext a
    simpa [F] using hg a
  refine RingQuot.liftAlgHom k ⟨F, fun x y h => hρ ?_⟩
  change (ρ.comp F) x = (ρ.comp F) y
  rw [hF]
  exact congrArg φ (rel h)

theorem liftOfFaithfulRepresentation_mk (ρ : B →ₐ[k] D) (hρ : Function.Injective ρ)
    (φ : GalleryAlgebra k Γ ν →ₐ[k] D) (g : Gen k Γ ν → B)
    (hg : ∀ a, ρ (g a) = φ (mk k Γ ν (FreeAlgebra.ι k a)))
    (x : FreeAlgebra k (Gen k Γ ν)) :
    liftOfFaithfulRepresentation ρ hρ φ g hg (mk k Γ ν x) = FreeAlgebra.lift k g x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

theorem faithfulRepresentation_lift (ρ : B →ₐ[k] D) (hρ : Function.Injective ρ)
    (φ : GalleryAlgebra k Γ ν →ₐ[k] D) (g : Gen k Γ ν → B)
    (hg : ∀ a, ρ (g a) = φ (mk k Γ ν (FreeAlgebra.ι k a))) :
    ρ.comp (liftOfFaithfulRepresentation ρ hρ φ g hg) = φ := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := mk_surjective x
  rw [AlgHom.comp_apply, liftOfFaithfulRepresentation_mk]
  have hF : ρ.comp (FreeAlgebra.lift k g) = φ.comp (mk k Γ ν) := by
    apply FreeAlgebra.hom_ext
    funext a
    simpa using hg a
  exact AlgHom.congr_fun hF x

end Categorification.WeightedKLR.GalleryAlgebra

namespace Categorification.WeightedKLR.Local

open GalleryAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The sum of the idempotents of all original chambers incident to the point. -/
def chartIdem (p : Strand ν → 𝕜) : GalleryAlgebra k Γ ν :=
  chamberIdem (chamber (Γ := Γ) p)

theorem chartIdem_idempotent (p : Strand ν → 𝕜) :
    IsIdempotentElem (chartIdem (Γ := Γ) p) :=
  chamberIdem_idempotent (chamber p) (chamber_injective p)

/-- The polynomial representation of the original chamber-star corner. -/
def chartRepresentation (p : Strand ν → 𝕜) (hΓ : Γ.PSymm) :
    (chartIdem_idempotent (Γ := Γ) p).Corner →ₐ[k]
      Module.End k (FullChamber (graph Γ p) (weight p) → PolyRing ν k) :=
  chamberRepresentation (chamber p) (chamber_injective p) hΓ

/-- Rename the polynomial variables on every local chamber summand. -/
def polynomialSummandsEquiv (p : Strand ν → 𝕜) :
    (FullChamber (graph Γ p) (weight p) → PolyRing (weight p) k) ≃ₗ[k]
      (FullChamber (graph Γ p) (weight p) → PolyRing ν k) :=
  LinearEquiv.piCongrRight fun _ => (polyEquiv (k := k) p).toLinearEquiv

/-- The polynomial representation of the refined graph, on renamed variables. -/
def chartPolynomialRep (p : Strand ν → 𝕜) (hS : Γ.Standing) :
    GalleryAlgebra k (graph Γ p) (weight p) →ₐ[k]
      Module.End k (FullChamber (graph Γ p) (weight p) → PolyRing ν k) :=
  ((polynomialSummandsEquiv (Γ := Γ) p).conjAlgEquiv k).toAlgHom.comp
    (galleryRep k (standing p hS).psymm)

/-- Original diagram representatives of the generators in a local chart. -/
def chartRawGen (p : Strand ν → 𝕜) :
    Gen k (graph Γ p) (weight p) → GalleryAlgebra k Γ ν
  | .idem C => e (chamber p C)
  | .poly f => poly (polyEquiv p f)
  | .step C D => t (chamber p C) (chamber p D)
  | .relabel g C => r (perm p g) (chamber p C)

/-- Generator representatives, regarded as elements of the chamber-star corner. -/
def chartGen (p : Strand ν → 𝕜) (a : Gen k (graph Γ p) (weight p)) :
    (chartIdem_idempotent (Γ := Γ) p).Corner :=
  chamberSandwich (chamber p) (chamber_injective p) (chartRawGen p a)

theorem chartPolynomialRep_gen (p : Strand ν → 𝕜) (hS : Γ.Standing)
    (a : Gen k (graph Γ p) (weight p))
    (v : FullChamber (graph Γ p) (weight p) → PolyRing ν k)
    (C : FullChamber (graph Γ p) (weight p)) :
    chartPolynomialRep p hS (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k a)) v C =
      polyEquiv p (genOp k (graph Γ p) (weight p) a
        (fun D => (polyEquiv p).symm (v D)) C) := by
  simp only [chartPolynomialRep, AlgHom.comp_apply, galleryRep_mk, freeRep,
    FreeAlgebra.lift_ι_apply]
  rfl

/-- The original chart diagrams have exactly the local polynomial operators. -/
theorem chartGen_intertwines (p : Strand ν → 𝕜) (hS : Γ.Standing)
    (a : Gen k (graph Γ p) (weight p)) :
    chartRepresentation p hS.psymm (chartGen p a) =
      chartPolynomialRep p hS (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k a)) := by
  apply LinearMap.ext
  intro v
  funext C
  change chamberRepresentation (chamber p) (chamber_injective p) hS.psymm
      (chamberSandwich (chamber p) (chamber_injective p) (chartRawGen p a)) v C = _
  rw [chamberRepresentation_sandwich, chartPolynomialRep_gen]
  cases a with
  | idem D =>
    by_cases h : C = D
    · subst D
      simp [chartRawGen, galleryRep_e, blk_apply, genOp,
        chamberIncl_at _ (chamber_injective p)]
    · have hJ : chamber p C ≠ chamber p D := fun he => h (chamber_injective p he)
      simp [chartRawGen, galleryRep_e, blk_apply, genOp, h, hJ]
  | poly f =>
    simp [chartRawGen, galleryRep_poly, diagOp_apply, genOp,
      chamberIncl_at _ (chamber_injective p), map_mul]
  | step D E =>
    by_cases h : C = E
    · subst E
      simp only [chartRawGen, galleryRep_t, blk_apply, genOp, Pi.single_eq_same,
        chamberIncl_at _ (chamber_injective p)]
      simpa only [AlgEquiv.apply_symm_apply] using
        (polyEquiv_stepOp p D C ((polyEquiv p).symm (v D))).symm
    · have hJ : chamber p C ≠ chamber p E := fun he => h (chamber_injective p he)
      simp [chartRawGen, galleryRep_t, blk_apply, genOp, h, hJ]
  | relabel g D =>
    by_cases h : C = g • D
    · subst C
      simp only [chartRawGen, galleryRep_r, perm_smul_chamber, blk_apply, genOp,
        Pi.single_eq_same, chamberIncl_at _ (chamber_injective p)]
      simpa only [AlgEquiv.apply_symm_apply] using
        (polyEquiv_ren p g ((polyEquiv p).symm (v D))).symm
    · have hJ : chamber p C ≠ chamber p (g • D) := fun he => h (chamber_injective p he)
      simp [chartRawGen, galleryRep_r, perm_smul_chamber, blk_apply, genOp,
        h, hJ]

/-- The local zero-weight gallery algebra embeds into the original chamber-star
corner. This supporting map for Theorem 2.19 is checked in the faithful polynomial
representation of Webster Proposition 2.7. It is not asserted to be surjective. -/
def galleryHom (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) :
    GalleryAlgebra k (graph Γ p) (weight p) →ₐ[k] (chartIdem_idempotent (Γ := Γ) p).Corner :=
  liftOfFaithfulRepresentation (chartRepresentation p hS.psymm)
    (chamberRepresentation_injective (chamber p) (chamber_injective p) hS.psymm
      (galleryRep_injective hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor'))
    (chartPolynomialRep p hS) (chartGen p) (chartGen_intertwines p hS)

theorem galleryHom_mk (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (x : FreeAlgebra k (Gen k (graph Γ p) (weight p))) :
    galleryHom p hD hZ hS (mk k (graph Γ p) (weight p) x) =
      FreeAlgebra.lift k (chartGen p) x :=
  liftOfFaithfulRepresentation_mk _ _ _ _ _ x

theorem galleryHom_one_val (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) : (galleryHom p hD hZ hS 1).1 = chartIdem (Γ := Γ) p := by
  rw [map_one]
  rfl

theorem galleryHom_e (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (C : FullChamber (graph Γ p) (weight p)) :
    (galleryHom p hD hZ hS (e C)).1 = e (chamber p C) := by
  change (galleryHom p hD hZ hS
    (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k (.idem C)))).1 = _
  rw [galleryHom_mk, FreeAlgebra.lift_ι_apply]
  change chamberIdem (chamber p) * e (chamber p C) * chamberIdem (chamber p) = _
  rw [chamberIdem_mul_e _ (chamber_injective p), e_mul_chamberIdem _ (chamber_injective p)]

theorem galleryHom_poly (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (f : PolyRing (weight p) k) :
    (galleryHom p hD hZ hS (poly f)).1 = poly (polyEquiv p f) * chartIdem (Γ := Γ) p := by
  change (galleryHom p hD hZ hS
    (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k (.poly f)))).1 = _
  rw [galleryHom_mk, FreeAlgebra.lift_ι_apply]
  change chamberIdem (chamber p) * poly (polyEquiv p f) * chamberIdem (chamber p) = _
  rw [chamberIdem_mul_poly, mul_assoc, (chamberIdem_idempotent _ (chamber_injective p)).eq]
  rfl

theorem galleryHom_t (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (C D : FullChamber (graph Γ p) (weight p)) :
    (galleryHom p hD hZ hS (t C D)).1 = t (chamber p C) (chamber p D) := by
  change (galleryHom p hD hZ hS
    (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k (.step C D)))).1 = _
  rw [galleryHom_mk, FreeAlgebra.lift_ι_apply]
  change chamberIdem (chamber p) * t (chamber p C) (chamber p D) * chamberIdem (chamber p) = _
  rw [chamberIdem_mul_t _ (chamber_injective p), t_mul_chamberIdem _ (chamber_injective p)]

theorem galleryHom_r (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (g : ColPerm (weight p))
    (C : FullChamber (graph Γ p) (weight p)) :
    (galleryHom p hD hZ hS (r g C)).1 = r (perm p g) (chamber p C) := by
  change (galleryHom p hD hZ hS
    (mk k (graph Γ p) (weight p) (FreeAlgebra.ι k (.relabel g C)))).1 = _
  rw [galleryHom_mk, FreeAlgebra.lift_ι_apply]
  change chamberIdem (chamber p) * r (perm p g) (chamber p C) * chamberIdem (chamber p) = _
  have hleft : chamberIdem (chamber p) * r (perm p g) (chamber p C) =
      r (perm p g) (chamber p C) := by
    rw [r_eq, perm_smul_chamber, ← mul_assoc, ← mul_assoc,
      chamberIdem_mul_e _ (chamber_injective p), ← perm_smul_chamber, ← r_eq]
  rw [hleft, ← r_mul_e, mul_assoc, e_mul_chamberIdem _ (chamber_injective p)]

/-- The full chart, followed by inclusion of its chamber-star corner. -/
def galleryVal (p : Strand ν → 𝕜) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) :
    GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν where
  toFun a := (galleryHom p hD hZ hS a).1
  map_zero' := congrArg Subtype.val (map_zero (galleryHom p hD hZ hS))
  map_add' a b := congrArg Subtype.val (map_add (galleryHom p hD hZ hS) a b)
  map_mul' a b := congrArg Subtype.val (map_mul (galleryHom p hD hZ hS) a b)

@[simp] theorem galleryVal_apply (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (b : GalleryAlgebra k (graph Γ p) (weight p)) :
    galleryVal p hD hZ hS b = (galleryHom p hD hZ hS b).1 := rfl

@[simp] theorem galleryVal_e (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (C : FullChamber (graph Γ p) (weight p)) :
    galleryVal p hD hZ hS (e C) = e (chamber p C) := galleryHom_e p hD hZ hS C

theorem galleryVal_map_smul (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (c : k)
    (a : GalleryAlgebra k (graph Γ p) (weight p)) :
    galleryVal p hD hZ hS (c • a) = c • galleryVal p hD hZ hS a :=
  congrArg Subtype.val (map_smul (galleryHom p hD hZ hS) c a)

theorem galleryVal_poly (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (f : PolyRing (weight p) k) :
    galleryVal p hD hZ hS (poly f) =
      poly (rename (strandEquiv p) f) * galleryVal p hD hZ hS 1 := by
  change (galleryHom p hD hZ hS (poly f)).1 =
    poly (rename (strandEquiv p) f) * (galleryHom p hD hZ hS 1).1
  rw [galleryHom_poly, galleryHom_one_val, polyEquiv_apply]

end Categorification.WeightedKLR.Local
