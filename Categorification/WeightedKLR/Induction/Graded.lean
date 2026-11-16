/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Grading
import Categorification.WeightedKLR.Induction.TensorMap

/-!
# Juxtaposition preserves degrees

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4: the map
`ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}` (paragraph before Definition 2.17) juxtaposes
diagrams. For every grading datum `G` (`WeightedKLR.GradingDatum`, the degree function of §2.1),
it sends the tensor product of elements of degrees `d'` and `d''` to an element of degree
`d' + d''`, so `ι` is a map of graded algebras, and induction and restriction (Definition 2.17)
are built from graded maps.

The degree of a dot, of a step across a wall and of a same-colour crossing only depends on the
colours involved, and the embeddings of arrangements (`ChamberEmbedding`) preserve colours. So
the algebra map `ChamberEmbedding.galleryHom` intertwines the coactions defining the gradings
(`ChamberEmbedding.coaction_galleryVal`); the maps `leftHom`, `rightHom` and `ι` are built from
these maps.

## Main results

* `ChamberEmbedding.galleryHom_mem_grade`: the map of an embedding of arrangements preserves
  degrees.
* `Juxtapose.galleryTensorHom_tmul_mem_grade`, `Juxtapose.inductionMap_tmul_mem_grade`:
  juxtaposition `ι_{ν';ν''}` adds degrees.
-/

namespace Categorification.WeightedKLR

open AddMonoidAlgebra GalleryAlgebra IsIdempotentElem
open scoped TensorProduct

/-- `AddMonoidAlgebra.map` along a non-unital ring map is multiplicative. -/
theorem _root_.AddMonoidAlgebra.map_mul_of_nonUnitalRingHom {R S M : Type*} [Semiring R]
    [Semiring S] [AddMonoid M] (f : R →ₙ+* S) (x y : AddMonoidAlgebra R M) :
    map (f : R →+ S) (x * y) = map (f : R →+ S) x * map (f : R →+ S) y := by
  classical
  ext
  simp [AddMonoidAlgebra.mul_def, Finsupp.sum_mapRange_index, map_finsuppSum, Finsupp.single_apply,
    apply_ite]

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace ChamberEmbedding

variable {ν₁ ν : I →₀ ℕ} (G : GradingDatum Γ) (J : ChamberEmbedding Γ ν₁ ν)

/-- The map of an embedding of arrangements, with values in the gallery algebra of `ν`. -/
noncomputable def galleryVal : GalleryAlgebra k Γ ν₁ →ₙ+* GalleryAlgebra k Γ ν where
  toFun x := (J.galleryHom x).1
  map_mul' x y := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl

theorem galleryVal_apply (x : GalleryAlgebra k Γ ν₁) : J.galleryVal x = (J.galleryHom x).1 :=
  rfl

omit [DecidableEq I] in
theorem hypDeg_hyp (h : Hyp Γ ν₁) : G.hypDeg (J.hyp h) = G.hypDeg h := by
  rcases h with w | d
  · rfl
  · exact congrArg G.cross (J.colour d.fst)

theorem stepDeg_chamber (C D : FullChamber Γ ν₁) :
    G.stepDeg (J.chamber C) (J.chamber D) = G.stepDeg C D := by
  by_cases hC : ∃ h, C.Adjacent D h
  · obtain ⟨h, hh⟩ := hC
    rw [G.stepDeg_of_adjacent hh, G.stepDeg_of_adjacent (J.adjacent_chamber hh), J.hypDeg_hyp]
  · have hC' : ∀ h, ¬C.Adjacent D h := fun h hh => hC ⟨h, hh⟩
    rw [G.stepDeg_of_not_adjacent hC,
      G.stepDeg_of_not_adjacent fun ⟨h', hh⟩ => J.not_adjacent_chamber hC' h' hh]

theorem idem_mem_grade : J.idem ∈ G.grade ν 0 :=
  Submodule.sum_mem _ fun C _ => G.e_mem_grade (J.chamber C)

/-- The map of an embedding of arrangements intertwines the coactions defining the gradings. -/
theorem coaction_galleryVal (x : GalleryAlgebra k Γ ν₁) :
    G.coaction (J.galleryVal x) = map (J.galleryVal : _ →+ _) (G.coaction x) := by
  obtain ⟨u, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel k Γ ν₁) x
  change G.coaction (J.galleryVal (GalleryAlgebra.mk k Γ ν₁ u)) =
    map (J.galleryVal : _ →+ _) (G.coaction (GalleryAlgebra.mk k Γ ν₁ u))
  rw [G.coaction_mk]
  induction u using FreeAlgebra.induction with
  | grade0 c =>
    have h1 : J.galleryVal (GalleryAlgebra.mk k Γ ν₁ (algebraMap k _ c)) = c • J.idem := by
      rw [galleryVal_apply, AlgHom.commutes, AlgHom.commutes]
      exact corner_val_algebraMap _ c
    rw [h1, map_smul, (G.mem_grade).1 (idem_mem_grade G J), AlgHom.commutes,
      AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, map_single]
    rw [smul_single, ← h1, AlgHom.commutes]
    rfl
  | grade1 g =>
    cases g with
    | idem C =>
      change G.coaction (J.galleryHom (e C)).1 = map _ (G.liftF (fe k Γ ν₁ C))
      rw [galleryHom_e, G.liftF_fe, map_single, (G.mem_grade).1 (G.e_mem_grade _)]
      change _ = single 0 (J.galleryHom (e C)).1
      rw [galleryHom_e]
    | step C D =>
      change G.coaction (J.galleryHom (t C D)).1 = map _ (G.liftF (ft k Γ ν₁ C D))
      rw [galleryHom_t, G.liftF_ft, map_single, (G.mem_grade).1 (G.t_mem_grade _ _),
        stepDeg_chamber]
      change _ = single _ (J.galleryHom (t C D)).1
      rw [galleryHom_t]
    | relabel g C =>
      change G.coaction (J.galleryHom (r g C)).1 = map _ (G.liftF (fr k Γ ν₁ g C))
      rw [galleryHom_r, G.liftF_fr, map_single, (G.mem_grade).1 (G.r_mem_grade _ _)]
      change _ = single 0 (J.galleryHom (r g C)).1
      rw [galleryHom_r]
    | poly f =>
      change G.coaction (J.galleryHom (poly f)).1 = map _ (G.liftF (fp k Γ ν₁ f))
      rw [galleryHom_poly, G.liftF_fp]
      induction f using MvPolynomial.induction_on' with
      | monomial m c =>
        have hm : (MvPolynomial.monomial m c : PolyRing ν₁ k).IsWeightedHomogeneous G.wt
            (Finsupp.weight G.wt m) := MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
        have hren : (MvPolynomial.rename J.toFun (MvPolynomial.monomial m c : PolyRing ν₁ k)).IsWeightedHomogeneous G.wt
            (Finsupp.weight G.wt m) :=
          isWeightedHomogeneous_rename (w := G.wt) (w' := G.wt) J.toFun
            (fun s => congrArg G.dot (J.colour s)) hm
        rw [map_mul, (G.mem_grade).1 (G.poly_mem_grade hren), (G.mem_grade).1 (idem_mem_grade G J),
          single_mul_single, add_zero, G.polyCo_of_isWeightedHomogeneous hm, map_single]
        change _ = single _ (J.galleryHom (poly _)).1
        rw [galleryHom_poly]
      | add f f' hf hf' =>
        have hp : (poly (MvPolynomial.rename J.toFun (f + f')) : GalleryAlgebra k Γ ν) =
            poly (MvPolynomial.rename J.toFun f) + poly (MvPolynomial.rename J.toFun f') := by
          rw [map_add]; exact map_add (polyHom k Γ ν) _ _
        rw [hp, add_mul, map_add, hf, hf', map_add, AddMonoidAlgebra.map_add]
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, map_mul, map_mul_of_nonUnitalRingHom, ← ha, ← hb]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, AddMonoidAlgebra.map_add, ha, hb]

/-- **The map of an embedding of arrangements preserves degrees.** -/
theorem galleryHom_mem_grade {d : ℤ} {x : GalleryAlgebra k Γ ν₁} (hx : x ∈ G.grade ν₁ d) :
    (J.galleryHom x).1 ∈ G.grade ν d := by
  rw [G.mem_grade, ← galleryVal_apply, coaction_galleryVal, (G.mem_grade).1 hx, map_single]
  rfl

end ChamberEmbedding

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ} (G : GradingDatum Γ)

theorem leftHom_mem_grade {d : ℤ} {x : GalleryAlgebra k Γ ν'} (hx : x ∈ G.grade ν' d) :
    (leftHom k Γ ν' ν'' x).1 ∈ G.grade (ν' + ν'') d := by
  rw [leftHom, cornerSum_val]
  exact Submodule.sum_mem _ fun C'' _ => (leftChamberEmb C'').galleryHom_mem_grade G hx

theorem rightHom_mem_grade {d : ℤ} {y : GalleryAlgebra k Γ ν''} (hy : y ∈ G.grade ν'' d) :
    (rightHom k Γ ν' ν'' y).1 ∈ G.grade (ν' + ν'') d := by
  rw [rightHom, cornerSum_val]
  exact Submodule.sum_mem _ fun C' _ => (rightChamberEmb C').galleryHom_mem_grade G hy

/-- **Juxtaposition adds degrees** (Webster §2.4, the map `ι_{ν';ν''}` on gallery algebras). -/
theorem galleryTensorHom_tmul_mem_grade {d' d'' : ℤ} {x : GalleryAlgebra k Γ ν'}
    {y : GalleryAlgebra k Γ ν''} (hx : x ∈ G.grade ν' d') (hy : y ∈ G.grade ν'' d'') :
    (galleryTensorHom k Γ ν' ν'' (x ⊗ₜ y)).1 ∈ G.grade (ν' + ν'') (d' + d'') := by
  rw [galleryTensorHom_tmul]
  exact CoactionGrading.mul_mem_grade _ (leftHom_mem_grade G hx) (rightHom_mem_grade G hy)

/-- **Webster's map `ι_{ν';ν''}` adds degrees**: for `x` of degree `d'` and `y` of degree `d''`,
`ι(x ⊗ y)` has degree `d' + d''`. -/
theorem inductionMap_tmul_mem_grade {d' d'' : ℤ} {x : WeightedKLRAlgebra k Γ ν'}
    {y : WeightedKLRAlgebra k Γ ν''} (hx : x.1 ∈ G.grade ν' d') (hy : y.1 ∈ G.grade ν'' d'') :
    (inductionMap k Γ ν' ν'' (x ⊗ₜ y)).1 ∈ G.grade (ν' + ν'') (d' + d'') :=
  galleryTensorHom_tmul_mem_grade G hx hy

end Juxtapose

end Categorification.WeightedKLR
