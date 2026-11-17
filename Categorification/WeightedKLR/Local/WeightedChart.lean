/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.StarRelabel
import Categorification.WeightedKLR.Local.Chambers
import Categorification.WeightedKLR.Local.Chart
import Categorification.WeightedKLR.RedStrands.Reduced
import Categorification.WeightedKLR.Mackey.MiddleCorner
import Categorification.WeightedKLR.CentralFinite

/-!
# The local chart on rank-ordered corners

Supporting the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
Theorem 2.19 (roadmap A). A local chart at a weakly rank-ordered configuration
restricts to the rank-ordered corners defining Webster's weighted algebras.
The resulting map is non-unital: its unit image selects precisely the incident
rank-ordered chambers. These are supporting constructions for the local-chart
proof, not statements printed in the source.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

section CornerRestriction

variable {A B : Type*} [Ring A] [Ring B] {f : A} {g : B}

/-- Restrict a non-unital ring map to two idempotent corners when the source
idempotent maps into the target corner. -/
def cornerRestrict (φ : A →ₙ+* B) (hf : IsIdempotentElem f)
    (hg : IsIdempotentElem g) (hφ : φ f ∈ Subsemigroup.corner g) :
    hf.Corner →ₙ+* hg.Corner where
  toFun x := ⟨φ x.1, by
    have hx := (Subsemigroup.mem_corner_iff hf).1 x.2
    have he := (Subsemigroup.mem_corner_iff hg).1 hφ
    have hl : φ f * φ x.1 = φ x.1 := by rw [← map_mul, hx.1]
    have hr : φ x.1 * φ f = φ x.1 := by rw [← map_mul, hx.2]
    apply (Subsemigroup.mem_corner_iff hg).2
    constructor
    · rw [← hl, ← mul_assoc, he.1]
    · rw [← hr, mul_assoc, he.2]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' x y := Subtype.ext (map_add φ x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul φ x.1 y.1)

@[simp] theorem cornerRestrict_val (φ : A →ₙ+* B) (hf : IsIdempotentElem f)
    (hg : IsIdempotentElem g) (hφ : φ f ∈ Subsemigroup.corner g) (x : hf.Corner) :
    (cornerRestrict φ hf hg hφ x).1 = φ x.1 := rfl

@[simp] theorem cornerRestrict_one_val (φ : A →ₙ+* B) (hf : IsIdempotentElem f)
    (hg : IsIdempotentElem g) (hφ : φ f ∈ Subsemigroup.corner g) :
    (cornerRestrict φ hf hg hφ 1).1 = φ f := rfl

theorem cornerRestrict_map_smul {k : Type*} [CommRing k] [Algebra k A] [Algebra k B]
    (φ : A →ₙ+* B) (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hφ : φ f ∈ Subsemigroup.corner g)
    (hsmul : ∀ (c : k) (a : A), φ (c • a) = c • φ a) (c : k) (x : hf.Corner) :
    cornerRestrict φ hf hg hφ (c • x) = c • cornerRestrict φ hf hg hφ x :=
  Subtype.ext (hsmul c x.1)

end CornerRestriction

section WeightedStar

open GalleryAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

/-- Rank-ordered chambers whose closures contain the configuration. -/
abbrev RankIncident (p : Strand ν → 𝕜) :=
  {C : FullChamber Γ ν // C.IsRankOrdered ∧ C.Incident p}

noncomputable instance (p : Strand ν → 𝕜) : Fintype (RankIncident (Γ := Γ) p) :=
  Fintype.ofFinite _

/-- The sum of the idempotents of the incident rank-ordered chambers, in
Webster's weighted algebra. -/
def starIdemW (p : Strand ν → 𝕜) : WeightedKLRAlgebra k Γ ν := by
  classical
  exact ∑ C : RankIncident (Γ := Γ) p, rankE k C.2.1

theorem starIdemW_val (p : Strand ν → 𝕜) :
    (starIdemW (Γ := Γ) (k := k) p).1 =
      ∑ C : RankIncident (Γ := Γ) p, (e C.1 : GalleryAlgebra k Γ ν) := by
  classical
  let v : WeightedKLRAlgebra k Γ ν →+ GalleryAlgebra k Γ ν :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change v (∑ C : RankIncident (Γ := Γ) p, rankE k C.2.1) = _
  rw [map_sum]
  rfl

theorem isIdempotentElem_starIdemW (p : Strand ν → 𝕜) :
    IsIdempotentElem (starIdemW (Γ := Γ) (k := k) p) := by
  classical
  apply Subtype.ext
  change (starIdemW (Γ := Γ) (k := k) p).1 * (starIdemW (Γ := Γ) (k := k) p).1 = _
  rw [starIdemW_val]
  simp [Finset.sum_mul, Finset.mul_sum, e_mul_e, Subtype.val_injective.eq_iff]

theorem starIdemW_mul_rankE (p : Strand ν → 𝕜) {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hp : C.Incident p) :
    starIdemW (Γ := Γ) (k := k) p * rankE k hC = rankE k hC := by
  classical
  let D : RankIncident (Γ := Γ) p := ⟨C, hC, hp⟩
  apply Subtype.ext
  change (starIdemW (Γ := Γ) (k := k) p).1 * e D.1 = e D.1
  rw [starIdemW_val, Finset.sum_mul]
  simp [e_mul_e, Subtype.val_injective.eq_iff]

theorem rankE_mul_starIdemW (p : Strand ν → 𝕜) {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hp : C.Incident p) :
    rankE k hC * starIdemW (Γ := Γ) (k := k) p = rankE k hC := by
  classical
  let D : RankIncident (Γ := Γ) p := ⟨C, hC, hp⟩
  apply Subtype.ext
  change e D.1 * (starIdemW (Γ := Γ) (k := k) p).1 = e D.1
  rw [starIdemW_val, Finset.mul_sum]
  simp [e_mul_e, Subtype.val_injective.eq_iff]

private theorem rankIdem_mul_poly (f : PolyRing ν k) :
    rankIdem k Γ ν * poly f = poly f * rankIdem k Γ ν := by
  classical
  simp only [rankIdem, Finset.sum_mul, Finset.mul_sum, e_mul_poly]

/-- A labelled dot acts by its polynomial on every element of the rank-ordered
corner; no uniqueness assumption on its colour is needed. -/
theorem reducedDot_mul_val (s : Strand ν) (x : WeightedKLRAlgebra k Γ ν) :
    (reducedDot k Γ ν s * x).1 = poly (X s) * x.1 := by
  have hx := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1 x.2
  change rankIdem k Γ ν * poly (X s) * rankIdem k Γ ν * x.1 = _
  rw [rankIdem_mul_poly, mul_assoc, hx.1, mul_assoc, hx.1]

/-- Chamber selection commutes with every labelled dot. -/
theorem reducedDot_commute_starIdemW (p : Strand ν → 𝕜) (s : Strand ν) :
    Commute (reducedDot k Γ ν s) (starIdemW (Γ := Γ) p) := by
  apply Subtype.ext
  rw [reducedDot_mul_val]
  change poly (X s) * (starIdemW (Γ := Γ) (k := k) p).1 =
    (starIdemW (Γ := Γ) (k := k) p).1 *
      (rankIdem k Γ ν * poly (X s) * rankIdem k Γ ν)
  have hs := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1
    (starIdemW (Γ := Γ) (k := k) p).2
  have he : poly (X s) * (starIdemW (Γ := Γ) (k := k) p).1 =
      (starIdemW (Γ := Γ) (k := k) p).1 * poly (X s) := by
    classical
    rw [starIdemW_val]
    simp only [Finset.sum_mul, Finset.mul_sum, e_mul_poly]
  simp only [← mul_assoc, hs.2]
  rw [← he, mul_assoc, hs.2]

/-- At a weakly rank-ordered base configuration, the local chamber is rank
ordered exactly when its original chamber is rank ordered. -/
theorem chamber_isRankOrdered_iff (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (C : FullChamber (graph Γ p) (weight p)) :
    (chamber p C).IsRankOrdered ↔ C.IsRankOrdered := by
  constructor
  · intro hC d
    rw [← chamber_hyp p C (.inr d)]
    exact hC (diag p d)
  · intro hC d
    by_cases hd : d.val p = 0
    · rw [← diag_diagOfZero p d hd]
      exact (chamber_hyp p C (.inr (diagOfZero p d hd))).trans (hC _)
    · exact ((chamber_incident p C).sign_eq (.inr d) hd).trans
        (decide_eq_true (lt_of_le_of_ne (hp d) (Ne.symm hd)))

/-- The rank-ordered local chambers are exactly the incident rank-ordered
original chambers when the base configuration is weakly rank ordered. -/
def rankChamberEquiv (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p) :
    {C : FullChamber (graph Γ p) (weight p) // C.IsRankOrdered} ≃
      RankIncident (Γ := Γ) p where
  toFun C := ⟨chamber p C.1, (chamber_isRankOrdered_iff p hp C.1).2 C.2,
    chamber_incident p C.1⟩
  invFun C := ⟨(linearization Γ p).localChamber C.1,
    (chamber_isRankOrdered_iff p hp _).1 (by
      change ((linearization Γ p).chamber ((linearization Γ p).localChamber C.1)).IsRankOrdered
      rw [(linearization Γ p).chamber_localChamber C.1 C.2.2]
      exact C.2.1)⟩
  left_inv C := Subtype.ext ((linearization Γ p).localChamber_chamber C.1)
  right_inv C := Subtype.ext ((linearization Γ p).chamber_localChamber C.1 C.2.2)

/-- A map with the local chart's chamber images sends the local rank idempotent
to the incident original rank idempotent. -/
theorem map_rankIdem_eq_starIdemW (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C)) :
    φ (rankIdem k (graph Γ p) (weight p)) = (starIdemW (Γ := Γ) (k := k) p).1 := by
  classical
  calc
    φ (rankIdem k (graph Γ p) (weight p)) =
        ∑ C ∈ Finset.univ.filter FullChamber.IsRankOrdered, e (chamber p C) := by
      simp only [rankIdem, map_sum, he]
    _ = ∑ C : {C : FullChamber (graph Γ p) (weight p) // C.IsRankOrdered},
        e (chamber p C.1) := Finset.sum_subtype _ (by simp) _
    _ = ∑ C : RankIncident (Γ := Γ) p, e C.1 :=
      (rankChamberEquiv p hp).sum_comp (fun C => e C.1)
    _ = (starIdemW (Γ := Γ) (k := k) p).1 := (starIdemW_val p).symm

/-- Restrict a chart with the prescribed chamber images to Webster's corners.
The chamber-image hypothesis is an explicit hypothesis of this intermediate
construction; the concrete chart discharges it below. -/
def weightedHomOfChart (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C)) :
    WeightedKLRAlgebra k (graph Γ p) (weight p) →ₙ+* WeightedKLRAlgebra k Γ ν :=
  cornerRestrict φ isIdempotentElem_rankIdem isIdempotentElem_rankIdem (by
    rw [map_rankIdem_eq_starIdemW p hp φ he]
    exact (starIdemW (Γ := Γ) (k := k) p).2)

@[simp] theorem weightedHomOfChart_val (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (x : WeightedKLRAlgebra k (graph Γ p) (weight p)) :
    (weightedHomOfChart p hp φ he x).1 = φ x.1 := rfl

@[simp] theorem weightedHomOfChart_one (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C)) :
    weightedHomOfChart p hp φ he 1 = starIdemW (Γ := Γ) (k := k) p :=
  Subtype.ext (map_rankIdem_eq_starIdemW p hp φ he)

@[simp] theorem weightedHomOfChart_rankE (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    {C : FullChamber (graph Γ p) (weight p)} (hC : C.IsRankOrdered) :
    weightedHomOfChart p hp φ he (rankE k hC) =
      rankE k ((chamber_isRankOrdered_iff p hp C).2 hC) := Subtype.ext (he C)

theorem weightedHomOfChart_map_smul (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (hsmul : ∀ (c : k) (a), φ (c • a) = c • φ a)
    (c : k) (x : WeightedKLRAlgebra k (graph Γ p) (weight p)) :
    weightedHomOfChart p hp φ he (c • x) = c • weightedHomOfChart p hp φ he x :=
  Subtype.ext (hsmul c x.1)

/-- The linear form of the restricted chart, used to describe the image of its
action on a module. -/
def weightedLinearMapOfChart (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (hsmul : ∀ (c : k) (a), φ (c • a) = c • φ a) :
    WeightedKLRAlgebra k (graph Γ p) (weight p) →ₗ[k] WeightedKLRAlgebra k Γ ν where
  toFun := weightedHomOfChart p hp φ he
  map_add' := map_add _
  map_smul' := weightedHomOfChart_map_smul p hp φ he hsmul

/-- The local dot maps to the corresponding original dot followed by the star
idempotent. Polynomial compatibility is an explicit hypothesis of this
intermediate construction; the concrete chart discharges it below. -/
theorem weightedHomOfChart_reducedDot (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (hpoly : ∀ f, φ (poly f) = poly (rename (strandEquiv p) f) * φ 1)
    (s : Strand (weight p)) :
    weightedHomOfChart p hp φ he (reducedDot k (graph Γ p) (weight p) s) =
      reducedDot k Γ ν (strandEquiv p s) * starIdemW (Γ := Γ) (k := k) p := by
  apply Subtype.ext
  rw [weightedHomOfChart_val, reducedDot_mul_val]
  change φ (rankIdem k (graph Γ p) (weight p) * poly (X s) *
    rankIdem k (graph Γ p) (weight p)) = _
  rw [rankIdem_mul_poly, mul_assoc, isIdempotentElem_rankIdem.eq, map_mul,
    hpoly, rename_X, mul_assoc]
  have hu : φ 1 * φ (rankIdem k (graph Γ p) (weight p)) =
      φ (rankIdem k (graph Γ p) (weight p)) := by rw [← map_mul, one_mul]
  rw [hu, map_rankIdem_eq_starIdemW p hp φ he]

/-- A full-gallery preimage becomes a preimage in the weighted corner after
sandwiching by the local rank idempotent, provided the target is supported on
the rank-ordered chamber star. -/
theorem weightedHomOfChart_cornerProjection_eq (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (φ : GalleryAlgebra k (graph Γ p) (weight p) →ₙ+* GalleryAlgebra k Γ ν)
    (he : ∀ C, φ (e C) = e (chamber p C))
    (b : GalleryAlgebra k (graph Γ p) (weight p)) (a : WeightedKLRAlgebra k Γ ν)
    (hb : φ b = a.1)
    (ha : starIdemW (Γ := Γ) (k := k) p * a * starIdemW (Γ := Γ) p = a) :
    weightedHomOfChart p hp φ he (colourSymCornerProjection b) = a := by
  apply Subtype.ext
  change φ (rankIdem k (graph Γ p) (weight p) * b *
    rankIdem k (graph Γ p) (weight p)) = a.1
  rw [map_mul, map_mul, map_rankIdem_eq_starIdemW p hp φ he, hb]
  exact congrArg Subtype.val ha

/-- The local chart on Webster's weighted algebras, at a weakly rank-ordered
configuration. Its unit image is the sum of the incident rank-ordered chambers. -/
def weightedHom (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    WeightedKLRAlgebra k (graph Γ p) (weight p) →ₙ+* WeightedKLRAlgebra k Γ ν :=
  weightedHomOfChart p hp (galleryVal p hD hZ hS) (galleryVal_e p hD hZ hS)

@[simp] theorem weightedHom_val (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (x : WeightedKLRAlgebra k (graph Γ p) (weight p)) :
    (weightedHom p hp hD hZ hS x).1 = (galleryHom p hD hZ hS x.1).1 := rfl

@[simp] theorem weightedHom_one (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    weightedHom p hp hD hZ hS 1 = starIdemW (Γ := Γ) (k := k) p :=
  weightedHomOfChart_one p hp _ _

@[simp] theorem weightedHom_rankE (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {C : FullChamber (graph Γ p) (weight p)} (hC : C.IsRankOrdered) :
    weightedHom p hp hD hZ hS (rankE k hC) =
      rankE k ((chamber_isRankOrdered_iff p hp C).2 hC) :=
  weightedHomOfChart_rankE p hp _ _ hC

theorem weightedHom_map_smul (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (c : k)
    (x : WeightedKLRAlgebra k (graph Γ p) (weight p)) :
    weightedHom p hp hD hZ hS (c • x) = c • weightedHom p hp hD hZ hS x :=
  weightedHomOfChart_map_smul p hp _ _ (galleryVal_map_smul p hD hZ hS) c x

/-- The local weighted chart, in the linear form used for its action image. -/
def weightedLinearMap (p : Strand ν → 𝕜) (hp : ∀ d : Diag ν, 0 ≤ d.val p)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    WeightedKLRAlgebra k (graph Γ p) (weight p) →ₗ[k] WeightedKLRAlgebra k Γ ν :=
  weightedLinearMapOfChart p hp (galleryVal p hD hZ hS) (galleryVal_e p hD hZ hS)
    (galleryVal_map_smul p hD hZ hS)

@[simp] theorem weightedLinearMap_apply (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (x : WeightedKLRAlgebra k (graph Γ p) (weight p)) :
    weightedLinearMap p hp hD hZ hS x = weightedHom p hp hD hZ hS x := rfl

/-- A local labelled dot maps to the original labelled dot times the weighted
star idempotent. This supplies dot nilpotence on the local restriction. -/
theorem weightedHom_reducedDot (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (s : Strand (weight p)) :
    weightedHom p hp hD hZ hS (reducedDot k (graph Γ p) (weight p) s) =
      reducedDot k Γ ν (strandEquiv p s) * starIdemW (Γ := Γ) (k := k) p :=
  weightedHomOfChart_reducedDot p hp _ _ (galleryVal_poly p hD hZ hS) s

/-- Full-gallery preimages of weighted star-corner elements descend to weighted
preimages by applying the local rank-corner projection. -/
theorem weightedLinearMap_cornerProjection_eq (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (b : GalleryAlgebra k (graph Γ p) (weight p))
    (a : WeightedKLRAlgebra k Γ ν) (hb : (galleryHom p hD hZ hS b).1 = a.1)
    (ha : starIdemW (Γ := Γ) (k := k) p * a * starIdemW (Γ := Γ) p = a) :
    weightedLinearMap p hp hD hZ hS (colourSymCornerProjection b) = a :=
  weightedHomOfChart_cornerProjection_eq p hp (galleryVal p hD hZ hS)
    (galleryVal_e p hD hZ hS) b a hb ha

end WeightedStar

end Categorification.WeightedKLR.Local
