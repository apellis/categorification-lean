/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.CornerShuffle
import Categorification.WeightedKLR.Mackey.Parabolic
import Categorification.WeightedKLR.Mackey.Subquotient

/-!
# The subquotients of the Mackey filtration are spanned by `ι(x) ψ^W_g ι(y)`

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Webster identifies each subquotient of the filtration of
`e D * W_ν * e C` by shuffle types with a module induced from `W_{ν₁} ⊗ W_{ν₂}` and
`W_{ν'} ⊗ W_{ν''}` through the shuffle element. Here the map underlying this identification is
constructed and shown to be surjective.

The shuffle element `ψ^W_g` between rank-ordered chambers (`GalleryAlgebra.rankShuffleElt`) is a
relabelling by `u g v⁻¹`, with `u`, `v` relabellings inside the blocks, followed by a minimal
gallery; it therefore lies in the step of the filtration of every lower set containing the
shuffle type of `g` (`GalleryAlgebra.rankShuffleElt_mem_mackeyFilt`). As the steps are
sub-bimodules for Webster's maps `ι`, the element `e D ι(x) ψ^W_g ι(y) e C` lies in the step
too, which defines a `k`-linear map `GalleryAlgebra.shuffleInductionMap` from
`(W_{ν₁} ⊗ W_{ν₂}) ⊗ (W_{ν'} ⊗ W_{ν''})` to the subquotient. By the factorization
`b(g, m) ≡ ι(x) ψ^W_g ι(y)` (`GalleryAlgebra.exists_cornerBasis_sub_rankShuffleElt_mem`) and
induction on the length of the chosen gallery, the images of these maps, over the relabellings
`g` of shuffle type in `S` but not in `S'`, span the subquotient
(`GalleryAlgebra.iSup_range_shuffleInductionMap`).

## Main definitions

* `GalleryAlgebra.rankShuffleTop`, `GalleryAlgebra.rankShuffleBot`: the rank-ordered ends of
  `ψ^W_g`.
* `GalleryAlgebra.shuffleInductionMap`: `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]` into the subquotient.

## Main results

* `GalleryAlgebra.rankShuffleElt_mem_mackeyFilt`: `ψ^W_g` lies in the step of shuffle types `S`.
* `GalleryAlgebra.iSup_range_shuffleInductionMap`: the maps `shuffleInductionMap` are jointly
  surjective onto the subquotient.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace Juxtapose

omit [DecidableEq I] in
/-- The block sort preserves the strands of the first block. -/
theorem blockSort_mem_leftBlockStab (hν : ν₁ + ν₂ = ν) (E : FullChamber Γ ν) :
    blockSort hν E ∈ leftBlockStab ν ν₁ := by
  subst hν
  exact colPermProd_mem_leftBlockStab _

end Juxtapose

namespace GalleryAlgebra

/-- The top end `u • g • shuffleTop Y C` of `ψ^W_g`, rank-ordered. -/
noncomputable def rankShuffleTop (hν₁ : ν₁ + ν₂ = ν) (g : ColPerm ν) (C : FullChamber Γ ν) :
    FullChamber Γ ν :=
  blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
    g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C

/-- The bottom end `v • shuffleBot X Y C` of `ψ^W_g`, rank-ordered. -/
noncomputable def rankShuffleBot (hν' : ν' + ν'' = ν) (ν₁ : I →₀ ℕ) (g : ColPerm ν)
    (C : FullChamber Γ ν) : FullChamber Γ ν :=
  blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁))
      C) •
    shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C

theorem isRankOrdered_rankShuffleTop (hν₁ : ν₁ + ν₂ = ν) (g : ColPerm ν)
    (C : FullChamber Γ ν) : (rankShuffleTop hν₁ g C).IsRankOrdered :=
  (blockSort_spec (k := k) hν₁ (isSeparated_smul_shuffleTop g C)).1

theorem isRankOrdered_rankShuffleBot (hν' : ν' + ν'' = ν) (ν₁ : I →₀ ℕ) (g : ColPerm ν)
    (C : FullChamber Γ ν) : (rankShuffleBot hν' ν₁ g C).IsRankOrdered :=
  (blockSort_spec (k := k) hν' (isSeparated_shuffleBot (fun t => decide ((g.1 t).IsLeft ν₁))
    C)).1

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **The shuffle element lies in the filtration.** For a lower set `S` of shuffle types
containing that of `g`, `ψ^W_g` lies in the step `S` of the filtration of
`e (rankShuffleTop) * A * e (rankShuffleBot)`: it is the relabelling `u g v⁻¹`, of the same
shuffle type as `g`, after a minimal gallery. -/
theorem rankShuffleElt_mem_mackeyFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S)
    (C : FullChamber Γ ν) :
    rankShuffleElt k hν' hν₁ hD hZ g C ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ (rankShuffleTop hν₁ g C)
        (rankShuffleBot hν' ν₁ g C) S := by
  set Y : Strand ν → Bool := fun t => decide ((g.1 t).IsLeft ν₁)
  set X : Strand ν → Bool := fun t => decide (t.IsLeft ν')
  set T := shuffleTop Y C
  set F := shuffleBot X Y C
  set u := blockSort hν₁ (g • T)
  set v := blockSort hν' F
  set w := shuffleWord hD hZ X Y C
  have hw := goodWord_shuffleWord hD hZ X Y C
  have hfw : F.flips w = T := flips_shuffleWord hD hZ X Y C
  obtain ⟨h1, h2, h3⟩ := goodWord_smul (k := k) v hw
  rw [hfw] at h2 h3
  have hT : e T * galList k F w = galList k F w := by
    conv_lhs => rw [← hfw]
    exact e_mul_galList _ _
  have h4 : galList k F w * r v⁻¹ (v • F) =
      r v⁻¹ (v • T) * galList k (v • F) (w.map (Hyp.comap v⁻¹)) := by
    have := congrArg (fun z => r v⁻¹ (v • T) * z * r v⁻¹ (v • F)) h3
    simp only [mul_assoc] at this
    rw [r_mul_r_eq v F v⁻¹ (v • F), ite_eq_left (inv_smul_smul v F).symm, mul_inv_cancel, r_one,
      galList_mul_e, ← mul_assoc (r v⁻¹ (v • T)) (r v T), r_mul_r_eq, ite_eq_left rfl,
      inv_mul_cancel, r_one, ← mul_assoc, hT] at this
    exact this.symm
  have hψ : rankShuffleElt k hν' hν₁ hD hZ g C =
      r (u * g * v⁻¹) (v • T) * galList k (v • F) (w.map (Hyp.comap v⁻¹)) := by
    rw [rankShuffleElt, shuffleElt]
    change r u (g • T) * (r g T * galList k F w) * r v⁻¹ (v • F) = _
    rw [← mul_assoc, r_mul_r, mul_assoc, h4, ← mul_assoc, r_mul_r_eq,
      ite_eq_left (inv_smul_smul v T).symm]
  have hsmul : (u * g * v⁻¹)⁻¹ • rankShuffleTop hν₁ g C = v • T := by
    change (u * g * v⁻¹)⁻¹ • u • g • T = v • T
    simp [mul_smul]
  have htype : shuffleType ν' ν₁ (u * g * v⁻¹) = shuffleType ν' ν₁ g := by
    have e1 : shuffleType ν' ν₁ (u * g * v⁻¹) = shuffleType ν' ν₁ (g * v⁻¹) := by
      rw [mul_assoc]
      exact shuffleType_mul_of_image_left ν' ν₁
        (image_leftStrands_of_mem (blockSort_mem_leftBlockStab hν₁ _)) _
    have e2 := shuffleType_mul_of_image_right ν' ν₁
      (fun i => image_rightStrands_of_mem (blockSort_mem_leftBlockStab hν' F) i) (g * v⁻¹)
    rw [inv_mul_cancel_right] at e2
    rw [e1, ← e2]
  have hmem := r_mul_galList_mul_mem_mackeyFilt hP hD hZ hΓ hW hL ν' ν₁
    (isRankOrdered_rankShuffleBot (k := k) hν' ν₁ g C)
    (isRankOrdered_rankShuffleTop (k := k) hν₁ g C) hS (htype ▸ hg) h1
    (h2.trans hsmul.symm) 0
  rw [hsmul, monomial_zero', C_1, show (poly 1 : GalleryAlgebra k Γ ν) = polyHom k Γ ν 1 from rfl,
    map_one, mul_one] at hmem
  rw [hψ]
  exact hmem

theorem cornerBasis_mem_mackeyFilt (D C : FullChamber Γ ν) {S : Set (I → ℕ)}
    {i : ColPerm ν × (Strand ν →₀ ℕ)} (hi : shuffleType ν' ν₁ i.1 ∈ S) :
    (cornerBasis hP hD hZ hΓ hW hL D C i : GalleryAlgebra k Γ ν) ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

variable (k) in
/-- Webster's map `ι`, followed by the identification `ν₁ + ν₂ = ν`, as a `k`-linear map into
the gallery algebra. -/
noncomputable def inductionVal (hν : ν₁ + ν₂ = ν) :
    WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂ →ₗ[k] GalleryAlgebra k Γ ν where
  toFun x := castGallery k Γ hν (inductionMap k Γ ν₁ ν₂ x).1
  map_add' a b := by rw [map_add]; exact map_add (castGallery k Γ hν) _ _
  map_smul' c a := by rw [map_smul]; exact map_smul (castGallery k Γ hν) c _

theorem inductionVal_apply (hν : ν₁ + ν₂ = ν)
    (x : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) :
    inductionVal k hν x = castGallery k Γ hν (inductionMap k Γ ν₁ ν₂ x).1 := rfl

variable (k) in
/-- `x ⊗ y ↦ e D ι(x) ψ^W_g ι(y) e C`, as a map into the gallery algebra. -/
noncomputable def shuffleInductionAux (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (D C : FullChamber Γ ν) (g : ColPerm ν) :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') →ₗ[k]
      GalleryAlgebra k Γ ν :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun x y => e D * inductionVal k hν₁ x * rankShuffleElt k hν' hν₁ hD hZ g C *
      inductionVal k hν' y * e C)
    (fun a b y => by simp only [map_add, mul_add, add_mul])
    (fun c a y => by simp only [map_smul, mul_smul_comm, smul_mul_assoc])
    (fun x a b => by simp only [map_add, mul_add, add_mul])
    (fun c x a => by simp only [map_smul, mul_smul_comm, smul_mul_assoc])

theorem shuffleInductionAux_tmul (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (D C : FullChamber Γ ν) (g : ColPerm ν)
    (x : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    shuffleInductionAux k hD hZ hν' hν₁ D C g (x ⊗ₜ y) =
      e D * castGallery k Γ hν₁ (inductionMap k Γ ν₁ ν₂ x).1 *
        rankShuffleElt k hν' hν₁ hD hZ g C * castGallery k Γ hν' (inductionMap k Γ ν' ν'' y).1 *
        e C := rfl

theorem shuffleInductionAux_mem_mackeyFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S)
    (z : (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')) :
    shuffleInductionAux k hD hZ hν' hν₁ D C g z ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [shuffleInductionAux_tmul]
    exact inductionMap_mul_mul_mem_mackeyFilt hP hD hZ hΓ hW hL hν₁ hν'
      (isRankOrdered_rankShuffleBot (k := k) hν' ν₁ g C) hC
      (isRankOrdered_rankShuffleTop (k := k) hν₁ g C) hD' hS x y
      (rankShuffleElt_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hS hg C)
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb

variable (k) in
/-- **The map to the subquotient.** For `g` of shuffle type in the lower set `S`, the `k`-linear
map `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]` from `(W_{ν₁} ⊗ W_{ν₂}) ⊗ (W_{ν'} ⊗ W_{ν''})` to the
quotient of the step `S` of the filtration of `e D * A * e C` by the step `S'`. -/
noncomputable def shuffleInductionMap (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (S' : Set (I → ℕ)) {S : Set (I → ℕ)} (hS : IsLowerSet S) {g : ColPerm ν}
    (hg : shuffleType ν' ν₁ g ∈ S) :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (shuffleInductionAux k hD hZ hν' hν₁ D C g)
    (shuffleInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hC hD' hS hg)

theorem shuffleInductionMap_apply (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (S' : Set (I → ℕ)) {S : Set (I → ℕ)} (hS : IsLowerSet S) {g : ColPerm ν}
    (hg : shuffleType ν' ν₁ g ∈ S)
    (z : (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')) :
    shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hg z =
      Submodule.Quotient.mk ⟨shuffleInductionAux k hD hZ hν' hν₁ D C g z,
        shuffleInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hC hD' hS hg z⟩ := rfl

/-- **The subquotients are spanned by the images of the shuffle elements** (the surjectivity
half of the identification of the subquotients of the Mackey filtration with induced modules in
the proof of B. Webster, arXiv:1209.2463v4, Theorem 2.19). Let `C`, `D` be rank-ordered, with the
strands of `ν'` to the left in `C` and those of `ν₁` to the left in `D`, and let `S` be a lower
set of shuffle types. The quotient of the step `S` of the filtration of `e D * A * e C` by the
step `S'` is the sum of the images of the maps `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]`, over the
relabellings `g` of shuffle type in `S` but not in `S'`. -/
theorem iSup_range_shuffleInductionMap (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) (S' : Set (I → ℕ)) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) :
    ⨆ g : {g : ColPerm ν // shuffleType ν' ν₁ g ∈ S ∧ shuffleType ν' ν₁ g ∉ S'},
        LinearMap.range (shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS g.2.1) =
      ⊤ := by
  set T := ⨆ g : {g : ColPerm ν // shuffleType ν' ν₁ g ∈ S ∧ shuffleType ν' ν₁ g ∉ S'},
    LinearMap.range (shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS g.2.1)
  set M := mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S
  set N := (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S').comap M.subtype
  have key : ∀ n (h : ColPerm ν) (m : Strand ν →₀ ℕ) (hh : shuffleType ν' ν₁ h ∈ S),
      segLength P C (h⁻¹ • D) = n →
      N.mkQ ⟨cornerBasis hP hD hZ hΓ hW hL D C (h, m),
        cornerBasis_mem_mackeyFilt hP hD hZ hΓ hW hL D C (i := (h, m)) hh⟩ ∈ T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro h m hh hn
    by_cases hh' : shuffleType ν' ν₁ h ∈ S'
    · rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2]
      · exact T.zero_mem
      · exact cornerBasis_mem_mackeyFilt hP hD hZ hΓ hW hL D C (i := (h, m)) hh'
    set L := Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
      shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (h⁻¹ • D)} =>
        (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν))
    have hLM : L ≤ M := Submodule.span_le.2 <| by
      rintro _ ⟨i, rfl⟩
      exact cornerBasis_mem_mackeyFilt hP hD hZ hΓ hW hL D C i.2.1
    have hLC : L ≤ cornerSpace k D C :=
      hLM.trans (mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C S)
    have hLT : ∀ ℓ ∈ L, ∀ hℓ : ℓ ∈ M, N.mkQ ⟨ℓ, hℓ⟩ ∈ T := by
      intro ℓ hℓ
      induction hℓ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro _
        exact ih _ (hn ▸ i.2.2) i.1.1 i.1.2 i.2.1 rfl
      | zero =>
        intro _
        exact T.zero_mem
      | add x y hx hy ihx ihy =>
        intro _
        have := add_mem (ihx (hLM hx)) (ihy (hLM hy))
        rwa [← map_add] at this
      | smul c x hx ihx =>
        intro _
        have := Submodule.smul_mem T c (ihx (hLM hx))
        rwa [← map_smul] at this
    obtain ⟨x, y, hxy⟩ := exists_cornerBasis_sub_rankShuffleElt_mem hP hD hZ hΓ hW hL hν' hν₁ hC
      hD' hCs hDs hS hh m
    set b := (cornerBasis hP hD hZ hΓ hW hL D C (h, m) : GalleryAlgebra k Γ ν)
    have hb : e D * b * e C = b := mem_cornerSpace_iff.1 (cornerBasis hP hD hZ hΓ hW hL D C _).2
    have hdiff : shuffleInductionAux k hD hZ hν' hν₁ D C h (x ⊗ₜ y) - b ∈ L := by
      have := mem_cornerSpace_iff.1 (hLC hxy)
      rw [shuffleInductionAux_tmul]
      convert hxy using 1
      rw [← this, mul_sub, sub_mul, hb]
      simp only [mul_assoc]
    have hmem := shuffleInductionAux_mem_mackeyFilt hP hD hZ hΓ hW hL hν' hν₁ hC hD' hS hh
      (x ⊗ₜ y)
    have hsplit : (⟨b, cornerBasis_mem_mackeyFilt hP hD hZ hΓ hW hL D C (i := (h, m)) hh⟩ : M) =
        ⟨_, hmem⟩ - ⟨_, hLM hdiff⟩ := Subtype.ext (sub_sub_cancel _ _).symm
    rw [hsplit, map_sub]
    refine sub_mem ?_ (hLT _ hdiff _)
    refine (le_iSup (fun g : {g : ColPerm ν // shuffleType ν' ν₁ g ∈ S ∧
      shuffleType ν' ν₁ g ∉ S'} => LinearMap.range
        (shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS g.2.1)) ⟨h, hh, hh'⟩) ?_
    exact ⟨x ⊗ₜ y, rfl⟩
  have hgen : ∀ i, N.mkQ (mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S i) ∈ T := fun i => by
    have e1 : mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S i =
        ⟨cornerBasis hP hD hZ hΓ hW hL D C (i.1.1, i.1.2),
          cornerBasis_mem_mackeyFilt hP hD hZ hΓ hW hL D C (i := (i.1.1, i.1.2)) i.2⟩ :=
      Subtype.ext (mackeyFiltBasis_apply hP hD hZ hΓ hW hL ν' ν₁ D C S i)
    rw [e1]
    exact key _ i.1.1 i.1.2 i.2 rfl
  have hall : ∀ z : M, N.mkQ z ∈ T := fun z => by
    have hz : z ∈ Submodule.span k (Set.range (mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S)) :=
      by rw [Module.Basis.span_eq]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hgen i
    | zero => rw [map_zero]; exact T.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact T.smul_mem c hx
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨z, rfl⟩ := N.mkQ_surjective q
  exact hall z

end GalleryAlgebra

end Categorification.WeightedKLR
