/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleSpan

/-!
# The juxtaposed corner of the balanced tensor product of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (injectivity half, after Khovanov–Lauda, arXiv:0803.4121v2,
Proposition 2.18). By `Juxtapose.middleTensorMap_tmul_corner`, the descended map
`MiddleTensor → Res ∘ Ind` only sees the corner cut out by `z_L = e L' ⊗ e L''` on the left and
`z_R = e R' ⊗ e R''` on the right. This file defines that corner (`Juxtapose.middleCornerMap`,
whose range it is) and shows that it is spanned by the tensors
`(c_{u₁} ⊗ c_{u₂}) ⊗ (b₁ ⊗ b₂)`, for `u₁`, `u₂` representatives for the chambers `L'`, `L''` and
`b₁`, `b₂` elements of the corner bases of Webster, Theorem 2.8, from the juxtapositions of the
left (resp. right) restrictions of the chambers `u₁⁻¹ • L'`, `u₂⁻¹ • L''` to `R'` (resp. `R''`)
(`Juxtapose.range_middleCornerMap_le_span`).

## Main definitions

* `GalleryAlgebra.rankE`: the idempotent `e C` of a rank-ordered chamber in `W_ν`.
* `GalleryAlgebra.cornerW`: the inclusion of a corner `e D A e C` into `W_ν`, `D`, `C`
  rank-ordered.
* `Juxtapose.middleCornerMap`: `t ⊗ y ↦ z_L t ⊗ y z_R` on `MiddleTensor`.

## Main results

* `GalleryAlgebra.rankE_mul_mul_rankE_mem_span`: `e D x e C` is a combination of the corner basis.
* `Juxtapose.range_middleCornerMap_le_span`: the spanning family of the juxtaposed corner.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

variable {ν : I →₀ ℕ}

/-- The idempotent of a rank-ordered chamber lies in Webster's algebra. -/
theorem e_mem_corner {C : FullChamber Γ ν} (hC : C.IsRankOrdered) :
    (e C : GalleryAlgebra k Γ ν) ∈ Subsemigroup.corner (rankIdem k Γ ν) :=
  (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
    ⟨by rw [rankIdem_mul_e, ite_eq_left hC], by rw [e_mul_rankIdem, ite_eq_left hC]⟩

variable (k) in
/-- The idempotent `e C` of a rank-ordered chamber, as an element of `W_ν`. -/
noncomputable def rankE {C : FullChamber Γ ν} (hC : C.IsRankOrdered) : WeightedKLRAlgebra k Γ ν :=
  ⟨e C, e_mem_corner hC⟩

/-- A corner `e D A e C` between rank-ordered chambers lies in Webster's algebra. -/
theorem cornerSpace_mem_corner {D C : FullChamber Γ ν} (hD : D.IsRankOrdered)
    (hC : C.IsRankOrdered) (x : cornerSpace k D C) :
    (x : GalleryAlgebra k Γ ν) ∈ Subsemigroup.corner (rankIdem k Γ ν) := by
  rw [← mem_cornerSpace_iff.1 x.2]
  refine (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2 ⟨?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, rankIdem_mul_e, ite_eq_left hD]
  · rw [mul_assoc, e_mul_rankIdem, ite_eq_left hC]

variable (k) in
/-- The inclusion of the corner `e D A e C` into Webster's algebra, `D`, `C` rank-ordered. -/
def cornerW {D C : FullChamber Γ ν} (hD : D.IsRankOrdered) (hC : C.IsRankOrdered) :
    cornerSpace k D C →ₗ[k] WeightedKLRAlgebra k Γ ν where
  toFun x := ⟨x, cornerSpace_mem_corner hD hC x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_cornerW {D C : FullChamber Γ ν} (hD : D.IsRankOrdered) (hC : C.IsRankOrdered)
    (x : cornerSpace k D C) : (cornerW k hD hC x).1 = x := rfl

/-- `e D * cornerW x = cornerW x` for `x` in the corner of `D` and `C`. -/
theorem rankE_mul_cornerW {D C : FullChamber Γ ν} (hD : D.IsRankOrdered) (hC : C.IsRankOrdered)
    (x : cornerSpace k D C) : rankE k hD * cornerW k hD hC x = cornerW k hD hC x := by
  refine Subtype.ext ?_
  show e D * (x : GalleryAlgebra k Γ ν) = x
  conv_lhs => rw [← mem_cornerSpace_iff.1 x.2]
  rw [← mul_assoc, ← mul_assoc, e_mul_e, ite_eq_left rfl, mem_cornerSpace_iff.1 x.2]

/-- `cornerW x * e C = cornerW x` for `x` in the corner of `D` and `C`. -/
theorem cornerW_mul_rankE {D C : FullChamber Γ ν} (hD : D.IsRankOrdered) (hC : C.IsRankOrdered)
    (x : cornerSpace k D C) : cornerW k hD hC x * rankE k hC = cornerW k hD hC x := by
  refine Subtype.ext ?_
  show (x : GalleryAlgebra k Γ ν) * e C = x
  conv_lhs => rw [← mem_cornerSpace_iff.1 x.2]
  rw [mul_assoc, e_mul_e, ite_eq_left rfl, mem_cornerSpace_iff.1 x.2]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand ν), Γ.loop s.1 = some Q → s ≠ t →
    s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **`e D x e C` in the corner basis** (Webster, arXiv:1209.2463v4, Theorem 2.8): for `x ∈ W_ν`
and rank-ordered `D`, `C`, `e D x e C` is a combination of the corner basis vectors. -/
theorem rankE_mul_mul_rankE_mem_span {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered)
    (hC' : C.IsRankOrdered) (x : WeightedKLRAlgebra k Γ ν) :
    rankE k hD' * x * rankE k hC' ∈ Submodule.span k (Set.range fun i =>
      cornerW k hD' hC' (cornerBasis hP hD hZ hΓ hW hL D C i)) := by
  have hx : rankE k hD' * x * rankE k hC' =
      cornerW k hD' hC' ⟨e D * x.1 * e C, ⟨x.1, sandwich_apply _ _ _⟩⟩ := Subtype.ext rfl
  rw [hx, Set.range_comp' (cornerW k hD' hC'), Submodule.span_image, Module.Basis.span_eq]
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- `e C e C = e C` in Webster's algebra. -/
theorem rankE_mul_rankE {C : FullChamber Γ ν} (hC : C.IsRankOrdered) :
    rankE k hC * rankE k hC = rankE k hC :=
  Subtype.ext (by show e C * e C = e C; rw [e_mul_e, ite_eq_left rfl])

section TensorCorner

variable {μ μ' : I →₀ ℕ}
  {P₁ : FullChamber Γ μ → FullChamber Γ μ → (Strand μ → 𝕜) × (Strand μ → 𝕜)}
  (hP₁ : ∀ C E, IsChamberSegment C E (P₁ C E))
  {P₂ : FullChamber Γ μ' → FullChamber Γ μ' → (Strand μ' → 𝕜) × (Strand μ' → 𝕜)}
  (hP₂ : ∀ C E, IsChamberSegment C E (P₂ C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW₁ : ∀ w : Wall Γ μ, IsRegular (w.factor (k := k)))
  (hW₂ : ∀ w : Wall Γ μ', IsRegular (w.factor (k := k)))
  (hL₁ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand μ), Γ.loop s.1 = some Q → s ≠ t →
    s.1 = t.1 → IsRegular (loopFactor Q s t))
  (hL₂ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand μ'), Γ.loop s.1 = some Q → s ≠ t →
    s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **Corners of `W_μ ⊗ W_{μ'}` in the tensor corner basis** (Webster, arXiv:1209.2463v4,
Theorem 2.8, for both factors): `(e X ⊗ e Y) y (e X' ⊗ e Y')` is a combination of the tensors of
corner basis vectors. -/
theorem tmul_mul_mul_tmul_mem_span {X X' : FullChamber Γ μ} {Y Y' : FullChamber Γ μ'}
    (hX : X.IsRankOrdered) (hX' : X'.IsRankOrdered) (hY : Y.IsRankOrdered)
    (hY' : Y'.IsRankOrdered) (y : WeightedKLRAlgebra k Γ μ ⊗[k] WeightedKLRAlgebra k Γ μ') :
    (rankE k hX ⊗ₜ rankE k hY) * y * (rankE k hX' ⊗ₜ rankE k hY') ∈
      Submodule.span k (Set.range fun i : (ColPerm μ × (Strand μ →₀ ℕ)) ×
          (ColPerm μ' × (Strand μ' →₀ ℕ)) =>
        cornerW k hX hX' (cornerBasis hP₁ hD hZ hΓ hW₁ hL₁ X X' i.1) ⊗ₜ[k]
          cornerW k hY hY' (cornerBasis hP₂ hD hZ hΓ hW₂ hL₂ Y Y' i.2)) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [mul_add, add_mul]; exact Submodule.add_mem _ hy hy'
  | tmul x x' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have h := Submodule.apply_mem_map₂ (TensorProduct.mk k _ _)
      (rankE_mul_mul_rankE_mem_span hP₁ hD hZ hΓ hW₁ hL₁ hX hX' x)
      (rankE_mul_mul_rankE_mem_span hP₂ hD hZ hΓ hW₂ hL₂ hY hY' x')
    rw [Submodule.map₂_span_span] at h
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩

end TensorCorner

section Rep

variable {ν' ν'' : I →₀ ℕ}

/-- `ι(e C' ⊗ e C'') = e (chamber C' C'')`. -/
theorem inductionMap_rankE_tmul_rankE {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered) :
    inductionMap k Γ ν' ν'' (rankE k hC' ⊗ₜ rankE k hC'') =
      rankE k ((isRankOrdered_chamber_iff C' C'').2 ⟨hC', hC''⟩) :=
  Subtype.ext (inductionMap_e_tmul_e hC' hC'')

/-- `ι(1) z = z` if `e (chamber C' C'') z = z`. -/
theorem inductionMap_one_mul {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC : (chamber C' C'').IsRankOrdered) {z : WeightedKLRAlgebra k Γ (ν' + ν'')}
    (hz : rankE k hC * z = z) : inductionMap k Γ ν' ν'' 1 * z = z := by
  have hz' : e (chamber C' C'') * z.1 = z.1 := congrArg Subtype.val hz
  refine Subtype.ext ?_
  show (inductionMap k Γ ν' ν'' 1).1 * z.1 = z.1
  have h := castGallery_splitIdem_mul_e (k := k) (rfl : ν' + ν'' = ν' + ν'') hC
    (isSeparated_chamber C' C'')
  rw [castGallery_rfl] at h
  rw [inductionMap_one, ← hz', ← mul_assoc, h]

variable {D : FullChamber Γ (ν' + ν'')}

/-- The restriction of `G_u = shuffleTop X (u⁻¹ • D)` to the strands of `ν'`. -/
noncomputable def repLeft (u : ParabolicRep ν' D) : FullChamber Γ ν' :=
  (leftEmb ν' ν'').restrict (shuffleTop (fun t => decide (t.IsLeft ν')) (u.1⁻¹ • D))

/-- The restriction of `G_u = shuffleTop X (u⁻¹ • D)` to the strands of `ν''`. -/
noncomputable def repRight (u : ParabolicRep ν' D) : FullChamber Γ ν'' :=
  (rightEmb ν' ν'').restrict (shuffleTop (fun t => decide (t.IsLeft ν')) (u.1⁻¹ • D))

omit [DecidableEq I] in
/-- `G_u` is the juxtaposition of its restrictions. -/
theorem chamber_repLeft_repRight (u : ParabolicRep ν' D) :
    chamber (repLeft u) (repRight u) = shuffleTop (fun t => decide (t.IsLeft ν')) (u.1⁻¹ • D) :=
  (eq_chamber_of_isSeparated (isSeparated_sep _ _ _)).symm

omit [DecidableEq I] in
theorem isRankOrdered_repLeft (u : ParabolicRep ν' D) : (repLeft u).IsRankOrdered := by
  have h := u.2
  rw [← chamber_repLeft_repRight, isRankOrdered_chamber_iff] at h
  exact h.1

omit [DecidableEq I] in
theorem isRankOrdered_repRight (u : ParabolicRep ν' D) : (repRight u).IsRankOrdered := by
  have h := u.2
  rw [← chamber_repLeft_repRight, isRankOrdered_chamber_iff] at h
  exact h.2

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)

/-- `c_u ι(e G'_u ⊗ e G''_u) = c_u`. -/
theorem cosetW_mul_inductionMap_rankE (hD' : D.IsRankOrdered) (u : ParabolicRep ν' D) :
    cosetW k hD hZ hD' u * inductionMap k Γ ν' ν''
      (rankE k (isRankOrdered_repLeft u) ⊗ₜ rankE k (isRankOrdered_repRight u)) =
      cosetW k hD hZ hD' u := by
  rw [inductionMap_rankE_tmul_rankE]
  refine Subtype.ext ?_
  show cosetElt k hD hZ ν' u.1 D * e (chamber (repLeft u) (repRight u)) = _
  rw [chamber_repLeft_repRight, cosetElt_mul_e]
  rfl

/-- `e E c_u` is `c_u` if `E = D` and `0` otherwise. -/
theorem rankE_mul_cosetW {E : FullChamber Γ (ν' + ν'')} (hE : E.IsRankOrdered)
    (hD' : D.IsRankOrdered) (u : ParabolicRep ν' D) :
    rankE k hE * cosetW k hD hZ hD' u = if E = D then cosetW k hD hZ hD' u else 0 := by
  split_ifs with h
  · subst h
    refine Subtype.ext ?_
    show e E * cosetElt k hD hZ ν' u.1 E = cosetElt k hD hZ ν' u.1 E
    rw [cosetElt, ← mul_assoc, e_mul_r, ite_eq_left (smul_inv_smul u.1 E).symm]
  · refine Subtype.ext ?_
    show e E * cosetElt k hD hZ ν' u.1 D = 0
    rw [cosetElt, ← mul_assoc, e_mul_r,
      ite_eq_right_iff.2 fun h' => (h (h'.trans (smul_inv_smul u.1 D))).elim, zero_mul]

end Rep

end GalleryAlgebra

end Categorification.WeightedKLR
