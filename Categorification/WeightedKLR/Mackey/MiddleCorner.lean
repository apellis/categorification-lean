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
namespace Juxtapose

variable {a b c d : I →₀ ℕ}

section CornerMap

variable (zL : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
  (zR : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))

/-- Left multiplication by `z_L` on `MiddleTop`. -/
noncomputable def middleTopMulLeft : MiddleTop k Γ a b c d →ₗ[k] MiddleTop k Γ a b c d where
  toFun t := zL • t
  map_add' := smul_add zL
  map_smul' r t := Subtype.ext (by
    show zL * (r • t.1) = r • (zL * t.1)
    exact mul_smul_comm r zL t.1)

/-- Right multiplication by `z_R` on `MiddleBot`. -/
noncomputable def middleBotMulRight : MiddleBot k Γ a b c d →ₗ[k] MiddleBot k Γ a b c d where
  toFun y := ⟨y.1 * zR, by rw [mem_middleBotSub, ← mul_assoc, mem_middleBotSub.1 y.2]⟩
  map_add' y y' := Subtype.ext (add_mul _ _ _)
  map_smul' r y := Subtype.ext (smul_mul_assoc _ _ _)

theorem middleTopMulLeft_apply (t : MiddleTop k Γ a b c d) : middleTopMulLeft zL t = zL • t :=
  rfl

theorem coe_middleBotMulRight (y : MiddleBot k Γ a b c d) :
    (middleBotMulRight zR y :
      WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) = y.1 * zR := rfl

theorem middleBotMulRight_smul (w : MiddleAlg k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleBotMulRight zR (w • y) = w • middleBotMulRight zR y :=
  Subtype.ext (mul_assoc _ _ _)

/-- The corner map `t ⊗ y ↦ z_L t ⊗ y z_R` of `MiddleTensor`. For `z_L = e L' ⊗ e L''` and
`z_R = e R' ⊗ e R''` its range is the juxtaposed corner, which the descended map
`middleTensorMap` sends to the corner of `chamber L' L''` and `chamber R' R''` of the Mackey
subquotient (`Juxtapose.middleTensorMap_tmul_corner`). -/
noncomputable def middleCornerMap : MiddleTensor k Γ a b c d →ₗ[k] MiddleTensor k Γ a b c d :=
  BalancedTensor.lift ((BalancedTensor.mkBil k _ _ _ _).compl₁₂ (middleTopMulLeft zL)
    (middleBotMulRight zR)) fun t w y => by
    simp only [LinearMap.compl₁₂_apply, BalancedTensor.mkBil_apply, middleTopMulLeft_apply,
      middleBotMulRight_smul]
    rw [← BalancedTensor.op_smul_tmul, smul_comm zL (op w) t]

theorem middleCornerMap_tmul (t : MiddleTop k Γ a b c d) (y : MiddleBot k Γ a b c d) :
    middleCornerMap zL zR (BalancedTensor.tmul t y) =
      BalancedTensor.tmul (zL • t) (middleBotMulRight zR y) := rfl

end CornerMap

/-- `x ⊗ y` lies in `MiddleBot` if `x`, `y` lie under juxtapositions of rank-ordered chambers. -/
theorem tmul_mem_middleBotSub {X' : FullChamber Γ a} {X'' : FullChamber Γ b}
    {Y' : FullChamber Γ c} {Y'' : FullChamber Γ d} (hX : (chamber X' X'').IsRankOrdered)
    (hY : (chamber Y' Y'').IsRankOrdered) {x : WeightedKLRAlgebra k Γ (a + b)}
    {y : WeightedKLRAlgebra k Γ (c + d)} (hx : rankE k hX * x = x) (hy : rankE k hY * y = y) :
    x ⊗ₜ y ∈ middleBotSub k Γ a b c d := by
  rw [mem_middleBotSub, middleBot_one, Algebra.TensorProduct.tmul_mul_tmul,
    inductionMap_one_mul hX hx, inductionMap_one_mul hY hy]

variable {L' : FullChamber Γ (a + c)} {L'' : FullChamber Γ (b + d)}

omit [DecidableEq I] in
theorem isRankOrdered_botLeft (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    (chamber (repLeft u₁) (repLeft u₂)).IsRankOrdered :=
  (isRankOrdered_chamber_iff _ _).2 ⟨isRankOrdered_repLeft u₁, isRankOrdered_repLeft u₂⟩

omit [DecidableEq I] in
theorem isRankOrdered_botRight (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    (chamber (repRight u₁) (repRight u₂)).IsRankOrdered :=
  (isRankOrdered_chamber_iff _ _).2 ⟨isRankOrdered_repRight u₁, isRankOrdered_repRight u₂⟩

variable (Γ L' L'') in
/-- The index set of the spanning family of the juxtaposed corner: representatives `u₁`, `u₂`
for `L'` and `L''`, and indices of the corner bases for `a + b` and `c + d`. -/
abbrev MiddleCornerIdx : Type _ :=
  (ParabolicRep a L' × ParabolicRep b L'') ×
    ((ColPerm (a + b) × (Strand (a + b) →₀ ℕ)) × (ColPerm (c + d) × (Strand (c + d) →₀ ℕ)))

variable {R' : FullChamber Γ (a + b)} {R'' : FullChamber Γ (c + d)}
  {P₃ : FullChamber Γ (a + b) → FullChamber Γ (a + b) →
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
  (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered) (hR' : R'.IsRankOrdered)
  (hR'' : R''.IsRankOrdered)

/-- The bottom factor `b₁ ⊗ b₂` of a vector of the spanning family. -/
noncomputable def middleCornerBot (i : MiddleCornerIdx Γ L' L'') : MiddleBot k Γ a b c d :=
  ⟨cornerW k (isRankOrdered_botLeft i.1.1 i.1.2) hR'
      (cornerBasis hP₃ hD hZ hΓ hW₃ hL₃ _ R' i.2.1) ⊗ₜ
    cornerW k (isRankOrdered_botRight i.1.1 i.1.2) hR''
      (cornerBasis hP₄ hD hZ hΓ hW₄ hL₄ _ R'' i.2.2),
    tmul_mem_middleBotSub _ _ (rankE_mul_cornerW _ _ _) (rankE_mul_cornerW _ _ _)⟩

/-- The spanning family of the juxtaposed corner: `(c_{u₁} ⊗ c_{u₂}) ⊗ (b₁ ⊗ b₂)`, `b₁` (resp.
`b₂`) in the corner basis from the juxtaposition of the left (resp. right) restrictions of
`G_{u₁}`, `G_{u₂}` to `R'` (resp. `R''`). -/
noncomputable def middleCornerVec (i : MiddleCornerIdx Γ L' L'') : MiddleTensor k Γ a b c d :=
  BalancedTensor.tmul (middleGen k hD hZ (⟨⟨L', hL'⟩, i.1.1⟩, ⟨⟨L'', hL''⟩, i.1.2⟩))
    (middleCornerBot hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hR' hR'' i)

include hP₃ hP₄ hΓ hW₃ hW₄ hL₃ hL₄ in
/-- The juxtaposed corner part of a generator `(c_{u₁} ⊗ c_{u₂}) ⊗ y z_R` is a combination of the
spanning family. -/
theorem tmul_middleGen_mem_span (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'')
    (y : MiddleBot k Γ a b c d) :
    BalancedTensor.tmul (middleGen k hD hZ (⟨⟨L', hL'⟩, u₁⟩, ⟨⟨L'', hL''⟩, u₂⟩))
        (middleBotMulRight (rankE k hR' ⊗ₜ rankE k hR'') y) ∈
      Submodule.span k (Set.range
        (middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'')) := by
  set g := middleGen k hD hZ (⟨⟨L', hL'⟩, u₁⟩, ⟨⟨L'', hL''⟩, u₂⟩)
  set w : MiddleAlg k Γ a b c d :=
    (rankE k (isRankOrdered_repLeft u₁) ⊗ₜ rankE k (isRankOrdered_repLeft u₂)) ⊗ₜ
      (rankE k (isRankOrdered_repRight u₁) ⊗ₜ rankE k (isRankOrdered_repRight u₂))
  set E := rankE k (isRankOrdered_botLeft u₁ u₂) ⊗ₜ[k] rankE k (isRankOrdered_botRight u₁ u₂)
  have hw : op w • g = g := Subtype.ext (by
    rw [coe_op_smul_middleTop, unop_op, coe_middleGen, middleTop_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    exact congrArg₂ _ (cosetW_mul_inductionMap_rankE hD hZ hL' u₁)
      (cosetW_mul_inductionMap_rankE hD hZ hL'' u₂))
  have hbot : middleBot k Γ a b c d w = E := by
    rw [middleBot_tmul, inductionMap_rankE_tmul_rankE, inductionMap_rankE_tmul_rankE]
  have hE : E * E = E := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, rankE_mul_rankE, rankE_mul_rankE]
  have hEmem : ∀ z, E * z ∈ middleBotSub k Γ a b c d := fun z => by
    rw [← hbot]; exact middleBot_mul_mem w z
  let j : (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) →ₗ[k]
      MiddleBot k Γ a b c d :=
    LinearMap.codRestrict _ (LinearMap.mulLeft k E) hEmem
  let F : (WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) →ₗ[k]
      MiddleTensor k Γ a b c d :=
    { toFun := fun z => BalancedTensor.tmul g (j z)
      map_add' := fun z z' => by rw [map_add, BalancedTensor.tmul_add]
      map_smul' := fun r z => by rw [map_smul, BalancedTensor.tmul_smul]; rfl }
  set q := E * y.1 * (rankE k hR' ⊗ₜ rankE k hR'')
  have hq := tmul_mul_mul_tmul_mem_span hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄
    (isRankOrdered_botLeft u₁ u₂) hR' (isRankOrdered_botRight u₁ u₂) hR'' y.1
  have hFq : BalancedTensor.tmul g (middleBotMulRight (rankE k hR' ⊗ₜ rankE k hR'') y) = F q := by
    rw [← hw, BalancedTensor.op_smul_tmul]
    show _ = BalancedTensor.tmul g (j q)
    congr 1
    refine Subtype.ext ?_
    show middleBot k Γ a b c d w * (y.1 * _) = E * q
    rw [hbot, ← mul_assoc, ← mul_assoc, ← mul_assoc, hE]
  rw [hFq]
  have hmem := Submodule.mem_map_of_mem (f := F) hq
  rw [Submodule.map_span] at hmem
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨((u₁, u₂), i), ?_⟩
  show BalancedTensor.tmul g _ = BalancedTensor.tmul g (j _)
  congr 1
  refine Subtype.ext ?_
  show _ = E * _
  rw [Algebra.TensorProduct.tmul_mul_tmul, rankE_mul_cornerW, rankE_mul_cornerW]
  rfl

variable {P₁ : FullChamber Γ (a + c) → FullChamber Γ (a + c) →
    (Strand (a + c) → 𝕜) × (Strand (a + c) → 𝕜)}
  (hP₁ : ∀ C E, IsChamberSegment C E (P₁ C E))
  {P₂ : FullChamber Γ (b + d) → FullChamber Γ (b + d) →
    (Strand (b + d) → 𝕜) × (Strand (b + d) → 𝕜)}
  (hP₂ : ∀ C E, IsChamberSegment C E (P₂ C E))
  (hW₁ : ∀ w : Wall Γ (a + c), IsRegular (w.factor (k := k)))
  (hW₂ : ∀ w : Wall Γ (b + d), IsRegular (w.factor (k := k)))
  (hL₁ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + c)), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  (hL₂ : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (b + d)), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

include hP₁ hP₂ hW₁ hW₂ hL₁ hL₂ hP₃ hP₄ hΓ hW₃ hW₄ hL₃ hL₄ in
/-- **A spanning family of the juxtaposed corner of the middle parabolic** (Webster,
arXiv:1209.2463v4, Theorem 2.19, injectivity half; after Khovanov–Lauda, arXiv:0803.4121v2, proof
of Proposition 2.18). The corner `(e L' ⊗ e L'') MiddleTensor (e R' ⊗ e R'')`, the range of
`middleCornerMap`, is spanned by the tensors `(c_{u₁} ⊗ c_{u₂}) ⊗ (b₁ ⊗ b₂)`, `u₁`, `u₂`
representatives for `L'`, `L''` and `b₁`, `b₂` in the corner bases of Webster, Theorem 2.8, from
`chamber G'_{u₁} G'_{u₂}` to `R'` and from `chamber G''_{u₁} G''_{u₂}` to `R''`. The hypotheses of
Theorem 2.8 enter for the four weights `a + c`, `b + d`, `a + b` and `c + d`. -/
theorem range_middleCornerMap_le_span :
    LinearMap.range (middleCornerMap (rankE k hL' ⊗ₜ rankE k hL'')
        (rankE k hR' ⊗ₜ rankE k hR'')) ≤
      Submodule.span k (Set.range
        (middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'')) := by
  rw [LinearMap.range_eq_map, ← span_tmul_middleGen_eq_top hP₁ hP₂ hD hZ hΓ hW₁ hW₂ hL₁ hL₂,
    Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨⟨⟨⟨E₁, hE₁⟩, u₁⟩, ⟨⟨E₂, hE₂⟩, u₂⟩⟩, y⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, middleCornerMap_tmul]
  have hval : (((rankE k hL' ⊗ₜ[k] rankE k hL'') •
      middleGen k hD hZ (⟨⟨E₁, hE₁⟩, u₁⟩, ⟨⟨E₂, hE₂⟩, u₂⟩) : MiddleTop k Γ a b c d) :
        WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) =
      (if L' = E₁ then cosetW k hD hZ hE₁ u₁ else 0) ⊗ₜ[k]
        (if L'' = E₂ then cosetW k hD hZ hE₂ u₂ else 0) := by
    rw [Submodule.coe_smul, coe_middleGen, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    exact congrArg₂ _ (rankE_mul_cosetW hD hZ hL' hE₁ u₁) (rankE_mul_cosetW hD hZ hL'' hE₂ u₂)
  by_cases h : L' = E₁ ∧ L'' = E₂
  · obtain ⟨rfl, rfl⟩ := h
    have hg : (rankE k hL' ⊗ₜ[k] rankE k hL'') •
        middleGen k hD hZ (⟨⟨L', hE₁⟩, u₁⟩, ⟨⟨L'', hE₂⟩, u₂⟩) =
        middleGen k hD hZ (⟨⟨L', hE₁⟩, u₁⟩, ⟨⟨L'', hE₂⟩, u₂⟩) :=
      Subtype.ext (by rw [hval, ite_eq_left rfl, ite_eq_left rfl]; rfl)
    rw [hg]
    exact tmul_middleGen_mem_span hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'' u₁ u₂ y
  · have hg : (rankE k hL' ⊗ₜ[k] rankE k hL'') •
        middleGen k hD hZ (⟨⟨E₁, hE₁⟩, u₁⟩, ⟨⟨E₂, hE₂⟩, u₂⟩) = 0 := by
      refine Subtype.ext ?_
      rw [hval]
      rcases not_and_or.1 h with h₁ | h₁ <;> simp [h₁]
    rw [hg, BalancedTensor.zero_tmul]
    exact Submodule.zero_mem _

/-- Each vector of the spanning family lies in the juxtaposed corner. -/
theorem middleCornerVec_mem_range (i : MiddleCornerIdx Γ L' L'') :
    middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'' i ∈
      LinearMap.range (middleCornerMap (rankE k hL' ⊗ₜ rankE k hL'')
        (rankE k hR' ⊗ₜ rankE k hR'')) := by
  refine ⟨middleCornerVec hP₃ hP₄ hD hZ hΓ hW₃ hW₄ hL₃ hL₄ hL' hL'' hR' hR'' i, ?_⟩
  rw [middleCornerVec, middleCornerMap_tmul]
  congr 1
  · refine Subtype.ext ?_
    rw [Submodule.coe_smul, coe_middleGen, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    refine congrArg₂ _ ((rankE_mul_cosetW hD hZ hL' hL' i.1.1).trans (ite_eq_left rfl))
      ((rankE_mul_cosetW hD hZ hL'' hL'' i.1.2).trans (ite_eq_left rfl))
  · refine Subtype.ext ?_
    rw [coe_middleBotMulRight]
    show _ ⊗ₜ _ * _ = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, cornerW_mul_rankE, cornerW_mul_rankE]

end Juxtapose

end Categorification.WeightedKLR
