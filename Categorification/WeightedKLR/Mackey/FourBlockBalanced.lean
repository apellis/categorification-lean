/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockJuxtapose

/-!
# The four-block chambers of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. The chambers `(A B)(C D)` of `(a + b) + (c + d)` with
rank-ordered `A, B, C, D` are four-block chambers for the strands of `a + b` and the strands
`middleLeft a b c d` of the blocks `a` and `c`, and the juxtaposed diagrams `(x_a x_b)(x_c x_d)`
relabel strands only within these four blocks. Together with the local conjugacy of the two
layouts, this gives the balancedness of the four-block shuffle for the middle parabolic:
`Juxtapose.fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_middleSwap`.

## Main results

* `FullChamber.shuffleBot_eq_self`: a chamber separated by `X`, `X ∧ Z` and `X ∨ Z` is fixed by
  `shuffleBot X Z`.
* `Juxtapose.isFourBlock_fourChamber`: `(A B)(C D)` is a four-block chamber.
* `Juxtapose.isBlockSupported_galleryTensorHom_fourBlock`: the juxtapositions
  `(x_a x_b)(x_c x_d)` relabel strands only within the four blocks.
* `Juxtapose.shuffleType_middleSwap`: the middle swap has shuffle type `c`.
* `Juxtapose.fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_middleSwap`: the four-block
  shuffle carries `(x_a x_b)(x_c x_d)` to `(x_a x_c)(x_b x_d)` up to lower shuffle types.
* `Juxtapose.isRankOrdered_fourChamberSwap_iff`: `(A C)(B D)` is rank-ordered exactly when
  `(A B)(C D)` is.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra ChamberEmbedding TensorProduct IsIdempotentElem

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace FullChamber

variable {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- A chamber separated by `X`, by `X ∧ Z` and by `X ∨ Z` is fixed by moving first the strands
of `Z` and then those of `X` to the left. -/
theorem shuffleBot_eq_self {X Z : Strand ν → Bool} {C : FullChamber Γ ν}
    (hX : IsSeparated X C) (hand : IsSeparated (fun t => X t && Z t) C)
    (hor : IsSeparated (fun t => X t || Z t) C) : shuffleBot X Z C = C := by
  refine Subtype.ext (funext fun h => ?_)
  rw [shuffleBot_apply, shuffleTop_apply]
  have h₁ := hX h
  have h₂ := hand h
  have h₃ := hor h
  beta_reduce at h₂ h₃
  revert h₁ h₂ h₃
  generalize X h.lo = x₁
  generalize X h.hi = x₂
  generalize Z h.lo = z₁
  generalize Z h.hi = z₂
  generalize C.1 h = c
  revert x₁ x₂ z₁ z₂ c
  decide

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- A chamber is separated by a constant labelling. -/
theorem isSeparated_const (x : Bool) (C : FullChamber Γ ν) :
    IsSeparated (fun _ : Strand ν => x) C :=
  fun _ h => (h rfl).elim

end FullChamber

namespace ChamberEmbedding

omit [DecidableEq I] in
/-- The relabellings extended from a chamber embedding on whose strands `X` and `Z` are constant
preserve `X` and `Z`. -/
theorem perm_mem_blockStab {ν₀ ν : I →₀ ℕ} {J : ChamberEmbedding Γ ν₀ ν}
    {X Z : Strand ν → Bool} {x z : Bool} (hX : ∀ s, X (J.toFun s) = x)
    (hZ : ∀ s, Z (J.toFun s) = z) (g : ColPerm ν₀) : J.perm g ∈ blockStab ν X Z := by
  intro t
  by_cases ht : t ∈ Set.range J.toFun
  · obtain ⟨s, rfl⟩ := ht
    rw [J.perm_apply, hX, hX, hZ, hZ]
    exact ⟨rfl, rfl⟩
  · rw [J.perm_apply_of_not_mem _ _ ht]
    exact ⟨rfl, rfl⟩

end ChamberEmbedding

namespace Juxtapose

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem isRankOrdered_castChamber {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) (C : FullChamber Γ ν₀) :
    (castChamber h C).IsRankOrdered ↔ C.IsRankOrdered := by
  subst h
  rfl

variable {a b c d : I →₀ ℕ}

omit [DecidableEq I] in
theorem middleLeft_inl_inl (s : Strand a) :
    middleLeft a b c d (inlStrand (a + b) (c + d) (inlStrand a b s)) = true := by
  have hl : (inlStrand (a + b) (c + d) (inlStrand a b s)).IsLeft (a + b) := isLeft_inlStrand _
  simp only [middleLeft, blockLeft, hl, ↓reduceIte, decide_eq_true_eq]
  show s.2.val < (a + c) s.1 - c s.1
  rw [Finsupp.add_apply]
  have := s.2.2
  omega

omit [DecidableEq I] in
theorem middleLeft_inl_inr (s : Strand b) :
    middleLeft a b c d (inlStrand (a + b) (c + d) (inrStrand a b s)) = false := by
  have hl : (inlStrand (a + b) (c + d) (inrStrand a b s)).IsLeft (a + b) := isLeft_inlStrand _
  simp only [middleLeft, blockLeft, hl, ↓reduceIte, decide_eq_false_iff_not]
  show ¬ a s.1 + s.2.val < (a + c) s.1 - c s.1
  rw [Finsupp.add_apply]
  omega

omit [DecidableEq I] in
theorem middleLeft_inr_inl (s : Strand c) :
    middleLeft a b c d (inrStrand (a + b) (c + d) (inlStrand c d s)) = true := by
  have hn : ¬ (inrStrand (a + b) (c + d) (inlStrand c d s)).IsLeft (a + b) :=
    not_isLeft_inrStrand _
  simp only [middleLeft, blockLeft, hn, ↓reduceIte, decide_eq_true_eq]
  show (a + b) s.1 + s.2.val < (a + b) s.1 + c s.1
  have := s.2.2
  omega

omit [DecidableEq I] in
theorem middleLeft_inr_inr (s : Strand d) :
    middleLeft a b c d (inrStrand (a + b) (c + d) (inrStrand c d s)) = false := by
  have hn : ¬ (inrStrand (a + b) (c + d) (inrStrand c d s)).IsLeft (a + b) :=
    not_isLeft_inrStrand _
  simp only [middleLeft, blockLeft, hn, ↓reduceIte, decide_eq_false_iff_not]
  show ¬ (a + b) s.1 + (c s.1 + s.2.val) < (a + b) s.1 + c s.1
  omega

omit [DecidableEq I] in
/-- **The chambers `(A B)(C D)` are four-block chambers.** For rank-ordered `A, B, C, D`, the
juxtaposition `(A B)(C D)` is a four-block chamber for the strands of `a + b` and the strands of
the blocks `a` and `c`. -/
theorem isFourBlock_fourChamber {A : FullChamber Γ a} {B : FullChamber Γ b}
    {C : FullChamber Γ c} {D : FullChamber Γ d} (hA : A.IsRankOrdered) (hB : B.IsRankOrdered)
    (hC : C.IsRankOrdered) (hD : D.IsRankOrdered) :
    IsFourBlock (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d)
      (chamber (chamber A B) (chamber C D)) := by
  refine ⟨(isRankOrdered_chamber_iff _ _).2 ⟨(isRankOrdered_chamber_iff _ _).2 ⟨hA, hB⟩,
    (isRankOrdered_chamber_iff _ _).2 ⟨hC, hD⟩⟩, shuffleBot_eq_self (isSeparated_chamber _ _)
    ?_ ?_⟩
  · refine isSeparated_chamber_of ?_ ?_ ?_
    · have e : (fun s => decide ((inlStrand (a + b) (c + d) s).IsLeft (a + b)) &&
          middleLeft a b c d (inlStrand (a + b) (c + d) s)) =
          fun s => decide (s.IsLeft a) := by
        funext s
        obtain ⟨x | x, rfl⟩ := (strandEquiv a b).surjective s
        · show (decide _ && middleLeft a b c d (inlStrand _ _ (inlStrand a b x))) = _
          rw [middleLeft_inl_inl]
          simp [isLeft_inlStrand]
        · show (decide _ && middleLeft a b c d (inlStrand _ _ (inrStrand a b x))) = _
          rw [middleLeft_inl_inr]
          simp [not_isLeft_inrStrand]
      rw [e]
      exact isSeparated_chamber _ _
    · have e : (fun s => decide ((inrStrand (a + b) (c + d) s).IsLeft (a + b)) &&
          middleLeft a b c d (inrStrand (a + b) (c + d) s)) = fun _ => false := by
        funext s
        simp [not_isLeft_inrStrand]
      rw [e]
      exact isSeparated_const _ _
    · intro s t h
      simpa [not_isLeft_inrStrand] using h
  · refine isSeparated_chamber_of ?_ ?_ fun s _ _ => by simp [isLeft_inlStrand]
    · have e : (fun s => decide ((inlStrand (a + b) (c + d) s).IsLeft (a + b)) ||
          middleLeft a b c d (inlStrand (a + b) (c + d) s)) = fun _ => true := by
        funext s
        simp [isLeft_inlStrand]
      rw [e]
      exact isSeparated_const _ _
    · have e : (fun s => decide ((inrStrand (a + b) (c + d) s).IsLeft (a + b)) ||
          middleLeft a b c d (inrStrand (a + b) (c + d) s)) =
          fun s => decide (s.IsLeft c) := by
        funext s
        obtain ⟨x | x, rfl⟩ := (strandEquiv c d).surjective s
        · show (decide _ || middleLeft a b c d (inrStrand _ _ (inlStrand c d x))) = _
          rw [middleLeft_inr_inl]
          simp [isLeft_inlStrand]
        · show (decide _ || middleLeft a b c d (inrStrand _ _ (inrStrand c d x))) = _
          rw [middleLeft_inr_inr]
          simp [not_isLeft_inrStrand]
      rw [e]
      exact isSeparated_chamber _ _

omit [DecidableEq I] in
/-- `(A C)(B D)` is rank-ordered exactly when `(A B)(C D)` is. -/
theorem isRankOrdered_fourChamberSwap_iff
    (q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d) :
    (fourChamberSwap a b c d q).IsRankOrdered ↔ (fourChamber a b c d q).IsRankOrdered := by
  simp only [fourChamberSwap, fourChamber, isRankOrdered_castChamber, isRankOrdered_chamber_iff]
  tauto

/-- **The shuffle type of the middle swap.** The middle swap sends exactly `c i` strands of colour
`i` of the second block `c + d` into the first block `a + c`. -/
theorem shuffleType_middleSwap :
    shuffleType (a + b) (a + c) (middleSwap a b c d) = ⇑c := by
  funext i
  unfold shuffleType
  by_cases hi : i ∈ (a + b + (c + d)).support
  · have e : (Finset.univ.filter fun t : Strand (a + b + (c + d)) => t.1.1 = i ∧
        ¬ t.IsLeft (a + b) ∧ ((middleSwap a b c d).1 t).IsLeft (a + c)) =
        Finset.univ.filter fun t : Strand (a + b + (c + d)) => t.1 = ⟨i, hi⟩ ∧
          (a + b) i ≤ t.2.val ∧ t.2.val < (a + b) i + c i ∧ True := by
      refine Finset.filter_congr fun t _ => ?_
      obtain ⟨⟨i', hi'⟩, ⟨n, hn⟩⟩ := t
      show i' = i ∧ ¬ n < (a + b) i' ∧ middleRank (a i') (b i') (c i') n < (a + c) i' ↔
        (⟨i', hi'⟩ : (a + b + (c + d)).support) = ⟨i, hi⟩ ∧ (a + b) i ≤ n ∧
          n < (a + b) i + c i ∧ True
      rw [Subtype.mk.injEq]
      constructor
      · rintro ⟨rfl, h2, h3⟩
        simp only [Finsupp.add_apply] at h2 h3 hn ⊢
        unfold middleRank at h3
        refine ⟨trivial, by omega, ?_, trivial⟩
        split_ifs at h3 <;> omega
      · rintro ⟨rfl, h2, h3, -⟩
        simp only [Finsupp.add_apply] at h2 h3 hn ⊢
        unfold middleRank
        refine ⟨trivial, by omega, ?_⟩
        split_ifs <;> omega
    rw [e, card_filter_colour ⟨i, hi⟩ ((a + b) i) ((a + b) i + c i)
      (by show _ ≤ (a + b + (c + d)) i; simp only [Finsupp.add_apply]; omega)]
    have e3 : ((Finset.Ico ((a + b) i) ((a + b) i + c i)).filter
        fun r => ∃ _ : r < (a + b + (c + d)) i, True) =
        Finset.Ico ((a + b) i) ((a + b) i + c i) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Ico, exists_prop, and_true]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      simp only [Finsupp.add_apply] at h ⊢
      omega
    rw [e3, Nat.card_Ico]
    show (a + b) i + c i - (a + b) i = c i
    omega
  · have hc : c i = 0 := by
      rw [Finsupp.notMem_support_iff] at hi
      simp only [Finsupp.add_apply] at hi
      omega
    rw [hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro t - ⟨h1, -⟩
    exact hi (h1 ▸ t.1.2)

variable (hΓ : Γ.PSymm)

/-- **Juxtaposed diagrams in the layout `a b c d` preserve the four blocks.** The juxtaposition
`(x_a x_b)(x_c x_d)` relabels strands only through relabellings preserving the strands of `a + b`
and those of the blocks `a` and `c`. -/
theorem isBlockSupported_galleryTensorHom_fourBlock (xa : GalleryAlgebra k Γ a)
    (xb : GalleryAlgebra k Γ b) (xc : GalleryAlgebra k Γ c) (xd : GalleryAlgebra k Γ d) :
    IsBlockSupported hΓ (blockStab (a + b + (c + d)) (fun t => decide (t.IsLeft (a + b)))
      (middleLeft a b c d))
      (galleryTensorHom k Γ (a + b) (c + d)
        ((galleryTensorHom k Γ a b (xa ⊗ₜ xb)).1 ⊗ₜ
          (galleryTensorHom k Γ c d (xc ⊗ₜ xd)).1)).1 := by
  simp only [galleryTensorHom_tmul, corner_val_mul, map_mul]
  refine (((?_ : IsBlockSupported _ _ _).mul ?_).mul ((?_ : IsBlockSupported _ _ _).mul ?_))
  · rw [leftHom_leftHom_val]
    refine IsBlockSupported.sum _ fun u _ => ?_
    rw [toHom_apply]
    exact isBlockSupported_galleryHom ((leftChamberEmb u.1).comp (leftChamberEmb u.2)) hΓ
      (perm_mem_blockStab (x := true) (z := true)
        (fun s => decide_eq_true (isLeft_inlStrand (ν'' := c + d) (inlStrand a b s)))
        (fun s => middleLeft_inl_inl s)) xa
  · rw [leftHom_rightHom_val]
    refine IsBlockSupported.sum _ fun u _ => ?_
    rw [toHom_apply]
    exact isBlockSupported_galleryHom ((rightChamberEmb u.1).comp (leftChamberEmb u.2)) hΓ
      (perm_mem_blockStab (x := true) (z := false)
        (fun s => decide_eq_true (isLeft_inlStrand (ν'' := c + d) (inrStrand a b s)))
        (fun s => middleLeft_inl_inr s)) xb
  · rw [rightHom_leftHom_val]
    refine IsBlockSupported.sum _ fun u _ => ?_
    rw [toHom_apply]
    exact isBlockSupported_galleryHom ((leftChamberEmb u.1).comp (rightChamberEmb u.2)) hΓ
      (perm_mem_blockStab (x := false) (z := true)
        (fun s => decide_eq_false (not_isLeft_inrStrand (ν' := a + b) (inlStrand c d s)))
        (fun s => middleLeft_inr_inl s)) xc
  · rw [rightHom_rightHom_val]
    refine IsBlockSupported.sum _ fun u _ => ?_
    rw [toHom_apply]
    exact isBlockSupported_galleryHom ((rightChamberEmb u.1).comp (rightChamberEmb u.2)) hΓ
      (perm_mem_blockStab (x := false) (z := false)
        (fun s => decide_eq_false (not_isLeft_inrStrand (ν' := a + b) (inrStrand c d s)))
        (fun s => middleLeft_inr_inr s)) xd

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **Balancedness of the middle parabolic, up to lower shuffle types.** Let `A, B, C, D` and
`A', B', C', D'` be rank-ordered chambers of `a, b, c, d`, and `x_a, x_b, x_c, x_d` diagrams of
`a, b, c, d`. The four-block shuffle for the blocks `a` and `c` passes from the juxtaposition
`(x_a x_b)(x_c x_d)` in the layout `a b c d`, cut down to the chambers `(A B)(C D)` and
`(A' B')(C' D')`, to the juxtaposition `(x_a x_c)(x_b x_d)` in the layout `a c b d`, cut down to
`(A C)(B D)` and `(A' C')(B' D')`, up to terms of shuffle type strictly below `c` (for the
parabolics of `a + b` and `a + c`).

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_middleSwap
    {A A' : FullChamber Γ a} {B B' : FullChamber Γ b} {C C' : FullChamber Γ c}
    {D D' : FullChamber Γ d} (hA : A.IsRankOrdered) (hB : B.IsRankOrdered)
    (hC : C.IsRankOrdered) (hD₀ : D.IsRankOrdered) (hA' : A'.IsRankOrdered)
    (hB' : B'.IsRankOrdered) (hC' : C'.IsRankOrdered) (hD' : D'.IsRankOrdered)
    (xa : GalleryAlgebra k Γ a) (xb : GalleryAlgebra k Γ b) (xc : GalleryAlgebra k Γ c)
    (xd : GalleryAlgebra k Γ d) :
    fourShuffle k hD hZ (middleLeft a b c d) (chamber (chamber A B) (chamber C D)) *
        (e (chamber (chamber A B) (chamber C D)) *
          (galleryTensorHom k Γ (a + b) (c + d)
            ((galleryTensorHom k Γ a b (xa ⊗ₜ xb)).1 ⊗ₜ
              (galleryTensorHom k Γ c d (xc ⊗ₜ xd)).1)).1 *
          e (chamber (chamber A' B') (chamber C' D'))) -
      (e (castChamber (layout_eq a b c d) (chamber (chamber A C) (chamber B D))) *
          castGallery k Γ (layout_eq a b c d) (galleryTensorHom k Γ (a + c) (b + d)
            ((galleryTensorHom k Γ a c (xa ⊗ₜ xc)).1 ⊗ₜ
              (galleryTensorHom k Γ b d (xb ⊗ₜ xd)).1)).1 *
          e (castChamber (layout_eq a b c d) (chamber (chamber A' C') (chamber B' D')))) *
        fourShuffle k hD hZ (middleLeft a b c d) (chamber (chamber A' B') (chamber C' D')) ∈
      mackeyFilt k hP hD hZ hΓ hW hL (a + b) (a + c)
        (castChamber (layout_eq a b c d) (chamber (chamber A C) (chamber B D)))
        (chamber (chamber A' B') (chamber C' D')) (Set.Iio ⇑c) := by
  let Q := {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d //
    (fourChamber a b c d q).IsRankOrdered}
  have hrank : ∀ q : Q, q.1.1.IsRankOrdered ∧ q.1.2.1.IsRankOrdered ∧
      q.1.2.2.1.IsRankOrdered ∧ q.1.2.2.2.IsRankOrdered := fun q => by
    have h := q.2
    simp only [fourChamber, isRankOrdered_chamber_iff] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have key := fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_of_blockOp (k := k) hΓ hP hD hZ
    hW hL (ν' := a + b) (ν'' := c + d) (ν₁ := a + c) (ν₂ := b + d) rfl (layout_eq a b c d)
    ⟨middleSwap a b c d, shuffleType_middleSwap⟩
    (χ := fun q : Q => fourChamber a b c d q.1) (χ' := fun q : Q => fourChamberSwap a b c d q.1)
    (fun q => isFourBlock_fourChamber (hrank q).1 (hrank q).2.1 (hrank q).2.2.1
      (hrank q).2.2.2)
    (ρ := middleSwap a b c d) (fun q => middleSwap_smul_shuffleTop a b c d _ _ _ _)
    (fun q => (isRankOrdered_fourChamberSwap_iff q.1).2 q.2)
    (isBlockSupported_galleryTensorHom_fourBlock hΓ xa xb xc xd)
    (fun q q' => (isLocalConj_galleryTensorHom_fourBlock hΓ xa xb xc xd).2.2 q.1 q'.1)
    ⟨(A, B, C, D), (isRankOrdered_chamber_iff _ _).2 ⟨(isRankOrdered_chamber_iff _ _).2 ⟨hA, hB⟩,
      (isRankOrdered_chamber_iff _ _).2 ⟨hC, hD₀⟩⟩⟩
    ⟨(A', B', C', D'), (isRankOrdered_chamber_iff _ _).2
      ⟨(isRankOrdered_chamber_iff _ _).2 ⟨hA', hB'⟩, (isRankOrdered_chamber_iff _ _).2 ⟨hC', hD'⟩⟩⟩
  exact key

end Juxtapose

end Categorification.WeightedKLR
