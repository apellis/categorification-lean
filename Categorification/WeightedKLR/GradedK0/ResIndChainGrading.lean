/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.Graded.K0Filtration
import Categorification.Algebra.Graded.TensorGdim
import Categorification.WeightedKLR.Mackey.ResIndChain
import Categorification.WeightedKLR.GradedK0.ResIndGrading
import Categorification.WeightedKLR.GradedK0.Induction

/-!
# The graded Mackey chain of `Res ∘ Ind`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19, filters `Res_{ν₁;ν₂} Ind_{ν';ν''}` by shuffle types; the subquotient of type `c` is
the middle balanced tensor product `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`, shifted
in degree by `middleShift`. This file makes the chain of
`GalleryAlgebra.exists_resInd_balancedTensor_eq_sum` graded.

## Main results

* `Juxtapose.middleAlgGrading`, the `Decomposition` instances of `middleTopGrading`,
  `middleBotGrading` and `middleGrading`: the middle balanced tensor product is a graded space.
* `Juxtapose.middleCornerMap_mem_middleGrading`: `t ⊗ y ↦ zL t ⊗ y zR` raises degrees by
  `deg zL + deg zR`.
* `ResIndPiece.grading`: the grading of the piece of a four-block layout, the middle grading
  shifted by `middleShift`; the left and right actions are graded.
* `GalleryAlgebra.resIndBimoduleGrading`: the grading of `Res_{ν₁;ν₂} Ind_{ν';ν''}`, with graded
  left and right actions and homogeneous steps.
* `Juxtapose.exists_middleResInd_gradedEquiv`: the subquotient of shuffle type `c` is the shifted
  middle balanced tensor product, as a graded bimodule;
  `GalleryAlgebra.resIndPieceMap_preservesGrading`: the projections of the steps onto the pieces
  are degree-preserving.
* `GalleryAlgebra.exists_resInd_balancedTensor_eq_sum_graded`: the Mackey filtration of
  `Res_{ν₁;ν₂} Ind_{ν';ν''} ⊗ N` in graded `K₀`, over a field.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose _root_.Categorification.Graded DirectSum MulOpposite

open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

attribute [local instance] ColPerm.fintype

section CommRing

variable {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GradingDatum

variable (G : GradingDatum Γ)

theorem castW_mem_klrGrade {ν μ : I →₀ ℕ} (h : ν = μ) {d : ℤ} {x : WeightedKLRAlgebra k Γ ν}
    (hx : x ∈ G.klrGrade ν d) : castW k Γ h x ∈ G.klrGrade μ d := by
  subst h
  exact hx

theorem castW_symm_mem_klrGrade {ν μ : I →₀ ℕ} (h : ν = μ) {d : ℤ}
    {x : WeightedKLRAlgebra k Γ μ} (hx : x ∈ G.klrGrade μ d) :
    (castW k Γ h).symm x ∈ G.klrGrade ν d := by
  subst h
  exact hx

/-- `castW ⊗ castW` is degree-preserving. -/
theorem congr_castW_mem_tensorGrading {ν₁ ν₂ μ₁ μ₂ : I →₀ ℕ} (h₁ : ν₁ = μ₁) (h₂ : ν₂ = μ₂)
    {d : ℤ} {t : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂}
    (ht : t ∈ tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂) d) :
    Algebra.TensorProduct.congr (castW k Γ h₁) (castW k Γ h₂) t ∈
      tensorGrading (G.klrGrade μ₁) (G.klrGrade μ₂) d := by
  subst h₁ h₂
  simpa [castW] using ht

/-- `ι_{ν₁;ν₂}`, read in the gallery algebra of `ν`, is degree-preserving. -/
theorem inductionVal_mem_grade {ν₁ ν₂ : I →₀ ℕ} (hν : ν₁ + ν₂ = ν) {d : ℤ}
    {t : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂}
    (ht : t ∈ tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂) d) :
    inductionVal k hν t ∈ G.grade ν d :=
  tensorGrading_map_mem _ _ (G.grade ν) (inductionVal k hν)
    (fun _ _ _ _ hx hy => inductionVal_tmul_mem_grade G hν hx hy) ht

end GradingDatum

namespace Juxtapose

variable (G : GradingDatum Γ) {a b c d : I →₀ ℕ}

variable (a b c d) in
/-- The grading of the middle algebra `W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`. -/
noncomputable abbrev middleAlgGrading : ℤ → Submodule k (MiddleAlg k Γ a b c d) :=
  tensorGrading (tensorGrading (G.klrGrade a) (G.klrGrade b))
    (tensorGrading (G.klrGrade c) (G.klrGrade d))

/-- `middleTop : W' → W_{a+c} ⊗ W_{b+d}` is degree-preserving. -/
theorem middleTop_mem {n : ℤ} {r : MiddleAlg k Γ a b c d} (hr : r ∈ middleAlgGrading G a b c d n) :
    middleTop k Γ a b c d r ∈ tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) n := by
  refine tensorGrading_map_mem _ _ _ (middleTop k Γ a b c d)
    (fun i j m m' hm hm' => ?_) hr
  refine tensorGrading_map_mem _ _
    (fun i' => tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) (i' + j))
    (middleTop k Γ a b c d ∘ₗ (TensorProduct.mk k _ _).flip m') (fun i₁ i₂ xa xb ha hb => ?_) hm
  refine tensorGrading_map_mem _ _
    (fun j' => tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) (i₁ + i₂ + j'))
    (middleTop k Γ a b c d ∘ₗ TensorProduct.mk k _ _ (xa ⊗ₜ xb)) (fun j₁ j₂ xc xd hc hd => ?_) hm'
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, middleTop_tmul]
  have := tmul_mem_tensorGrading (G.inductionMap_mem_klrGrade (tmul_mem_tensorGrading ha hc))
    (G.inductionMap_mem_klrGrade (tmul_mem_tensorGrading hb hd))
  convert this using 2
  ring

/-- `middleBot : W' → W_{a+b} ⊗ W_{c+d}` is degree-preserving. -/
theorem middleBot_mem {n : ℤ} {r : MiddleAlg k Γ a b c d} (hr : r ∈ middleAlgGrading G a b c d n) :
    middleBot k Γ a b c d r ∈ tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) n := by
  refine tensorGrading_map_mem _ _ _ (middleBot k Γ a b c d)
    (fun i j m m' hm hm' => ?_) hr
  refine tensorGrading_map_mem _ _
    (fun i' => tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) (i' + j))
    (middleBot k Γ a b c d ∘ₗ (TensorProduct.mk k _ _).flip m') (fun i₁ i₂ xa xb ha hb => ?_) hm
  refine tensorGrading_map_mem _ _
    (fun j' => tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) (i₁ + i₂ + j'))
    (middleBot k Γ a b c d ∘ₗ TensorProduct.mk k _ _ (xa ⊗ₜ xb)) (fun j₁ j₂ xc xd hc hd => ?_) hm'
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, middleBot_tmul]
  exact tmul_mem_tensorGrading (G.inductionMap_mem_klrGrade (tmul_mem_tensorGrading ha hb))
    (G.inductionMap_mem_klrGrade (tmul_mem_tensorGrading hc hd))

theorem middleTop_one_mem :
    middleTop k Γ a b c d 1 ∈ tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) 0 := by
  rw [middleTop_one, ← add_zero (0 : ℤ)]
  exact tmul_mem_tensorGrading G.inductionMap_one_mem_klrGrade G.inductionMap_one_mem_klrGrade

theorem middleBot_one_mem :
    middleBot k Γ a b c d 1 ∈ tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) 0 := by
  rw [middleBot_one, ← add_zero (0 : ℤ)]
  exact tmul_mem_tensorGrading G.inductionMap_one_mem_klrGrade G.inductionMap_one_mem_klrGrade

/-! ### The middle balanced tensor product as a graded space -/

theorem middleTopSub_isHomogeneous :
    (middleTopSub k Γ a b c d).IsHomogeneous
      (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) := by
  intro n x hx
  rw [mem_middleTopSub] at hx ⊢
  rw [← coe_decompose_mul_of_right_mem_zero
    (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)))
    (middleTop_one_mem (a := a) (b := b) (c := c) (d := d) G), hx]

theorem middleBotSub_isHomogeneous :
    (middleBotSub k Γ a b c d).IsHomogeneous
      (tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d))) := by
  intro n x hx
  rw [mem_middleBotSub] at hx ⊢
  rw [← coe_decompose_mul_of_left_mem_zero (tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)))
    (middleBot_one_mem (a := a) (b := b) (c := c) (d := d) G), hx]

noncomputable instance : Decomposition (middleTopGrading G a b c d) :=
  submoduleDecomposition (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)))
    (middleTopSub_isHomogeneous G)

noncomputable instance : Decomposition (middleBotGrading G a b c d) :=
  submoduleDecomposition (tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)))
    (middleBotSub_isHomogeneous G)

/-- The right action of `W'` on `(W_{a+c} ⊗ W_{b+d}) e'` is graded. -/
theorem op_smul_mem_middleTopGrading {i l : ℤ} {t : MiddleTop k Γ a b c d}
    {r : MiddleAlg k Γ a b c d} (ht : t ∈ middleTopGrading G a b c d i)
    (hr : r ∈ middleAlgGrading G a b c d l) :
    op r • t ∈ middleTopGrading G a b c d (i + l) :=
  SetLike.GradedMul.mul_mem (A := tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) ht
    (middleTop_mem G hr)

/-- The left action of `W'` on `e (W_{a+b} ⊗ W_{c+d})` is graded. -/
instance : SetLike.GradedSMul (middleAlgGrading G a b c d) (middleBotGrading G a b c d) where
  smul_mem _ _ _ _ hr hy :=
    SetLike.GradedMul.mul_mem (A := tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)))
      (middleBot_mem G hr) hy

/-- **The middle balanced tensor product is a graded space.** -/
noncomputable instance : Decomposition (middleGrading G a b c d) :=
  balancedDecomposition (middleAlgGrading G a b c d)
    fun _ _ _ _ ht hr => op_smul_mem_middleTopGrading G ht hr

/-- **`t ⊗ y ↦ zL t ⊗ y zR` raises degrees by `deg zL + deg zR`.** -/
theorem middleCornerMap_mem_middleGrading {i j n : ℤ}
    {zL : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)}
    {zR : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)}
    (hzL : zL ∈ tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) i)
    (hzR : zR ∈ tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) j)
    {x : MiddleTensor k Γ a b c d} (hx : x ∈ middleGrading G a b c d n) :
    middleCornerMap zL zR x ∈ middleGrading G a b c d (i + n + j) := by
  refine balancedGrading_map_mem (fun n' => middleGrading G a b c d (i + n' + j)) _
    (fun i' j' t y ht hy => ?_) hx
  rw [middleCornerMap_tmul]
  have h₁ : zL • t ∈ middleTopGrading G a b c d (i + i') :=
    SetLike.GradedMul.mul_mem (A := tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)))
      hzL ht
  have h₂ : middleBotMulRight zR y ∈ middleBotGrading G a b c d (j' + j) :=
    SetLike.GradedMul.mul_mem (A := tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)))
      hy hzR
  rw [show i + (i' + j') + j = (i + i') + (j' + j) by ring]
  exact tmul_mem_balancedGrading h₁ h₂

end Juxtapose


namespace ShuffleLayout

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂) (G : GradingDatum Γ)

/-- The inverse of `ShuffleLayout.leftEquiv` is degree-preserving. -/
theorem leftEquiv_symm_mem {d : ℤ} {u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂}
    (hu : u ∈ tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂) d) :
    (L.leftEquiv k Γ).symm u ∈ tensorGrading (G.klrGrade (L.a + L.c)) (G.klrGrade (L.b + L.d)) d :=
  tensorGrading_map_mem _ _ _ (L.leftEquiv k Γ).symm.toLinearMap
    (fun _ _ _ _ hx hy => by
      simp only [ShuffleLayout.leftEquiv, AlgEquiv.toLinearMap_apply,
        Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul]
      exact tmul_mem_tensorGrading (G.castW_symm_mem_klrGrade L.hac hx)
        (G.castW_symm_mem_klrGrade L.hbd hy)) hu

/-- The inverse of `ShuffleLayout.rightEquiv` is degree-preserving. -/
theorem rightEquiv_symm_mem {d : ℤ}
    {w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''}
    (hw : w ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') d) :
    (L.rightEquiv k Γ).symm w ∈ tensorGrading (G.klrGrade (L.a + L.b)) (G.klrGrade (L.c + L.d)) d :=
  tensorGrading_map_mem _ _ _ (L.rightEquiv k Γ).symm.toLinearMap
    (fun _ _ _ _ hx hy => by
      simp only [ShuffleLayout.rightEquiv, AlgEquiv.toLinearMap_apply,
        Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul]
      exact tmul_mem_tensorGrading (G.castW_symm_mem_klrGrade L.hab hx)
        (G.castW_symm_mem_klrGrade L.hcd hy)) hw

end ShuffleLayout

namespace ResIndPiece

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂) (G : GradingDatum Γ)

/-- **The grading of the piece of a four-block layout**: the grading of the middle balanced tensor
product, shifted by `middleShift` (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19). -/
noncomputable def grading : ℤ → Submodule k (ResIndPiece k Γ L) :=
  Graded.shift (middleGrading G L.a L.b L.c L.d) (middleShift G L.a L.b L.c L.d)

theorem mem_grading {n : ℤ} {x : ResIndPiece k Γ L} :
    x ∈ grading L G n ↔
      (x : MiddleTensor k Γ L.a L.b L.c L.d) ∈
        middleGrading G L.a L.b L.c L.d (n - middleShift G L.a L.b L.c L.d) :=
  Iff.rfl

noncomputable instance : Decomposition (grading L G) :=
  inferInstanceAs (Decomposition (Graded.shift (middleGrading G L.a L.b L.c L.d)
    (middleShift G L.a L.b L.c L.d)))

instance : SetLike.GradedSMul (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂)) (grading L G) where
  smul_mem {i j u x} hu hx := by
    rw [mem_grading] at hx ⊢
    rw [smul_left_def, ResIndPiece.leftAct, middleLeftAct_apply]
    have := middleCornerMap_mem_middleGrading G (L.leftEquiv_symm_mem G hu)
      (SetLike.GradedOne.one_mem (A := tensorGrading (G.klrGrade (L.a + L.b))
        (G.klrGrade (L.c + L.d)))) hx
    rw [show (i +ᵥ j) - middleShift G L.a L.b L.c L.d =
      i + (j - middleShift G L.a L.b L.c L.d) + 0 by rw [vadd_eq_add]; ring]
    exact this

/-- The right action on a piece raises degrees. -/
theorem op_smul_mem {i l : ℤ} {x : ResIndPiece k Γ L}
    {w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''}
    (hx : x ∈ grading L G i) (hw : w ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') l) :
    op w • x ∈ grading L G (i + l) := by
  rw [mem_grading] at hx ⊢
  rw [smul_right_def, ResIndPiece.rightAct, middleRightAct_apply]
  have := middleCornerMap_mem_middleGrading G
    (SetLike.GradedOne.one_mem (A := tensorGrading (G.klrGrade (L.a + L.c))
      (G.klrGrade (L.b + L.d)))) (L.rightEquiv_symm_mem G hw) hx
  rw [show i + l - middleShift G L.a L.b L.c L.d =
    0 + (i - middleShift G L.a L.b L.c L.d) + l by ring]
  exact this

end ResIndPiece


namespace Juxtapose

variable {a b c d : I →₀ ℕ}

/-- **The subquotient of one shuffle type of the Mackey filtration of `Res ∘ Ind` is the shifted
middle balanced tensor product, as a graded bimodule** (B. Webster, arXiv:1209.2463v4, proof of
Theorem 2.19): `exists_middleResInd_equiv`, with the isomorphism moreover carrying the grading of
the middle balanced tensor product shifted by `middleShift G a b c d` onto the grading of the
subquotient `S / S'`. The hypotheses `hP`, `hW`, `hL` are those of Webster, Theorem 2.8, for the
weight `ν`. -/
theorem exists_middleResInd_gradedEquiv (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (G : GradingDatum Γ) {ν ν' ν'' ν₁ ν₂ : I →₀ ℕ}
    {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand ν), Γ.loop s.1 = some Q → s ≠ t →
      s.1 = t.1 → IsRegular (loopFactor Q s t))
    (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S' S : Set (I → ℕ)} (hS : IsLowerSet S)
    (hS'l : IsLowerSet S') {μ : I → ℕ} (hμS : μ ∈ S) (hlow : Set.Iio μ ⊆ S') (hμS' : μ ∉ S')
    (hone : ∀ μ' ∈ S, μ' ∉ S' → μ' = μ) (hab : a + b = ν') (hcd : c + d = ν'')
    (hac : a + c = ν₁) (hbd : b + d = ν₂) (hμc : μ = ⇑c) :
    ∃ f : MiddleTensor k Γ a b c d ≃ₗ[k]
        ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S,
      (∀ zL zR, f.toLinearMap ∘ₗ middleCornerMap zL zR =
        resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS'l hS
            (Algebra.TensorProduct.congr (castW k Γ hac) (castW k Γ hbd) zL)
            (Algebra.TensorProduct.congr (castW k Γ hab) (castW k Γ hcd) zR) ∘ₗ
          f.toLinearMap) ∧
      ∀ (n : ℤ) (x : MiddleTensor k Γ a b c d),
        x ∈ Graded.shift (middleGrading G a b c d) (middleShift G a b c d) n ↔
          f x ∈ resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S n := by
  subst hab hcd hac hbd hμc hν'
  refine ⟨middleResIndEquiv hD hZ hP hΓ hW hL hS hμS hlow hS'l hμS' hone, fun zL zR => ?_,
    fun n x => ?_⟩
  · have h := middleResIndMap_comp_middleCornerMap hD hZ hP hΓ hW hL hS hμS hlow hS'l zL zR
    simp only [castW, Algebra.TensorProduct.congr_refl]
    exact h
  · let g := middleResIndGradedEquiv hD hZ G hP hΓ hW hL hS hμS hlow hS'l hμS' hone
    refine ⟨fun hx => g.map_mem hx, fun hy => ?_⟩
    have := g.symm.map_mem hy
    rwa [show g.symm (middleResIndEquiv hD hZ hP hΓ hW hL hS hμS hlow hS'l hμS' hone x) = x from
      g.toLinearEquiv.symm_apply_apply x] at this

end Juxtapose


namespace GalleryAlgebra

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}
  {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  {hP : ∀ C E, IsChamberSegment C E (P C E)} {hD : Γ.Dagger} {hZ : Γ.NoZeroLoops}
  {hΓ : Γ.PSymm} {hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k))}
  {hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b)}
  {hν' : ν' + ν'' = ν} {hν₁ : ν₁ + ν₂ = ν} (G : GradingDatum Γ)

variable (hP hD hZ hΓ hW hL hν' hν₁) in
/-- **The grading of `Res_{ν₁;ν₂} Ind_{ν';ν''}`**, restricted from the grading of the gallery
algebra `W_ν` (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19). -/
noncomputable def resIndBimoduleGrading :
    ℤ → Submodule k (ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁) :=
  Graded.comap (G.grade ν) ResIndBimodule.valHom

theorem mem_resIndBimoduleGrading {n : ℤ} {z : ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁} :
    z ∈ resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G n ↔ z.val ∈ G.grade ν n :=
  Iff.rfl

noncomputable instance : Decomposition (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G) :=
  (isInternal_comap (G.grade ν) ResIndBimodule.valHom
    (ResIndBimodule.val_injective hP hD hZ hΓ hW hL hν' hν₁) fun z d =>
      ⟨⟨_, resIndFilt_mono hP hD hZ hΓ hW hL hν' hν₁ (Set.subset_univ _)
        (decompose_mem_resIndFilt hP hD hZ hΓ hW hL G hν' hν₁ Set.univ z.2 d)⟩,
      rfl⟩).chooseDecomposition

instance : SetLike.GradedSMul (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
    (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G) where
  smul_mem {i j u z} hu hz := by
    rw [mem_resIndBimoduleGrading] at hz ⊢
    rw [ResIndBimodule.val_smul_left, vadd_eq_add, ← add_zero (i + j)]
    exact SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem
      (G.inductionVal_mem_grade hν₁ hu) hz) (inductionVal_one_mem_grade G hν')

/-- The right action on `Res_{ν₁;ν₂} Ind_{ν';ν''}` raises degrees. -/
theorem op_smul_mem_resIndBimoduleGrading {i l : ℤ}
    {z : ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁}
    {w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''}
    (hz : z ∈ resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G i)
    (hw : w ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') l) :
    op w • z ∈ resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G (i + l) := by
  rw [mem_resIndBimoduleGrading] at hz ⊢
  rw [ResIndBimodule.val_smul_right, unop_op, ← zero_add i]
  exact SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem
    (inductionVal_one_mem_grade G hν₁) hz) (G.inductionVal_mem_grade hν' hw)

/-- **The steps of the Mackey filtration are homogeneous sub-bimodules.** -/
theorem resIndSubBimodule_isHomogeneous {S : Set (I → ℕ)} (hS : IsLowerSet S) :
    (resIndSubBimodule (hP := hP) (hD := hD) (hZ := hZ) (hΓ := hΓ) (hW := hW) (hL := hL)
      (hν' := hν') (hν₁ := hν₁) hS).toSubmodule.IsHomogeneous
      (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G) := by
  intro d z hz
  rw [mem_resIndSubBimodule]
  have h := decompose_map (ℳ := resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G)
    (𝒩 := G.grade ν) (f := ResIndBimodule.valHom) (fun _ _ hx => hx) z d
  change ResIndBimodule.valHom _ ∈ _
  rw [← h]
  exact decompose_mem_resIndFilt hP hD hZ hΓ hW hL G hν' hν₁ S hz d

/-- **The projection of a step of the Mackey filtration onto its piece is degree-preserving**, for
a graded isomorphism of the subquotient with the shifted middle balanced tensor product (as
supplied by `Juxtapose.exists_middleResInd_gradedEquiv`). -/
theorem resIndPieceMap_preservesGrading {S' S : Set (I → ℕ)} (hS' : IsLowerSet S')
    (hS : IsLowerSet S) (L : ShuffleLayout ν' ν'' ν₁ ν₂)
    (f : MiddleTensor k Γ L.a L.b L.c L.d ≃ₗ[k] ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S)
    (hf : ∀ zL zR, f.toLinearMap ∘ₗ middleCornerMap zL zR =
      resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS
        (Algebra.TensorProduct.congr (castW k Γ L.hac) (castW k Γ L.hbd) zL)
        (Algebra.TensorProduct.congr (castW k Γ L.hab) (castW k Γ L.hcd) zR) ∘ₗ f.toLinearMap)
    (hfg : ∀ (n : ℤ) (x : MiddleTensor k Γ L.a L.b L.c L.d),
      x ∈ Graded.shift (middleGrading G L.a L.b L.c L.d) (middleShift G L.a L.b L.c L.d) n ↔
        f x ∈ resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S n) :
    ∀ ⦃d : ℤ⦄ ⦃x : (resIndSubBimodule (hP := hP) (hD := hD) (hZ := hZ) (hΓ := hΓ) (hW := hW)
        (hL := hL) (hν' := hν') (hν₁ := hν₁) hS).toSubmodule⦄,
      x ∈ Graded.submodule (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G)
        (resIndSubBimodule (hP := hP) (hD := hD) (hZ := hZ) (hΓ := hΓ) (hW := hW) (hL := hL)
          (hν' := hν') (hν₁ := hν₁) hS).toSubmodule d →
      resIndPieceMap hS' hS L f hf x ∈ ResIndPiece.grading L G d := by
  intro d x hx
  have hq : resIndStepMk S' hS x ∈ resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S d :=
    Submodule.mem_map_of_mem (p := resIndFiltGrading hP hD hZ hΓ hW hL G hν' hν₁ S d)
      (r := ⟨(x : ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁).val, x.2⟩) hx
  rw [resIndPieceMap_apply]
  exact (hfg d (f.symm (resIndStepMk S' hS x))).2 (by rwa [f.apply_symm_apply])

end GalleryAlgebra

end CommRing

section Field

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}
  {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (G : GradingDatum Γ)

/-- **The graded Mackey filtration of `Res_{ν₁;ν₂} Ind_{ν';ν''}` in graded `K₀`** (B. Webster,
arXiv:1209.2463v4, proof of Theorem 2.19, step (iii); after Khovanov–Lauda, arXiv:0803.4121v2,
Proposition 2.18), over a field. There are four-block layouts `L 0, …, L (n - 1)` whose shuffle
types `c` are exactly the shuffle types that occur, each once, such that for every graded
projective left `W_{ν'} ⊗ W_{ν''}`-module `N` for which all `ResIndPiece L ⊗ N` are finitely
generated projective, `ResIndBimodule ⊗ N` is finitely generated projective and
`[ResIndBimodule ⊗ N] = ∑_i [ResIndPiece (L i) ⊗ N]` in the graded `K₀` of `W_{ν₁} ⊗ W_{ν₂}`.
`ResIndBimodule` carries the grading of the gallery algebra `W_ν` and `ResIndPiece (L i)` the
grading of the middle balanced tensor product shifted by `middleShift G a b c d`, so the
`i`-th summand is `q^{middleShift}` times the class of the unshifted middle tensor product. The
hypotheses `hP`, `hW`, `hL` are those of Webster, Theorem 2.8, for the weight `ν`. -/
theorem exists_resInd_balancedTensor_eq_sum_graded :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν) ν' ν₁) ∧
      ∀ (N : Type (max u w)) [AddCommGroup N] [Module k N]
        [Module (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]
        [IsScalarTower k (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]
        (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩]
        [SetLike.GradedSMul (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) 𝒩]
        [Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') N]
        [∀ i, Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
          (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ (L i)) N)]
        [∀ i, Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
          (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ (L i)) N)],
        ∃ (_ : Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
              (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
              (ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁) N))
          (_ : Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
              (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
              (ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁) N)),
          K0.of (balancedTensorGProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
            (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) 𝒩
            (ResIndBimodule k hP hD hZ hΓ hW hL hν' hν₁)
            (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G)
            fun _ _ _ _ hz hw => op_smul_mem_resIndBimoduleGrading G hz hw) =
            ∑ i, K0.of (balancedTensorGProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
              (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) 𝒩
              (ResIndPiece k Γ (L i)) (ResIndPiece.grading (L i) G)
              fun _ _ _ _ hx hw => ResIndPiece.op_smul_mem (L i) G hx hw) := by
  obtain ⟨n, f, hfi, hfr, hlt⟩ :=
    Categorification.exists_enum_of_finite (finite_range_shuffleType (ν := ν) ν' ν₁)
  have hlay : ∀ j : Fin n, ∃ L : ShuffleLayout ν' ν'' ν₁ ν₂, ⇑L.c = f j := fun j => by
    obtain ⟨y, hy⟩ : f j ∈ Set.range (shuffleType (ν := ν) ν' ν₁) := hfr ▸ ⟨j, rfl⟩
    obtain ⟨a, b, c, d, hab, hcd, hac, hbd, hc⟩ := exists_layout_of_shuffleType hν' hν₁ y
    exact ⟨⟨a, b, c, d, hab, hcd, hac, hbd⟩, hc.trans hy⟩
  choose L hLc using hlay
  have hS' : ∀ j : Fin n, IsLowerSet (shuffleTypeStep f j ∪ Set.Iio (f j)) := fun j =>
    (isLowerSet_shuffleTypeStep f j).union (isLowerSet_Iio (f j))
  have heq := fun j : Fin n =>
    exists_middleResInd_gradedEquiv hD hZ G hP hΓ hW hL hν' hν₁
      (isLowerSet_shuffleTypeStep f (j + 1)) (hS' j) (μ := f j) ⟨j, Nat.lt_succ_self _, le_rfl⟩
      Set.subset_union_right
      (fun h => h.elim (notMem_shuffleTypeStep hfi hlt j)
        (fun h => lt_irrefl (f j) (Set.mem_Iio.1 h)))
      (fun _ hμ hμ' => eq_of_mem_shuffleTypeStep_succ j hμ hμ') (L j).hab (L j).hcd (L j).hac
      (L j).hbd (hLc j).symm
  choose e he heg using heq
  have hcf : (fun i => ⇑(L i).c) = f := funext hLc
  refine ⟨n, L, ?_, by rw [hcf, hfr], fun N _ _ _ _ 𝒩 _ _ _ _ _ => ?_⟩
  · intro i j h
    exact hfi ((hLc i).symm.trans (h.trans (hLc j)))
  refine K0.exists_of_balancedTensor_eq_sum (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
    (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) 𝒩
    (resIndBimoduleGrading hP hD hZ hΓ hW hL hν' hν₁ G)
    (fun _ _ _ _ hz hw => op_smul_mem_resIndBimoduleGrading G hz hw)
    (fun i => ResIndPiece.grading (L i) G)
    (fun i _ _ _ _ hx hw => ResIndPiece.op_smul_mem (L i) G hx hw)
    (fun i => resIndSubBimodule (hP := hP) (hD := hD) (hZ := hZ) (hΓ := hΓ) (hW := hW)
      (hL := hL) (hν' := hν') (hν₁ := hν₁) (isLowerSet_shuffleTypeStep f i))
    (fun i j hij => resIndSubBimodule_mono _ _ _ _ _ _ _ _ _ _ (shuffleTypeStep_mono f hij))
    (fun i => resIndSubBimodule_isHomogeneous G (isLowerSet_shuffleTypeStep f i))
    ?_ ?_
    (fun i => resIndPieceMap (hS' i) (isLowerSet_shuffleTypeStep f (i + 1)) (L i) (e i) (he i))
    (fun i => isBimoduleHom_resIndPieceMap _ _ _ _ _)
    (fun i => resIndPieceMap_preservesGrading G (hS' i) (isLowerSet_shuffleTypeStep f (i + 1))
      (L i) (e i) (he i) (heg i))
    (fun i => resIndPieceMap_surjective _ _ _ _ _) fun i x => ?_
  · refine (Submodule.eq_bot_iff _).2 fun z hz =>
      ResIndBimodule.val_injective hP hD hZ hΓ hW hL hν' hν₁ ?_
    rw [mem_resIndSubBimodule, shuffleTypeStep_zero, resIndFilt_empty, Submodule.mem_bot] at hz
    exact hz
  · refine resIndSubBimodule_eq_top _ _ _ _ _ _ _ _ _ ?_
    rw [← hfr]
    exact range_subset_shuffleTypeStep f
  · rw [resIndPieceMap_eq_zero_iff, mem_resIndSubBimodule,
      resIndFilt_congr hP hD hZ hΓ hW hL hν' hν₁ (S' := shuffleTypeStep f i)
        (by rw [← hfr]; exact shuffleTypeStep_union_Iio_inter hlt i)]

end GalleryAlgebra

end Field

end Categorification.WeightedKLR
