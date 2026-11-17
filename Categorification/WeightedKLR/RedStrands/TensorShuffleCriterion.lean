/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordRelations
import Categorification.WeightedKLR.RedStrands.TensorShuffleRecurrence
import Categorification.Algebra.Graded.ProjectiveCharacter
import Categorification.WeightedKLR.RedStrands.SimpleTopGrading
import Categorification.WeightedKLR.RedStrands.LastRedRank
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Testing ordinary Stendhal words on finite modules

Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38. An ordinary
word can be tested by its graded Hom into finite modules. If these
numbers compute separating tensor coordinates of its shuffle vector,
then factorial cancellation identifies the divided words. The rank
upper bound makes the resulting surjection injective. The target
integral lattice uses Laurent inversion for the projective grading shift.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open Categorification.Graded
open GProj
local notation "LP" => LaurentPolynomial ℤ
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [Module.Finite k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

private theorem injective_of_rank_le {N : Type*} [AddCommGroup N] [Module LP N]
    (f : K0 𝒜 →ₛₗ[invLP.toRingHom] N) (hs : Function.Surjective f)
    (hrank : Module.finrank LP (K0 𝒜) ≤ Module.finrank LP N) : Function.Injective f := by
  have := finite_indec 𝒜
  let b := K0.indecBasis 𝒜
  let := Module.Finite.of_basis b
  let σ : (IndecClass 𝒜 →₀ LP) ≃ₛₗ[invLP.toRingHom] (IndecClass 𝒜 →₀ LP) := Finsupp.mapRange.linearEquiv invLP.toSemilinearEquiv
  let e : K0 𝒜 ≃ₛₗ[invLP.toRingHom] K0 𝒜 := b.repr.trans (σ.trans b.repr.symm)
  let g : K0 𝒜 →ₗ[LP] N := f.comp e.toLinearMap
  have hg : Function.Surjective g := hs.comp e.surjective
  have hd : Disjoint (⊤ : Submodule LP (K0 𝒜)) (LinearMap.ker g) := by
    apply Submodule.disjoint_ker_of_finrank_le
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    simpa using hrank
  have hi := LinearMap.ker_eq_bot.mp (top_disjoint.mp hd)
  intro x y h
  apply e.symm.injective
  apply hi
  change f (e (e.symm x)) = f (e (e.symm y))
  rwa [e.apply_symm_apply,e.apply_symm_apply]


section Words
open KLR QuantumGroup LieLean LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I F Y : Type*} [DecidableEq I] [Field F] [AddCommGroup Y] [Finite I] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) F} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} (wt : Fin ℓ → Dom R) (hR : R.IsXRegular)
  (β : Multiset I)
local notation "𝕂" => RatFunc ℚ
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "𝓣" => tensorProductGrade G β
local notation "T" => TensorProductAlgebra F Q Λ β
local notation "P" => K0 𝓣
local notation "V" => integralTensorWeight wt hR β.toFinsupp
local notation "qToV" => KLGamma.qToV

/-- The ordinary principal projective associated to the expanded loading in a fixed block. -/
def ordinaryProjectiveAt (w : TensorWordAt ℓ β) : GProj 𝓣 :=
  w.2 ▸ sequenceProj G w.1.loading w.1.blocks_redOrdered

/-- The boundary idempotent at the ordinary loading of a tensor word. -/
def ordinaryLoadingIdem (w : TensorWordAt ℓ β) : T :=
  w.2 ▸ TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e w.1.loading w.1.blocks_redOrdered)

omit [Finite I] in
/-- Evaluation at the loading idempotent computes the graded Hom from its
ordinary projective, as used in Webster §4.7. -/
theorem ordinary_hom_eq_corner (w : TensorWordAt ℓ β) (M : GFin 𝓣) :
    gdimPoly (homGrade T (ordinaryProjectiveAt Λ C hQ β w).grading M.grading) =
      gdimPoly (idem M.grading (ordinaryLoadingIdem (Q := Q) Λ β w)) := by
  rcases w with ⟨w,rfl⟩
  let := tensorProductAlgebra_finite Λ w.content.toMultiset hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G w.content.toMultiset)
  rw [← projectiveHomPolynomial_of]
  exact projectiveHomPolynomial_ofIdempotent _ _ (isIdempotentElem_mk_e w.loading w.blocks_redOrdered)
    (mk_e_mem_tensorProductGrade G _ w.loading w.blocks_redOrdered)

omit [Finite I] in
private theorem ordinary_factor (w : TensorWordAt ℓ β) :
    K0.of (ordinaryProjectiveAt Λ C hQ β w) = KL2.divQFact2 C w.1.blackBlocks • projectiveWordAt Λ C hQ β w := by
  rcases w with ⟨w,rfl⟩
  exact tensorWordProjective_factorial Λ C hQ w

private def homTest (M : GFin 𝓣) : P →ₛₗ[qToV] 𝕂 := by
  let := tensorProductAlgebra_finite Λ β hQ
  let := HasGdim.of_finiteDimensional 𝓣
  exact { toFun := fun x => qToV (projectiveCharacter 𝓣 M x)
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }

omit [Finite I] in
private theorem homTest_of (M : GFin 𝓣) (p : GProj 𝓣) :
    homTest Λ C hQ β M (K0.of p) = integralLaurentEval (gdimPoly (homGrade T p.grading M.grading)) := by
  let := tensorProductAlgebra_finite Λ β hQ
  let := HasGdim.of_finiteDimensional 𝓣
  change qToV (LaurentPolynomial.invert (projectiveHomPolynomial 𝓣 M (K0.of p))) = _
  rw [projectiveHomPolynomial_of, ← CycKLR.integralEval_invert]
  exact congrArg integralLaurentEval (LaurentPolynomial.invert.symm_apply_apply _)

variable {J : Type*} (S : J → GFin (tensorProductGrade
  (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) β))
  (test : J → TensorSpace wt →ₗ[RatFunc ℚ] RatFunc ℚ)

/-- The tensor coordinates on the integral weight lattice in the bar coproduct convention. -/
abbrev barWeightCoordinates (v : V) : J → 𝕂 := fun j => test j ((tensorCoproductEquiv hR wt).symm (v : TensorSpace wt))

/-- An ordinary graded Hom shuffle computation and a finite rank upper
bound suffice to identify the entire divided-word block integrally. The
observations need separate only its tensor weight lattice. -/
theorem exists_wordEquivAt_of_shuffle
    (separates : Function.Injective (barWeightCoordinates C wt hR β test))
    (shuffle : ∀ (w : TensorWordAt ℓ β) j,
      integralLaurentEval (gdimPoly (homGrade T (ordinaryProjectiveAt Λ C hQ β w).grading (S j).grading)) =
        test j (barOrdinaryWord w.1 wt))
    (upper : Module.Finite LP V → Module.finrank LP P ≤ Module.finrank LP V) :
    ∃ e : P ≃ₛₗ[invLP.toRingHom] V, ∀ w : TensorWordAt ℓ β,
      e (projectiveWordAt Λ C hQ β w) = vectorWordAt C wt hR β w := by
  let := tensorProductAlgebra_finite Λ β hQ
  let := HasGdim.of_finiteDimensional 𝓣
  let p := projectiveWordAt Λ C hQ β
  let v := vectorWordAt C wt hR β
  let H (x : P) (j : J) := homTest Λ C hQ β (S j) x
  let t := barWeightCoordinates C wt hR β test
  have hword (w : TensorWordAt ℓ β) : H (p w) = t (v w) := by
    funext j
    let c := KL2.divQFact2 C w.1.blackBlocks
    apply smul_right_injective 𝕂 (KL2Gamma.qToV_divQFact2_ne_zero C w.1.blackBlocks)
    change qToV c • (homTest Λ C hQ β (S j) (p w)) = qToV c • test j ((tensorCoproductEquiv hR wt).symm (tensorWordVector w.1 wt))
    rw [← (homTest Λ C hQ β (S j)).map_smulₛₗ, ← ordinary_factor, homTest_of, shuffle,
      ← (test j).map_smul, ← (tensorCoproductEquiv hR wt).symm.map_smul]
    apply congrArg (test j)
    apply (tensorCoproductEquiv hR wt).injective
    rw [tensorCoproductEquiv_ordinary, LinearEquiv.apply_symm_apply, tensorWordVector_factorial]
  have htadd (x y : V) : t (x+y) = t x + t y := by
    ext j
    change test j ((tensorCoproductEquiv hR wt).symm ((x : TensorSpace wt) + y)) = _
    simp only [map_add]
    rfl
  have htsmul (c : LP) (y : V) : t (invLP c • y) = qToV c • t y := by
    ext j
    change test j ((tensorCoproductEquiv hR wt).symm (LaurentPolynomial.invert c • (y : TensorSpace wt))) = _
    rw [tensor_laurent_smul, CycKLR.integralEval_invert, map_smul, map_smul]
    rfl
  have hHadd (x y : P) : H (x+y) = H x + H y := by ext j; exact (homTest Λ C hQ β _).map_add _ _
  have hHsmul (c : LP) (x : P) : H (c • x) = qToV c • H x := by ext j; exact (homTest Λ C hQ β _).map_smulₛₗ _ _
  have lifts (x : P) : ∃ z : V, H x = t z := by
    have hx : x ∈ Submodule.span LP (Set.range p) := by rw [span_projectiveWordAt]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w,rfl⟩ := hx; exact ⟨v w,hword w⟩
    | zero =>
      refine ⟨0,?_⟩
      ext j
      change homTest Λ C hQ β _ 0 = test j ((tensorCoproductEquiv hR wt).symm 0)
      simp
    | add x y _ _ hx hy =>
      obtain ⟨a,ha⟩ := hx
      obtain ⟨b,hb⟩ := hy
      exact ⟨a+b, by rw [hHadd,htadd,ha,hb]⟩
    | smul c x _ hx =>
      obtain ⟨y,hy⟩ := hx
      exact ⟨invLP c • y, by rw [hHsmul, htsmul,hy]⟩
  choose g hg using lifts
  let f : P →ₛₗ[invLP.toRingHom] V :=
    { toFun := g
      map_add' := fun x y => separates (by change t (g (x+y)) = t (g x + g y); rw [← hg, htadd, ← hg, ← hg, hHadd])
      map_smul' := fun c x => separates (by change t (g (c • x)) = t (invLP c • g x); rw [← hg,htsmul,← hg,hHsmul]) }
  have hf (w) : f (p w) = v w := separates ((hg _).symm.trans (hword w))
  have hs : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← span_vectorWordAt (C := C) wt hR β]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact ⟨p w,hf w⟩
  have := finite_indec 𝓣
  let := Module.Finite.of_basis (K0.indecBasis 𝓣)
  have hfinite := Module.Finite.of_surjective f hs
  have hi : Function.Injective f := injective_of_rank_le (k := F) (A := T) (N := V) 𝓣 f hs (upper hfinite)
  exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, hf⟩

end Words
section LastRed
open KLR QuantumGroup LieLean LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {F Y : Type*} [DecidableEq I] [Field F] [AddCommGroup Y] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) F} (Λ : Fin (ℓ+1) → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} (β : Multiset I)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The last-red projective rank bound counts a finite set of pairs of shift
classes, even over a non-algebraically-closed field. -/
theorem finrank_le_lastRedPairs :
    Module.finrank LP (K0 (tensorProductGrade G β)) ≤
      Nat.card (Σ u : LastRedWeightSplit β, LastRedFactorClasses Λ β G u) := by
  classical
  have : Finite (LastRedWeightSplit β) :=
    Finite.of_injective (fun u : LastRedWeightSplit β =>
      (⟨u.1, by simpa using u.2⟩ : ↥(β.antidiagonal.toFinset))) (fun _ _ h => Subtype.ext (congrArg (fun x : ↥(β.antidiagonal.toFinset) => x.val) h))
  have : ∀ u : LastRedWeightSplit β, Finite (LastRedFactorClasses Λ β G u) := fun u => by
    let := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) u.1.1 hQ
    let := CycKLR.module_finite (ν := u.1.2) (Q := Q) (fun i j hij => by
      obtain ⟨c,hc,he⟩ := hQ.polyInY_leading i j hij
      rw [he]
      exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := F) (Λ (Fin.last ℓ) i))
    let 𝓔 := tensorProductGrade (restrictRedGrading Q Λ G) u.1.1
    let 𝓕 := CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) u.1.2
    let := HasGdim.of_finiteDimensional 𝓔
    let := HasGdim.of_finiteDimensional 𝓕
    have := finite_indec 𝓔
    have := finite_indec 𝓕
    exact inferInstanceAs (Finite (IndecClass 𝓔 × IndecClass 𝓕))
  let := tensorProductAlgebra_finite Λ β hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G β)
  rw [Module.finrank_eq_nat_card_basis (K0.indecBasis (tensorProductGrade G β))]
  exact Nat.card_le_card_of_injective _ (lastRedRankEmbedding Λ β hQ G).injective

variable [Finite I] (wt : Fin (ℓ+1) → Dom R) (hR : R.IsXRegular)

/-- Standard Hom tests for ordinary loadings suffice in all black contents.
The numerical hypothesis concerns only the two factor ranks; the categorical
rank estimate is supplied by the last-red filtration. -/
theorem exists_tensorWordEquiv_of_lastRedShuffle
    {J : Multiset I → Type*} (S : ∀ β, J β → GFin (tensorProductGrade G β))
    (test : ∀ β, J β → TensorSpace wt →ₗ[RatFunc ℚ] RatFunc ℚ)
    (separates : ∀ β, Function.Injective (barWeightCoordinates C wt hR β (test β)))
    (shuffle : ∀ (β : Multiset I) (w : TensorWordAt (ℓ+1) β) j,
      integralLaurentEval (gdimPoly (idem (S β j).grading (ordinaryLoadingIdem (Q := Q) Λ β w))) =
        test β j (barOrdinaryWord w.1 wt))
    (factors : ∀ β : Multiset I, Module.Finite LP (integralTensorWeight wt hR β.toFinsupp) →
      Nat.card (Σ u : LastRedWeightSplit β, LastRedFactorClasses Λ β G u) ≤
      Module.finrank LP (integralTensorWeight wt hR β.toFinsupp)) :
    ∃ e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade G β)) ≃ₛₗ[invLP.toRingHom] integralTensor wt,
      ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w := by
  apply (exists_tensorWordEquiv_iff Λ C hQ wt hR).2
  intro β
  apply (exists_wordEquivAt_iff Λ C hQ wt hR β).1
  exact exists_wordEquivAt_of_shuffle Λ C hQ wt hR β (S β) (test β) (separates β)
    (fun w j => by rw [ordinary_hom_eq_corner]; exact shuffle β w j) (fun hfin => (finrank_le_lastRedPairs Λ C hQ β).trans (factors β hfin))

end LastRed

end Categorification.Stendhal.FirstWeight
