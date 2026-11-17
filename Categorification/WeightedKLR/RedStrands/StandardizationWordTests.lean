/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaskComparison
import Categorification.WeightedKLR.RedStrands.StandardizationTensorCharacter
import Categorification.WeightedKLR.RedStrands.TensorShuffleCriterion

/-!
# Standard tests in each black content

In Webster, arXiv:1309.3796v2, §§4.7, 5 and (5.10), each pair of factor modules gives
a standard module in the sum of their black contents. Its character on ordinary loadings
extends by zero to the other contents, as does the corresponding product of factor tests.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u
variable {I : Type} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
variable (X : GFin (tensorProductGrade (restrictRedGrading Q Λ G) θ))
  (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))

private def zeroTest {A : Type*} [Ring A] [Algebra k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] : GFin 𝒜 where
  toGMod := (GProj.zeroObj 𝒜).toGMod
  finiteDimensional := inferInstanceAs (Module.Finite k (GProj.zeroObj 𝒜).carrier)

/-- The finite graded standard test in any ambient black block. -/
def standardizationTestAt (ν : Multiset I) : GFin (tensorProductGrade G ν) :=
  if h : θ + β = ν then h ▸ standardizationGFin Λ G θ β hsym (X.extTensor Z)
  else zeroTest (tensorProductGrade G ν)

private theorem dim_zeroTest {A : Type*} [Ring A] [Algebra k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (x : A) :
    gdimPoly (Graded.idem (zeroTest 𝒜).grading x) = 0 := by
  let : Subsingleton (zeroTest 𝒜).carrier := inferInstanceAs (Subsingleton (GProj.zeroObj 𝒜).carrier)
  let ℳ := Graded.idem (zeroTest 𝒜).grading x
  have h (d : ℤ) : Module.finrank k (ℳ d) = 0 := Module.finrank_zero_of_subsingleton
  simp [gdimPoly, ℳ, h]
  ext d
  rfl

/-- On another black block all loading multiplicities of the standard test vanish. -/
theorem standardizationTestAt_of_ne {ν : Multiset I} (h : θ+β ≠ ν) (w : TensorWordAt (ℓ+1) ν) :
    gdimPoly (Graded.idem (standardizationTestAt Λ G θ β hsym X Z ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w)) = 0 := by
  rw [standardizationTestAt,dite_eq_right h]
  exact dim_zeroTest _ _

private theorem cast_labels {J : Type*} {a b : Multiset J} (h : a = b) (s : Seq a) :
    List.ofFn (Seq.cast h s).1 = List.ofFn s.1 := by subst b; rfl

private theorem loadingIdem_eq {ν : Multiset I} (w : TensorWordAt (ℓ+1) ν)
    (s : Seq (stendhalWeight (ℓ+1) ν)) (ho : IsRedOrdered s)
    (hw : List.ofFn s.1 = expandDiv w.1.blocks) :
    TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s ho) = ordinaryLoadingIdem (Q := Q) Λ ν w := by
  rcases w with ⟨w,rfl⟩
  have he : s = w.loading := Subtype.ext (List.ofFn_injective (hw.trans (ofFn_loading w).symm))
  subst s
  rfl

/-- An ordinary test loading, regarded as a shuffle of the two parabolic input contents. -/
theorem exists_ordinaryTestLoading (w : TensorWordAt (ℓ+1) (θ+β)) :
    ∃ (s : Seq (α+δ)) (ho : IsRedOrdered s), List.ofFn s.1 = expandDiv w.1.blocks ∧
      (TensorProductAlgebra.mk Q Λ (θ+β) (StendhalAlgebra.e
        (Seq.cast (parabolicInputWeights_add (ℓ := ℓ) θ β) s) ((isRedOrdered_cast_iff _ s).mpr ho))) =
        ordinaryLoadingIdem (Q := Q) Λ (θ+β) w := by
  let H := parabolicInputWeights_add (ℓ := ℓ) θ β
  let E := congrArg (stendhalWeight (ℓ+1)) w.2
  let t := Seq.cast E w.1.loading
  let s := Seq.cast H.symm t
  have ht : IsRedOrdered t := (isRedOrdered_cast_iff _ _).mpr w.1.blocks_redOrdered
  have hs : IsRedOrdered s := (isRedOrdered_cast_iff _ _).mpr ht
  have hw := (cast_labels H.symm t).trans ((cast_labels E _).trans (ofFn_loading w.1))
  exact ⟨s,hs,hw,loadingIdem_eq Λ w _ _ ((cast_labels H s).trans hw)⟩

private theorem partition_contents {J : Type*} (t : List (J × Bool)) :
    (maskSubword false t : Multiset J) + (maskSubword true t : Multiset J) = (t.map Prod.fst : Multiset J) := by
  induction t with
  | nil => simp [maskSubword]
  | cons p t ih =>
    rcases p with ⟨j,b⟩
    cases b
    · rw [show maskSubword false ((j,false)::t) = j :: maskSubword false t by simp [maskSubword],
        show maskSubword true ((j,false)::t) = maskSubword true t by simp [maskSubword]]
      exact (Multiset.cons_add j _ _).trans (congrArg (Multiset.cons j) ih)
    · rw [show maskSubword false ((j,true)::t) = maskSubword false t by simp [maskSubword],
        show maskSubword true ((j,true)::t) = j :: maskSubword true t by simp [maskSubword]]
      exact (Multiset.add_cons j _ _).trans (congrArg (Multiset.cons j) ih)

omit [DecidableEq I] in
private theorem tags_contents (w : TensorWord I (ℓ+1)) (c : Fin (lastRedWord w).2.length → Bool) :
    ((lastRedBlackTags w c).map Prod.fst : Multiset _) = stendhalWeight (ℓ+1) w.content.toMultiset := by
  rw [← w.blocks_weight, lastRedWord_blocks w]
  simp [lastRedBlackTags,List.map_map,Function.comp_def,tagMask,List.map_ofFn]

omit [DecidableEq I] in
/-- A suffix mask supported on both factors forces the total black content to be their sum. -/
theorem fitsLastRedContents_weight (w : TensorWord I (ℓ+1)) (c : Fin (lastRedWord w).2.length → Bool)
    (h : fitsLastRedContents («α» := α) («β» := δ) w c) : θ+β = w.content.toMultiset := by
  obtain ⟨hx,hy⟩ := h
  have he := partition_contents (lastRedBlackTags w c)
  rw [hx,hy,parabolicInputWeights_add,tags_contents] at he
  exact Multiset.map_injective Sum.inl_injective (add_right_cancel he)

variable {Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} {R : D.RootDatum Y} (wt : Fin (ℓ+1) → Dom R)
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance wordTestVNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
local notation "V₀" => TensorSpace (fun j : Fin ℓ => wt (Fin.castSucc j))
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last ℓ)))

/-- Product tests supported at unequal total content vanish on every term in the ordinary word. -/
theorem factorTensorTest_word_of_content_ne {A B : Type*}
    (f : A → V₀ →ₗ[L] L) (g : B → V₁ →ₗ[L] L) (a : A) (b : B) (w : TensorWord I (ℓ+1))
    (h : θ+β ≠ w.content.toMultiset)
    (hf : ∀ c, (maskSubword false (lastRedBlackTags w c) : Multiset _) ≠ α →
      f a (prefixMaskVector w wt c) = 0)
    (hg : ∀ c, (maskSubword true (lastRedBlackTags w c) : Multiset _) ≠ δ →
      g b (finalMaskVector w wt c) = 0) :
    factorTensorTest f g a b (tensorSplitLast wt (barOrdinaryWord w wt)) = 0 := by
  rw [factorTensorTest_barOrdinaryWord]
  apply Finset.sum_eq_zero
  intro c _
  change _ * (f a (prefixMaskVector w wt c) * g b (finalMaskVector w wt c)) = 0
  by_cases hx : (maskSubword false (lastRedBlackTags w c) : Multiset _) = α
  · rw [hg c (fun hy => h (fitsLastRedContents_weight θ β w c ⟨hx,hy⟩)),mul_zero,mul_zero]
  · rw [hf c hx,zero_mul,mul_zero]

end Categorification.Stendhal.FirstWeight
