/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaskComparison
import Categorification.WeightedKLR.RedStrands.LastRedSuffixExponent
import Categorification.WeightedKLR.RedStrands.StandardizationTensorCharacter

/-!
# The standardization character in ordinary tensor-word coordinates

Webster, arXiv:1309.3796v2, §§4.6–4.7 and (5.10). The standardization of a pair
of finite graded modules has the two-factor tensor coordinate on each ordinary word once
the factors realize their individual word coordinates and are supported on their own weights.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded QuantumGroup KL2 LieLean LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
set_option backward.isDefEq.respectTransparency false
universe u
variable {I : Type} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) (θ β : Multiset I)
omit [DecidableEq I] in
private theorem symmQ (h : IsRouquierQ C Q) : KLRSymm Q := fun i j hij => (h.symm i j hij).symm

private abbrev grading := stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "G" => grading Λ C hQ
local notation "Pwt" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "redLast" => (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ+1))
variable (X : GFin (tensorProductGrade (restrictRedGrading Q Λ (grading Λ C hQ)) θ))
  (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ (grading Λ C hQ)) (Λ (Fin.last ℓ)) β))
local notation "N" => GFin.extTensor X Z
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

omit [DecidableEq I] in
private theorem final_head_iff (t : Seq δ) :
    (List.ofFn t.1).head? = some redLast ↔ ¬ IsViolated t := by
  have hn : 0 < (δ).card := by simp [stendhalWeight]
  rw [List.head?_eq_getElem?,List.getElem?_ofFn,dite_eq_left hn,Option.some.injEq]
  change t.lbl ⟨0,hn⟩ = redLast ↔ _
  cases he : t.lbl ⟨0,hn⟩ with
  | inl i =>
    have hv : IsViolated t := ⟨hn,by rw [he]; rfl⟩
    simp [hv]
  | inr r =>
    have hr := parabolicLast_red_eq_last (ℓ := ℓ) β t ⟨0,hn⟩ he
    simp [IsViolated,he,hr]

private theorem final_dim_zero (t : Seq δ) (h : (List.ofFn t.1).head? ≠ some redLast) :
    gdimPoly (Graded.idem Z.grading (parabolicLastCyclotomic Q Λ β (e t))) = 0 := by
  have hv := Classical.not_not.1 (fun hn => h ((final_head_iff β t).2 hn))
  have he : parabolicLastCyclotomic Q Λ β (e t) = 0 :=
    (congrArg (SingleRed.cyclotomicEquiv Q (fun _ => Λ (Fin.last ℓ)) β).symm
      (parabolicLastProjection_e_violated Q Λ β t hv)).trans (map_zero _)
  refine (congrArg (fun e => gdimPoly (Graded.idem Z.grading e)) he).trans ?_
  let := idemDecomposition Z.grading (𝒜 := CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
    (Submodule.zero_mem _)
  let : Subsingleton (idemSubspace k Z.carrier (0 : CycKLR k Q (fun i => Polynomial.X ^ Λ (Fin.last ℓ) i) β)) := ⟨fun x y => Subtype.ext (by
    have hx := mem_idemSubspace.1 x.2
    have hy := mem_idemSubspace.1 y.2
    rw [zero_smul] at hx hy
    exact hx.symm.trans hy)⟩
  ext d
  simp [gdimPoly_apply]
  exact Subsingleton.elim _ _

variable {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (wt : Fin (ℓ+1) → Dom R)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => LieLean.QuantumGroup.IrreducibleModule R v (Subtype.val (wt (Fin.last ℓ)))

/-- Comparing the two factor word evaluations suffices to compare the entire standardization
character with the full ordinary tensor word. All permutations, shifts, and the removal
of violated final-factor summands are computed in the theorem. -/
theorem standardizationWord_eq_factorTensorTest {A B : Type*} (f : A → V₀ →ₗ[RatFunc ℚ] RatFunc ℚ)
    (g : B → V₁ →ₗ[RatFunc ℚ] RatFunc ℚ) (a : A) (b : B)
    (highest : ∀ i, (wt (Fin.last ℓ)).1 (R.coroot i) = (Λ (Fin.last ℓ) i : ℤ))
    (w : TensorWord I (ℓ+1)) (s : Seq (Pwt+δ)) (ho : IsRedOrdered s)
    (hw : List.ofFn s.1 = expandDiv w.blocks)
    (hx : ∀ u, integralLaurentEval (gdimPoly (Graded.idem X.grading
      (parabolicPrefixProjection Q Λ θ (e u.1.split.1)))) =
      f a (prefixMaskVector w wt (ordinaryShuffleEquiv w s hw u).1))
    (hz : ∀ u, integralLaurentEval (gdimPoly (Graded.idem Z.grading
      (parabolicLastCyclotomic Q Λ β (e u.1.split.2)))) =
      g b (finalMaskVector w wt (ordinaryShuffleEquiv w s hw u).1))
    (hf0 : ∀ c, (maskSubword false (lastRedBlackTags w c) : Multiset _) ≠ Pwt →
      f a (prefixMaskVector w wt c) = 0)
    (hg0 : ∀ c, (maskSubword true (lastRedBlackTags w c) : Multiset _) ≠ δ →
      g b (finalMaskVector w wt c) = 0) :
    integralLaurentEval (gdimPoly (Graded.idem
      (standardizationGFin Λ G θ β (symmQ C hQ) N).grading
      (TensorProductAlgebra.mk Q Λ (θ+β) (StendhalAlgebra.e
        (Seq.cast (parabolicInputWeights_add (ℓ := ℓ) θ β) s) ((isRedOrdered_cast_iff _ s).mpr ho))))) =
      factorTensorTest f g a b (tensorSplitLast wt (barOrdinaryWord w wt)) := by
  refine (congrArg integralLaurentEval (gdimPoly_standardization_extTensor Λ G θ β
    (symmQ C hQ) X Z s ho)).trans ?_
  rw [map_sum]
  simp only [map_mul,integralLaurentEval_T]
  refine shuffleSum_eq_factorTensorTest w s wt f g a b hw (fun u => (G).indShuffleDegree u.1 s)
    (fun t => integralLaurentEval (gdimPoly (Graded.idem X.grading (parabolicPrefixProjection Q Λ θ (e t)))))
    (fun t => integralLaurentEval (gdimPoly (Graded.idem Z.grading (parabolicLastCyclotomic Q Λ β (e t)))))
    ?_ ?_ hx hz hf0 hg0
  · intro t ht
    rw [final_dim_zero Λ C hQ β Z t ht,map_zero]
  · intro u
    rw [lastRed_indShuffleDegree hQ Λ u.1 ho ((final_head_iff β u.1.split.2).1 u.2)]
    change shuffleCrossingSum _ (shuffleTags s u.1) = _
    rw [← ordinaryShuffleEquiv_tags w s hw u]
    have hm : Prod.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) (id : Bool → Bool) =
        fun z => (Sum.inl z.1,z.2) := by funext z; cases z; rfl
    simpa only [lastRedBlackTags,List.append_assoc,List.singleton_append,hm] using
      lastRedCrossingSum_eq_suffixMaskExponent C _ _ highest
        ((expandDiv (lastRedWord w).1.blocks).map (addRedColor ℓ))
        (tagMask (lastRedWord w).2 (ordinaryShuffleEquiv w s hw u).1)

end Categorification.Stendhal.FirstWeight
