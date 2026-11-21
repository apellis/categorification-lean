/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleSumDecomp
import Categorification.WeightedKLR.RedStrands.MatEndResIndPi

/-!
# `Eᵢ Fᵢ` on modules of content not containing `i`

Webster, arXiv:1309.3796v3, the commutation relation of Theorem 4.31 on modules, an input of
the proof of Proposition 5.5. On the all-down matrix ring of a content `μ` with `i ∉ μ`, the
functor `Eᵢ` vanishes: every object of `Eᵢ (⊕ O_μ)` has signed content `μ - i`, which has a
negative coefficient at `i`, so its identity factors through no all-down boundary and is zero
(Webster, §4.5, proof of Theorem 4.29; `isZero_blackUp_downSum`). The weight `λ` of content `μ`
then has `n = ⟨i, λ⟩ ≥ 0` (`ip_nonneg_of_notMem`), and the commutation relation
`Eᵢ Fᵢ 1_λ ≅ Fᵢ Eᵢ 1_λ ⊕ 1_λ^{⊕ n}` of Webster's Theorem 4.31 gives, for every right module `M`,
`Eᵢ Fᵢ M ≅ M^{⊕ n}` as modules over the all-down matrix ring
(`blackModuleEFEquivOfNotMem`), naturally in `M` (`blackModuleEFEquivOfNotMem_map`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits QuantumGroup
  QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram
  InductionAlong MulOpposite

open scoped Classical

attribute [local instance] HomTensor.bimodule

theorem contentVector_apply_eq_count (ν : Multiset I') (i : I') :
    contentVector ν i = ν.count i := by
  induction ν using Multiset.induction_on with
  | empty => simp [contentVector]
  | cons j ν ih =>
    by_cases h : i = j
    · subst j; simp [contentVector, ← ih, add_comm]
    · simp [contentVector, Multiset.count_cons_of_ne h, Finsupp.single_eq_of_ne h, ← ih]

namespace DoubleDiagram

universe w u v

section Content

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (t : I → I → kˣ)

local notation "Q" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k t P)

/-- A boundary whose signed content has a negative coefficient has zero identity in the
violating quotient: by the proof of Webster, arXiv:1309.3796v3, Theorem 4.29, its identity
factors through all-down boundaries of the same signed content, and there are none. -/
theorem id_eq_zero_of_signedContent_neg {right : X} (b : DoubleStendhalTriple RD Λ 0 right)
    (i : I) (h : b.val.signedContent i < 0) :
    𝟙 ((violatingFunctor (Q) right).obj b) = 0 := by
  have h1 := id_mem_matchingContentFactorSpan P t b
  have hle : factorSpan k (violatingFunctor (Q) right).obj
      (fun d => d.val.AllDown ∧ contentVector d.val.blackContent = b.val.signedContent) b b ≤
      ⊥ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨d, ⟨_, hd⟩, _, _, rfl⟩
    have := contentVector_apply_eq_count d.val.blackContent i
    rw [hd] at this
    omega
  exact (Submodule.mem_bot k).mp (hle h1)

/-- An object of the idempotent completion of the additive envelope of the violating quotient
all of whose entries have signed content with a negative coefficient at `i` is zero. -/
theorem isZero_of_signedContent_neg {right : X}
    (Z : Karoubi (Mat_ (ViolatingCategory (Q) right))) (i : I)
    (hZ : ∀ j, (Z.X.X j).as.val.signedContent i < 0) : IsZero Z := by
  have hX : IsZero Z.X := by
    rw [IsZero.iff_id_eq_zero]
    ext j j'
    by_cases hj : j = j'
    · subst hj
      rw [Mat_.id_apply_self]
      exact id_eq_zero_of_signedContent_neg P t (Z.X.X j).as i (hZ j)
    · rw [Mat_.id_apply_of_ne _ _ _ hj]
      rfl
  rw [IsZero.iff_id_eq_zero]
  exact Karoubi.hom_ext _ _ (hX.eq_of_tgt _ _)

variable (i : I) (μ : Multiset I)

theorem signedContent_appendUp_sub {lam lam' : X} {b : DoubleStendhalTriple RD Λ 0 lam}
    {c : I →₀ ℤ} (hb : b.val.signedContent = c)
    (h : endWeight RD (Subtype.val ∘ Λ) lam (blackWord [(true, i)]) = lam') :
    (appendRight (blackWord [(true, i)]) (blackWord_redFree _) h b).val.signedContent =
      c - Finsupp.single i 1 := by
  change wordContent (_ ++ _) = _
  rw [wordContent_append, ← DoubleBoundary.signedContent_eq_wordContent, hb]
  simp [blackWord, sub_eq_add_neg]

/-- The objects of `Eᵢ (⊕ O_μ)` have signed content `μ - i`. -/
theorem blackUp_downSum_content_sub (j) :
    (((completionMap (blackAct (Q) [(true, i)]
        (rfl : wt RD (downRightWeight RD Λ μ) [(true, i)] = _))).obj
      ((toKaroubi _).obj (downSum (Q) μ))).X.X j).as.val.signedContent =
      contentVector μ - Finsupp.single i 1 :=
  signedContent_appendUp_sub i ((DoubleBoundary.signedContent_of_allDown _
    (DoubleBoundary.allDown_ofDown _ ((Fintype.equivFin _).symm j).2)).trans
      (congrArg contentVector (DoubleBoundary.blackContent_ofDown _ _)))
    ((endWeight_blackWord RD _ _ _).trans rfl)

/-- **`Eᵢ` vanishes outside the content** (Webster, arXiv:1309.3796v3, §4.5–4.6): for `i ∉ μ`,
`Eᵢ` of the all-down sum of content `μ` is zero. -/
theorem isZero_blackUp_downSum (hi : i ∉ μ) :
    IsZero ((completionMap (blackAct (Q) [(true, i)]
        (rfl : wt RD (downRightWeight RD Λ μ) [(true, i)] = _))).obj
      ((toKaroubi _).obj (downSum (Q) μ))) := by
  refine isZero_of_signedContent_neg P t _ i fun j => ?_
  rw [blackUp_downSum_content_sub, Finsupp.sub_apply, contentVector_apply_eq_count,
    Multiset.count_eq_zero_of_notMem hi, Finsupp.single_eq_same]
  norm_num

/-- For `i ∉ μ`, `Fᵢ Eᵢ` of the all-down sum of content `μ` is zero, so it receives only the
zero morphism. -/
theorem subsingleton_hom_blackDnUp_downSum (hi : i ∉ μ) :
    Subsingleton ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := μ))) ⟶
      (completionMap (blackAct (Q) [dn i, up i] (wt_dn_up RD i (downRightWeight RD Λ μ)))).obj
        ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := μ))))) := by
  have hz := isZero_blackUp_downSum P t i μ hi
  have hz' := (completionMap (blackAct (Q) [dn i]
    ((wt_append RD (downRightWeight RD Λ μ) [dn i] [up i]).symm.trans
      (wt_dn_up RD i (downRightWeight RD Λ μ))))).map_isZero hz
  have e := (completionIso (blackActAppend (Q) [dn i] [up i]
    (rfl : wt RD (downRightWeight RD Λ μ) [(true, i)] = _)
    ((wt_append RD (downRightWeight RD Λ μ) [dn i] [up i]).symm.trans
      (wt_dn_up RD i (downRightWeight RD Λ μ))) (wt_dn_up RD i _))).app
    ((toKaroubi _).obj (downSum (Q) μ))
  exact ⟨fun f g => (hz'.of_iso e).eq_of_tgt f g⟩

/-- For `i ∉ μ`, the weight `λ` of content `μ` has `⟨i, λ⟩ ≥ 0`: the red labels are dominant,
and every black label `j ∈ μ` differs from `i`, so `⟨i, j_X⟩ ≤ 0`. -/
theorem ip_nonneg_of_notMem (hi : i ∉ μ) : 0 ≤ ip RD i (downRightWeight RD Λ μ) := by
  have h1 : 0 ≤ RD.pair (RD.iY i) (List.ofFn (Subtype.val ∘ Λ)).sum := by
    rw [map_list_sum]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨r, rfl⟩ := (List.mem_ofFn' _ _).mp hy
      exact (Λ r).property i
  have h2 : RD.pair (RD.iY i) (μ.map RD.iX).sum ≤ 0 := by
    rw [map_multiset_sum, Multiset.map_map]
    refine (Multiset.sum_le_card_nsmul _ 0 fun x hx => ?_).trans (by simp)
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hx
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    change RD.pair (RD.iY i) (RD.iX j) ≤ 0
    rw [RD.pair_iY_iX]
    exact Int.ediv_nonpos_of_nonpos_of_neg (by linarith [C.dot_nonpos i j hij])
      (C.dot_self_pos i)
  change 0 ≤ RD.pair (RD.iY i) ((List.ofFn (Subtype.val ∘ Λ)).sum - (μ.map RD.iX).sum)
  rw [map_sub]
  omega

/-- **`Eᵢ Fᵢ` outside the content on all modules** (Webster, arXiv:1309.3796v3, Theorem 4.31
and input of the proof of Proposition 5.5): for `i ∉ μ`, with `λ` the weight of content `μ` and
`n = ⟨i, λ⟩ ≥ 0`, `Eᵢ Fᵢ M ≅ M^{⊕ n}` for every right module `M` over the all-down matrix ring
of content `μ`. -/
def blackModuleEFEquivOfNotMem (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    (M : Type (max u v w)) [AddCommGroup M] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M]
    (hi : i ∉ μ) :=
  KLR.Diagram.MatEnd.resIndEquivPiOfSubsingleton
    (blackAct (Q) [(false, i)] (wt_downRightWeight i μ)) (appendDown_injective i)
    (blackAct_downObj (Q) i)
    (blackCompletedAdjunction (Q) hP i (wt_downRightWeight i μ) (wt_upDownRightWeight i μ))
    (completionIso (blackActAppend (Q) [up i] [dn i] (wt_downRightWeight i μ)
      (wt_upDownRightWeight i μ) (wt_up_dn RD i _)))
    (subsingleton_hom_blackDnUp_downSum P t i μ hi)
    (completionMap_eq_id _ (blackAct_nil (Q) _)) M
    (letI := HomTensor.transferModule
      (KLR.Diagram.MatEnd.karoubiMatrixOp (downObj (Q) (ν := μ))) M
    blackModuleSumDecompEF (Q) hP i (downRightWeight RD Λ μ)
      ((toKaroubi _).obj (KLR.Diagram.MatEnd.familySum (downObj (Q) (ν := μ)))) M
      (ip_nonneg_of_notMem i μ hi))

/-- `blackModuleEFEquivOfNotMem` is natural in the module: it carries `Eᵢ Fᵢ f` to `f^n`. -/
theorem blackModuleEFEquivOfNotMem_map (hP : ∀ r : (pres RD k).Rel,
      (Q).lin (blackMirrorLinear RD (Subtype.val ∘ Λ) ((pres RD k).rel r)) = 0)
    {M M₂ : Type (max u v w)} [AddCommGroup M] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M]
    [AddCommGroup M₂] [Module (downwardMatrix (Q) μ)ᵐᵒᵖ M₂]
    (f : M →ₗ[(downwardMatrix (Q) μ)ᵐᵒᵖ] M₂) (hi : i ∉ μ)
    (x : Res (blackMatrixOp P t i μ) (Ind M (blackMatrixOp P t i μ))) :
    blackModuleEFEquivOfNotMem P t i μ hP M₂ hi
        (Res.map (φ := blackMatrixOp P t i μ) (Ind.map (φ := blackMatrixOp P t i μ) f) x) =
      fun s => f (blackModuleEFEquivOfNotMem P t i μ hP M hi x s) := by
  delta blackModuleEFEquivOfNotMem blackModuleSumDecompEF
  apply KLR.Diagram.MatEnd.resIndEquivPiOfSubsingleton_map

end Content

end DoubleDiagram

end Categorification.Stendhal
