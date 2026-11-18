/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorModuleIdentification
import Categorification.WeightedKLR.RedStrands.TensorWordRaising
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverSequenceRaising
import Categorification.WeightedKLR.RedStrands.BlackRaising

/-! # Raising under the integral tensor-product identification

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35 and Theorem 4.38.
On an ordered loading the categorical and representation-theoretic raising
operators have the same sum over black-strand deletions. Quantum factorials
then identify their values on divided projectives, which span the integral
Grothendieck group by Lemma 4.37.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KL2 QuantumGroup QuantumGroup.UDot KLGamma Categorification.Graded
  LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "K" => DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)
local notation "D" => I ⊕ Fin ℓ

/-- The canonical comparison with values in the rational tensor space. A grading
shift acts there by the inverse power of the quantum parameter. -/
def tensorModuleVectorMap : K →ₛₗ[qToV] TensorSpace wt where
  toFun x := η x
  map_add' x y := congrArg Subtype.val ((η).map_add x y)
  map_smul' c x := by
    change (↑(η (c • x)) : TensorSpace wt) = _
    rw [(η).map_smulₛₗ,Submodule.coe_smul,tensor_laurent_smul]
    exact congrArg (· • (η x : TensorSpace wt)) (CycKLR.integralEval_invert c)

local notation "V" => tensorModuleVectorMap C hQ hR Λ wt hwt

private theorem compare_expanded (w : TensorWord I ℓ) :
    V (ι w.content.toMultiset (K0.of (sequenceProj G w.loading w.blocks_redOrdered))) =
      tensorWordUndivided w wt := by
  change V (ι w.content.toMultiset (K0.of (sequenceProj G (Seq.ofList _ w.blocks_weight) _))) = _
  rw [tensorWordProjective_factorial Λ C hQ,map_smul,map_smulₛₗ,tensorWordVector_factorial (C := C)]
  apply congrArg
  change ((η (tensorWordProjectiveClass Λ C hQ w)) : TensorSpace wt) = _
  rw [tensorModuleEquiv_word]
  rfl

private theorem expand_singletons {J : Type*} (s : List J) :
    expandDiv (s.map fun j => (j,1)) = s := by induction s <;> simp_all [expandDiv]

private theorem compare_loading {β : Multiset I} (s : List D) (hs : (s : Multiset D) = stendhalWeight ℓ β)
    (ho : IsRedOrdered (Seq.ofList s hs)) :
    V (ι β (projectedSequenceClass Λ C hQ β (Seq.ofList s hs))) = loadingVector wt s := by
  let d := s.map fun j => (j,1)
  have he : expandDiv d = s := expand_singletons s
  let hd := (congrArg ((↑) : List D → Multiset D) he).trans hs
  obtain ⟨w,hw,_⟩ := exists_tensorWord_of_ordered d hd ((Seq.ofList_congr he hd hs).symm ▸ ho)
  have hw' := hw.trans he
  have hν : w.content.toMultiset = β := Multiset.map_injective Sum.inl_injective (add_right_cancel
    (w.blocks_weight.symm.trans ((congrArg ((↑) : List D → Multiset D) hw').trans hs)))
  subst β
  calc
    _ = V (ι w.content.toMultiset (projectedSequenceClass Λ C hQ _ w.loading)) :=
      congrArg (fun t => V (ι _ (projectedSequenceClass Λ C hQ _ t))) (Seq.ofList_congr hw' w.blocks_weight hs).symm
    _ = tensorWordUndivided w wt := by
      rw [projectedSequenceClass_ordered Λ C hQ _ w.loading w.blocks_redOrdered]
      exact compare_expanded C hQ hR Λ wt hwt w
    _ = loadingVector wt s := (loadingVector_expand w wt).symm.trans (congrArg (loadingVector wt) hw')

/-- The canonical comparison of Webster, Theorem 4.38, sends any ordered
undivided sequence projective to the tensor vector read from its loading. -/
theorem tensorModuleEquiv_loading {β : Multiset I} (s : List D) (hs : (s : Multiset D) = stendhalWeight ℓ β)
    (ho : IsRedOrdered (Seq.ofList s hs)) :
    (η (ι β (projectedSequenceClass Λ C hQ β (Seq.ofList s hs))) : TensorSpace wt) = loadingVector wt s :=
  compare_loading C hQ hR Λ wt hwt s hs ho

private theorem compare_occupied {β : Multiset I} (i : I) (s : List D)
    (hs : (s : Multiset D) = {Sum.inl i} + stendhalWeight ℓ β)
    (ho : IsRedOrdered (Seq.ofList s (hs.trans (stendhalWeight_black_cons i β))))
    (hr : s.filterMap Sum.getRight? = List.ofFn id) :
    V (blackRaise G i C hQ (ι ({i}+β) (projectedSequenceClass Λ C hQ _ (Seq.ofList s
        (hs.trans (stendhalWeight_black_cons i β)))))) =
      tensorRepresentation wt (E R v i) (loadingVector wt s) := by
  rw [blackRaise_lof, blackRaiseK0_projectedSequenceClass Λ C hQ β i s hs ho,
    map_list_sum,map_list_sum,tensorRepresentation_E_loading Λ wt hwt i s hr]
  rw [← List.attach_map_val (l := CycKLR.markedWords s)]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  split_ifs with hi
  · rw [map_smul,map_smulₛₗ]
    apply congrArg
    apply compare_loading
    let del : CycKLR.WordDeletion (.inl i) s := ⟨(t.1.1,t.1.2.2),hi ▸ markedWord_split t.2⟩
    exact (isRedOrdered_delete_black del (hs.trans (stendhalWeight_black_cons i β)) _).mpr ho
  · rw [map_zero,map_zero]

private theorem compare_all_loadings {β : Multiset I} (i : I) (s : List D)
    (hs : (s : Multiset D) = stendhalWeight ℓ β) (ho : IsRedOrdered (Seq.ofList s hs))
    (hr : s.filterMap Sum.getRight? = List.ofFn id) :
    V (blackRaise G i C hQ (ι β (projectedSequenceClass Λ C hQ β (Seq.ofList s hs)))) =
      tensorRepresentation wt (E R v i) (V (ι β (projectedSequenceClass Λ C hQ β (Seq.ofList s hs)))) := by
  rw [compare_loading C hQ hR Λ wt hwt s hs ho]
  by_cases hb : i ∈ β
  · obtain ⟨γ,hγ⟩ := Multiset.exists_cons_of_mem hb
    rw [← Multiset.singleton_add] at hγ
    subst β
    exact compare_occupied C hQ hR Λ wt hwt i s (hs.trans (stendhalWeight_black_cons i γ).symm) ho hr
  · rw [blackRaise_lof_of_notMem _ _ _ _ _ hb,map_zero,tensorRepresentation_E_loading Λ wt hwt i s hr]
    have hnone : ∀ t ∈ CycKLR.markedWords s, (Sum.inl i : D) ≠ t.2.1 := by
      intro t ht he
      have hi : (Sum.inl i : D) ∈ s := by rw [markedWord_split ht,he]; simp
      have hm : (Sum.inl i : D) ∈ stendhalWeight ℓ β := hs ▸ (show (Sum.inl i : D) ∈ (s : Multiset D) from hi)
      simp [stendhalWeight,hb] at hm
    rw [← List.attach_map_val (l := CycKLR.markedWords s)]
    simp [fun t : {t // t ∈ CycKLR.markedWords s} => hnone t.1 t.2]

/-- Under Webster's canonical integral identification (arXiv:1309.3796v2,
§4.7, Lemma 4.35 and Theorem 4.38), normalized right-black restriction is
the iterated tensor coproduct action of the raising generator. -/
theorem tensorModuleEquiv_E (i : I) (x : K) :
    (η (blackRaise G i C hQ x) : TensorSpace wt) =
      tensorRepresentation wt (E R v i) (η x : TensorSpace wt) := by
  change V (blackRaise G i C hQ x) = tensorRepresentation wt (E R v i) (V x)
  have hx : x ∈ Submodule.span LP (Set.range (tensorWordProjectiveClass Λ C hQ)) := by
    rw [span_tensorWordProjectiveClass]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,rfl⟩ := hz
    have h := compare_all_loadings C hQ hR Λ wt hwt i (expandDiv w.blocks) w.blocks_weight
      w.blocks_redOrdered w.filterMap_reds
    rw [projectedSequenceClass,dite_eq_left w.blocks_redOrdered,tensorWordProjective_factorial Λ C hQ w,
      map_smul,map_smul,map_smulₛₗ,map_smulₛₗ,map_smul] at h
    exact (isRegular_iff_ne_zero.mpr (KL2Gamma.qToV_divQFact2_ne_zero C w.blackBlocks)).smul_right_inj.mp h
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul a x _ hx => rw [map_smul,map_smulₛₗ,map_smulₛₗ,map_smul,hx]

end Categorification.Stendhal.FirstWeight
