/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedK0
import Categorification.WeightedKLR.RedStrands.TensorWordSpanning
import Categorification.WeightedKLR.RedStrands.TensorWordFirstRed

/-!
# Divided word projectives of `T̃^λ` and the functor `𝔯_N`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 4.39. A divided red/black word `w` gives a graded projective `P̃_w` of `T̃^λ`: the
image of the KLR nilHecke idempotent of its divided blocks, with the Cartan shift. Black blocks
may precede every red strand, since `T̃^λ` has no violating relation.

Extension of scalars along `prependRed` (the functor `𝔯_N`) sends `[P̃_w]` to the class of
the projective of `T^{(λ₀, λ)}` on the word with a red strand added on the left
(`prependRedK0_tildeWordClass`).

## Main definitions

* `tildeProjection` : `KLR → T̃^λ`, the KLR presentation of `T̃^λ`.
* `tildeWordClass` : the class `[P̃_w]`.

## Main results

* `tildeWordClass_factorial` : `[T̃^λ e(w)] = [w]! [P̃_w]`.
* `prependRedK0_tildeWordClass` : `𝔯_N [P̃_w] = [P_{r(w)}]`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KL2 QuantumGroup Categorification.Graded MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} {ℓ : ℕ}

/-! ### Words with a red strand added on the left -/

/-- Adding a red strand on the left puts a red block of size one first and renames the
old red labels. -/
theorem TensorWord.blocks_prependRed : ∀ {n : ℕ} (w : TensorWord I n),
    w.prependRed.blocks = ((Sum.inr 0 : I ⊕ Fin (n + 1)), 1) :: w.blocks.map (Prod.map (prependRedColor n) id)
  | _, .empty => rfl
  | n + 1, .red w => by
    change w.prependRed.blocks.map (Prod.map (addRedColor (n + 1)) id) ++
      [(.inr (Fin.last (n + 1)), 1)] = _
    rw [TensorWord.blocks_prependRed w]
    change _ = (Sum.inr 0, 1) :: (w.blocks.map (Prod.map (addRedColor n) id) ++
      [((Sum.inr (Fin.last n) : I ⊕ Fin (n + 1)), 1)]).map (Prod.map (prependRedColor (n + 1)) id)
    simp only [List.map_cons, List.map_append, List.map_map, List.cons_append, List.map_cons,
      List.map_nil]
    refine congrArg₂ _ rfl (congrArg₂ _ ?_ ?_)
    · refine List.map_congr_left fun q _ => ?_
      rcases q with ⟨i | r, a⟩ <;> rfl
    · rfl
  | _, .black w i a => by
    change w.prependRed.blocks ++ [(Sum.inl i, a)] = _
    rw [TensorWord.blocks_prependRed w]
    show _ = _ :: List.map (Prod.map (prependRedColor _) id) (w.blocks ++ [(Sum.inl i, a)])
    simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append]
    rfl

theorem TensorWord.blackBlocks_prependRed : ∀ {n : ℕ} (w : TensorWord I n),
    w.prependRed.blackBlocks = w.blackBlocks
  | _, .empty => rfl
  | _, .red w => TensorWord.blackBlocks_prependRed w
  | _, .black w i a => by
    change w.prependRed.blackBlocks ++ [(i, a)] = w.blackBlocks ++ [(i, a)]
    rw [TensorWord.blackBlocks_prependRed w]

private theorem expandDiv_map_prepend (n : ℕ) (d : List ((I ⊕ Fin n) × ℕ)) :
    expandDiv (d.map (Prod.map (prependRedColor n) id)) = (expandDiv d).map (prependRedColor n) := by
  induction d with
  | nil => rfl
  | cons q d ih =>
    simp only [expandDiv, List.map_cons, List.flatMap_cons, Prod.map_fst, Prod.map_snd, id_eq,
      List.map_append, List.map_replicate] at ih ⊢
    rw [ih]

theorem TensorWord.expandDiv_prependRed {n : ℕ} (w : TensorWord I n) :
    expandDiv w.prependRed.blocks = .inr 0 :: (expandDiv w.blocks).map (prependRedColor n) := by
  rw [w.blocks_prependRed, ← expandDiv_map_prepend]
  rfl

variable [DecidableEq I]

omit [DecidableEq I] in
theorem TensorWord.prependRed_blocks_weight (w : TensorWord I ℓ) :
    (expandDiv w.prependRed.blocks : Multiset _) = stendhalWeight (ℓ + 1) w.content.toMultiset := by
  rw [w.prependRed.blocks_weight, w.content_prependRed]

omit [DecidableEq I] in
/-- The loading of the word with a red strand added on the left. -/
theorem TensorWord.ofList_prependRed (w : TensorWord I ℓ) :
    Seq.ofList _ w.prependRed_blocks_weight = prependRedLoading w.loading := by
  apply Subtype.ext
  funext a
  change (Seq.ofList _ w.prependRed_blocks_weight).lbl a = (prependRedLoading w.loading).lbl a
  have hn : (expandDiv w.blocks).length = w.content.toMultiset.card + ℓ := by
    simpa [stendhalWeight] using congrArg Multiset.card w.blocks_weight
  rcases eq_firstPosition_or a with rfl | ⟨b, rfl⟩
  · rw [prependRedLoading_head, Seq.ofList_lbl]
    simp only [getElem_congr_coll w.expandDiv_prependRed]
    rfl
  · rw [prependRedLoading_lbl, Seq.ofList_lbl]
    simp only [getElem_congr_coll w.expandDiv_prependRed, prependRedPosition_val,
      List.getElem_cons_succ, List.getElem_map]
    rfl

/-! ### The KLR presentation of `T̃^λ` -/

variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section Tilde

variable (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "B" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "T̃" => StendhalAlgebra k Q Λ ν

/-- The presentation `KLR → T̃^λ`: all red orders, then the red-ordered corner. -/
def tildeProjection : B →ₐ[k] T̃ :=
  (orderProjection Q Λ ν).comp (StendhalAlgebraAllOrders.ofKLR k Q Λ ν)

variable (G : GradingDatum (stendhalQ Q Λ))

theorem tildeProjection_graded :
    PreservesGrading (G.grade μ) (stendhalGrade G ν) (tildeProjection Λ ν).toLinearMap := by
  intro n x hx
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν x * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈
    allOrdersGrade G ν n
  have he : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ (G.e_mem_grade i)
  simpa only [add_zero, AlgHom.toLinearMap_apply] using SetLike.GradedMul.mul_mem (A := allOrdersGrade G ν)
    (Graded.mem_map_of_mem _ _ hx) he

local instance : Module Bᵐᵒᵖ T̃ := Module.compHom T̃ (tildeProjection Λ ν).toRingHom.op
local instance : SMulCommClass T̃ Bᵐᵒᵖ T̃ where
  smul_comm b r x := (mul_assoc b x (tildeProjection Λ ν r.unop)).symm
local instance : IsScalarTower k Bᵐᵒᵖ T̃ where
  smul_assoc c r x := by
    change x * tildeProjection Λ ν (c • r.unop) = c • (x * tildeProjection Λ ν r.unop)
    rw [map_smul, mul_smul_comm]

/-- Extension of graded projectives from the KLR algebra to `T̃^λ`. -/
def tildeProjectionK0 : K0 (G.grade μ) →ₗ[LaurentPolynomial ℤ] K0 (stendhalGrade G ν) :=
  extensionK0 (G.grade μ) (stendhalGrade G ν) (tildeProjection Λ ν)
    (tildeProjection_graded Λ ν G) (fun _ _ => rfl)

theorem tildeProjectionK0_ofIdempotent {e : B} (he : IsIdempotentElem e) (he₀ : e ∈ G.grade μ 0) :
    tildeProjectionK0 Λ ν G (K0.of (GProj.ofIdempotent e he he₀)) =
      K0.of (GProj.ofIdempotent (𝒜 := stendhalGrade G ν) (tildeProjection Λ ν e)
        (he.map _) (tildeProjection_graded Λ ν G he₀)) :=
  extensionK0_ofIdempotent _ _ _ (tildeProjection_graded Λ ν G) (fun _ _ => rfl) he he₀

end Tilde

/-! ### The divided word projectives -/

section Generic

variable (Λ' : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (G' : GradingDatum (stendhalQ Q Λ'))
  (hs : ∀ a b, G'.degΨ a b = G'.degΨ b a) (hX : ∀ a, G'.degX a = (affineCoverCartan C ℓ).dot a a)

/-- **The divided word projective `[P̃_w]` of `T̃^λ`** (Webster, arXiv:1309.3796v3, proof of
Proposition 4.39): the nilHecke idempotent of the divided blocks of `w`, with its Cartan
shift. -/
def tildeWordClass (w : TensorWord I ℓ) : K0 (stendhalGrade G' w.content.toMultiset) :=
  tildeProjectionK0 Λ' _ G' (K0.of (G'.dividedProjective hs (affineCoverCartan C ℓ) w.blocks
    w.blocks_weight))

include hX in
/-- The undivided word projective is the quantum factorial multiple of the divided one. -/
theorem tildeWordClass_factorial (w : TensorWord I ℓ) :
    K0.of (GProj.ofIdempotent (𝒜 := stendhalGrade G' w.content.toMultiset)
      (tildeProjection Λ' _ (KLRAlgebra.e w.loading))
      ((show IsIdempotentElem (KLRAlgebra.e w.loading) from e_mul_self _).map _)
      (tildeProjection_graded _ _ G' (G'.e_mem_grade _))) =
      divQFact2 C w.blackBlocks • tildeWordClass Λ' C G' hs w := by
  have H := congrArg (tildeProjectionK0 Λ' _ G')
    (G'.of_expanded_eq_factorial hs (affineCoverCartan C ℓ) hX w.blocks w.blocks_weight)
  rw [map_smul, w.blocks_factorial C] at H
  exact (tildeProjectionK0_ofIdempotent _ _ G' (e_mul_self _) _).symm.trans H

end Generic

variable (Λ : Fin (ℓ + 1) → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "di" => fun i => C.dot i i / 2
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "G₀" => restrictFirstRedGrading Q Λ G
local notation "C'" => affineCoverCartan C ℓ

omit [DecidableEq I] in
theorem restrictFirstRedGrading_cross_symm : ∀ a b, (G₀).degΨ a b = (G₀).degΨ b a := by
  rintro (i | r) (j | s)
  · exact congrArg Neg.neg (C.symm i j)
  · rfl
  · rfl
  · rfl

omit [DecidableEq I] in
theorem restrictFirstRedGrading_dot : ∀ a, (G₀).degX a = (C').dot a a := by
  rintro (i | r)
  · rfl
  · exact (CartanDatum.ofGraph_dot_self (⊥ : SimpleGraph (Fin ℓ)) r).symm

/-- The image of a word idempotent under `prependRed` is the idempotent of the word with a
red strand added on the left. -/
private theorem prependRed_tildeProjection_e (w : TensorWord I ℓ) :
    prependRed Q Λ _ (tildeProjection (Λ ∘ Fin.succ) _ (KLRAlgebra.e w.loading)) =
      TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e (Seq.ofList _ w.prependRed_blocks_weight)
        (by rw [w.ofList_prependRed, prependRedLoading_ordered_iff]; exact w.blocks_redOrdered)) := by
  classical
  have hval : (tildeProjection (k := k) (Q := Q) (Λ ∘ Fin.succ) w.content.toMultiset
      (KLRAlgebra.e w.loading)).val =
      StendhalAlgebraAllOrders.e w.loading := by
    change StendhalAlgebraAllOrders.e w.loading * StendhalAlgebraAllOrders.redOrderedIdem k Q _ _ = _
    rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
    exact ite_eq_left_of_eq_true _ _ (eq_true w.blocks_redOrdered)
  rw [prependRed_apply, hval, prependRedAllOrders_e, orderedQuotient_e]
  split_ifs with h
  · congr 1
    congr 1
    exact w.ofList_prependRed.symm
  · exact absurd ((prependRedLoading_ordered_iff _).mpr w.blocks_redOrdered) h

section Extension

variable (ν : Multiset I) (Gr : GradingDatum (stendhalQ Q Λ))

local notation "T̃ν" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "Tν" => TensorProductAlgebra k Q Λ ν

local instance : Module T̃νᵐᵒᵖ Tν := Module.compHom Tν (prependRed Q Λ ν).toRingHom.op
local instance : SMulCommClass Tν T̃νᵐᵒᵖ Tν where
  smul_comm b a x := (mul_assoc b x (prependRed Q Λ ν a.unop)).symm
local instance : IsScalarTower k T̃νᵐᵒᵖ Tν where
  smul_assoc c a x := by
    change x * prependRed Q Λ ν (c • a.unop) = c • (x * prependRed Q Λ ν a.unop)
    rw [map_smul, mul_smul_comm]

/-- `𝔯_N` on the class of an idempotent projective. -/
theorem prependRedK0_ofIdempotent {e : T̃ν} (he : IsIdempotentElem e)
    (he₀ : e ∈ stendhalGrade (restrictFirstRedGrading Q Λ Gr) ν 0) :
    prependRedK0 Q Λ ν Gr (K0.of (GProj.ofIdempotent e he he₀)) =
      K0.of (GProj.ofIdempotent (𝒜 := tensorProductGrade Gr ν) (prependRed Q Λ ν e)
        (he.map _) (prependRed_preservesGrading Q Λ ν Gr he₀)) :=
  extensionK0_ofIdempotent _ _ _ (prependRed_preservesGrading Q Λ ν Gr) (fun _ _ => rfl) he he₀

end Extension

/-- **`𝔯_N [P̃_w] = [P_{r(w)}]`** (Webster, arXiv:1309.3796v3, proof of Proposition 4.39):
extension of scalars along `prependRed` sends the divided word projective of `T̃^λ` to the
divided word projective of `T^{(λ₀, λ)}` on the word with a red strand added on the left. -/
theorem prependRedK0_tildeWordClass (w : TensorWord I ℓ) :
    prependRedK0 Q Λ _ G (tildeWordClass (Λ ∘ Fin.succ) C G₀
      (restrictFirstRedGrading_cross_symm Λ C hQ) w) =
      K0.of (dividedSequenceProj Λ C hQ _ w.prependRed.blocks w.prependRed_blocks_weight) := by
  set ν := w.content.toMultiset
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G ν)
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero _ _ (by rw [h, map_zero])
  apply (isRegular_iff_ne_zero.mpr hn).smul_right_injective (K0 (tensorProductGrade G ν))
  change divQFact2 C w.blackBlocks • _ = divQFact2 C w.blackBlocks • _
  rw [← map_smul, ← tildeWordClass_factorial _ C G₀ _ (restrictFirstRedGrading_dot Λ C hQ)]
  refine (prependRedK0_ofIdempotent Λ _ _ _ _).trans ?_
  have ho : IsRedOrdered (Seq.ofList _ w.prependRed_blocks_weight) := by
    rw [w.ofList_prependRed, prependRedLoading_ordered_iff]; exact w.blocks_redOrdered
  have hf := sequenceProj_eq_factorial Λ C hQ ν w.prependRed.blocks w.prependRed_blocks_weight ho
  have hb : divQFact2 (affineCoverCartan C (ℓ + 1)) w.prependRed.blocks =
      divQFact2 C w.blackBlocks := by
    rw [w.prependRed.blocks_factorial C, w.blackBlocks_prependRed]
  rw [hb] at hf
  refine Eq.trans ?_ hf
  exact K0.of_ofIdempotent_congr (prependRed_tildeProjection_e Λ w) _ _ _ _

end Categorification.Stendhal.FirstWeight
