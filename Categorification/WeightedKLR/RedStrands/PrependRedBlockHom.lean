/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedBlocks

/-!
# Adding a red strand on the left commutes with the block maps

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.3, for the comparison of `T̃^λ` with `T^{(λ₀, λ)}`. Adding the red strand `λ₀`
on the left of a diagram of `T̃^λ` sends the block map of the block `b_j` to the block map of
the block `j + 1` of `0, b_0, …, b_ℓ` (`StendhalAlgebra.prependBlockVal_eq`): both place a
KLR diagram of weight `b_j` on the same strands, one position further right after adding `λ₀`.
Restricted to the corners of `e_α` and `e_{(0, α)}`, adding the red strand is a unital algebra
map (`StendhalAlgebra.prependRedCorner`).

## Main definitions

* `KLR.nonUnitalCornerHom`: the restriction of a non-unital algebra map to corners.
* `StendhalAlgebra.prependRedCorner`: adding the red strand,
  `e_α T̃^λ e_α → e_{(0,α)} T̃^{(λ₀, λ)} e_{(0,α)}`.

## Main results

* `KLRAlgebra.nonUnitalRingHom_eq_of_generators`: maps out of a KLR algebra agreeing on
  scalars and on the generators agree.
* `StendhalAlgebra.val_val_blockHom_e`, `val_val_blockHom_x`, `val_val_blockHom_ψ`: the block
  maps on generators.
* `StendhalAlgebra.prependBlockVal_eq`.
-/

noncomputable section

namespace Categorification.KLR

variable {k : Type*} [CommRing k] {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]

section CornerHom

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- **The restriction of a non-unital algebra map to corners**: `f : R → S` with `f E = E'`
restricts to a unital algebra map `E R E → E' S E'`. -/
def nonUnitalCornerHom (f : R →ₙₐ[k] S) {E : R} (hE : IsIdempotentElem E) {E' : S}
    (hE' : IsIdempotentElem E') (h : f E = E') : hE.Corner →ₐ[k] hE'.Corner where
  toFun a := Corner.mk (f a.val) (by rw [← h, ← map_mul, ← map_mul, Corner.E_mul_val_mul_E])
  map_one' := Corner.ext (by simp [h])
  map_mul' a b := Corner.ext (by simp)
  map_zero' := Corner.ext (by simp)
  map_add' a b := Corner.ext (by simp)
  commutes' c := Subtype.ext (by
    show f (c • E) = c • E'
    rw [map_smul, h])

@[simp] theorem val_nonUnitalCornerHom (f : R →ₙₐ[k] S) {E : R} (hE : IsIdempotentElem E)
    {E' : S} (hE' : IsIdempotentElem E') (h : f E = E') (a : hE.Corner) :
    (nonUnitalCornerHom f hE hE' h a).val = f a.val := rfl

end CornerHom

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

omit [Algebra k R] in
/-- Non-unital ring maps out of `R(ν)` agreeing on scalars and on the generators agree. -/
theorem nonUnitalRingHom_eq_of_generators (f g : KLRAlgebra k Q ν →ₙ+* R)
    (hc : ∀ c, f (algebraMap k _ c) = g (algebraMap k _ c)) (he : ∀ i, f (e i) = g (e i))
    (hx : ∀ a, f (x a) = g (x a)) (hψ : ∀ j, f (ψ j) = g (ψ j)) (z : KLRAlgebra k Q ν) :
    f z = g z := by
  obtain ⟨w, rfl⟩ := mk_surjective z
  induction w using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, hc]
  | grade1 g' =>
    cases g' with
    | idem i => exact he i
    | dot a => exact hx a
    | cross j => exact hψ j
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end KLRAlgebra

end Categorification.KLR

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

namespace StendhalAlgebra

section Corner

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- **Adding the red strand on corners**: `e_α T̃^λ e_α → e_{(0, α)} T̃^{(λ₀, λ)} e_{(0, α)}`. -/
def prependRedCorner (α : Fin ℓ → I → ℕ) :
    (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) α).Corner →ₐ[k]
      (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (Fin.cons (0 : I → ℕ) α)).Corner :=
  nonUnitalCornerHom (prependRedStendhal Q Λ ν) _ _ (prependRedStendhal_rootIdem Q Λ ν α)

theorem val_prependRedCorner (α : Fin ℓ → I → ℕ)
    (a : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) α).Corner) :
    (prependRedCorner Q Λ ν α a).val = prependRedStendhal Q Λ ν a.val := rfl

end Corner

variable {Q Λ ν}

section General

variable {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {b' : Fin (ℓ' + 1) → Multiset I}

/-- The block map on an idempotent: the sum of the idempotents of its fibre. -/
theorem val_val_blockHom_e (hb : blockPrefix b' (ℓ' + 1) = ν) (j : ℕ) (hj : j < ℓ' + 1)
    (i : Seq (b' ⟨j, hj⟩)) :
    (blockHom Q Λ' hb j hj (KLRAlgebra.e i)).val.val =
      ∑ s ∈ (blockEmb hb j hj).F (Seq.map Sum.inl i), StendhalAlgebraAllOrders.e s := by
  rw [val_val_blockHom]
  erw [KLRAlgebra.reindexEquiv_e]
  rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, eSum, map_sum]
  rfl

/-- The block map on a dot. -/
theorem val_val_blockHom_x (hb : blockPrefix b' (ℓ' + 1) = ν) (j : ℕ) (hj : j < ℓ' + 1)
    (a : Fin (Multiset.card (b' ⟨j, hj⟩))) :
    (blockHom Q Λ' hb j hj (KLRAlgebra.x a)).val.val =
      StendhalAlgebraAllOrders.x ((blockEmb hb j hj).pos (Fin.cast (Multiset.card_map _ _).symm a)) *
        ∑ s ∈ rootSet ν (blockRoot b'), StendhalAlgebraAllOrders.e s := by
  rw [val_val_blockHom]
  erw [KLRAlgebra.reindexEquiv_x]
  rw [BlockEmb.hom_x, val_polCorner, pol_X, map_mul, eSum, map_sum]
  rfl

/-- The block map on a crossing inside the block. -/
theorem val_val_blockHom_ψ (hb : blockPrefix b' (ℓ' + 1) = ν) (j : ℕ) (hj : j < ℓ' + 1)
    {l : ℕ} (hl : l + 1 < Multiset.card (b' ⟨j, hj⟩)) :
    (blockHom Q Λ' hb j hj (KLRAlgebra.ψ l)).val.val =
      StendhalAlgebraAllOrders.ψ (blockStart b' j + l) *
        ∑ s ∈ rootSet ν (blockRoot b'), StendhalAlgebraAllOrders.e s := by
  rw [val_val_blockHom]
  erw [KLRAlgebra.reindexEquiv_ψ]
  rw [BlockEmb.hom_ψ, BlockEmb.val_gψ _ (by rw [Multiset.card_map]; exact hl), map_mul, eSum,
    map_sum]
  rfl

/-- The block map on a crossing leaving the block is zero. -/
theorem val_val_blockHom_ψ_of_not_lt (hb : blockPrefix b' (ℓ' + 1) = ν) (j : ℕ)
    (hj : j < ℓ' + 1) {l : ℕ} (hl : ¬ l + 1 < Multiset.card (b' ⟨j, hj⟩)) :
    (blockHom Q Λ' hb j hj (KLRAlgebra.ψ l)).val.val = 0 := by
  rw [val_val_blockHom]
  erw [KLRAlgebra.reindexEquiv_ψ]
  rw [BlockEmb.hom_ψ, BlockEmb.gψ_of_not_lt _ (by rw [Multiset.card_map]; exact hl)]
  exact map_zero _

end General

section BlockHom

variable (b : Fin (ℓ + 1) → Multiset I) (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1)

omit [DecidableEq I] in
theorem blockPrefix_consBlocks_eq (b : Fin (ℓ + 1) → Multiset I)
    (hb : blockPrefix b (ℓ + 1) = ν) : blockPrefix (consBlocks b) (ℓ + 1 + 1) = ν :=
  (blockPrefix_consBlocks b (ℓ + 1)).trans hb

/-- Adding the red strand to the block map of `b_j`, as a map into the ambient algebra. -/
def prependBlockVal : KLRAlgebra k Q (b ⟨j, hj⟩) →ₙ+* StendhalAlgebraAllOrders k Q Λ ν :=
  (KLR.cornerVal _).comp ((prependRedStendhal Q Λ ν :
      StendhalAlgebra k Q (Λ ∘ Fin.succ) ν →ₙ+* StendhalAlgebra k Q Λ ν).comp
    ((KLR.cornerVal _).comp (blockHom Q (Λ ∘ Fin.succ) hb j hj).toRingHom.toNonUnitalRingHom))

/-- The block map of the block `j + 1` of `0, b_0, …, b_ℓ`, with the source `b_j`. -/
def consBlockHom : KLRAlgebra k Q (b ⟨j, hj⟩) →ₐ[k]
    (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot (consBlocks b))).Corner :=
  blockHom Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb) (j + 1) (Nat.succ_lt_succ hj)

/-- The block map of the block `j + 1` of `0, b_0, …, b_ℓ`, into the ambient algebra. -/
def consBlockVal : KLRAlgebra k Q (b ⟨j, hj⟩) →ₙ+* StendhalAlgebraAllOrders k Q Λ ν :=
  (KLR.cornerVal _).comp ((KLR.cornerVal _).comp
    (consBlockHom b hb j hj).toRingHom.toNonUnitalRingHom)

theorem prependBlockVal_apply (z : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    prependBlockVal b hb j hj z =
      (prependRedStendhal Q Λ ν (blockHom Q (Λ ∘ Fin.succ) hb j hj z).val).val := rfl

theorem consBlockVal_apply (z : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    consBlockVal (Q := Q) (Λ := Λ) b hb j hj z =
      (consBlockHom (Q := Q) (Λ := Λ) b hb j hj z).val.val := rfl

omit [DecidableEq I] in
theorem blockStart_consBlocks_succ : blockStart (consBlocks b) (j + 1) = blockStart b j + 1 :=
  blockStart_consBlocks b j

/-- The fibres of the block `j + 1` of `0, b_0, …, b_ℓ` are those of `b_j`, with `λ₀` added. -/
theorem blockEmb_F_consBlocks (i : Seq (b ⟨j, hj⟩)) :
    (blockEmb (b := consBlocks b) (blockPrefix_consBlocks_eq b hb) (j + 1)
        (Nat.succ_lt_succ hj)).F (Seq.map Sum.inl i) =
      ((blockEmb hb j hj).F (Seq.map Sum.inl i)).map
        ⟨prependRedLoading, prependRedLoading_injective⟩ := by
  change (rootSet ν (blockRoot (consBlocks b))).filter _ = _
  rw [blockRoot_consBlocks, rootSet_cons, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun s _ => ?_
  simp only [Function.comp_apply, Function.Embedding.coeFn_mk]
  refine (finCongr (by rw [Multiset.card_map, Multiset.card_map]; rfl)).forall_congr fun a => ?_
  change (prependRedLoading s).lbl _ = Sum.inl _ ↔ s.lbl _ = Sum.inl _
  have ha : a.val < Multiset.card (b ⟨j, hj⟩) := by
    have h1 := a.2
    have h2 : Multiset.card ((consBlocks b ⟨j + 1, Nat.succ_lt_succ hj⟩).map
      (Sum.inl : I → I ⊕ Fin (ℓ + 1))) = Multiset.card (b ⟨j, hj⟩) := Multiset.card_map _ _
    omega
  have hE := blockEnd_le hb hj
  rw [Multiset.card_map] at hE
  rw [show KLRAlgebra.windowPos (blockStart (consBlocks b) (j + 1)) _ a =
      prependRedPosition ⟨blockStart b j + a.val, by omega⟩ from
    Fin.ext (by simp only [KLRAlgebra.windowPos, prependRedPosition_val, blockStart_consBlocks]; omega),
    prependRedLoading_lbl]
  exact (prependRedColor_injective ℓ).eq_iff' rfl

theorem consBlockVal_e (i : Seq (b ⟨j, hj⟩)) :
    consBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.e i) =
      ∑ s ∈ (blockEmb hb j hj).F (Seq.map Sum.inl i),
        StendhalAlgebraAllOrders.e (prependRedLoading s) := by
  rw [consBlockVal_apply, consBlockHom]
  refine (val_val_blockHom_e (Q := Q) (Λ' := Λ) (b' := consBlocks b)
    (blockPrefix_consBlocks_eq b hb) (j + 1) (Nat.succ_lt_succ hj) i).trans ?_
  erw [blockEmb_F_consBlocks b hb j hj i, Finset.sum_map]
  rfl

theorem prependBlockVal_e (i : Seq (b ⟨j, hj⟩)) :
    prependBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.e i) =
      ∑ s ∈ (blockEmb hb j hj).F (Seq.map Sum.inl i),
        StendhalAlgebraAllOrders.e (prependRedLoading s) := by
  rw [prependBlockVal_apply]
  change prependRedValue Q Λ ν _ = _
  rw [val_val_blockHom_e, map_sum]
  exact Finset.sum_congr rfl fun s _ => prependRedValue_e Q Λ ν s

theorem firstRedIdem_mul_prependRedValue (z : StendhalAlgebraAllOrders k Q (Λ ∘ Fin.succ) ν) :
    firstRedIdem Q Λ ν * prependRedValue Q Λ ν z = prependRedValue Q Λ ν z :=
  KLR.Corner.E_mul_val _

theorem prependRedValue_sum_rootSet :
    prependRedValue Q Λ ν (∑ s ∈ rootSet ν (blockRoot b), StendhalAlgebraAllOrders.e s) =
      ∑ s ∈ rootSet ν (blockRoot (consBlocks b)), StendhalAlgebraAllOrders.e s := by
  rw [map_sum, blockRoot_consBlocks, rootSet_cons, Finset.sum_map]
  exact Finset.sum_congr rfl fun s _ => prependRedValue_e Q Λ ν s

theorem prependBlockVal_x (a : Fin (Multiset.card (b ⟨j, hj⟩))) :
    prependBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.x a) =
      consBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.x a) := by
  rw [prependBlockVal_apply, consBlockVal_apply, consBlockHom]
  change prependRedValue Q Λ ν _ = _
  refine Eq.trans ?_ (val_val_blockHom_x (Q := Q) (Λ' := Λ) (b' := consBlocks b)
    (blockPrefix_consBlocks_eq b hb) (j + 1) (Nat.succ_lt_succ hj) a).symm
  rw [val_val_blockHom_x, map_mul, ← prependRedValue_sum_rootSet b]
  change (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.x _)).val *
    prependRedValue Q Λ ν _ = _
  rw [prependRedAllOrders_x, mul_assoc, firstRedIdem_mul_prependRedValue]
  congr 2
  apply Fin.ext
  simp only [prependRedPosition_val, BlockEmb.pos_val, Fin.val_cast]
  change blockStart b j + a.val + 1 = blockStart (consBlocks b) (j + 1) + a.val
  rw [blockStart_consBlocks]
  omega

theorem prependBlockVal_ψ (l : ℕ) :
    prependBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.ψ l) =
      consBlockVal (Q := Q) (Λ := Λ) b hb j hj (KLRAlgebra.ψ l) := by
  rw [prependBlockVal_apply, consBlockVal_apply, consBlockHom]
  change prependRedValue Q Λ ν _ = _
  by_cases hl : l + 1 < Multiset.card (b ⟨j, hj⟩)
  · refine Eq.trans ?_ (val_val_blockHom_ψ (Q := Q) (Λ' := Λ) (b' := consBlocks b)
      (blockPrefix_consBlocks_eq b hb) (j + 1) (Nat.succ_lt_succ hj) hl).symm
    have hE := blockEnd_le hb hj
    rw [Multiset.card_map] at hE
    rw [val_val_blockHom_ψ _ _ _ hl, map_mul, ← prependRedValue_sum_rootSet b]
    change (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.ψ _)).val *
      prependRedValue Q Λ ν _ = _
    rw [prependRedAllOrders_ψ Q Λ ν _ (by omega), mul_assoc, firstRedIdem_mul_prependRedValue,
      blockStart_consBlocks]
    congr 2
    omega
  · rw [val_val_blockHom_ψ_of_not_lt _ _ _ hl, map_zero]
    exact (val_val_blockHom_ψ_of_not_lt (Q := Q) (Λ' := Λ) (b' := consBlocks b)
      (blockPrefix_consBlocks_eq b hb) (j + 1) (Nat.succ_lt_succ hj) hl).symm

theorem val_val_algebraMap {A B : Type*} [Ring A] [Algebra k A] {e : A} (he : IsIdempotentElem e)
    {E : he.Corner} (hE : IsIdempotentElem E) [Ring B] [Algebra k B] (f : B →ₐ[k] hE.Corner)
    (c : k) : (f (algebraMap k B c)).val.val = c • (f 1).val.val := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, KLR.Corner.val_smul, KLR.Corner.val_smul]

theorem prependBlockVal_one :
    prependRedValue Q Λ ν (blockHom Q (Λ ∘ Fin.succ) hb j hj 1).val.val =
      (consBlockHom (Q := Q) (Λ := Λ) b hb j hj 1).val.val := by
  rw [map_one, map_one]
  change (prependRedStendhal Q Λ ν (rootIdem Q (Λ ∘ Fin.succ) (blockRoot b))).val =
    (rootIdem Q Λ (blockRoot (consBlocks b))).val
  rw [prependRedStendhal_rootIdem, blockRoot_consBlocks]

theorem prependBlockVal_algebraMap (c : k) :
    prependBlockVal (Q := Q) (Λ := Λ) b hb j hj (algebraMap k _ c) =
      consBlockVal (Q := Q) (Λ := Λ) b hb j hj (algebraMap k _ c) := by
  rw [prependBlockVal_apply, consBlockVal_apply]
  change prependRedValue Q Λ ν _ = _
  rw [val_val_algebraMap, val_val_algebraMap, prependRedValue_smul]
  exact congrArg (c • ·) (prependBlockVal_one b hb j hj)

/-- **Adding the red strand on the left commutes with the block maps**: it sends the block map
of `b_j` to the block map of the block `j + 1` of `0, b_0, …, b_ℓ`. -/
theorem prependBlockVal_eq (z : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    prependBlockVal (Q := Q) (Λ := Λ) b hb j hj z = consBlockVal (Q := Q) (Λ := Λ) b hb j hj z :=
  KLRAlgebra.nonUnitalRingHom_eq_of_generators _ _ (prependBlockVal_algebraMap b hb j hj)
    (fun i => (prependBlockVal_e b hb j hj i).trans (consBlockVal_e b hb j hj i).symm)
    (prependBlockVal_x b hb j hj) (prependBlockVal_ψ b hb j hj) z

end BlockHom

end StendhalAlgebra

end Categorification.Stendhal
