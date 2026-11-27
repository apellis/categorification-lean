/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Adding a black strand on the left of `T̃^λ`

B. Webster, arXiv:1309.3796v3, before Proposition 4.39: the functor `F̃_i^*` is the
reflection of `F̃_i` through a horizontal line, which adds the black strand on the left of
every diagram instead of on the right. Diagrams of `T̃^λ` carry no violating relation, so the
new leftmost black strand is compatible with the red-strand relations and keeps red orders.

## Main definitions and results

* `prependBlackLoading` : the loading with a black strand `i` added at the far left.
* `prependBlackStendhal` : the non-unital map `T̃^λ_ν → T̃^λ_{ν+i}`.
* `prependBlackStendhal_e`, `prependBlackStendhal_mem_grade`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type*} {ℓ : ℕ}

section Loadings

variable (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

/-- Adjoining a black strand coloured `i` on the left of the Stendhal weight. -/
theorem stendhalWeight_prependBlack : σᵢ + μ = stendhalWeight ℓ νᵢ := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_singleton]
  ac_rfl

/-- Add the black colour at the left boundary, shifting all other positions by one. -/
def prependBlackLoading (s : Seq μ) : Seq (stendhalWeight ℓ νᵢ) :=
  Seq.cast (stendhalWeight_prependBlack i ν) ((default : Seq σᵢ).append s)

/-- The position of an old strand after adding the black strand on the left. -/
def prependBlackPosition (a : Fin (Multiset.card μ)) :
    Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  Fin.cast (congrArg Multiset.card (stendhalWeight_prependBlack i ν)) (Seq.posR σᵢ a)

@[simp] theorem prependBlackPosition_val (a : Fin (Multiset.card μ)) :
    (prependBlackPosition i ν a).val = a.val + 1 := by
  change (Seq.posR σᵢ a).val = a.val + 1
  rw [Seq.posR_val, Multiset.card_singleton, add_comm]

theorem prependBlackLoading_lbl (s : Seq μ) (a : Fin (Multiset.card μ)) :
    (prependBlackLoading i ν s).lbl (prependBlackPosition i ν a) = s.lbl a := by
  simp only [prependBlackLoading, prependBlackPosition, Seq.cast_apply, Fin.cast_cast,
    Fin.cast_eq_self, Seq.append_posR]

/-- The new left boundary strand carries the black label `i`. -/
theorem prependBlackLoading_lbl_zero (s : Seq μ) (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (ha : a.val = 0) : (prependBlackLoading i ν s).lbl a = .inl i := by
  change ((default : Seq σᵢ).append s).1 (Fin.cast _ a) = _
  rw [Seq.append_apply_lt _ _ _ (by rw [Fin.val_cast, ha, Multiset.card_singleton]; exact one_pos)]
  exact Multiset.mem_singleton.mp ((default : Seq σᵢ).mem _)

theorem eq_prependBlackPosition_of_ne_zero (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (ha : a.val ≠ 0) : ∃ c, a = prependBlackPosition i ν c := by
  have h := a.isLt
  have hc : a.val - 1 < Multiset.card μ := by
    simp only [stendhalWeight, Multiset.card_add, Multiset.card_map, Multiset.card_singleton]
      at h ⊢
    omega
  exact ⟨⟨a.val - 1, hc⟩, Fin.ext (by simp; omega)⟩

theorem prependBlackLoading_ordered (s : Seq μ) (hs : IsRedOrdered s) :
    IsRedOrdered (prependBlackLoading i ν s) := by
  intro a c r t hac har hct
  have hne (b) (r' : Fin ℓ) (hb : (prependBlackLoading i ν s).lbl b = .inr r') : b.val ≠ 0 :=
    fun h0 => Sum.inl_ne_inr ((prependBlackLoading_lbl_zero i ν s b h0).symm.trans hb)
  obtain ⟨a, rfl⟩ := eq_prependBlackPosition_of_ne_zero i ν a (hne a r har)
  obtain ⟨c, rfl⟩ := eq_prependBlackPosition_of_ne_zero i ν c (hne c t hct)
  refine hs a c r t ?_ ((prependBlackLoading_lbl i ν s a).symm.trans har)
    ((prependBlackLoading_lbl i ν s c).symm.trans hct)
  have : (prependBlackPosition i ν a).val < (prependBlackPosition i ν c).val := hac
  simp only [prependBlackPosition_val] at this
  exact Fin.lt_def.mpr (by omega)

end Loadings

section Algebra

variable [DecidableEq I] {k : Type*} [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "S" => stendhalQ Q Λ
local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ

private def prependBlackAmbient : KLRAlgebra k S (σᵢ + μ) →ₐ[k] A :=
  (StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ).comp
    (castKLR S (stendhalWeight_prependBlack i ν)).toAlgHom

/-- The sum of the idempotents of loadings beginning with the new black strand. -/
def initialBlackIdem : A :=
  prependBlackAmbient Q Λ i ν (oneConcat S σᵢ μ)

theorem isIdempotentElem_initialBlackIdem : IsIdempotentElem (initialBlackIdem Q Λ i ν) :=
  (oneConcat_idem (Q := S) (ν := σᵢ) (ν' := μ)).map (prependBlackAmbient Q Λ i ν)

local instance instAlgebraInitialBlackCorner :
    Algebra k (isIdempotentElem_initialBlackIdem Q Λ i ν).Corner :=
  KLR.cornerAlgebra _

private def prependBlackConcatCorner :
    ConcatCorner S σᵢ μ →ₐ[k] (isIdempotentElem_initialBlackIdem Q Λ i ν).Corner where
  toFun z := KLR.Corner.mk (prependBlackAmbient Q Λ i ν z.val) (by
    have hz : oneConcat S σᵢ μ * z.val * oneConcat S σᵢ μ = z.val :=
      (congrArg (· * oneConcat S σᵢ μ) (KLR.Corner.E_mul_val z)).trans
        (KLR.Corner.val_mul_E z)
    simpa only [map_mul, initialBlackIdem] using congrArg (prependBlackAmbient Q Λ i ν) hz)
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  commutes' c := Subtype.ext (by
    change prependBlackAmbient Q Λ i ν (algebraMap k _ c * oneConcat S σᵢ μ) =
      algebraMap k A c * initialBlackIdem Q Λ i ν
    rw [map_mul, AlgHom.commutes]
    rfl)

private def prependBlackKLR :
    KLRAlgebra k S μ →ₐ[k] (isIdempotentElem_initialBlackIdem Q Λ i ν).Corner :=
  (prependBlackConcatCorner Q Λ i ν).comp ((blockR σᵢ μ).hom S)

private theorem prependBlackKLR_val (z : KLRAlgebra k S μ) :
    (prependBlackKLR Q Λ i ν z).val =
      prependBlackAmbient Q Λ i ν (((blockR σᵢ μ).hom S) z).val := rfl

private theorem prependBlackKLR_e (s : Seq μ) :
    (prependBlackKLR Q Λ i ν (KLRAlgebra.e s)).val =
      StendhalAlgebraAllOrders.e (prependBlackLoading i ν s) := by
  have hf : (blockR σᵢ μ).F s = {(default : Seq σᵢ).append s} := by
    classical
    ext t
    change t ∈ Finset.univ.image (fun a : Seq σᵢ => a.append s) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg (·.append s) (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  rw [prependBlackKLR_val, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum,
    Finset.sum_singleton]
  exact congrArg (StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ)
    (castKLR_e (stendhalWeight_prependBlack i ν) _)

private theorem prependBlackKLR_x (a : Fin (Multiset.card μ)) :
    (prependBlackKLR Q Λ i ν (KLRAlgebra.x a)).val =
      StendhalAlgebraAllOrders.x (prependBlackPosition i ν a) * initialBlackIdem Q Λ i ν := by
  rw [prependBlackKLR_val, BlockEmb.hom_x, val_polCorner, pol_X, map_mul]
  congr 1
  exact congrArg (StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ)
    (castKLR_x (stendhalWeight_prependBlack i ν) _)

private theorem prependBlackKLR_ψ {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    (prependBlackKLR Q Λ i ν (KLRAlgebra.ψ j)).val =
      StendhalAlgebraAllOrders.ψ (j + 1) * initialBlackIdem Q Λ i ν := by
  rw [prependBlackKLR_val, BlockEmb.hom_ψ, BlockEmb.val_gψ _ hj, map_mul]
  congr 1
  rw [prependBlackAmbient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_ψ]
  simp [StendhalAlgebraAllOrders.ψ, add_comm]

/-- Add the black strand on the left of a diagram with arbitrary red orders. -/
def prependBlackAllOrders :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] (isIdempotentElem_initialBlackIdem Q Λ i ν).Corner :=
  RingQuot.liftAlgHom k
    ⟨(prependBlackKLR Q Λ i ν).comp (KLRAlgebra.mk k S μ), fun x y h => by
      cases h with
      | klr h =>
        exact congrArg (prependBlackKLR Q Λ i ν) (RingQuot.mkAlgHom_rel k h)
      | red_dot a s ha =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (prependBlackKLR Q Λ i ν (KLRAlgebra.x a)).val *
          (prependBlackKLR Q Λ i ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (prependBlackKLR Q Λ i ν (KLRAlgebra.e s))
        rw [prependBlackKLR_e] at hs
        rw [prependBlackKLR_x, prependBlackKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.x (prependBlackPosition i ν a) *
          (initialBlackIdem Q Λ i ν * StendhalAlgebraAllOrders.e (prependBlackLoading i ν s)) = _
        rw [hs]
        have ha' : ((prependBlackLoading i ν s).lbl (prependBlackPosition i ν a)).isRight := by
          simpa only [prependBlackLoading_lbl] using ha
        exact StendhalAlgebraAllOrders.x_mul_e_of_red (prependBlackPosition i ν a)
          (prependBlackLoading i ν s) ha'
      | red_cross j hj s ha hb =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul, KLR.Corner.val_zero]
        change (prependBlackKLR Q Λ i ν (KLRAlgebra.ψ j)).val *
          (prependBlackKLR Q Λ i ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (prependBlackKLR Q Λ i ν (KLRAlgebra.e s))
        rw [prependBlackKLR_e] at hs
        rw [prependBlackKLR_ψ Q Λ i ν hj, prependBlackKLR_e, mul_assoc]
        change StendhalAlgebraAllOrders.ψ (j + 1) *
          (initialBlackIdem Q Λ i ν * StendhalAlgebraAllOrders.e (prependBlackLoading i ν s)) = _
        rw [hs]
        have hj' : j + 1 + 1 < Multiset.card (stendhalWeight ℓ νᵢ) := by
          simp [stendhalWeight] at hj ⊢
          omega
        have ha' : ((prependBlackLoading i ν s).lbl ⟨j + 1, by omega⟩).isRight := by
          rw [show (⟨j + 1, by omega⟩ : Fin (Multiset.card (stendhalWeight ℓ νᵢ))) =
            prependBlackPosition i ν ⟨j, by omega⟩ from Fin.ext (by simp),
            prependBlackLoading_lbl]
          exact ha
        have hb' : ((prependBlackLoading i ν s).lbl ⟨j + 1 + 1, hj'⟩).isRight := by
          rw [show (⟨j + 1 + 1, hj'⟩ : Fin (Multiset.card (stendhalWeight ℓ νᵢ))) =
            prependBlackPosition i ν ⟨j + 1, hj⟩ from Fin.ext (by simp),
            prependBlackLoading_lbl]
          exact hb
        exact StendhalAlgebraAllOrders.ψ_mul_e_of_red (j + 1) hj' (prependBlackLoading i ν s)
          ha' hb'⟩

private theorem prependBlackAllOrders_ofKLR_eq (z : KLRAlgebra k S μ) :
    prependBlackAllOrders Q Λ i ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z) =
      prependBlackKLR Q Λ i ν z := by
  obtain ⟨w, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem prependBlackAllOrders_ofKLR (z : KLRAlgebra k S μ) :
    (prependBlackAllOrders Q Λ i ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ
        (castKLR S (stendhalWeight_prependBlack i ν) (((blockR σᵢ μ).hom S) z).val) := by
  rw [prependBlackAllOrders_ofKLR_eq]
  rfl

theorem prependBlackAllOrders_e (s : Seq μ) :
    (prependBlackAllOrders Q Λ i ν (StendhalAlgebraAllOrders.e s)).val =
      StendhalAlgebraAllOrders.e (prependBlackLoading i ν s) :=
  (prependBlackAllOrders_ofKLR Q Λ i ν _).trans (prependBlackKLR_e Q Λ i ν s)

/-- `prependBlackAllOrders` as a non-unital ring map into the ambient all-orders algebra. -/
def prependBlackValue : StendhalAlgebraAllOrders k Q Λ ν →ₙ+* A :=
  (KLR.cornerVal (isIdempotentElem_initialBlackIdem Q Λ i ν)).comp
    (prependBlackAllOrders Q Λ i ν).toRingHom.toNonUnitalRingHom

theorem prependBlackValue_e (s : Seq μ) :
    prependBlackValue Q Λ i ν (StendhalAlgebraAllOrders.e s) =
      StendhalAlgebraAllOrders.e (prependBlackLoading i ν s) :=
  prependBlackAllOrders_e Q Λ i ν s

theorem prependBlackValue_smul (c : k) (z : StendhalAlgebraAllOrders k Q Λ ν) :
    prependBlackValue Q Λ i ν (c • z) = c • prependBlackValue Q Λ i ν z := by
  change (prependBlackAllOrders Q Λ i ν (c • z)).val =
    c • (prependBlackAllOrders Q Λ i ν z).val
  rw [AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem prependBlackValue_ordered :
    prependBlackValue Q Λ i ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ) := by
  classical
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  let J := Finset.univ.filter (fun s : Seq μ => IsRedOrdered s)
  let P := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ
  let E := ∑ s ∈ J, (StendhalAlgebraAllOrders.e s : StendhalAlgebraAllOrders k Q Λ ν)
  change P * prependBlackValue Q Λ i ν E = prependBlackValue Q Λ i ν E ∧
    prependBlackValue Q Λ i ν E * P = prependBlackValue Q Λ i ν E
  dsimp only [E]
  simp only [map_sum, prependBlackValue_e]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact (StendhalAlgebraAllOrders.redOrderedIdem_mul_e _).trans
      (ite_eq_left (prependBlackLoading_ordered i ν s (Finset.mem_filter.mp hs).2))
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem _).trans
      (ite_eq_left (prependBlackLoading_ordered i ν s (Finset.mem_filter.mp hs).2))

private theorem prependBlackValue_corner (z : StendhalAlgebra k Q Λ ν) :
    prependBlackValue Q Λ i ν z.val ∈
      Subsemigroup.corner (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ) := by
  let f := prependBlackValue Q Λ i ν
  let E : StendhalAlgebra k Q Λ νᵢ := ⟨_, prependBlackValue_ordered Q Λ i ν⟩
  have hl : E.val * f z.val = f z.val :=
    (map_mul f _ _).symm.trans (congrArg f (KLR.Corner.E_mul_val z))
  have hr : f z.val * E.val = f z.val :=
    (map_mul f _ _).symm.trans (congrArg f (KLR.Corner.val_mul_E z))
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  exact ⟨by rw [← hl, ← mul_assoc]; exact congrArg (· * f z.val) (KLR.Corner.E_mul_val E),
    by rw [← hr, mul_assoc]; exact congrArg (f z.val * ·) (KLR.Corner.val_mul_E E)⟩

/-- Webster's reflected map: add a black strand on the left of a red-ordered diagram
(arXiv:1309.3796v3, before Proposition 4.39). -/
def prependBlackStendhal : StendhalAlgebra k Q Λ ν →ₙₐ[k] StendhalAlgebra k Q Λ νᵢ where
  toFun z := ⟨prependBlackValue Q Λ i ν z.val, prependBlackValue_corner Q Λ i ν z⟩
  map_zero' := Subtype.ext (map_zero (prependBlackValue Q Λ i ν))
  map_add' x y := Subtype.ext (map_add (prependBlackValue Q Λ i ν) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (prependBlackValue Q Λ i ν) x.val y.val)
  map_smul' c z := Subtype.ext (prependBlackValue_smul Q Λ i ν c z.val)

theorem prependBlackStendhal_e (s : Seq μ) (hs : IsRedOrdered s) :
    prependBlackStendhal Q Λ i ν (StendhalAlgebra.e s hs) =
      StendhalAlgebra.e (prependBlackLoading i ν s) (prependBlackLoading_ordered i ν s hs) :=
  Subtype.ext (prependBlackValue_e Q Λ i ν s)

/-- Adding a straight black strand on the left preserves degrees. -/
theorem prependBlackStendhal_mem_grade (G : GradingDatum S) {d : ℤ}
    {z : StendhalAlgebra k Q Λ ν} (hz : z ∈ stendhalGrade G ν d) :
    prependBlackStendhal Q Λ i ν z ∈ stendhalGrade G νᵢ d := by
  change (prependBlackAllOrders Q Λ i ν z.val).val ∈ allOrdersGrade G νᵢ d
  obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp (show z.val ∈ allOrdersGrade G ν d from hz)
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν a = z.val at he
  rw [← he, prependBlackAllOrders_ofKLR]
  apply Graded.mem_map_of_mem
  exact G.castKLR_mem_grade _ ((blockR σᵢ μ).valHom_mem_grade G ha)

end Algebra

end Categorification.Stendhal
