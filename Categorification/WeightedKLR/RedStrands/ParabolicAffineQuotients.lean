/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.WeightedKLR.RedStrands.OrderProjection

/-!
# The two affine input quotients for standardization

Webster, arXiv:1309.3796v2, Definitions 4.5–4.7 and §5, Theorem 5.8.
Splitting off the final
red factor relabels the first and second KLR weights in a common alphabet.
In either part all black labels stay fixed. Projecting the relabelled
affine KLR algebra selects the prescribed red order, sets red dots to zero,
and kills violated loadings. The final one-red factor admits the cyclotomic
presentation of Theorem 4.20.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {m n : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin n → I →₀ ℕ)
    (f : Fin m → Fin n) (hf : Function.Injective f) (ν : Multiset I)

local notation "c" => Sum.map (id : I → I) f
local notation "μ" => stendhalWeight m ν
local notation "S" => stendhalQ Q Λ
local notation "Λ₀" => Λ ∘ f
local notation "π" => TensorProductAlgebra.mk Q (Λ₀) ν
local notation "τ" => orderProjection Q (Λ₀) ν
local notation "q₀" => StendhalAlgebraAllOrders.ofKLR k Q (Λ₀) ν

/-- Embed a red subfamily in the common KLR alphabet, preserving both the
black labels and the pairwise Stendhal parameters. -/
def redSubfamilyRelabel : SeqRelabel k (stendhalQ Q (Λ₀)) S μ ((μ).map c) :=
  let h := SeqRelabel.ofInjective (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩) S μ
  { h with
    Q_eq := fun s a b hab => by
      rw [h.Q_eq _ _ _ hab]
      cases s.lbl a <;> cases s.lbl b <;> rfl }

local notation "ρ" => redSubfamilyRelabel Q Λ f hf ν

/-- The unital quotient on an input block of the standardization functor,
with red labels included by `f`. -/
def redSubfamilyProjection : KLRAlgebra k S ((μ).map c) →ₐ[k] TensorProductAlgebra k Q (Λ₀) ν :=
  (π).comp ((τ).comp ((q₀).comp (relabelEquiv ρ).symm.toAlgHom))

local notation "P" => redSubfamilyProjection Q Λ f hf ν

theorem redSubfamilyProjection_surjective : Function.Surjective P :=
  (show Function.Surjective π from RingCon.mkₐ_surjective _).comp
    ((orderProjection_surjective Q (Λ₀) ν).comp
      (StendhalAlgebraAllOrders.ofKLR_surjective.comp (relabelEquiv ρ).symm.surjective))

private theorem redSubfamilyProjection_relabel (z : KLRAlgebra k (stendhalQ Q (Λ₀)) μ) :
    P (relabelEquiv ρ z) = π (τ (q₀ z)) := by
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

private theorem relabel_e (s : Seq μ) : relabelEquiv ρ (e s) = e (Seq.map c s) :=
  relabelHom_e _ _

private theorem relabel_x (a : Fin (μ).card) :
    relabelEquiv ρ (x a) = x (Fin.cast (Multiset.card_map c μ).symm a) :=
  relabelHom_x _ _

/-- An ordered boundary idempotent projects to the corresponding tensor
product algebra idempotent. -/
theorem redSubfamilyProjection_e (s : Seq μ) (ho : IsRedOrdered s) :
    P (e (Seq.map c s)) = π (StendhalAlgebra.e s ho) := by
  rw [← relabel_e Q Λ f hf ν, redSubfamilyProjection_relabel]
  exact congrArg π (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left ho)))

/-- An idempotent outside the prescribed red order projects to zero. -/
theorem redSubfamilyProjection_e_unordered (s : Seq μ) (ho : ¬ IsRedOrdered s) :
    P (e (Seq.map c s)) = 0 := by
  rw [← relabel_e Q Λ f hf ν, redSubfamilyProjection_relabel]
  exact (congrArg π (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans
    (ite_eq_right ho)))).trans (map_zero π)

/-- A violated loading projects to zero even if its red labels are ordered. -/
theorem redSubfamilyProjection_e_violated (s : Seq μ) (hv : IsViolated s) :
    P (e (Seq.map c s)) = 0 := by
  by_cases ho : IsRedOrdered s
  · rw [redSubfamilyProjection_e Q Λ f hf ν s ho]
    change (StendhalAlgebra.violatedIdeal k Q (Λ₀) ν).ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨s, ho, hv, rfl⟩
  · exact redSubfamilyProjection_e_unordered Q Λ f hf ν s ho

/-- Dots in the ambient alphabet preserve their strand positions. -/
theorem redSubfamilyProjection_x (a : Fin (μ).card) :
    P (x (Fin.cast (Multiset.card_map c μ).symm a)) = π (τ (StendhalAlgebraAllOrders.x a)) := by
  rw [← relabel_x Q Λ f hf ν, redSubfamilyProjection_relabel]
  rfl

/-- The homogeneous dot times a red loading vanishes by Definition 4.5. -/
theorem redSubfamilyProjection_red_dot (s : Seq μ) (a : Fin (μ).card) (ha : (s.lbl a).isRight) :
    P (x (Fin.cast (Multiset.card_map c μ).symm a) * e (Seq.map c s)) = 0 := by
  rw [← relabel_x Q Λ f hf ν, ← relabel_e Q Λ f hf ν, ← map_mul, redSubfamilyProjection_relabel,
    map_mul]
  change π (τ (StendhalAlgebraAllOrders.x a * StendhalAlgebraAllOrders.e s)) = 0
  rw [StendhalAlgebraAllOrders.x_mul_e_of_red a s ha, map_zero, map_zero]

omit [DecidableEq I] in
private theorem red_of_map_eq {z : I ⊕ Fin m} {r : Fin n} (h : c z = .inr r) :
    ∃ j, z = .inr j ∧ f j = r := by
  cases z with
  | inl i => contradiction
  | inr j => exact ⟨j, rfl, Sum.inr.inj h⟩

/-- Killing violations depends only on the ambient loading. -/
theorem redSubfamilyProjection_e_violated_ambient (t : Seq ((μ).map c)) (ht : IsViolated t) :
    P (e t) = 0 := by
  obtain ⟨s, rfl⟩ := (Seq.map_bijective (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩) μ).surjective t
  apply redSubfamilyProjection_e_violated Q Λ f hf ν s
  obtain ⟨h, hr⟩ := ht
  refine ⟨by simpa using h, ?_⟩
  simpa only [Seq.map_lbl, Sum.isLeft_map, Fin.cast_mk] using hr

omit [DecidableEq I] in
/-- Recolouring the red strands along an increasing map keeps a loading red-ordered. -/
theorem isRedOrdered_map_of_strictMono (hmono : StrictMono f) (s : Seq μ) (hs : IsRedOrdered s) :
    IsRedOrdered (Seq.map c s) := by
  intro a b r r' hab ha hb
  rw [Seq.map_lbl] at ha hb
  obtain ⟨j, hj, rfl⟩ := red_of_map_eq f ha
  obtain ⟨j', hj', rfl⟩ := red_of_map_eq f hb
  exact hmono (hs _ _ j j' hab hj hj')

/-- For an increasing inclusion of red labels an unordered ambient
loading projects to zero. -/
theorem redSubfamilyProjection_e_unordered_ambient (hmono : StrictMono f)
    (t : Seq ((μ).map c)) (ht : ¬ IsRedOrdered t) : P (e t) = 0 := by
  obtain ⟨s, rfl⟩ := (Seq.map_bijective (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩) μ).surjective t
  apply redSubfamilyProjection_e_unordered Q Λ f hf ν s
  intro hs
  apply ht
  exact isRedOrdered_map_of_strictMono f ν hmono s hs

/-- On any ambient loading the dot vanishes at a red position. -/
theorem redSubfamilyProjection_red_dot_ambient (t : Seq ((μ).map c)) (a : Fin ((μ).map c).card)
    (ha : (t.lbl a).isRight) : P (x a * e t) = 0 := by
  obtain ⟨s, rfl⟩ := (Seq.map_bijective (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩) μ).surjective t
  let b := Fin.cast (Multiset.card_map c μ) a
  have hb : (s.lbl b).isRight := by simpa only [Seq.map_lbl, Sum.isRight_map] using ha
  exact redSubfamilyProjection_red_dot Q Λ f hf ν s b hb

variable {ℓ : ℕ} (wt : Fin (ℓ + 1) → I →₀ ℕ) (θ : Multiset I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "λ₁" => (fun _ : Fin 1 => wt (Fin.last ℓ))

omit [DecidableEq I] in
/-- The prefix and last-factor affine input weights add up to the total
Stendhal weight before applying the induction idempotent. -/
theorem parabolicInputWeights_add (β : Multiset I) :
    (stendhalWeight ℓ θ).map (addRedColor ℓ) + (stendhalWeight 1 β).map lastColour =
      stendhalWeight (ℓ+1) (θ+β) := by
  have hb : (stendhalWeight 1 β).map lastColour =
      β.map Sum.inl + ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1))) := by
    simp [stendhalWeight, Function.comp_def]
  rw [hb, add_comm (β.map Sum.inl), ← add_assoc, stendhalWeight_addRed]
  simp [stendhalWeight, add_assoc, add_comm, add_left_comm]

/-- The surjective affine input homomorphism on the first `ℓ` red factors. -/
abbrev parabolicPrefixProjection :=
  redSubfamilyProjection Q wt Fin.castSucc (Fin.castSucc_injective ℓ) θ

private theorem finalIndex_injective (ℓ : ℕ) : Function.Injective (fun _ : Fin 1 => Fin.last ℓ) :=
  fun _ _ _ => Subsingleton.elim _ _

/-- The surjective affine input homomorphism on the final red factor. -/
abbrev parabolicLastProjection :=
  redSubfamilyProjection Q wt (fun _ : Fin 1 => Fin.last ℓ) (finalIndex_injective ℓ) θ

theorem parabolicPrefixProjection_surjective : Function.Surjective (parabolicPrefixProjection Q wt θ) :=
  redSubfamilyProjection_surjective Q wt _ _ θ

theorem parabolicLastProjection_surjective : Function.Surjective (parabolicLastProjection Q wt θ) :=
  redSubfamilyProjection_surjective Q wt _ _ θ

local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 θ)

theorem parabolicPrefixProjection_e_violated (t : Seq Aₚ) (ht : IsViolated t) :
    parabolicPrefixProjection Q wt θ (e t) = 0 :=
  redSubfamilyProjection_e_violated_ambient Q wt _ _ θ t ht

theorem parabolicLastProjection_e_violated (t : Seq Aₗ) (ht : IsViolated t) :
    parabolicLastProjection Q wt θ (e t) = 0 :=
  redSubfamilyProjection_e_violated_ambient Q wt _ _ θ t ht

theorem parabolicPrefixProjection_e_unordered (t : Seq Aₚ) (ht : ¬ IsRedOrdered t) :
    parabolicPrefixProjection Q wt θ (e t) = 0 :=
  redSubfamilyProjection_e_unordered_ambient Q wt Fin.castSucc (Fin.castSucc_injective ℓ) θ
    (fun _ _ h => h) t ht

omit [DecidableEq I] in
/-- The final alphabet has only one red index, so every ambient loading
of the last factor is red-ordered. -/
theorem parabolicLast_ordered (t : Seq Aₗ) : IsRedOrdered t := by
  have hf := Sum.map_injective.mpr ⟨Function.injective_id (α := I), finalIndex_injective ℓ⟩
  obtain ⟨s, rfl⟩ := (Seq.map_bijective hf (stendhalWeight 1 θ)).surjective t
  exact isRedOrdered_map_of_strictMono last θ (fun a b hab => (hab.ne (Subsingleton.elim a b)).elim) s (SingleRed.ordered θ s)

theorem parabolicLastProjection_e_unordered (t : Seq Aₗ) (ht : ¬ IsRedOrdered t) :
    parabolicLastProjection Q wt θ (e t) = 0 := (ht (parabolicLast_ordered θ t)).elim

theorem parabolicPrefixProjection_red_dot (t : Seq Aₚ) (a : Fin (Aₚ).card) (ha : (t.lbl a).isRight) :
    parabolicPrefixProjection Q wt θ (x a * e t) = 0 :=
  redSubfamilyProjection_red_dot_ambient Q wt _ _ θ t a ha

theorem parabolicLastProjection_red_dot (t : Seq Aₗ) (a : Fin (Aₗ).card) (ha : (t.lbl a).isRight) :
    parabolicLastProjection Q wt θ (x a * e t) = 0 :=
  redSubfamilyProjection_red_dot_ambient Q wt _ _ θ t a ha

omit [DecidableEq I] in
/-- Every red label in the prefix weight is earlier than the final one. -/
theorem parabolicPrefix_red_lt_last (t : Seq Aₚ) (a : Fin (Aₚ).card) {r : Fin (ℓ+1)} (hr : t.lbl a = .inr r) :
    r < Fin.last ℓ := by
  obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp (t.mem a)
  obtain ⟨j, _, rfl⟩ := red_of_map_eq Fin.castSucc (hz.trans hr)
  exact Fin.castSucc_lt_last j

omit [DecidableEq I] in
/-- The final factor weight has just the final red label. -/
theorem parabolicLast_red_eq_last (t : Seq Aₗ) (a : Fin (Aₗ).card) {r : Fin (ℓ+1)} (hr : t.lbl a = .inr r) :
    r = Fin.last ℓ := by
  obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp (t.mem a)
  obtain ⟨_, _, rfl⟩ := red_of_map_eq last (hz.trans hr)
  rfl

/-- Erasing the final red strand identifies the right input quotient
with the cyclotomic algebra of its highest weight. -/
def parabolicLastCyclotomic :=
  (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => wt (Fin.last ℓ)) θ).symm.toAlgHom.comp
    (parabolicLastProjection Q wt θ)

theorem parabolicLastCyclotomic_surjective : Function.Surjective (parabolicLastCyclotomic Q wt θ) :=
  (SingleRed.cyclotomicEquiv Q _ θ).symm.surjective.comp (parabolicLastProjection_surjective Q wt θ)

/-- An affine loading with the last red strand inserted on the left
becomes the corresponding cyclotomic black loading. -/
theorem parabolicLastCyclotomic_e (s : Seq θ) :
    parabolicLastCyclotomic Q wt θ (e (Seq.map lastColour (SingleRed.insertWord θ s))) =
      CycKLR.mk k Q (fun i => Polynomial.X ^ wt (Fin.last ℓ) i) θ (e s) := by
  apply (SingleRed.cyclotomicEquiv Q λ₁ θ).injective
  rw [parabolicLastCyclotomic, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rw [parabolicLastProjection, redSubfamilyProjection_e Q wt last (finalIndex_injective ℓ) θ (SingleRed.insertWord θ s) (SingleRed.ordered θ _)]
  change _ = SingleRed.cyclotomicProjection Q λ₁ θ (CycKLR.mk k Q _ θ (e s))
  rw [SingleRed.cyclotomicProjection, CycKLR.lift_mk, SingleRed.insertRed_e]
  rfl

/-- Erasing the final factor's leftmost red strand removes its position
from the indexing of the remaining black dots. -/
theorem parabolicLastCyclotomic_blackDot (a : Fin θ.card) :
    parabolicLastCyclotomic Q wt θ
      (x (Fin.cast (Multiset.card_map lastColour (stendhalWeight 1 θ)).symm (SingleRed.blackPos θ a))) =
        CycKLR.mk k Q (fun i => Polynomial.X ^ wt (Fin.last ℓ) i) θ (x a) := by
  apply (SingleRed.cyclotomicEquiv Q λ₁ θ).injective
  rw [parabolicLastCyclotomic, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    parabolicLastProjection, redSubfamilyProjection_x Q wt last (finalIndex_injective ℓ) θ (SingleRed.blackPos θ a)]
  change _ = SingleRed.cyclotomicProjection Q λ₁ θ (CycKLR.mk k Q _ θ (x a))
  rw [SingleRed.cyclotomicProjection, CycKLR.lift_mk, SingleRed.insertRed_x]
  apply congrArg (TensorProductAlgebra.mk Q λ₁ θ)
  apply Subtype.ext
  let z : StendhalAlgebraAllOrders k Q λ₁ θ := StendhalAlgebraAllOrders.x (SingleRed.blackPos θ a)
  change z * StendhalAlgebraAllOrders.redOrderedIdem k Q λ₁ θ = z
  rw [SingleRed.redOrderedIdem_eq_one, mul_one]

local notation "R₁" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))
local notation "B₁" => Multiset.map ι θ
local notation "S₁" => stendhalQ Q wt
local notation "qB" => KLRAlgebra.reindexEquiv Sum.inl_injective S₁ θ
local notation "πB" => CycKLR.mk k Q (fun i => Polynomial.X ^ wt (Fin.last ℓ) i) θ

omit [DecidableEq I] in
/-- Splitting the final factor into its red strand and its black strands
gives its relabelled Stendhal weight. -/
theorem lastRedBlackWeight : R₁ + B₁ = Aₗ := by
  simp [stendhalWeight, Function.comp_def, add_comm]

private abbrev lastRedBlackCast := castKLR S₁ (lastRedBlackWeight (ℓ := ℓ) θ)
local notation "liftLast" => parabolicLastCyclotomic Q wt θ
local notation "κ" => lastRedBlackCast Q wt θ

omit [DecidableEq I] in
private theorem lastRedBlackLoading (s : Seq θ) (u : Seq R₁) :
    Seq.cast (lastRedBlackWeight (ℓ := ℓ) θ) (u.append (Seq.map ι s)) =
    Seq.map lastColour (SingleRed.insertWord θ s) := by
  apply Subtype.ext
  funext a
  change (u.append (Seq.map ι s)).1 (Fin.cast _ a) =
    lastColour ((SingleRed.insertWord θ s).lbl (Fin.cast _ a))
  by_cases hz : a.val = 0
  · rw [Seq.append_apply_lt _ _ _ (by change a.val < (R₁).card; simpa using hz)]
    have hpos : Fin.cast (Multiset.card_map lastColour _) a = ⟨0, by simp [stendhalWeight]⟩ :=
      Fin.ext hz
    rw [hpos, SingleRed.insertWord_head]
    exact Multiset.mem_singleton.mp (u.mem _)
  · rw [Seq.append_apply_ge _ _ _ (by change (R₁).card ≤ a.val; simpa using (show 1 ≤ a.val by omega))]
    have hlen := a.isLt
    simp [stendhalWeight] at hlen
    let b : Fin θ.card := ⟨a.val-1, by omega⟩
    have hpos : Fin.cast (Multiset.card_map lastColour _) a = SingleRed.blackPos θ b :=
      Fin.ext (by change a.val = a.val-1+1; omega)
    rw [hpos, SingleRed.insertWord_black]
    change Sum.inl (s.1 _) = Sum.inl (s.1 b)
    congr 2

private def lastBlackConcat : KLRAlgebra k Q θ →ₗ[k] CycKLR k Q
    (fun i => Polynomial.X ^ wt (Fin.last ℓ) i) θ :=
  (liftLast).toLinearMap.comp ((κ).toLinearMap.comp ((concat S₁ R₁ B₁).comp
    ((TensorProduct.mk k _ _ 1).comp (qB).toLinearMap)))

local notation "F" => lastBlackConcat Q wt θ

private theorem lastBlackConcat_e (s : Seq θ) : F (e s) = πB (e s) := by
  change liftLast (κ (concat S₁ R₁ B₁ (1 ⊗ₜ[k] qB (e s)))) = _
  rw [reindexEquiv_e, ← e_single (Q := S₁) (Sum.inr (Fin.last ℓ)) (default : Seq R₁), concat_e_tmul_e,
    lastRedBlackCast, castKLR_e, lastRedBlackLoading, parabolicLastCyclotomic_e]

private theorem lastBlackConcat_one : F 1 = 1 := by
  rw [← sum_e (Q := Q) (ν := θ), map_sum]
  simp only [lastBlackConcat_e, ← map_sum, sum_e, map_one]

private theorem lastProj_oneConcat : liftLast (κ (oneConcat S₁ R₁ B₁)) = 1 := by
  have h := lastBlackConcat_one Q wt θ
  change liftLast (κ (concat S₁ R₁ B₁ (1 ⊗ₜ[k] qB 1))) = 1 at h
  rwa [map_one, concat_one_tmul_one] at h

private theorem parabolicLastCyclotomic_blackCross (j : ℕ) (hj : j+1<θ.card) :
    liftLast (ψ (j+1)) = πB (ψ j) := by
  apply (SingleRed.cyclotomicEquiv Q λ₁ θ).injective
  rw [parabolicLastCyclotomic, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  let r := redSubfamilyRelabel Q wt last (finalIndex_injective ℓ) θ
  have hψ : relabelEquiv r (ψ (j+1)) = ψ (j+1) := relabelHom_ψ _ _
  rw [parabolicLastProjection, ← hψ, redSubfamilyProjection_relabel]
  change _ = SingleRed.cyclotomicProjection Q λ₁ θ (πB (ψ j))
  rw [SingleRed.cyclotomicProjection, CycKLR.lift_mk, SingleRed.insertRed_ψ Q λ₁ θ j hj]
  apply congrArg (TensorProductAlgebra.mk Q λ₁ θ)
  apply Subtype.ext
  let z : StendhalAlgebraAllOrders k Q λ₁ θ := StendhalAlgebraAllOrders.ψ (j+1)
  change z * StendhalAlgebraAllOrders.redOrderedIdem k Q λ₁ θ = z
  rw [SingleRed.redOrderedIdem_eq_one, mul_one]

/-- Placing an arbitrary affine black diagram after the last red strand
and erasing that red strand is the ordinary cyclotomic quotient map
(Webster, Theorem 4.20). -/
theorem parabolicLastCyclotomic_concat_black (y : KLRAlgebra k Q θ) :
    liftLast (castKLR S₁ (lastRedBlackWeight (ℓ := ℓ) θ)
      (concat S₁ R₁ B₁ (1 ⊗ₜ[k] qB y))) = πB y := by
  change F y = πB y
  induction y using klr_induction with
  | hr scalar =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, lastBlackConcat_one, map_smul, map_one]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hmul x y hx hy =>
    let relabel : KLRAlgebra k Q θ ≃ₐ[k] KLRAlgebra k S₁ B₁ := qB
    change liftLast (κ (concat S₁ R₁ B₁ (1 ⊗ₜ[k] relabel (x*y)))) = _
    rw [map_mul relabel x y, ← one_mul (1 : KLRAlgebra k S₁ R₁), ← Algebra.TensorProduct.tmul_mul_tmul,
      concat_mul, map_mul, map_mul]
    exact (congrArg₂ (· * ·) hx hy).trans (map_mul πB x y).symm
  | he s => exact lastBlackConcat_e Q wt θ s
  | hx a =>
    change liftLast (κ (concat S₁ R₁ B₁ (1 ⊗ₜ[k] qB (x a)))) = _
    rw [reindexEquiv_x, concat_one_tmul_x, map_mul, map_mul, lastProj_oneConcat, mul_one]
    rw [lastRedBlackCast, castKLR_x]
    convert parabolicLastCyclotomic_blackDot Q wt θ a using 3
    apply Fin.ext
    change (R₁).card + a.val = a.val+1
    simp [add_comm]
  | hψ j =>
    by_cases hj : j+1<θ.card
    · change liftLast (κ (concat S₁ R₁ B₁ (1 ⊗ₜ[k] qB (ψ j)))) = _
      rw [reindexEquiv_ψ, concat_one_tmul_ψ (by simpa using hj), map_mul, map_mul,
        lastProj_oneConcat, mul_one, lastRedBlackCast, castKLR_ψ]
      simpa [add_comm] using parabolicLastCyclotomic_blackCross Q wt θ j hj
    · rw [ψ_eq_zero j (by omega), map_zero, map_zero]

end Categorification.Stendhal
