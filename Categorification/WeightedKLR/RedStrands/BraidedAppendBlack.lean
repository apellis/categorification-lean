/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient

set_option backward.isDefEq.respectTransparency false

/-!
# Appending a black strand to braided Stendhal diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7. The functors `𝔈_i`, `𝔉_i` on tensor product algebras are induction and
restriction along the map adding a black strand at the right. Proposition 6.7 says that the
bimodules `B_w` intertwine these functors. This file constructs the map on braided Stendhal
diagrams adding a straight black strand at the far right, as for the tensor product algebras
in `BlackInduction`.

## Main definitions

* `Stendhal.BraidedStendhalAlgebra.appendBlack`: the algebra map from braided diagrams of
  black weight `ν` to the corner of braided diagrams of weight `{i} + ν` cut out by the
  idempotents whose rightmost strand is black of colour `i`.

## Main results

* `appendBlack_ofKLR_e`, `appendBlack_ofKLR_x`, `appendBlack_ofKLR_ψ`: its values on the
  generators.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "S" => stendhalQ Q Λ
local notation "B" => BraidedStendhalAlgebra k Q Λ νᵢ

namespace BraidedStendhalAlgebra

/-- The KLR algebra of the Stendhal weight with an extra black strand maps to braided
diagrams of weight `{i} + ν`. -/
def appendAmbient : KLRAlgebra k S (μ + σᵢ) →ₐ[k] B :=
  (ofKLR k Q Λ νᵢ).comp (castKLR S (stendhalWeight_addBlack i ν)).toAlgHom

/-- The idempotent of braided diagrams whose rightmost strand is black of colour `i`. -/
def appendIdem : B :=
  appendAmbient Q Λ i ν (oneConcat S μ σᵢ)

theorem isIdempotentElem_appendIdem : IsIdempotentElem (appendIdem Q Λ i ν) :=
  (oneConcat_idem (Q := S) (ν := μ) (ν' := σᵢ)).map (appendAmbient Q Λ i ν)

local instance : Algebra k (isIdempotentElem_appendIdem Q Λ i ν).Corner :=
  KLR.cornerAlgebra _

private def appendConcatCorner :
    ConcatCorner S μ σᵢ →ₐ[k] (isIdempotentElem_appendIdem Q Λ i ν).Corner where
  toFun z := KLR.Corner.mk (appendAmbient Q Λ i ν z.val) (by
    have hz : oneConcat S μ σᵢ * z.val * oneConcat S μ σᵢ = z.val :=
      (congrArg (· * oneConcat S μ σᵢ) (KLR.Corner.E_mul_val z)).trans
        (KLR.Corner.val_mul_E z)
    simpa only [map_mul, appendIdem] using congrArg (appendAmbient Q Λ i ν) hz)
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  commutes' c := Subtype.ext (by
    change appendAmbient Q Λ i ν (algebraMap k _ c * oneConcat S μ σᵢ) =
      algebraMap k B c * appendIdem Q Λ i ν
    rw [map_mul, AlgHom.commutes]
    rfl)

/-- Appending a straight black strand to a KLR diagram of the Stendhal weight. -/
def appendKLR : KLRAlgebra k S μ →ₐ[k] (isIdempotentElem_appendIdem Q Λ i ν).Corner :=
  (appendConcatCorner Q Λ i ν).comp ((blockL μ σᵢ).hom S)

theorem appendKLR_e (s : Seq μ) :
    (appendKLR Q Λ i ν (KLRAlgebra.e s)).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) := by
  have hf : (blockL μ σᵢ).F s = {s.append (default : Seq σᵢ)} := by
    classical
    ext t
    change t ∈ Finset.univ.image (fun a : Seq σᵢ => s.append a) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg s.append (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  change appendAmbient Q Λ i ν (((blockL μ σᵢ).hom S) (KLRAlgebra.e s)).val = _
  rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum, Finset.sum_singleton]
  exact congrArg (ofKLR k Q Λ νᵢ) (castKLR_e (stendhalWeight_addBlack i ν) _)

/-- The position in the weight with the new black strand of an old position. -/
def appendPos (a : Fin (Multiset.card μ)) : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  ⟨a.val, by simpa only [← stendhalWeight_addBlack i ν, Multiset.card_add,
    Multiset.card_singleton] using Nat.lt_succ_of_lt a.isLt⟩

omit [DecidableEq I] in
theorem appendBlackLoading_lbl_appendPos (s : Seq μ) (a : Fin (Multiset.card μ)) :
    (appendBlackLoading i ν s).lbl (appendPos i ν a) = s.lbl a :=
  appendBlackLoading_lbl_of_lt i ν s _ a.isLt

theorem appendKLR_x (a : Fin (Multiset.card μ)) :
    (appendKLR Q Λ i ν (KLRAlgebra.x a)).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν a)) * appendIdem Q Λ i ν := by
  change appendAmbient Q Λ i ν (((blockL μ σᵢ).hom S) (KLRAlgebra.x a)).val = _
  rw [BlockEmb.hom_x, val_polCorner, pol_X, map_mul]
  congr 1
  exact congrArg (ofKLR k Q Λ νᵢ) (castKLR_x (stendhalWeight_addBlack i ν) _)

theorem appendKLR_ψ {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    (appendKLR Q Λ i ν (KLRAlgebra.ψ j)).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.ψ j) * appendIdem Q Λ i ν := by
  change appendAmbient Q Λ i ν (((blockL μ σᵢ).hom S) (KLRAlgebra.ψ j)).val = _
  rw [BlockEmb.hom_ψ, BlockEmb.val_gψ _ hj, map_mul]
  congr 1
  simp only [blockL, Nat.zero_add]
  exact congrArg (ofKLR k Q Λ νᵢ) (castKLR_ψ (stendhalWeight_addBlack i ν) j)

/-- **Appending a black strand** (arXiv:1309.3796v2, §6.1, the map behind Proposition 6.7):
the map from braided diagrams of black weight `ν` to the corner of braided diagrams of weight
`{i} + ν` adding a straight black strand coloured `i` at the right. -/
def appendBlack :
    BraidedStendhalAlgebra k Q Λ ν →ₐ[k] (isIdempotentElem_appendIdem Q Λ i ν).Corner :=
  RingQuot.liftAlgHom k
    ⟨(appendKLR Q Λ i ν).comp (KLRAlgebra.mk k (stendhalQ Q Λ) μ), fun x y h => by
      cases h with
      | klr h =>
        exact congrArg (appendKLR Q Λ i ν) (RingQuot.mkAlgHom_rel k h)
      | red_dot a s ha =>
        apply KLR.Corner.ext
        simp only [AlgHom.comp_apply, map_mul, map_zero, KLR.Corner.val_mul,
          KLR.Corner.val_zero]
        change (appendKLR Q Λ i ν (KLRAlgebra.x a)).val *
          (appendKLR Q Λ i ν (KLRAlgebra.e s)).val = 0
        have hs := KLR.Corner.E_mul_val (appendKLR Q Λ i ν (KLRAlgebra.e s))
        rw [appendKLR_e] at hs
        rw [appendKLR_x, appendKLR_e, mul_assoc]
        change ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν a)) *
          (appendIdem Q Λ i ν * ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s))) = _
        rw [hs, ← map_mul]
        refine ofKLR_x_mul_e_of_red _ _ ?_
        rwa [appendBlackLoading_lbl_appendPos]⟩

theorem appendBlack_ofKLR (z : KLRAlgebra k (stendhalQ Q Λ) μ) :
    appendBlack Q Λ i ν (ofKLR k Q Λ ν z) = appendKLR Q Λ i ν z := by
  obtain ⟨w, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem appendBlack_ofKLR_e (s : Seq μ) :
    (appendBlack Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.e s))).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) := by
  rw [appendBlack_ofKLR, appendKLR_e]

theorem appendBlack_ofKLR_x (a : Fin (Multiset.card μ)) :
    (appendBlack Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.x a))).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν a)) * appendIdem Q Λ i ν := by
  rw [appendBlack_ofKLR, appendKLR_x]

theorem appendBlack_ofKLR_ψ {j : ℕ} (hj : j + 1 < Multiset.card μ) :
    (appendBlack Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.ψ j))).val =
      ofKLR k Q Λ νᵢ (KLRAlgebra.ψ j) * appendIdem Q Λ i ν := by
  rw [appendBlack_ofKLR, appendKLR_ψ Q Λ i ν hj]

theorem appendBlack_one_val : (appendBlack Q Λ i ν 1).val = appendIdem Q Λ i ν := by
  rw [map_one]
  rfl

/-! ### Red orders and violated idempotents -/

omit [DecidableEq I] in
private theorem filterMap_finRange_of_succ {α : Type*} {n n' : ℕ} (h : n' = n + 1)
    (f : Fin n' → Option α) (g : Fin n → Option α)
    (hlt : ∀ a : Fin n, f ⟨a.val, by omega⟩ = g a) (hlast : f ⟨n, by omega⟩ = none) :
    (List.finRange n').filterMap f = (List.finRange n).filterMap g := by
  subst h
  rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
  have h1 : (fun x : Fin n => f x.castSucc) = g := funext fun a => hlt a
  have h2 : f (Fin.last n) = none := hlast
  simp only [Function.comp_def, h1, h2, List.filterMap_cons_none, List.filterMap_nil,
    List.append_nil]

omit [DecidableEq I] in
theorem card_stendhalWeight_addBlack :
    Multiset.card (stendhalWeight ℓ νᵢ) = Multiset.card μ + 1 := by
  rw [← stendhalWeight_addBlack i ν, Multiset.card_add, Multiset.card_singleton]

omit [DecidableEq I] in
/-- A black strand at the right does not change the red order. -/
theorem redWord_appendBlackLoading (s : Seq μ) :
    redWord (appendBlackLoading i ν s) = redWord s :=
  filterMap_finRange_of_succ (card_stendhalWeight_addBlack i ν) _ _
    (fun a => by rw [appendBlackLoading_lbl_of_lt i ν s _ a.isLt])
    (by rw [appendBlackLoading_lbl_of_eq i ν s _ rfl]; rfl)

/-- `appendBlack` as a non-unital ring map into braided diagrams of weight `{i} + ν`. -/
def appendBlackValue : BraidedStendhalAlgebra k Q Λ ν →ₙ+* B :=
  (KLR.cornerVal (isIdempotentElem_appendIdem Q Λ i ν)).comp
    (appendBlack Q Λ i ν).toRingHom.toNonUnitalRingHom

theorem appendBlackValue_apply (z : BraidedStendhalAlgebra k Q Λ ν) :
    appendBlackValue Q Λ i ν z = (appendBlack Q Λ i ν z).val := rfl

theorem appendBlackValue_e (s : Seq μ) :
    appendBlackValue Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) =
      ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) :=
  appendBlack_ofKLR_e Q Λ i ν s

theorem appendIdem_eq_sum :
    appendIdem Q Λ i ν =
      ∑ s : Seq μ, ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) := by
  rw [← appendBlack_one_val, ← appendBlackValue_apply, ← map_one (ofKLR k Q Λ ν),
    ← KLRAlgebra.sum_e, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackValue_e Q Λ i ν s

theorem redProj_mul_appendIdem (κ : List (Fin ℓ)) :
    redProj k Q Λ νᵢ κ * appendIdem Q Λ i ν =
      ∑ s ∈ Finset.univ.filter (fun s : Seq μ => redWord s = κ),
        ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) := by
  rw [appendIdem_eq_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [redProj_mul_e, redWord_appendBlackLoading]

theorem appendIdem_mul_redProj (κ : List (Fin ℓ)) :
    appendIdem Q Λ i ν * redProj k Q Λ νᵢ κ =
      ∑ s ∈ Finset.univ.filter (fun s : Seq μ => redWord s = κ),
        ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) := by
  rw [appendIdem_eq_sum, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [e_mul_redProj, redWord_appendBlackLoading]

/-- Appending a black strand preserves red orders. -/
theorem appendBlackValue_redProj (κ : List (Fin ℓ)) :
    appendBlackValue Q Λ i ν (redProj k Q Λ ν κ) =
      redProj k Q Λ νᵢ κ * appendIdem Q Λ i ν := by
  rw [redProj_mul_appendIdem, redProj, redIdem, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackValue_e Q Λ i ν s

theorem redProj_commute_appendIdem (κ : List (Fin ℓ)) :
    Commute (redProj k Q Λ νᵢ κ) (appendIdem Q Λ i ν) :=
  (redProj_mul_appendIdem Q Λ i ν κ).trans (appendIdem_mul_redProj Q Λ i ν κ).symm

/-- Appending a black strand sends the violated ideal into the violated ideal. -/
theorem appendBlackValue_mem_violIdeal {z : BraidedStendhalAlgebra k Q Λ ν}
    (hz : z ∈ violIdeal k Q Λ ν) : appendBlackValue Q Λ i ν z ∈ violIdeal k Q Λ νᵢ := by
  have hle :
      violIdeal k Q Λ ν ≤ (violIdeal k Q Λ νᵢ).comap (appendBlackValue Q Λ i ν) := by
    refine TwoSidedIdeal.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap (appendBlackValue Q Λ i ν), appendBlackValue_e]
    exact TwoSidedIdeal.subset_span ⟨_, appendBlackLoading_violated i ν s hs, rfl⟩
  exact (TwoSidedIdeal.mem_comap (appendBlackValue Q Λ i ν)).1 (hle hz)

end BraidedStendhalAlgebra

end Categorification.Stendhal
