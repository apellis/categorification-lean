/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRed

/-!
# Injectivity of the terminal red strand map

Webster, arXiv:1309.3796v2, Proposition 4.16 and §4.3, Proposition
4.18. Appending a red strand extends a PBW index by fixing the final position
and appending a zero dot exponent. Independence of the larger Stendhal PBW
family detects the kernel of the map before quotienting.
-/

noncomputable section


namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "M" => stendhalWeight (ℓ + 1) ν
local notation "n" => Multiset.card μ
local notation "m" => Multiset.card M

private theorem appendCard : n + 1 = m := by simp [stendhalWeight]; omega

private def appendPerm (w : Perm (Fin n)) : Perm (Fin m) := blockPerm appendCard w (1 : Perm (Fin 1))

private theorem appendPerm_injective : Function.Injective (appendPerm (ν := ν) (ℓ := ℓ)) :=
  fun _ _ h => (blockPerm_injective appendCard h).1

private theorem appendRedLoading_smul (w : Perm (Fin n)) (s : KLR.Seq μ) :
    appendPerm w • appendRedLoading s = appendRedLoading (w • s) := by
  let h := appendCard (ℓ := ℓ) (ν := ν)
  have hp (b : Fin n) : appendRedPosition b = blockEquiv h (Sum.inl b) := Fin.ext rfl
  have hl : lastRedPosition ℓ ν = blockEquiv h (Sum.inr (0 : Fin 1)) :=
    Fin.ext (by change ν.card + ℓ = n + 0; simp [stendhalWeight])
  apply Subtype.ext
  funext a
  change (appendRedLoading s).lbl ((appendPerm w)⁻¹ a) = (appendRedLoading (w • s)).lbl a
  rcases eq_lastRedPosition_or a with rfl | ⟨b, rfl⟩
  · rw [appendPerm, blockPerm_inv, hl, blockPerm_inr]
    change (appendRedLoading s).lbl (blockEquiv h (.inr (0 : Fin 1))) = _
    rw [← hl]
    exact (hasLastRed_appendRedLoading s).trans (hasLastRed_appendRedLoading (w • s)).symm
  · rw [appendPerm, blockPerm_inv, hp, blockPerm_inl, ← hp, ← hp, appendRedLoading_lbl,
      appendRedLoading_lbl]
    rfl

private theorem isReduced_appendWord {ρ : List ℕ} (hρ : IsReduced n ρ) : IsReduced m ρ := by
  refine ⟨hρ.1.of_le (by have := appendCard (ℓ := ℓ) (ν := ν); omega), ?_⟩
  rw [wordProd_eq_blockPerm_left appendCard hρ.1, length_blockPerm, length_one, add_zero]
  exact hρ.2

private def extendedWord : Perm (Fin m) → List ℕ :=
  Function.extend appendPerm (canWord n) (canWord m)

private theorem extendedWord_append (w : Perm (Fin n)) :
    extendedWord (appendPerm w) = canWord n w :=
  appendPerm_injective.extend_apply _ _ w

private theorem extendedWord_spec (w : Perm (Fin m)) :
    IsReduced m (extendedWord w) ∧ wordProd m (extendedWord w) = w := by
  classical
  by_cases h : ∃ v, appendPerm v = w
  · obtain ⟨v, rfl⟩ := h
    rw [extendedWord_append]
    exact ⟨isReduced_appendWord (isReduced_canWord n v), by
      rw [wordProd_eq_blockPerm_left appendCard (validWord_canWord n v), wordProd_canWord]; rfl⟩
  · rw [extendedWord, Function.extend_apply' _ _ _ h]
    exact ⟨isReduced_canWord m w, wordProd_canWord m w⟩

private theorem extendedWord_prod (w : Perm (Fin m)) : wordProd m (extendedWord w) = w :=
  (extendedWord_spec w).2

private theorem noRedCross_append (s : KLR.Seq μ) {ρ : List ℕ} (hv : ValidWord n ρ)
    (hr : NoRedCross ρ s) : NoRedCross ρ (appendRedLoading s) := by
  induction ρ with
  | nil => trivial
  | cons j ρ ih =>
    obtain ⟨hj, hρ⟩ := validWord_cons.1 hv
    refine ⟨ih hρ hr.1, ?_⟩
    intro hj'
    have hw := wordProd_eq_blockPerm_left appendCard hρ
    change wordProd m ρ = appendPerm (wordProd n ρ) at hw
    rw [hw, appendRedLoading_smul]
    have hpos₀ : (⟨j, by omega⟩ : Fin m) = appendRedPosition ⟨j, by omega⟩ := Fin.ext rfl
    have hpos₁ : (⟨j+1, hj'⟩ : Fin m) = appendRedPosition ⟨j+1, hj⟩ := Fin.ext rfl
    rw [hpos₀, hpos₁]
    change ((appendRedLoading _).lbl (appendRedPosition _)).isLeft ∨
      ((appendRedLoading _).lbl (appendRedPosition _)).isLeft
    simpa only [appendRedLoading_lbl, addRedColor_isLeft] using! hr.2 hj

private def appendPosEmb : Fin n ↪ Fin m :=
  ⟨appendRedPosition, fun _ _ h => Fin.ext (congrArg (fun x : Fin m => x.val) h)⟩

local notation "OldTerm" => {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) (canWord n) b}
local notation "NewTerm" => {b // IsStendhalTerm (ν := ν) (ℓ := ℓ+1) extendedWord b}

private def appendTerm (b : OldTerm) : NewTerm := by
  let w := b.1.2.1
  let s := b.1.1
  let d := b.1.2.2
  refine ⟨(appendRedLoading s, appendPerm w, Finsupp.embDomain appendPosEmb d),
    (appendRedLoading_ordered_iff s).2 b.2.1, ?_, ?_, ?_⟩
  · rw [appendRedLoading_smul]
    exact (appendRedLoading_ordered_iff _).2 b.2.2.1
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
    change ((appendRedLoading s).lbl (appendRedPosition x)).isLeft
    rw [appendRedLoading_lbl, addRedColor_isLeft]
    exact b.2.2.2.1 x hx
  · rw [extendedWord_append]
    exact noRedCross_append s (validWord_canWord _ w) b.2.2.2.2

private theorem appendTerm_injective : Function.Injective (appendTerm (ℓ := ℓ) (ν := ν)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (appendRedLoading_injective (congrArg (fun z : NewTerm => z.1.1) h))
    (Prod.ext (appendPerm_injective (congrArg (fun z : NewTerm => z.1.2.1) h))
      (Finsupp.embDomain_injective appendPosEmb (congrArg (fun z : NewTerm => z.1.2.2) h)))

section Independence

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
variable (ν)

local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "oldB" => stendhalTerm Q Λ₀ (wordProd_canWord n)
local notation "newB" => stendhalTerm Q Λ extendedWord_prod
local notation "φ" => appendRedStendhalValue Q Λ ν

private theorem appendTerm_value (b : OldTerm) : φ (oldB b) = newB (appendTerm b) := by
  apply Subtype.ext
  rw [appendRedStendhalValue_stendhalTerm Q Λ ν
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) b, stendhalTerm_val]
  change _ = StendhalAlgebraAllOrders.ofKLR k Q Λ ν
    (ψw (extendedWord (appendPerm b.1.2.1)) * pol (monomial (Finsupp.embDomain appendPosEmb b.1.2.2) 1) *
      KLRAlgebra.e (appendRedLoading b.1.1))
  rw [extendedWord_append, rename_monomial, Finsupp.embDomain_eq_mapDomain, mul_assoc]
  rfl

private theorem appendRedStendhalValue_injective_of_independent
    (hB : LinearIndependent k (newB : NewTerm → _)) : Function.Injective φ := by
  let f : StendhalAlgebra k Q Λ₀ ν →ₗ[k] StendhalAlgebra k Q Λ ν :=
    { toFun := φ, map_add' := map_add _, map_smul' := appendRedStendhalValue_smul Q Λ ν }
  have hall := span_stendhalTerm (Q := Q) (Λ := Λ₀) (ν := ν)
    (fun w => ⟨isReduced_canWord n w, wordProd_canWord n w⟩)
  apply LinearMap.injective_of_linearIndependent (f := f) (v := oldB) (top_unique hall)
  have he : f ∘ oldB = newB ∘ appendTerm := funext (appendTerm_value (ν := ν) Q Λ)
  exact he ▸ hB.comp appendTerm appendTerm_injective

end Independence

section Graph

open WeightedKLR
variable [DecidableEq I] {k : Type*} [CommRing k] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] (Γ : WeightedGraph I 𝕜 k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ c, Γ.loop c = none)
  (hw : ∀ e, Γ.weight e = 0) (hS : Γ.Standing)

include hD hE hl hw hS in
/-- The prequotient map in Webster, arXiv:1309.3796v2, Proposition 4.18 is injective
for the graph parameters of the Stendhal basis theorem (Proposition 4.16). -/
theorem appendRedStendhalValue_injective :
    Function.Injective (appendRedStendhalValue Γ.klrQ Λ ν) :=
  appendRedStendhalValue_injective_of_independent (ν := ν) Γ.klrQ Λ
    (linearIndependent_stendhalTerm hD hE hl hw hS extendedWord_spec)

include hD hE hl hw hS in
/-- Appending the terminal red strand identifies Webster's violating quotient with
the terminal-red corner (arXiv:1309.3796v2, Proposition 4.18). Independence uses
the loopless, weight-zero graph hypotheses of Proposition 4.16 as formalized here. -/
def appendRedEquiv :
    TensorProductAlgebra k Γ.klrQ (Λ ∘ Fin.castSucc) ν ≃ₐ[k] TensorProductAlgebra.lastRedCorner Γ.klrQ Λ ν :=
  AlgEquiv.ofBijective (appendRed Γ.klrQ Λ ν)
    ⟨appendRed_injective_of_stendhal ν Γ.klrQ Λ (appendRedStendhalValue_injective Γ Λ ν hD hE hl hw hS),
      appendRed_surjective Γ.klrQ Λ ν⟩

@[simp] theorem appendRedEquiv_apply (a : TensorProductAlgebra k Γ.klrQ (Λ ∘ Fin.castSucc) ν) :
    appendRedEquiv Γ Λ ν hD hE hl hw hS a = appendRed Γ.klrQ Λ ν a := rfl

end Graph

end Categorification.Stendhal
