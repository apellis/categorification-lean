/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackSurjective

/-!
# The violating ideal and the bimodule map of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. The map `g ↦ appendRed(g) · crossingStendhalCut` of
`Categorification.Stendhal.lastRedBlackStendhal` carries the violating ideal of the algebra on
the first `ℓ` red strands onto the part of the violating ideal in `e_ℓ T̃_{i+ν} ν_i(e_ℓ)`.
A diagram in this part is cut at a violated slice; the last red strand ends at the far right,
so it can be moved to the far right of that slice, which stays violated. The diagram then
factors through a violated idempotent with the last red strand on the right, which comes from
the smaller algebra, followed by a diagram in the image of `lastRedBlackStendhal`.

Consequently injectivity of `lastRedBlackStendhal` (on `T̃_{i+ν} ν_i(1)`) gives injectivity of
`lastRedBlackMap` on `T_{i+ν} ν_i(1)`.

## Main results

* `terminalMirrorWord`: reduced words that first move the strand ending at the far right to the
  far right of the bottom loading.
* `exists_violated_lastRedBlackStendhal`: the violating ideal, cut by `e_ℓ` on top and by
  `ν_i(e_ℓ)` at the bottom, is the image of the earlier violating ideal.
* `lastRedBlackMap_eq_zero`: if `lastRedBlackStendhal g = 0` forces `g · ν_i(1) = 0`, the same
  holds for `lastRedBlackMap` in the violating quotient.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

section Mirror

variable {I : Type} {ℓ : ℕ} {β : Multiset I}

local notation "M" => stendhalWeight (ℓ + 1) β

/-- Reduced words whose first letters (at the bottom of the diagram) move the strand that ends
at the far right of the top loading to the far right of the bottom loading. They are the
reversed words of `terminalWord` for the inverse permutation. -/
def terminalMirrorWord (w : Perm (Fin (Multiset.card M))) : List ℕ :=
  (terminalWord (ℓ := ℓ) (ν := β) w⁻¹).reverse

theorem terminalMirrorWord_spec (w : Perm (Fin (Multiset.card M))) :
    IsReduced (Multiset.card M) (terminalMirrorWord w) ∧
      wordProd (Multiset.card M) (terminalMirrorWord w) = w :=
  ⟨reversed_reduced (terminalWord_spec w⁻¹).1, by
    rw [terminalMirrorWord, wordProd_reverse, terminalWord_prod, inv_inv]⟩

theorem terminalMirrorWord_prod (w : Perm (Fin (Multiset.card M))) :
    wordProd (Multiset.card M) (terminalMirrorWord w) = w :=
  (terminalMirrorWord_spec w).2

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "A" => StendhalAlgebraAllOrders k Q Λ β
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ β
local notation "hρ" => terminalMirrorWord_prod (ℓ := ℓ) (β := β)
local notation "Term" =>
  {b // IsStendhalTerm (ν := β) (ℓ := ℓ + 1) terminalMirrorWord b}

/-- A Stendhal term from a violated loading to a loading ending with the last red strand
factors through a violated loading ending with the last red strand. -/
theorem factor_through_mirror_violation (b : Term) (ht : HasLastRed (b.1.2.1 • b.1.1))
    (hv : IsViolated b.1.1) :
    ∃ (t : KLR.Seq M), IsRedOrdered t ∧ HasLastRed t ∧ IsViolated t ∧
      ∃ l r : A, (stendhalTerm Q Λ hρ b).val = l * StendhalAlgebraAllOrders.e t * r := by
  obtain ⟨⟨s, w, f⟩, hb⟩ := b
  dsimp only at ht hv ⊢
  let a : Fin (Multiset.card M) := w⁻¹ (lastRedPosition ℓ β)
  let C := KLR.cycA (m := Multiset.card M) (n := β.card + ℓ) a.val
  let D := (terminalPrefix (ℓ := ℓ) (ν := β) w⁻¹).reverse
  let R := (terminalRest (ℓ := ℓ) (ν := β) w⁻¹).reverse
  have hD : wordProd (Multiset.card M) D = C := by
    change wordProd _ (terminalPrefix w⁻¹).reverse = _
    rw [wordProd_reverse, show wordProd (Multiset.card M) (terminalPrefix (ℓ := ℓ) (ν := β) w⁻¹) =
      C⁻¹ from wordProd_reverse _ _, inv_inv]
  have ha : s.lbl a = Sum.inr (Fin.last ℓ) := ht
  have h := slide_terminal_loading s hb.1 hv a ha
  refine ⟨C • s, h.1, h.2.1, h.2.2, π (ψw R),
    π (ψw D * pol (MvPolynomial.monomial f 1) * KLRAlgebra.e s), ?_⟩
  have hcut : (KLRAlgebra.e (C • s) : KLRAlgebra k (stendhalQ Q Λ) M) *
      (ψw D * pol (MvPolynomial.monomial f 1) * KLRAlgebra.e s) =
      ψw D * pol (MvPolynomial.monomial f 1) * KLRAlgebra.e s := by
    rw [e_mul_gen, hD, inv_smul_smul, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rw [stendhalTerm_val, stdElt]
  change π ((ψw (terminalWord (ℓ := ℓ) (ν := β) w⁻¹).reverse) * _ * KLRAlgebra.e s) =
    π _ * π (KLRAlgebra.e (C • s)) * π _
  rw [terminalWord, List.reverse_append, ψw_append, mul_assoc (π (ψw R)),
    ← map_mul π (KLRAlgebra.e (C • s)), hcut]
  simp only [map_mul, mul_assoc]
  rfl

end Mirror

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ₀" => (Λ ∘ Fin.castSucc)

section Stendhal

local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ
local notation "P'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ
local notation "S" => StendhalAlgebra k Q Λ νᵢ
local notation "E" => StendhalAlgebra.lastRedIdem Q Λ νᵢ
local notation "J₀" => StendhalAlgebra.violatedIdeal k Q Λ₀ νᵢ
local notation "L" => lastRedBlackStendhal Q Λ i ν
local notation "rb" => redBlackStendhal Q Λ i ν (1 : StendhalAlgebra k Q Λ₀ ν)

/-- A diagram of `e_ℓ T̃_{i+ν} ν_i(e_ℓ)` cut at a violated loading ending with the last red
strand is the image of an element of the earlier violating ideal. -/
theorem exists_violated_lastRedBlackStendhal_of_cut
    (t : KLR.Seq (stendhalWeight (ℓ + 1) νᵢ)) (ho : IsRedOrdered t) (hs : HasLastRed t)
    (hV : IsViolated t) (X Y : A) :
    ∃ v ∈ J₀, (L v).val =
      (E).val * X * StendhalAlgebraAllOrders.e t * Y * (rb).val := by
  obtain ⟨v₁, h₁, hv₁⟩ := exists_violated_preimage_of_terminal_cut νᵢ Q Λ t ho hs hV X 1
  have hP : P' * P' = P' := StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq
  let W : S := ⟨P' * (StendhalAlgebraAllOrders.e t * Y * (rb).val) * P',
    (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
      ⟨by rw [← mul_assoc, ← mul_assoc, hP], by rw [mul_assoc, hP]⟩⟩
  obtain ⟨g, hg⟩ := exists_lastRedBlackStendhal Q Λ i ν W
  refine ⟨v₁ * g, TwoSidedIdeal.mul_mem_right _ _ _ h₁, ?_⟩
  have hL : L (v₁ * g) = appendRedStendhalValue Q Λ νᵢ v₁ * L g := by
    rw [lastRedBlackStendhal_apply, lastRedBlackStendhal_apply, map_mul, mul_assoc]
  have hr : StendhalAlgebraAllOrders.e t * (E).val = StendhalAlgebraAllOrders.e t := by
    have h := StendhalAlgebra.e_mul_lastRedIdem Q Λ νᵢ t ho
    rw [ite_eq_left_of_eq_true _ _ (eq_true hs)] at h
    exact congrArg (fun z : S => z.val) h
  have h1 : ∀ z : A, StendhalAlgebraAllOrders.e t * ((E).val * z) =
      StendhalAlgebraAllOrders.e t * z := fun z => by rw [← mul_assoc, hr]
  have h3 : ∀ z : A, StendhalAlgebraAllOrders.e t * (P' * z) =
      StendhalAlgebraAllOrders.e t * z := fun z => by
    rw [← mul_assoc, StendhalAlgebraAllOrders.e_mul_redOrderedIdem,
      ite_eq_left_of_eq_true _ _ (eq_true ho)]
  have h4 : ∀ z : A, StendhalAlgebraAllOrders.e t * (StendhalAlgebraAllOrders.e t * z) =
      StendhalAlgebraAllOrders.e t * z := fun z => by
    rw [← mul_assoc, StendhalAlgebraAllOrders.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hrb : (rb).val * (rb).val = (rb).val := by
    rw [← KLR.Corner.val_mul, ← map_mul, mul_one]
  have h5 : (rb).val * (P' * (rb).val) = (rb).val := by
    rw [← mul_assoc, KLR.Corner.val_mul_E, hrb]
  rw [hL, hg, KLR.Corner.val_mul, hv₁, KLR.Corner.val_mul, KLR.Corner.val_mul]
  change (E).val * X * StendhalAlgebraAllOrders.e t * 1 * (E).val *
    ((E).val * (P' * (StendhalAlgebraAllOrders.e t * Y * (rb).val) * P') * (rb).val) = _
  simp only [mul_assoc, one_mul, h1, h3, h4, h5]

/-- **The violating ideal in Proposition 4.32** (Webster, arXiv:1309.3796v3): an element of the
violating ideal, cut by `e_ℓ` on top and by `ν_i(e_ℓ)` at the bottom, is the image under
`lastRedBlackStendhal` of an element of the violating ideal on the first `ℓ` red strands. -/
theorem exists_violated_lastRedBlackStendhal (x : S)
    (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ νᵢ) :
    ∃ v ∈ J₀, L v = E * x * rb := by
  classical
  have h := (mem_violatedIdeal_iff (Q := Q) (Λ := Λ)
    (terminalMirrorWord_spec (ℓ := ℓ) (β := νᵢ)) x).1 hx
  clear hx
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, c, hv, hs, rfl⟩ := hx
    by_cases hb : HasLastRed (b.1.2.1 • b.1.1)
    · obtain ⟨t, ho, he, hV, l, r, hEq⟩ := factor_through_mirror_violation Q Λ b hb hv
      obtain ⟨v, h₀, hval⟩ := exists_violated_lastRedBlackStendhal_of_cut Q Λ i ν t ho he hV l
        (r * (stendhalTerm Q Λ (fun w => (terminalMirrorWord_spec (ℓ := ℓ) (β := νᵢ) w).2)
          c).val)
      refine ⟨v, h₀, Subtype.ext ?_⟩
      rw [hval, KLR.Corner.val_mul, KLR.Corner.val_mul, KLR.Corner.val_mul, hEq]
      simp only [mul_assoc]
    · have he : E * stendhalTerm Q Λ
          (fun w => (terminalMirrorWord_spec (ℓ := ℓ) (β := νᵢ) w).2) b = 0 := by
        rw [← e_mul_stendhalTerm _ b _ b.2.2.1 |>.trans
            (ite_eq_left_of_eq_true _ _ (eq_true rfl)), ← mul_assoc,
          StendhalAlgebra.lastRedIdem_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hb),
          zero_mul]
      exact ⟨0, zero_mem _, by rw [map_zero, ← mul_assoc, he, zero_mul, zero_mul]⟩
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, mul_zero, zero_mul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, heu⟩ := hx
    obtain ⟨v, hv, hev⟩ := hy
    exact ⟨u + v, add_mem hu hv, by rw [map_add, heu, hev, mul_add, add_mul]⟩
  | smul c x _ hx =>
    obtain ⟨v, hv, he⟩ := hx
    refine ⟨c • v, ?_, ?_⟩
    · rw [Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hv
    · rw [map_smul, he, mul_smul_comm, smul_mul_assoc]

/-- The values of `lastRedBlackStendhal` lie in `e_ℓ T̃_{i+ν} ν_i(e_ℓ)`. -/
theorem lastRedIdem_mul_lastRedBlackStendhal_mul (g : StendhalAlgebra k Q Λ₀ νᵢ) :
    E * L g * rb = L g := by
  have hE : E * appendRedStendhalValue Q Λ νᵢ g = appendRedStendhalValue Q Λ νᵢ g := by
    rw [← appendRedStendhalValue_one, ← map_mul, one_mul]
  have hc : crossingStendhalCut Q Λ i ν * rb = crossingStendhalCut Q Λ i ν := by
    rw [crossingStendhalCut, mul_assoc, ← map_mul, mul_one]
  rw [lastRedBlackStendhal_apply, ← mul_assoc, hE, mul_assoc, hc]

end Stendhal

section Quotient

local notation "T₀'" => TensorProductAlgebra k Q Λ₀ νᵢ

/-- **Injectivity in Proposition 4.32, reduced to diagrams** (Webster, arXiv:1309.3796v3): if
`lastRedBlackStendhal g = 0` implies `g · ν_i(1) = 0` before taking the violating quotients,
then `lastRedBlackMap g = 0` implies `g · ν_i(1) = 0` in `T₀_{i+ν}`. -/
theorem lastRedBlackMap_eq_zero
    (hL : ∀ g, lastRedBlackStendhal Q Λ i ν g = 0 →
      g * appendBlackStendhal Q Λ₀ i ν 1 = 0)
    (g : T₀') (hg : lastRedBlackMap Q Λ i ν g = 0) :
    g * appendBlack Q Λ₀ i ν 1 = 0 := by
  obtain ⟨x, rfl⟩ := (StendhalAlgebra.violatedIdeal k Q Λ₀ νᵢ).ringCon.mk'_surjective g
  have hmk : ∀ {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {β : Multiset I} (z : StendhalAlgebra k Q Λ' β),
      TensorProductAlgebra.mk Q Λ' β z = 0 ↔ z ∈ StendhalAlgebra.violatedIdeal k Q Λ' β :=
    fun z => by
      change (StendhalAlgebra.violatedIdeal k Q _ _).ringCon.mk' z = 0 ↔ _
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  have hx : lastRedBlackStendhal Q Λ i ν x ∈ StendhalAlgebra.violatedIdeal k Q Λ νᵢ := by
    rw [← hmk]
    rw [← hg, lastRedBlackMap_apply, lastRedBlackStendhal_apply, map_mul]
    rfl
  obtain ⟨v, hv, hLv⟩ := exists_violated_lastRedBlackStendhal Q Λ i ν _ hx
  rw [lastRedIdem_mul_lastRedBlackStendhal_mul] at hLv
  have h0 := hL (x - v) (by rw [map_sub, hLv, sub_self])
  rw [sub_mul, sub_eq_zero] at h0
  have h1 : (1 : TensorProductAlgebra k Q Λ₀ ν) = TensorProductAlgebra.mk Q Λ₀ ν 1 :=
    (map_one _).symm
  change TensorProductAlgebra.mk Q Λ₀ νᵢ x * appendBlack Q Λ₀ i ν 1 = 0
  rw [h1, appendBlack_mk, ← map_mul, hmk, h0]
  exact TwoSidedIdeal.mul_mem_right _ _ _ hv

end Quotient

end Categorification.Stendhal
