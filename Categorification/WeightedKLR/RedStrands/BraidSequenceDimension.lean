/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingDimension
import Categorification.WeightedKLR.RedStrands.RightSequenceWordExpansion
import Categorification.WeightedKLR.RedStrands.GradedBraidRowClass

set_option backward.isDefEq.respectTransparency false

/-!
# The dimension of the braid of a sequence projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11, step `p_n → f_n`. Let the class map of `𝔅_w` be `x ↦ B(f x, -)` with `f`
congruent at `v = 1` to the permutation of the tensor factors by `w`. The class of
`e(t) T^λ` is `Σ_{(d, u)} v^d F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}` over the monomials
`loadingMono` of `t`; the permutation sends the word tensor of `u` to that of `u ∘ w`, which is
the class of the right row standard of `u ∘ w` (Proposition 5.6). So
`dim 𝔅_w (e(t) T^λ) = Σ_{(d, u)} dim S_{u ∘ w}` (`finrank_braidF_rightSequence`).

## Main results

* `blockContent_of_mem_loadingMono`: every monomial of a loading has the black content of the
  loading.
* `tensorPermute_monoSum`: the permutation of the factors on a sum of word tensors.
* `finrank_braidF_rightSequence`: the dimension count.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)

/-! ### Black contents of monomials -/

section Content

variable {I : Type} [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}

omit [DecidableEq I] in
theorem blockContent_comp_equiv {n : ℕ} (u : Fin n → List I) (w : Equiv.Perm (Fin n)) :
    blockContent (u ∘ w) = blockContent u :=
  Fintype.sum_equiv w _ _ fun _ => rfl

omit [DecidableEq I] in
theorem blockContent_lastCases {n : ℕ} (a : List I) (u : Fin n → List I) :
    blockContent (Fin.lastCases a u : Fin (n + 1) → List I) = blockContent u + a := by
  rw [blockContent, Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  rfl

theorem blockContent_of_mem_wordF (i : I) : ∀ {n : ℕ} (wt : Fin n → Dom R)
    (u : Fin n → List I) {p : ℤ × (Fin n → List I)}, p ∈ wordF i wt u →
    blockContent p.2 = blockContent u + {i}
  | 0, _, _, _, hp => by simp [wordF] at hp
  | n + 1, wt, u, p, hp => by
    rw [wordF, List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with ⟨q, hq, rfl⟩ | rfl
    · rw [blockContent_lastCases, blockContent_of_mem_wordF i _ _ hq, ← blockContent_succ u]
      abel
    · rw [blockContent_lastCases, ← blockContent_succ u, ← Multiset.coe_add,
        Multiset.coe_singleton]
      abel

theorem blockContent_of_mem_monoF (i : I) {n : ℕ} (wt : Fin n → Dom R)
    {l : List (ℤ × (Fin n → List I))} {c : Multiset I}
    (hl : ∀ p ∈ l, blockContent p.2 = c) {p : ℤ × (Fin n → List I)} (hp : p ∈ monoF i wt l) :
    blockContent p.2 = c + {i} := by
  rw [monoF, List.mem_flatMap] at hp
  obtain ⟨q, hq, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  rw [blockContent_of_mem_wordF i wt q.2 hr, hl q hq]

variable {J : Type*}

/-- The black letters of a loading. -/
def blackLetters (s : List (I ⊕ J)) : Multiset I := (s.filterMap Sum.getLeft? : List I)

theorem blockContent_of_mem_monoReverse : ∀ (s : List (I ⊕ J)) {n : ℕ} (wt : Fin n → Dom R)
    {p : ℤ × (Fin n → List I)}, p ∈ monoReverse s wt → blockContent p.2 = blackLetters s
  | [], 0, _, p, hp => by
    rw [monoReverse, List.mem_singleton] at hp
    subst hp
    simp [blockContent, blackLetters]
  | [], _ + 1, _, _, hp => by simp [monoReverse] at hp
  | .inl i :: s, _, wt, p, hp => by
    classical
    rw [monoReverse] at hp
    rw [blockContent_of_mem_monoF i wt (fun q hq => blockContent_of_mem_monoReverse s wt hq) hp]
    simp [blackLetters, add_comm]
  | .inr _ :: _, 0, _, _, hp => by simp [monoReverse] at hp
  | .inr _ :: s, _ + 1, wt, p, hp => by
    rw [monoReverse, monoRed, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [blockContent_lastCases, blockContent_of_mem_monoReverse s _ hq]
    simp [blackLetters]

theorem blockContent_of_mem_loadingMono (s : List (I ⊕ J)) {n : ℕ} (wt : Fin n → Dom R)
    {p : ℤ × (Fin n → List I)} (hp : p ∈ loadingMono wt s) :
    blockContent p.2 = blackLetters s := by
  rw [blockContent_of_mem_monoReverse s.reverse wt hp, blackLetters, blackLetters,
    List.filterMap_reverse, Multiset.coe_reverse]

omit [DecidableEq I] in
theorem blackLetters_toList {ℓ : ℕ} {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) :
    blackLetters (Seq.toList t) = ν := by
  rw [blackLetters, ← Multiset.filterMap_coe, Seq.coe_toList, stendhalWeight,
    Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map]
  have h1 : (Sum.getLeft? ∘ (Sum.inl : I → I ⊕ Fin ℓ)) = some := funext fun _ => rfl
  have h2 : ∀ s : Multiset (Fin ℓ), Multiset.filterMap (Sum.getLeft? ∘ (Sum.inr : Fin ℓ → I ⊕ Fin ℓ))
      s = 0 := fun s => by
    induction s using Multiset.induction_on with
    | empty => rfl
    | cons a s ih => rw [Multiset.filterMap_cons_none a s rfl, ih]
  rw [h1, h2, Multiset.filterMap_some, add_zero]

end Content

/-! ### Permuting word tensors -/

section Permute

variable {I : Type} [Finite I] [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} {n : ℕ}

omit [Finite I] in
theorem tensorPermute_wordTensor (wt : Fin n → Dom R) (w : Equiv.Perm (Fin n))
    (u : Fin n → List I) :
    tensorPermute wt w (wordTensor C wt u) = wordTensor C (wt ∘ w) (u ∘ w) := by
  rw [wordTensor, tensorPermute_tprod]
  rfl

omit [Finite I] in
/-- The permutation of the tensor factors on a sum of word tensors. -/
theorem tensorPermute_monoSum (wt : Fin n → Dom R) (w : Equiv.Perm (Fin n))
    (l : List (ℤ × (Fin n → List I))) :
    tensorPermute wt w (monoSum (C := C) wt l) =
      (l.map fun p => (𝕍 ^ p.1 : 𝕂) • wordTensor C (wt ∘ w) (p.2 ∘ w)).sum := by
  rw [monoSum, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [Function.comp_apply, map_smul, tensorPermute_wordTensor]

end Permute

/-! ### The dimension count -/

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- A right row standard, with its black content written as `ν`. -/
theorem exists_rightRowStandard_class {ν : Multiset I} (u : Fin ℓ → List I)
    (hν : blockContent u = ν) :
    ∃ S : GFin (oppositeGrade (tensorProductGrade (stendhalGradingDatum Λ hQ.gradingDatum
        (fun i => C.dot i i / 2) (dotDegree C hQ)) ν)),
      classFunctional C hQ hR Λ wt hwt ν S = TensorPairing.orderedForm hR wt (wordTensor C wt u) ∧
        Module.finrank k S.carrier = Module.finrank k (rightRowStandard C hQ Λ u).carrier := by
  subst hν
  exact ⟨rightRowStandard C hQ Λ u, classFunctional_rightRowStandard_eq C hQ hR Λ wt hwt u, rfl⟩

/-- **The dimension of the braid of a sequence projective** (Webster, arXiv:1309.3796v2, proof
of Lemma 6.11, step `p_n → f_n`): if the class map of `𝔅_w` is `x ↦ B(f x, -)` with `f`
congruent at `v = 1` to the permutation of the factors by `w`, then
`dim 𝔅_w (e(t) T^λ) = Σ_{(d, u)} dim S_{u ∘ w}`, over the monomials `(d, u)` of the loading
`t`, where `S_{u ∘ w}` is the right row standard of `u ∘ w` for the labels `λ ∘ w`. -/
theorem finrank_braidF_rightSequence (w : Equiv.Perm (Fin ℓ))
    (f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ w))
    (hf : VOneCongr f (tensorPermute wt w).toLinearMap)
    (hcls : braidClass C hQ hR Λ wt hwt w = (formDual hR (wt ∘ w)).comp f)
    {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    Module.finrank k (braidF C hQ Λ w ν (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
        (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht).toGFin).carrier =
      ((loadingMono wt (Seq.toList t)).map fun p =>
        Module.finrank k (rightRowStandard C hQ (Λ ∘ w) (p.2 ∘ w)).carrier).sum := by
  have : ∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q (Λ ∘ w) ν)ᵐᵒᵖ :=
    fun ν => Module.Finite.equiv (MulOpposite.opLinearEquiv k)
  set l := loadingMono wt (Seq.toList t)
  have hc : ∀ p ∈ l, blockContent (p.2 ∘ w) = ν := fun p hp => by
    rw [blockContent_comp_equiv, blockContent_of_mem_loadingMono _ wt hp, blackLetters_toList]
  choose S hS hdim using fun c : {p // p ∈ l} => exists_rightRowStandard_class C hQ hR
    (Λ ∘ w) (wt ∘ w) (fun r i => hwt (w r) i) (c.1.2 ∘ w) (hc c.1 c.2)
  set a := (rightTensorModuleEquiv C hQ hR Λ wt hwt (DirectSum.lof LP _
    (rightTensorProjectiveGroup C hQ Λ) ν (K0.of (rightSequenceProj (stendhalGradingDatum Λ
      hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht))) : TensorSpace wt)
  have ha : a = monoSum (C := C) wt l :=
    rightTensorModuleEquiv_rightSequence_eq_monoSum C hQ hR Λ wt hwt t ht
  have hN := braidClass_of C hQ hR Λ wt hwt w ν (rightSequenceProj (stendhalGradingDatum Λ
      hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht)
  rw [hcls, LinearMap.comp_apply, formDual_apply] at hN
  have h := finrank_eq_sum_of_vOneCongr C hQ hR (Λ ∘ w) (wt ∘ w) (fun r i => hwt (w r) i) hf
    (a := a) (Subtype.prop _) ν _ (ConjDual.of.injective hN).symm l.attach S
    (fun c => wordTensor C (wt ∘ w) (c.1.2 ∘ w)) (fun c => c.1.1) hS ?_
  · rw [h, List.map_congr_left fun c _ => hdim c]
    exact congrArg List.sum (List.attach_map_val (l := l) (f := fun p =>
      Module.finrank k (rightRowStandard C hQ (Λ ∘ w) (p.2 ∘ w)).carrier))
  · rw [LinearEquiv.coe_coe, ha, tensorPermute_monoSum]
    exact (congrArg List.sum (List.attach_map_val (l := l) (f := fun p =>
      (𝕍 ^ p.1 : 𝕂) • wordTensor C (wt ∘ w) (p.2 ∘ w)))).symm

end Categorification.Stendhal.FirstWeight
