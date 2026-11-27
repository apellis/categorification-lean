/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildePhiGradedLayers

/-!
# The layers of `T̃^λ e(s)` are the standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Corollary
5.23 (the `T̃^λ` form of Proposition 5.21): for a red-ordered loading `s` and every block
assignment `φ` of `s`, the map `S̃_{φ • s} → P̃_{≥φ}/P̃_{≻φ}`, `[e(φ • s)] ↦ [x̃_φ]`, is an
isomorphism of `T̃^λ`-modules (`tildePhiLayerEquiv`).

Injectivity is checked one homogeneous component at a time. For the component of degree `j`,
a red strand `λ₀` is added on the left with `λ₀` large relative to `j` and the degrees of the
`x̃_φ` (`extGrading` extends the grading to it), and
`mem_tildeLeftUpper_of_mul_mem_above` applies. This needs the dots on black strands to have
positive degree (`hpos`), so that a large `λ₀` exists. Route hypothesis:
`AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`.

## Main definitions

* `extGrading`: a grading for `(λ₀, λ)` restricting to a given grading for `λ`.
* `tildeRelLayerEquiv`: the isomorphism `S̃_{φ • s} ≅ P̃_{⪰φ}/P̃_{≻φ}`.

## Main results

* `restrict_extGrading`, `isHomogeneousSubspace_tildeRelAbove`,
  `mem_tildeLeftUpper_of_mul_mem_tildeAbove`,
  `tildeRelLayerMap_injective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module TypeA Equiv MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

section ExtGrading

variable (l0 : I →₀ ℕ) (G' : KLR.GradingDatum (stendhalQ Q Λ'))

/-- Degrees of dots for `(λ₀, λ)`: those of `G'`, and `0` on the new red strand. -/
def extDegX : I ⊕ Fin (ℓ + 1) → ℤ
  | .inl i => G'.degX (.inl i)
  | .inr r => Fin.cases 0 (fun r => G'.degX (.inr r)) r

/-- Degrees of crossings for `(λ₀, λ)`: those of `G'`; a black strand `i` crossing the new red
strand from the left has degree `λ₀(i) deg x_i`, from the right degree `0`. -/
def extDegΨ : I ⊕ Fin (ℓ + 1) → I ⊕ Fin (ℓ + 1) → ℤ
  | .inl i, .inl j => G'.degΨ (.inl i) (.inl j)
  | .inl i, .inr r => Fin.cases (l0 i * G'.degX (.inl i)) (fun r => G'.degΨ (.inl i) (.inr r)) r
  | .inr r, .inl i => Fin.cases 0 (fun r => G'.degΨ (.inr r) (.inl i)) r
  | .inr r, .inr r' => Fin.cases 0 (fun r => Fin.cases 0 (fun r' => G'.degΨ (.inr r) (.inr r')) r')
      r

/-- **A grading for `(λ₀, λ)` extending `G'`.** -/
def extGrading : KLR.GradingDatum (stendhalQ Q (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ)) where
  degX := extDegX Q Λ' G'
  degΨ := extDegΨ Q Λ' l0 G'
  degΨ_self a := by
    rcases a with i | r
    · exact G'.degΨ_self _
    · cases r using Fin.cases with
      | zero => simp [extDegΨ, extDegX]
      | succ r => exact G'.degΨ_self _
  isWeightedHomogeneous a b hab := by
    rcases a with i | r <;> rcases b with j | r'
    · exact G'.isWeightedHomogeneous (.inl i) (.inl j) (by simpa using hab)
    · cases r' using Fin.cases with
      | zero =>
        have h := (isWeightedHomogeneous_X k ![G'.degX (.inl i), 0] (0 : Fin 2)).pow (l0 i)
        have hd : extDegΨ Q Λ' l0 G' (.inl i) (.inr 0) + extDegΨ Q Λ' l0 G' (.inr 0) (.inl i) =
            l0 i • ![G'.degX (.inl i), 0] 0 := by
          simp [extDegΨ, mul_comm]
        change IsWeightedHomogeneous ![G'.degX (.inl i), 0] (X 0 ^ l0 i)
          (extDegΨ Q Λ' l0 G' (.inl i) (.inr 0) + extDegΨ Q Λ' l0 G' (.inr 0) (.inl i))
        rw [hd]
        exact h
      | succ r' => exact G'.isWeightedHomogeneous (.inl i) (.inr r') (by simp)
    · cases r using Fin.cases with
      | zero =>
        have h := (isWeightedHomogeneous_X k ![0, G'.degX (.inl j)] (1 : Fin 2)).pow (l0 j)
        have hd : extDegΨ Q Λ' l0 G' (.inr 0) (.inl j) + extDegΨ Q Λ' l0 G' (.inl j) (.inr 0) =
            l0 j • ![0, G'.degX (.inl j)] 1 := by
          simp [extDegΨ, mul_comm]
        change IsWeightedHomogeneous ![0, G'.degX (.inl j)] (X 1 ^ l0 j)
          (extDegΨ Q Λ' l0 G' (.inr 0) (.inl j) + extDegΨ Q Λ' l0 G' (.inl j) (.inr 0))
        rw [hd]
        exact h
      | succ r => exact G'.isWeightedHomogeneous (.inr r) (.inl j) (by simp)
    · exact isWeightedHomogeneous_zero _ _ _

omit [DecidableEq I] in
/-- The extension restricts to `G'`. -/
theorem restrict_extGrading :
    restrictFirstRedGrading Q (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) (extGrading Q Λ' l0 G') =
      G' := by
  obtain ⟨dX, dΨ, h1, h2⟩ := G'
  simp only [restrictFirstRedGrading, extGrading]
  congr 1
  · funext a
    rcases a with i | r <;> rfl
  · funext a b
    rcases a with i | r <;> rcases b with j | r' <;> rfl

end ExtGrading

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => StendhalAlgebra k Q Λ' ν

variable {Q Λ' ν}

/-- `P̃_{≻φ}` is a homogeneous subspace of `T̃^λ`. -/
theorem isHomogeneousSubspace_tildeRelAbove (G' : KLR.GradingDatum (stendhalQ Q Λ'))
    (ρ₀ : Perm (Fin m) → List ℕ) {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    (rel : PhiIndex s → PhiIndex s → Prop) (g : PhiIndex s) :
    IsHomogeneousSubspace (stendhalGrade G' ν)
      (((tildeRelAbove Q Λ' ρ₀ hs rel g).map (lIdeal (StendhalAlgebra.e s hs : B)).subtype
        ).restrictScalars k) := by
  classical
  simp only [Submodule.above, Submodule.map_iSup, Submodule.restrictScalars_iSup]
  refine IsHomogeneousSubspace.iSup fun g' => IsHomogeneousSubspace.iSup fun _ => ?_
  have hspan : ((tildePhiSub Q Λ' ρ₀ hs g').map (lIdeal (StendhalAlgebra.e s hs : B)).subtype
      ).restrictScalars k =
      (Submodule.span B {tildePhiElt Q Λ' ρ₀ hs g'.mem}).restrictScalars k := by
    rw [tildePhiSub, Submodule.map_span, Set.image_singleton]
    rfl
  rw [hspan]
  refine isHomogeneousSubspace_span (stendhalGrade G' ν) ?_
  rintro _ rfl j
  have hmem := tildePhiElt_mem_grade Q Λ' ν G' ρ₀ hs g'.mem
  by_cases hj : G'.degW (ρ₀ (phiPerm s g'.1)) s = j
  · rw [← hj, decompose_of_mem_same _ hmem]
    exact Submodule.subset_span rfl
  · rw [decompose_of_mem_ne _ hmem hj]
    exact zero_mem _

/-- **Injectivity of `S̃_{φ • s} → P̃_{≥φ}/P̃_{≻φ}`** (Webster, arXiv:1309.3796v3, proof of
Corollary 5.23): an element `y` of `T̃^λ e(φ • s)` with `y x̃_φ ∈ P̃_{≻φ}` lies in `Ũ_{φ • s}`.
The grading `G'` is bounded below on all red orders (`hc`) and gives the dots on black strands
positive degree (`hpos`), as Webster's grading does. Route hypothesis:
`AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`. -/
theorem mem_tildeLeftUpper_of_mul_mem_tildeAbove {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ')) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s)
    {rel : PhiIndex s → PhiIndex s → Prop} (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) (y : B)
    (hy : y ∈ lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B))
    (habove : y * tildePhiElt Q Λ' ρ₀ hs g.mem ∈
      (tildeRelAbove Q Λ' ρ₀ hs rel g).map (lIdeal (StendhalAlgebra.e s hs : B)).subtype) :
    y ∈ tildeLeftUpper Q Λ' ν (phiBottom s g.1) (g.isRedOrdered hs) := by
  classical
  set ℳ := stendhalGrade G' ν
  set d : PhiIndex s → ℤ := fun g => G'.degW (ρ₀ (phiPerm s g.1)) s
  have hAh := isHomogeneousSubspace_tildeRelAbove G' ρ₀ hs rel g
  have hμ : ∀ m', ∀ x ∈ ℳ m', LinearMap.mulRight k (tildePhiElt Q Λ' ρ₀ hs g.mem) x ∈
      ℳ (m' + d g) := fun m' x hx =>
    SetLike.GradedMul.mul_mem hx (tildePhiElt_mem_grade Q Λ' ν G' ρ₀ hs g.mem)
  have hcomp : ∀ j, (decompose ℳ y j : B) ∈
      tildeLeftUpper Q Λ' ν (phiBottom s g.1) (g.isRedOrdered hs) := by
    intro j
    set n := j + d g
    set N : ℤ := |n| + ∑ g', |n - d g'|
    have hsum0 : 0 ≤ ∑ g', |n - d g'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hnN : n ≤ N := (le_abs_self n).trans (le_add_of_nonneg_right hsum0)
    have hN : ∀ g', n - d g' ≤ N := fun g' => by
      have h1 : |n - d g'| ≤ ∑ g'', |n - d g''| :=
        Finset.single_le_sum (f := fun g'' => |n - d g''|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ g')
      have h2 := le_abs_self (n - d g')
      have h3 := abs_nonneg n
      change _ ≤ |n| + ∑ g'', |n - d g''|
      omega
    set K : ℕ := (N + 2 * c).toNat + 1
    set l0 : I →₀ ℕ := K • Multiset.toFinsupp ν
    have hl0 : ∀ i ∈ ν, K ≤ l0 i := fun i hi => by
      simp only [l0, Finsupp.smul_apply, Multiset.toFinsupp_apply, smul_eq_mul]
      exact Nat.le_mul_of_pos_right _ (Multiset.count_pos.2 hi)
    have hΛ : ∀ i ∈ ν, N + 2 * c < ((Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) 0) i *
        (extGrading Q Λ' l0 G').degX (.inl i) := fun i hi => by
      change N + 2 * c < (l0 i : ℤ) * G'.degX (.inl i)
      have h1 : (K : ℤ) ≤ l0 i := by exact_mod_cast hl0 i hi
      have h2 := hpos i hi
      have h3 : N + 2 * c < (K : ℤ) := by
        have := Int.self_le_toNat (N + 2 * c)
        simp only [K, Nat.cast_add, Nat.cast_one]
        omega
      nlinarith
    have hG := restrict_extGrading Q Λ' l0 G'
    have hc' : ∀ m' < -c, allOrdersGrade (restrictFirstRedGrading Q
        (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) (extGrading Q Λ' l0 G')) ν m' = ⊥ := by
      rw [hG]
      exact hc
    have hN' : ∀ g' : PhiIndex s, n - GradingDatum.degW (restrictFirstRedGrading Q
        (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) (extGrading Q Λ' l0 G'))
          (ρ₀ (phiPerm s g'.1)) s ≤ N := by
      rw [hG]
      exact hN
    have hyj : (decompose ℳ y j : B) ∈
        lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B) :=
      isHomogeneousSubspace_lIdeal_of_mem_zero ℳ (e_mem_stendhalGrade G' ν _ _) j y hy
    have hdeg : (decompose ℳ y j : B) ∈ stendhalGrade (restrictFirstRedGrading Q
        (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) (extGrading Q Λ' l0 G')) ν
          (n - GradingDatum.degW (restrictFirstRedGrading Q
            (Fin.cons l0 Λ' : Fin (ℓ + 1) → I →₀ ℕ) (extGrading Q Λ' l0 G'))
              (ρ₀ (phiPerm s g.1)) s) := by
      rw [hG]
      change (decompose ℳ y j : B) ∈ ℳ (j + d g - d g)
      rw [add_sub_cancel_right]
      exact (decompose ℳ y j).2
    have habj : (decompose ℳ y j : B) * tildePhiElt Q Λ' ρ₀ hs g.mem ∈
        (tildeRelAbove Q Λ' ρ₀ hs rel g).map (lIdeal (StendhalAlgebra.e s hs : B)).subtype := by
      have h1 := decompose_map_of_shift hμ y (j + d g)
      rw [add_sub_cancel_right] at h1
      have h2 := hAh (j + d g) (y * tildePhiElt Q Λ' ρ₀ hs g.mem) habove
      rw [← LinearMap.mulRight_apply (R := k), h1, LinearMap.mulRight_apply] at h2
      exact h2
    exact mem_tildeLeftUpper_of_mul_mem_above (extGrading Q Λ' l0 G') hQ hR hall ρ₀ hρ₀ hc' hΛ
      s hs hnN hN' hirr htr hrel g _ hyj hdeg habj
  rw [← sum_support_decompose ℳ y]
  exact Submodule.sum_mem _ fun j _ => hcomp j

/-- `S̃_{φ • s} → P̃_{≥φ}/P̃_{≻φ}` is injective, under the hypotheses of
`mem_tildeLeftUpper_of_mul_mem_tildeAbove`. Route hypothesis: `AllFiniteDeltaInjective`. -/
theorem tildeRelLayerMap_injective {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ')) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s)
    {rel : PhiIndex s → PhiIndex s → Prop} (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) :
    Function.Injective (tildeRelLayerMap Q Λ' ρ₀ hs hρ₀ hrel g) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [tildeRelLayerMap_mk, tildeRelLayerGen, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hv
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact mem_tildeLeftUpper_of_mul_mem_tildeAbove hQ hR hall G' ρ₀ hρ₀ hc hpos s hs hirr htr hrel g
    (y : B) y.2 ⟨_, hv, rfl⟩

/-- **The layers of `T̃^λ e(s)` are the standard modules** (Webster, arXiv:1309.3796v3,
Corollary 5.23, the `T̃^λ` form of Proposition 5.21): `S̃_{φ • s} ≅ P̃_{≥φ}/P̃_{≻φ}` as
`T̃^λ`-modules, `[e(φ • s)] ↦ [x̃_φ]`. Hypotheses on the grading as in
`mem_tildeLeftUpper_of_mul_mem_tildeAbove`. Route hypothesis: `AllFiniteDeltaInjective`,
inherited from `phiLayerEquiv`. -/
def tildeRelLayerEquiv {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ')) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s)
    {rel : PhiIndex s → PhiIndex s → Prop} (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) :
    tildeStandard Q Λ' (phiBottom s g.1) (g.isRedOrdered hs) ≃ₗ[B]
      tildeRelLayer Q Λ' ρ₀ hs rel g :=
  LinearEquiv.ofBijective (tildeRelLayerMap Q Λ' ρ₀ hs hρ₀ hrel g)
    ⟨tildeRelLayerMap_injective hQ hR hall G' ρ₀ hρ₀ hc hpos s hs hirr htr hrel g,
      tildeRelLayerMap_surjective ρ₀ hs hρ₀ hrel g⟩

theorem tildeRelLayerEquiv_apply {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ')) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s)
    {rel : PhiIndex s → PhiIndex s → Prop} (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) (v : tildeStandard Q Λ' (phiBottom s g.1) (g.isRedOrdered hs)) :
    tildeRelLayerEquiv hQ hR hall G' ρ₀ hρ₀ hc hpos s hs hirr htr hrel g v =
      tildeRelLayerMap Q Λ' ρ₀ hs hρ₀ hrel g v :=
  rfl

end Categorification.Stendhal
