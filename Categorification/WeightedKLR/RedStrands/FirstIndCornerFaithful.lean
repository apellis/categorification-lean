/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerFaithfulModule
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount
import Categorification.WeightedKLR.RedStrands.RedFirstDoubleCentralizer
import Categorification.WeightedKLR.RedStrands.RedFirstReach
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty

set_option backward.isDefEq.respectTransparency false

/-!
# Black induction and modules without submodules killed by `e⁰`

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.30, (2) ⇒ (3), and Corollary 5.32 (v2: Theorem 5.27 and
Corollary 5.29): no nonzero submodule of a standard module is killed by the red-first idempotent
`e⁰`. Two steps of the induction proving this are here.

* `isCornerFaithfulModule_firstIndF`: at the standard Khovanov–Lauda parameters, if `S N` has no
  nonzero submodule killed by `e⁰`, neither has `Fⱼ S(N)`. A finite-dimensional module of this
  kind embeds into a free module (the pairing on `P⁰ = T^λ e⁰`), induction along `appendBlack`
  preserves injections (Theorem 4.31), and `T^λ` acts faithfully on `e⁰ T^λ` (Lemma 5.23,
  reflected).
* `isCornerFaithfulModule_lastIndBase`: with no black strand in the first block, `e⁰` acts as the
  identity on `S(₂Fᵢ N)`, since every other red-ordered loading puts the black strand left of
  the last red strand.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}

local notation "Si" j => (Singleton.singleton j : Multiset I)

section Cast

variable (Q : I → I → MvPolynomial (Fin 2) k) {m : ℕ} (Λ : Fin m → I →₀ ℕ)

theorem castTensorProductAlgebra_redFirstIdem {ν ν' : Multiset I} (h : ν = ν') :
    castTensorProductAlgebra Q Λ h (redFirstIdem Q Λ ν) = redFirstIdem Q Λ ν' := by
  subst h; rfl

theorem castTensorProductAlgebra_symm_redFirstIdem {ν ν' : Multiset I} (h : ν = ν') :
    (castTensorProductAlgebra Q Λ h).symm (redFirstIdem Q Λ ν') = redFirstIdem Q Λ ν := by
  subst h; rfl

end Cast

section Induction

variable {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

include hR hQs in
/-- `T^λ` acts faithfully on `e⁰ T^λ` from the right: the reflection of
`eq_zero_of_mul_redFirstProjective` (Webster, arXiv:1309.3796v2, Lemma 5.23). -/
private theorem eq_zero_of_forall_redFirstIdem_mul_mul (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) (y : TensorProductAlgebra k QL Λ ν)
    (hy : ∀ b, redFirstIdem QL Λ ν * b * y = 0) : y = 0 := by
  have hz : tensorFlip y = 0 := eq_zero_of_mul_redFirstProjective hR hQs Λ ν _ fun c hc => by
    have h1 : tensorFlip c = redFirstIdem QL Λ ν * tensorFlip c := by
      conv_lhs => rw [← hc]
      rw [tensorFlip_mul, tensorFlip_redFirstIdem]
    calc tensorFlip y * c = tensorFlip (tensorFlip c * y) := by
          rw [tensorFlip_mul, tensorFlip_tensorFlip]
      _ = 0 := by rw [h1, hy, map_zero]
  rw [← tensorFlip_tensorFlip y, hz, map_zero]

variable (Λ : Fin (ℓ + 1) → I →₀ ℕ)

include hR in
/-- **`Fⱼ` preserves the absence of submodules killed by `e⁰`** (Webster, arXiv:1309.3796v3,
proof of Theorem 5.30, (2) ⇒ (3)): if `S N` has no nonzero submodule killed by `e⁰` and `N` is
finite-dimensional, then neither has `Fⱼ S(N)`. -/
theorem isCornerFaithfulModule_firstIndF (j : I) (θ β : Multiset I) (Z : Type) [AddCommGroup Z]
    [Module k Z] [Module (parabolicFactorAlgebra QL Λ θ β) Z]
    [IsScalarTower k (parabolicFactorAlgebra QL Λ θ β) Z] [FiniteDimensional k Z]
    (h : IsCornerFaithfulModule (redFirstIdem QL Λ (θ + β))
      (ParabolicStandardT QL Λ θ β Z hQs)) :
    IsCornerFaithfulModule (redFirstIdem QL Λ ((Si j) + (θ + β)))
      (FirstIndF QL Λ j θ β Z hQs) := by
  have : FiniteDimensional k (ParabolicStandardT QL Λ θ β Z hQs) :=
    finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQs _ _ Z
  have := tensorProductAlgebra_finite (Q := QL) Λ (θ + β) hR
  obtain ⟨τ, hτ⟩ := redFirstIdem_pairing_nondegenerate hR hQs Λ (θ + β)
  obtain ⟨d, ι, hι⟩ := exists_injective_pi_lIdeal_of_isCornerFaithfulModule (τ := τ) hτ
    (finrank_leftCorner_redFirstIdem Λ (θ + β))
    (isIdempotentElem_redFirstIdem QL Λ (θ + β)).eq h
  exact IsCornerFaithfulModule.ind (appendBlackHom QL Λ j θ β)
    (eq_zero_of_forall_redFirstIdem_mul_mul hR hQs Λ _) ι
    (appendBlack_ind_map_injective C hR hι)

end Induction

section Base

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)

/-- In a red-ordered loading of a single black strand that is not red-first, the last red
strand is the rightmost strand. -/
theorem lt_val_of_not_isRedFirst (s : Seq (stendhalWeight (ℓ + 1) (0 + ((Si i) + 0))))
    (hs : IsRedOrdered s) (hrf : ¬ IsRedFirst s)
    (q : Fin (Multiset.card (stendhalWeight (ℓ + 1) (0 + ((Si i) + 0)))))
    (hq : s.lbl q = .inr (Fin.last ℓ)) : ℓ < q.val := by
  have hcard : Multiset.card (stendhalWeight (ℓ + 1) (0 + ((Si i) + 0))) = ℓ + 2 := by
    simp [stendhalWeight]
  have hblack : ∀ a, (s.lbl a).isLeft → s.lbl a = .inl i := by
    intro a ha
    cases h : s.lbl a with
    | inl j =>
      have := mem_of_lbl_eq_inl s a h
      simp only [zero_add, add_zero, Multiset.mem_singleton] at this
      rw [this]
    | inr r => rw [h] at ha; simp at ha
  have hafter : ∀ b, q < b → s.lbl b = .inl i := by
    intro b hb
    apply hblack
    cases h : s.lbl b with
    | inl j => rfl
    | inr r => exact absurd (hs q b _ _ hb hq h) (not_lt.2 (Fin.le_last r))
  simp only [IsRedFirst, not_forall] at hrf
  obtain ⟨a, b, ha, hb, hab⟩ := hrf
  have hbq : b ≤ q := by
    by_contra h
    rw [hafter b (lt_of_not_ge h)] at hb
    simp at hb
  have hab' : a < b := by
    rcases lt_or_eq_of_le (not_lt.1 hab) with h | h
    · exact h
    · subst h
      cases h : s.lbl a <;> simp_all
  by_contra hle
  rw [not_lt] at hle
  let p : Fin (Multiset.card (stendhalWeight (ℓ + 1) (0 + ((Si i) + 0)))) := ⟨ℓ + 1, by omega⟩
  have hqp : q < p := Fin.lt_def.2 (by change q.val < ℓ + 1; omega)
  have hap : a ≠ p := Fin.ne_of_lt ((hab'.trans_le hbq).trans hqp)
  have hsub : ({a, p} : Finset _) ⊆
      Finset.univ.filter (fun x => (Sum.inl i : I ⊕ Fin (ℓ + 1)) = s.1 x) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with hx | hx <;> rw [hx]
    · exact (hblack a ha).symm
    · exact (hafter p hqp).symm
  have h2 : 2 ≤ Multiset.count (Sum.inl i : I ⊕ Fin (ℓ + 1)) (Finset.univ.val.map s.1) := by
    rw [Multiset.count_map]
    calc 2 = ({a, p} : Finset _).card := (Finset.card_pair hap).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ = _ := rfl
  rw [s.2] at h2
  simp [stendhalWeight] at h2

variable (hQ : KLRSymm Q) (N : Type) [AddCommGroup N] [Module (parabolicFactorAlgebra Q Λ 0 0) N]

/-- With no black strand in the first block, `e⁰` acts as the identity on `S(₂Fᵢ N)`: every
red-ordered loading other than the red-first one has the black strand left of the last red
strand, so its idempotent kills `S(₂Fᵢ N)`. -/
theorem redFirstIdem_smul_lastIndBase
    (m : ParabolicStandardT Q Λ 0 ((Si i) + 0) (LastIndRight Q Λ i 0 0 N) hQ) :
    redFirstIdem Q Λ (0 + ((Si i) + 0)) • m = m := by
  have hP := TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem (k := k) Q Λ
    (0 + ((Si i) + 0))
  have hcard : Multiset.card (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ (0 : Multiset I))) =
      ℓ := by
    simp [stendhalWeight]
  have hkill : ∀ s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ + 1) (0 + ((Si i) + 0)),
      ¬ IsRedFirst s.1 → ∀ x : ParabolicStandardT Q Λ 0 ((Si i) + 0) (LastIndRight Q Λ i 0 0 N) hQ,
        TensorProductAlgebra.boundaryIdem Q Λ (0 + ((Si i) + 0)) s • x = 0 := by
    intro s hs x
    obtain ⟨q, hq⟩ := exists_lbl_eq_inr s.1 (Fin.last ℓ)
    rw [TensorProductAlgebra.boundaryIdem, ← affineTensorProjection_e_of_ordered Q Λ _ s.1 s.2]
    exact affineTensorProjection_e_smul_standard Q Λ 0 ((Si i) + 0) (LastIndRight Q Λ i 0 0 N) hQ
      s.1 q hq (by rw [hcard]; exact lt_val_of_not_isRedFirst i s.1 s.2 hs q hq) x
  have key : ∀ s, TensorProductAlgebra.boundaryIdem Q Λ (0 + ((Si i) + 0)) s • m =
      TensorProductAlgebra.boundaryIdem Q Λ (0 + ((Si i) + 0)) s •
        (redFirstIdem Q Λ (0 + ((Si i) + 0)) • m) := by
    intro s
    by_cases hs : IsRedFirst s.1
    · rw [smul_smul]
      exact congrArg (· • m) (redLoadingIdem_mul_redFirstIdem Q Λ _ s.1 s.2 hs).symm
    · rw [hkill s hs, hkill s hs]
  symm
  calc m = (1 : TensorProductAlgebra k Q Λ (0 + ((Si i) + 0))) • m := (one_smul _ _).symm
    _ = ∑ s, TensorProductAlgebra.boundaryIdem Q Λ (0 + ((Si i) + 0)) s • m := by
      rw [← hP.complete, Finset.sum_smul]
    _ = ∑ s, TensorProductAlgebra.boundaryIdem Q Λ (0 + ((Si i) + 0)) s •
        (redFirstIdem Q Λ (0 + ((Si i) + 0)) • m) := Finset.sum_congr rfl fun s _ => key s
    _ = _ := by rw [← Finset.sum_smul, hP.complete, one_smul]

/-- **The base case**: with no black strand in the first block, `S(₂Fᵢ N)` has no nonzero
submodule killed by `e⁰`. -/
theorem isCornerFaithfulModule_lastIndBase :
    IsCornerFaithfulModule (redFirstIdem Q Λ (0 + ((Si i) + 0)))
      (ParabolicStandardT Q Λ 0 ((Si i) + 0) (LastIndRight Q Λ i 0 0 N) hQ) := fun m hm => by
  rw [← redFirstIdem_smul_lastIndBase Q Λ i hQ N m]
  simpa using hm 1

end Base

end Categorification.Stendhal
