/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiLastLayer
import Categorification.WeightedKLR.RedStrands.EiRightTerm
import Categorification.WeightedKLR.RedStrands.EiInitLayer
import Categorification.WeightedKLR.RedStrands.EiFiltrationStatement
import Categorification.Algebra.ModuleFiltrationMap

/-!
# The induction step of the `Eᵢ` filtration when both pieces contain `i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For blocks `b` of `ℓ + 1` red strands such that `i` occurs both in
the first `ℓ + 1` blocks and in the last block, the filtration of `Eᵢ(M ⊗_B S^L_α)` is obtained
from the last-strand sequence `0 → S(₂Eᵢ X_M) → Eᵢ S(X_M) → S(₁Eᵢ X_M) → 0`: its left term is
the layer of the last red strand (`lastLayerEquiv`), and its right term is the standardization
of the module of the induction hypothesis (`rightTermEquiv`), whose layers standardize to the
layers of the other red strands (`initLayerStandardEquiv`). The result is
`eiFiltration_step_both`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong ModuleFiltration
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I)

omit [DecidableEq I] in
/-- Without red strands before the last one, the first blocks carry no black strands. -/
theorem initWeight_eq_zero_of_zero {b : Fin (0 + 2) → Multiset I} (h00 : leftBlock b = 0) :
    initWeight b = 0 := by
  change blockPrefix (initBlocks b) (0 + 1) = 0
  rw [blockPrefix_succ _ (Nat.zero_lt_succ 0), blockPrefix_zero, zero_add]
  exact h00

/-- **Induction step of Webster's Proposition 5.5, `E`-part, when `i` occurs in both pieces.** -/
theorem eiFiltration_step_both (hQ : KLRSymm Q) {ℓ : ℕ} (IH : EiFiltration (k := k) Q i ℓ)
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I) (ν₀ : Multiset I)
    (h00 : leftBlock b = 0) (hb : blockPrefix b (ℓ + 2) = ({i} : Multiset I) + ν₀)
    (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b))
    (b' : {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ} → Fin (ℓ + 2) → Multiset I)
    (h0 : ∀ κ, leftBlock (b' κ) = leftBlock b)
    (hr : ∀ κ r, r ≠ κ.1 → rightBlock (b' κ) r = rightBlock b r)
    (hκ : ∀ κ, {i} + rightBlock (b' κ) κ.1 = rightBlock b κ.1)
    (hb' : ∀ κ, blockPrefix (b' κ) (ℓ + 2) = ν₀)
    (hα' : ∀ κ, RootNonViolated (ν := ν₀) (blockRoot (b' κ)))
    (C : Type) [Ring C] [Algebra k C]
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (hiθ : i ∈ initWeight b) (hiβ : i ∈ lastBlock b) :
    ∃ m : List {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ}, m.Nodup ∧ (∀ κ, κ ∈ m) ∧
      HasFiltration (fun κ => eiLayer Q i Λ ν₀ κ.1 (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ)
        m (eiTop Q i Λ b ν₀ hb hα C M ρ) := by
  have hℓ : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h
      rw [initWeight_eq_zero_of_zero h00] at hiθ
      exact absurd hiθ (Multiset.notMem_zero i)
    · exact h
  obtain ⟨θ₀, hθ⟩ : ∃ θ₀, initWeight b = ({i} : Multiset I) + θ₀ :=
    ⟨(initWeight b).erase i, ((Multiset.singleton_add _ _).trans (Multiset.cons_erase hiθ)).symm⟩
  let last : {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ} := ⟨Fin.last ℓ, hiβ⟩
  obtain ⟨β₀, hβc⟩ : ∃ β₀, lastBlock (b' last) = β₀ := ⟨_, rfl⟩
  have hβ : lastBlock b = ({i} : Multiset I) + β₀ := by
    rw [← hβc]
    exact (hκ last).symm
  have hν : ν₀ = θ₀ + (({i} : Multiset I) + β₀) := by
    have h1 := hb
    rw [blockPrefix_last, hθ, hβ, add_assoc] at h1
    exact (add_left_cancel h1).symm
  subst hν
  -- the root hypotheses of the two-piece standardizations
  have hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) :=
    rootNonViolated_blockRoot hℓ h00
  have hα₁' : RootNonViolated (ν := ({i} : Multiset I) + θ₀) (blockRoot (initBlocks b)) :=
    hθ ▸ hα₁
  have hαl : RootNonViolated (ν := initWeight (b' last)) (blockRoot (initBlocks (b' last))) :=
    rootNonViolated_blockRoot hℓ ((h0 last).trans h00)
  have hθl : initWeight (b' last) = ({i} : Multiset I) + θ₀ :=
    (initWeight_eq_of_last (h0 last) (hr last)).trans hθ
  -- the labels of the first `ℓ` red strands
  let f : {κ : Fin ℓ // i ∈ rightBlock (initBlocks b) κ} →
      {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ} :=
    fun κ => ⟨κ.1.castSucc, κ.2⟩
  have hβf : ∀ κ, lastBlock (b' (f κ)) = ({i} : Multiset I) + β₀ := fun κ =>
    (hr (f κ) (Fin.last ℓ) (Fin.castSucc_lt_last κ.1).ne').trans hβ
  have hθf : ∀ κ, initWeight (b' (f κ)) = θ₀ := fun κ => by
    have h1 := hb' (f κ)
    rw [blockPrefix_last, hβf κ] at h1
    exact add_right_cancel h1
  have hα₁f : ∀ κ, RootNonViolated (ν := initWeight (b' (f κ)))
      (blockRoot (initBlocks (b' (f κ)))) := fun κ =>
    rootNonViolated_blockRoot hℓ ((h0 (f κ)).trans h00)
  have hα'f : ∀ κ, RootNonViolated (ν := θ₀) (blockRoot (initBlocks (b' (f κ)))) := fun κ =>
    hθf κ ▸ hα₁f κ
  -- the induction hypothesis
  obtain ⟨m, hnd, hall, hY⟩ := IH (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ h00 hθ hα₁'
    (fun κ => initBlocks (b' (f κ))) (fun κ => h0 (f κ))
    (fun κ => initBlocks_rightBlock_of_ne κ.1 (hr (f κ))) (fun κ => hκ (f κ)) hθf hα'f
    ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
      (({i} : Multiset I) + β₀)) ⊗[k] C) (InitRestrict Q Λ b M)
    (inductionAction Q Λ b M hβ C ρ)
  -- the right term
  have hZ2 := (hasFiltration_splitStandard Q Λ hQ hY).mono
    (L' := fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) (f κ).1 (h0 (f κ)) (hr (f κ))
      (hκ (f κ)) (hb' (f κ)) (hα' (f κ)) C M ρ)
    (fun κ => ⟨initLayerStandardEquiv Q Λ hQ i κ.1 (h0 (f κ)) (hr (f κ)) (hκ (f κ)) M C ρ hβ
      (hβf κ) (hθf κ) (hα₁f κ) (hθf κ) (hα'f κ) (hb' (f κ)) (hα' (f κ))⟩)
  have hZ3 : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f)
      (splitStandard Q Λ hQ θ₀ (({i} : Multiset I) + β₀) C (eiTop Q i (Λ ∘ Fin.castSucc)
        (initBlocks b) θ₀ hθ hα₁' ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^
          Λ (Fin.last ℓ) i) (({i} : Multiset I) + β₀)) ⊗[k] C) (InitRestrict Q Λ b M)
          (inductionAction Q Λ b M hβ C ρ))) := by
    apply HasFiltration.relabel
    exact hZ2
  have eZ := (rightTermEquiv Q Λ hQ i b M hθ hβ hα₁ hα₁' C ρ).symm
  have hZ : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f)
      (ModuleCat.of _ (BothRight Q Λ hQ i θ₀ β₀ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))) := by
    apply HasFiltration.of_equiv hZ3
    exact eZ
  -- the left term
  have eX := (lastLayerEquiv Q Λ i (h0 last) (hr last) (hκ last) M hα₁ hαl hQ θ₀ β₀ hθ hθl hβ hβc
      (hb' last) (hα' last) C ρ).symm
  have hX : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) [last]
      (ModuleCat.of _ (BothLeft Q Λ hQ i θ₀ β₀ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))) := by
    apply HasFiltration.single
    exact eX
  -- the middle term
  have hmid : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f ++ [last])
      (ModuleCat.of _ (BothMid Q Λ hQ i θ₀ β₀ C (twoPieceCastAction Q Λ b M hθ hβ hα₁ C ρ))) :=
    hZ.extension (bothSeqTwo Q Λ hQ i θ₀ β₀ C _) (bothSeqOne Q Λ hQ i θ₀ β₀ C _)
      (bothSeqTwo_injective Q Λ hQ i θ₀ β₀ C _) (bothSeq_exact Q Λ hQ i θ₀ β₀ C _)
      (bothSeqOne_surjective Q Λ hQ i θ₀ β₀ C _) hX
  have eT := (eiTopEquiv Q Λ hQ i b M hθ hβ hα₁ (Eq.symm (lastBlack_weight i θ₀ β₀)) hb hα C
    ρ).symm
  have htop : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + (({i} : Multiset I) + β₀)) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f ++ [last])
      (eiTop Q i Λ b (θ₀ + (({i} : Multiset I) + β₀)) hb hα C M ρ) := by
    apply HasFiltration.of_equiv hmid
    exact eT
  refine ⟨m.map f ++ [last], ?_, ?_, htop⟩
  · refine List.nodup_append.2 ⟨hnd.map (fun κ κ' h => Subtype.ext (Fin.castSucc_injective _
      (congrArg Subtype.val h))), List.nodup_singleton _, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hx
    subst hy
    exact fun h => (Fin.castSucc_lt_last κ.1).ne (congrArg Subtype.val h)
  · intro κ
    rcases Fin.eq_castSucc_or_eq_last κ.1 with ⟨j, hj⟩ | hj
    · refine List.mem_append_left _ (List.mem_map.2 ⟨⟨j, ?_⟩, hall _, Subtype.ext hj.symm⟩)
      have h2 := κ.2
      rw [hj] at h2
      exact h2
    · exact List.mem_append_right _ (List.mem_singleton.2 (Subtype.ext hj))

end StendhalAlgebra

end Categorification.Stendhal
