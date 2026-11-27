/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiStepBoth
import Categorification.WeightedKLR.RedStrands.EiTopOneBlock

/-!
# The induction step of the `Eᵢ` filtration when one piece contains `i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For blocks `b` of `ℓ + 1` red strands:

* if `i` occurs in the first `ℓ + 1` blocks but not in the last one, then
  `Eᵢ(M ⊗_B S^L_α) ≅ S(₁Eᵢ X_M)` is the standardization of the module of the induction
  hypothesis, whose filtration standardizes to the required one (`eiFiltration_step_left`);
* if `i` occurs in the last block only, then `Eᵢ(M ⊗_B S^L_α) ≅ S(₂Eᵢ X_M)` is the layer of the
  last red strand (`eiFiltration_step_right`).
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

/-- The first blocks of blocks with `b_0 = 0` carry no violated sequence. -/
theorem rootNonViolated_initBlocks {ℓ : ℕ} {b : Fin (ℓ + 2) → Multiset I}
    (h00 : leftBlock b = 0) : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h
    rw [initWeight_eq_zero_of_zero h00]
    rintro s - ⟨hc, -⟩
    simp [stendhalWeight] at hc
  · exact rootNonViolated_blockRoot h h00

/-- A block of the first red strands lies in the weight of the first blocks. -/
theorem rightBlock_castSucc_le_initWeight {ℓ : ℕ} (b : Fin (ℓ + 2) → Multiset I) (j : Fin ℓ) :
    rightBlock b j.castSucc ≤ initWeight b := by
  have hmem : (j.succ : Fin (ℓ + 1)) ∈
      Finset.univ.filter (fun r : Fin (ℓ + 1) => r.val < ℓ + 1) := by simp
  exact Finset.single_le_sum (f := initBlocks b) (fun _ _ => Multiset.zero_le _) hmem

/-- **Induction step of Webster's Proposition 5.5, `E`-part, when `i` occurs in the first blocks
but not in the last one.** -/
theorem eiFiltration_step_left (hQ : KLRSymm Q) {ℓ : ℕ} (IH : EiFiltration (k := k) Q i ℓ)
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
    (hiθ : i ∈ initWeight b) (hiβ : i ∉ lastBlock b) :
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
  have hν : ν₀ = θ₀ + lastBlock b := by
    have h1 := hb
    rw [blockPrefix_last, hθ, add_assoc] at h1
    exact (add_left_cancel h1).symm
  subst hν
  have hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) :=
    rootNonViolated_blockRoot hℓ h00
  have hα₁' : RootNonViolated (ν := ({i} : Multiset I) + θ₀) (blockRoot (initBlocks b)) :=
    hθ ▸ hα₁
  let f : {κ : Fin ℓ // i ∈ rightBlock (initBlocks b) κ} →
      {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ} :=
    fun κ => ⟨κ.1.castSucc, κ.2⟩
  have hβf : ∀ κ, lastBlock (b' (f κ)) = lastBlock b := fun κ =>
    hr (f κ) (Fin.last ℓ) (Fin.castSucc_lt_last κ.1).ne'
  have hθf : ∀ κ, initWeight (b' (f κ)) = θ₀ := fun κ => by
    have h1 := hb' (f κ)
    rw [blockPrefix_last, hβf κ] at h1
    exact add_right_cancel h1
  have hα₁f : ∀ κ, RootNonViolated (ν := initWeight (b' (f κ)))
      (blockRoot (initBlocks (b' (f κ)))) := fun κ =>
    rootNonViolated_blockRoot hℓ ((h0 (f κ)).trans h00)
  have hα'f : ∀ κ, RootNonViolated (ν := θ₀) (blockRoot (initBlocks (b' (f κ)))) := fun κ =>
    hθf κ ▸ hα₁f κ
  obtain ⟨m, hnd, hall, hY⟩ := IH (Λ ∘ Fin.castSucc) (initBlocks b) θ₀ h00 hθ hα₁'
    (fun κ => initBlocks (b' (f κ))) (fun κ => h0 (f κ))
    (fun κ => initBlocks_rightBlock_of_ne κ.1 (hr (f κ))) (fun κ => hκ (f κ)) hθf hα'f
    ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
      (lastBlock b)) ⊗[k] C) (InitRestrict Q Λ b M)
    (inductionAction Q Λ b M rfl C ρ)
  have hZ2 := (hasFiltration_splitStandard Q Λ hQ hY).mono
    (L' := fun κ => eiLayer Q i Λ (θ₀ + lastBlock b) (f κ).1 (h0 (f κ)) (hr (f κ))
      (hκ (f κ)) (hb' (f κ)) (hα' (f κ)) C M ρ)
    (fun κ => ⟨initLayerStandardEquiv Q Λ hQ i κ.1 (h0 (f κ)) (hr (f κ)) (hκ (f κ)) M C ρ rfl
      (hβf κ) (hθf κ) (hα₁f κ) (hθf κ) (hα'f κ) (hb' (f κ)) (hα' (f κ))⟩)
  have hZ3 : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + lastBlock b) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f)
      (splitStandard Q Λ hQ θ₀ (lastBlock b) C (eiTop Q i (Λ ∘ Fin.castSucc)
        (initBlocks b) θ₀ hθ hα₁' ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^
          Λ (Fin.last ℓ) i) (lastBlock b)) ⊗[k] C) (InitRestrict Q Λ b M)
          (inductionAction Q Λ b M rfl C ρ))) := by
    apply HasFiltration.relabel
    exact hZ2
  have eT := eiTopEquiv Q Λ hQ i b M hθ rfl hα₁ (leftBlack_weight i θ₀ (lastBlock b)).symm hb hα
    C ρ
  have eL := eiLeftOnlyEquiv Q Λ hQ i C θ₀ (lastBlock b)
    (twoPieceCastAction Q Λ b M hθ rfl hα₁ C ρ) hiβ
  have eR := leftTermEquiv Q Λ hQ i b M hθ rfl hα₁ hα₁' ρ
  have htop : HasFiltration (fun κ => eiLayer Q i Λ (θ₀ + lastBlock b) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (m.map f)
      (eiTop Q i Λ b (θ₀ + lastBlock b) hb hα C M ρ) := by
    apply HasFiltration.of_equiv hZ3
    exact (eT.trans (eL.trans eR)).symm
  refine ⟨m.map f, hnd.map (fun κ κ' h => Subtype.ext (Fin.castSucc_injective _
    (congrArg Subtype.val h))), ?_, htop⟩
  intro κ
  rcases Fin.eq_castSucc_or_eq_last κ.1 with ⟨j, hj⟩ | hj
  · refine List.mem_map.2 ⟨⟨j, ?_⟩, hall _, Subtype.ext hj.symm⟩
    have h2 := κ.2
    rw [hj] at h2
    exact h2
  · have h2 := κ.2
    rw [hj] at h2
    exact absurd h2 hiβ

/-- **Induction step of Webster's Proposition 5.5, `E`-part, when `i` occurs in the last block
only.** -/
theorem eiFiltration_step_right (hQ : KLRSymm Q) {ℓ : ℕ}
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
    (hiθ : i ∉ initWeight b) (hiβ : i ∈ lastBlock b) :
    ∃ m : List {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ}, m.Nodup ∧ (∀ κ, κ ∈ m) ∧
      HasFiltration (fun κ => eiLayer Q i Λ ν₀ κ.1 (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ)
        m (eiTop Q i Λ b ν₀ hb hα C M ρ) := by
  let last : {κ : Fin (ℓ + 1) // i ∈ rightBlock b κ} := ⟨Fin.last ℓ, hiβ⟩
  obtain ⟨β₀, hβc⟩ : ∃ β₀, lastBlock (b' last) = β₀ := ⟨_, rfl⟩
  have hβ : lastBlock b = ({i} : Multiset I) + β₀ := by
    rw [← hβc]
    exact (hκ last).symm
  have hν : ν₀ = initWeight b + β₀ := by
    have h1 := hb
    rw [blockPrefix_last, hβ, add_left_comm] at h1
    exact (add_left_cancel h1).symm
  subst hν
  have hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) :=
    rootNonViolated_initBlocks h00
  have hαl : RootNonViolated (ν := initWeight (b' last)) (blockRoot (initBlocks (b' last))) :=
    rootNonViolated_initBlocks ((h0 last).trans h00)
  have hθl : initWeight (b' last) = initWeight b := initWeight_eq_of_last (h0 last) (hr last)
  have eT := eiTopEquiv Q Λ hQ i b M rfl hβ hα₁ (rightBlack_weight i (initWeight b) β₀).symm hb
    hα C ρ
  have eR := eiRightOnlyEquiv Q Λ hQ i C (initWeight b) β₀
    (twoPieceCastAction Q Λ b M rfl hβ hα₁ C ρ) hiθ
  have eL := lastLayerRightEquiv Q Λ i (h0 last) (hr last) (hκ last) M hα₁ hαl hQ rfl hθl hβ hβc
    (hb' last) (hα' last) C ρ
  have htop : HasFiltration (fun κ => eiLayer Q i Λ (initWeight b + β₀) κ.1 (h0 κ)
      (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) [last]
      (eiTop Q i Λ b (initWeight b + β₀) hb hα C M ρ) := by
    apply HasFiltration.single
    exact eT.trans (eR.trans eL.symm)
  refine ⟨[last], List.nodup_singleton _, ?_, htop⟩
  intro κ
  rcases Fin.eq_castSucc_or_eq_last κ.1 with ⟨j, hj⟩ | hj
  · have h2 := κ.2
    rw [hj] at h2
    exact absurd (Multiset.mem_of_le (rightBlock_castSucc_le_initWeight b j) h2) hiθ
  · exact List.mem_singleton.2 (Subtype.ext hj)

end StendhalAlgebra

end Categorification.Stendhal
