/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiQuotTerm
import Categorification.WeightedKLR.RedStrands.FiTopEquiv
import Categorification.WeightedKLR.RedStrands.EiStepOne
import Categorification.Algebra.ModuleFiltrationMap

/-!
# The `Fᵢ` filtration of standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `F`-part: for blocks `b` with `b_0 = 0` and total weight `ν`, and a right
module `M` over the block algebra `B`, `Fᵢ(M ⊗_B S^L_α)` has a filtration whose subquotients
are the `ₖFᵢ M ⊗_{B'} S^L_{α'}`, one for each red strand `k` (`fiFiltration`). It is stated over
`T(i + ν) ⊗ C` for an algebra `C` acting on `M` by `B`-linear maps; `C = k` is Webster's
statement.

The proof is by induction on the number of red strands. For `ℓ + 1` red strands,
`Fᵢ(M ⊗_B S^L_α) ≅ Fᵢ S(X_M)` (`fiTopEquiv`), and the last-strand sequence
`0 → S(₁Fᵢ X_M) → Fᵢ S(X_M) → S(₂Fᵢ X_M) → 0` has as quotient term the layer of the last red
strand (`fiQuotEquiv`) and as sub term the standardization of the module of the induction
hypothesis (`fiSubEquiv`), whose layers standardize to the layers of the other red strands
(`fiInitLayerStandardEquiv`).

Route hypothesis: the injectivity of the first map of the last-strand sequence,
`AllDeltaInjective` (Webster deduces it from the freeness of Theorem 4.31 over the parabolic
subalgebra). It is an explicit hypothesis of `fiFiltration`, tracked for removal in the roadmap.
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

/-- **`FiFiltration` for the modules satisfying `P`**: the statement of Webster's
Proposition 5.5, `F`-part, for `ℓ` red strands, for those `M` with `P M` (`P` true: every
module, as `FiFiltration`; `P` finite-dimensionality: Webster's category of finite-dimensional
modules). -/
def FiFiltrationFor (P : (M : Type) → [AddCommGroup M] → [Module k M] → Prop) (ℓ : ℕ) : Prop :=
  ∀ (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν : Multiset I), leftBlock b = 0 →
    ∀ (hb : blockPrefix b (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b))
      (b' : Fin ℓ → Fin (ℓ + 1) → Multiset I)
      (h0 : ∀ κ, leftBlock b = leftBlock (b' κ))
      (hr : ∀ κ r, r ≠ κ → rightBlock b r = rightBlock (b' κ) r)
      (hκ : ∀ κ, {i} + rightBlock b κ = rightBlock (b' κ) κ)
      (hb' : ∀ κ, blockPrefix (b' κ) (ℓ + 1) = ({i} : Multiset I) + ν)
      (hα' : ∀ κ, RootNonViolated (ν := ({i} : Multiset I) + ν) (blockRoot (b' κ)))
      (C : Type) [Ring C] [Algebra k C]
      (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M], P M →
      ∀ (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M),
      ∃ m : List (Fin ℓ), m.Nodup ∧ (∀ κ, κ ∈ m) ∧
        HasFiltration (fun κ => fiLayer Q i Λ ν κ (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ)
          m (fiTop Q i Λ b ν hb hα C M ρ)

theorem fiFiltrationFor_zero (P : (M : Type) → [AddCommGroup M] → [Module k M] → Prop) :
    FiFiltrationFor (k := k) Q i P 0 := by
  intro Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C _ _ M _ _ _ _ _ ρ
  exact fiFiltration_zero Q i Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C M ρ

/-- **Induction step of Webster's Proposition 5.5, `F`-part**, given the injectivity of the
first map of the last-strand sequence (`FirstIndDeltaInjective` for `X_M`, a route
hypothesis), for the modules satisfying `P`. -/
theorem fiFiltrationFor_step (hQ : KLRSymm Q)
    (P : (M : Type) → [AddCommGroup M] → [Module k M] → Prop) {ℓ : ℕ}
    (IH : FiFiltrationFor (k := k) Q i P ℓ)
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)
    (h00 : leftBlock b = 0) (hb : blockPrefix b (ℓ + 1 + 1) = initWeight b + lastBlock b)
    (hα : RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))
    (b' : Fin (ℓ + 1) → Fin (ℓ + 2) → Multiset I)
    (h0 : ∀ κ, leftBlock b = leftBlock (b' κ))
    (hr : ∀ κ r, r ≠ κ → rightBlock b r = rightBlock (b' κ) r)
    (hκ : ∀ κ, {i} + rightBlock b κ = rightBlock (b' κ) κ)
    (hb' : ∀ κ, blockPrefix (b' κ) (ℓ + 1 + 1) =
      ({i} : Multiset I) + (initWeight b + lastBlock b))
    (hα' : ∀ κ, RootNonViolated (ν := ({i} : Multiset I) + (initWeight b + lastBlock b))
      (blockRoot (b' κ)))
    (C : Type) [Ring C] [Algebra k C]
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (hPM : P (InitRestrict Q Λ b M))
    (hinj : FirstIndDeltaInjective Q Λ i (initWeight b) (lastBlock b)
      (TwoPieceInput Q Λ b M (rootNonViolated_initBlocks h00)) hQ)
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    ∃ m : List (Fin (ℓ + 1)), m.Nodup ∧ (∀ κ, κ ∈ m) ∧
      HasFiltration (fun κ => fiLayer Q i Λ (initWeight b + lastBlock b) κ (h0 κ) (hr κ) (hκ κ)
        (hb' κ) (hα' κ) C M ρ) m (fiTop Q i Λ b (initWeight b + lastBlock b) hb hα C M ρ) := by
  have hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)) :=
    rootNonViolated_initBlocks h00
  -- the data of the induction hypothesis
  have hlast : ∀ κ : Fin ℓ, lastBlock (b' κ.castSucc) = lastBlock b := fun κ =>
    (hr κ.castSucc (Fin.last ℓ) (Fin.castSucc_lt_last κ).ne').symm
  have hθκ : ∀ κ : Fin ℓ, initWeight (b' κ.castSucc) = ({i} : Multiset I) + initWeight b :=
    fun κ => by
      have h1 := (blockPrefix_last (b' κ.castSucc)).symm.trans (hb' κ.castSucc)
      rw [hlast κ, ← add_assoc] at h1
      exact add_right_cancel h1
  have hα₁κ : ∀ κ : Fin ℓ, RootNonViolated (ν := ({i} : Multiset I) + initWeight b)
      (blockRoot (initBlocks (b' κ.castSucc))) := fun κ =>
    hθκ κ ▸ rootNonViolated_initBlocks ((h0 κ.castSucc).symm.trans h00)
  obtain ⟨m, hnd, hall, hY⟩ := IH (Λ ∘ Fin.castSucc) (initBlocks b) (initWeight b) h00 rfl hα₁
    (fun κ => initBlocks (b' κ.castSucc)) (fun κ => h0 κ.castSucc)
    (fun κ => initBlocks_rightBlock_of_ne κ (hr κ.castSucc))
    (fun κ => hκ κ.castSucc) hθκ hα₁κ
    ((CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
      (lastBlock b)) ⊗[k] C) (InitRestrict Q Λ b M) hPM (inductionAction Q Λ b M rfl C ρ)
  -- the sub term
  have hX₁ := ((hasFiltration_splitStandard Q Λ hQ hY).restrictScalars
    (firstIndCastHom Q Λ i (initWeight b) (lastBlock b) C)).mono
    (L' := fun κ : Fin ℓ => fiLayer Q i Λ (initWeight b + lastBlock b) κ.castSucc
      (h0 κ.castSucc) (hr κ.castSucc) (hκ κ.castSucc) (hb' κ.castSucc) (hα' κ.castSucc) C M ρ)
    (fun κ => ⟨fiInitLayerStandardEquiv Q Λ hQ i κ (h0 κ.castSucc) (hr κ.castSucc)
      (hκ κ.castSucc) M C ρ (hθκ κ) (hlast κ) rfl (hθκ κ) (hα₁κ κ)
      (firstInd_blackWeight i (initWeight b) (lastBlock b)) (hb' κ.castSucc)
      (hα' κ.castSucc)⟩)
  have hX₂ := HasFiltration.relabel (L := fun κ => fiLayer Q i Λ (initWeight b + lastBlock b) κ
    (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) Fin.castSucc hX₁
  have hX := HasFiltration.of_equiv (Y' := ModuleCat.of _
    (FiSub Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ))) hX₂
    (fiSubEquiv Q Λ hQ i b M hα₁ C ρ).symm
  -- the quotient term
  have hαc : RootNonViolated (ν := initWeight (b' (Fin.last ℓ)))
      (blockRoot (initBlocks (b' (Fin.last ℓ)))) :=
    rootNonViolated_initBlocks ((h0 (Fin.last ℓ)).symm.trans h00)
  have hZ := HasFiltration.single (L := fun κ => fiLayer Q i Λ (initWeight b + lastBlock b) κ
    (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ) (Y := ModuleCat.of _
    (FiQuot Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ)))
    (fiQuotEquiv Q Λ hQ i (h0 (Fin.last ℓ)) (hr (Fin.last ℓ)) (hκ (Fin.last ℓ)) M hα₁ hαc C ρ
      (hb' (Fin.last ℓ)) (hα' (Fin.last ℓ)))
  -- the middle term
  have hmid := hZ.extension (X := ModuleCat.of _
    (FiSub Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ)))
    (Y := ModuleCat.of _
      (FiMid Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ)))
    (fiSeqOne Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ))
    (fiSeqTwo Q Λ hQ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ))
    (fiSeqOne_injective Q Λ hQ i (initWeight b) (lastBlock b) C _ hinj)
    (fiSeq_exact Q Λ hQ i (initWeight b) (lastBlock b) C _)
    (fiSeqTwo_surjective Q Λ hQ i (initWeight b) (lastBlock b) C _) hX
  have htop := HasFiltration.of_equiv (Y' := fiTop Q i Λ b (initWeight b + lastBlock b) hb hα C
    M ρ) hmid (fiTopEquiv Q Λ hQ i b M hα₁ hb hα C ρ).symm
  refine ⟨[Fin.last ℓ] ++ m.map Fin.castSucc, ?_, ?_, htop⟩
  · refine List.nodup_append.2 ⟨List.nodup_singleton _,
      hnd.map (Fin.castSucc_injective _), ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hx
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hy
    subst hx
    exact fun h => (Fin.castSucc_lt_last κ).ne h.symm
  · intro κ
    rcases Fin.eq_castSucc_or_eq_last κ with ⟨j, rfl⟩ | rfl
    · exact List.mem_append_right _ (List.mem_map.2 ⟨j, hall j, rfl⟩)
    · exact List.mem_append_left _ (List.mem_singleton.2 rfl)

/-- **Webster's Proposition 5.5, `F`-part** (arXiv:1309.3796v3), with a commuting action:
`Fᵢ` of a standardization is filtered by the standardizations of the inductions adding an
`i`-strand to one block, each red strand occurring exactly once. Route hypothesis:
`AllDeltaInjective` (injectivity of the first map of the last-strand sequence, which Webster
obtains from Theorem 4.31), tracked for removal in the roadmap. -/
theorem fiFiltration (hQ : KLRSymm Q)
    (hδ : ∀ (ℓ : ℕ) (Λ : Fin (ℓ + 1) → I →₀ ℕ), AllDeltaInjective Q Λ hQ) :
    ∀ ℓ, FiFiltration (k := k) Q i ℓ
  | 0 => fiFiltration_zero Q i
  | ℓ + 1 => by
    intro Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C _ _ M _ _ _ _ ρ
    obtain rfl : ν = initWeight b + lastBlock b := hb.symm.trans (blockPrefix_last b)
    have IH : FiFiltrationFor (k := k) Q i (fun _ _ _ => True) ℓ := by
      intro Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C _ _ M _ _ _ _ _ ρ
      exact fiFiltration hQ hδ ℓ Λ b ν h00 hb hα b' h0 hr hκ hb' hα' C M ρ
    exact fiFiltrationFor_step Q i hQ (fun _ _ _ => True) IH Λ b h00 hb hα b' h0 hr hκ
      hb' hα' C M trivial
      (hδ ℓ Λ i _ _ ⟨TwoPieceInput Q Λ b M (rootNonViolated_initBlocks h00)⟩) ρ

end StendhalAlgebra

end Categorification.Stendhal
