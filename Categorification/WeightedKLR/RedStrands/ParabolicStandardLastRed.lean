/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent

/-!
# Idempotents with the last red strand at the parabolic cut

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. On the standardization `S N` of a module `N` of the parabolic factor algebra,
an idempotent `e_s` whose last red strand lies at or after the cut `|α|` maps into the identity
copy of `N`: every supported shuffle of such an `s` is the identity, so `e_s` either is a
concatenation idempotent or acts by zero.

## Main results

* `parabolicShuffle_e_smul_mem_unit`: the statement on the shuffle module.
* `parabolicStandardAction_e_mem_range`: the statement on the standardization.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "νall" => (θ + β)
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
local notation "N₀" => ParabolicInput Q Λ θ β N
local notation "M" => ParabolicShuffle Q Λ θ β N
local notation "unitI" => indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀
local notation "ρ" => parabolicShuffleAction Q Λ θ β N
local notation "F" => parabolicOrderedLoadings (ℓ := ℓ) θ β
local notation "π" => Submodule.mkQ (excludedSpace ρ F)

omit [DecidableEq I] in
private theorem lastBlock_positive : 0 < (δ).card := by simp [stendhalWeight]

omit [DecidableEq I] in
private theorem lastBlock_first (b : Seq δ) (hb : ¬ IsViolated b) :
    b.lbl ⟨0, lastBlock_positive (ℓ := ℓ) β⟩ = .inr (Fin.last ℓ) := by
  let z : Fin (δ).card := ⟨0, lastBlock_positive (ℓ := ℓ) β⟩
  change b.lbl z = _
  cases hx : b.lbl z with
  | inr r => exact congrArg Sum.inr (parabolicLast_red_eq_last β b z hx)
  | inl i => exact (hb ⟨_, by change (b.lbl z).isLeft = true; simp [hx]⟩).elim

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- If the last red strand of `s` lies at or after the cut, the only supported shuffle of `s`
is the identity, and `s` is a concatenation. -/
theorem parabolicShuffle_supported_of_lastRed (s : Seq (α+δ))
    (hle : ∀ p : Fin (α+δ).card, s.lbl p = .inr (Fin.last ℓ) → (α).card ≤ p.val)
    (u : Shuffle (Seq.card_add' α δ))
    (hne : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) :
    u = shufOne ∧ s ∈ concatSet α δ := by
  obtain ⟨a,b,he,_,_,_,hb⟩ := parabolicShuffle_supported_input Q Λ θ β N s u hne
  let z : Fin (δ).card := ⟨0, lastBlock_positive (ℓ := ℓ) β⟩
  let p := u.1.symm (Seq.posR α z)
  have hp : s.lbl p = .inr (Fin.last ℓ) := by
    change (u.1 • s).1 (Seq.posR α z) = _
    rw [he, Seq.append_posR]
    exact lastBlock_first β b hb
  have hu : u = shufOne := by
    apply Subtype.ext
    exact lastRedShuffle_eq_one (Seq.card_add' α δ) u (lastBlock_positive (ℓ := ℓ) β) (hle p hp)
  refine ⟨hu, mem_concatSet.mpr ⟨a, b, ?_⟩⟩
  subst hu
  simpa [shufOne] using he.symm

/-- On the shuffle module, an idempotent whose last red strand lies at or after the cut maps
into the identity copy of the input. -/
theorem parabolicShuffle_e_smul_mem_unit (hQ : KLRSymm Q) (s : Seq (α+δ))
    (hle : ∀ p : Fin (α+δ).card, s.lbl p = .inr (Fin.last ℓ) → (α).card ≤ p.val) (m : M) :
    ∃ n : N₀, ρ (e s) m = unitI n := by
  classical
  have h := indShuffle_eSum_mem_unit (stendhalQ_swap_symm Q Λ hQ) N₀ {s} (fun s' hs' u hu => by
    rw [Finset.mem_singleton] at hs'
    subst hs'
    by_contra hn
    exact hu (parabolicShuffle_supported_of_lastRed Q Λ θ β N s' hle u hn).1) m
  simpa [eSum] using h

/-- On the standardization, an idempotent whose last red strand lies at or after the cut maps
into the identity copy of the input module. -/
theorem parabolicStandardAction_e_mem_range (hQ : KLRSymm Q) (s : Seq (α+δ))
    (hle : ∀ p : Fin (α+δ).card, s.lbl p = .inr (Fin.last ℓ) → (α).card ≤ p.val)
    (z : ParabolicStandard Q Λ θ β N) :
    parabolicStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) (e s))))) z ∈
      LinearMap.range (parabolicStandardUnit Q Λ θ β N) := by
  obtain ⟨m,rfl⟩ := (excludedSpace ρ F).mkQ_surjective z
  rw [parabolicStandardAction_affine]
  change π (ρ (e s) m) ∈ _
  obtain ⟨n,hn⟩ := parabolicShuffle_e_smul_mem_unit Q Λ θ β N hQ s hle m
  exact ⟨n, by rw [hn]; rfl⟩

end Categorification.Stendhal
