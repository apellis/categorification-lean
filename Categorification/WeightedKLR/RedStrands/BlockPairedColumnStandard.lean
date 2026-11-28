/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockPairedColumnInjection
import Categorification.WeightedKLR.RedStrands.BlockLoadingPlacement
import Categorification.WeightedKLR.RedStrands.BlockColumnSupport
import Categorification.WeightedKLR.RedStrands.TwoRedCrossingInjectivity

/-!
# Right crossing on the source column at standard parameters

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8, (6.21).
For Rouquier parameters, the ordered two-red right crossing
supplies the internal support test for the adjacent source-order column.
-/

namespace Categorification.Stendhal.RedBlock

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra QuantumGroup KL3.Diagram

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
    (C : CartanDatum I) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}

variable {Q : I → I → MvPolynomial (Fin 2) k}
local notation "row" => adjacentRow L M f β
local notation "μ" => stendhalWeight ℓ ν
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

/-- The supported black–second-red crossing detects zero on the source-order
column at standard parameters over a field. -/
theorem blockColumn_eq_zero_of_standard_paired_crossing
    (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)
    (h : weightSum row = μ) (t s : Seq μ) (j : ℕ) (hj : j+1 < (weightSum row).card) (i : I)
    (ht : redWord t = κ) :
    let s₀ := sadj (Multiset.card μ) j • s
    let source := Seq.cast h.symm s₀
    redWord s₀ = κ → source.lbl ⟨j,by omega⟩ = .inl i → source.lbl ⟨j+1,hj⟩ = .inr (f 1) →
    ∀ x : blockColumn Q Λ L M f β h,
      π (e t) * x.1 = x.1 → x.1 * π (e s₀) = x.1 → x.1 * π (ψ j * e s) = 0 → x = 0 := by
  apply blockColumn_eq_zero_of_ordered_paired_crossing Q Λ hQ L M f β h t s j hj i _ ht
  intro r a ha hord hblack hred
  exact (IsSecondRedCrossing.eq_zero_of_mul hR hQ (Λ ∘ f)
    (isSecondRedCrossing_of_labels r hord i ha hblack hred)).2.2

/-- The zero-kernel test for the supported source column gives cancellation
modulo the higher ideal indexed by an arbitrary upper loading. -/
theorem mem_blockUpperIdeal_of_standard_paired_crossing
    (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)
    (Lr Mr : List (Fin ℓ)) (t s : Seq μ) (j : ℕ) (hj : j + 1 < (Multiset.card μ)) (i : I)
    (ht : redWord t = Lr ++ f 0 :: f 1 :: Mr) :
    let s₀ := sadj (Multiset.card μ) j • s
    let p := (violMk k Q Λ ν).comp (ofKLR k Q Λ ν)
    let Jt := blockUpperIdeal k Q Λ ν (f 0) (f 1) (adjacentBlockRoot (f 0) (f 1) t) (redWord t)
    redWord s₀ = redWord t → s₀.lbl ⟨j, by omega⟩ = .inl i → s₀.lbl ⟨j+1,hj⟩ = .inr (f 1) →
    ∀ x : ViolQuotient k Q Λ ν, p (e t) * x * p (e s₀) = x →
      x * p (ψ j * e s) ∈ Jt → x ∈ Jt := by
  intro s₀ p Jt hord hblack hred x hleft hmul
  by_cases htbad : IsViolated t
  · have hp : p (e t) = 0 := violMk_e htbad
    rw [hp, zero_mul, zero_mul] at hleft
    rw [← hleft]
    exact Jt.zero_mem
  obtain ⟨L', M', β', h, v, hL, hM, hplace, hv⟩ :=
    exists_place_adjacent t htbad Lr Mr f ht
  let ρ := adjacentRow L' M' f β'
  have align : redWord t = L'.map Prod.fst ++ f 0 :: f 1 :: M'.map Prod.fst := by
    rw [hL,hM,ht]
  have hvord : UncrossedLoading ρ v := (uncrossedLoading_iff L' M' f β' h v).2
    (hplace.symm ▸ align)
  have hcut := blockUpperIdeal_placed Q Λ L' M' f β' h v hvord hv
  rw [hplace] at hcut
  have hr : j + 1 < (weightSum ρ).card := by rwa [h]
  have hcast {δ δ' : Multiset (I ⊕ Fin ℓ)} (g : δ = δ') (u : Seq δ)
      (n : ℕ) (hn : n < δ.card) (hn' : n < δ'.card) :
      (Seq.cast g u).lbl ⟨n,hn'⟩ = u.lbl ⟨n,hn⟩ := by subst δ'; rfl
  have hbc : (Seq.cast h.symm s₀).lbl ⟨j, Nat.lt_trans (Nat.lt_succ_self _) hr⟩ = .inl i :=
    (hcast h.symm s₀ j (Nat.lt_trans (Nat.lt_succ_self _) hj)
      (Nat.lt_trans (Nat.lt_succ_self _) hr)).trans hblack
  have hrc : (Seq.cast h.symm s₀).lbl ⟨j+1, hr⟩ = .inr (f 1) :=
    (hcast h.symm s₀ _ hj hr).trans hred
  have hK := blockColumn_eq_zero_of_standard_paired_crossing C Λ L' M' f β' hR hQ h t s j hr i
    align (hord.trans align) hbc hrc
  have hnew := mem_blockUpperIdeal_of_blockColumn_right_kernel Q Λ L' M' f β' h v hvord
    s₀ (hord.trans align) (ψ j * e s)
  rw [hplace] at hnew
  change x ∈ blockUpperIdeal k Q Λ ν (f 0) (f 1) (adjacentBlockRoot (f 0) (f 1) t) (redWord t)
  rw [hcut]
  apply hnew hK x hleft
  simpa only [← hcut] using hmul

end Categorification.Stendhal.RedBlock
