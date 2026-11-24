/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
import Categorification.WeightedKLR.RedStrands.OneBlackRetainedOrder

/-!
# Kernel equivalence across a chain of zero-weight spectators

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
Composing unit crossings along a finite spectator chain identifies the source
kernel with the final partial standard when its retained loading is strictly
higher and has no surviving strictly higher loading.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {i : I}
variable (Λ : Fin ℓ → I →₀ ℕ)
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ

/-- A finite sequence of swaps moving the black strand left over zero-weight reds. -/
inductive ZeroWeightSpectatorPath (s : Seq μ) : Seq μ → Prop
  | nil : ZeroWeightSpectatorPath s s
  | swap {t : Seq μ} (path : ZeroWeightSpectatorPath s t) (j : ℕ) (hj : j + 1 < n)
      (r : Fin ℓ) (hr : t.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
      (hb : t.lbl ⟨j + 1, hj⟩ = .inl i) (hz : Λ r i = 0) :
      ZeroWeightSpectatorPath s (TypeA.sadj n j • t)

omit [DecidableEq I] in
theorem ZeroWeightSpectatorPath.redWord_eq {s t : Seq μ}
    (path : ZeroWeightSpectatorPath Λ s t) : redWord t = redWord s := by
  induction path with
  | nil => rfl
  | swap _ j hj r hr hb hz ih =>
    exact (redWord_sadj_smul _ hj (by rw [hr, hb]; simp)).trans ih

variable {k : Type*} [CommRing k]
variable (Q : I → I → MvPolynomial (Fin 2) k)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ

private theorem unitEval (v : Fin 2 → R) : ncEval v (1 : MvPolynomial (Fin 2) k) = 1 := by
  unfold ncEval
  rw [show (1 : MvPolynomial (Fin 2) k).coeff = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

private theorem unitBigons (t : Seq μ) (j : ℕ) (hj : j + 1 < n) (r : Fin ℓ)
    (hr : t.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hb : t.lbl ⟨j + 1, hj⟩ = .inl i) (hz : Λ r i = 0) :
    ((KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e t : R) = KLRAlgebra.e t) ∧
      ((KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e (TypeA.sadj n j • t) : R) =
        KLRAlgebra.e (TypeA.sadj n j • t)) := by
  refine ⟨?_, ?_⟩
  · rw [KLRAlgebra.ψ_sq j hj, hr, hb]
    simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, hz, pow_zero, unitEval, one_mul]
  · have hr' : (TypeA.sadj n j • t).lbl ⟨j + 1, hj⟩ = .inr r := by
      change (TypeA.sadj n j • t).1 _ = _
      rw [KLRAlgebra.sadj_smul_apply, TypeA.sadj_apply_right hj]
      exact hr
    have hb' : (TypeA.sadj n j • t).lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inl i := by
      change (TypeA.sadj n j • t).1 _ = _
      rw [KLRAlgebra.sadj_smul_apply, TypeA.sadj_apply_left hj]
      exact hb
    rw [KLRAlgebra.ψ_sq j hj, hb', hr']
    simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, hz, pow_zero, unitEval, one_mul]

/-- The endpoint idempotents are equivalent in any common ordered corner. -/
theorem ZeroWeightSpectatorPath.orderedIdemEquivAt {s t : Seq μ} {κ : List (Fin ℓ)}
    (path : ZeroWeightSpectatorPath Λ s t) (hs : redWord s = κ) :
    IdemEquiv (orderedLoadingIdemAt Q Λ κ s hs)
      (orderedLoadingIdemAt Q Λ κ t ((path.redWord_eq Λ).trans hs)) := by
  induction path with
  | nil =>
    subst κ
    exact IdemEquiv.refl (orderedLoadingIdem_idem Q Λ s)
  | @swap t path j hj r hr hb hz ih =>
    apply ih.trans
    have ht := (path.redWord_eq Λ).trans hs
    have hw : redWord (TypeA.sadj n j • t) = redWord t :=
      redWord_sadj_smul _ hj (by rw [hr, hb]; simp)
    obtain ⟨h₁, h₂⟩ := unitBigons Λ Q t j hj r hr hb hz
    have aux (κ' : List (Fin ℓ)) (ht' : redWord t = κ') :
        IdemEquiv (orderedLoadingIdemAt Q Λ κ' t ht')
          (orderedLoadingIdemAt Q Λ κ' (TypeA.sadj n j • t) (hw.trans ht')) := by
      subst κ'
      exact loadingIdemEquiv_of_unit_bigon Q Λ t _ hw j rfl h₁ h₂
    exact aux _ ht

/-- The actual retained kernel is the final partial standard whenever a chain of
zero-weight crossings reaches a maximal surviving higher retained loading. -/
def kernelEquivPartialStandard_of_zeroWeightSpectatorPath
    {s t : Seq μ} (path : ZeroWeightSpectatorPath Λ s t) (a b : Fin ℓ)
    (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b t)
    (hmax : ∀ w : Seq μ, redWord w = redWord t →
      adjacentBlockRoot a b t < adjacentBlockRoot a b w → IsViolated w) :
    (blockLoadingKernel Q Λ s a b) ≃ₗ[
      (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord s)))ᵐᵒᵖ]
      blockPartialStandardAt Q Λ t a b (redWord s) (path.redWord_eq Λ) := by
  have he := ZeroWeightSpectatorPath.orderedIdemEquivAt Λ Q path rfl
  have htop := blockLoadingKernel_eq_top_of_equiv Q Λ s t a b (path.redWord_eq Λ) hlt he
  let p := blockLoadingKernel Q Λ s a b
  let φ := Classical.choose_spec (Classical.choose_spec he)
  exact (LinearEquiv.ofEq p ⊤ htop).trans (Submodule.topEquiv.trans
    (φ.rIdealEquiv.trans (blockPartialStandardAt_equiv_projective
      Q Λ t a b (redWord s) (path.redWord_eq Λ) hmax).symm))

omit [DecidableEq I] in
private theorem headRedWord_eq {w : Seq μ} (hpos : 0 < n) {r : Fin ℓ}
    (hr : w.lbl ⟨0, hpos⟩ = .inr r) : (redWord w).head? = some r := by
  have hhead : (List.finRange n).head? = some ⟨0, hpos⟩ := by
    rw [List.head?_eq_getElem?]
    have hlen : 0 < (List.finRange n).length := by simpa only [List.length_finRange]
    rw [List.getElem?_eq_getElem hlen, List.getElem_finRange]
    rfl
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hhead
  unfold redWord
  rw [hrest, List.filterMap_cons, hr]
  rfl

/-- If the pair is first and the black is before every spectator, any strictly
higher loading in that same order is globally violated. -/
theorem isViolated_of_strictly_higher_beforeSpectators
    {a b : Fin ℓ} {t w : Seq μ} {M : List (Fin ℓ)}
    (ht : redWord t = a :: b :: M) (ho : redWord w = redWord t)
    (x : Fin n) (hx : t.lbl x = .inl i)
    (hbefore : ∀ r : Fin ℓ, r ≠ a → r ≠ b →
      ∀ q : Fin n, t.lbl q = .inr r → x < q)
    (hlt : adjacentBlockRoot a b t < adjacentBlockRoot a b w) : IsViolated w := by
  have hpos : 0 < n := by simp [stendhalWeight]
  cases hhead : w.lbl ⟨0, hpos⟩ with
  | inl c => exact ⟨hpos, by rw [hhead]; rfl⟩
  | inr r =>
    exfalso
    have hheadRed := headRedWord_eq hpos hhead
    rw [ho, ht] at hheadRed
    have hr : a = r := Option.some.inj hheadRed
    subst r
    have hm : (Sum.inl i : I ⊕ Fin ℓ) ∈ μ := by simp [stendhalWeight]
    rw [← show Finset.univ.val.map w.lbl = μ from w.2, Multiset.mem_map] at hm
    obtain ⟨y, _, hy⟩ := hm
    have hw : redWord w = ([] : List (Fin ℓ)) ++ a :: b :: M := ho.trans ht
    apply hlt.not_ge
    apply (adjacentBlockRoot_oneBlack_le_iff hw ht y x hy hx).2
    intro r hr p q hp hq hyp
    by_cases hra : r = a
    · subst r
      have huniq : Function.Injective w.lbl := by
        have hn : (Finset.univ.val.map w.lbl).Nodup := by
          rw [show Finset.univ.val.map w.lbl = μ from w.2]
          simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
        exact fun j l e => Multiset.inj_on_of_nodup_map hn j (by simp) l (by simp) e
      have hp0 : p = ⟨0, hpos⟩ := huniq (hp.trans hhead.symm)
      subst p
      exact (Nat.not_lt_zero _ (show y.val < 0 from hyp)).elim
    · exact hbefore r hra hr q hq

/-- A chain ending before all spectators gives the actual higher partial standard
when the paired reds are first and the endpoint is strictly higher. -/
def kernelEquivPartialStandard_beforeSpectators
    {s t : Seq μ} (path : ZeroWeightSpectatorPath Λ s t) (a b : Fin ℓ) {M : List (Fin ℓ)}
    (ht : redWord t = a :: b :: M) (x : Fin n) (hx : t.lbl x = .inl i)
    (hbefore : ∀ r : Fin ℓ, r ≠ a → r ≠ b →
      ∀ q : Fin n, t.lbl q = .inr r → x < q)
    (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b t) :
    (blockLoadingKernel Q Λ s a b) ≃ₗ[
      (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord s)))ᵐᵒᵖ]
      blockPartialStandardAt Q Λ t a b (redWord s) (path.redWord_eq Λ) :=
  kernelEquivPartialStandard_of_zeroWeightSpectatorPath Λ Q path a b hlt
    (fun _ ho hh => isViolated_of_strictly_higher_beforeSpectators ht ho x hx hbefore hh)

end Categorification.Stendhal.BraidedStendhalAlgebra
