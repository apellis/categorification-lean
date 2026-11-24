/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineHigherKernelMap
import Categorification.WeightedKLR.RedStrands.OneBlackOmittedRedCrossing
import Categorification.WeightedKLR.RedStrands.OrdinaryRetainedCrossing

/-!
# The one-black kernel map across a pair

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The two-crossing coefficient identifies the actual higher loading projective
with the retained kernel when the constituent ordinary crossing tests hold.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₁
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν₁
local notation "π" => AlgHom.comp (violMk k Q Λ ν₁) (ofKLR k Q Λ ν₁)
local notation "p" => fun w => π (KLRAlgebra.e w)
local notation "E" => violMk k Q Λ ν₁ (redProj k Q Λ ν₁ (List.finRange ℓ))


/-- The two constituent crossings across the pair identify the final higher
loading projective with the initial kernel. -/
theorem nonempty_kernelEquiv_of_twoCrossingTests
    {s t u : KLR.Seq (stendhalWeight ℓ (Singleton.singleton i : Multiset I))} (j : ℕ)
    (a b : Fin ℓ) {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) (word : redWord s = List.finRange ℓ)
    (h₁ : sadj n (j + 1) • s = t) (h₂ : sadj n j • t = u)
    (ho : redWord u = redWord s) (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b u)
    (hj : j + 2 < n) (ha : s.lbl ⟨j, by omega⟩ = .inr a)
    (hr : s.lbl ⟨j + 1, by omega⟩ = .inr b) (hb : s.lbl ⟨j + 2, hj⟩ = .inl i)
    (hQ : KLRSymm Q)
    (test₁ : OrdinaryCutCrossingTest Q Λ s t (j + 1))
    (test₂ : OrdinaryCutCrossingTest Q Λ t u j) :
    Nonempty (rIdeal (orderedLoadingIdemAt Q Λ (redWord s) u ho) ≃ₗ[(IsIdempotentElem.Corner
      (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord s)))ᵐᵒᵖ]
      blockLoadingKernel Q Λ s a b) := by
  have ht : redWord t = redWord s := by
    rw [← h₁]
    exact redWord_sadj_smul s hj (by rw [hr, hb]; simp)
  have hu : redWord u = redWord t := ho.trans ht.symm
  let coefficient : R := (ψ (j + 1) * KLRAlgebra.e t) * (ψ j * KLRAlgebra.e u)
  have hleft : AffineLeftFixed Q Λ s coefficient := by
    have hswt : sadj n (j + 1) • t = s := by rw [← h₁, sadj_smul_smul]
    have hfix : (KLRAlgebra.e s : R) * (ψ (j + 1) * KLRAlgebra.e t) =
        ψ (j + 1) * KLRAlgebra.e t := by rw [ψ_mul_e, hswt, ← mul_assoc, e_mul_self]
    change (KLRAlgebra.e s : R) * coefficient = coefficient
    dsimp only [coefficient]
    rw [← mul_assoc, hfix]
  have hright : AffineRightFixed Q Λ u coefficient := by
    change coefficient * (KLRAlgebra.e u : R) = coefficient
    dsimp only [coefficient]
    simp only [mul_assoc, e_mul_self]
  let f := affineIntoKernelMap Q Λ a b ho hlt coefficient hright
  have hsurj : Function.Surjective f := by
    apply affineIntoKernelMap_surjective_of_factors Q Λ a b ho hlt coefficient hleft hright
    intro w hw hh _ z
    have hfactor := oneBlack_cut_factors_across_pair Q Λ s hs j hj ha hr hb w hw hh z
    rw [h₁, h₂] at hfactor
    exact hfactor
  have hzero (y : rIdeal (orderedLoadingIdemAt Q Λ (redWord s) u ho)) (hy : f y = 0) : y = 0 := by
    have hY : E * y.1.1 = y.1.1 ∧ y.1.1 * E = y.1.1 := by
      have inner := (Subsemigroup.mem_corner_iff
        (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord s))).1 y.1.2
      have hEeq := congrArg (fun word => violMk k Q Λ ν₁ (redProj k Q Λ ν₁ word)) word
      exact ⟨(congrArg (fun z => z * y.1.1) hEeq).symm.trans inner.1,
        (congrArg (fun z => y.1.1 * z) hEeq).symm.trans inner.2⟩
    have hp : p u * y.1.1 = y.1.1 := congrArg Subtype.val y.2
    have hy' : π coefficient * y.1.1 = 0 := by
      rw [← affineIntoKernelMap_val Q Λ a b ho hlt coefficient hleft hright]
      change (f y).1.1.1 = 0
      rw [hy]
      rfl
    apply Subtype.ext
    apply Subtype.ext
    exact eq_zero_of_twoCrossings_mul_of_corner Q Λ word ht hu (j + 1) j h₁ h₂ hQ
      test₁ test₂ y.1.1 hY hp hy'
  have hinj : Function.Injective f := by
    intro y z heq
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, heq, sub_self]
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
