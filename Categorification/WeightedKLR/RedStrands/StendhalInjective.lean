/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StendhalDescent
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep

/-!
# Injectivity of the homomorphism of Webster's Theorem 3.5

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5: the homomorphism `stTildeHom` from `T̃^λ` (Stendhal diagrams,
arXiv:1309.3796v2, Definition 4.5) to the chamber algebra of `Γ_λ` modulo the dot on the
`0`-strand is injective.

Webster's argument compares bases. Here the comparison runs through the polynomial
representations. An element of `T̃^λ` is a combination of the elements `ψ_{ρ w} x^u e(i)` of the
KLR basis (KL I, Theorem 2.5, `KLRAlgebra.span_stdElt`). Those with `i` or `w • i` not
red-ordered, with a dot on a red strand, or crossing two red strands are `0` in `T̃^λ`. If the
image of the combination lies in the ideal of the dot on the `0`-strand, its operator in the
polynomial representation of the chamber algebra has values divisible by that dot. Through the
renaming to the strands of `ν̃` (`chamberRep_stFreeHom`) this kills the KLR operators of the
remaining terms, for the polynomials `stBlackP`, on polynomials in the variables of the black
strands (`blackEval_wordComp`). Faithfulness on the black strands
(`eq_zero_of_blockSum_eq_zero`, from KL I, Theorem 2.5) gives that their coefficients vanish.

## Main results

* `Stendhal.stBack`, `Stendhal.blackEval_eq_zero_of_stRen_eq`: a renamed polynomial divisible by
  the dot on the `0`-strand has no part in the variables of the black strands.
* `Stendhal.exists_chamberRep_eq_mulXOp`: elements of `stZeroDotIdeal` act by operators with
  values divisible by the dot on the `0`-strand.
-/

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv MvPolynomial FullChamber GalleryAlgebra

section Injective

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}

local notation "μ" => stendhalWeight ℓ ν
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "s₀" => GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)

/-- Back from the strands of `ν̃` to the positions of `i`: a black strand to its position, the
`0`-strand to `0`. -/
noncomputable def stBack (i : KLR.Seq μ) : PolyRing ν̃ k →ₐ[k] MvPolynomial (Fin m) k :=
  aeval fun t => (ofTilde t).elim 0 fun s => X (i.posOf s)

/-- Going back after renaming kills the variables of the red strands. -/
theorem stBack_stRen (i : KLR.Seq μ) (p : MvPolynomial (Fin m) k) :
    stBack i (stRen i p) = blackEval i p := by
  have h : (stBack (k := k) i).comp (stRen i) = blackEval i := by
    refine MvPolynomial.algHom_ext fun a => ?_
    rw [AlgHom.comp_apply, stRen, rename_X, stBack, aeval_X, blackEval_X]
    by_cases ha : (i.1 a).isLeft
    · rw [ofTilde_toTilde_inl (s := i.strandAt a) ha]
      simp [ha]
    · rw [toTilde_of_not_isLeft (s := i.strandAt a) ha, ofTilde_zeroStrand]
      simp [ha]
  exact congrArg (fun φ : MvPolynomial (Fin m) k →ₐ[k] _ => φ p) h

theorem stBack_X_zeroStrand (i : KLR.Seq μ) : stBack (k := k) i (X s₀) = 0 := by
  rw [stBack, aeval_X, ofTilde_zeroStrand]
  rfl

/-- A renamed polynomial divisible by the dot on the `0`-strand has no part in the variables of
the black strands. -/
theorem blackEval_eq_zero_of_stRen_eq {i : KLR.Seq μ} {p : MvPolynomial (Fin m) k}
    {q : PolyRing ν̃ k} (h : stRen i p = X s₀ * q) : blackEval i p = 0 := by
  rw [← stBack_stRen, h, map_mul, stBack_X_zeroStrand, zero_mul]

/-- **Elements of the ideal of the `0`-dot act by multiples of the `0`-dot**: the operator of an
element of `stZeroDotIdeal` in the polynomial representation of the chamber algebra has values
divisible by the dot on the `0`-strand. -/
theorem exists_chamberRep_eq_mulXOp (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (hΓ : (WeightedGraph.crawleyBoeveyIn Γ Λ ϖ).PSymm)
    {y : ChamberAlgebra k (stFull (ν := ν) Λ hϖ hw0)} (hy : y ∈ stZeroDotIdeal ν k Λ hϖ hw0)
    (g : OrdSeq ℓ ν → PolyRing ν̃ k) :
    ∃ G, chamberRep k (stFull Λ hϖ hw0) hΓ y g = mulXOp s₀ G := by
  have hc : ∀ x : ChamberAlgebra k (stFull (ν := ν) Λ hϖ hw0),
      Commute (chamberRep k (stFull Λ hϖ hw0) hΓ x) (mulXOp s₀) := fun x =>
    chamberOp_commute_mulXOp (GalleryAlgebra.redWeight_zeroStrand _) hΓ x.1
  induction hy using TwoSidedIdeal.span_induction generalizing g with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨g, funext fun j => ?_⟩
    rw [stZeroDot, chamberRep_chamberElt, chamberOp_diagonal, galleryRep_poly, diagOp_apply,
      Pi.single_eq_same, LinearMap.mulLeft_apply, mulXOp_apply]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨G, hG⟩ := h g
    obtain ⟨G', hG'⟩ := h' g
    exact ⟨G + G', by rw [map_add, LinearMap.add_apply, hG, hG', map_add]⟩
  | neg x _ h =>
    obtain ⟨G, hG⟩ := h g
    exact ⟨-G, by rw [map_neg, LinearMap.neg_apply, hG, map_neg]⟩
  | left_absorb a x _ h =>
    obtain ⟨G, hG⟩ := h g
    refine ⟨chamberRep k (stFull Λ hϖ hw0) hΓ a G, ?_⟩
    rw [map_mul, Module.End.mul_apply, hG, ← Module.End.mul_apply, (hc a).eq,
      Module.End.mul_apply]
  | right_absorb b x _ h =>
    obtain ⟨G, hG⟩ := h (chamberRep k (stFull Λ hϖ hw0) hΓ b g)
    exact ⟨G, by rw [map_mul, Module.End.mul_apply, hG]⟩

end Injective

end Categorification.Stendhal
