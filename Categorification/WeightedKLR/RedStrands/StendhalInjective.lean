/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StendhalDescent
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep
import Categorification.KLR.BasisTheorem
import Categorification.KLR.Filtration

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


/-! ### The spanning set of `T̃^λ` -/

section Terms

open KLR TypeA StendhalAlgebraAllOrders

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- A word exchanging two red strands kills `e(i)` in the algebra of Stendhal diagrams. -/
theorem ofKLR_ψw_mul_e_of_not_noRedCross (ρ : List ℕ) (i : KLR.Seq μ)
    (hn : ¬ NoRedCross ρ i) :
    ofKLR k Q Λ ν (KLRAlgebra.ψw ρ * KLRAlgebra.e i) = 0 := by
  induction ρ with
  | nil => exact absurd trivial hn
  | cons j ρ ih =>
    rw [KLRAlgebra.ψw_cons, mul_assoc]
    by_cases hρ : NoRedCross ρ i
    · have hj : ¬ ∀ h : j + 1 < m, ((wordProd m ρ • i).1 ⟨j, by omega⟩).isLeft ∨
          ((wordProd m ρ • i).1 ⟨j + 1, h⟩).isLeft := fun hj => hn ⟨hρ, hj⟩
      push Not at hj
      obtain ⟨h, h₁, h₂⟩ := hj
      have hz := ψ_mul_e_of_red (k := k) (Q := Q) (Λ := Λ) j h (wordProd m ρ • i)
        (by simpa using h₁) (by simpa using h₂)
      rw [KLRAlgebra.ψw_mul_e, ← mul_assoc, map_mul, map_mul]
      change ψ j * e (wordProd m ρ • i) * _ = 0
      rw [hz, zero_mul]
    · rw [map_mul, ih hρ, mul_zero]

/-- A dot on a red strand kills `e(i)` in the algebra of Stendhal diagrams. -/
theorem ofKLR_pol_mul_e_of_red (u : Fin m →₀ ℕ) (i : KLR.Seq μ) {a : Fin m}
    (ha : a ∈ u.support) (hr : ¬ (i.1 a).isLeft) :
    ofKLR k Q Λ ν (KLRAlgebra.pol (monomial u 1) * KLRAlgebra.e i) = 0 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + Finsupp.single a 1 :=
    ⟨u - Finsupp.single a 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 ha)))).symm⟩
  have hz := x_mul_e_of_red (k := k) (Q := Q) (Λ := Λ) a i (by simpa using hr)
  rw [monomial_add_single, pow_one, map_mul KLRAlgebra.pol, KLRAlgebra.pol_X, mul_assoc, map_mul,
    map_mul]
  change _ * (x a * e i) = 0
  rw [hz, mul_zero]

variable (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)

/-- The terms `ψ_{ρ w} x^u e(i)` of the KLR basis that survive in `T̃^λ`: `i` and `w • i` have
their red strands in order, `u` puts no dot on a red strand, and `ρ w` exchanges no two red
strands. -/
def IsStendhalTerm (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) : Prop :=
  IsRedOrdered b.1 ∧ IsRedOrdered (b.2.1 • b.1) ∧ (∀ a ∈ b.2.2.support, (b.1.1 a).isLeft) ∧
    NoRedCross (ρ b.2.1) b.1

variable {ρ}

theorem stdElt_mul_e (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    (KLRAlgebra.stdElt ρ b : KLRAlgebra k (stendhalQ Q Λ) μ) * KLRAlgebra.e b.1 =
      KLRAlgebra.stdElt ρ b := by
  rw [KLRAlgebra.stdElt, mul_assoc, KLRAlgebra.e_mul_e]
  simp

theorem e_mul_stdElt (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    KLRAlgebra.e (b.2.1 • b.1) * (KLRAlgebra.stdElt ρ b : KLRAlgebra k (stendhalQ Q Λ) μ) =
      KLRAlgebra.stdElt ρ b := by
  rw [KLRAlgebra.stdElt, KLRAlgebra.e_mul_gen, hρ, inv_smul_smul]
  simp

theorem stdElt_eq_ψw_mul_e_mul_pol (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    (KLRAlgebra.stdElt ρ b : KLRAlgebra k (stendhalQ Q Λ) μ) =
      KLRAlgebra.ψw (ρ b.2.1) * KLRAlgebra.e b.1 * KLRAlgebra.pol (monomial b.2.2 1) := by
  rw [KLRAlgebra.stdElt, mul_assoc, ← (KLRAlgebra.e_commute_pol _ _).eq, mul_assoc]

open Classical in
/-- **Cutting a basis term by the idempotent of `T̃^λ`**: `ψ_{ρ w} x^u e(i)` survives exactly
when it is a Stendhal term. -/
theorem redOrderedIdem_mul_ofKLR_stdElt_mul (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    redOrderedIdem k Q Λ ν * ofKLR k Q Λ ν (KLRAlgebra.stdElt ρ b) * redOrderedIdem k Q Λ ν =
      if IsStendhalTerm ρ b then ofKLR k Q Λ ν (KLRAlgebra.stdElt ρ b) else 0 := by
  set y := ofKLR k Q Λ ν (KLRAlgebra.stdElt ρ b)
  have hr : y * redOrderedIdem k Q Λ ν = if IsRedOrdered b.1 then y else 0 := by
    have hy : y = y * e b.1 := by
      change _ = ofKLR k Q Λ ν _ * ofKLR k Q Λ ν _
      rw [← map_mul, stdElt_mul_e]
    calc y * redOrderedIdem k Q Λ ν = y * (e b.1 * redOrderedIdem k Q Λ ν) := by
          rw [← mul_assoc, ← hy]
      _ = _ := by rw [e_mul_redOrderedIdem]; split_ifs <;> simp [← hy]
  have hl : redOrderedIdem k Q Λ ν * y = if IsRedOrdered (b.2.1 • b.1) then y else 0 := by
    have hy : y = e (b.2.1 • b.1) * y := by
      change _ = ofKLR k Q Λ ν _ * ofKLR k Q Λ ν _
      rw [← map_mul, e_mul_stdElt hρ]
    calc redOrderedIdem k Q Λ ν * y = redOrderedIdem k Q Λ ν * e (b.2.1 • b.1) * y := by
          rw [mul_assoc, ← hy]
      _ = _ := by rw [redOrderedIdem_mul_e]; split_ifs <;> simp [← hy]
  rw [hl]
  by_cases h₁ : IsRedOrdered (b.2.1 • b.1)
  · simp only [h₁, ↓reduceIte, hr]
    by_cases h₂ : IsRedOrdered b.1
    · simp only [h₂, ↓reduceIte]
      by_cases h₃ : ∀ a ∈ b.2.2.support, (b.1.1 a).isLeft
      · by_cases h₄ : NoRedCross (ρ b.2.1) b.1
        · have ht : IsStendhalTerm ρ b := ⟨h₂, h₁, h₃, h₄⟩
          simp only [ht, ↓reduceIte]
        · have ht : ¬ IsStendhalTerm ρ b := fun h => h₄ h.2.2.2
          have hy : y = 0 := by
            simp only [y]
            rw [stdElt_eq_ψw_mul_e_mul_pol, map_mul, ofKLR_ψw_mul_e_of_not_noRedCross _ _ h₄,
              zero_mul]
          simp only [ht, ↓reduceIte, hy]
      · have ht : ¬ IsStendhalTerm ρ b := fun h => h₃ h.2.2.1
        push Not at h₃
        obtain ⟨a, ha, har⟩ := h₃
        have hy : y = 0 := by
          simp only [y]
          rw [KLRAlgebra.stdElt, mul_assoc, map_mul,
            ofKLR_pol_mul_e_of_red _ _ ha (by simpa using har), mul_zero]
        simp only [ht, ↓reduceIte, hy]
    · have ht : ¬ IsStendhalTerm ρ b := fun h => h₂ h.1
      simp only [h₂, ht, ↓reduceIte]
  · have ht : ¬ IsStendhalTerm ρ b := fun h => h₁ h.2.1
    simp only [h₁, ht, ↓reduceIte, zero_mul]

open Classical in
/-- **The Stendhal terms span `T̃^λ`**: every element of `T̃^λ` is a combination of the images
of the Stendhal terms `ψ_{ρ w} x^u e(i)` of the KLR basis (KL I, Theorem 2.5). -/
theorem exists_eq_sum_stendhalTerm
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (x : StendhalAlgebra k Q Λ ν) :
    ∃ c : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) →₀ k,
      x.1 = ∑ b ∈ c.support, (if IsStendhalTerm ρ b then c b else 0) •
        ofKLR k Q Λ ν (KLRAlgebra.stdElt ρ b) := by
  have hx' := (Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 x.2
  obtain ⟨y, hy⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) x.1
  have hys : y ∈ Submodule.span k (Set.range (KLRAlgebra.stdElt (k := k)
      (Q := stendhalQ Q Λ) ρ)) := by
    rw [KLRAlgebra.span_stdElt ρ hρ]; trivial
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hys
  refine ⟨c, ?_⟩
  rw [← hx'.2, ← hx'.1, ← hy, Finsupp.sum, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, mul_smul_comm, smul_mul_assoc,
    redOrderedIdem_mul_ofKLR_stdElt_mul (fun w => (hρ w).2)]
  split_ifs <;> simp

end Terms

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
