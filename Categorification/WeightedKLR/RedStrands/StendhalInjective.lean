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

variable (ρ) in
/-- The lift `ψ_{ρ w} x^u e(i)` of a term of the KLR basis to the free algebra. -/
noncomputable def fStd (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    FreeAlgebra k (KLR.Gen μ) :=
  ((ρ b.2.1).map (KLR.fψ k μ)).prod * KLR.ncEval (fun a => KLR.fx k μ a) (monomial b.2.2 (1 : k)) *
    KLR.fe k μ b.1

theorem mk_fStd (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    KLRAlgebra.mk k (stendhalQ Q Λ) μ (fStd ρ b) = KLRAlgebra.stdElt ρ b := by
  have hp : KLRAlgebra.mk k (stendhalQ Q Λ) μ
      (KLR.ncEval (fun a => KLR.fx k μ a) (monomial b.2.2 (1 : k))) =
        KLRAlgebra.pol (monomial b.2.2 1) := by
    rw [KLRAlgebra.mk_ncEval]
    exact (KLRAlgebra.ncEval_eq_pol id _).trans (by rw [rename_id]; rfl)
  rw [fStd, map_mul, map_mul, hp, map_list_prod, List.map_map]
  rfl

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

/-! ### The polynomial representation of the lifted terms -/

open KLR.PolyRep in
theorem freeRep_fStd_single (P : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (ρ : Perm (Fin m) → List ℕ) (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ))
    (i : KLR.Seq μ) (h : MvPolynomial (Fin m) k) :
    freeRep μ P (fStd ρ b) (Pi.single i h) =
      if b.1 = i then
        Pi.single (TypeA.wordProd m (ρ b.2.1) • i) (wordComp P (ρ b.2.1) i (monomial b.2.2 1 * h))
      else 0 := by
  have hψ : freeRep μ P ((ρ b.2.1).map (KLR.fψ k μ)).prod = opΨw P (ρ b.2.1) := by
    rw [map_list_prod, List.map_map]
    simp [opΨw, Function.comp_def]
  have hp : freeRep μ P (KLR.ncEval (fun a => KLR.fx k μ a) (monomial b.2.2 (1 : k))) =
      opMul μ (monomial b.2.2 (1 : k)) :=
    (freeRep_ncEval P id _).trans (by rw [rename_id]; rfl)
  rw [fStd, map_mul, map_mul, hψ, hp, Module.End.mul_apply, Module.End.mul_apply, freeRep_fe]
  by_cases hi : b.1 = i
  · subst hi
    have e1 : opE b.1 (Pi.single b.1 h) = Pi.single b.1 h := by
      funext t; rw [opE_apply]; by_cases ht : t = b.1 <;> simp [ht]
    have e2 : opMul μ (monomial b.2.2 1) (Pi.single b.1 h : Pol k μ) =
        Pi.single b.1 (monomial b.2.2 1 * h) := by
      funext t; rw [opMul_apply]; by_cases ht : t = b.1 <;> simp [ht]
    rw [e1, e2, opΨw_single]
    simp
  · have e1 : opE b.1 (Pi.single i h) = 0 := by
      funext t; rw [opE_apply]; by_cases ht : t = b.1 <;> simp [ht, Ne.symm hi]
    rw [e1, map_zero, map_zero]
    simp [hi]

open KLR.PolyRep in
/-- The operator of a combination of lifted terms, between the components `Pol_i` and `Pol_t`,
is the block `blockSum`. -/
theorem freeRep_sum_fStd (P : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.wordProd m (ρ w) = w)
    (s : Finset (KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)))
    (c : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) → k) (i t : KLR.Seq μ)
    (h : MvPolynomial (Fin m) k) :
    freeRep μ P (∑ b ∈ s, c b • fStd ρ b) (Pi.single i h) t = blockSum P ρ s c i t h := by
  classical
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, freeRep_fStd_single, hρ, blockSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hi : b.1 = i
  · subst hi
    by_cases ht : b.2.1 • b.1 = t
    · subst ht; simp
    · simp [ht, Ne.symm ht]
  · simp [hi]

omit [DecidableEq I] in
theorem blackEval_monomial {i : KLR.Seq μ} {u : Fin m →₀ ℕ}
    (hu : ∀ a ∈ u.support, (i.1 a).isLeft) :
    blackEval (k := k) i (monomial u 1) = monomial u 1 := by
  rw [blackEval, aeval_monomial, monomial_eq, map_one, C_1]
  congr 1
  refine Finsupp.prod_congr fun a ha => ?_
  simp [hu a ha]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Killing the red variables turns the blocks for `stP` into the blocks for `stBlackP`, on the
polynomials in the black variables, for combinations of terms without red dots or red
crossings. -/
theorem blackEval_blockSum {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.wordProd m (ρ w) = w)
    (s : Finset (KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)))
    (c : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) → k)
    (hc : ∀ b, c b ≠ 0 → (∀ a ∈ b.2.2.support, (b.1.1 a).isLeft) ∧ NoRedCross (ρ b.2.1) b.1)
    (i t : KLR.Seq μ) {h : MvPolynomial (Fin m) k} (hh : blackEval i h = h) :
    blackEval t (blockSum (stP Γ Λ) ρ s c i t h) = blockSum (stBlackP Γ Λ) ρ s c i t h := by
  simp only [blockSum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨-, rfl, rfl⟩ := Finset.mem_filter.1 hb
  by_cases hcb : c b = 0
  · simp [hcb]
  obtain ⟨hu, hn⟩ := hc b hcb
  have := blackEval_wordComp (Γ := Γ) (Λ := Λ) (ρ b.2.1) b.1 hn (monomial b.2.2 1 * h)
  rw [hρ] at this
  rw [this, map_mul, blackEval_monomial hu, hh]

/-! ### Injectivity -/

open StendhalAlgebraAllOrders in
/-- **Injectivity in Webster's Theorem 3.5** (arXiv:1209.2463v4, proof of Theorem 3.5): the
homomorphism `stTildeHom` from `T̃^λ` to the chamber algebra of `Γ_λ = crawleyBoeveyIn Γ Λ ϖ`
modulo the dot on the `0`-strand is injective.

The hypotheses `hE` (no edge from a vertex to itself) and `hl` (no loops) are those of
`stTildeHom`; they are needed only to check the relations through the polynomial
representation, and are not among Webster's hypotheses. -/
theorem stTildeHom_injective (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (hS : Γ.Standing) : Function.Injective (stTildeHom ν k Γ Λ hD hE hl hϖ hw0 hS) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Perm (Fin m) → List ℕ,
      ∀ w, TypeA.IsReduced m (ρ w) ∧ TypeA.wordProd m (ρ w) = w :=
    ⟨fun w => (TypeA.exists_reduced m w).choose, fun w => (TypeA.exists_reduced m w).choose_spec⟩
  have hρ' : ∀ w, TypeA.wordProd m (ρ w) = w := fun w => (hρ w).2
  obtain ⟨c, hc⟩ := exists_eq_sum_stendhalTerm (k := k) (Q := Γ.klrQ) (Λ := Λ) hρ x
  set c' := fun b => if IsStendhalTerm ρ b then c b else 0 with hc'
  have hc'0 : ∀ b, c' b ≠ 0 → IsStendhalTerm ρ b := fun b hb => by
    by_contra h; exact hb (by simp [hc', h])
  set F := ∑ b ∈ c.support, c' b • fStd (k := k) ρ b
  have hxF : x.1 = RingQuot.mkAlgHom k (Rel k Γ.klrQ Λ ν) F := by
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← ofKLR_mk, mk_fStd]
    rfl
  have hF : stFreeHom ν k Λ hϖ hw0 F ∈ stZeroDotIdeal ν k Λ hϖ hw0 := by
    have h0 := hx
    rw [stTildeHom_apply, hxF, stStendhalHom_mk, ← map_zero
      ((stZeroDotIdeal ν k Λ hϖ hw0).ringCon.mkₐ k)] at h0
    have := (TwoSidedIdeal.rel_iff _ _ _).1 ((RingCon.eq _).1 h0)
    rwa [sub_zero] at this
  have hzero : ∀ b ∈ c.support, c' b = 0 := by
    refine eq_zero_of_blockSum_eq_zero (stBlackP Γ Λ) c.support c'
      (fun a b _ f hf => isRegular_rename_stBlackP hS a b hf) hρ fun i t h hh => ?_
    by_cases hit : IsRedOrdered i ∧ IsRedOrdered t
    · rw [← blackEval_blockSum hρ' c.support c'
        (fun b hb => ⟨(hc'0 b hb).2.2.1, (hc'0 b hb).2.2.2⟩) i t hh,
        ← freeRep_sum_fStd (stP Γ Λ) hρ']
      obtain ⟨G, hG⟩ := exists_chamberRep_eq_mulXOp hϖ hw0
        (WeightedGraph.crawleyBoeveyIn_psymm (psymm_of_loop hl)) hF
        (stRenOp ℓ ν k (Pi.single i h))
      have hR := congrArg (fun φ => φ (Pi.single i h) ⟨t, hit.2⟩)
        (chamberRep_stFreeHom (Λ := Λ) hD hE hl hϖ hw0 F)
      simp only [LinearMap.comp_apply, hG, mulXOp_apply, stRenOp_apply] at hR
      exact blackEval_eq_zero_of_stRen_eq hR.symm
    · rw [blockSum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun b hb => ?_
      obtain ⟨-, rfl, rfl⟩ := Finset.mem_filter.1 hb
      have : c' b = 0 := by
        by_contra hcb
        exact hit ⟨(hc'0 b hcb).1, (hc'0 b hcb).2.1⟩
      rw [LinearMap.smul_apply, this, zero_smul]
  refine Subtype.ext ?_
  rw [hc]
  refine (Finset.sum_eq_zero fun b hb => ?_).trans rfl
  change c' b • _ = 0
  rw [hzero b hb, zero_smul]

end Injective

end Categorification.Stendhal
