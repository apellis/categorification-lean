/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardEnd
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.QuotientBasis
import Categorification.TypeA.Inversions
import Categorification.KLR.NcEvalHom
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The two dots in the label-two middle standard

Webster, arXiv:1309.3796v2, §8.2, proof preceding Proposition 8.4. Using
the actual loading with one black strand on each side of the second red,
the two dot squares factor through a violated cut and a higher cut.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 blackWeight

variable (k : Type) [Field k]

/-- The two red strands each have coroot pairing two. -/
def weights (_ : Fin 2) : Unit →₀ ℕ := Finsupp.single () 2

/-- The one-colour KLR polynomial for type A₁. -/
def parameter (_ _ : Unit) : MvPolynomial (Fin 2) k := 0

local notation "q₀" => parameter k
local notation "wt₂" => weights
local notation "A" => TensorProductAlgebra k q₀ wt₂ blackWeight

/-- The middle loading is red, black, red, black. -/
def loading : Seq μ :=
  Seq.ofList [.inr 0, .inl (), .inr 1, .inl ()] (by decide)

theorem loading_ordered : IsRedOrdered loading := by
  unfold IsRedOrdered
  decide +kernel

/-- The actual diagrammatic middle standard for two red weights of label two. -/
abbrev Standard := leftStandard q₀ wt₂ loading loading_ordered

local notation "S" => Standard k
local notation "g" => leftStandardUnit q₀ wt₂ loading loading_ordered
local notation "π" => tensorOfKLR q₀ wt₂ blackWeight

/-- Dot on the black strand before the second red. -/
def leftMiddleDot : A := π (KLRAlgebra.x ⟨1, by decide⟩)

/-- Dot on the black strand after the second red. -/
def rightMiddleDot : A := π (KLRAlgebra.x ⟨3, by decide⟩)

private abbrev cut (j : ℕ) : Seq μ := sadj (Multiset.card μ) j • loading

private theorem cutZeroOrdered : IsRedOrdered (cut 0) := by
  unfold IsRedOrdered
  decide +kernel

private theorem cutTwoOrdered : IsRedOrdered (cut 2) := by
  unfold IsRedOrdered
  decide +kernel

private theorem cutZeroViolated : IsViolated (cut 0) := ⟨by decide, rfl⟩

private theorem cutTwoHigher : StendhalLT loading (cut 2) := by
  unfold StendhalLT StendhalLE
  decide +kernel

private theorem proj_loading (s : Seq μ) (hs : IsRedOrdered s) :
    π (e s) = seqIdem q₀ wt₂ s hs := by
  apply congrArg (TensorProductAlgebra.mk q₀ wt₂ blackWeight)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem proj_cutZero : π (e (cut 0)) = 0 := by
  rw [proj_loading k _ cutZeroOrdered]
  change (StendhalAlgebra.violatedIdeal k q₀ wt₂ blackWeight).ringCon.mk' _ = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨cut 0, cutZeroOrdered, cutZeroViolated, rfl⟩

private theorem projected_mul (a b : KLRAlgebra k (stendhalQ q₀ wt₂) μ) :
    π (a * b) = π a * π b := by simp only [tensorOfKLR, map_mul]

private theorem projected_pow (a : KLRAlgebra k (stendhalQ q₀ wt₂) μ) (n : ℕ) :
    π (a ^ n) = π a ^ n := by simp only [tensorOfKLR, map_pow]

private theorem middle_bigon (j : ℕ) (hj : j + 1 < Multiset.card μ) (r : Fin 2)
    (hr : loading.lbl ⟨j, by omega⟩ = .inr r)
    (hi : loading.lbl ⟨j+1, hj⟩ = .inl ()) :
    (π (KLRAlgebra.x (Q := stendhalQ q₀ wt₂) ⟨j+1, hj⟩)) ^ 2 *
      seqIdem q₀ wt₂ loading loading_ordered =
      π (KLRAlgebra.ψ j) * (π (KLRAlgebra.e (cut j)) * π (KLRAlgebra.ψ j)) := by
  rw [← projected_mul, ← projected_mul, ← mul_assoc, ← KLRAlgebra.e_mul_ψ,
    mul_assoc, KLRAlgebra.e_mul_ψ_mul_ψ, ← projected_pow]
  -- Both sides are the projection of the mixed bigon at the middle loading.
  rw [← proj_loading k _ loading_ordered, ← projected_mul]
  apply congrArg (fun a => π a)
  symm
  have hb := KLRAlgebra.ψ_sq (Q := stendhalQ q₀ wt₂) j hj loading
  rw [hr, hi] at hb
  simp only [reduceCtorEq, ↓reduceIte] at hb
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j+1, hj⟩] :
      Fin 2 → KLRAlgebra k (stendhalQ q₀ wt₂) μ) =
      fun q => KLRAlgebra.x (![⟨j, by omega⟩, ⟨j+1, hj⟩] q) := by
    funext q
    fin_cases q <;> rfl
  rw [stendhalQ_inr_inl, hv, KLRAlgebra.ncEval_eq_pol] at hb
  simp only [map_pow, MvPolynomial.rename_X, KLRAlgebra.pol_X,
    weights, Finsupp.single_eq_same] at hb
  exact hb

private theorem gen_fixed : seqIdem q₀ wt₂ loading loading_ordered • (g : S) = g := by
  rw [leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self q₀ wt₂ _ _)

/-- The left dot square kills the generator by factoring through a violated
loading. -/
theorem leftMiddleDot_sq_generator : (leftMiddleDot k)^2 • (g : S) = 0 := by
  have h := middle_bigon k 0 (by decide) 0 rfl rfl
  change (leftMiddleDot k)^2 * _ = _ at h
  rw [proj_cutZero, zero_mul, mul_zero] at h
  rw [← gen_fixed k, ← mul_smul, h, zero_smul]

/-- The right dot square kills the generator by factoring through the
loading with both blacks before the second red. -/
theorem rightMiddleDot_sq_generator : (rightMiddleDot k)^2 • (g : S) = 0 := by
  have h := middle_bigon k 2 (by decide) 1 rfl rfl
  change (rightMiddleDot k)^2 * _ = _ at h
  rw [← gen_fixed k, ← mul_smul, h, mul_smul, mul_smul,
    proj_loading k _ cutTwoOrdered,
    seqIdem_smul_leftStandard_eq_zero q₀ wt₂ loading_ordered cutTwoOrdered cutTwoHigher, smul_zero]

/-- The crossing that moves the right black into the higher loading
annihilates the entire fixed space of the middle loading. This is the
first crossing of the reduced word exchanging the two black strands
through the higher cut. -/
theorem higherCrossing_kills_middle_fixed (z : S)
    (hz : seqIdem q₀ wt₂ loading loading_ordered • z = z) :
    π (KLRAlgebra.ψ 2) • z = 0 := by
  have hcross : π (KLRAlgebra.ψ 2) * seqIdem q₀ wt₂ loading loading_ordered =
      seqIdem q₀ wt₂ (cut 2) cutTwoOrdered * π (KLRAlgebra.ψ 2) := by
    rw [← proj_loading k loading loading_ordered, ← proj_loading k _ cutTwoOrdered,
      ← projected_mul, ← projected_mul, KLRAlgebra.ψ_mul_e]
  rw [← hz, ← mul_smul, hcross, mul_smul,
    seqIdem_smul_leftStandard_eq_zero q₀ wt₂ loading_ordered cutTwoOrdered cutTwoHigher]

private def liftMiddleDot (a : A) : Module.End A S :=
  leftStandardLift (Q := q₀) (Λ := wt₂) loading loading_ordered (a • g)
    (fun t ht b hlt => by
      rw [mul_smul, seqIdem_smul_leftStandard_eq_zero q₀ wt₂ loading_ordered ht hlt])

private theorem liftMiddleDot_generator (a : A)
    (ha : Commute (seqIdem q₀ wt₂ loading loading_ordered) a) :
    liftMiddleDot k a g = a • g := by
  unfold liftMiddleDot
  apply leftStandardLift_unit (Q := q₀) (Λ := wt₂)
  rw [← mul_smul, ha.eq, mul_smul, gen_fixed]

private theorem projected_dot_commutes_idem (j : Fin (Multiset.card μ)) :
    Commute (seqIdem q₀ wt₂ loading loading_ordered) (π (KLRAlgebra.x j)) := by
  rw [← proj_loading k loading loading_ordered]
  change π (e loading) * π (KLRAlgebra.x j) =
    π (KLRAlgebra.x j) * π (e loading)
  rw [← projected_mul, ← projected_mul, KLRAlgebra.e_mul_x]

/-- The two right-dot endomorphisms of the diagrammatic standard. -/
def dotEnd : Fin 2 → Module.End A S :=
  ![liftMiddleDot k (leftMiddleDot k), liftMiddleDot k (rightMiddleDot k)]

/-- On the middle generator, the first right-dot map inserts the left black dot. -/
theorem dotEnd_zero_gen :
    dotEnd k 0 g = leftMiddleDot k • g :=
  liftMiddleDot_generator k _ (projected_dot_commutes_idem k ⟨1, by decide⟩)

/-- On the middle generator, the second right-dot map inserts the right black dot. -/
theorem dotEnd_one_gen :
    dotEnd k 1 g = rightMiddleDot k • g :=
  liftMiddleDot_generator k _ (projected_dot_commutes_idem k ⟨3, by decide⟩)

theorem dotEnd_sq (r : Fin 2) : (dotEnd k r)^2 = 0 := by
  apply leftStandard_hom_ext loading loading_ordered
  fin_cases r
  · change ((dotEnd k 0)^2) g = _
    rw [pow_two, Module.End.mul_apply, dotEnd_zero_gen, map_smul, dotEnd_zero_gen,
      ← mul_smul, ← pow_two, leftMiddleDot_sq_generator, LinearMap.zero_apply]
  · change ((dotEnd k 1)^2) g = _
    rw [pow_two, Module.End.mul_apply, dotEnd_one_gen, map_smul, dotEnd_one_gen,
      ← mul_smul, ← pow_two, rightMiddleDot_sq_generator, LinearMap.zero_apply]

private theorem dotEnd_pair : Commute (dotEnd k 0) (dotEnd k 1) := by
  apply leftStandard_hom_ext loading loading_ordered
  change (dotEnd k 0) ((dotEnd k 1) g) = (dotEnd k 1) ((dotEnd k 0) g)
  rw [dotEnd_one_gen, dotEnd_zero_gen, map_smul, map_smul, dotEnd_zero_gen, dotEnd_one_gen, ← mul_smul,
    ← mul_smul]
  congr 1
  unfold rightMiddleDot leftMiddleDot
  rw [← projected_mul, ← projected_mul]
  apply congrArg (fun a => π a)
  rw [← KLRAlgebra.pol_X, ← KLRAlgebra.pol_X, ← map_mul, ← map_mul, mul_comm]

private theorem dotEnd_commutes (r s : Fin 2) : Commute (dotEnd k r) (dotEnd k s) := by
  fin_cases r <;> fin_cases s
  · exact Commute.refl _
  · exact dotEnd_pair k
  · exact (dotEnd_pair k).symm
  · exact Commute.refl _

private def polynomialDotEnd : MvPolynomial (Fin 2) k →ₐ[k] Module.End A S :=
  (exists_algHom_ncEval (dotEnd k) (dotEnd_commutes k)).choose

private theorem polynomialDotEnd_X (r : Fin 2) :
    polynomialDotEnd k (MvPolynomial.X r) = dotEnd k r :=
  (exists_algHom_ncEval (dotEnd k) (dotEnd_commutes k)).choose_spec.1 r

/-- The square relations in the two-variable middle algebra. -/
def middleDotIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span (Set.range fun r => (MvPolynomial.X r : MvPolynomial (Fin 2) k)^2)

/-- The two-dot quotient in the proof preceding Webster's Proposition 8.4
acts by right dots on the actual middle standard. -/
def middleDotQuotientAction :
    ((MvPolynomial (Fin 2) k) ⧸ middleDotIdeal k) →ₐ[k] Module.End A S :=
  Ideal.Quotient.liftₐ (middleDotIdeal k) (polynomialDotEnd k) (by
    intro a ha
    have hk : middleDotIdeal k ≤ RingHom.ker (polynomialDotEnd k).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨r, rfl⟩
      change polynomialDotEnd k ((MvPolynomial.X r)^2) = 0
      rw [map_pow, polynomialDotEnd_X, dotEnd_sq]
    exact hk ha)

/-- Under the right-dot action, the two polynomial generators are the
two black dots on the middle standard. -/
@[simp] theorem middleDotQuotientAction_X (r : Fin 2) :
    middleDotQuotientAction k (Ideal.Quotient.mk (middleDotIdeal k) (MvPolynomial.X r)) =
      dotEnd k r := polynomialDotEnd_X k r

/-- The sum used in Webster's middle-layer quotient acts by the sum of the
two diagrammatic right dots. -/
theorem middleDotQuotientAction_sum :
    middleDotQuotientAction k (Ideal.Quotient.mk (middleDotIdeal k)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) = dotEnd k 0 + dotEnd k 1 := by
  rw [map_add, map_add, middleDotQuotientAction_X, middleDotQuotientAction_X]

/-- The middle-layer quotient by the sum of its two right-dot maps. -/
abbrev StandardDotSumQuotient := S ⧸ LinearMap.range (dotEnd k 0 + dotEnd k 1)

section Spanning

private abbrev blackPosition : Fin 2 → Fin (Multiset.card μ) :=
  ![⟨1, by decide⟩, ⟨3, by decide⟩]

private abbrev swapBlacks : Equiv.Perm (Fin (Multiset.card μ)) :=
  wordProd (Multiset.card μ) [2, 1, 2]

private def wordChoice (w : Equiv.Perm (Fin (Multiset.card μ))) : List ℕ :=
  if w = swapBlacks then [2, 1, 2] else canWord (Multiset.card μ) w

private theorem wordChoice_spec (w : Equiv.Perm (Fin (Multiset.card μ))) :
    IsReduced (Multiset.card μ) (wordChoice w) ∧ wordProd _ (wordChoice w) = w := by
  unfold wordChoice
  split_ifs with h
  · subst w
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    · rw [length_eq_invCount]
      decide +kernel
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private theorem wordChoice_one : wordChoice 1 = [] := by
  rw [wordChoice, ite_eq_right (by decide +kernel)]
  exact List.length_eq_zero_iff.mp (by rw [length_canWord, length_one])

private theorem middle_stabilizer (w : Equiv.Perm (Fin (Multiset.card μ)))
    (hw : w • loading = loading) : w = 1 ∨ w = swapBlacks := by
  have hc : ∀ f : Equiv.Perm (Fin (Multiset.card μ)), f • loading = loading →
      f = 1 ∨ f = swapBlacks := by decide +kernel
  exact hc w hw

private def blackPolynomial : MvPolynomial (Fin 2) k →ₐ[k] A :=
  ((TensorProductAlgebra.mk q₀ wt₂ blackWeight).comp ((orderProjection q₀ wt₂ blackWeight).comp
    (StendhalAlgebraAllOrders.ofKLR k q₀ wt₂ blackWeight))).comp
      (KLRAlgebra.pol.comp (MvPolynomial.rename blackPosition))

private theorem blackPolynomial_X (r : Fin 2) :
    blackPolynomial k (MvPolynomial.X r) = π (KLRAlgebra.x (blackPosition r)) := by
  change π (KLRAlgebra.pol (MvPolynomial.rename blackPosition (MvPolynomial.X r))) = _
  rw [MvPolynomial.rename_X, KLRAlgebra.pol_X]

private theorem dotPolynomial_generator (p : MvPolynomial (Fin 2) k) :
    polynomialDotEnd k p g = blackPolynomial k p • g := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
    change c • (g : S) = _
    rw [algebraMap_smul]
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, add_smul, hp, hq]
  | mul_X p r hp =>
    have hx : dotEnd k r g = blackPolynomial k (MvPolynomial.X r) • g := by
      rw [blackPolynomial_X]
      fin_cases r
      · exact dotEnd_zero_gen k
      · exact dotEnd_one_gen k
    rw [map_mul, Module.End.mul_apply, polynomialDotEnd_X, hx, map_smul, hp, ← mul_smul,
      mul_comm p (MvPolynomial.X r), map_mul]

private theorem dotMonomial_lift (d : Fin (Multiset.card μ) →₀ ℕ)
    (hd : ∀ j ∈ d.support, (loading.lbl j).isLeft) :
    ∃ p : MvPolynomial (Fin 2) k,
      MvPolynomial.rename blackPosition p = MvPolynomial.monomial d 1 := by
  let a := blackPosition 0
  let b := blackPosition 1
  have hs (j : Fin (Multiset.card μ)) (hj : j ∈ d.support) :
      j = a ∨ j = b := by
    have hshape : ∀ j : Fin (Multiset.card μ), (loading.lbl j).isLeft →
        j = blackPosition 0 ∨ j = blackPosition 1 := by decide +kernel
    exact hshape j (hd j hj)
  have hrepr : d = Finsupp.single a (d a) + Finsupp.single b (d b) := by
    ext j
    rw [Finsupp.add_apply]
    by_cases ha : j = a
    · subst j
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : a ≠ b), add_zero]
    by_cases hb : j = b
    · subst j
      rw [Finsupp.single_eq_of_ne ha, Finsupp.single_eq_same, zero_add]
    have hz : d j = 0 := Finsupp.notMem_support_iff.mp (fun h => (hs j h).elim ha hb)
    rw [Finsupp.single_eq_of_ne ha, Finsupp.single_eq_of_ne hb, zero_add, hz]
  refine ⟨MvPolynomial.X 0 ^ (d a) * MvPolynomial.X 1 ^ (d b), ?_⟩
  rw [map_mul, map_pow, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_X,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, one_mul]
  exact congrArg (fun s => MvPolynomial.monomial s 1) hrepr.symm

/-- Evaluate a two-variable dot polynomial on the middle generator. -/
def dotPolynomialEval : MvPolynomial (Fin 2) k →ₗ[k] S where
  toFun p := polynomialDotEnd k p g
  map_add' p q := by rw [map_add, LinearMap.add_apply]
  map_smul' c p := by
    rw [map_smul, LinearMap.smul_apply]
    rfl

private theorem projectTerm
    (b : {b // IsStendhalTerm (ν := blackWeight) (ℓ := 2) wordChoice b}) :
    tensorProductTerm wordChoice_spec q₀ wt₂ b = π (KLRAlgebra.stdElt wordChoice b.1) := by
  apply congrArg (TensorProductAlgebra.mk q₀ wt₂ blackWeight)
  apply Subtype.ext
  exact ((Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp
    (stendhalTerm q₀ wt₂ (fun w => (wordChoice_spec w).2) b).2).2.symm

local notation "E" => seqIdem q₀ wt₂ loading loading_ordered

private theorem blackPolynomial_fixed (p : MvPolynomial (Fin 2) k) :
    E • (blackPolynomial k p • g) = blackPolynomial k p • g := by
  have hc : E * blackPolynomial k p = blackPolynomial k p * E := by
    change E * π (KLRAlgebra.pol (MvPolynomial.rename blackPosition p)) =
      π (KLRAlgebra.pol (MvPolynomial.rename blackPosition p)) * E
    rw [← proj_loading k loading loading_ordered, ← projected_mul, ← projected_mul,
      (KLRAlgebra.e_commute_pol _ _).eq]
  rw [← mul_smul, hc, mul_smul, gen_fixed]

theorem dotPolynomialEval_fixed (p : MvPolynomial (Fin 2) k) :
    E • dotPolynomialEval k p = dotPolynomialEval k p := by
  change E • polynomialDotEnd k p g = polynomialDotEnd k p g
  rw [dotPolynomial_generator]
  exact blackPolynomial_fixed k p

private theorem middle_fixed_in_range (a : A) :
    (E * a) • g ∈ LinearMap.range (dotPolynomialEval k) := by
  classical
  let W := LinearMap.range (dotPolynomialEval k)
  have ha : a ∈ Submodule.span k (Set.range (tensorProductTerm wordChoice_spec q₀ wt₂)) := by
    rw [span_tensorProductTerm wordChoice_spec q₀ wt₂]
    trivial
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    let d := tensorProductTerm wordChoice_spec q₀ wt₂ b
    have hL : E * d = if b.1.2.1 • b.1.1 = loading then d else 0 := by
      unfold d tensorProductTerm
      rw [← map_mul, e_mul_stendhalTerm]
      split_ifs <;> simp only [map_zero]
    have hR : d * E = if b.1.1 = loading then d else 0 := by
      unfold d tensorProductTerm
      rw [← map_mul, stendhalTerm_mul_e]
      split_ifs <;> simp only [map_zero]
    change (E * d) • g ∈ W
    rw [hL]
    split_ifs with ht
    · have hbg : d • g = (d * E) • g := by rw [mul_smul, gen_fixed]
      rw [hbg, hR]
      split_ifs with hb
      · have hw : b.1.2.1 • loading = loading := hb ▸ ht
        have hl (j : Fin (Multiset.card μ)) (hj : j ∈ b.1.2.2.support) : (loading.lbl j).isLeft := by
          have h := b.2.2.2.1 j hj
          change (b.1.1.lbl j).isLeft = true at h
          rwa [hb] at h
        obtain ⟨p, hp⟩ := dotMonomial_lift k b.1.2.2 hl
        have hpoly : π (KLRAlgebra.pol (MvPolynomial.monomial b.1.2.2 1)) = blackPolynomial k p := by
          change π (KLRAlgebra.pol (MvPolynomial.monomial b.1.2.2 1)) =
            π (KLRAlgebra.pol (MvPolynomial.rename blackPosition p))
          rw [hp]
        change d • g ∈ W
        rw [show d = _ from projectTerm k b, KLRAlgebra.stdElt,
          projected_mul, projected_mul, hpoly, hb, proj_loading k _ loading_ordered,
          mul_smul, gen_fixed, mul_smul]
        rcases middle_stabilizer _ hw with h | h
        · rw [h, wordChoice_one, KLRAlgebra.ψw, List.map_nil, List.prod_nil,
            show π (1 : KLRAlgebra k (stendhalQ q₀ wt₂) μ) = 1 from
              by simp only [tensorOfKLR, map_one], one_smul]
          exact ⟨p, dotPolynomial_generator k p⟩
        · rw [h, wordChoice, ite_eq_left rfl, KLRAlgebra.ψw]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            projected_mul, mul_smul]
          rw [higherCrossing_kills_middle_fixed k _ (blackPolynomial_fixed k p), smul_zero, smul_zero]
          exact W.zero_mem
      · rw [zero_smul]
        exact W.zero_mem
    · rw [zero_smul]
      exact W.zero_mem
  | zero => rw [mul_zero, zero_smul]; exact W.zero_mem
  | add x y _ _ hx hy => simpa only [mul_add, add_smul] using W.add_mem hx hy
  | smul c x _ hx =>
    simpa only [mul_smul_comm, smul_assoc] using W.smul_mem c hx

/-- The polynomial dot quotient surjects onto the endomorphism algebra
of the actual middle standard. In the PBW expansion, the only possible
nonidentity permutation exchanges the black strands through the higher
cut and hence contributes zero. -/
theorem middleDotQuotientAction_surjective : Function.Surjective (middleDotQuotientAction k) := by
  intro f
  obtain ⟨a, ha⟩ := leftStandard_exists_smul_unit
    (Q := q₀) (Λ := wt₂) loading loading_ordered (f g)
  have h : (E * a) • g = f g := by
    rw [mul_smul, ← ha, ← f.map_smul, gen_fixed]
  obtain ⟨p, hp⟩ := middle_fixed_in_range k a
  refine ⟨Ideal.Quotient.mk _ p, leftStandard_hom_ext loading loading_ordered ?_⟩
  change polynomialDotEnd k p g = f g
  exact hp.trans h

/-- The loading with both black strands to the right of the second red. -/
def terminalLoading : Seq μ :=
  Seq.ofList [.inr 0, .inr 1, .inl (), .inl ()] (by decide)

theorem terminalLoading_ordered : IsRedOrdered terminalLoading := by
  unfold IsRedOrdered
  decide +kernel

local notation "n" => Multiset.card μ

private abbrev terminalShuffleFirst : Equiv.Perm (Fin n) := wordProd n [1]
private abbrev terminalShuffleSecond : Equiv.Perm (Fin n) := wordProd n [2, 1]

theorem terminal_transporters (w : Equiv.Perm (Fin n)) (hw : w • loading = terminalLoading) :
    w = terminalShuffleFirst ∨ w = terminalShuffleSecond := by
  have h : ∀ f : Equiv.Perm (Fin n), f • loading = terminalLoading →
      f = terminalShuffleFirst ∨ f = terminalShuffleSecond := by decide +kernel
  exact h w hw


private def terminalWordChoice (w : Equiv.Perm (Fin n)) : List ℕ :=
  if w = terminalShuffleFirst then [1]
  else if w = terminalShuffleSecond then [2, 1]
  else canWord n w

private theorem terminalWordChoice_spec (w : Equiv.Perm (Fin n)) :
    IsReduced n (terminalWordChoice w) ∧ wordProd _ (terminalWordChoice w) = w := by
  unfold terminalWordChoice
  split_ifs with h₁ h₂
  · subst w
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      decide
    · rw [length_eq_invCount]
      decide +kernel
  · subst w
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl <;> decide
    · rw [length_eq_invCount]
      decide +kernel
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

/-- The two terminal shuffle words applied to separated bottom polynomials. -/
def terminalPolynomialEval (p : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k) : S :=
  π (KLRAlgebra.ψw [1]) • dotPolynomialEval k p.1 +
    π (KLRAlgebra.ψw [2, 1]) • dotPolynomialEval k p.2

private def terminalPolynomialEvalLinear :
    (MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k) →ₗ[k] S where
  toFun := terminalPolynomialEval k
  map_add' x y := by
    simp only [terminalPolynomialEval, Prod.fst_add, Prod.snd_add, map_add, smul_add]
    abel
  map_smul' c z := by
    simp only [terminalPolynomialEval, Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
      smul_comm (π (KLRAlgebra.ψw [1])) c, smul_comm (π (KLRAlgebra.ψw [2, 1])) c,
      RingHom.id_apply]

local notation "Et" => seqIdem q₀ wt₂ terminalLoading terminalLoading_ordered

private theorem terminal_fixed_in_range (a : A) :
    (Et * a) • g ∈ LinearMap.range (terminalPolynomialEvalLinear k) := by
  classical
  let W := LinearMap.range (terminalPolynomialEvalLinear k)
  have ha : a ∈ Submodule.span k (Set.range (tensorProductTerm terminalWordChoice_spec q₀ wt₂)) := by
    rw [span_tensorProductTerm terminalWordChoice_spec q₀ wt₂]
    trivial
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    let d := tensorProductTerm terminalWordChoice_spec q₀ wt₂ b
    have hL : Et * d = if b.1.2.1 • b.1.1 = terminalLoading then d else 0 := by
      unfold d tensorProductTerm
      rw [← map_mul, e_mul_stendhalTerm]
      split_ifs <;> simp only [map_zero]
    have hR : d * E = if b.1.1 = loading then d else 0 := by
      unfold d tensorProductTerm
      rw [← map_mul, stendhalTerm_mul_e]
      split_ifs <;> simp only [map_zero]
    change (Et * d) • g ∈ W
    rw [hL]
    split_ifs with ht
    · have hbg : d • g = (d * E) • g := by rw [mul_smul, gen_fixed]
      rw [hbg, hR]
      split_ifs with hb
      · have hw : b.1.2.1 • loading = terminalLoading := hb ▸ ht
        have hl (j : Fin (Multiset.card μ)) (hj : j ∈ b.1.2.2.support) : (loading.lbl j).isLeft := by
          have h := b.2.2.2.1 j hj
          change (b.1.1.lbl j).isLeft = true at h
          rwa [hb] at h
        obtain ⟨p, hp⟩ := dotMonomial_lift k b.1.2.2 hl
        have hpoly : π (KLRAlgebra.pol (MvPolynomial.monomial b.1.2.2 1)) = blackPolynomial k p := by
          change π (KLRAlgebra.pol (MvPolynomial.monomial b.1.2.2 1)) =
            π (KLRAlgebra.pol (MvPolynomial.rename blackPosition p))
          rw [hp]
        change d • g ∈ W
        have hd : d = π (KLRAlgebra.stdElt terminalWordChoice b.1) := by
          apply congrArg (TensorProductAlgebra.mk q₀ wt₂ blackWeight)
          apply Subtype.ext
          exact ((Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp
            (stendhalTerm q₀ wt₂ (fun w => (terminalWordChoice_spec w).2) b).2).2.symm
        rw [hd, KLRAlgebra.stdElt,
          projected_mul, projected_mul, hpoly, hb, proj_loading k _ loading_ordered,
          mul_smul, gen_fixed, mul_smul]
        rcases terminal_transporters _ hw with h | h
        · rw [h, terminalWordChoice, ite_eq_left rfl, ← dotPolynomial_generator]
          refine ⟨(p, 0), ?_⟩
          change terminalPolynomialEval k (_, _) = π (KLRAlgebra.ψw [1]) • dotPolynomialEval k p
          simp only [terminalPolynomialEval, map_zero, smul_zero, add_zero]
        · rw [h, terminalWordChoice, ite_eq_right (by decide +kernel), ite_eq_left rfl,
            ← dotPolynomial_generator]
          refine ⟨(0, p), ?_⟩
          change terminalPolynomialEval k (_, _) = π (KLRAlgebra.ψw [2, 1]) • dotPolynomialEval k p
          simp only [terminalPolynomialEval, map_zero, smul_zero, zero_add]
      · rw [zero_smul]
        exact W.zero_mem
    · rw [zero_smul]
      exact W.zero_mem
  | zero => rw [mul_zero, zero_smul]; exact W.zero_mem
  | add x y _ _ hx hy => simpa only [mul_add, add_smul] using W.add_mem hx hy
  | smul c x _ hx =>
    simpa only [mul_smul_comm, smul_assoc] using W.smul_mem c hx


/-- At the terminal loading the middle standard is spanned by the two
shuffle diagrams with arbitrary polynomial dots at the source. -/
theorem terminalPolynomialEval_surjective_on_fixed (z : S) (hz : Et • z = z) :
    ∃ p, terminalPolynomialEval k p = z := by
  obtain ⟨a, ha⟩ := leftStandard_exists_smul_unit
    (Q := q₀) (Λ := wt₂) loading loading_ordered z
  obtain ⟨p, hp⟩ := terminal_fixed_in_range k a
  exact ⟨p, hp.trans (by rw [mul_smul, ← ha, hz])⟩

end Spanning

end Categorification.Stendhal.LabelTwo
