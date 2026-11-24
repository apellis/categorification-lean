/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardEnd
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
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

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν

variable (k : Type) [Field k]

/-- The two red strands each have coroot pairing two. -/
def weights (_ : Fin 2) : Unit →₀ ℕ := Finsupp.single () 2

/-- The one-colour KLR polynomial for type A₁. -/
def parameter (_ _ : Unit) : MvPolynomial (Fin 2) k := 0

local notation "q₀" => parameter k
local notation "wt₂" => weights
local notation "A" => TensorProductAlgebra k q₀ wt₂ ν

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
local notation "π" => tensorOfKLR q₀ wt₂ ν

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
  apply congrArg (TensorProductAlgebra.mk q₀ wt₂ ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem proj_cutZero : π (e (cut 0)) = 0 := by
  rw [proj_loading k _ cutZeroOrdered]
  change (StendhalAlgebra.violatedIdeal k q₀ wt₂ ν).ringCon.mk' _ = 0
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

private theorem dotEnd_zero_gen :
    dotEnd k 0 g = leftMiddleDot k • g :=
  liftMiddleDot_generator k _ (projected_dot_commutes_idem k ⟨1, by decide⟩)

private theorem dotEnd_one_gen :
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

end Categorification.Stendhal.LabelTwo
