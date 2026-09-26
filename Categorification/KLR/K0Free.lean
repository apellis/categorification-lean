/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.Algebra.Graded.G0Basis
import Categorification.KLR.Gamma
import Categorification.KLR.Simple
import Categorification.KLR.GradedBasis

/-!
# `K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module (KL I, §2.5)

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, TeX lines 1513–1556: over a field `k`, "each simple
`S_b` has a projective cover `P_b` … `K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module with the basis
`{[P_b]}_{b ∈ B(ν)}`", where `B(ν)` indexes the simple graded modules up to isomorphism and grading
shift.

We apply the general graded Krull–Schmidt theory (`Categorification.Algebra.Graded.KrullSchmidt`)
to `A = R(ν)`, which has finite-dimensional graded pieces vanishing in sufficiently negative
degrees when all dots have positive degree (`GradingDatum.hasGdim_grade'`).

## Main results

* `GradingDatum.k0Basis` : a `ℤ[q, q⁻¹]`-basis of `K₀(R(ν))`, indexed by the indecomposable
  graded projective `R(ν)`-modules up to isomorphism and shift, `[P] ↦ [P]`; hence
  `GradingDatum.k0_free` and `GradingDatum.K0R_free` (`K₀(R) = ⨁_ν K₀(R(ν))` is free).
* `GradingDatum.finite_and_card_indecClass_le` : there are finitely many such classes, at most
  `(m!)² = dim_k R'(ν)` (via their graded simple tops and KL I, Proposition 2.12).
* `GradingDatum.g0Basis`, `GradingDatum.g0_free` : `G₀(R(ν))` is free with basis the classes of
  the graded simple tops `S_b` (finite-dimensional by Proposition 2.12,
  `GradingDatum.finiteDimensional_top`), and `GradingDatum.pairing_k0Basis_g0Basis` :
  `([P_b], [S_{b'}]) = δ_{b b'} dim_k END(S_b)_0`.
* `KLGamma.qToV_injective` : `ℤ[q, q⁻¹] → ℚ(v)`, `q ↦ v⁻¹`, is injective.
* `KLGamma.toK0Q_injective` : **`K₀(R) → ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` is injective** for the rings of
  KL I over a field `k`. This discharges the hypothesis `hinj` of `KLGamma.gammaInt`
  (`KLGamma.gammaInt'`).
-/

noncomputable section

namespace Categorification.KLR

open Graded MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k]

/-! ### General KLR algebras -/

namespace GradingDatum

variable {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)
  (ν : Multiset I)

include hPQ hP hG

/-- **KL I, §2.5**: a `ℤ[q, q⁻¹]`-basis of `K₀(R(ν))`, indexed by the indecomposable finitely
generated graded projective `R(ν)`-modules up to isomorphism and grading shift. -/
def k0Basis :
    Basis (GProj.IndecClass (G.grade ν)) (LaurentPolynomial ℤ) (K0 (G.grade ν)) :=
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  K0.indecBasis (G.grade ν)

theorem k0Basis_apply (b : GProj.IndecClass (G.grade ν)) :
    G.k0Basis hPQ hP hG ν b = K0.of b.rep := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  exact K0.indecBasis_apply b

/-- **KL I, §2.5: `K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module.** -/
theorem k0_free : Module.Free (LaurentPolynomial ℤ) (K0 (G.grade ν)) :=
  Module.Free.of_basis (G.k0Basis hPQ hP hG ν)

/-- `K₀(R) = ⨁_ν K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module. -/
theorem K0R_free : Module.Free (LaurentPolynomial ℤ) G.K0R := by
  haveI : ∀ ν, Module.Free (LaurentPolynomial ℤ) (G.K0fam ν) := fun ν => G.k0_free hPQ hP hG ν
  infer_instance

omit hPQ hP hG in
/-- A graded simple top of the representative of an indecomposable class. -/
theorem exists_top (b : GProj.IndecClass (G.grade ν)) :
    ∃ (S : GMod (G.grade ν)) (f : b.rep.carrier →ₗ[KLRAlgebra k Q ν] S),
      IsGradedSimple (G.grade ν) S.grading ∧ PreservesGrading b.rep.grading S.grading f ∧
        f ≠ 0 := by
  haveI := (GProj.IndecClass.isIndec_rep b).nontrivial
  obtain ⟨S, f, hS, hf, hf0, -⟩ := b.rep.exists_isGradedSimple_quotient
  exact ⟨S, f, hS, hf, hf0⟩

/-- **KL I, §2.5: finitely many indecomposable projectives.** Up to isomorphism and grading
shift, there are at most `(m!)² = dim_k R'(ν)` indecomposable finitely generated graded
projective `R(ν)`-modules: their graded simple tops are pairwise non-isomorphic up to shift
(uniqueness of projective covers), and there are at most `(m!)²` simples (KL I, Proposition 2.12).
-/
theorem finite_and_card_indecClass_le :
    Finite (GProj.IndecClass (G.grade ν)) ∧
      Nat.card (GProj.IndecClass (G.grade ν)) ≤ (Multiset.card ν).factorial ^ 2 := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  choose S f hS hf hf0 using G.exists_top ν
  refine KLRAlgebra.card_le_of_isGradedSimple hPQ hP G hG (fun b => (S b).carrier)
    (fun b => (S b).grading) hS fun b b' c ⟨e⟩ => ?_
  -- `rep b → S b ≅ (S b'){c}` and `rep b' {c} → (S b'){c}` are nonzero
  have hSc : IsGradedSimple (G.grade ν) (Graded.shift (S b').grading c) := (hS b').shift c
  have hg : PreservesGrading b.rep.grading (Graded.shift (S b').grading c)
      (e.toLinearEquiv.toLinearMap ∘ₗ f b) := fun _ _ hx => e.map_mem (hf b hx)
  have hg0 : e.toLinearEquiv.toLinearMap ∘ₗ f b ≠ 0 := by
    intro h
    apply hf0 b
    ext x
    have := LinearMap.congr_fun h x
    exact e.toLinearEquiv.injective (this.trans (map_zero _).symm)
  obtain ⟨iso⟩ := (GProj.IndecClass.isIndec_rep b).nonempty_iso
    ((GProj.IndecClass.isIndec_rep b').shift c) hSc hg hg0
    (f' := f b') (fun j _ hx => hf b' (d := j - c) hx) (hf0 b')
  exact GProj.IndecClass.eq_of_iso_rep iso

/-- **KL I, Proposition 2.12**: the graded simple tops `S_b` of the indecomposable projectives
are finite-dimensional. -/
theorem finiteDimensional_top (b : GProj.IndecClass (G.grade ν)) : FiniteDimensional k b.top :=
  KLRAlgebra.finiteDimensional_of_isGradedSimple hPQ hP G hG b.top.grading
    (GProj.IndecClass.isGradedSimple_top b)

/-- **KL I, §2.5**: a `ℤ[q, q⁻¹]`-basis `[S_b]` of `G₀(R(ν))`, indexed by the same set as
`k0Basis` (`S_b` is the graded simple top of `P_b`). -/
def g0Basis :
    Basis (GProj.IndecClass (G.grade ν)) (LaurentPolynomial ℤ) (G0 (G.grade ν)) :=
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  G0.topBasis (G.finiteDimensional_top hPQ hP hG ν)

/-- **KL I, §2.5: `G₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module.** -/
theorem g0_free : Module.Free (LaurentPolynomial ℤ) (G0 (G.grade ν)) :=
  Module.Free.of_basis (G.g0Basis hPQ hP hG ν)

open scoped Classical in
/-- **KL I, §2.5: the bases `[P_b]` of `K₀(R(ν))` and `[S_b]` of `G₀(R(ν))` are dual** under
`([P], [M]) = gdim HOM(P, M)`, up to the dimensions of the degree-zero endomorphism algebras
`END(S_b)_0` (which are `1` when `End(S_b) = k`). -/
theorem pairing_k0Basis_g0Basis (b b' : GProj.IndecClass (G.grade ν)) :
    pairing (G.k0Basis hPQ hP hG ν b) (G.g0Basis hPQ hP hG ν b') =
      if b = b' then HahnSeries.single 0 (Module.finrank k (endZero (KLRAlgebra k Q ν)
        b.top.grading) : ℤ) else 0 := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  exact pairing_indecBasis_topBasis _ b b'

end GradingDatum

/-! ### The rings of KL I and the injectivity of `K₀(R) → K₀(R)_{ℚ(v)}` -/

namespace KLGamma

open LaurentPolynomial Polynomial QuantumGroup

variable (k) (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- **`K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module** for the rings `R(ν)` of KL I over a field. -/
theorem k0_free (ν : Multiset I) :
    Module.Free (LaurentPolynomial ℤ) (K0 ((klGradingDatum k Γ).grade ν)) :=
  (klGradingDatum k Γ).k0_free (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν

/-- **`K₀(R) = ⨁_ν K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module** for the rings of KL I over a
field. -/
theorem K0R_free : Module.Free (LaurentPolynomial ℤ) (klGradingDatum k Γ).K0R :=
  (klGradingDatum k Γ).K0R_free (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos

/-- `v⁻¹` is transcendental over `ℤ` in `ℚ(v)`. -/
theorem transcendental_vQ_inv : Transcendental ℤ ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  have hX : Transcendental ℚ (RatFunc.X : RatFunc ℚ) := by
    rw [← RatFunc.algebraMap_X]
    exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective ℚ)).2
      (Polynomial.transcendental_X ℚ)
  have hXinv : Transcendental ℚ (RatFunc.X⁻¹ : RatFunc ℚ) := fun h =>
    hX (IsAlgebraic.inv_iff.1 h)
  haveI : @IsScalarTower ℤ ℚ (RatFunc ℚ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun n => by
      rw [eq_intCast (algebraMap ℤ ℚ) n, map_intCast, eq_intCast (algebraMap ℤ (RatFunc ℚ)) n]
  exact hXinv.restrictScalars (algebraMap ℤ ℚ).injective_int

/-- The specialisation `q ↦ v⁻¹`, `ℤ[q, q⁻¹] → ℚ(v)`, is injective. -/
theorem qToV_injective : Function.Injective qToV := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hcomp : qToV.comp (Polynomial.toLaurent (R := ℤ)) =
      (Polynomial.aeval ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Function.comp_apply, Polynomial.toLaurent_X, Polynomial.aeval_X]
      rw [qToV_T]
      simp
  have hf0 : Polynomial.aeval ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) f = 0 := by
    have := congrArg (fun g => g f) hcomp
    simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Function.comp_apply] at this
    rw [← this, hf, map_mul, hp, zero_mul]
  have hf' : f = 0 := (transcendental_iff_injective.1 transcendental_vQ_inv)
    (hf0.trans (map_zero _).symm)
  have hpT : p * T n = 0 := by rw [← hf, hf', map_zero]
  have : p * T n * T (-n) = 0 := by rw [hpT, zero_mul]
  rwa [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one] at this

attribute [local instance] qToVAlgebra in
/-- **The map `K₀(R) → K₀(R)_{ℚ(v)} = ℚ(v) ⊗_{ℤ[q, q⁻¹]} K₀(R)` is injective** for the rings of
KL I over a field `k` (`K₀(R)` is free, hence flat, over `ℤ[q, q⁻¹]`, and `q ↦ v⁻¹` is
injective). This is the hypothesis `hinj` of `KLGamma.gammaInt`. -/
theorem toK0Q_injective : Function.Injective (toK0Q k Γ) := by
  haveI := K0R_free k Γ
  exact Algebra.TensorProduct.includeRight_injective (A := RatFunc ℚ) (qToV_injective)

/-- The integral homomorphism `γ : _𝒜 f → K₀(R)` of KL I, Theorem 1.1, over a field `k`,
under the quantum Gabber–Kac hypothesis only (the injectivity hypothesis of `gammaInt` is
discharged by `toK0Q_injective`). -/
def gammaInt' (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    KL.Af Γ →+* (klGradingDatum k Γ).K0R :=
  gammaInt k Γ hGK (toK0Q_injective k Γ)

end KLGamma

end Categorification.KLR
