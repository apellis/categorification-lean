/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstInjective
import Categorification.KLR.CyclotomicAction.FrobeniusSymmetric
import Categorification.Algebra.CornerSelfDual

set_option backward.isDefEq.respectTransparency false

/-!
# The symmetric trace on the red-first corner and the self-duality of `y T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. The pairing there is built from the Frobenius trace of the red-first corner
`e⁰ T^λ e⁰ ≅ R^{∑ λ_r}` (Proposition 5.28), and it uses that this trace is symmetric,
`tr(ȧ b y) = tr(y ȧ b)` (Theorem 3.18 with Remark 3.19). Transporting the symmetric trace of
`R^{∑ λ_r}` (`IsRouquierQ.cyclotomic_frobenius_symmetric`, for `t_ij = t_ji`) gives a linear
form `τ` on `T^λ` that is symmetric and nondegenerate on both sides on `e⁰ T^λ e⁰`
(`exists_redFirstTrace_symmetric`).

At the standard Khovanov–Lauda scalars, `T^λ` acts faithfully on `P⁰ = T^λ e⁰` and the
horizontal reflection exchanges `e⁰ T^λ` and `T^λ e⁰`, so `τ` is nondegenerate between
`e⁰ T^λ` and `T^λ e⁰` (`redFirstIdem_symmetricPairing`). For every `y ∈ e⁰ T^λ e⁰` the
pairing `⟨y a, b y⟩ = τ(y a b)` then identifies `y T^λ` with the dual of `T^λ y`
(`redFirstSelfDualEquiv`, from `CornerSelfDual.rangeMulLeftDualEquiv`).

## Main results

* `exists_redFirstTrace_symmetric`: the symmetric trace on the red-first corner.
* `exists_mul_ne_zero_of_redFirstIdem_mul`: every nonzero `a ∈ e⁰ T^λ` has `a c ≠ 0` for some
  `c ∈ T^λ e⁰`.
* `redFirstIdem_symmetricPairing`: the trace is symmetric on `e⁰ T^λ e⁰` and nondegenerate
  between `e⁰ T^λ` and `T^λ e⁰`.
* `redFirstSelfDualEquiv`: `y T^λ ≃ Hom_k(T^λ y, k)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KL3.Diagram

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section General

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) {D : QuantumGroup.CartanDatum I}
  (hQ : IsRouquierQ D Q) (ν : Multiset I)

include hQ in
/-- **The symmetric trace on the red-first corner** (Webster, arXiv:1309.3796v3, Theorem 3.18
with Remark 3.19, transported by Proposition 5.28): when `t_ij = t_ji` for all `i ≠ j`, a
`k`-linear form `τ` on `T^λ`, factoring through `x ↦ e⁰ x e⁰`, that is nondegenerate on both
sides and symmetric on `e⁰ T^λ e⁰`. -/
theorem exists_redFirstTrace_symmetric
    (hsym : ∀ i j, i ≠ j → extremalCoeff D Q i j = extremalCoeff D Q j i)
    {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) :
    ∃ τ : TensorProductAlgebra k Q Λ ν →ₗ[k] k,
      (∀ z, redFirstIdem Q Λ ν * z = z → z * redFirstIdem Q Λ ν = z → z ≠ 0 →
        ∃ y, redFirstIdem Q Λ ν * y = y ∧ y * redFirstIdem Q Λ ν = y ∧ τ (z * y) ≠ 0) ∧
      (∀ y, redFirstIdem Q Λ ν * y = y → y * redFirstIdem Q Λ ν = y → y ≠ 0 →
        ∃ z, redFirstIdem Q Λ ν * z = z ∧ z * redFirstIdem Q Λ ν = z ∧ τ (z * y) ≠ 0) ∧
      (∀ a b, redFirstIdem Q Λ ν * a * redFirstIdem Q Λ ν = a →
        redFirstIdem Q Λ ν * b * redFirstIdem Q Λ ν = b → τ (a * b) = τ (b * a)) := by
  set e := redFirstIdem Q Λ ν
  have he : IsIdempotentElem e := isIdempotentElem_redFirstIdem Q Λ ν
  obtain ⟨tr, ⟨htrl, htrr⟩, htrs⟩ := IsRouquierQ.cyclotomic_frobenius_symmetric hQ hsym
    (coordinateWeightDatum D) (fun i => ((∑ r, Λ r) i : ℤ))
    (a := fun i => Polynomial.X ^ (∑ r, Λ r) i)
    (fun _ => Polynomial.monic_X_pow _) (fun i => by simp [coordinateWeightDatum]) ν
  let φ := redFirstCornerEquiv Q hQ ν Λ
  have hmem : ∀ x : TensorProductAlgebra k Q Λ ν, e * (e * x * e) * e = e * x * e := fun x => by
    rw [← mul_assoc, ← mul_assoc, he.eq, mul_assoc, he.eq]
  let cut : TensorProductAlgebra k Q Λ ν →ₗ[k] he.Corner :=
    { toFun := fun x => KLR.Corner.mk (idem := he) (e * x * e) (hmem x)
      map_add' := fun x y => KLR.Corner.ext (by simp [mul_add, add_mul])
      map_smul' := fun d x => Subtype.ext (by
        change e * (d • x) * e = d • (e * x * e)
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]) }
  let φl : he.Corner →ₗ[k] CycKLR k Q (fun i => Polynomial.X ^ (∑ r, Λ r) i) ν :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := redFirstCornerEquiv_smul Q hQ ν Λ }
  have hcorner : ∀ a, e * a = a → a * e = a → e * a * e = a := fun a h1 h2 => by rw [h1, h2]
  refine ⟨tr ∘ₗ φl ∘ₗ cut, fun z hz1 hz2 hz0 => ?_, fun y hy1 hy2 hy0 => ?_,
    fun a b ha hb => ?_⟩
  · set zc : he.Corner := KLR.Corner.mk z (by rw [hcorner z hz1 hz2])
    have hφz : φ zc ≠ 0 := fun h0 => hz0 (by
      have : zc = 0 := φ.injective (h0.trans (map_zero φ).symm)
      exact congrArg KLR.Corner.val this)
    obtain ⟨y', hy'⟩ := htrl _ hφz
    set yc := φ.symm y'
    refine ⟨yc.val, KLR.Corner.E_mul_val yc, KLR.Corner.val_mul_E yc, ?_⟩
    have hc : cut (z * yc.val) = zc * yc := KLR.Corner.ext (by
      change e * (z * yc.val) * e = z * yc.val
      rw [← mul_assoc, hz1, mul_assoc, KLR.Corner.val_mul_E])
    change tr (φ (cut (z * yc.val))) ≠ 0
    rw [hc, map_mul, RingEquiv.apply_symm_apply]
    exact hy'
  · set yc : he.Corner := KLR.Corner.mk y (by rw [hcorner y hy1 hy2])
    have hφy : φ yc ≠ 0 := fun h0 => hy0 (by
      have : yc = 0 := φ.injective (h0.trans (map_zero φ).symm)
      exact congrArg KLR.Corner.val this)
    obtain ⟨z', hz'⟩ := htrr _ hφy
    set zc := φ.symm z'
    refine ⟨zc.val, KLR.Corner.E_mul_val zc, KLR.Corner.val_mul_E zc, ?_⟩
    have hc : cut (zc.val * y) = zc * yc := KLR.Corner.ext (by
      change e * (zc.val * y) * e = zc.val * y
      rw [← mul_assoc, KLR.Corner.E_mul_val, mul_assoc, hy2])
    change tr (φ (cut (zc.val * y))) ≠ 0
    rw [hc, map_mul, RingEquiv.apply_symm_apply]
    exact hz'
  · have h1a : e * a = a := by rw [← ha, ← mul_assoc, ← mul_assoc, he.eq]
    have h2a : a * e = a := by rw [← ha, mul_assoc, he.eq]
    have h1b : e * b = b := by rw [← hb, ← mul_assoc, ← mul_assoc, he.eq]
    have h2b : b * e = b := by rw [← hb, mul_assoc, he.eq]
    set ac : he.Corner := KLR.Corner.mk a (by rw [ha])
    set bc : he.Corner := KLR.Corner.mk b (by rw [hb])
    have hab : cut (a * b) = ac * bc := KLR.Corner.ext (by
      change e * (a * b) * e = a * b
      rw [← mul_assoc, h1a, mul_assoc, h2b])
    have hba : cut (b * a) = bc * ac := KLR.Corner.ext (by
      change e * (b * a) * e = b * a
      rw [← mul_assoc, h1b, mul_assoc, h2a])
    change tr (φ (cut (a * b))) = tr (φ (cut (b * a)))
    rw [hab, hba, map_mul φ, map_mul φ]
    exact htrs _ _

end General

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

include hR hQs in
/-- `T^λ` acts faithfully on `P⁰` from `e⁰ T^λ` (Webster, arXiv:1309.3796v2, Lemma 5.23): every
nonzero `a ∈ e⁰ T^λ` has `c ∈ T^λ e⁰` with `a c ≠ 0`. -/
theorem exists_mul_ne_zero_of_redFirstIdem_mul {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) (a : TensorProductAlgebra k QL Λ ν) (ha0 : a ≠ 0) :
    ∃ c, c * redFirstIdem QL Λ ν = c ∧ a * c ≠ 0 := by
  have hcomp := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).complete
  obtain ⟨s, hs⟩ : ∃ s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ + 1) ν,
      a * TensorProductAlgebra.boundaryIdem QL Λ ν s ≠ 0 := by
    by_contra! h
    apply ha0
    rw [← mul_one a, ← hcomp, Finset.mul_sum]
    exact Finset.sum_eq_zero fun s _ => h s
  have hidem := (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem
    (k := k) QL Λ ν).idem s
  set es := TensorProductAlgebra.boundaryIdem QL Λ ν s
  obtain ⟨c, hc, hac⟩ := exists_mul_redFirstIdem_ne_zero hR hQs (baseCrossing_std hR hQs) Λ ν
    s.1 s.2 (a * es) (by rw [mul_assoc]; exact congrArg _ hidem.eq) hs
  exact ⟨es * c, by rw [mul_assoc, hc], by rwa [← mul_assoc]⟩

include hR hQs in
/-- **The symmetric pairing on `P⁰`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14, at
the standard Khovanov–Lauda scalars): a `k`-linear form `τ` on `T^λ`, symmetric on
`e⁰ T^λ e⁰`, such that every nonzero `a ∈ e⁰ T^λ` has `b ∈ T^λ e⁰` with `τ(a b) ≠ 0` and every
nonzero `b ∈ T^λ e⁰` has `a ∈ e⁰ T^λ` with `τ(a b) ≠ 0`. -/
theorem redFirstIdem_symmetricPairing {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) :
    ∃ τ : TensorProductAlgebra k QL Λ ν →ₗ[k] k,
      (∀ a b, redFirstIdem QL Λ ν * a * redFirstIdem QL Λ ν = a →
        redFirstIdem QL Λ ν * b * redFirstIdem QL Λ ν = b → τ (a * b) = τ (b * a)) ∧
      (∀ a, redFirstIdem QL Λ ν * a = a → a ≠ 0 →
        ∃ b, b * redFirstIdem QL Λ ν = b ∧ τ (a * b) ≠ 0) ∧
      (∀ b, b * redFirstIdem QL Λ ν = b → b ≠ 0 →
        ∃ a, redFirstIdem QL Λ ν * a = a ∧ τ (a * b) ≠ 0) := by
  obtain ⟨τ, hl, hr, hs⟩ := exists_redFirstTrace_symmetric QL hR ν (fun i j hij => by
    rw [CyclotomicAction.extremalCoeff_qCL_kl i j hij,
      CyclotomicAction.extremalCoeff_qCL_kl j i (Ne.symm hij)]) Λ
  set e := redFirstIdem QL Λ ν
  have hfe : tensorFlip e = e := tensorFlip_redFirstIdem QL Λ ν
  refine ⟨τ, hs, fun a ha ha0 => ?_, fun b hb hb0 => ?_⟩
  · obtain ⟨c, hc, hac⟩ := exists_mul_ne_zero_of_redFirstIdem_mul hR hQs Λ ν a ha0
    obtain ⟨y, -, hy2, hzy⟩ := hl (a * c) (by rw [← mul_assoc, ha])
      (by rw [mul_assoc, hc]) hac
    exact ⟨c * y, by rw [mul_assoc, hy2], by rwa [← mul_assoc]⟩
  · have hfb : e * tensorFlip b = tensorFlip b := by
      rw [← hfe, ← tensorFlip_mul, hb]
    have hfb0 : tensorFlip b ≠ 0 := fun h0 => hb0 (by
      rw [← tensorFlip_tensorFlip b, h0, map_zero])
    obtain ⟨c, hc, hbc⟩ := exists_mul_ne_zero_of_redFirstIdem_mul hR hQs Λ ν _ hfb0
    have hfc : e * tensorFlip c = tensorFlip c := by
      rw [← hfe, ← tensorFlip_mul, hc]
    have hw0 : tensorFlip c * b ≠ 0 := fun h0 => hbc (by
      rw [← tensorFlip_tensorFlip (tensorFlip b * c), tensorFlip_mul, tensorFlip_tensorFlip,
        h0, map_zero])
    obtain ⟨z, hz1, -, hzw⟩ := hr (tensorFlip c * b) (by rw [← mul_assoc, hfc])
      (by rw [mul_assoc, hb]) hw0
    exact ⟨z * tensorFlip c, by rw [← mul_assoc, hz1], by rwa [mul_assoc]⟩

/-- The symmetric trace of `redFirstIdem_symmetricPairing`. -/
def redFirstTrace {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) :
    TensorProductAlgebra k QL Λ ν →ₗ[k] k :=
  (redFirstIdem_symmetricPairing hR hQs Λ ν).choose

/-- **Self-duality of `y T^λ`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14): for
`y ∈ e⁰ T^λ e⁰`, the pairing `⟨y a, b y⟩ = τ(y a b)` with the symmetric red-first trace
identifies `y T^λ` with the dual of `T^λ y`. -/
def redFirstSelfDualEquiv {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (y : TensorProductAlgebra k QL Λ ν)
    (hy : redFirstIdem QL Λ ν * y * redFirstIdem QL Λ ν = y) :
    CornerSelfDual.Left k y ≃ₗ[k] Module.Dual k (CornerSelfDual.Right k y) :=
  haveI : FiniteDimensional k (TensorProductAlgebra k QL Λ ν) :=
    tensorProductAlgebra_finite Λ ν hR
  CornerSelfDual.rangeMulLeftDualEquiv (redFirstIdem QL Λ ν) y (redFirstTrace hR hQs Λ ν)
    (isIdempotentElem_redFirstIdem QL Λ ν) hy
    (redFirstIdem_symmetricPairing hR hQs Λ ν).choose_spec.1
    (redFirstIdem_symmetricPairing hR hQs Λ ν).choose_spec.2.1
    (redFirstIdem_symmetricPairing hR hQs Λ ν).choose_spec.2.2

theorem redFirstSelfDualEquiv_apply {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (y : TensorProductAlgebra k QL Λ ν)
    (hy : redFirstIdem QL Λ ν * y * redFirstIdem QL Λ ν = y) (a : TensorProductAlgebra k QL Λ ν)
    (z : CornerSelfDual.Right k y) :
    redFirstSelfDualEquiv hR hQs Λ ν y hy ⟨y * a, a, rfl⟩ z =
      redFirstTrace hR hQs Λ ν (redFirstIdem QL Λ ν * a * z.1) :=
  haveI : FiniteDimensional k (TensorProductAlgebra k QL Λ ν) :=
    tensorProductAlgebra_finite Λ ν hR
  CornerSelfDual.rangeMulLeftDualEquiv_apply _ _ _ _ _ _ _ _ a z

end Categorification.Stendhal
