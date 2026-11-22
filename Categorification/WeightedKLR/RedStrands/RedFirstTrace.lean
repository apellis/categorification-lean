/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstCorner
import Categorification.KLR.CyclotomicAction.Frobenius

set_option backward.isDefEq.respectTransparency false

/-!
# The trace on the red-first corner

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Theorem 5.27, implication (3) ⇒ (1): the endomorphism algebra `e⁰ T^λ e⁰` of `P⁰` is the
cyclotomic KLR algebra of the total weight (Proposition 5.28, `redFirstCornerEquiv`), which is a
symmetric Frobenius algebra (Theorem 3.18, `IsRouquierQ.cyclotomic_frobenius`). Transporting its
trace gives a `k`-linear functional `τ` on `T^λ` with `τ(z y) ≠ 0` for some `y ∈ e⁰ T^λ e⁰`
whenever `0 ≠ z ∈ e⁰ T^λ e⁰`.

## Main results

* `redFirstCornerEquiv_smul`: the isomorphism of Proposition 5.28 is `k`-linear.
* `exists_redFirstTrace`: the transported trace.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR QuantumGroup QuantumGroup.UDot

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification


variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) {D : QuantumGroup.CartanDatum I}
  (hQ : IsRouquierQ D Q) (ν : Multiset I)

theorem redFirstSplitEquiv_smul {ℓ : ℕ} (c : Fin (ℓ + 1)) (Λ' : Fin (ℓ + 2) → I →₀ ℕ) (d : k)
    (x : (isIdempotentElem_redFirstIdem Q (SplitRed.mergeWeights c Λ') ν).Corner) :
    SplitRed.redFirstSplitEquiv Q c Λ' hQ (d • x) =
      d • SplitRed.redFirstSplitEquiv Q c Λ' hQ x := by
  apply Subtype.ext
  change ((SplitRed.splitRedEquiv c Q Λ' hQ) (d • x.1)).1 =
    d • ((SplitRed.splitRedEquiv c Q Λ' hQ) x.1).1
  rw [map_smul]
  exact KLR.Corner.val_smul _ _

theorem redFirstCornerEquivOne_smul (Λ : Fin 1 → I →₀ ℕ) (d : k)
    (x : (isIdempotentElem_redFirstIdem Q Λ ν).Corner) :
    redFirstCornerEquivOne Q Λ ν (d • x) = d • redFirstCornerEquivOne Q Λ ν x := by
  change (SingleRed.cyclotomicEquiv Q Λ ν).symm (d • x.1) =
    d • (SingleRed.cyclotomicEquiv Q Λ ν).symm x.1
  exact map_smul _ _ _

theorem redFirstCornerEquivAux_smul : ∀ (ℓ : ℕ) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (w : I →₀ ℕ)
    (h : ∑ r, Λ r = w) (d : k) (x : (isIdempotentElem_redFirstIdem Q Λ ν).Corner),
    redFirstCornerEquivAux Q hQ ν ℓ Λ w h (d • x) =
      d • redFirstCornerEquivAux Q hQ ν ℓ Λ w h x
  | 0, Λ, w, h, d, x => by
      obtain rfl : Λ 0 = w := by rw [← h, Fin.sum_univ_one]
      exact redFirstCornerEquivOne_smul Q ν Λ d x
  | ℓ + 1, Λ', w, h, d, x => by
      change redFirstCornerEquivAux Q hQ ν ℓ (SplitRed.mergeWeights 0 Λ') w _
          ((SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).symm (d • x)) =
        d • redFirstCornerEquivAux Q hQ ν ℓ (SplitRed.mergeWeights 0 Λ') w _
          ((SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).symm x)
      have hs : (SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).symm (d • x) =
          d • (SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).symm x := by
        apply (SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).injective
        rw [redFirstSplitEquiv_smul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      rw [hs, redFirstCornerEquivAux_smul]

/-- **Webster, arXiv:1309.3796v2, Proposition 5.28**: the isomorphism
`e⁰ T^λ e⁰ ≅ R^{∑ λ_r}` is `k`-linear. -/
theorem redFirstCornerEquiv_smul {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (d : k)
    (x : (isIdempotentElem_redFirstIdem Q Λ ν).Corner) :
    redFirstCornerEquiv Q hQ ν Λ (d • x) = d • redFirstCornerEquiv Q hQ ν Λ x :=
  redFirstCornerEquivAux_smul Q hQ ν ℓ Λ _ rfl d x

/-- The weight datum on `ℤ^I` with simple coroots the coordinate functionals. -/
def coordinateWeightDatum (C : QuantumGroup.CartanDatum I) :
    WeightDatum C (I → ℤ) ((I → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A C i j
  iY i := { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  pair_iY_iX _ _ := rfl

include hQ in
/-- **The trace on the red-first corner** (Webster, arXiv:1309.3796v2, proof of Theorem 5.27):
a `k`-linear functional `τ` on `T^λ` such that every nonzero `z ∈ e⁰ T^λ e⁰` has
`y ∈ e⁰ T^λ e⁰` with `τ(z y) ≠ 0`. -/
theorem exists_redFirstTrace {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) :
    ∃ τ : TensorProductAlgebra k Q Λ ν →ₗ[k] k, ∀ z, redFirstIdem Q Λ ν * z = z →
      z * redFirstIdem Q Λ ν = z → z ≠ 0 →
      ∃ y, redFirstIdem Q Λ ν * y = y ∧ y * redFirstIdem Q Λ ν = y ∧ τ (z * y) ≠ 0 := by
  set e := redFirstIdem Q Λ ν
  have he : IsIdempotentElem e := isIdempotentElem_redFirstIdem Q Λ ν
  obtain ⟨tr, htr, -⟩ := IsRouquierQ.cyclotomic_frobenius hQ (coordinateWeightDatum D)
    (fun i => ((∑ r, Λ r) i : ℤ)) (a := fun i => Polynomial.X ^ (∑ r, Λ r) i)
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
  refine ⟨tr ∘ₗ φl ∘ₗ cut, fun z hz1 hz2 hz0 => ?_⟩
  have hzc : e * z * e = z := by rw [hz1, hz2]
  set zc : he.Corner := KLR.Corner.mk z (by rw [hzc])
  have hφz : φ zc ≠ 0 := fun h0 => hz0 (by
    have : zc = 0 := φ.injective (h0.trans (map_zero φ).symm)
    exact congrArg KLR.Corner.val this)
  obtain ⟨y', hy'⟩ := htr _ hφz
  set yc := φ.symm y'
  refine ⟨yc.val, KLR.Corner.E_mul_val yc, KLR.Corner.val_mul_E yc, ?_⟩
  have hcut : cut (z * yc.val) = zc * yc := KLR.Corner.ext (by
    change e * (z * yc.val) * e = z * yc.val
    rw [← mul_assoc, hz1, mul_assoc, KLR.Corner.val_mul_E])
  change tr (φ (cut (z * yc.val))) ≠ 0
  rw [hcut, map_mul, RingEquiv.apply_symm_apply]
  exact hy'

end Categorification.Stendhal
