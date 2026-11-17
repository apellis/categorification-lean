/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlack
import Categorification.Algebra.Graded.HomogeneousBasis
import Categorification.Algebra.Graded.Duality

/-!
# Graded endomorphisms in the one-factor first lowering block

Webster, arXiv:1309.3796v2, Corollary 3.22 and Lemma 4.36. The black
dot gives a homogeneous power basis of the regular projective's endomorphisms.
-/

noncomputable section

namespace Categorification.Stendhal.SingleBlack

variable {I : Type*} [DecidableEq I] (i : I)
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Euler

open Categorification.Graded

variable {k : Type*} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 1 → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "𝒯" => TensorProductAlgebra k Q Λ ν
local notation "𝒜" => tensorProductGrade G ν
local notation "deg" => G.degX (Sum.inl i)
local notation "pEuler" => (Polynomial.X ^ Λ 0 i : Polynomial k)

private def dotBasis : Module.Basis (Fin (Polynomial.natDegree pEuler)) k 𝒯 :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X.pow (Λ 0 i))).basis.map
    (oneBlackOneRedEquiv i Q Λ).symm.toLinearEquiv

private theorem dotBasis_apply (a : Fin (Polynomial.natDegree pEuler)) : dotBasis (Q := Q) (Λ := Λ) i a =
    dot i Q Λ ^ (a : ℕ) := by
  apply (oneBlackOneRedEquiv i Q Λ).injective
  let b := AdjoinRoot.powerBasis' (Polynomial.monic_X (R := k) |>.pow (Λ 0 i))
  change (oneBlackOneRedEquiv i Q Λ) ((oneBlackOneRedEquiv i Q Λ).symm (b.basis a)) = _
  rw [AlgEquiv.apply_symm_apply, map_pow, oneBlackOneRedEquiv_dot]
  exact b.basis_eq_pow a

private theorem dotBasis_mem (a : Fin (Polynomial.natDegree pEuler)) :
    dotBasis (Q := Q) (Λ := Λ) i a ∈ 𝒜 ((a : ℕ) • deg) := by
  rw [dotBasis_apply]
  exact SetLike.pow_mem_graded _ (dot_mem_grade i G)

private def regularHomGradeEquiv (j : ℤ) : homGrade 𝒯 𝒜 𝒜 j ≃ₗ[k] 𝒜 j where
  toFun f := ⟨f.1 1, by simpa using (mem_homGrade.mp f.2) (SetLike.one_mem_graded 𝒜)⟩
  invFun a := ⟨LinearMap.toSpanSingleton 𝒯 𝒯 a, mem_homGrade.mpr fun e u hu => by
    change u * (a : 𝒯) ∈ 𝒜 (e + j)
    exact SetLike.GradedMul.mul_mem hu a.2⟩
  left_inv f := Subtype.ext (LinearMap.ext fun u => by
    change u • f.1 1 = f.1 u
    rw [← map_smul]
    exact congrArg f.1 (mul_one u))
  right_inv a := Subtype.ext (one_smul 𝒯 (a : 𝒯))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Webster, arXiv:1309.3796v2, §3.4, Corollary 3.22 and §4.7,
Theorem 4.38, in black weight `αᵢ` and one tensor factor. The graded
endomorphism dimension of the regular projective is the sum of the
degrees of the surviving dot monomials. -/
theorem regular_homGdim : GProj.homGdim (GProj.regular 𝒜) (GProj.regular 𝒜) =
    ∑ a : Fin (Λ 0 i), HahnSeries.single ((a : ℕ) • deg) (1 : ℤ) := by
  classical
  let B := dotBasis (Q := Q) (Λ := Λ) i
  let d := fun a : Fin (Polynomial.natDegree pEuler) => (a : ℕ) • deg
  have hspan : Submodule.span k (B '' Set.univ) = ⊤ := by rw [Set.image_univ, B.span_eq]
  have hfin (j : ℤ) : {a | a ∈ Set.univ ∧ d a = j}.Finite := Set.toFinite _
  have hbounded : BddBelow (d '' Set.univ) := (Set.toFinite _).bddBelow
  have hseries := gdim_eq_of_finrank_eq fun j => (regularHomGradeEquiv i G j).finrank_eq
  change gdim (homGrade 𝒯 𝒜 𝒜) = _
  rw [hseries]
  ext j
  have hc := coeff_gdim_inf_span 𝒜 d B.linearIndependent (dotBasis_mem i G)
    Set.univ hfin hbounded j
  rw [hspan] at hc
  simp only [inf_top_eq] at hc
  rw [hc, HahnSeries.coeff_sum]
  simp only [HahnSeries.coeff_single]
  let e : Fin (Polynomial.natDegree pEuler) ≃ Fin (Λ 0 i) :=
    finCongr (by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one])
  rw [← Equiv.sum_comp e]
  simp only [show ∀ a, (e a).val = a.val from fun _ => rfl, ← show ∀ a, d a = a.val • deg from fun _ => rfl]
  rw [Finset.sum_boole]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

private theorem regular_homGdimPoly_eq : gdimPoly (homGrade 𝒯 𝒜 𝒜) = gdimPoly 𝒜 := by
  have hf : (fun d => (Module.finrank k (homGrade 𝒯 𝒜 𝒜 d) : ℤ)) =
      fun d => (Module.finrank k (𝒜 d) : ℤ) :=
    funext fun j => congrArg Nat.cast (regularHomGradeEquiv i G j).finrank_eq
  unfold gdimPoly
  rw [hf]

/-- The one-red, one-black algebra is finite dimensional, so its grading
has a well-defined dimension series in every compatible grading. -/
theorem hasGdim_oneBlack : HasGdim 𝒜 := by
  let := Module.Finite.of_basis (dotBasis (Q := Q) (Λ := Λ) i)
  exact HasGdim.of_finiteDimensional _

/-- The Laurent polynomial of the homogeneous endomorphisms of the regular
projective in Corollary 3.22, with an arbitrary compatible dot degree. -/
theorem regular_homGdimPoly : gdimPoly (homGrade 𝒯 𝒜 𝒜) =
    ∑ a : Fin (Λ 0 i), LaurentPolynomial.T ((a : ℕ) • deg) := by
  let := Module.Finite.of_basis (dotBasis (Q := Q) (Λ := Λ) i)
  rw [regular_homGdimPoly_eq]
  apply toLaurentSeries_injective
  rw [toLaurentSeries_gdimPoly, map_sum]
  simp_rw [K0.toLaurentSeries_T]
  exact (gdim_eq_of_finrank_eq fun j => (regularHomGradeEquiv i G j).finrank_eq).symm.trans (regular_homGdim i G)

/-- A shift by `a` of the source and by `b` of the target contributes `T^(b-a)`
to the graded Hom polynomial for the repository's left regular projective. -/
theorem regular_shift_homGdimPoly (a b : ℤ) :
    gdimPoly (homGrade 𝒯 (shift 𝒜 a) (shift 𝒜 b)) =
      LaurentPolynomial.T (b - a) * gdimPoly (homGrade 𝒯 𝒜 𝒜) := by
  let := Module.Finite.of_basis (dotBasis (Q := Q) (Λ := Λ) i)
  have hf (j : ℤ) : Module.finrank k (homGrade 𝒯 (shift 𝒜 a) (shift 𝒜 b) j) =
      Module.finrank k (shift 𝒜 (b - a) j) := by
    rw [homGrade_shift_left, homGrade_shift_right, shift_apply]
    rw [(regularHomGradeEquiv i G _).finrank_eq, show a + j - b = j - (b - a) by abel]
  rw [regular_homGdimPoly_eq, ← gdimPoly_shift]
  have hs := funext fun j => congrArg (Nat.cast : ℕ → ℤ) (hf j)
  unfold gdimPoly
  rw [hs]

end Euler

end Categorification.Stendhal.SingleBlack
