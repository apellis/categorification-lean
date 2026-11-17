/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ExtensionK0
import Categorification.KLR.CyclotomicProjectiveLift
import Categorification.KLR.K0Algebra

/-!
# Extension to the cyclotomic quotient on projective K₀

Webster, arXiv:1309.3796v2, §3.4, proof of Proposition 3.21. Tensoring an
affine graded projective with the monomial cyclotomic quotient takes a principal
projective to the left ideal of the projected idempotent. Over a field,
lifting a degree-zero idempotent gives a preimage for every shifted
indecomposable projective class. Hence extension is onto in each weight and
on their direct sum.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open Categorification.Graded MulOpposite

section Algebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

local notation "Aff" => KLRAlgebra k Q ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ i) ν
local notation "π" => mk k Q (fun i => Polynomial.X ^ Λ i) ν
local notation "srcGr" => G.grade ν
local notation "dstGr" => grade G Λ ν

local instance : Module Affᵐᵒᵖ C := Module.compHom C (π).toRingHom.op

local instance : SMulCommClass C Affᵐᵒᵖ C where
  smul_comm b r x := (mul_assoc b x (π r.unop)).symm

local instance : IsScalarTower k Affᵐᵒᵖ C where
  smul_assoc c r x := by
    change x * π (c • r.unop) = c • (x * π r.unop)
    rw [map_smul, mul_smul_comm]

private theorem mk_preservesGrading : PreservesGrading srcGr dstGr (π).toLinearMap :=
  fun _ _ hx => Graded.mem_map_of_mem _ _ hx

/-- The graded cyclotomic projective obtained as `C ⊗_A P` via the quotient map. -/
def quotientProj (P : GProj srcGr) : GProj dstGr :=
  extensionProj srcGr dstGr π (mk_preservesGrading G Λ ν) (fun _ _ => rfl) P

/-- Extension of scalars along the cyclotomic quotient on graded projective classes
(Webster, arXiv:1309.3796v2, proof of Proposition 3.21). -/
def quotientK0 : K0 srcGr →ₗ[LaurentPolynomial ℤ] K0 dstGr :=
  extensionK0 srcGr dstGr π (mk_preservesGrading G Λ ν) (fun _ _ => rfl)

@[simp] theorem quotientK0_of (P : GProj srcGr) :
    quotientK0 G Λ ν (K0.of P) = K0.of (quotientProj G Λ ν P) :=
  extensionK0_of srcGr dstGr π (mk_preservesGrading G Λ ν) (fun _ _ => rfl) P

/-- Extension of scalars takes `A e` to `C π(e)` with its inherited grading
(Webster, proof of Proposition 3.21). -/
theorem quotientK0_ofIdempotent {e : Aff} (he : IsIdempotentElem e) (he0 : e ∈ srcGr 0) :
    quotientK0 G Λ ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dstGr) (π e) (he.map (π))
        (Graded.mem_map_of_mem _ (π).toLinearMap he0)) :=
  extensionK0_ofIdempotent srcGr dstGr π (mk_preservesGrading G Λ ν) (fun _ _ => rfl) he he0

/-- Extension of scalars on the direct sum of all root contents (Webster, §3.4,
proof of Proposition 3.21). -/
def totalQuotientK0 : G.K0R →ₗ[LaurentPolynomial ℤ] projectiveK0 G Λ :=
  DirectSum.lmap (quotientK0 G Λ)

@[simp] theorem totalQuotientK0_lof (x : K0 srcGr) :
    totalQuotientK0 G Λ (DirectSum.lof (LaurentPolynomial ℤ) _ G.K0fam ν x) =
      DirectSum.lof (LaurentPolynomial ℤ) _ (fun β => K0 (grade G Λ β)) ν (quotientK0 G Λ ν x) :=
  DirectSum.lmap_lof ..

end Algebra

section Field

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (ν : Multiset I)

/-- The affine-to-cyclotomic map is onto in each weight (Webster, proof of
Proposition 3.21). Symmetry and positive dot degrees ensure that the
degree-zero affine algebra is finite dimensional. -/
theorem quotientK0_surjective (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) :
    Function.Surjective (quotientK0 G Λ ν) := by
  let := G.hasGdim_grade' (ν := ν) hsym hX
  let : HasGdim (grade G Λ ν) :=
    { finiteDimensional := fun n => inferInstanceAs (Module.Finite k ((G.grade ν n).map _))
      bddBelow := by
        obtain ⟨L, hL⟩ := HasGdim.bddBelow (ℳ := G.grade ν)
        refine ⟨L, fun n hn => hL ?_⟩
        intro h
        apply hn
        change (G.grade ν n).map _ = ⊥
        rw [h, Submodule.map_bot] }
  apply LinearMap.range_eq_top.mp
  rw [eq_top_iff, ← K0.span_indec (grade G Λ ν)]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  obtain ⟨e, he, he0, j, ⟨u⟩⟩ := exists_iso_of_affineIdempotent G Λ ν hsym hX b.rep b.isIndec_rep
  refine ⟨(LaurentPolynomial.T j : LaurentPolynomial ℤ) • K0.of (GProj.ofIdempotent e he he0), ?_⟩
  rw [map_smul, quotientK0_ofIdempotent, K0.T_smul_of]
  exact (K0.of_eq_of_iso u).symm

/-- The affine graded projective Grothendieck group surjects onto the direct sum
of cyclotomic weight groups (Webster, Proposition 3.21, generation step). -/
theorem totalQuotientK0_surjective (hsym : KLRSymm Q) (hX : ∀ i, 0 < G.degX i) :
    Function.Surjective (totalQuotientK0 G Λ) :=
  (DirectSum.lmap_surjective _).mpr fun γ => quotientK0_surjective G Λ γ hsym hX

end Field

end Categorification.KLR.CycKLR
