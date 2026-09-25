/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Grading
import Categorification.Algebra.Graded.Idempotent
import Categorification.Algebra.Graded.Dimension

/-!
# Graded modules over KLR algebras: projectives `P_i`, `K₀`, characters

The generic graded-module layer (`Categorification.Algebra.Graded.*`) specialised to the
KLR algebra `R(ν)` over a field `k`, graded by a `GradingDatum` `G` (for KL I,
`KLR.klGradingDatum`). Following Khovanov–Lauda I (arXiv:0803.4121v2, §2.5):

* `GradingDatum.projP G i` : the graded projective module `P_i = R(ν) 1_i`, `i ∈ Seq(ν)`
  (for `i ∈ Seq(ν)` one has `⟨i⟩ = 0`, so there is no grading shift);
* `GradingDatum.K0_regular_eq_sum` : `[R(ν)] = ∑_i [P_i]` in `K₀(R(ν))`, from the complete
  orthogonal family of degree-zero idempotents `1_i`;
* `GradingDatum.ch G M i = gdim (1_i M)` : the character `ch(M) = ∑_i gdim(1_i M) · i` of a
  graded `R(ν)`-module, as a function `Seq ν → ℤ((q))`;
* `ch_shift` (`ch(M{a}) = q^a ch(M)`), `ch_prod`, `ch_eq_add_of_exact` (additivity on short exact
  sequences of graded modules with degree-preserving maps).

`K₀(R(ν))` is `Graded.K0 (G.grade ν)`, a `ℤ[q, q⁻¹]`-module with `q^a [P] = [P{a}]`.
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

/-- The idempotents `1_i`, `i ∈ Seq(ν)`, form a complete family of orthogonal idempotents. -/
theorem completeOrthogonalIdempotents_e (ν : Multiset I) :
    CompleteOrthogonalIdempotents (fun i : Seq ν => (e i : KLRAlgebra k Q ν)) where
  idem i := e_mul_self i
  ortho i j h := by simp only [e_mul_e, if_neg h]
  complete := sum_e

namespace GradingDatum

variable (G : GradingDatum Q) {ν : Multiset I}

/-- The graded projective module `P_i = R(ν) 1_i` (KL I, §2.5). -/
def projP (i : Seq ν) : GProj (G.grade ν) :=
  GProj.ofIdempotent (e i) (e_mul_self i) (G.e_mem_grade i)

/-- `[R(ν)] = ∑_i [P_i]` in `K₀(R(ν))`. -/
theorem K0_regular_eq_sum :
    K0.of (GProj.regular (G.grade ν)) = ∑ i : Seq ν, K0.of (G.projP i) :=
  K0.of_regular_eq_sum (completeOrthogonalIdempotents_e ν) G.e_mem_grade

/-- The `i`-component `ch(M, i) = gdim (1_i M)` of the character of a graded `R(ν)`-module. -/
def ch (M : GMod (G.grade ν)) (i : Seq ν) : LaurentSeries ℤ :=
  gdim (idem M.grading (e i : KLRAlgebra k Q ν))

/-- `ch(M{a}) = q^a ch(M)`. -/
theorem ch_shift (M : GMod (G.grade ν)) (a : ℤ) (i : Seq ν) :
    G.ch (M.shift a) i = HahnSeries.single a 1 * G.ch M i := by
  have h : idem (M.shift a).grading (e i : KLRAlgebra k Q ν) =
      Graded.shift (idem M.grading (e i : KLRAlgebra k Q ν)) a := rfl
  rw [ch, h, gdim_shift]
  rfl

/-- Characters are additive on short exact sequences of graded modules with degree-preserving
maps. -/
theorem ch_eq_add_of_exact {M N P : GMod (G.grade ν)} [HasGdim N.grading]
    {f : M →ₗ[KLRAlgebra k Q ν] N} {g : N →ₗ[KLRAlgebra k Q ν] P}
    (hfgr : PreservesGrading M.grading N.grading f) (hggr : PreservesGrading N.grading P.grading g)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (i : Seq ν) : G.ch N i = G.ch M i + G.ch P i :=
  gdim_idem_eq_add_of_exact (𝒜 := G.grade ν) (e_mul_self i) (G.e_mem_grade i) hfgr hggr hf hg
    hfg

/-- `ch(M ⊕ N) = ch(M) + ch(N)`. -/
theorem ch_prod (M N : GMod (G.grade ν)) [HasGdim M.grading] [HasGdim N.grading] (i : Seq ν) :
    G.ch (M.prod N) i = G.ch M i + G.ch N i := by
  haveI : HasGdim (M.prod N).grading :=
    inferInstanceAs (HasGdim (Graded.prod M.grading N.grading))
  exact G.ch_eq_add_of_exact (M := M) (N := M.prod N) (P := N)
    (f := LinearMap.inl _ M N) (g := LinearMap.snd _ M N)
    (fun _ _ hx => ⟨hx, zero_mem _⟩) (fun _ _ hx => hx.2) LinearMap.inl_injective
    LinearMap.snd_surjective Function.Exact.inl_snd i

end GradingDatum

end Categorification.KLR

end
