/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0Algebra
import Categorification.Diagrams.KL3.Theorem13

/-!
# KL III Theorems 1.1 and 1.2 for the algebra homomorphism `γ : _𝒜 U̇ → K₀(U̇)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §1:

> **Theorem 1.1.** The map `γ` is surjective for any root datum and field `k`.
> **Theorem 1.2.** The map `γ` is injective if the graphical calculus for the root datum and
> field `k` is nondegenerate.

Here `γ = gammaAlg` is the homomorphism of idempotented `ℤ[q, q⁻¹]`-algebras of
`Categorification.Diagrams.KL3.K0Algebra` (KL III Proposition 3.27). Its source is the actual
integral form `AUD RD vQ`, and its target is the direct sum `K0All RD k` of all weight blocks.

The conditional core uses `hG : HomGdim RD k` and `hspan : SortedSpan RD k`. For every finite
Cartan datum, `homGdim` proves the first using the general-Cartan graded Hom bounds;
`sortedSpan_holds` proves the second without even a finite-rank assumption. No simply-laced
hypothesis is used. Proposition 2.5 is supplied by `UDot.KL3.formNondeg_unconditional`.

* `gammaAlg_surjective`: **Theorem 1.1** given `hG`, `hspan`;
* `gammaAlg_injective`: **Theorem 1.2** given `hG` and `CalculusNondeg RD k`;
* `gammaAlgEquiv`: the resulting ring equivalence given `hG`, `hspan`, `CalculusNondeg RD k`;
* `gammaAlg_surjective_unconditional`: surjectivity for every finite Cartan datum;
* `gammaAlgEquiv_unconditional`: equivalence for every finite Cartan datum, still requiring
  `CalculusNondeg RD k` ("unconditional" discharges hom-finiteness and spanning, not nondegeneracy);
* `gammaAlgEquiv_sl`: the `sl_n` case over any field, using Theorem 1.3.

The equivalences are packaged as `RingEquiv` between non-unital rings. Laurent-scalar
compatibility is stated separately by `gammaAlg_smul`, and weight idempotents are respected
by `gammaAlg_one`. This is not an unconditional general-Cartan nondegeneracy theorem.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams
  Categorification.QuantumGroup Categorification.QuantumGroup.UDot Presentation GradedBicat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

section Bij

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

variable [DecidableEq I] [Finite I] (hG : HomGdim RD k)

omit [Finite I] in
/-- **KL III Theorem 1.1, as a statement about idempotented algebras** (any root datum,
`k` a field; given hom-finiteness and the spanning hypothesis, both consequences of
Proposition 3.11 and its proof): `γ : _𝒜 U̇ → K₀(U̇)` is surjective. -/
theorem gammaAlg_surjective (hspan : SortedSpan RD k) :
    Function.Surjective (gammaAlg k (torsionFreeK0_of_homGdim hG)) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add y y' hy hy' =>
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨x', rfl⟩ := hy'
    exact ⟨x + x', map_add _ _ _⟩
  | of a y =>
    obtain ⟨⟨_, f, rfl⟩, hz⟩ := gammaUA'_surjective_of_sortedSpan' hG hspan a.2 a.1 y
    rw [gammaUA'_apply] at hz
    refine ⟨⟨genU RD (Finsupp.mapDomain (Sigma.mk a) f), (mem_AUD_iff _).2 ⟨_, rfl⟩⟩, ?_⟩
    rw [gammaAlg_genU, genK_mapDomain, hz]

omit [Finite I] in
/-- **KL III Theorem 1.2, as a statement about idempotented algebras** (any root datum, `k` a
field, given hom-finiteness): if the graphical calculus is nondegenerate, `γ : _𝒜 U̇ → K₀(U̇)` is
injective. -/
theorem gammaAlg_injective (hnd : CalculusNondeg RD k) :
    Function.Injective (gammaAlg k (torsionFreeK0_of_homGdim hG)) := by
  set htf := torsionFreeK0_of_homGdim hG
  refine (injective_iff_map_eq_zero (gammaAlg k htf)).2 fun x hx => ?_
  obtain ⟨f, hf⟩ := (mem_AUD_iff x.1).1 x.2
  have hK : genK RD k f = 0 := by
    rw [← gammaFun_eq htf hf]; exact hx
  have hblk : ∀ a : X × X, one RD vQ a.1 * genU RD f * one RD vQ a.2 = 0 := by
    intro a
    obtain ⟨f', hf'⟩ := exists_block a.1 a.2 f
    have hK' : genK RD k (Finsupp.mapDomain (Sigma.mk a) f') = 0 := by
      rw [← hf', genK_mulG, genK_mulG, hK, mul_zero, zero_mul]
    rw [genK_mapDomain] at hK'
    have h0 : dpCComb (k := k) a.2 a.1 f' = 0 :=
      DirectSum.of_injective (β := fun p : X × X => K0Kar RD k p.1 p.2) a
        (by rw [hK', map_zero])
    have hz : (⟨dpComb a.2 a.1 f', LinearMap.mem_range_self _ _⟩ :
        LinearMap.range (dpComb (RD := RD) a.2 a.1)) = 0 := by
      refine gammaUA'_injective_unconditional hG hnd a.2 a.1 ?_
      rw [gammaUA'_apply, h0, map_zero]
    have hz' : dpComb (RD := RD) a.2 a.1 f' = 0 := congrArg Subtype.val hz
    rw [← genU_genOne, ← genU_genOne, ← genU_mulG, ← genU_mulG, hf', genU_mapDomain, hz',
      map_zero, map_zero]
  apply Subtype.ext
  rw [← hf, genU_eq_sum_blocks]
  exact Finset.sum_eq_zero fun a _ => hblk a

/-- **`_𝒜 U̇ ≅ K₀(U̇)` as idempotented `ℤ[q, q⁻¹]`-algebras** (KL III Theorems 1.1 and 1.2; any
root datum, `k` a field, nondegenerate calculus, given hom-finiteness and the
spanning hypothesis): `γ` is a ring isomorphism (non-unital rings; `ℤ[q, q⁻¹]`-linear by
`gammaAlg_smul`, `γ(1_λ) = [1_λ]` by `gammaAlg_one`). -/
def gammaAlgEquiv (hspan : SortedSpan RD k) (hnd : CalculusNondeg RD k) :
    AUD RD vQ ≃+* K0All RD k :=
  RingEquiv.ofBijective (gammaAlg k (torsionFreeK0_of_homGdim hG))
    ⟨gammaAlg_injective hG hnd, gammaAlg_surjective hG hspan⟩

/-- KL III Theorem 1.1 for every finite Cartan datum, without additional hypotheses. -/
theorem gammaAlg_surjective_unconditional :
    Function.Surjective (gammaAlg (RD := RD) k (torsionFreeK0_of_homGdim homGdim)) :=
  gammaAlg_surjective homGdim sortedSpan_holds

/-- `_𝒜 U̇ ≅ K₀(U̇)` for every finite Cartan datum with nondegenerate calculus. -/
def gammaAlgEquiv_unconditional (hnd : CalculusNondeg RD k) :
    AUD RD vQ ≃+* K0All RD k :=
  gammaAlgEquiv homGdim sortedSpan_holds hnd

end Bij

/-! ## `sl_n` -/

section SlN

attribute [local instance] KLR.KLGamma.vAlgebra

/-- **KL III, `sl_n`: `_𝒜 U̇(sl_n) ≅ K₀(U̇(sl_n))` as idempotented `ℤ[q, q⁻¹]`-algebras**, over
any field `K` (Theorems 1.1, 1.2 with Theorem 1.3; root datum `slRootDatum m`, `I = Fin m`). -/
def gammaAlgEquiv_sl (K : Type w) [Field K] (m : ℕ) :
    AUD (Categorification.Flag.slRootDatum m) vQ ≃+* K0All (Categorification.Flag.slRootDatum m) K :=
  gammaAlgEquiv_unconditional (theorem_1_3 K m)

end SlN

end Categorification.KL3.Diagram
