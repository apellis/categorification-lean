/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerIdempotents
import Categorification.KLR.NilHeckeFullSplitting
import Categorification.KLR.CyclotomicGrading
import Categorification.KLR.SimpleNilHecke
import Categorification.Algebra.Graded.CornerResolution

/-!
# The positive corner of the cyclotomic nilHecke algebra

For the nilHecke ring `NH_m` and its idempotent `e_m = x^δ ∂_{w_0}` (M. Khovanov, A. Lauda,
*A diagrammatic approach to categorification of quantum groups I*, arXiv:0803.4121v2, §2.2,
Example 3), every element of the corner is a polynomial times the idempotent:
`e_m T e_m = ∂_{w_0}(T x^δ) e_m` (`NilHecke.idemNH_mul_mul_idemNH`). So in `R(m i) ≅ NH_m`, and
in every cyclotomic quotient `R^Λ(m i)` (the cyclotomic nilHecke algebra), the corner at the
block idempotent `e_{i,m}` is spanned by the dot monomials times `e_{i,m}`: it vanishes in
negative degrees and is `k e_{i,m}` in degree zero, as soon as the dots have positive degree.
Since `1` splits through `m!` copies of `e_m` (`NilHecke.exists_isSplitting_one_idemNH`),
`A e A = A`.

This is the base case of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.28: for one red strand and `β = m α_i`, the algebra
`T^λ_β ≅ R^λ(m α_i)` is Morita equivalent to its corner at `e_{i,m}`, the cohomology ring of a
Grassmannian, which is nonnegatively graded with `k` in degree zero; so every finite-dimensional
graded module has a projective resolution in `C↑` (`CycKLR.exists_upResolution_of_forall`).
We do not identify the corner with the cohomology ring: only its positivity is used.

## Main results

* `NilHecke.apply_mul_of_swap_invariant` : elements of `NH_m` are linear over symmetric
  polynomials.
* `NilHecke.idemNH_mul_mul_idemNH` : `e_m T e_m = ∂_{w_0}(T x^δ) e_m`.
* `KLRAlgebra.blockIdem_mul_mul_blockIdem` and its graded form
  `KLRAlgebra.blockIdem_mul_mul_blockIdem_of_mem_grade`.
* `CycKLR.exists_upResolution_of_forall`.
-/

noncomputable section

namespace Categorification

open MvPolynomial Equiv

namespace NilHecke

variable {k : Type*} [CommRing k] {m : ℕ}

/-- Elements of the nilHecke ring commute with multiplication by polynomials that are
invariant under the adjacent transpositions. -/
theorem apply_mul_of_swap_invariant {T : Module.End k (MvPolynomial (Fin m) k)}
    (hT : T ∈ nilHecke k m) {g : MvPolynomial (Fin m) k}
    (hg : ∀ j (h : j + 1 < m), rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) g = g)
    (f : MvPolynomial (Fin m) k) : T (g * f) = g * T f := by
  induction hT using Algebra.adjoin_induction generalizing f with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨j, rfl⟩
    · simp only [mulX_apply]; ring
    · have := ddw_mul_of_forall (k := k) (m := m) (ρ := [j])
        (fun l hl h => by rw [List.mem_singleton] at hl; subst hl; exact hg l h) f
      simpa using this
  | algebraMap r =>
    simp only [Module.algebraMap_end_apply, mul_smul_comm]
  | add x y _ _ hx hy => simp only [LinearMap.add_apply, hx, hy, mul_add]
  | mul x y _ _ hx hy => simp only [Module.End.mul_apply, hy, hx]

/-- **The corner of `NH_m` at `e_m`** (KL I §2.2, Example 3): `e_m T e_m = ∂_{w_0}(T x^δ) e_m`. -/
theorem idemNH_mul_mul_idemNH {T : Module.End k (MvPolynomial (Fin m) k)}
    (hT : T ∈ nilHecke k m) :
    idemNH k m * T * idemNH k m = mulPoly k m (ddw (w0Word m) (T (xDelta m))) * idemNH k m := by
  refine LinearMap.ext fun f => ?_
  simp only [idemNH, Module.End.mul_apply, mulPoly_apply]
  have hsym := fun j (h : j + 1 < m) => rename_swap_ddw_w0Word (k := k) h f
  rw [mul_comm (xDelta m) (ddw (w0Word m) f), apply_mul_of_swap_invariant hT hsym,
    ddw_mul_of_forall (fun j _ h => hsym j h)]
  ring

end NilHecke

namespace Graded

/-- A splitting of `1` through copies of `e` puts `1` in the two-sided ideal `A e A`. -/
theorem one_mem_span_of_isSplitting {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : A} {a b : ι → A} (h : IsSplitting 1 (fun _ => e) a b) :
    (1 : A) ∈ Submodule.span A (Set.range fun c : A => e * c) := by
  have hj : ∀ j, a j * b j = a j * (e * b j) := fun j => by
    have := congrArg (· * (a j * b j)) h.sum_eq
    simp only [one_mul, Finset.sum_mul] at this
    rw [← this, Finset.sum_eq_single j]
    · rw [mul_assoc, ← mul_assoc (b j), h.mul_self]
    · intro i _ hij
      rw [mul_assoc, ← mul_assoc (b i), h.mul_ne hij, zero_mul, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [← h.sum_eq]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hj]
  exact Submodule.smul_mem _ (a j) (Submodule.subset_span ⟨b j, rfl⟩)

end Graded

namespace KLR

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I} {c : I} (hν : ∀ a ∈ ν, a = c) (t : Seq ν)

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

omit [DecidableEq I] in
include hν in
theorem isConstOn_of_forall : IsConstOn t 0 m := fun a b _ _ _ _ =>
  (hν _ (t.mem a)).trans (hν _ (t.mem b)).symm

include hν in
/-- **The corner of `R(m i)` at `e_{i,m}`** (KL I §2.2, Example 3): `e z e = p(x) e` for a
polynomial `p` in the dots. -/
theorem blockIdem_mul_mul_blockIdem (z : A) :
    ∃ s : MvPolynomial (Fin m) k,
      blockIdem t 0 m * z * blockIdem t 0 m = pol s * blockIdem t 0 m := by
  have hz : toNH hν Q z ∈ NilHecke.nilHecke k m := by
    rw [← range_toNH hν Q]; exact ⟨z, rfl⟩
  refine ⟨NilHecke.ddw (NilHecke.w0Word m) (toNH hν Q z (NilHecke.xDelta m)), ?_⟩
  apply toNH_injective hν Q
  rw [map_mul, map_mul, map_mul, toNH_blockIdem hν t, toNH_pol]
  exact NilHecke.idemNH_mul_mul_idemNH hz

variable (G : GradingDatum Q)

include hν in
/-- **Positivity of the corner of `R(m i)` at `e_{i,m}`.** If the dots have positive degree,
`e R(m i) e` vanishes in negative degrees and is `k e` in degree zero. -/
theorem blockIdem_mul_mul_blockIdem_of_mem_grade (hdeg : 0 < G.degX c) {d : ℤ} {z : A}
    (hz : z ∈ G.grade ν d) :
    (d < 0 → blockIdem t 0 m * z * blockIdem t 0 m = 0) ∧
      (d = 0 → ∃ r : k, blockIdem t 0 m * z * blockIdem t 0 m = r • blockIdem t 0 m) := by
  set E : A := blockIdem t 0 m
  obtain ⟨s, hs⟩ := blockIdem_mul_mul_blockIdem hν t z
  have hE0 : E ∈ G.grade ν 0 := blockIdem_mem_grade G (zero_add _).le (isConstOn_of_forall hν t)
  have het : (e t : A) = 1 := e_eq_one_of_forall hν Q t
  have hw : ∀ u : Fin m →₀ ℕ, Finsupp.weight (fun a => G.degX (t.lbl a)) u =
      (u.sum fun _ n => (n : ℤ)) * G.degX c := by
    intro u
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hl : t.lbl a = c := hν _ (t.mem a)
    rw [hl, nsmul_eq_mul]
  have hy : ∀ u : Fin m →₀ ℕ, pol (monomial u 1) * E ∈
      G.grade ν ((u.sum fun _ n => (n : ℤ)) * G.degX c) := by
    intro u
    have h1 := G.pol_monomial_mul_e_mem_grade (k := k) u t
    rw [het, mul_one, hw] at h1
    simpa using SetLike.GradedMul.mul_mem h1 hE0
  have hsum : E * z * E = ∑ u ∈ s.support, s.coeff u • (pol (monomial u 1) * E) := by
    rw [hs]
    conv_lhs => rw [s.as_sum]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show monomial u (s.coeff u) = s.coeff u • monomial u (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_mul_assoc]
  have hEzE : E * z * E ∈ G.grade ν d := by
    simpa using SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hE0 hz) hE0
  have hproj : E * z * E = ∑ u ∈ s.support, s.coeff u •
      GradedAlgebra.proj (G.grade ν) d (pol (monomial u 1) * E) := by
    conv_lhs => rw [← DirectSum.decompose_of_mem_same (G.grade ν) hEzE]
    rw [← GradedAlgebra.proj_apply, hsum, map_sum]
    simp only [map_smul]
  have hnn : ∀ u : Fin m →₀ ℕ, 0 ≤ (u.sum fun _ n => (n : ℤ)) :=
    fun u => Finset.sum_nonneg fun a _ => Int.natCast_nonneg _
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [hproj]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne (G.grade ν) (hy u)
      (by nlinarith [hnn u]), smul_zero]
  · subst hd
    refine ⟨s.coeff 0, ?_⟩
    rw [hproj]
    by_cases h0 : (0 : Fin m →₀ ℕ) ∈ s.support
    · rw [Finset.sum_eq_single (0 : Fin m →₀ ℕ)]
      · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same (G.grade ν)
          (by simpa using hy 0), monomial_zero', C_1, map_one, one_mul]
      · intro u _ hu
        have hpos : 0 < (u.sum fun _ n => (n : ℤ)) := by
          obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hu
          have ha' : 0 < u a := Nat.pos_of_ne_zero (by simpa using ha)
          have hle : (u a : ℤ) ≤ u.sum fun _ n => (n : ℤ) := by
            rw [Finsupp.sum]
            exact Finset.single_le_sum (f := fun b => (u b : ℤ)) (fun b _ => Int.natCast_nonneg _)
              (Finsupp.mem_support_iff.2 (by omega))
          omega
        rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne (G.grade ν) (hy u)
          (by positivity), smul_zero]
      · intro h; exact absurd h0 h
    · rw [Finsupp.notMem_support_iff.1 h0, zero_smul]
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
      have hpos : 0 < (u.sum fun _ n => (n : ℤ)) := by
        obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hu0
        have ha' : 0 < u a := Nat.pos_of_ne_zero (by simpa using ha)
        have hle : (u a : ℤ) ≤ u.sum fun _ n => (n : ℤ) := by
          rw [Finsupp.sum]
          exact Finset.single_le_sum (f := fun b => (u b : ℤ)) (fun b _ => Int.natCast_nonneg _)
            (Finsupp.mem_support_iff.2 (by omega))
        omega
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne (G.grade ν) (hy u)
        (by positivity), smul_zero]

include hν in
/-- `1 ∈ R(m i)` splits through `m!` copies of `e_{i,m}`. -/
theorem exists_isSplitting_one_blockIdem :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → A),
      Graded.IsSplitting 1 (fun _ => blockIdem t 0 m) a b := by
  obtain ⟨ι, _, _, a, b, -, hS⟩ := NilHecke.exists_isSplitting_one_idemNH k m
  have h := hS.map (nilHeckeEquivOfForall hν Q).symm
  have he : (nilHeckeEquivOfForall hν Q).symm ⟨NilHecke.idemNH k m, NilHecke.idemNH_mem⟩ =
      blockIdem t 0 m :=
    (AlgEquiv.symm_apply_eq _).2 (nilHeckeEquivOfForall_blockIdem hν t).symm
  rw [map_one] at h
  simp only [he] at h
  exact ⟨ι, inferInstance, inferInstance, _, _, h⟩

end KLRAlgebra

namespace CycKLR

open KLRAlgebra Categorification.Graded

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) (Λ : I → ℕ) {ν : Multiset I} {c : I} (hν : ∀ a ∈ ν, a = c)

local notation "aΛ" => (fun i => Polynomial.X ^ Λ i : I → Polynomial k)
local notation "m" => Multiset.card ν

include hν in
/-- **Webster, arXiv:1309.3796v3, proof of Theorem 5.28, base case.** Every finite-dimensional
graded module over the cyclotomic nilHecke algebra `R^Λ(m i)` has a graded projective resolution
in `C↑`, when the dots have positive degree: the corner at `e_{i,m}` is nonnegatively graded with
`k` in degree zero, and `1` splits through `e_{i,m}`. -/
theorem exists_upResolution_of_forall (hdeg : 0 < G.degX c)
    [Module.Finite k (CycKLR k Q aΛ ν)] (N : GFin (CycKLR.grade G Λ ν)) :
    ∃ c', Nonempty (GFin.UpResolution N c') := by
  obtain ⟨t⟩ : Nonempty (Seq ν) := ⟨(Seq.uniqueOfForall hν).default⟩
  set E : KLRAlgebra k Q ν := blockIdem t 0 m
  have hE : IsIdempotentElem E :=
    isIdempotentElem_blockIdem (zero_add _).le (isConstOn_of_forall hν t)
  have he : IsIdempotentElem (mk k Q aΛ ν E) := hE.map _
  have he0 : mk k Q aΛ ν E ∈ CycKLR.grade G Λ ν 0 :=
    Submodule.mem_map.2 ⟨E, blockIdem_mem_grade G (zero_add _).le (isConstOn_of_forall hν t), rfl⟩
  obtain ⟨ι, _, _, a, b, hS⟩ := exists_isSplitting_one_blockIdem (k := k) (Q := Q) hν t
  have hS' := hS.map (mk k Q aΛ ν)
  rw [map_one] at hS'
  refine GFin.exists_upResolution_of_corner he he0 ?_ ?_ (one_mem_span_of_isSplitting hS') N
  · intro d hd z hz
    obtain ⟨z, hz', rfl⟩ := Submodule.mem_map.1 hz
    simp only [AlgHom.toLinearMap_apply]
    rw [← map_mul, ← map_mul,
      (blockIdem_mul_mul_blockIdem_of_mem_grade hν t G hdeg hz').1 hd, map_zero]
  · intro z hz
    obtain ⟨z, hz', rfl⟩ := Submodule.mem_map.1 hz
    simp only [AlgHom.toLinearMap_apply]
    obtain ⟨r, hr⟩ := (blockIdem_mul_mul_blockIdem_of_mem_grade hν t G hdeg hz').2 rfl
    exact ⟨r, by rw [← map_mul, ← map_mul, hr, map_smul]⟩

end CycKLR

end KLR

end Categorification
