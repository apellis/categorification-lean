/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Graded
import Categorification.KLR.BasisTheorem

/-!
# The completed polynomial representation

The proof of Lemma `lem:gamma-homo` (label) in Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3 (§3.3 and the appendix of proofs), uses that a graded completion
of a KLR algebra acts faithfully on the completion of its polynomial representation (KL I,
arXiv:0803.4121v2, §2.3), a fact Webster takes from the literature. Here it is proved for the
graded completion, using the grading `PolyRep.polyRep_mem_homGrade` and the faithfulness of the
polynomial representation (`polyRep_injective`).

We model elements of the graded completion of `R(ν)` as Hahn series
`f : HahnSeries ℤ (KLRAlgebra k Q ν)` (the coefficient `f.coeff d` is meant to be homogeneous of
degree `d`, but nothing here needs this) and elements of the completed polynomial representation
as Hahn series `v : HahnSeries ℤ (Pol k ν)` (the coefficient `v.coeff e` is meant to be
homogeneous of degree `e`). The action is the convolution

  `(f • v).coeff n = ∑_{d + e = n} polyRep (f.coeff d) (v.coeff e)`,

obtained from Mathlib's `HahnModule` by applying `polyRep` to the coefficients of `f`.

## Main definitions and results

* `Unfurling.decomp G f` : a polynomial `f ∈ Pol_ν` as the Hahn series of its homogeneous
  components;
* `Unfurling.act hPQ f v` : the action of `HahnSeries ℤ R(ν)` on `HahnSeries ℤ Pol_ν`, with
  `act_mul`, `act_one`, `add_act`, `act_add`, `coeff_act`;
* `Unfurling.ser G a` : an element of `R(ν)` as the Hahn series of its homogeneous components,
  and `act_ser_decomp` : `ser a • decomp f = decomp (a • f)`;
* `Unfurling.eq_zero_of_act_decomp_eq_zero`, `Unfurling.eq_of_act_decomp_eq` : faithfulness
  and continuity: a series acting by zero on the completions of a graded-adically dense set
  (`IsGradedDense`) of polynomials is zero (`act_decomp_eq_zero_of_isGradedDense` is the
  continuity step).
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial PolyRep HahnSeries Finset

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (G : GradingDatum Q) {ν : Multiset I}

/-! ### Polynomials as series of their homogeneous components -/

/-- A polynomial `f ∈ Pol_ν` as the (finite) series `∑_e homPart e f`. -/
noncomputable def decomp : Pol k ν →ₗ[k] HahnSeries ℤ (Pol k ν) where
  toFun f :=
    { coeff := fun e => homPart G e f
      isPWO_support' := (degrees G f).finite_toSet.isPWO.mono fun e he => by
        by_contra h
        exact he (homPart_eq_zero_of_notMem G h) }
  map_add' f g := by ext : 1; funext e; simp
  map_smul' c f := by ext : 1; funext e; simp

omit [DecidableEq I] in
@[simp] theorem coeff_decomp (f : Pol k ν) (e : ℤ) : (decomp G f).coeff e = homPart G e f :=
  rfl

omit [DecidableEq I] in
theorem decomp_of_mem {e : ℤ} {f : Pol k ν} (hf : f ∈ homGrade G ν e) :
    decomp G f = single e f := by
  classical
  ext : 1; funext n
  rw [coeff_decomp, homPart_of_mem G hf]
  by_cases h : n = e
  · subst h; simp
  · simp [h]

/-! ### The action -/

local notation "E" => Module.End k (Pol k ν)

/-- The action of `HahnSeries ℤ R(ν)` on `HahnSeries ℤ Pol_ν` by convolution through the
polynomial representation. -/
noncomputable def act (f : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : HahnSeries ℤ (Pol k ν)) :
    HahnSeries ℤ (Pol k ν) :=
  (HahnModule.of E).symm (f.map (polyRep hPQ) • HahnModule.of E v)

theorem coeff_act (f : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : HahnSeries ℤ (Pol k ν)) (n : ℤ) :
    (act hPQ f v).coeff n =
      ∑ ij ∈ VAddAntidiagonal n (Set.VAddAntidiagonal.finite_of_isPWO
          (f.map (polyRep hPQ)).isPWO_support v.isPWO_support n),
        polyRep hPQ (f.coeff ij.1) (v.coeff ij.2) :=
  rfl

theorem act_mul (f g : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : HahnSeries ℤ (Pol k ν)) :
    act hPQ (f * g) v = act hPQ f (act hPQ g v) := by
  unfold act
  rw [Equiv.apply_symm_apply,
    show (f * g).map (polyRep hPQ) = f.map (polyRep hPQ) * g.map (polyRep hPQ) from
      HahnSeries.map_mul (polyRep hPQ).toRingHom.toNonUnitalRingHom, mul_smul]

theorem map_polyRep_one :
    (1 : HahnSeries ℤ (KLRAlgebra k Q ν)).map (polyRep hPQ) = 1 := by
  ext : 1; funext n
  simp only [map_coeff, HahnSeries.coeff_one]
  split_ifs <;> simp

theorem act_one (v : HahnSeries ℤ (Pol k ν)) : act hPQ 1 v = v := by
  rw [act, map_polyRep_one, one_smul, Equiv.symm_apply_apply]

theorem add_act (f g : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : HahnSeries ℤ (Pol k ν)) :
    act hPQ (f + g) v = act hPQ f v + act hPQ g v := by
  have : (f + g).map (polyRep hPQ) = f.map (polyRep hPQ) + g.map (polyRep hPQ) := by
    ext : 1; funext n; simp
  rw [act, this, HahnModule.add_smul fun _ _ _ => rfl]
  rfl

theorem sub_act (f g : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : HahnSeries ℤ (Pol k ν)) :
    act hPQ (f - g) v = act hPQ f v - act hPQ g v := by
  rw [eq_sub_iff_add_eq, ← add_act, sub_add_cancel]

theorem act_add (f : HahnSeries ℤ (KLRAlgebra k Q ν)) (v w : HahnSeries ℤ (Pol k ν)) :
    act hPQ f (v + w) = act hPQ f v + act hPQ f w := by
  rw [act, HahnModule.of_add, smul_add]
  rfl

theorem zero_act (v : HahnSeries ℤ (Pol k ν)) : act hPQ 0 v = 0 := by
  have := add_act hPQ 0 0 v
  rwa [add_zero, left_eq_add] at this

/-- The coefficients of `f • v` for series of finite support, as a double sum. -/
theorem coeff_act_of_subset {f : HahnSeries ℤ (KLRAlgebra k Q ν)} {v : HahnSeries ℤ (Pol k ν)}
    {Sd Se : Finset ℤ} (hf : f.support ⊆ Sd) (hv : v.support ⊆ Se) (n : ℤ) :
    (act hPQ f v).coeff n =
      ∑ d ∈ Sd, ∑ e ∈ Se, if d + e = n then polyRep hPQ (f.coeff d) (v.coeff e) else 0 := by
  classical
  rw [coeff_act, ← Finset.sum_product' (f := fun d e =>
    if d + e = n then polyRep hPQ (f.coeff d) (v.coeff e) else 0), ← Finset.sum_filter]
  refine Finset.sum_subset (fun ij hij => ?_) (fun ij _ hij => ?_)
  · rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hf ?_, hv h2⟩, h3⟩
    intro h; apply h1; simp [h]
  · rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨-, h3⟩ := Finset.mem_filter.1 ‹_›
    by_cases h1 : (f.map (polyRep hPQ)).coeff ij.1 = 0
    · rw [map_coeff] at h1; rw [h1, LinearMap.zero_apply]
    by_cases h2 : v.coeff ij.2 = 0
    · rw [h2, map_zero]
    exact absurd ⟨h1, h2, h3⟩ hij

/-- `(f • single e q).coeff n = polyRep (f.coeff (n - e)) q`. -/
theorem coeff_act_single (f : HahnSeries ℤ (KLRAlgebra k Q ν)) (e : ℤ) (q : Pol k ν) (n : ℤ) :
    (act hPQ f (single e q)).coeff n = polyRep hPQ (f.coeff (n - e)) q := by
  classical
  rw [coeff_act]
  by_cases hq : q = 0
  · subst hq
    simp
  by_cases hn : polyRep hPQ (f.coeff (n - e)) = 0
  · rw [hn, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    have h2' : ij.2 = e := by simpa [hq] using h2
    have h1' : ij.1 = n - e := by rw [← h3, ← h2']; simp
    rw [h1', hn, LinearMap.zero_apply]
  · rw [Finset.sum_eq_single (n - e, e)]
    · simp
    · intro ij hij hne
      rw [Finset.mem_vaddAntidiagonal] at hij
      obtain ⟨-, h2, h3⟩ := hij
      have h2' : ij.2 = e := by simpa [hq] using h2
      have h1' : ij.1 = n - e := by rw [← h3, ← h2']; simp
      exact absurd (Prod.ext h1' h2') hne
    · intro h
      exact absurd ((Finset.mem_vaddAntidiagonal _ _).2 ⟨by simpa using hn, by simpa using hq,
        by simp⟩) h

/-! ### Elements of `R(ν)` as series -/

/-- An element `a ∈ R(ν)` as the (finite) series of its homogeneous components. -/
noncomputable def ser (a : KLRAlgebra k Q ν) : HahnSeries ℤ (KLRAlgebra k Q ν) where
  coeff d := (G.coaction a).coeff d
  isPWO_support' := by
    rw [Finsupp.fun_support_eq]; exact (G.coaction a).coeff.support.finite_toSet.isPWO

@[simp] theorem coeff_ser (a : KLRAlgebra k Q ν) (d : ℤ) :
    (ser G a).coeff d = (G.coaction a).coeff d := rfl

/-- The coefficient of degree `d` of `ser a` is the degree `d` component of `a`. -/
theorem coeff_ser_eq_decompose (a : KLRAlgebra k Q ν) (d : ℤ) :
    (ser G a).coeff d = (DirectSum.decompose (G.grade ν) a d : KLRAlgebra k Q ν) :=
  (G.decompose_apply a d).symm

variable (hPdeg : ∀ a b, a ≠ b → (P a b).IsWeightedHomogeneous ![G.degX b, G.degX a]
  (G.degΨ a b))

include hPdeg in
/-- The action of `R(ν)` on `Pol_ν` is compatible with the decompositions into homogeneous
components: `ser a • decomp f = decomp (a • f)`. -/
theorem act_ser_decomp (a : KLRAlgebra k Q ν) (f : Pol k ν) :
    act hPQ (ser G a) (decomp G f) = decomp G (polyRep hPQ a f) := by
  classical
  ext : 1; funext n
  have hsd : (ser G a).support ⊆ ((G.coaction a).coeff.support : Set ℤ) := fun d hd => by
    simpa using hd
  have hse : (decomp G f).support ⊆ (degrees G f : Set ℤ) := fun e he => by
    by_contra h; exact he (homPart_eq_zero_of_notMem G h)
  rw [coeff_act_of_subset hPQ hsd hse, coeff_decomp]
  have hmem : ∀ d e, polyRep hPQ ((G.coaction a).coeff d) (homPart G e f) ∈
      homGrade G ν (d + e) := fun d e =>
    polyRep_mem_homGrade G hPdeg hPQ (G.coassoc a d) (homPart_mem G e f)
  conv_rhs => rw [← sum_homPart_degrees G f, ← G.counit a]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  rw [homPart_of_mem G (hmem _ _)]
  simp only [coeff_ser, coeff_decomp, eq_comm]

/-! ### Faithfulness and continuity -/

omit [DecidableEq I] in
/-- Graded-adic density of a set `S` of polynomials: every `q` agrees with some `s ∈ S` in
all degrees below any given bound. -/
def IsGradedDense (S : Set (Pol k ν)) : Prop :=
  ∀ (D : ℤ) (q : Pol k ν), ∃ s ∈ S, ∀ e < D, homPart G e (q - s) = 0

/-- Continuity: a series acting by zero on the completions of a dense set of polynomials acts by
zero on the completion of every polynomial. -/
theorem act_decomp_eq_zero_of_isGradedDense {S : Set (Pol k ν)} (hS : IsGradedDense G S)
    {f : HahnSeries ℤ (KLRAlgebra k Q ν)} (h : ∀ s ∈ S, act hPQ f (decomp G s) = 0)
    (q : Pol k ν) : act hPQ f (decomp G q) = 0 := by
  ext : 1; funext n
  obtain ⟨s, hs, hqs⟩ := hS (n - f.order + 1) q
  rw [show q = s + (q - s) by abel, map_add, act_add, h s hs, zero_add, coeff_act]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_vaddAntidiagonal] at hij
  obtain ⟨h1, -, h3⟩ := hij
  have h1' : f.coeff ij.1 ≠ 0 := fun h0 => h1 (by simp [h0])
  have hle := order_le_of_coeff_ne_zero h1'
  have h3' : ij.1 + ij.2 = n := h3
  rw [coeff_decomp, hqs _ (by omega), map_zero]

section Domain

variable [IsDomain k] (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hP in
/-- **Faithfulness of the completed polynomial representation** (used in the proof of
Webster, arXiv:1603.06311v3, Lemma `lem:gamma-homo` (label)): over a domain, with all `P a b`
nonzero, a series `f` with `f • decomp s = 0` for all `s` in a graded-adically dense set of
polynomials is zero. -/
theorem eq_zero_of_act_decomp_eq_zero {S : Set (Pol k ν)} (hS : IsGradedDense G S)
    {f : HahnSeries ℤ (KLRAlgebra k Q ν)} (h : ∀ s ∈ S, act hPQ f (decomp G s) = 0) :
    f = 0 := by
  have h0 := act_decomp_eq_zero_of_isGradedDense hPQ G hS h
  ext : 1; funext d
  rw [HahnSeries.coeff_zero]
  refine polyRep_injective hPQ hP ?_
  rw [map_zero]
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.zero_apply, ← sum_homPart_degrees G q, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have := congrArg (fun v => HahnSeries.coeff v (d + e)) (h0 (homPart G e q))
  simp only [decomp_of_mem G (homPart_mem G e q), coeff_act_single, add_sub_cancel_right,
    HahnSeries.coeff_zero] at this
  exact this

include hP in
/-- Two series acting in the same way on the completions of a graded-adically dense set of
polynomials are equal. -/
theorem eq_of_act_decomp_eq {S : Set (Pol k ν)} (hS : IsGradedDense G S)
    {f g : HahnSeries ℤ (KLRAlgebra k Q ν)}
    (h : ∀ s ∈ S, act hPQ f (decomp G s) = act hPQ g (decomp G s)) : f = g := by
  rw [← sub_eq_zero]
  exact eq_zero_of_act_decomp_eq_zero hPQ G hP hS fun s hs => by
    rw [sub_act, h s hs, sub_self]

end Domain

end Categorification.KLR.Unfurling
