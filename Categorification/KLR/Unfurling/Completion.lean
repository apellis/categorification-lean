/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Grading

/-!
# The graded completion of a KLR algebra

Webster (arXiv:1603.06311v3, §3.2) completes 2-morphism spaces in the grading topology, in which
the elements of degree `≥ d` form a basis of neighbourhoods of `0`; the completion `R̂` of a
KLR algebra in this topology is the target of the homomorphism `γ` of §3.3, Lemma label
`lem:gamma-homo`. For a single graded KLR algebra `R(ν)` (with `ν` finite, so that the cofinite
part of Webster's topology plays no role), an element of the completion is a formal sum
`∑_d f_d` of homogeneous components `f_d ∈ R(ν)_d` with `f_d = 0` for `d ≪ 0`; products are
computed degreewise, since in each degree only finitely many pairs of components contribute.

We formalize this completion as the subalgebra `GradingDatum.completion G ν` of Hahn series
`HahnSeries ℤ R(ν)` whose degree `d` coefficient lies in the degree `d` part `G.grade ν d`.
The algebra `R(ν)` embeds by sending an element to the series of its homogeneous components
(`GradingDatum.toCompletion`).

When every dot has positive degree, a formal power series `F` in the dots defines an element
`F(x) e_i` of the completion (`GradingDatum.seriesAt`): its degree `d` component is the finite
sum `∑_{c : dotWeight c = d} F_c x^c e_i`, where `dotWeight c = ∑_a c_a · degX i_a`. The
assignment `F ↦ F(x) e_i` is `k`-linear and multiplicative, sends `1` to `e_i` and a polynomial
`p` to `p(x) e_i`, is absorbed by `e_i` on both sides, sends power series with invertible
constant term to units of the corner `e_i R̂(ν) e_i`, and turns multiplication by a dot into
multiplication by the corresponding variable. Such power series in the dots appear in Webster's
factorization of the polynomials `P_ij` (§3.3, equation label `eq:factorize`) and in the
formulas defining `γ`.

These results are infrastructure for Lemma label `lem:gamma-homo`.

## Main definitions and results

* `HahnSeries.ofAddMonoidAlgebra` : finitely supported series as Hahn series (an algebra map).
* `KLR.GradingDatum.completion` : the graded completion of `R(ν)`.
* `KLR.GradingDatum.toCompletion`, `KLR.GradingDatum.toCompletion_injective`,
  `KLR.GradingDatum.coeff_toCompletion_of_mem_grade` : the embedding of `R(ν)`.
* `KLR.GradingDatum.seriesAt`, `KLR.GradingDatum.coeff_seriesAt` : power series in the dots
  times an idempotent.
* `KLR.GradingDatum.seriesAt_add`, `seriesAt_smul`, `seriesAt_mul`, `seriesAt_one`,
  `seriesAt_coe`, `toCompletion_e_mul_seriesAt`, `seriesAt_mul_toCompletion_e`,
  `seriesAt_mul_seriesAt_invOfUnit`, `seriesAt_invOfUnit_mul_seriesAt`,
  `toCompletion_x_mul_seriesAt`, `seriesAt_mul_toCompletion_x` : its algebraic properties.
-/

open Finset

namespace HahnSeries

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- The inclusion `A → HahnSeries ℤ A` of constants as an algebra map. -/
private noncomputable def constAlgHom : A →ₐ[k] HahnSeries ℤ A :=
  { (C : A →+* HahnSeries ℤ A) with commutes' := fun _ => rfl }

/-- The monomials `n ↦ single n 1`. -/
private noncomputable def singleOneHom : Multiplicative ℤ →* HahnSeries ℤ A where
  toFun n := single n.toAdd 1
  map_one' := rfl
  map_mul' a b := by rw [single_mul_single, mul_one]; rfl

variable (k A) in
/-- A finitely supported `ℤ`-indexed family of coefficients, as a Hahn series. -/
noncomputable def ofAddMonoidAlgebra : AddMonoidAlgebra A ℤ →ₐ[k] HahnSeries ℤ A :=
  AddMonoidAlgebra.liftNCAlgHom constAlgHom singleOneHom fun a n => by
    change Commute (C a) (single n.toAdd 1)
    rw [Commute, SemiconjBy, C_apply, single_mul_single, single_mul_single, zero_add, add_zero,
      mul_one, one_mul]

@[simp] theorem ofAddMonoidAlgebra_single (n : ℤ) (a : A) :
    ofAddMonoidAlgebra k A (AddMonoidAlgebra.single n a) = single n a := by
  refine (AddMonoidAlgebra.liftNC_single _ _ n a).trans ?_
  change C a * single n 1 = _
  rw [C_apply, single_mul_single, zero_add, mul_one]

@[simp] theorem coeff_ofAddMonoidAlgebra (f : AddMonoidAlgebra A ℤ) (d : ℤ) :
    (ofAddMonoidAlgebra k A f).coeff d = f.coeff d := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, coeff_add, hf, hg, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | single n a =>
    rw [ofAddMonoidAlgebra_single, coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs with h h' h' <;> first | rfl | (exact absurd h.symm h') | (exact absurd h'.symm h)

end HahnSeries

namespace Categorification.KLR

open KLRAlgebra MvPolynomial HahnSeries

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

namespace GradingDatum

variable (G : GradingDatum Q)

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-! ### The completion -/

theorem mul_mem_grade' {d d' : ℤ} {a b : A} (ha : a ∈ G.grade ν d) (hb : b ∈ G.grade ν d') :
    a * b ∈ G.grade ν (d + d') :=
  CoactionGrading.mul_mem_grade _ ha hb

variable (ν) in
/-- The graded completion `R̂(ν)`: Hahn series whose degree `d` coefficient lies in the degree `d`
part of `R(ν)`. -/
noncomputable def completion : Subalgebra k (HahnSeries ℤ A) where
  carrier := {f | ∀ d, f.coeff d ∈ G.grade ν d}
  mul_mem' {f g} hf hg d := by
    rw [Set.mem_ofPred_eq] at hf hg
    rw [HahnSeries.coeff_mul]
    refine Submodule.sum_mem _ fun ij hij => ?_
    have h := G.mul_mem_grade' (hf ij.1) (hg ij.2)
    rwa [(Finset.mem_antidiagonal.1 hij).2.2] at h
  add_mem' {f g} hf hg d := by
    rw [HahnSeries.coeff_add]; exact Submodule.add_mem _ (hf d) (hg d)
  algebraMap_mem' r d := by
    show _ ∈ _
    rw [HahnSeries.algebraMap_apply, HahnSeries.C_apply, coeff_single]
    split_ifs with h
    · subst h
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (CoactionGrading.one_mem_grade _)
    · exact Submodule.zero_mem _

theorem mem_completion {f : HahnSeries ℤ A} :
    f ∈ G.completion ν ↔ ∀ d, f.coeff d ∈ G.grade ν d := Iff.rfl

theorem coeff_mem_grade (f : G.completion ν) (d : ℤ) :
    (f : HahnSeries ℤ A).coeff d ∈ G.grade ν d := f.2 d

/-! ### The embedding `R(ν) → R̂(ν)` -/

/-- The embedding `R(ν) → R̂(ν)` sending `a` to the series of its homogeneous components. -/
noncomputable def toCompletion : A →ₐ[k] G.completion ν :=
  ((ofAddMonoidAlgebra k A).comp G.coaction).codRestrict (G.completion ν) fun a d => by
    rw [AlgHom.comp_apply, coeff_ofAddMonoidAlgebra]
    exact G.coassoc a d

/-- The degree `d` coefficient of `toCompletion a` is the degree `d` component of `a`. -/
theorem coeff_toCompletion (a : A) (d : ℤ) :
    ((G.toCompletion a : G.completion ν) : HahnSeries ℤ A).coeff d =
      (G.coaction a).coeff d :=
  coeff_ofAddMonoidAlgebra _ _

theorem coeff_toCompletion_eq_decompose (a : A) (d : ℤ) :
    ((G.toCompletion a : G.completion ν) : HahnSeries ℤ A).coeff d =
      (DirectSum.decompose (G.grade ν) a d : A) := by
  rw [coeff_toCompletion, G.decompose_apply]

theorem coeff_toCompletion_of_mem_grade {a : A} {d : ℤ} (ha : a ∈ G.grade ν d) (d' : ℤ) :
    ((G.toCompletion a : G.completion ν) : HahnSeries ℤ A).coeff d' =
      if d' = d then a else 0 := by
  rw [coeff_toCompletion, CoactionGrading.apply_of_mem_grade _ ha]
  by_cases h : d' = d
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem coe_toCompletion_of_mem_grade {a : A} {d : ℤ} (ha : a ∈ G.grade ν d) :
    ((G.toCompletion a : G.completion ν) : HahnSeries ℤ A) = single d a := by
  ext d'
  rw [G.coeff_toCompletion_of_mem_grade ha, coeff_single]
  split_ifs <;> rfl

theorem toCompletion_injective : Function.Injective (G.toCompletion (ν := ν)) := by
  intro a b h
  have hc : G.coaction a = G.coaction b := by
    ext d
    rw [← G.coeff_toCompletion, ← G.coeff_toCompletion, h]
  rw [← G.counit a, ← G.counit b, hc]

/-! ### Power series in the dots -/

/-- The weight `∑_a c_a · degX i_a` of the monomial `x^c e_i`. -/
noncomputable abbrev dotWeight (i : Seq ν) : (Fin m →₀ ℕ) →+ ℤ :=
  Finsupp.weight fun a => G.degX (i.lbl a)

omit [DecidableEq I] in
theorem dotWeight_apply (i : Seq ν) (c : Fin m →₀ ℕ) :
    G.dotWeight i c = ∑ a, (c a : ℤ) * G.degX (i.lbl a) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [nsmul_eq_mul]

variable {G}

theorem completion_ext {f g : G.completion ν}
    (h : ∀ d, (f : HahnSeries ℤ A).coeff d = (g : HahnSeries ℤ A).coeff d) : f = g :=
  Subtype.ext (HahnSeries.ext (funext h))

section Positive

variable (hX : ∀ a, 0 < G.degX a)
include hX

omit [DecidableEq I] in
theorem le_dotWeight (i : Seq ν) (c : Fin m →₀ ℕ) (a : Fin m) :
    (c a : ℤ) ≤ G.dotWeight i c := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  calc (c a : ℤ) ≤ c a • G.degX (i.lbl a) := by
        rw [nsmul_eq_mul]; nlinarith [hX (i.lbl a), (c a).cast_nonneg (α := ℤ)]
    _ ≤ ∑ b, c b • G.degX (i.lbl b) :=
        Finset.single_le_sum (f := fun b => c b • G.degX (i.lbl b))
          (fun b _ => nsmul_nonneg (hX (i.lbl b)).le _) (Finset.mem_univ a)

omit [DecidableEq I] in
theorem dotWeight_nonneg (i : Seq ν) (c : Fin m →₀ ℕ) : 0 ≤ G.dotWeight i c := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_nonneg fun b _ => nsmul_nonneg (hX (i.lbl b)).le _

omit hX in
/-- The exponents bounded by `d` in every variable. -/
noncomputable def exponentBox (d : ℤ) : Finset (Fin m →₀ ℕ) :=
  Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d.toNat)

omit [DecidableEq I] in
theorem mem_exponentBox {i : Seq ν} {c : Fin m →₀ ℕ} {d : ℤ}
    (h : G.dotWeight i c ≤ d) :
    c ∈ exponentBox (ν := ν) d := by
  rw [exponentBox, Finset.mem_Iic]
  intro a
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  have := le_dotWeight hX i c a
  omega

omit hX in
/-- The exponents of weight exactly `d`. -/
noncomputable def weightFiber (G : GradingDatum Q) (i : Seq ν) (d : ℤ) :
    Finset (Fin m →₀ ℕ) :=
  (exponentBox d).filter fun c => G.dotWeight i c = d

omit [DecidableEq I] in
theorem mem_weightFiber {i : Seq ν} {c : Fin m →₀ ℕ} {d : ℤ} :
    c ∈ weightFiber G i d ↔ G.dotWeight i c = d := by
  rw [weightFiber, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨mem_exponentBox hX h.le, h⟩⟩

omit hX in
/-- The element `x^c e_i`. -/
noncomputable abbrev dotMonomial (i : Seq ν) (c : Fin m →₀ ℕ) : A := pol (monomial c 1) * e i

/-- The family `(single (dotWeight c) (F_c x^c e_i))_c`, summable since dots have positive
degree. -/
noncomputable def seriesFamily (i : Seq ν) (F : MvPowerSeries (Fin m) k) :
    SummableFamily ℤ A (Fin m →₀ ℕ) where
  toFun c := single (G.dotWeight i c) (MvPowerSeries.coeff c F • dotMonomial i c)
  isPWO_iUnion_support' := by
    refine Set.IsWF.isPWO (BddBelow.isWF ⟨0, ?_⟩)
    intro d hd
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hd
    have := support_single_subset hc
    rw [Set.mem_singleton_iff] at this
    rw [this]; exact dotWeight_nonneg hX i c
  finite_co_support' d := by
    refine (weightFiber G i d).finite_toSet.subset fun c hc => ?_
    rw [Set.mem_ofPred_eq, coeff_single] at hc
    rw [Finset.mem_coe, mem_weightFiber hX]
    by_contra h
    exact hc (ite_eq_right (Ne.symm h))

/-- The element `F(x) e_i` of the completion, for a power series `F` in the dots. Its degree `d`
coefficient is `∑_{dotWeight(c) = d} F_c x^c e_i` (`coeff_seriesAt`). -/
noncomputable def seriesAt (i : Seq ν) (F : MvPowerSeries (Fin m) k) : G.completion ν :=
  ⟨(seriesFamily hX i F).hsum, fun d => by
    rw [SummableFamily.coeff_hsum_eq_sum_of_subset (t := weightFiber G i d)]
    · refine Submodule.sum_mem _ fun c hc => ?_
      change (single (G.dotWeight i c) _ : HahnSeries ℤ A).coeff d ∈ _
      rw [coeff_single, ite_eq_left ((mem_weightFiber hX).1 hc).symm]
      refine Submodule.smul_mem _ _ ?_
      rw [← (mem_weightFiber hX).1 hc]
      exact G.pol_monomial_mul_e_mem_grade c i
    · intro c hc
      change (single (G.dotWeight i c) _ : HahnSeries ℤ A).coeff d ≠ 0 at hc
      rw [Finset.mem_coe, mem_weightFiber hX]
      by_contra h
      exact hc (by rw [coeff_single, ite_eq_right (Ne.symm h)])⟩

theorem coeff_seriesAt (i : Seq ν) (F : MvPowerSeries (Fin m) k) (d : ℤ) :
    ((seriesAt hX i F : G.completion ν) : HahnSeries ℤ A).coeff d =
      ∑ c ∈ weightFiber G i d, MvPowerSeries.coeff c F • (pol (monomial c 1) * e i : A) := by
  change (seriesFamily hX i F).hsum.coeff d = _
  rw [SummableFamily.coeff_hsum_eq_sum_of_subset (t := weightFiber G i d)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    change (single (G.dotWeight i c) _ : HahnSeries ℤ A).coeff d = _
    rw [coeff_single, ite_eq_left ((mem_weightFiber hX).1 hc).symm]
  · intro c hc
    change (single (G.dotWeight i c) _ : HahnSeries ℤ A).coeff d ≠ 0 at hc
    rw [Finset.mem_coe, mem_weightFiber hX]
    by_contra h
    exact hc (by rw [coeff_single, ite_eq_right (Ne.symm h)])

theorem seriesAt_add (i : Seq ν) (F F' : MvPowerSeries (Fin m) k) :
    seriesAt hX i (F + F') = seriesAt hX i F + seriesAt hX i F' :=
  completion_ext fun d => by
    rw [Subalgebra.coe_add, HahnSeries.coeff_add, coeff_seriesAt, coeff_seriesAt, coeff_seriesAt,
      ← Finset.sum_add_distrib]
    simp only [map_add, add_smul]

theorem seriesAt_smul (i : Seq ν) (r : k) (F : MvPowerSeries (Fin m) k) :
    seriesAt hX i (r • F) = r • seriesAt hX i F :=
  completion_ext fun d => by
    rw [Subalgebra.coe_smul, HahnSeries.coeff_smul, coeff_seriesAt, coeff_seriesAt, Finset.smul_sum]
    simp only [map_smul, smul_eq_mul, mul_smul]

theorem seriesAt_zero (i : Seq ν) : seriesAt hX i (0 : MvPowerSeries (Fin m) k) = 0 := by
  simpa using seriesAt_smul hX i 0 0

omit hX in
theorem dotMonomial_mul_dotMonomial (i : Seq ν) (c c' : Fin m →₀ ℕ) :
    dotMonomial (Q := Q) i c * dotMonomial i c' = dotMonomial i (c + c') := by
  simp only [dotMonomial]
  rw [mul_assoc, ← mul_assoc (e i), (e_commute_pol i _).eq, mul_assoc, e_mul_self, ← mul_assoc,
    ← map_mul, monomial_mul_monomial, one_mul]

theorem seriesAt_mul (i : Seq ν) (F F' : MvPowerSeries (Fin m) k) :
    seriesAt hX i (F * F') = seriesAt hX i F * seriesAt hX i F' := by
  refine completion_ext fun d => ?_
  rw [Subalgebra.coe_mul]
  change _ = ((seriesFamily hX i F).hsum * (seriesFamily hX i F').hsum).coeff d
  have hterm : ∀ p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ),
      ((SummableFamily.mul (seriesFamily hX i F) (seriesFamily hX i F')) p) =
        single (G.dotWeight i p.1 + G.dotWeight i p.2) ((MvPowerSeries.coeff p.1 F *
          MvPowerSeries.coeff p.2 F') • dotMonomial i (p.1 + p.2)) := by
    intro p
    change (single (G.dotWeight i p.1) (MvPowerSeries.coeff p.1 F • dotMonomial i p.1) :
        HahnSeries ℤ A) *
      single (G.dotWeight i p.2) (MvPowerSeries.coeff p.2 F' • dotMonomial i p.2) = _
    rw [single_mul_single, smul_mul_smul_comm, dotMonomial_mul_dotMonomial]
  rw [← SummableFamily.hsum_mul,
    SummableFamily.coeff_hsum_eq_sum_of_subset
      (t := (exponentBox d ×ˢ exponentBox d).filter
        fun p => G.dotWeight i p.1 + G.dotWeight i p.2 = d)]
  · symm
    refine (Finset.sum_congr (g := fun p : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) =>
      (MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 F') • dotMonomial i (p.1 + p.2))
      rfl fun p hp => ?_).trans ?_
    · rw [hterm, coeff_single, ite_eq_left (Finset.mem_filter.1 hp).2.symm]
    rw [coeff_seriesAt]
    simp_rw [MvPowerSeries.coeff_mul, Finset.sum_smul]
    rw [← Finset.sum_fiberwise_of_maps_to (t := weightFiber G i d) (g := fun p => p.1 + p.2)]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hcd := (mem_weightFiber hX).1 hc
      have hS : ((exponentBox d ×ˢ exponentBox d).filter
          fun p => G.dotWeight i p.1 + G.dotWeight i p.2 = d).filter
          (fun p => p.1 + p.2 = c) = antidiagonal c := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
        constructor
        · exact fun h => h.2
        · intro h
          have h1 := dotWeight_nonneg hX i p.1
          have h2 := dotWeight_nonneg hX i p.2
          have h3 : G.dotWeight i p.1 + G.dotWeight i p.2 = d := by rw [← map_add, h, hcd]
          exact ⟨⟨⟨mem_exponentBox hX (i := i) (by omega),
            mem_exponentBox hX (i := i) (by omega)⟩, h3⟩, h⟩
      rw [hS]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [mem_weightFiber hX, map_add, hp.2]
  · intro p hp
    change ((SummableFamily.mul (seriesFamily hX i F) (seriesFamily hX i F')) p).coeff d ≠ 0 at hp
    rw [hterm, coeff_single] at hp
    have h : d = G.dotWeight i p.1 + G.dotWeight i p.2 := by by_contra h; exact hp (ite_eq_right h)
    have h1 := dotWeight_nonneg hX i p.1
    have h2 := dotWeight_nonneg hX i p.2
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨mem_exponentBox hX (i := i) (by omega), mem_exponentBox hX (i := i) (by omega)⟩,
      h.symm⟩

omit hX in
theorem dotMonomial_mem_grade (i : Seq ν) (c : Fin m →₀ ℕ) :
    dotMonomial (Q := Q) i c ∈ G.grade ν (G.dotWeight i c) :=
  G.pol_monomial_mul_e_mem_grade c i

theorem seriesAt_monomial (i : Seq ν) (c : Fin m →₀ ℕ) (r : k) :
    seriesAt hX i (↑(monomial c r : MvPolynomial (Fin m) k)) =
      G.toCompletion (r • dotMonomial i c) := by
  refine completion_ext fun d => ?_
  rw [coeff_seriesAt, map_smul, Subalgebra.coe_smul, HahnSeries.coeff_smul,
    G.coeff_toCompletion_of_mem_grade (dotMonomial_mem_grade i c)]
  simp_rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_monomial, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  by_cases h : d = G.dotWeight i c
  · rw [ite_eq_left ((mem_weightFiber hX).2 h.symm), ite_eq_left h]
  · rw [ite_eq_right fun hc => h ((mem_weightFiber hX).1 hc).symm, ite_eq_right h, smul_zero]

/-- A polynomial `p` in the dots gives the image of `p(x) e_i ∈ R(ν)`. -/
theorem seriesAt_coe (i : Seq ν) (p : MvPolynomial (Fin m) k) :
    seriesAt hX i (↑p : MvPowerSeries (Fin m) k) = G.toCompletion (pol p * e i) := by
  induction p using MvPolynomial.induction_on' with
  | monomial c r =>
    rw [seriesAt_monomial, dotMonomial, ← smul_mul_assoc, ← map_smul, smul_monomial,
      smul_eq_mul, mul_one]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, seriesAt_add, hp, hq, map_add, add_mul, map_add]

/-- `1(x) e_i = e_i`. -/
theorem seriesAt_one (i : Seq ν) :
    seriesAt hX i (1 : MvPowerSeries (Fin m) k) = G.toCompletion (e i) := by
  rw [← MvPolynomial.coe_one, seriesAt_coe, map_one, one_mul]

/-- `e_{i'} · F(x) e_i = δ_{i' i} F(x) e_i`. -/
theorem toCompletion_e_mul_seriesAt (i' i : Seq ν) (F : MvPowerSeries (Fin m) k) :
    G.toCompletion (e i') * seriesAt hX i F = if i' = i then seriesAt hX i F else 0 := by
  have key : ∀ c, (e i' : A) * dotMonomial i c = if i' = i then dotMonomial i c else 0 := by
    intro c
    rw [dotMonomial, ← mul_assoc, (e_commute_pol i' _).eq, mul_assoc, e_mul_e]
    rcases eq_or_ne i' i with rfl | h <;> simp [*]
  split_ifs with h
  · subst h
    refine completion_ext fun d => ?_
    rw [Subalgebra.coe_mul, G.coe_toCompletion_of_mem_grade (G.e_mem_grade i'),
      coeff_single_zero_mul, coeff_seriesAt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_smul_comm, key, ite_eq_left rfl]
  · refine completion_ext fun d => ?_
    rw [Subalgebra.coe_mul, G.coe_toCompletion_of_mem_grade (G.e_mem_grade i'),
      coeff_single_zero_mul, coeff_seriesAt, Finset.mul_sum, ZeroMemClass.coe_zero,
      HahnSeries.coeff_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [mul_smul_comm, key, ite_eq_right h, smul_zero]

/-- `F(x) e_i · e_{i'} = δ_{i i'} F(x) e_i`. -/
theorem seriesAt_mul_toCompletion_e (i i' : Seq ν) (F : MvPowerSeries (Fin m) k) :
    seriesAt hX i F * G.toCompletion (e i') = if i = i' then seriesAt hX i F else 0 := by
  have key : ∀ c, dotMonomial (Q := Q) i c * e i' = if i = i' then dotMonomial i c else 0 := by
    intro c
    rw [dotMonomial, mul_assoc, e_mul_e]
    rcases eq_or_ne i i' with rfl | h <;> simp [*]
  split_ifs with h
  · subst h
    refine completion_ext fun d => ?_
    rw [Subalgebra.coe_mul, G.coe_toCompletion_of_mem_grade (G.e_mem_grade i),
      coeff_mul_single_zero, coeff_seriesAt, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_mul_assoc, key, ite_eq_left rfl]
  · refine completion_ext fun d => ?_
    rw [Subalgebra.coe_mul, G.coe_toCompletion_of_mem_grade (G.e_mem_grade i'),
      coeff_mul_single_zero, coeff_seriesAt, Finset.sum_mul, ZeroMemClass.coe_zero,
      HahnSeries.coeff_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [smul_mul_assoc, key, ite_eq_right h, smul_zero]

/-- If the constant term of `F` is a unit `u`, then `F(x) e_i` is invertible in the corner
`e_i R̂(ν) e_i`, with inverse `F⁻¹(x) e_i`. -/
theorem seriesAt_mul_seriesAt_invOfUnit (i : Seq ν) (F : MvPowerSeries (Fin m) k) (u : kˣ)
    (hu : MvPowerSeries.constantCoeff F = u) :
    seriesAt hX i F * seriesAt hX i (F.invOfUnit u) = G.toCompletion (e i) := by
  rw [← seriesAt_mul, MvPowerSeries.mul_invOfUnit F u hu, seriesAt_one]

theorem seriesAt_invOfUnit_mul_seriesAt (i : Seq ν) (F : MvPowerSeries (Fin m) k) (u : kˣ)
    (hu : MvPowerSeries.constantCoeff F = u) :
    seriesAt hX i (F.invOfUnit u) * seriesAt hX i F = G.toCompletion (e i) := by
  rw [← seriesAt_mul, MvPowerSeries.invOfUnit_mul F u hu, seriesAt_one]

/-- Dots act on `F(x) e_i` by multiplication by the variable: `x_a · F(x) e_i = (X_a F)(x) e_i`. -/
theorem toCompletion_x_mul_seriesAt (i : Seq ν) (a : Fin m) (F : MvPowerSeries (Fin m) k) :
    G.toCompletion (x a) * seriesAt hX i F = seriesAt hX i (MvPowerSeries.X a * F) := by
  rw [seriesAt_mul, ← MvPolynomial.coe_X, seriesAt_coe, pol_X, map_mul, mul_assoc,
    toCompletion_e_mul_seriesAt, ite_eq_left rfl]

/-- `F(x) e_i · x_a = (F X_a)(x) e_i`. -/
theorem seriesAt_mul_toCompletion_x (i : Seq ν) (a : Fin m) (F : MvPowerSeries (Fin m) k) :
    seriesAt hX i F * G.toCompletion (x a) = seriesAt hX i (F * MvPowerSeries.X a) := by
  rw [seriesAt_mul, ← MvPolynomial.coe_X, seriesAt_coe, pol_X, x_mul_e, map_mul, ← mul_assoc,
    seriesAt_mul_toCompletion_e, ite_eq_left rfl]

end Positive

end GradingDatum

end Categorification.KLR
