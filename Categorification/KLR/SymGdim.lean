/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.GradedFree

/-!
# The graded dimension `(ν)_q` of `Sym(ν)`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, display after equation `eq_bil_pair2`:

  `(ν)_q = gdim Sym(ν) = ∏_{i} ∏_{a=1}^{ν_i} 1 / (1 - q^{2a})`.

## Polynomial invariants of Young subgroups

Let `lab : Fin n → J` label the variables of `k[x_1, …, x_n]` and grade them by
`deg x_v = wt (lab v) > 0` (weights constant on the fibres of `lab`). For the Young subgroup
`G_lab` of label-preserving permutations:

* the weighted homogeneous components of a `G_lab`-invariant polynomial are invariant
  (`weightedHomogeneousComponent_mem_labelInvariants`), so the invariants form a graded
  subspace `invGrade`;
* `k[x]` has a basis over the invariants consisting of monomials, whose degree generating
  function is `∏_c ∏_{a=1}^{n_c} [a]_{q^{wt c}}` (`exists_graded_monomial_isInvBasis_fibres`,
  a graded refinement of the parabolic Artin theorem);
* hence `k[x] ≅ ⨁_β k[x]^{G_lab} · b_β` as graded spaces, and
  `gdim k[x] = gdim k[x]^{G_lab} · ∑_β q^{deg b_β}` (`gdim_polGrade_eq_mul`); with
  `gdim k[x] = ∏_v (1 - q^{wt(lab v)})⁻¹` (`gdim_polGrade`) this gives

  `gdim k[x]^{G_lab} = ∏_c ∏_{a=1}^{n_c} (1 - q^{a · wt c})⁻¹` (`gdim_invGrade`).

## `Sym(ν)`

`Sym(ν) = Pol(ν)^{S_m}` sits in `R(ν)` through `polNu`, and inherits the grading of `R(ν)`
(`GradingDatum.symGrade`). Evaluation at a sequence `i` identifies it, degree by degree, with
the invariants of the stabiliser of `i` graded by `deg x_a = degX(i_a)`
(`GradingDatum.finrank_symGrade`). Hence (`GradingDatum.gdim_symGrade`)

  `gdim Sym(ν) = ∏_{c ∈ supp ν} ∏_{a=1}^{ν_c} (1 - q^{a · degX c})⁻¹`,

and for KL I (`degX = 2`, `KL1.gdim_symGrade`) this is the paper's `(ν)_q`. By KL I,
Theorem 2.9 (`center_eq`), the same holds for the center of `R(ν)` (`GradingDatum.gdim_center`).
-/

open Equiv MvPolynomial

namespace Categorification

open Graded DirectSum Module

/-! ### Laurent series identities -/

section Series

/-- The `q`-integer `[N]_{q^w} = ∑_{t < N} q^{t w}`. -/
noncomputable def qStair (w : ℤ) (N : ℕ) : LaurentSeries ℤ :=
  ∑ t ∈ Finset.range N, HahnSeries.single ((t : ℤ) * w) 1

theorem qStair_mul_one_sub (w : ℤ) (N : ℕ) :
    qStair w N * (1 - HahnSeries.single w 1) = 1 - HahnSeries.single ((N : ℤ) * w) 1 := by
  induction N with
  | zero => simp [qStair, HahnSeries.single_zero_one]
  | succ N ih =>
    rw [qStair, Finset.sum_range_succ, add_mul, ← qStair, ih, mul_sub, mul_one,
      HahnSeries.single_mul_single, one_mul]
    push_cast
    rw [show (N : ℤ) * w + w = (N + 1) * w by ring]
    abel

theorem prod_single_one {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ a ∈ s, (HahnSeries.single (R := ℤ) (f a) 1 : LaurentSeries ℤ) =
      HahnSeries.single (R := ℤ) (∑ a ∈ s, f a) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HahnSeries.single_zero_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, HahnSeries.single_mul_single, one_mul]

/-- The generating function of the staircase `{u | u_a ≤ a}` with weight `w`:
`∑_u q^{w ∑_a u_a} = ∏_{a < N} [a + 1]_{q^w}`. -/
theorem sum_staircase_single (N : ℕ) (w : ℤ) [Fintype {u : Fin N → ℕ // ∀ a, u a ≤ a}] :
    ∑ u : {u : Fin N → ℕ // ∀ a, u a ≤ a},
      (HahnSeries.single (∑ a, ((u : Fin N → ℕ) a : ℤ) * w) 1 : LaurentSeries ℤ) =
      ∏ a : Fin N, qStair w (a + 1) := by
  classical
  simp only [qStair]
  rw [Finset.prod_univ_sum]
  simp only [prod_single_one]
  refine (Finset.sum_subtype (Fintype.piFinset fun a : Fin N => Finset.range (a + 1))
    (fun u => ?_) (fun x : Fin N → ℕ =>
      (HahnSeries.single (R := ℤ) (∑ a, ((x a : ℕ) : ℤ) * w) 1 : LaurentSeries ℤ))).symm
  simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

end Series

/-! ### Graded invariants of Young subgroups -/

section YoungHilbert

variable (k : Type*) [Field k] {n : ℕ} {J : Type*} (lab : Fin n → J) (wt : J → ℤ)

/-- The grading of `k[x_1, …, x_n]` by `deg x_v = wt (lab v)`. -/
abbrev polGrade : ℤ → Submodule k (MvPolynomial (Fin n) k) :=
  weightedHomogeneousSubmodule k (fun v => wt (lab v))

/-- The graded pieces of the invariants of the Young subgroup `G_lab`. -/
noncomputable def invGrade (d : ℤ) : Submodule k (MvPolynomial (Fin n) k) :=
  polGrade k lab wt d ⊓ Subalgebra.toSubmodule (labelInvariants k lab)

variable {k lab wt}

theorem coe_decompose_polGrade (p : MvPolynomial (Fin n) k) (d : ℤ) :
    letI := weightedGradedAlgebra k (fun v => wt (lab v))
    (decompose (polGrade k lab wt) p d : MvPolynomial (Fin n) k) =
      weightedHomogeneousComponent (fun v => wt (lab v)) d p :=
  weightedDecomposition.decompose'_apply k _ p d

/-- Label-preserving renamings preserve the weighted degree. -/
theorem rename_mem_polGrade {g : Perm (Fin n)} (hg : lab ∘ g = lab)
    {p : MvPolynomial (Fin n) k} {d : ℤ} (hp : p ∈ polGrade k lab wt d) :
    rename g p ∈ polGrade k lab wt d := by
  rw [mem_weightedHomogeneousSubmodule] at hp ⊢
  rw [p.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun u hu => ?_
  rw [rename_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← hp (mem_support_iff.1 hu), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [show lab (g v) = lab v from congrFun hg v]

/-- Weighted homogeneous components commute with label-preserving renamings. -/
theorem weightedHomogeneousComponent_rename {g : Perm (Fin n)} (hg : lab ∘ g = lab)
    (p : MvPolynomial (Fin n) k) (d : ℤ) :
    weightedHomogeneousComponent (fun v => wt (lab v)) d (rename g p) =
      rename g (weightedHomogeneousComponent (fun v => wt (lab v)) d p) := by
  letI := weightedGradedAlgebra k (fun v => wt (lab v))
  have := decompose_map (ℳ := polGrade k lab wt) (𝒩 := polGrade k lab wt)
    (f := (rename g : MvPolynomial (Fin n) k →ₐ[k] _).toLinearMap)
    (fun _ _ hx => rename_mem_polGrade (wt := wt) hg hx) p d
  rw [coe_decompose_polGrade, coe_decompose_polGrade] at this
  exact this

/-- The weighted homogeneous components of an invariant polynomial are invariant. -/
theorem weightedHomogeneousComponent_mem_labelInvariants {p : MvPolynomial (Fin n) k}
    (hp : p ∈ labelInvariants k lab) (d : ℤ) :
    weightedHomogeneousComponent (fun v => wt (lab v)) d p ∈ labelInvariants k lab :=
  fun g hg => by rw [← weightedHomogeneousComponent_rename hg, hp g hg]

/-! #### The graded dimension of `k[x]` -/

theorem monomial_mem_polGrade (u : Fin n →₀ ℕ) :
    (MvPolynomial.basisMonomials (Fin n) k) u ∈
      polGrade k lab wt (Finsupp.weight (fun v => wt (lab v)) u) := by
  rw [coe_basisMonomials]
  exact isWeightedHomogeneous_monomial _ _ _ rfl

theorem invGrade_le (d : ℤ) : invGrade k lab wt d ≤ polGrade k lab wt d := inf_le_left

theorem span_basisMonomials_univ :
    Submodule.span k ((MvPolynomial.basisMonomials (Fin n) k) '' Set.univ) = ⊤ := by
  rw [Set.image_univ, Basis.span_eq]

variable (hwt : ∀ c, 0 < wt c)
include hwt

theorem hasGdim_polGrade : HasGdim (polGrade k lab wt) := by
  letI := weightedGradedAlgebra k (fun v => wt (lab v))
  have h := hasGdim_inf_span (polGrade k lab wt) (Finsupp.weight (fun v => wt (lab v)))
    monomial_mem_polGrade Set.univ
    (fun d => by simpa using finite_weight_eq (fun v => hwt (lab v)) d)
    ⟨0, by rintro _ ⟨u, -, rfl⟩; exact weight_nonneg (fun v => (hwt (lab v)).le) u⟩
  simp only [span_basisMonomials_univ, inf_top_eq] at h
  exact h

/-- **The graded dimension of the weighted polynomial ring**:
`gdim k[x] = ∏_v (1 - q^{wt(lab v)})⁻¹`. -/
theorem gdim_polGrade : gdim (polGrade k lab wt) = ∏ v, geomSeries (wt (lab v)) := by
  letI := weightedGradedAlgebra k (fun v => wt (lab v))
  have h := fun d => coeff_gdim_inf_span (polGrade k lab wt)
    (Finsupp.weight (fun v => wt (lab v))) (MvPolynomial.basisMonomials (Fin n) k).linearIndependent
    monomial_mem_polGrade Set.univ
    (fun d => by simpa using finite_weight_eq (fun v => hwt (lab v)) d)
    ⟨0, by rintro _ ⟨u, -, rfl⟩; exact weight_nonneg (fun v => (hwt (lab v)).le) u⟩ d
  simp only [span_basisMonomials_univ, inf_top_eq, Set.mem_univ, true_and] at h
  ext d
  rw [h d, coeff_prod_geomSeries _ (fun v => hwt (lab v))]

theorem hasGdim_invGrade : HasGdim (invGrade k lab wt) := by
  haveI := hasGdim_polGrade (k := k) (lab := lab) hwt
  exact {
    finiteDimensional := fun d => Submodule.finiteDimensional_of_le (invGrade_le d)
    bddBelow := BddBelow.mono (t := {d | polGrade k lab wt d ≠ ⊥})
      (fun d (hd : invGrade k lab wt d ≠ ⊥) (h : polGrade k lab wt d = ⊥) => hd (by
        rw [eq_bot_iff, ← h]; exact invGrade_le d)) HasGdim.bddBelow }

end YoungHilbert

/-! ### A graded monomial basis over the invariants -/

section Fibres

variable {k : Type*} [Field k] {n : ℕ} {J : Type*} [DecidableEq J] (lab : Fin n → J)
  (wt : J → ℤ)

/-- **Graded parabolic Artin theorem**: for the fibres with labels in `T`, a basis `b` of `k[x]`
over the invariants of the fibre groups consisting of homogeneous elements (monomials), of
degrees `δ`, with degree generating function `∏_{c ∈ T} ∏_{a < n_c} [a + 1]_{q^{wt c}}`. -/
theorem exists_graded_monomial_isInvBasis_fibres (T : Finset J) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → MvPolynomial (Fin n) k) (δ : ι → ℤ),
      IsInvBasis (fibresGroup lab T) b ∧ (∀ β, b β ∈ polGrade k lab wt (δ β)) ∧
      ∑ β, (HahnSeries.single (R := ℤ) (δ β) 1 : LaurentSeries ℤ) =
        ∏ c ∈ T, ∏ a : Fin (Fintype.card {v // lab v = c}), qStair (wt c) (a + 1) := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, ?_, fun _ => ?_, by
      simp [HahnSeries.single_zero_one]⟩
    · rw [fibresGroup_empty]; exact IsInvBasis.empty
    · exact isWeightedHomogeneous_one k _
  | @insert c T hcT ih =>
    obtain ⟨ι, _, b, δ, hb, hδ, hsum⟩ := ih
    let e : Fin (Fintype.card {v // lab v = c}) → Fin n :=
      fun a => ((Fintype.equivFin {v // lab v = c}).symm a : Fin n)
    have he : ∀ a, lab (e a) = c := fun a => ((Fintype.equivFin {v // lab v = c}).symm a).2
    refine ⟨ι × {u : Fin (Fintype.card {v // lab v = c}) → ℕ // ∀ a, u a ≤ a}, inferInstance,
      fun q => b q.1 * ∏ a, X (e a) ^ q.2.1 a,
      fun q => δ q.1 + ∑ a, ((q.2.1 a : ℕ) : ℤ) * wt c, ?_, fun q => ?_, ?_⟩
    · rw [fibresGroup_insert]
      refine IsInvBasis.mul hb (isInvBasis_fibre k (lab · = c)) (fun u => ?_) ?_
      · exact isInvariant_prod_fibre lab hcT _ he _
      · rintro g ⟨c', hc', hg⟩ g' hg'
        exact fibreGroup_commute lab (fun h : c' = c => hcT (h ▸ hc')) hg hg'
    · have h1 : IsWeightedHomogeneous (fun v => wt (lab v)) (∏ a, X (e a) ^ q.2.1 a : MvPolynomial
          (Fin n) k) (∑ a, ((q.2.1 a : ℕ) : ℤ) * wt c) := by
        have := IsWeightedHomogeneous.prod (R := k) Finset.univ (fun a => X (e a) ^ q.2.1 a)
          (fun a => q.2.1 a • wt c) (w := fun v => wt (lab v)) (fun a _ => by
            have h := (isWeightedHomogeneous_X k (fun v => wt (lab v)) (e a)).pow (q.2.1 a)
            rwa [he a] at h)
        simpa [nsmul_eq_mul] using this
      exact (hδ q.1).mul h1
    · rw [Finset.prod_insert hcT, ← hsum, ← sum_staircase_single, Fintype.sum_prod_type,
        mul_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [HahnSeries.single_mul_single, one_mul]

end Fibres

/-! ### Graded freeness of `k[x]` over the invariants -/

section Free

variable {k : Type*} [Field k] {n : ℕ} {J : Type*} {lab : Fin n → J} {wt : J → ℤ}
  (hwt : ∀ c, 0 < wt c) {ι : Type*} [Fintype ι] {b : ι → MvPolynomial (Fin n) k} {δ : ι → ℤ}
  (hind : ∀ g : ι → MvPolynomial (Fin n) k, (∀ β, g β ∈ labelInvariants k lab) →
    ∑ β, g β * b β = 0 → ∀ β, g β = 0)
  (hspan : ∀ p : MvPolynomial (Fin n) k, ∃ g : ι → MvPolynomial (Fin n) k,
    (∀ β, g β ∈ labelInvariants k lab) ∧ ∑ β, g β * b β = p)
  (hb : ∀ β, b β ∈ polGrade k lab wt (δ β))
include hwt hind hspan hb

/-- **`k[x]` is graded free over the invariants**: `k[x]_D ≅ ⨁_β (k[x]^{G_lab})_{D - δ β}`. -/
theorem finrank_polGrade_eq_sum (D : ℤ) :
    finrank k (polGrade k lab wt D) = ∑ β, finrank k (invGrade k lab wt (D - δ β)) := by
  letI := weightedGradedAlgebra k (fun v => wt (lab v))
  haveI := hasGdim_invGrade (k := k) (lab := lab) hwt
  let Φ : ((β : ι) → invGrade k lab wt (D - δ β)) →ₗ[k] polGrade k lab wt D :=
    { toFun := fun g => ⟨∑ β, (g β : MvPolynomial (Fin n) k) * b β, Submodule.sum_mem _
          fun β _ => by
            have := SetLike.GradedMul.mul_mem (g β).2.1 (hb β)
            rwa [sub_add_cancel] at this⟩
      map_add' := fun g h => Subtype.ext (by
        simp only [Pi.add_apply, Submodule.coe_add, add_mul, Finset.sum_add_distrib])
      map_smul' := fun c g => Subtype.ext (by
        simp only [Pi.smul_apply, Submodule.coe_smul, smul_mul_assoc, Finset.smul_sum,
          RingHom.id_apply]) }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro g hg
    have h0 : ∑ β, (g β : MvPolynomial (Fin n) k) * b β = 0 := congrArg Subtype.val hg
    have := hind (fun β => g β) (fun β => (g β).2.2) h0
    exact (Submodule.mem_bot k).2 (funext fun β => Subtype.ext (this β))
  have hsurj : Function.Surjective Φ := by
    intro p
    obtain ⟨g, hg, hgp⟩ := hspan p
    refine ⟨fun β => ⟨weightedHomogeneousComponent (fun v => wt (lab v)) (D - δ β) (g β),
      weightedHomogeneousComponent_mem _ _ _,
      weightedHomogeneousComponent_mem_labelInvariants (hg β) _⟩, Subtype.ext ?_⟩
    show ∑ β, weightedHomogeneousComponent (fun v => wt (lab v)) (D - δ β) (g β) * b β = p
    rw [← decompose_of_mem_same (polGrade k lab wt) p.2, ← hgp, decompose_sum,
      DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    have := coe_decompose_mul_add_of_right_mem (polGrade k lab wt) (a := g β) (i := D - δ β)
      (hb β)
    rw [sub_add_cancel] at this
    rw [this, coe_decompose_polGrade]
  rw [← (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]

/-- In generating functions: `gdim k[x] = gdim k[x]^{G_lab} · ∑_β q^{δ β}`. -/
theorem gdim_polGrade_eq_mul :
    gdim (polGrade k lab wt) =
      gdim (invGrade k lab wt) * ∑ β, (HahnSeries.single (R := ℤ) (δ β) 1 : LaurentSeries ℤ) := by
  haveI := hasGdim_polGrade (k := k) (lab := lab) hwt
  haveI := hasGdim_invGrade (k := k) (lab := lab) hwt
  ext D
  rw [coeff_gdim, finrank_polGrade_eq_sum hwt hind hspan hb, Finset.mul_sum, HahnSeries.coeff_sum,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have := HahnSeries.coeff_single_mul_add (r := (1 : ℤ)) (x := gdim (invGrade k lab wt))
    (a := D - δ β) (b := δ β)
  rw [sub_add_cancel] at this
  rw [mul_comm, this, one_mul, coeff_gdim]

end Free

/-! ### The graded dimension of the invariants of a Young subgroup -/

section Main

noncomputable local instance : CommRing (LaurentSeries ℤ) :=
  inferInstanceAs (CommRing (HahnSeries ℤ ℤ))

variable {k : Type*} [Field k] {n : ℕ} {J : Type*} [DecidableEq J] (lab : Fin n → J)
  (wt : J → ℤ)

/-- **Hilbert series of the invariants of a Young subgroup**: for weights `deg x_v = wt(lab v)`
with `wt > 0`,
`gdim k[x]^{G_lab} = ∏_{c} ∏_{a=1}^{n_c} (1 - q^{a · wt c})⁻¹`, `n_c = #lab⁻¹(c)`. -/
theorem gdim_invGrade (hwt : ∀ c, 0 < wt c) :
    gdim (invGrade k lab wt) = ∏ c ∈ Finset.univ.image lab,
      ∏ a : Fin (Fintype.card {v // lab v = c}), geomSeries (((a : ℕ) + 1 : ℕ) * wt c) := by
  classical
  obtain ⟨ι, _, b, δ, hb, hδ, hsum⟩ :=
    exists_graded_monomial_isInvBasis_fibres (k := k) lab wt (Finset.univ.image lab)
  have hmul := gdim_polGrade_eq_mul hwt
    (fun g hg => hb.indep g fun i => (isInvariant_fibresGroup_iff lab).2 (hg i))
    (fun p => by
      obtain ⟨g, hg, hgp⟩ := hb.span p
      exact ⟨g, fun i => (isInvariant_fibresGroup_iff lab).1 (hg i), hgp⟩) hδ
  rw [gdim_polGrade hwt, hsum] at hmul
  set H := gdim (invGrade k lab wt)
  set E := ∏ v, (1 - HahnSeries.single (R := ℤ) (wt (lab v)) 1 : LaurentSeries ℤ)
  set Pz := ∏ c ∈ Finset.univ.image lab, ∏ a : Fin (Fintype.card {v // lab v = c}),
    (1 - HahnSeries.single (R := ℤ) ((((a : ℕ) + 1 : ℕ) : ℤ) * wt c) 1 : LaurentSeries ℤ)
  have hP : (∏ v, geomSeries (wt (lab v))) * E = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun v _ => by rw [mul_comm, one_sub_mul_geomSeries (hwt _)]
  have hS : (∏ c ∈ Finset.univ.image lab, ∏ a : Fin (Fintype.card {v // lab v = c}),
      qStair (wt c) (a + 1)) * E = Pz := by
    simp only [E, Pz]
    rw [Finset.prod_comp (fun c => (1 - HahnSeries.single (R := ℤ) (wt c) 1 : LaurentSeries ℤ))
      lab, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [show (Finset.univ.filter fun v => lab v = c).card = Fintype.card {v // lab v = c} from
      (Fintype.card_subtype _).symm, ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [qStair_mul_one_sub]
  have hT : (∏ c ∈ Finset.univ.image lab, ∏ a : Fin (Fintype.card {v // lab v = c}),
      geomSeries (((a : ℕ) + 1 : ℕ) * wt c)) * Pz = 1 := by
    simp only [Pz]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [mul_comm, one_sub_mul_geomSeries (mul_pos (by positivity) (hwt c))]
  calc H = H * ((∏ c ∈ Finset.univ.image lab, ∏ a : Fin (Fintype.card {v // lab v = c}),
        geomSeries (((a : ℕ) + 1 : ℕ) * wt c)) * Pz) := by rw [hT, mul_one]
    _ = (∏ c ∈ Finset.univ.image lab, ∏ a : Fin (Fintype.card {v // lab v = c}),
        geomSeries (((a : ℕ) + 1 : ℕ) * wt c)) * ((∏ v, geomSeries (wt (lab v))) * E) := by
          rw [← hS, hmul]; ring
    _ = _ := by rw [hP, mul_one]

end Main

/-! ### `Sym(ν)` -/

theorem isWeightedHomogeneous_rename {V W : Type*} {k : Type*} [CommSemiring k] {w : V → ℤ}
    {w' : W → ℤ} (σ : V → W) (hσ : ∀ v, w' (σ v) = w v) {p : MvPolynomial V k} {d : ℤ}
    (hp : p.IsWeightedHomogeneous w d) : (rename σ p).IsWeightedHomogeneous w' d := by
  rw [p.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun u hu => ?_
  rw [rename_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← hp (mem_support_iff.1 hu), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
  exact Finsupp.sum_congr fun v _ => by rw [hσ]

namespace KLR

open TypeA KLRAlgebra PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) {ν : Multiset I}

variable (k Q ν) in
/-- `Sym(ν) = polNu (Pol(ν)^{S_m}) ⊆ R(ν)`, as a `k`-subspace. -/
noncomputable def symSub : Submodule k (KLRAlgebra k Q ν) :=
  Subalgebra.toSubmodule ((symNu k ν).map polNu)

namespace GradingDatum

/-- The graded pieces `Sym(ν)_d = R(ν)_d ∩ Sym(ν)`. -/
noncomputable def symGrade (d : ℤ) : Submodule k (KLRAlgebra k Q ν) :=
  G.grade ν d ⊓ symSub k Q ν

theorem polNu_mem_grade_of_apply {f : Pol k ν} (hf : f ∈ symNu k ν) (i : Seq ν) {d : ℤ}
    (hfi : f i ∈ polGrade k i.1 G.degX d) : (polNu f : KLRAlgebra k Q ν) ∈ G.grade ν d := by
  rw [polNu_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : f j = rename (Seq.toPerm i j) (f i) := by
    conv_lhs => rw [← Seq.toPerm_smul i j]
    exact hf _ i
  rw [hj]
  refine G.pol_mul_e_mem_grade j (isWeightedHomogeneous_rename _ (fun a => ?_) hfi)
  have h := congrArg (fun s : Seq ν => s.1 (Seq.toPerm i j a)) (Seq.toPerm_smul i j)
  simp only [Seq.smul_apply, Equiv.symm_apply_apply] at h
  simp only [Seq.lbl, ← h]

include hPQ hP in
theorem apply_mem_polGrade_of_polNu {f : Pol k ν} (i : Seq ν) {d : ℤ}
    (hr : (polNu f : KLRAlgebra k Q ν) ∈ G.grade ν d) : f i ∈ polGrade k i.1 G.degX d := by
  classical
  have h1 : (pol (f i) * e i : KLRAlgebra k Q ν) ∈ G.grade ν d := by
    have := SetLike.GradedMul.mul_mem hr (G.e_mem_grade i)
    rwa [add_zero, polNu_mul_e] at this
  let ρ : Perm (Fin (Multiset.card ν)) → List ℕ := fun w => canWord _ w
  have hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w :=
    fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let c : Perm (Fin (Multiset.card ν)) → Pol k ν := fun w => if w = 1 then Pi.single i (f i) else 0
  have hc : ∑ w, ψw (ρ w) * polNu (c w) = (pol (f i) * e i : KLRAlgebra k Q ν) := by
    rw [Finset.sum_eq_single 1 (fun w _ hw => by simp [c, hw]) (by simp)]
    simp only [c, if_pos rfl, ρ, canWord_one, ψw_nil, one_mul, polNu_single]
  have := G.rightExpansion_isWeightedHomogeneous hPQ hP ρ hρ h1 hc 1 i
  simp only [c, if_pos rfl, Pi.single_eq_same, ρ, canWord_one, degW, sub_zero] at this
  exact this

/-- The subspace of `Sym(ν)` of elements whose `i`-component has degree `d`. -/
noncomputable def symDeg (i : Seq ν) (d : ℤ) : Submodule k (symNu k ν) :=
  (polGrade k i.1 G.degX d).comap ((LinearMap.proj i).comp (symNu k ν).val.toLinearMap)

include hPQ hP in
theorem symGrade_eq_map (i : Seq ν) (d : ℤ) :
    G.symGrade d = (G.symDeg i d).map
      ((polNu : Pol k ν →ₐ[k] KLRAlgebra k Q ν).toLinearMap.comp (symNu k ν).val.toLinearMap) := by
  ext r
  simp only [symGrade, symSub, Submodule.mem_inf, Subalgebra.mem_toSubmodule, Subalgebra.mem_map,
    Submodule.mem_map, symDeg, Submodule.mem_comap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val, LinearMap.coe_proj, Function.eval]
  constructor
  · rintro ⟨hr, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, G.apply_mem_polGrade_of_polNu hPQ hP i hr, rfl⟩
  · rintro ⟨⟨f, hf⟩, hfi, rfl⟩
    exact ⟨G.polNu_mem_grade_of_apply hf i hfi, f, hf, rfl⟩

theorem invGrade_eq_map (i : Seq ν) (d : ℤ) :
    invGrade k i.1 G.degX d = (G.symDeg i d).map
      ((LinearMap.proj i).comp (symNu k ν).val.toLinearMap) := by
  ext p
  simp only [invGrade, Submodule.mem_inf, Subalgebra.mem_toSubmodule, Submodule.mem_map, symDeg,
    Submodule.mem_comap, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Subalgebra.coe_val, LinearMap.coe_proj, Function.eval]
  constructor
  · rintro ⟨hp, hpi⟩
    refine ⟨⟨liftInv i p, liftInv_mem hpi⟩, ?_, liftInv_self hpi⟩
    show liftInv i p i ∈ _
    rw [liftInv_self hpi]; exact hp
  · rintro ⟨⟨f, hf⟩, hfi, rfl⟩
    exact ⟨hfi, apply_mem_labelInvariants hf i⟩

include hPQ hP in
/-- `dim Sym(ν)_d = dim (k[x]^{G_i})_d`, the invariants of the stabiliser of `i` graded by
`deg x_a = degX(i_a)`. -/
theorem finrank_symGrade (i : Seq ν) (d : ℤ) :
    finrank k (G.symGrade (ν := ν) d) = finrank k (invGrade k i.1 G.degX d) := by
  rw [G.symGrade_eq_map hPQ hP i d, G.invGrade_eq_map i d,
    ← ((G.symDeg i d).equivMapOfInjective _
      (fun f g h => Subtype.ext (polNu_injective hPQ h))).finrank_eq,
    ← ((G.symDeg i d).equivMapOfInjective _ (fun f g h => Subtype.ext (by
      rw [eq_liftInv f.2 i, eq_liftInv g.2 i]
      exact congrArg _ h))).finrank_eq]

include hPQ hP in
/-- **`(ν)_q = gdim Sym(ν)`** (KL I, §2.5), for any grading datum with dots of positive degree:
`gdim Sym(ν) = ∏_{c ∈ supp ν} ∏_{a=1}^{ν_c} (1 - q^{a · degX c})⁻¹`. -/
theorem gdim_symGrade (hX : ∀ a, 0 < G.degX a) :
    gdim (G.symGrade (ν := ν)) = ∏ c ∈ ν.toFinset, ∏ a ∈ Finset.range (ν.count c),
      geomSeries (((a + 1 : ℕ) : ℤ) * G.degX c) := by
  classical
  let i : Seq ν := Classical.arbitrary _
  rw [gdim_eq_of_finrank_eq (G.finrank_symGrade hPQ hP i), gdim_invGrade i.1 G.degX hX]
  have himage : Finset.univ.image i.1 = ν.toFinset := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset]
    constructor
    · rintro ⟨a, rfl⟩; exact i.mem a
    · intro hc
      rw [← i.2, Multiset.mem_map] at hc
      obtain ⟨a, -, ha⟩ := hc
      exact ⟨a, ha⟩
  rw [himage]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_eq_prod_range (fun a => geomSeries (((a + 1 : ℕ) : ℤ) * G.degX c))]
  congr 1
  rw [KL1.count_eq_card i c, Fintype.card_subtype]

include hPQ hP in
/-- The same for the center `Z(R(ν)) = Sym(ν)` (KL I, Theorem 2.9). -/
theorem gdim_center (hX : ∀ a, 0 < G.degX a) :
    gdim (fun d => (G.grade ν d ⊓ Subalgebra.toSubmodule (Subalgebra.center k
      (KLRAlgebra k Q ν)) : Submodule k (KLRAlgebra k Q ν))) =
      ∏ c ∈ ν.toFinset, ∏ a ∈ Finset.range (ν.count c),
        geomSeries (((a + 1 : ℕ) : ℤ) * G.degX c) := by
  rw [← G.gdim_symGrade hPQ hP hX]
  congr 1
  funext d
  rw [symGrade, symSub, center_eq hPQ hP]

end GradingDatum

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- **KL I, §2.5**: `(ν)_q = gdim Sym(ν) = ∏_i ∏_{a=1}^{ν_i} (1 - q^{2a})⁻¹`. -/
theorem gdim_symGrade :
    gdim ((klGradingDatum k Γ).symGrade (ν := ν)) = ∏ c ∈ ν.toFinset,
      ∏ a ∈ Finset.range (ν.count c), geomSeries (2 * ((a + 1 : ℕ) : ℤ)) := by
  rw [(klGradingDatum k Γ).gdim_symGrade (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) degX_pos]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun a _ => ?_
  rw [mul_comm]
  rfl

end KL1

end KLR

end Categorification
