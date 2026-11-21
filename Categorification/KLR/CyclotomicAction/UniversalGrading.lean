/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.UniversalFlat
import Categorification.KLR.CyclotomicFinite
import Categorification.KLR.Grading
import Categorification.Algebra.CoactionGrading
import Categorification.Algebra.Graded.QuotientAlgebra
import Categorification.Algebra.Graded.FreeOfProjective

/-!
# `Ř^λ` is free over `Ř^λ_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
**Corollary 3.26**: the universal cyclotomic quotient `Ř^λ_ν` is a free module over the
polynomial ring `Ř^λ_λ = k[e_n(p_j)]` (`UnivCyc.free`), for a field `k` and `Q` of Webster's form.

The proof is graded: `Ř^λ` is graded with `e_n(p_j)` in the degree
`n · ⟨α_j, α_j⟩` of `y^n` on a `j`-strand, so that the universal cyclotomic polynomials
`y^{λ^j} - e_1(p_j) y^{λ^j - 1} + ⋯` are homogeneous. A finitely generated graded projective
module over a positively graded polynomial ring is free (graded Nakayama,
`Graded.free_of_projective`), and `Ř^λ_ν` is finitely generated and projective
(`CycKLR.module_finite`, `UnivCyc.projective`).

The grading is constructed from a coaction. For a grading datum `G` of `Q` (Rouquier's grading,
`IsRouquierQ.gradingDatum`), the coaction of the KLR algebra over `k` (`GradingDatum.coaction`)
is extended to the KLR algebra over `Ř^λ_λ` by letting the scalars act through the coaction
`univCoact` of the polynomial ring, which puts `e_{n+1}(p_j)` in degree `(n + 1) · degX j`
(`univKLRCoact`). Every generator is homogeneous, so this is a grading (`univKLRGradedAlgebra`), and
the cyclotomic relations are homogeneous (`cycElt_mem_univKLRGrade`), so it descends to `Ř^λ_ν`
(`univCycGrade`).
-/

namespace Categorification.KLR.CyclotomicAction

open KLRAlgebra Categorification.Graded

noncomputable section

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] (lam : I → ℕ)
  {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q)

/-! ### The grading of `Ř^λ_λ` -/

/-- The degree of the variable `⟨j, n⟩ = e_{n+1}(p_j)`: that of `y^{n+1}` on a `j`-strand. -/
def univWt (s : Σ j : I, Fin (lam j)) : ℕ := (s.2.val + 1) * (G.degX s.1).toNat

/-- The coaction of `k[ℤ]` on `Ř^λ_λ` defining its grading. -/
def univCoact : UnivCycRing k lam →ₐ[k] AddMonoidAlgebra (UnivCycRing k lam) ℤ :=
  MvPolynomial.aeval fun s => AddMonoidAlgebra.single (univWt lam G s : ℤ) (MvPolynomial.X s)

omit [DecidableEq I] in
theorem univCoact_monomial (s : (Σ j : I, Fin (lam j)) →₀ ℕ) (c : k) :
    univCoact lam G (MvPolynomial.monomial s c) =
      AddMonoidAlgebra.single (Finsupp.weight (univWt lam G) s : ℤ)
        (MvPolynomial.monomial s c) := by
  have h1 : ∀ s, univCoact lam G (MvPolynomial.monomial s (1 : k)) =
      AddMonoidAlgebra.single (Finsupp.weight (univWt lam G) s : ℤ)
        (MvPolynomial.monomial s 1) := by
    intro s
    induction s using Finsupp.induction_linear with
    | zero =>
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, map_one, map_zero, Nat.cast_zero,
        AddMonoidAlgebra.one_def]
    | add s t hs ht =>
      rw [← one_mul (1 : k), ← MvPolynomial.monomial_mul_monomial, map_mul, hs, ht,
        AddMonoidAlgebra.single_mul_single, map_add, Nat.cast_add]
    | single t n =>
      rw [← MvPolynomial.X_pow_eq_monomial, map_pow, univCoact, MvPolynomial.aeval_X,
        AddMonoidAlgebra.single_pow]
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  rw [show MvPolynomial.monomial s c = c • MvPolynomial.monomial s (1 : k) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, h1,
    AddMonoidAlgebra.smul_single]

/-! ### The coaction on the KLR algebra over `Ř^λ_λ` -/

variable (ν : Multiset I)

local notation "R" => UnivCycRing k lam
local notation "A" => KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν
local notation "T" => AddMonoidAlgebra (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) ℤ

omit [DecidableEq I] in
theorem cycQ_map (a b : I) (_ : a ≠ b) :
    MvPolynomial.map (algebraMap k (UnivCycRing k lam)) (Q a b) = cycQ k lam Q a b := rfl

/-- The scalar `k`-algebra structure on the KLR algebra over `Ř^λ_λ`. -/
@[instance_reducible] local instance (priority := low) univKLRAlgebra :
    Algebra k (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :=
  Algebra.compHom _ (algebraMap k (UnivCycRing k lam))

local instance (priority := low) univKLRScalarTower :
    IsScalarTower k (UnivCycRing k lam) (KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The coaction of the KLR algebra over `k`, pushed to the KLR algebra over `Ř^λ_λ`. -/
def univCoactF : KLRAlgebra k Q ν →+* T :=
  (AddMonoidAlgebra.mapRingHom ℤ
    (KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam (Q := Q)))).comp
    (G.coaction (ν := ν)).toRingHom

/-- The scalars of `Ř^λ_λ` act on `T` through the coaction of `Ř^λ_λ`. -/
def univTwist : R →+* T :=
  (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R A)).comp (univCoact lam G).toRingHom

theorem mapRingHom_algebraMap_commute (w : AddMonoidAlgebra R ℤ) (y : T) :
    Commute (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R A) w) y := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add w w' hw hw' => rw [map_add]; exact hw.add_left hw'
  | single a r =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' => exact hy.add_right hy'
    | single b c =>
      rw [AddMonoidAlgebra.mapRingHom_single]
      simp only [Commute, SemiconjBy, AddMonoidAlgebra.single_mul_single, add_comm a b,
        Algebra.commutes]

/-- `T` as an `Ř^λ_λ`-algebra through the coaction of `Ř^λ_λ`. -/
@[instance_reducible] def univTwistAlgebra : Algebra R T :=
  (univTwist lam G ν).toAlgebra' fun _ y => mapRingHom_algebraMap_commute lam ν _ y

omit [DecidableEq I] in
theorem univCoact_algebraMap (c : k) :
    univCoact lam G (algebraMap k R c) = AddMonoidAlgebra.single 0 (algebraMap k R c) := by
  rw [AlgHom.commutes]; rfl

theorem univTwist_algebraMap (c : k) :
    univTwist lam G ν (algebraMap k R c) =
      AddMonoidAlgebra.single 0 (algebraMap R A (algebraMap k R c)) := by
  change AddMonoidAlgebra.mapRingHom ℤ (algebraMap R A) (univCoact lam G (algebraMap k R c)) = _
  rw [univCoact_algebraMap, AddMonoidAlgebra.mapRingHom_single]

theorem univCoactF_algebraMap (c : k) :
    univCoactF lam G ν (algebraMap k _ c) = univTwist lam G ν (algebraMap k R c) := by
  rw [univTwist_algebraMap]
  change AddMonoidAlgebra.mapRingHom ℤ
    (KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam (Q := Q)))
    (G.coaction (ν := ν) (algebraMap k _ c)) = _
  rw [AlgHom.commutes]
  change AddMonoidAlgebra.mapRingHom ℤ _ (AddMonoidAlgebra.single 0 (algebraMap k _ c)) = _
  rw [AddMonoidAlgebra.mapRingHom_single, KLRAlgebra.mapRingHom_algebraMap]

/-- The coaction `Ř^λ(ν) → Ř^λ(ν)[ℤ]`, as a ring homomorphism. -/
def univKLRCoactR : A →+* T :=
  letI := univTwistAlgebra lam G ν
  (KLRAlgebra.liftAlong (k := R) (algebraMap k R) (cycQ_map lam) (univCoactF lam G ν)
    (univCoactF_algebraMap lam G ν)).toRingHom

theorem univKLRCoactR_algebraMap (r : R) :
    univKLRCoactR lam G ν (algebraMap R A r) = univTwist lam G ν r := by
  let _ := univTwistAlgebra lam G ν
  exact (KLRAlgebra.liftAlong (k := R) (algebraMap k R) (cycQ_map lam) (univCoactF lam G ν)
    (univCoactF_algebraMap lam G ν)).commutes r

theorem univKLRCoactR_e (i : Seq ν) :
    univKLRCoactR lam G ν (e i) = univCoactF lam G ν (e i) := by
  let _ := univTwistAlgebra lam G ν
  exact KLRAlgebra.liftAlong_e _ _ _ _ i

theorem univKLRCoactR_x (a : Fin (Multiset.card ν)) :
    univKLRCoactR lam G ν (x a) = univCoactF lam G ν (x a) := by
  let _ := univTwistAlgebra lam G ν
  exact KLRAlgebra.liftAlong_x _ _ _ _ a

theorem univKLRCoactR_ψ (j : ℕ) :
    univKLRCoactR lam G ν (ψ j) = univCoactF lam G ν (ψ j) := by
  let _ := univTwistAlgebra lam G ν
  exact KLRAlgebra.liftAlong_ψ _ _ _ _ j

/-- On the image of the KLR algebra over `k`, the coaction is that of `G`. -/
theorem univKLRCoactR_mapRingHom (u : KLRAlgebra k Q ν) :
    univKLRCoactR lam G ν (KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam) u) =
      univCoactF lam G ν u := by
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective (k := k) (Q := Q) (ν := ν) u
  induction u using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, KLRAlgebra.mapRingHom_algebraMap, univKLRCoactR_algebraMap,
      univCoactF_algebraMap]
  | grade1 g =>
    cases g with
    | idem i =>
      change univKLRCoactR lam G ν (KLRAlgebra.mapRingHom _ _ (e i)) = _
      rw [KLRAlgebra.mapRingHom_e, univKLRCoactR_e]; rfl
    | dot a =>
      change univKLRCoactR lam G ν (KLRAlgebra.mapRingHom _ _ (x a)) = _
      rw [KLRAlgebra.mapRingHom_x, univKLRCoactR_x]; rfl
    | cross j =>
      change univKLRCoactR lam G ν (KLRAlgebra.mapRingHom _ _ (ψ j)) = _
      rw [KLRAlgebra.mapRingHom_ψ, univKLRCoactR_ψ]; rfl
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]

/-- **The coaction of `k[ℤ]` on `Ř^λ(ν)`**, the KLR algebra over `Ř^λ_λ`. -/
def univKLRCoact : A →ₐ[k] T :=
  { univKLRCoactR lam G ν with
    commutes' := fun c => by
      change univKLRCoactR lam G ν (algebraMap R A (algebraMap k R c)) = _
      rw [univKLRCoactR_algebraMap, univTwist_algebraMap]
      rfl }

theorem univKLRCoact_apply (u : A) : univKLRCoact lam G ν u = univKLRCoactR lam G ν u := rfl

/-- The grading of `Ř^λ(ν)`. -/
def univKLRGrade : ℤ → Submodule k A := CoactionGrading.grade (univKLRCoact lam G ν)

/-- Homogeneous elements of the KLR algebra over `k` stay homogeneous over `Ř^λ_λ`. -/
theorem mapRingHom_mem_univKLRGrade {d : ℤ} {u : KLRAlgebra k Q ν} (hu : u ∈ G.grade ν d) :
    KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam) u ∈ univKLRGrade lam G ν d := by
  rw [univKLRGrade, CoactionGrading.mem_grade, univKLRCoact_apply,
    univKLRCoactR_mapRingHom, univCoactF, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, (G.mem_grade).1 hu, AddMonoidAlgebra.mapRingHom_single]

/-- The scalar `e_{n+1}(p_j)`-monomials are homogeneous. -/
theorem algebraMap_monomial_mem_univKLRGrade (s : (Σ j : I, Fin (lam j)) →₀ ℕ) (c : k) :
    algebraMap R A (MvPolynomial.monomial s c) ∈
      univKLRGrade lam G ν (Finsupp.weight (univWt lam G) s : ℤ) := by
  rw [univKLRGrade, CoactionGrading.mem_grade, univKLRCoact_apply,
    univKLRCoactR_algebraMap, univTwist, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, univCoact_monomial, AddMonoidAlgebra.mapRingHom_single]

theorem mem_homogeneousSubalgebra (u : A) :
    u ∈ CoactionGrading.homogeneousSubalgebra (univKLRCoact lam G ν) := by
  have hmem : ∀ {d : ℤ} {v : A}, v ∈ univKLRGrade lam G ν d →
      v ∈ CoactionGrading.homogeneousSubalgebra (univKLRCoact lam G ν) :=
    fun hv => CoactionGrading.mem_homogeneousSubalgebra_of_mem_grade _ hv
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective (k := R) (Q := cycQ k lam Q) (ν := ν) u
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, r.as_sum, map_sum]
    exact Subalgebra.sum_mem _ fun s _ => hmem (algebraMap_monomial_mem_univKLRGrade lam G ν _ _)
  | grade1 g =>
    cases g with
    | idem i =>
      change e i ∈ _
      have h := mapRingHom_mem_univKLRGrade lam G ν (G.e_mem_grade i)
      rw [KLRAlgebra.mapRingHom_e] at h
      exact hmem h
    | dot a =>
      change x a ∈ _
      rw [← mul_one (x a), ← sum_e, Finset.mul_sum]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      have h := mapRingHom_mem_univKLRGrade lam G ν (G.x_mul_e_mem_grade a i)
      rw [map_mul, KLRAlgebra.mapRingHom_x, KLRAlgebra.mapRingHom_e] at h
      exact hmem h
    | cross j =>
      change ψ j ∈ _
      rw [← mul_one (ψ j : A), ← sum_e, Finset.mul_sum]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      have h := mapRingHom_mem_univKLRGrade lam G ν (G.ψ_mul_e_mem_grade' j i)
      rw [map_mul, KLRAlgebra.mapRingHom_ψ, KLRAlgebra.mapRingHom_e] at h
      exact hmem h
  | mul a b ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb

/-- **The grading of the KLR algebra over `Ř^λ_λ`**, with `e_{n+1}(p_j)` in degree
`(n + 1) · degX j`. -/
@[instance_reducible] def univKLRGradedAlgebra : GradedAlgebra (univKLRGrade lam G ν) :=
  CoactionGrading.gradedAlgebra
    (CoactionGrading.counit_of_forall_mem _ (mem_homogeneousSubalgebra lam G ν))
    (CoactionGrading.coassoc_of_forall_mem _ (mem_homogeneousSubalgebra lam G ν))

/-! ### The grading of `Ř^λ_ν` -/

/-- The degree of the universal cyclotomic relation at a sequence `𝐢`: `λ^{i_1} · degX i_1`. -/
def univCycDeg (i : Seq ν) : ℤ :=
  if h : 0 < Multiset.card ν then lam (i.lbl ⟨0, h⟩) • G.degX (i.lbl ⟨0, h⟩) else 0

/-- **The universal cyclotomic relations are homogeneous** when the dots have nonnegative
degree. -/
theorem cycElt_mem_univKLRGrade (hD : ∀ j, 0 ≤ G.degX j) (i : Seq ν) :
    cycElt (cycQ k lam Q) (univCycPoly k lam) i ∈ univKLRGrade lam G ν (univCycDeg lam G ν i) := by
  by_cases h : 0 < Multiset.card ν
  · rw [cycElt_of_pos _ _ _ h, univCycDeg, dite_eq_left h]
    set p : Fin (Multiset.card ν) := ⟨0, h⟩
    set j := i.lbl p
    have hxe : ∀ n : ℕ, (x p ^ n * e i : A) ∈ univKLRGrade lam G ν (n • G.degX j) := by
      intro n
      have H := G.mk_mem_grade_of_homAt (G.homAt_fx_pow_mul p (G.homAt_fe i) n)
      rw [map_mul, map_pow, add_zero] at H
      have H' := mapRingHom_mem_univKLRGrade lam G ν H
      rw [map_mul, map_pow] at H'
      change KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam) (x p) ^ n *
        KLRAlgebra.mapRingHom (algebraMap k R) (cycQ_map lam) (e i) ∈
          univKLRGrade lam G ν (n • G.degX j) at H'
      rw [KLRAlgebra.mapRingHom_x, KLRAlgebra.mapRingHom_e] at H'
      exact H'
    rw [univCycPoly, univCycTail, map_add, map_sum, add_mul, Finset.sum_mul, map_pow,
      Polynomial.aeval_X]
    refine Submodule.add_mem _ (hxe _) (Submodule.sum_mem _ fun n _ => ?_)
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, mul_assoc]
    have hc : ((-1 : R) ^ (n.val + 1) * MvPolynomial.X (⟨j, n⟩ : Σ j : I, Fin (lam j))) =
        MvPolynomial.monomial (Finsupp.single ⟨j, n⟩ 1) ((-1 : k) ^ (n.val + 1)) := by
      rw [MvPolynomial.X, show ((-1 : R) ^ (n.val + 1)) =
        MvPolynomial.C ((-1 : k) ^ (n.val + 1)) by simp, MvPolynomial.C_mul_monomial, mul_one]
    rw [hc]
    have := CoactionGrading.mul_mem_grade _
      (algebraMap_monomial_mem_univKLRGrade lam G ν (Finsupp.single ⟨j, n⟩ 1)
        ((-1 : k) ^ (n.val + 1)))
      (hxe (lam j - (n.val + 1)))
    have hdeg : (lam j • G.degX j : ℤ) =
        (Finsupp.weight (univWt lam G) (Finsupp.single (⟨j, n⟩ : Σ j : I, Fin (lam j)) 1) : ℤ) +
          (lam j - (n.val + 1)) • G.degX j := by
      rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp), one_smul, univWt]
      have hn : n.val + 1 ≤ lam j := n.isLt
      obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (hD j)
      simp only [hd, Int.toNat_natCast, nsmul_eq_mul]
      push_cast [Nat.cast_sub hn]
      ring
    rw [hdeg]
    exact this
  · simp [cycElt, h]

/-- The scalar `k`-algebra structure on `Ř^λ_ν`. -/
@[instance_reducible] local instance (priority := low) univCycAlgebra :
    Algebra k (UnivCyc k lam Q ν) :=
  Algebra.compHom _ (algebraMap k (UnivCycRing k lam))

local instance (priority := low) univCycScalarTower :
    IsScalarTower k (UnivCycRing k lam) (UnivCyc k lam Q ν) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The quotient map `Ř^λ(ν) → Ř^λ_ν`, over `k`. -/
def univCycMk : A →ₐ[k] UnivCyc k lam Q ν :=
  (CycKLR.mk (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν).restrictScalars k

/-- **The grading of `Ř^λ_ν`** (Webster, arXiv:1309.3796v2, Corollary 3.26). -/
def univCycGrade : ℤ → Submodule k (UnivCyc k lam Q ν) :=
  Graded.map (univKLRGrade lam G ν) (univCycMk lam ν).toLinearMap

/-- The grading of `Ř^λ_ν` descends from that of `Ř^λ(ν)`. -/
@[instance_reducible] def univCycGradedAlgebra (hD : ∀ j, 0 ≤ G.degX j) :
    GradedAlgebra (univCycGrade lam G ν) :=
  letI := univKLRGradedAlgebra lam G ν
  Graded.mapGradedAlgebra (univKLRGrade lam G ν) _ CycKLR.mk_surjective fun y hy n =>
    (CycKLR.mk_eq_zero_iff _).2 <| by
      have h := (CycKLR.mk_eq_zero_iff y).1 hy
      unfold cycIdeal at h ⊢
      apply Graded.decompose_mem_twoSidedSpan (univKLRGrade lam G ν) _ h n
      rintro _ ⟨i, rfl⟩
      exact ⟨_, cycElt_mem_univKLRGrade lam G ν hD i⟩

/-- Multiplication by a monomial of `Ř^λ_λ` raises the degree by its weight. -/
theorem monomial_smul_mem_univCycGrade (s : (Σ j : I, Fin (lam j)) →₀ ℕ) {d : ℤ}
    {y : UnivCyc k lam Q ν} (hy : y ∈ univCycGrade lam G ν d) :
    MvPolynomial.monomial s (1 : k) • y ∈
      univCycGrade lam G ν (d + (Finsupp.weight (univWt lam G) s : ℤ)) := by
  obtain ⟨y, hy, rfl⟩ := hy
  refine ⟨algebraMap R A (MvPolynomial.monomial s 1) * y, ?_, ?_⟩
  · rw [add_comm]
    exact CoactionGrading.mul_mem_grade _ (algebraMap_monomial_mem_univKLRGrade lam G ν s 1) hy
  · change CycKLR.mk _ _ _ ν _ = _ • CycKLR.mk _ _ _ ν y
    rw [map_mul, AlgHom.commutes, Algebra.smul_def]

end

/-! ### Freeness -/

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {lam : I → ℕ}
  {C : QuantumGroup.CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}

/-- **Webster, arXiv:1309.3796v2, Corollary 3.26** (freeness): over a field `k`, `Ř^λ_ν` is a
free `Ř^λ_λ`-module. -/
theorem UnivCyc.free (hQ : IsRouquierQ C Q) (ν : Multiset I) :
    Module.Free (UnivCycRing k lam) (UnivCyc k lam Q ν) := by
  let G := hQ.gradingDatum
  have hD : ∀ j, 0 < G.degX j := fun j => C.dot_self_pos j
  let _ := univCycAlgebra lam (Q := Q) ν
  have := univCycScalarTower lam (Q := Q) ν
  let _ := univCycGradedAlgebra lam G ν fun j => (hD j).le
  have := UnivCyc.projective (lam := lam) hQ ν
  have : Module.Finite (UnivCycRing k lam) (UnivCyc k lam Q ν) :=
    CycKLR.module_finite (fun i j hij => by
      obtain ⟨c, hc, h⟩ := hQ.cycQ.polyInY_leading i j hij
      rw [h]; exact hc.map _) (univCycPoly_monic k lam)
  exact Graded.free_of_projective
    (Graded.isConnectedGrading_mvPolynomial (ℳ := univCycGrade lam G ν) (univWt lam G)
      (fun s => Nat.mul_pos s.2.val.succ_pos (by have := hD s.1; omega))
      fun s d y hy => monomial_smul_mem_univCycGrade lam G ν s hy)

end Categorification.KLR.CyclotomicAction
