/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.PolyRep

/-!
# Webster's standing hypothesis on the polynomials `Q_e`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1 (the paragraph
before Definition 2.1).

Webster's graph carries edge multiplicities `c_e, c_ē ∈ ℤ_{≥0}` that are symmetrizable: there
are `d_i` with `d_{h(e)} c_e = d_{t(e)} c_ē`. The polynomial `Q_e(u, v)` is homogeneous of degree
`d_{h(e)} c_e` when `u` has degree `d_{h(e)}` and `v` has degree `d_{t(e)}`, and its coefficients
of the pure monomials in `u` and in `v` (that is, of `u ^ c_e` and `v ^ c_ē`, the only pure
monomials of that degree) are units. For a loop of weight `0` the polynomial is
`Q_e = (u - v) P_e` with `P_e` symmetric.

`WeightedGraph` records neither the `d_i` nor the multiplicities, so `WeightedGraph.Standing`
asks for their existence: positive integers `d : I → ℕ` and, for each edge, multiplicities
`c, c'` with `d (head e) * c = d (tail e) * c'` for which `Q_e` has this property
(`IsUnitHomogeneous`); and for each loop of weight `0` at `i`, recorded by its polynomial
`P = P_i`, the polynomial `P` is symmetric and `(u - v) P` has the property for the degrees
`d i, d i`. Here `u` is variable `0` (the dot on the strand coloured `head e`) and `v` is
variable `1`, as in `Wall.factor`.

## Reading of the hypothesis

* The `d_i` are positive. Webster does not say so explicitly, but with `d_{h(e)} = 0` every
  power of `u` would be a pure monomial of degree `0` and the condition would say nothing; for
  a symmetrizable Cartan matrix the symmetrizer is positive.
* Since the degree is `d_{h(e)} c_e = d_{t(e)} c_ē`, both pure monomials `u ^ c_e` and
  `v ^ c_ē` have the right degree, and both coefficients are required to be units. (Without the
  multiplicities, a degree not divisible by `d_{h(e)}` would leave no pure power of `u`, and the
  condition would say nothing about it.)
* Only the unit coefficient of `u ^ c_e` is used below: it is the leading coefficient of
  `Q_e(y_a, y_b)` as a polynomial in `y_a`.

## Main definitions

* `WeightedGraph.IsUnitHomogeneous a b c c' Q`.
* `WeightedGraph.Standing`: Webster's standing hypothesis.

## Main results

* `isRegular_rename_of_isUnitHomogeneous`: such a polynomial in two distinct
  variables of a polynomial ring is a non-zero-divisor, over any commutative ring.
* `WeightedGraph.Standing.psymm`, `WeightedGraph.Standing.isRegular_factor`,
  `WeightedGraph.Standing.isRegular_loopFactor`: the hypotheses `PSymm` and regularity of the
  wall and loop factors used by the basis theorem follow from the standing hypothesis.
-/

namespace Categorification.WeightedKLR

open MvPolynomial

variable {k : Type*} [CommRing k]

namespace WeightedGraph

/-- `Q(u, v)` is homogeneous of degree `a * c = b * c'` when `u` (variable `0`) has degree `a`
and `v` (variable `1`) has degree `b`, and the coefficients of the pure monomials `u ^ c` and
`v ^ c'` are units. -/
def IsUnitHomogeneous (a b c c' : ℕ) (Q : MvPolynomial (Fin 2) k) : Prop :=
  a * c = b * c' ∧ IsWeightedHomogeneous ![a, b] Q (a * c) ∧
    IsUnit (Q.coeff (Finsupp.single 0 c)) ∧ IsUnit (Q.coeff (Finsupp.single 1 c'))

variable {I 𝕜 : Type*} (Γ : WeightedGraph I 𝕜 k)

/-- **Webster's standing hypothesis** (arXiv:1209.2463v4, §2.1): there are positive integers
`d i` and, for each edge `e`, multiplicities `c_e, c_ē` with `d (head e) * c_e = d (tail e) * c_ē`
such that `Q_e` is homogeneous of degree `d (head e) * c_e` for the degrees `d (head e)` of `u`
and `d (tail e)` of `v`, with unit coefficients of `u ^ c_e` and `v ^ c_ē`; and for each loop
of weight `0` at `i`, its polynomial `P_i` is symmetric and `(u - v) P_i` satisfies the same
condition for the degrees `d i, d i`. See the module docstring for the reading. -/
def Standing : Prop :=
  ∃ d : I → ℕ, (∀ i, 0 < d i) ∧
    (∀ e, ∃ c c' : ℕ, IsUnitHomogeneous (d (Γ.head e)) (d (Γ.tail e)) c c' (Γ.Q e)) ∧
    ∀ i P, Γ.loop i = some P → rename (Equiv.swap (0 : Fin 2) 1) P = P ∧
      ∃ c c' : ℕ, IsUnitHomogeneous (d i) (d i) c c' ((X 0 - X 1) * P)

end WeightedGraph

section Regular

open Finsupp MonomialOrder

/-- A polynomial whose monomials have degree in `u` at most `c`, the only one of degree `c` being
`u ^ c`, with unit coefficient: substituted into two distinct variables of a polynomial ring in
finitely many variables, it is a non-zero-divisor. -/
theorem isRegular_rename_of_top {σ : Type*} [Finite σ] {f : Fin 2 → σ}
    (hf : Function.Injective f) {Q : MvPolynomial (Fin 2) k} {c : ℕ}
    (hu : IsUnit (Q.coeff (single 0 c)))
    (htop : ∀ d ∈ Q.support, d 0 ≤ c ∧ (d 0 = c → d = single 0 c)) :
    IsRegular (rename f Q) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let φ : σ → ℕ := fun s => if s = f 0 then 0 else e s + 1
  have hφ : Function.Injective φ := by
    intro s t h
    simp only [φ] at h
    split_ifs at h with hs ht ht
    · exact hs.trans ht.symm
    · exact e.injective (Fin.ext (by omega))
  let _ : LinearOrder σ := LinearOrder.lift' φ hφ
  have hmin : ∀ j : σ, ¬ j < f 0 := by
    intro j hj
    have : φ j < φ (f 0) := hj
    simp [φ] at this
  let m : MonomialOrder σ := MonomialOrder.lex
  have hsupp : ∀ d ∈ (rename f Q).support, d ≼[m] single (f 0) c := by
    intro d hd
    rw [support_rename_of_injective hf, Finset.mem_image] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨hle, heq⟩ := htop d' hd'
    rcases hle.lt_or_eq with hlt | hc
    · refine le_of_lt (MonomialOrder.lex_lt_iff.2 ?_)
      refine (Finsupp.Lex.lt_iff).2 ⟨f 0, fun j hj => absurd hj (hmin j), ?_⟩
      simpa [mapDomain_apply_of_injective hf] using hlt
    · rw [heq hc, mapDomain_single]
  have hmem : single (f 0) c ∈ (rename f Q).support := by
    rw [MvPolynomial.mem_support_iff, ← mapDomain_single, coeff_rename_mapDomain f hf]
    exact hu.ne_zero
  have hdeg : m.degree (rename f Q) = single (f 0) c :=
    m.toSyn.injective (le_antisymm (m.degree_le_iff.2 hsupp) (m.le_degree hmem))
  have hlc : IsRegular (m.leadingCoeff (rename f Q)) := by
    rw [MonomialOrder.leadingCoeff, hdeg, ← mapDomain_single, coeff_rename_mapDomain f hf]
    exact hu.isRegular
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_right]
  intro g hg
  by_contra hg0
  have := m.leadingCoeff_mul_of_isRegular_left hlc (g := g)
  rw [mul_comm g] at hg
  rw [hg, m.leadingCoeff_zero] at this
  exact (m.leadingCoeff_ne_zero_iff.2 hg0) (hlc.left (this.symm.trans (mul_zero _).symm))

/-- **Webster's condition gives non-zero-divisors**: if `Q(u, v)` is homogeneous of degree
`a * c` for positive degrees `a` of `u` and `b` of `v`, with unit coefficient of `u ^ c`, then
`Q(y_s, y_t)` is a non-zero-divisor in `k[y]` for distinct variables `y_s, y_t`, over any
commutative ring `k`. -/
theorem isRegular_rename_of_isUnitHomogeneous {σ : Type*} [Finite σ] {f : Fin 2 → σ}
    (hf : Function.Injective f) {a b c c' : ℕ} (ha : 0 < a) (hb : 0 < b)
    {Q : MvPolynomial (Fin 2) k} (hQ : WeightedGraph.IsUnitHomogeneous a b c c' Q) :
    IsRegular (rename f Q) := by
  obtain ⟨-, hhom, hu, -⟩ := hQ
  refine isRegular_rename_of_top hf hu fun d hd => ?_
  have hw := hhom (MvPolynomial.mem_support_iff.1 hd)
  simp only [weight_apply, smul_eq_mul] at hw
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_two] at hw
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hw
  have h0 : d 0 ≤ c := by nlinarith
  refine ⟨h0, fun hc => ?_⟩
  have h1 : d 1 = 0 := by subst hc; nlinarith
  ext j
  fin_cases j <;> simp [hc, h1]

end Regular

theorem injective_vecCons_two {α : Type*} {a b : α} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

variable {I : Type*} {𝕜 : Type*} {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- `Q_e(y_a, y_b)` is `Q_e` with its variables renamed to `y_a, y_b`. -/
theorem Wall.factor_eq_rename (w : Wall Γ ν) :
    w.factor (k := k) = rename ![w.src, w.tgt] (Γ.Q w.edge) := by
  rw [Wall.factor, rename_eq_aeval]
  congr 2
  funext j
  fin_cases j <;> rfl

/-- `P(y_a, y_b)` is `P` with its variables renamed to `y_a, y_b`. -/
theorem loopFactor_eq_rename (P : MvPolynomial (Fin 2) k) (a b : Strand ν) :
    loopFactor P a b = rename ![a, b] P := by
  rw [loopFactor, rename_eq_aeval]
  congr 2
  funext j
  fin_cases j <;> rfl

namespace WeightedGraph

/-- Under Webster's standing hypothesis the loop polynomials are symmetric. -/
theorem Standing.psymm (h : Γ.Standing) : Γ.PSymm := by
  obtain ⟨d, -, -, hL⟩ := h
  exact fun i P hP => (hL i P hP).1

/-- Under Webster's standing hypothesis every wall factor `Q_e(y_a, y_b)` is a non-zero-divisor,
over any commutative ring `k`. -/
theorem Standing.isRegular_factor (h : Γ.Standing) (w : Wall Γ ν) :
    IsRegular (w.factor (k := k)) := by
  obtain ⟨d, hd, hQ, -⟩ := h
  obtain ⟨c, c', hc⟩ := hQ w.edge
  rw [w.factor_eq_rename]
  exact isRegular_rename_of_isUnitHomogeneous (injective_vecCons_two w.2.2.2) (hd _) (hd _) hc

/-- Under Webster's standing hypothesis every loop factor `P_i(y_a, y_b)`, for distinct strands
`a, b`, is a non-zero-divisor, over any commutative ring `k`: it divides
`Q(y_a, y_b) = (y_a - y_b) P_i(y_a, y_b)`. -/
theorem Standing.isRegular_loopFactor (h : Γ.Standing) {P : MvPolynomial (Fin 2) k}
    {a b : Strand ν} (hP : Γ.loop a.1 = some P) (hab : a ≠ b) :
    IsRegular (loopFactor P a b) := by
  obtain ⟨d, hd, -, hL⟩ := h
  obtain ⟨-, c, c', hc⟩ := hL _ P hP
  have := isRegular_rename_of_isUnitHomogeneous (injective_vecCons_two hab) (hd _) (hd _) hc
  rw [map_mul] at this
  rw [loopFactor_eq_rename]
  exact (isRegular_mul_iff.1 this).2

/-- The loop-factor hypothesis of the basis theorem (`GalleryAlgebra.basisOfSegments`), from
Webster's standing hypothesis. -/
theorem Standing.isRegular_loopFactor' (h : Γ.Standing) :
    ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b) :=
  fun _ _ _ hQ hab _ => h.isRegular_loopFactor hQ hab

end WeightedGraph

end Categorification.WeightedKLR
