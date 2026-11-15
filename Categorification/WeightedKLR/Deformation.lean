/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Standing

/-!
# The canonical deformation of a weighted KLR algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Canonical deformations": the definition of the deformation and the Proposition that follows it
(the deformation is free, hence flat, over the ring of deformation parameters).

Fix data witnessing Webster's standing hypothesis (`WeightedGraph.StandingData`: degrees `d i`
and, for each edge `e`, multiplicities `c_e`, `c_ē` with `Q_e` homogeneous of degree
`d (head e) * c_e`). For each edge `e`, with `u` of degree `d (head e)` and `v` of degree
`d (tail e)` as in the rest of the library, the deformation parameters are variables `z_{e,a,b}`
for `a < d (tail e)`, `b < d (head e)` with `a * d (head e) + b * d (tail e) < d (head e) * c_e`
(`WeightedGraph.StandingData.DeformVar`), the deformed polynomials are
`Q̃_e(u, v) = Q_e(u, v) + ∑ z_{e,a,b} u^a v^b` (`WeightedGraph.StandingData.deformQ`), and the
canonical deformation is the weighted KLR algebra of the graph with these polynomials over
`S = k[z]` (`WeightedGraph.StandingData.deformGraph`).

## Encoding and deviations

* The loops of weight `0` are recorded in this library by their polynomial `P_i` (with
  `Q = (u - v) P_i`), not as edges. The deformation here leaves them undeformed (`P_i` is only
  base-changed to `S`). For such a loop the paper's recipe would add terms `z u^a v^b` to
  `(u - v) P_i`, which are in general not divisible by `u - v`, so it does not produce a
  polynomial of the required form; the source does not address this case.
* The deformation depends on the choice of the multiplicities `c_e`; they are part of the data
  `StandingData`, which is equivalent to Webster's standing hypothesis
  (`WeightedGraph.standing_iff_nonempty_standingData`).
* The grading in which `Q̃_e` is homogeneous (with `z_{e,a,b}` in degree
  `d (head e) * c_e - a * d (head e) - b * d (tail e)`) is not formalized: the Proposition does
  not use it.

## Main definitions

* `WeightedGraph.StandingData`, `StandingData.DeformVar`, `StandingData.deformQ`,
  `StandingData.deformGraph`.

## Main results

* `GalleryAlgebra.exists_deformBasis`: the Proposition, as a basis of the deformed algebra over `S`
  given by the diagrams `b_π y^m` of Theorem 2.8.
* `GalleryAlgebra.free_deform`, `GalleryAlgebra.flat_deform`: the deformation is free, hence
  flat, over `S`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Finsupp

variable {k : Type*} [CommRing k]

section Top

/-- A polynomial in `u, v` whose monomials have `u`-degree at most `c`, the only one of
`u`-degree `c` being `u ^ c`, with unit coefficient. This is the condition under which
`isRegular_rename_of_top` gives a non-zero-divisor. -/
def HasUnitTop (c : ℕ) {R : Type*} [CommRing R] (Q : MvPolynomial (Fin 2) R) : Prop :=
  IsUnit (Q.coeff (single 0 c)) ∧ ∀ d ∈ Q.support, d 0 ≤ c ∧ (d 0 = c → d = single 0 c)

theorem hasUnitTop_of_isUnitHomogeneous {a b c c' : ℕ} (ha : 0 < a) (hb : 0 < b)
    {Q : MvPolynomial (Fin 2) k} (hQ : WeightedGraph.IsUnitHomogeneous a b c c' Q) :
    HasUnitTop c Q := by
  obtain ⟨-, hhom, hu, -⟩ := hQ
  refine ⟨hu, fun d hd => ?_⟩
  have hw := hhom (MvPolynomial.mem_support_iff.1 hd)
  simp only [weight_apply, smul_eq_mul] at hw
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_two] at hw
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hw
  have h0 : d 0 ≤ c := by nlinarith
  refine ⟨h0, fun hc => ?_⟩
  have h1 : d 1 = 0 := by subst hc; nlinarith
  ext j
  fin_cases j <;> simp [hc, h1]

theorem HasUnitTop.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {c : ℕ}
    {Q : MvPolynomial (Fin 2) R} (h : HasUnitTop c Q) : HasUnitTop c (MvPolynomial.map f Q) := by
  refine ⟨by rw [coeff_map]; exact h.1.map f, fun d hd => h.2 d ?_⟩
  rw [MvPolynomial.mem_support_iff, coeff_map] at hd
  rw [MvPolynomial.mem_support_iff]
  intro h0
  exact hd (by rw [h0, map_zero])

/-- Adding to a polynomial with a unit top coefficient in `u ^ c` terms of lower `u`-degree
keeps it so. -/
theorem HasUnitTop.add {R : Type*} [CommRing R] {c : ℕ} {Q Q' : MvPolynomial (Fin 2) R}
    (h : HasUnitTop c Q) (h' : ∀ d ∈ Q'.support, d 0 < c) : HasUnitTop c (Q + Q') := by
  have hz : ∀ d, ¬ (d 0 < c) → Q'.coeff d = 0 := fun d hd => by
    by_contra h0
    exact hd (h' d (MvPolynomial.mem_support_iff.2 h0))
  have hadd : ∀ d, (Q + Q').coeff d = Q.coeff d + Q'.coeff d := fun d => by simp
  refine ⟨?_, fun d hd => ?_⟩
  · rw [hadd, hz _ (by simp), add_zero]
    exact h.1
  · rw [MvPolynomial.mem_support_iff, hadd] at hd
    by_cases hQ : Q.coeff d = 0
    · rw [hQ, zero_add] at hd
      have := h' d (MvPolynomial.mem_support_iff.2 hd)
      exact ⟨this.le, fun h => absurd h this.ne⟩
    · exact h.2 d (MvPolynomial.mem_support_iff.2 hQ)

theorem HasUnitTop.isRegular_rename {R : Type*} [CommRing R] {σ : Type*} [Finite σ]
    {f : Fin 2 → σ} (hf : Function.Injective f) {c : ℕ} {Q : MvPolynomial (Fin 2) R}
    (h : HasUnitTop c Q) : IsRegular (rename f Q) :=
  isRegular_rename_of_top hf h.1 h.2

end Top

variable {I : Type*} {𝕜 : Type*}

namespace WeightedGraph

/-- Data witnessing Webster's standing hypothesis (arXiv:1209.2463v4, §2.1): degrees `d i`,
multiplicities `c e`, `c' e` for each edge, with `Q_e` homogeneous of degree
`d (head e) * c e = d (tail e) * c' e` with unit coefficients of `u ^ c e` and `v ^ c' e`, and the
conditions on the loop polynomials. -/
structure StandingData (Γ : WeightedGraph I 𝕜 k) where
  /-- The degree `d i` of a dot on a strand of colour `i`. -/
  d : I → ℕ
  d_pos : ∀ i, 0 < d i
  /-- The multiplicity `c_e`: `Q_e` has degree `d (head e) * c e`. -/
  c : Γ.E → ℕ
  /-- The multiplicity `c_ē`. -/
  c' : Γ.E → ℕ
  isUnitHomogeneous : ∀ e, IsUnitHomogeneous (d (Γ.head e)) (d (Γ.tail e)) (c e) (c' e) (Γ.Q e)
  loop_cond : ∀ i P, Γ.loop i = some P → rename (Equiv.swap (0 : Fin 2) 1) P = P ∧
    ∃ c c' : ℕ, IsUnitHomogeneous (d i) (d i) c c' ((X 0 - X 1) * P)

theorem standing_iff_nonempty_standingData (Γ : WeightedGraph I 𝕜 k) :
    Γ.Standing ↔ Nonempty Γ.StandingData := by
  constructor
  · rintro ⟨d, hd, hQ, hL⟩
    choose c c' hc using hQ
    exact ⟨⟨d, hd, c, c', hc, hL⟩⟩
  · rintro ⟨D⟩
    exact ⟨D.d, D.d_pos, fun e => ⟨_, _, D.isUnitHomogeneous e⟩, D.loop_cond⟩

namespace StandingData

variable {Γ : WeightedGraph I 𝕜 k} (D : Γ.StandingData)

/-- The exponents `(a, b)` of the deformation parameters `z_{e,a,b}` of the edge `e`:
`a < d (tail e)`, `b < d (head e)` and `a * d (head e) + b * d (tail e) < d (head e) * c_e`. -/
def DeformExp (e : Γ.E) : Type :=
  {ab : Fin (D.d (Γ.tail e)) × Fin (D.d (Γ.head e)) //
    (ab.1 : ℕ) * D.d (Γ.head e) + (ab.2 : ℕ) * D.d (Γ.tail e) < D.d (Γ.head e) * D.c e}

instance (e : Γ.E) : Fintype (D.DeformExp e) := by unfold DeformExp; infer_instance

/-- The deformation parameters `z_{e,a,b}`. -/
abbrev DeformVar : Type := Σ e : Γ.E, D.DeformExp e

/-- The ring `S = k[z]` of deformation parameters. -/
abbrev DeformRing (k : Type*) [CommRing k] {Γ : WeightedGraph I 𝕜 k} (D : Γ.StandingData) :=
  MvPolynomial D.DeformVar k

/-- The monomial `u^a v^b` of a deformation parameter. -/
noncomputable def DeformExp.exp {e : Γ.E} (z : D.DeformExp e) : Fin 2 →₀ ℕ :=
  single 0 (z.1.1 : ℕ) + single 1 (z.1.2 : ℕ)

/-- The deformed polynomial `Q̃_e(u, v) = Q_e(u, v) + ∑_{a,b} z_{e,a,b} u^a v^b`, over `S`. -/
noncomputable def deformQ (e : Γ.E) : MvPolynomial (Fin 2) (D.DeformRing k) :=
  MvPolynomial.map (C (σ := D.DeformVar)) (Γ.Q e) +
    ∑ z : D.DeformExp e, monomial (DeformExp.exp D z) (X ⟨e, z⟩)

/-- **The canonical deformation** (Webster, §2, "Canonical deformations"): the weighted graph
over `S = k[z]` with the same edges, orientations and weights, the polynomials `Q̃_e`, and the
loop polynomials of weight `0` base-changed to `S` (see the module docstring). -/
noncomputable def deformGraph : WeightedGraph I 𝕜 (D.DeformRing k) where
  E := Γ.E
  tail := Γ.tail
  head := Γ.head
  weight := Γ.weight
  Q := D.deformQ
  loop i := (Γ.loop i).map (MvPolynomial.map C)

theorem DeformExp.exp_zero_lt {e : Γ.E} (z : D.DeformExp e) : DeformExp.exp D z 0 < D.c e := by
  have h0 : DeformExp.exp D z 0 = (z.1.1 : ℕ) := by
    simp [DeformExp.exp]
  rw [h0]
  have h := z.2
  have h1 : (z.1.1 : ℕ) * D.d (Γ.head e) < D.c e * D.d (Γ.head e) := by
    rw [mul_comm (D.c e)]
    exact lt_of_le_of_lt (Nat.le_add_right _ _) h
  exact Nat.lt_of_mul_lt_mul_right h1

theorem deformQ_hasUnitTop (e : Γ.E) : HasUnitTop (D.c e) (D.deformQ e) := by
  have htop := (hasUnitTop_of_isUnitHomogeneous (D.d_pos _) (D.d_pos _)
    (D.isUnitHomogeneous e)).map (C (σ := D.DeformVar))
  refine htop.add fun m hm => ?_
  obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  rw [Finset.mem_singleton.1 (support_monomial_subset hz)]
  exact DeformExp.exp_zero_lt D z

theorem dagger_deformGraph [Neg 𝕜] (hD : Γ.Dagger) : D.deformGraph.Dagger := hD

theorem noZeroLoops_deformGraph [Zero 𝕜] (hZ : Γ.NoZeroLoops) : D.deformGraph.NoZeroLoops := hZ

theorem psymm_deformGraph : D.deformGraph.PSymm := by
  intro i P hP
  simp only [deformGraph, Option.map_eq_some_iff] at hP
  obtain ⟨P₀, h₀, rfl⟩ := hP
  rw [← map_rename, (D.loop_cond i P₀ h₀).1]

variable {ν : I →₀ ℕ}

theorem isRegular_factor_deformGraph (w : Wall D.deformGraph ν) :
    IsRegular (w.factor (k := D.DeformRing k)) := by
  rw [w.factor_eq_rename]
  exact (D.deformQ_hasUnitTop w.1.1).isRegular_rename (injective_vecCons_two w.2.2.2)

theorem isRegular_loopFactor_deformGraph :
    ∀ (Q : MvPolynomial (Fin 2) (D.DeformRing k)) (a b : Strand ν),
      D.deformGraph.loop a.1 = some Q →
      a ≠ b → a.1 = b.1 → IsRegular (loopFactor Q a b) := by
  intro Q a b hQ hab _
  simp only [deformGraph, Option.map_eq_some_iff] at hQ
  obtain ⟨P₀, h₀, rfl⟩ := hQ
  obtain ⟨-, c, c', hc⟩ := D.loop_cond _ P₀ h₀
  have htop := (hasUnitTop_of_isUnitHomogeneous (D.d_pos _) (D.d_pos _) hc).map
    (C (σ := D.DeformVar))
  have := htop.isRegular_rename (injective_vecCons_two hab)
  rw [map_mul, map_sub, map_X, map_X, map_mul] at this
  rw [loopFactor_eq_rename]
  exact (isRegular_mul_iff.1 this).2

end StandingData

end WeightedGraph

namespace GalleryAlgebra

open WeightedGraph

variable [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {Γ : WeightedGraph I 𝕜 k} (D : Γ.StandingData) {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-- **Webster, §2, the Proposition on canonical deformations**, in basis form: under Webster's
hypotheses (standing data and (†)), for some choice of simple segments `P`, the diagrams
`r g (g⁻¹ • D') * segGallery P C (g⁻¹ • D') * poly (y^m)` form a basis of the canonical
deformation of Webster's algebra over the ring `S = k[z]` of deformation parameters. -/
theorem exists_deformBasis (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    ∃ P : FullChamber D.deformGraph ν → FullChamber D.deformGraph ν →
        (Strand ν → 𝕜) × (Strand ν → 𝕜),
      ∃ b : Module.Basis (RankChamber D.deformGraph ν × RankChamber D.deformGraph ν ×
          ColPerm ν × (Strand ν →₀ ℕ)) (D.DeformRing k)
          (weightedKLR (D.DeformRing k) D.deformGraph ν), ∀ C E g m,
        (b (C, E, g, m) : GalleryAlgebra (D.DeformRing k) D.deformGraph ν) =
          r g (g⁻¹ • E.1) * segGallery P C.1 (g⁻¹ • E.1) * poly (monomial m 1) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := D.DeformRing k)
    (D.dagger_deformGraph hD) (D.noZeroLoops_deformGraph hZ) (ν := ν)
  exact ⟨P, weightedKLRBasis hP (D.dagger_deformGraph hD) (D.noZeroLoops_deformGraph hZ)
      D.psymm_deformGraph D.isRegular_factor_deformGraph D.isRegular_loopFactor_deformGraph,
    weightedKLRBasis_apply _ _ _ _ _ _⟩

/-- **Webster, §2, the Proposition on canonical deformations**: the canonical deformation of
Webster's algebra is free over the ring `S = k[z]` of deformation parameters. -/
theorem free_deform (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Module.Free (D.DeformRing k) (weightedKLR (D.DeformRing k) D.deformGraph ν) := by
  obtain ⟨-, b, -⟩ := exists_deformBasis D (ν := ν) hD hZ
  exact Module.Free.of_basis b

/-- **Webster, §2, the Proposition on canonical deformations**: the canonical deformation of
Webster's algebra is flat over the ring `S = k[z]` of deformation parameters. -/
theorem flat_deform (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Module.Flat (D.DeformRing k) (weightedKLR (D.DeformRing k) D.deformGraph ν) := by
  have := free_deform D (ν := ν) hD hZ
  infer_instance

end GalleryAlgebra

end Categorification.WeightedKLR
