/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Standing

/-!
# The Crawley-Boevey graph: weighted KLR algebras with red strands

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §3.1 and the setup
of §3.2.

Given a weighted graph `Γ` with vertex set `I` and a list of dominant weights `λ_1, …, λ_ℓ`
(recorded by their pairings `α_i^∨(λ_j)`, as finitely supported functions `Λ j : I →₀ ℕ`),
Webster's Crawley-Boevey graph `Γ_λ` has one more vertex `0` and, for each `j` and `i`,
`α_i^∨(λ_j)` new edges from `0` to `i` of weight `ϖ_j`, each with polynomial `u - v`. Here the
vertex set is `Option I`, the new vertex being `none`.

## Encoding of the parallel new edges

The `α_i^∨(λ_j)` new edges from `0` to `i` of weight `ϖ_j` have the same tail, head and weight,
so the graph `Γ_λ` violates (†). Webster's Definition 2.6 defines the weighted KLR algebra of
such a graph as that of the graph in which these edges are replaced by one edge with the product
of their polynomials; this is how they enter here: one edge `(j, i)` for each `i` in the support
of `Λ j`, with polynomial `(u - v) ^ α_i^∨(λ_j)`. This is the factor that appears in the proof of
Webster's Theorem 3.5 when a bigon between an `i`-labelled strand and a ghost is undone.

With this encoding, (†) for `Γ_λ` holds as soon as it holds for `Γ` and the weights `ϖ_j` are
distinct (`WeightedGraph.crawleyBoevey_dagger`; Webster takes `ϖ_1 < ⋯ < ϖ_ℓ`).

## The standing hypothesis

Webster chooses the multiplicities `c_e = c_ē = 1` for the new edges. The polynomial `u - v` is
then homogeneous only if the degree `d_0` of the new vertex equals `d_i`; when the vertices
joined to `0` have different `d_i` (non-simply-laced `Γ`), the standing hypothesis of §2.1 does
not hold for `Γ_λ` as printed. It is used for the grading only: the basis theorem needs the wall
and loop factors to be non-zero-divisors, and these hold for `Γ_λ` whenever the standing
hypothesis holds for `Γ` (`WeightedGraph.crawleyBoevey_isRegular_factor`,
`WeightedGraph.crawleyBoevey_isRegular_loopFactor`).

## Main definitions

* `WeightedGraph.crawleyBoevey Γ Λ ϖ`: the Crawley-Boevey graph `Γ_λ` with new edges of weights
  `ϖ_j`.
* `WeightedGraph.redWeight ν`: the weight `ν̃ = ν + α_0` (one strand labelled `0`).

## Main results

* `GalleryAlgebra.exists_redBasis`: Webster's Theorem 2.8 for the weighted KLR algebra of the
  Crawley-Boevey graph, under the standing hypothesis and (†) for `Γ` and distinct `ϖ_j`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial

variable {I : Type} [DecidableEq I] {𝕜 : Type*} {k : Type*} [CommRing k]

namespace WeightedGraph

variable (Γ : WeightedGraph I 𝕜 k) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ϖ : Fin ℓ → 𝕜)

/-- The new edges of the Crawley-Boevey graph, after merging parallel edges (Webster's
Definition 2.6): the pairs `(j, i)` with `α_i^∨(λ_j) ≠ 0`. -/
abbrev RedEdge : Type := Σ j : Fin ℓ, (Λ j).support

/-- **Webster's Crawley-Boevey graph** `Γ_λ` (arXiv:1209.2463v4, §3.1, with the weighting of
§3.2): the vertices of `Γ` and a new vertex `none`; the edges of `Γ`, and for each `j` and `i`
with `α_i^∨(λ_j) = Λ j i ≠ 0` one new edge from `none` to `i` of weight `ϖ j` and polynomial
`(u - v) ^ (Λ j i)`, which stands for Webster's `Λ j i` parallel edges with polynomial `u - v`
(Definition 2.6). The new vertex carries no loop. -/
noncomputable def crawleyBoevey : WeightedGraph (Option I) 𝕜 k where
  E := Γ.E ⊕ RedEdge Λ
  tail := Sum.elim (fun e => some (Γ.tail e)) fun _ => none
  head := Sum.elim (fun e => some (Γ.head e)) fun e => some e.2.1
  weight := Sum.elim Γ.weight fun e => ϖ e.1
  Q := Sum.elim Γ.Q fun e => (X 0 - X 1) ^ (Λ e.1 e.2.1)
  loop := fun o => o.elim none Γ.loop

@[simp] theorem crawleyBoevey_loop_none : (Γ.crawleyBoevey Λ ϖ).loop none = none := rfl

@[simp] theorem crawleyBoevey_loop_some (i : I) :
    (Γ.crawleyBoevey Λ ϖ).loop (some i) = Γ.loop i := rfl

/-- The weight `ν̃ = ν + α_0` of Webster's §3.1: the strands of `ν` and one strand labelled by
the new vertex. -/
noncomputable def redWeight (ν : I →₀ ℕ) : Option I →₀ ℕ :=
  Finsupp.mapDomain some ν + Finsupp.single none 1

omit [DecidableEq I] in
@[simp] theorem redWeight_none (ν : I →₀ ℕ) : redWeight ν none = 1 := by
  simp [redWeight, Finsupp.mapDomain_of_notMem_range]

omit [DecidableEq I] in
@[simp] theorem redWeight_some (ν : I →₀ ℕ) (i : I) : redWeight ν (some i) = ν i := by
  simp [redWeight, Finsupp.mapDomain_apply_of_injective (Option.some_injective I)]

variable {Γ Λ ϖ}

/-- The Crawley-Boevey graph has no loops of weight `0` among its edges if `Γ` has none. -/
theorem crawleyBoevey_noZeroLoops [Zero 𝕜] (hZ : Γ.NoZeroLoops) :
    (Γ.crawleyBoevey Λ ϖ).NoZeroLoops := by
  rintro (e | e) h
  · exact hZ e (Option.some_injective _ h)
  · exact absurd h (Option.some_ne_none _)

/-- **(†) for the Crawley-Boevey graph**: it holds for `Γ_λ` (with merged parallel edges) when it
holds for `Γ` and the weights `ϖ_j` of the new edges are distinct. -/
theorem crawleyBoevey_dagger [Neg 𝕜] (hD : Γ.Dagger) (hϖ : Function.Injective ϖ) :
    (Γ.crawleyBoevey Λ ϖ).Dagger := by
  refine ⟨?_, ?_⟩
  · rintro (e | e) (e' | e') ht hh hw
    · exact congrArg Sum.inl (hD.1 e e' (Option.some_injective _ ht)
        (Option.some_injective _ hh) hw)
    · exact absurd ht (Option.some_ne_none _)
    · exact absurd ht.symm (Option.some_ne_none _)
    · obtain ⟨j, i, hi⟩ := e
      obtain ⟨j', i', hi'⟩ := e'
      have hj : j = j' := hϖ hw
      have hi'' : i = i' := Option.some_injective _ hh
      subst hj hi''
      rfl
  · rintro (e | e) (e' | e') ht hh
    · exact hD.2 e e' (Option.some_injective _ ht) (Option.some_injective _ hh)
    · exact absurd hh (Option.some_ne_none _)
    · exact absurd ht.symm (Option.some_ne_none _)
    · exact absurd hh (Option.some_ne_none _)

/-- The loop polynomials of the Crawley-Boevey graph are those of `Γ`. -/
theorem crawleyBoevey_psymm (hΓ : Γ.PSymm) : (Γ.crawleyBoevey Λ ϖ).PSymm := by
  rintro (_ | i) P hP
  · exact absurd hP (by simp)
  · exact hΓ i P hP

/-- `u - v` substituted into two distinct variables is a non-zero-divisor. -/
theorem isRegular_rename_X_sub_X {σ : Type*} [Finite σ] {f : Fin 2 → σ}
    (hf : Function.Injective f) : IsRegular (rename f (X 0 - X 1 : MvPolynomial (Fin 2) k)) := by
  refine isRegular_rename_of_isUnitHomogeneous hf one_pos one_pos (c := 1) (c' := 1) ?_
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (isWeightedHomogeneous_X k ![1, 1] 0).sub (isWeightedHomogeneous_X k ![1, 1] 1)
  · have : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 0 1 :=
      fun h => absurd (Finsupp.single_left_injective one_ne_zero h) (by decide)
    simp [coeff_X, this]
  · have : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 :=
      fun h => absurd (Finsupp.single_left_injective one_ne_zero h) (by decide)
    simp [coeff_X, this]

variable {ν : Option I →₀ ℕ}

/-- The wall factors of the Crawley-Boevey graph are non-zero-divisors, over any commutative
ring, when `Γ` satisfies Webster's standing hypothesis: for an old edge this is
`Standing.isRegular_factor`, and for a new edge `(j, i)` the factor is `(y_a - y_b) ^ α_i^∨(λ_j)`.
-/
theorem crawleyBoevey_isRegular_factor (hS : Γ.Standing) (w : Wall (Γ.crawleyBoevey Λ ϖ) ν) :
    IsRegular (w.factor (k := k)) := by
  rw [w.factor_eq_rename]
  obtain ⟨⟨e, a, b⟩, -, -, hab⟩ := w
  have hf := injective_vecCons_two hab
  rcases e with e | e
  · obtain ⟨d, hd, hQ, -⟩ := hS
    obtain ⟨c, c', hc⟩ := hQ e
    exact isRegular_rename_of_isUnitHomogeneous hf (hd _) (hd _) hc
  · change IsRegular (rename _ ((X 0 - X 1) ^ _))
    rw [map_pow]
    exact (isRegular_rename_X_sub_X hf).pow _

/-- The loop factors of the Crawley-Boevey graph are non-zero-divisors, over any commutative
ring, when `Γ` satisfies Webster's standing hypothesis. -/
theorem crawleyBoevey_isRegular_loopFactor (hS : Γ.Standing) :
    ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), (Γ.crawleyBoevey Λ ϖ).loop a.1 = some Q →
      a ≠ b → a.1 = b.1 → IsRegular (loopFactor Q a b) := by
  intro P a b hP hab _
  obtain ⟨⟨_ | i, ha⟩, m⟩ := a
  · exact absurd hP (by simp)
  · obtain ⟨d, hd, -, hL⟩ := hS
    obtain ⟨-, c, c', hc⟩ := hL i P hP
    have := isRegular_rename_of_isUnitHomogeneous (injective_vecCons_two hab) (hd _) (hd _) hc
    rw [map_mul] at this
    rw [loopFactor_eq_rename]
    exact (isRegular_mul_iff.1 this).2

end WeightedGraph

namespace GalleryAlgebra

open WeightedGraph

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {Γ : WeightedGraph I 𝕜 k} {ℓ : ℕ}
  {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜} {ν : Option I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-- **Webster, Theorem 2.8 (basis theorem)** for the weighted KLR algebra of the Crawley-Boevey
graph `Γ_λ` (arXiv:1209.2463v4, §3.1), for a choice `P` of simple segments: the elements
`r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)` form a `k`-basis, when `Γ` satisfies
the standing hypothesis and (†) and the weights `ϖ_j` are distinct. -/
noncomputable def redBasis
    {P : FullChamber (Γ.crawleyBoevey Λ ϖ) ν → FullChamber (Γ.crawleyBoevey Λ ϖ) ν →
      (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hϖ : Function.Injective ϖ) :
    Module.Basis (RankChamber (Γ.crawleyBoevey Λ ϖ) ν × RankChamber (Γ.crawleyBoevey Λ ϖ) ν ×
      ColPerm ν × (Strand ν →₀ ℕ)) k (weightedKLR k (Γ.crawleyBoevey Λ ϖ) ν) :=
  weightedKLRBasis hP (crawleyBoevey_dagger hD hϖ) (crawleyBoevey_noZeroLoops hZ)
    (crawleyBoevey_psymm hS.psymm) (crawleyBoevey_isRegular_factor hS)
    (crawleyBoevey_isRegular_loopFactor hS)

@[simp]
theorem redBasis_apply
    {P : FullChamber (Γ.crawleyBoevey Λ ϖ) ν → FullChamber (Γ.crawleyBoevey Λ ϖ) ν →
      (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hϖ : Function.Injective ϖ) (C D : RankChamber (Γ.crawleyBoevey Λ ϖ) ν)
    (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (redBasis hP hD hZ hS hϖ (C, D, g, m) : GalleryAlgebra k (Γ.crawleyBoevey Λ ϖ) ν) =
      r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) :=
  weightedKLRBasis_apply _ _ _ _ _ _ C D g m

/-- **Webster, Theorem 2.8 (basis theorem)** for the weighted KLR algebra of the Crawley-Boevey
graph `Γ_λ` (arXiv:1209.2463v4, §3.1): when `Γ` satisfies the standing hypothesis and (†) and
the weights `ϖ_j` of the new edges are distinct, for some choice of simple segments `P` the
elements `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)` (loadings `C`, `D`,
colour-preserving permutations `g`, monomials `m`) form a `k`-basis. This applies in particular
to the weight `ν̃ = redWeight ν` of Webster's Theorem 3.5. -/
theorem exists_redBasis (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (hϖ : Function.Injective ϖ) :
    ∃ P : FullChamber (Γ.crawleyBoevey Λ ϖ) ν → FullChamber (Γ.crawleyBoevey Λ ϖ) ν →
        (Strand ν → 𝕜) × (Strand ν → 𝕜),
      ∃ b : Module.Basis (RankChamber (Γ.crawleyBoevey Λ ϖ) ν ×
          RankChamber (Γ.crawleyBoevey Λ ϖ) ν × ColPerm ν × (Strand ν →₀ ℕ)) k
          (weightedKLR k (Γ.crawleyBoevey Λ ϖ) ν), ∀ C D g m,
        (b (C, D, g, m) : GalleryAlgebra k (Γ.crawleyBoevey Λ ϖ) ν) =
          r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) (crawleyBoevey_dagger hD hϖ)
    (crawleyBoevey_noZeroLoops (Λ := Λ) (ϖ := ϖ) hZ)
  exact ⟨P, redBasis hP hD hZ hS hϖ, redBasis_apply hP hD hZ hS hϖ⟩

end GalleryAlgebra

end Categorification.WeightedKLR
