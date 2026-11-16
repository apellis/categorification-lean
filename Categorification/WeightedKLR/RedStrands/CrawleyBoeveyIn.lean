/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.Reduced

/-!
# The Crawley-Boevey graph with new edges into the new vertex

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §3.1 and §3.2.

## Scope note: orientation of the new edges

Webster's §3.1 directs the new edges of the Crawley-Boevey graph `Γ_λ` from the new vertex `0`
to `i` (`WeightedGraph.crawleyBoevey`). Since the ghost of an edge belongs to the strand labelled
by its head, the crossings of the `0`-strand then sit at `x_0 - ϖ_j`, and for
`ϖ_1 < ⋯ < ϖ_ℓ` they read `λ_ℓ, …, λ_1` from left to right. The statement and proof of
Theorem 3.5 (the `p`-th ghost of the `0`-labelled strand from the left carries `λ_p`), the order
`λ_1, …, λ_ℓ` of red strands in the tensor product algebras of arXiv:1309.3796v2, and the
violating ideal of Theorem 3.6 (a black strand at the far left) need the opposite orientation:
new edges from `i` to `0`, so that the `0`-strand is the head and its ghosts sit at `x_0 + ϖ_j`.
This module records that orientation as `WeightedGraph.crawleyBoeveyIn`. The two graphs give
isomorphic weighted KLR algebras by reversing each new edge and negating its weight (the
hyperplane `x_h - x_t = ϖ` is the hyperplane `x_t - x_h = -ϖ`); Theorems 3.5 and 3.6 are stated
here for `crawleyBoeveyIn`.

Parallel new edges are merged as in `CrawleyBoevey.lean` (Webster's Definition 2.6): one edge
`(j, i)` from `i` to `0` of weight `ϖ_j` with polynomial `(u - v) ^ α_i^∨(λ_j)`.

## Main definitions

* `WeightedGraph.crawleyBoeveyIn Γ Λ ϖ`: the Crawley-Boevey graph with new edges `i → 0`.

## Main results

* `WeightedGraph.crawleyBoeveyIn_dagger`, `crawleyBoeveyIn_isRegular_factor`,
  `crawleyBoeveyIn_isRegular_loopFactor`: the hypotheses of Webster's Theorem 2.8.
* `GalleryAlgebra.redBasisIn`, `GalleryAlgebra.exists_redBasisIn`: Theorem 2.8 for it.
* `GalleryAlgebra.redReducedBasisIn`: the basis of its reduced quotient.
-/

namespace Categorification.WeightedKLR

open MvPolynomial

variable {I : Type} [DecidableEq I] {𝕜 : Type*} {k : Type*} [CommRing k]

namespace WeightedGraph

variable (Γ : WeightedGraph I 𝕜 k) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ϖ : Fin ℓ → 𝕜)

/-- **Webster's Crawley-Boevey graph** `Γ_λ` (arXiv:1209.2463v4, §3.1, with the weighting of
§3.2) **with the new edges directed into the new vertex**, the orientation used in the proof of
Theorem 3.5 (see the module docstring): the vertices of `Γ` and a new vertex `none`; the edges
of `Γ`, and for each `j` and `i` with `α_i^∨(λ_j) = Λ j i ≠ 0` one new edge from `i` to `none`
of weight `ϖ j` and polynomial `(u - v) ^ (Λ j i)` (Webster's `Λ j i` parallel edges merged as in
Definition 2.6). The new vertex carries no loop. -/
noncomputable def crawleyBoeveyIn : WeightedGraph (Option I) 𝕜 k where
  E := Γ.E ⊕ RedEdge Λ
  tail := Sum.elim (fun e => some (Γ.tail e)) fun e => some e.2.1
  head := Sum.elim (fun e => some (Γ.head e)) fun _ => none
  weight := Sum.elim Γ.weight fun e => ϖ e.1
  Q := Sum.elim Γ.Q fun e => (X 0 - X 1) ^ (Λ e.1 e.2.1)
  loop := fun o => o.elim none Γ.loop

@[simp] theorem crawleyBoeveyIn_loop_none : (Γ.crawleyBoeveyIn Λ ϖ).loop none = none := rfl

@[simp] theorem crawleyBoeveyIn_loop_some (i : I) :
    (Γ.crawleyBoeveyIn Λ ϖ).loop (some i) = Γ.loop i := rfl

variable {Γ Λ ϖ}

/-- `crawleyBoeveyIn` has no loops of weight `0` among its edges if `Γ` has none. -/
theorem crawleyBoeveyIn_noZeroLoops [Zero 𝕜] (hZ : Γ.NoZeroLoops) :
    (Γ.crawleyBoeveyIn Λ ϖ).NoZeroLoops := by
  rintro (e | e) h
  · exact hZ e (Option.some_injective _ h)
  · exact absurd h (by simp [crawleyBoeveyIn])

/-- **(†) for the Crawley-Boevey graph with new edges `i → 0`**: it holds when it holds for `Γ`
and the weights `ϖ_j` are distinct. -/
theorem crawleyBoeveyIn_dagger [Neg 𝕜] (hD : Γ.Dagger) (hϖ : Function.Injective ϖ) :
    (Γ.crawleyBoeveyIn Λ ϖ).Dagger := by
  refine ⟨?_, ?_⟩
  · rintro (e | e) (e' | e') ht hh hw
    · exact congrArg Sum.inl (hD.1 e e' (Option.some_injective _ ht)
        (Option.some_injective _ hh) hw)
    · exact absurd hh (by simp [crawleyBoeveyIn])
    · exact absurd hh.symm (by simp [crawleyBoeveyIn])
    · obtain ⟨j, i, hi⟩ := e
      obtain ⟨j', i', hi'⟩ := e'
      have hj : j = j' := hϖ hw
      have hi'' : i = i' := Option.some_injective _ ht
      subst hj hi''
      rfl
  · rintro (e | e) (e' | e') ht hh
    · exact hD.2 e e' (Option.some_injective _ ht) (Option.some_injective _ hh)
    · exact absurd ht (by simp [crawleyBoeveyIn])
    · exact absurd hh.symm (by simp [crawleyBoeveyIn])
    · exact absurd ht.symm (by simp [crawleyBoeveyIn])

/-- The loop polynomials of `crawleyBoeveyIn` are those of `Γ`. -/
theorem crawleyBoeveyIn_psymm (hΓ : Γ.PSymm) : (Γ.crawleyBoeveyIn Λ ϖ).PSymm := by
  rintro (_ | i) P hP
  · exact absurd hP (by simp)
  · exact hΓ i P hP

variable {ν : Option I →₀ ℕ}

/-- The wall factors of `crawleyBoeveyIn` are non-zero-divisors, over any commutative ring, when
`Γ` satisfies Webster's standing hypothesis. -/
theorem crawleyBoeveyIn_isRegular_factor (hS : Γ.Standing)
    (w : Wall (Γ.crawleyBoeveyIn Λ ϖ) ν) : IsRegular (w.factor (k := k)) := by
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

/-- The loop factors of `crawleyBoeveyIn` are non-zero-divisors, over any commutative ring, when
`Γ` satisfies Webster's standing hypothesis. -/
theorem crawleyBoeveyIn_isRegular_loopFactor (hS : Γ.Standing) :
    ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), (Γ.crawleyBoeveyIn Λ ϖ).loop a.1 = some Q →
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
graph with new edges `i → 0` (arXiv:1209.2463v4, §3.1; see the module docstring), for a choice
`P` of simple segments, when `Γ` satisfies the standing hypothesis and (†) and the weights `ϖ_j`
are distinct. -/
noncomputable def redBasisIn
    {P : FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν → FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν →
      (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hϖ : Function.Injective ϖ) :
    Module.Basis (RankChamber (Γ.crawleyBoeveyIn Λ ϖ) ν × RankChamber (Γ.crawleyBoeveyIn Λ ϖ) ν ×
      ColPerm ν × (Strand ν →₀ ℕ)) k (weightedKLR k (Γ.crawleyBoeveyIn Λ ϖ) ν) :=
  weightedKLRBasis hP (crawleyBoeveyIn_dagger hD hϖ) (crawleyBoeveyIn_noZeroLoops hZ)
    (crawleyBoeveyIn_psymm hS.psymm) (crawleyBoeveyIn_isRegular_factor hS)
    (crawleyBoeveyIn_isRegular_loopFactor hS)

@[simp]
theorem redBasisIn_apply
    {P : FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν → FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν →
      (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hϖ : Function.Injective ϖ)
    (C D : RankChamber (Γ.crawleyBoeveyIn Λ ϖ) ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (redBasisIn hP hD hZ hS hϖ (C, D, g, m) : GalleryAlgebra k (Γ.crawleyBoeveyIn Λ ϖ) ν) =
      r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) :=
  weightedKLRBasis_apply _ _ _ _ _ _ C D g m

/-- **Webster, Theorem 2.8 (basis theorem)** for the weighted KLR algebra of the Crawley-Boevey
graph with new edges `i → 0` (arXiv:1209.2463v4, §3.1): when `Γ` satisfies the standing
hypothesis and (†) and the weights `ϖ_j` are distinct, for some choice of simple segments `P`
the elements `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)` form a `k`-basis. -/
theorem exists_redBasisIn (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (hϖ : Function.Injective ϖ) :
    ∃ P : FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν → FullChamber (Γ.crawleyBoeveyIn Λ ϖ) ν →
        (Strand ν → 𝕜) × (Strand ν → 𝕜),
      ∃ b : Module.Basis (RankChamber (Γ.crawleyBoeveyIn Λ ϖ) ν ×
          RankChamber (Γ.crawleyBoeveyIn Λ ϖ) ν × ColPerm ν × (Strand ν →₀ ℕ)) k
          (weightedKLR k (Γ.crawleyBoeveyIn Λ ϖ) ν), ∀ C D g m,
        (b (C, D, g, m) : GalleryAlgebra k (Γ.crawleyBoeveyIn Λ ϖ) ν) =
          r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) (crawleyBoeveyIn_dagger hD hϖ)
    (crawleyBoeveyIn_noZeroLoops (Λ := Λ) (ϖ := ϖ) hZ)
  exact ⟨P, redBasisIn hP hD hZ hS hϖ, redBasisIn_apply hP hD hZ hS hϖ⟩

variable {J : Type} [DecidableEq J] {Γ' : WeightedGraph J 𝕜 k} {Λ' : Fin ℓ → J →₀ ℕ}

/-- **The basis of Webster's reduced quotient** `W̄^ϑ_ν̃` for the Crawley-Boevey graph with new
edges `i → 0` (arXiv:1209.2463v4, §3.1, the basis used in the proof of Theorem 3.5): the images
of the basis elements of Theorem 2.8 with no dot on the `0`-labelled strand form a `k`-basis,
when `Γ` satisfies the standing hypothesis and (†) and the weights `ϖ_j` are distinct. -/
noncomputable def redReducedBasisIn (ν : J →₀ ℕ)
    {P : FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      (Strand (redWeight ν) → 𝕜) × (Strand (redWeight ν) → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ'.Dagger) (hZ : Γ'.NoZeroLoops)
    (hS : Γ'.Standing) (hϖ : Function.Injective ϖ) :
    Module.Basis {i : RankChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) ×
        RankChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) × ColPerm (redWeight ν) ×
        (Strand (redWeight ν) →₀ ℕ) // i.2.2.2 (zeroStrand ν) = 0} k
      (ReducedQuotient k (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) (zeroStrand ν)) :=
  reducedBasis hP (crawleyBoeveyIn_dagger hD hϖ) (crawleyBoeveyIn_noZeroLoops hZ)
    (crawleyBoeveyIn_psymm hS.psymm) (crawleyBoeveyIn_isRegular_factor hS)
    (crawleyBoeveyIn_isRegular_loopFactor hS) (redWeight_zeroStrand ν)

theorem redReducedBasisIn_apply (ν : J →₀ ℕ)
    {P : FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      (Strand (redWeight ν) → 𝕜) × (Strand (redWeight ν) → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ'.Dagger) (hZ : Γ'.NoZeroLoops)
    (hS : Γ'.Standing) (hϖ : Function.Injective ϖ) (i) :
    redReducedBasisIn ν hP hD hZ hS hϖ i = reducedMk k _ _ _ (algebraBasis hP
      (crawleyBoeveyIn_dagger hD hϖ) (crawleyBoeveyIn_noZeroLoops hZ)
      (crawleyBoeveyIn_psymm hS.psymm) (crawleyBoeveyIn_isRegular_factor hS)
      (crawleyBoeveyIn_isRegular_loopFactor hS) i.1) :=
  reducedBasis_apply _ _ _ _ _ _ _ i

end GalleryAlgebra

end Categorification.WeightedKLR
