/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidLengthInduction
import Categorification.WeightedKLR.RedStrands.BraidingFunctorCompTor

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of derived braiding functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 6.12,
second clause: if `w > w s_i` then `𝔅_w ≅ 𝔅_{w s_i} ⊗ᴸ 𝔅_i`. In the red-order form, for
permutations `τ` and `s ≠ 1` of the red strands whose lengths add (every pair of strands crossed
by `τ` is still crossed by `τ s`), and the red orders `κ₂ = (1, …, ℓ)`, `κ₁ = τ κ₂`,
`κ₀ = τ s κ₂` of one algebra, `𝔅(κ₂, κ₁) ⋙ 𝔅(κ₁, κ₀) ≅ 𝔅(κ₂, κ₀)` on the whole derived
category (`braidingFunctorCompIsoOfLengthAdd`). Webster's statement is the case of an adjacent
transposition `s = s_i`.

The vanishing of the higher `Tor` (`isZero_braidingFunctor_homology_of_lengthAdd`) comes from the
standard filtrations of Lemma 6.11 (`hasCornerStandardFiltration_braidF`) for `τ ≠ 1`, and from
the projectivity of the corner for `τ = 1`.

Route hypotheses: those of Corollary 6.10 (`AllFiniteDeltaInjective`,
`RowFigureFiveHypotheses`), through Lemma 6.11.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF Equiv
open BraidedStendhalAlgebra ModuleFiltration CategoryTheory CategoryTheory.Limits
open scoped List RatFunc
open DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]

include hR in
/-- **The higher `Tor` of composable braiding bimodules vanish** (Webster, arXiv:1309.3796v3,
proof of Lemma 6.12, step `s_n + f_n → p_{n+1}`): for `s ≠ 1`, `B(κ₂, κ₁) ⊗ᴸ B(κ₁, κ₀)` has
homology only in degree `0`, for the red orders `κ₂ = (1, …, ℓ)`, `κ₁ = τ κ₂`, `κ₀ = τ s κ₂`.
Route hypotheses: those of Corollary 6.10, through Lemma 6.11. -/
theorem isZero_braidingFunctor_homology_of_lengthAdd
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (τ s : Perm (Fin ℓ)) (hs : s ≠ 1) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (isIdempotentElem_violMk_redProj k Q Λ ν
        ((List.finRange ℓ).map ⇑(τ * s))).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor.{0} k Q Λ ν ((List.finRange ℓ).map τ) ((List.finRange ℓ).map ⇑(τ * s))).obj
        (DG.DerivedCategory.Q.obj (DG.DGModuleCat.of
          (isIdempotentElem_violMk_redProj k Q Λ ν ((List.finRange ℓ).map τ)).Cornerᵐᵒᵖ
          (cornerOpDZ (isIdempotentElem_violMk_redProj k Q Λ ν (List.finRange ℓ))
            (violMk k Q Λ ν (redProj k Q Λ ν ((List.finRange ℓ).map τ)))))))) := by
  by_cases hτ : τ = 1
  · subst hτ
    exact isZero_braidingFunctor_braidingBimodule_self_homology (by simp) n hn
  · exact isZero_braidingFunctor_braidingBimodule_homology.{0} (isReducedChoice_canChoice ν)
      hQ.klrSymm hQ Λ τ s hall
      (fun t ht => hasCornerStandardFiltration_braidF.{0} C hQ hR hall H τ hτ Λ wt hwt t ht)
      (fun t ht => hasCornerStandardFiltration_braidF.{0} C hQ hR hall H s⁻¹ (inv_ne_one.2 hs)
        ((Λ ∘ τ) ∘ s) ((wt ∘ τ) ∘ s) (fun r i => hwt (τ (s r)) i) t ht) n hn

include hR in
/-- **Webster, Lemma 6.12, second clause** (arXiv:1309.3796v3), red-order form: for permutations
`τ` and `s ≠ 1` of the red strands whose lengths add (every pair of strands crossed by `τ` is
still crossed by `τ s`), the derived braiding functors compose:
`𝔅((1, …, ℓ), τ) ⋙ 𝔅(τ, τ s) ≅ 𝔅((1, …, ℓ), τ s)`. Webster's statement is the case of an
adjacent transposition `s`. Route hypotheses: those of Corollary 6.10
(`AllFiniteDeltaInjective`, `RowFigureFiveHypotheses`), through Lemma 6.11. -/
def braidingFunctorCompIsoOfLengthAdd
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (τ s : Perm (Fin ℓ)) (hs : s ≠ 1)
    (hL : ∀ x y, [x, y] <+ (List.finRange ℓ).map ⇑(τ * s) → [y, x] <+ (List.finRange ℓ).map τ →
      [y, x] <+ List.finRange ℓ) :
    braidingFunctor.{0} k Q Λ ν (List.finRange ℓ) ((List.finRange ℓ).map τ) ⋙
        braidingFunctor.{0} k Q Λ ν ((List.finRange ℓ).map τ) ((List.finRange ℓ).map ⇑(τ * s)) ≅
      braidingFunctor.{0} k Q Λ ν (List.finRange ℓ) ((List.finRange ℓ).map ⇑(τ * s)) :=
  braidingFunctorCompIso (isReducedChoice_canChoice ν) hQ.klrSymm
    ((List.nodup_finRange ℓ).map (τ * s).injective)
    ((List.perm_ext_iff_of_nodup ((List.nodup_finRange ℓ).map (τ * s).injective)
      ((List.nodup_finRange ℓ).map τ.injective)).2 fun a => by
        simp only [List.mem_map, List.mem_finRange, true_and]
        exact ⟨fun _ => ⟨τ.symm a, τ.apply_symm_apply a⟩,
          fun _ => ⟨(τ * s).symm a, (τ * s).apply_symm_apply a⟩⟩) hL
    (isZero_braidingFunctor_homology_of_lengthAdd C hQ hR hall H Λ wt hwt ν τ s hs)

end Categorification.Stendhal.FirstWeight
