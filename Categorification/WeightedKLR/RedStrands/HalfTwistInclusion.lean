/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistRedFirst

set_option backward.isDefEq.respectTransparency false

/-!
# The maps `ι` and `π` of the half twist

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. For a red-ordered top loading `t`, let `θ_t ∈ e(t) V e(t⁰)` be the red/black
shuffle from the red-first loading `t⁰ = τ_t • t` and `θ̇_t ∈ e(t⁰) V e(t)` its mirror image.
On the cuts of a bottom red order `κ`, left multiplication gives
`π = θ_t · : e(t⁰) V e_κ → e(t) V e_κ` and `ι = θ̇_t · : e(t) V e_κ → e(t⁰) V e_κ`, with
`ι π = y ·` for `y = θ̇_t θ_t`. When `κ` reverses every pair of red strands, `π` is surjective
(`violCorner_le_map_redShuffle`), so the image of `ι` is `y · e(t⁰) V e_κ`
(`map_violShuffleDual_violCorner`). If `ι` is injective, it identifies `e(t) V e_κ` with this
image (`halfTwistInclusionEquiv`).

## Main results

* `violShuffleDual`, `halfTwistY`: `θ̇_t` and `y = θ̇_t θ_t`.
* `map_violShuffleDual_violCorner`: `ι (e(t) V e_κ) = y · e(t⁰) V e_κ`.
* `halfTwistInclusionEquiv`: `e(t) V e_κ ≅ y · e(t⁰) V e_κ` when `ι` is injective.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open Equiv KLR TypeA KLRAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I} {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "ι" => ofKLR k Q Λ ν

/-- The mirror image `θ̇_t ∈ e(τ_t • t) V e(t)` of the red/black shuffle. -/
def violShuffleDual (t : Seq μ) : ViolQuotient k Q Λ ν :=
  violMk k Q Λ ν (ι (KLRAlgebra.e (redShufflePerm t • t) *
    ψw (canWord m (redShufflePerm t)⁻¹).reverse * KLRAlgebra.e t))

/-- The element `y = θ̇_t θ_t` of the red-first cut. -/
def halfTwistY (t : Seq μ) : ViolQuotient k Q Λ ν :=
  violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * violShuffle (k := k) (Q := Q) (Λ := Λ) t

/-- Left multiplication by an element `e(s) a e(s')` sends the cut at `s'` to the cut at `s`. -/
theorem mul_mem_violCorner (s s' : Seq μ) (a : KLRAlgebra k (stendhalQ Q Λ) μ) {κ : List (Fin ℓ)}
    {v : ViolQuotient k Q Λ ν} (hv : v ∈ violCorner k Q Λ ν s' κ) :
    violMk k Q Λ ν (ι (KLRAlgebra.e s * a * KLRAlgebra.e s')) * v ∈ violCorner k Q Λ ν s κ := by
  obtain ⟨b, rfl⟩ := hv
  refine ⟨ι (a * KLRAlgebra.e s') * b, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, mul_assoc]
  have he : ∀ z, violMk k Q Λ ν (ι (KLRAlgebra.e s')) * (violMk k Q Λ ν (ι (KLRAlgebra.e s')) * z)
      = violMk k Q Λ ν (ι (KLRAlgebra.e s')) * z := fun z => by
    rw [← mul_assoc, ← map_mul, ← map_mul, KLRAlgebra.e_mul_e,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  simp only [he]

theorem violShuffle_mul_mem {t : Seq μ} {κ : List (Fin ℓ)} {v : ViolQuotient k Q Λ ν}
    (hv : v ∈ violCorner k Q Λ ν (redShufflePerm t • t) κ) :
    violShuffle (k := k) (Q := Q) (Λ := Λ) t * v ∈ violCorner k Q Λ ν t κ :=
  mul_mem_violCorner _ _ _ hv

theorem violShuffleDual_mul_mem {t : Seq μ} {κ : List (Fin ℓ)} {v : ViolQuotient k Q Λ ν}
    (hv : v ∈ violCorner k Q Λ ν t κ) :
    violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * v ∈
      violCorner k Q Λ ν (redShufflePerm t • t) κ :=
  mul_mem_violCorner _ _ _ hv

/-- **The image of `ι`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14): when `κ` reverses
every pair of red strands, `θ̇_t · e(t) V e_κ = y · e(t⁰) V e_κ`. -/
theorem map_violShuffleDual_violCorner (hQ : KLRSymm Q) (t : Seq μ) (ht : IsRedOrdered t)
    (κ : List (Fin ℓ)) (hκ : ∀ t' : Seq μ, redWord t' = κ → IsRedReversed t') :
    (violCorner k Q Λ ν t κ).map
        (LinearMap.mulLeft k (violShuffleDual (k := k) (Q := Q) (Λ := Λ) t)) =
      (violCorner k Q Λ ν (redShufflePerm t • t) κ).map
        (LinearMap.mulLeft k (halfTwistY (k := k) (Q := Q) (Λ := Λ) t)) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨p, hp, rfl⟩ := violCorner_le_map_redShuffle hQ t ht κ hκ hv
    exact ⟨p, hp, by simp [halfTwistY]⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨_, violShuffle_mul_mem hp, by simp [halfTwistY]⟩

/-- **`ι` as an isomorphism onto its image** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14): if left multiplication by `θ̇_t` is injective on `e(t) V e_κ`, it identifies
`e(t) V e_κ` with `y · e(t⁰) V e_κ`. The injectivity is an input here (Webster deduces it from
Lemma 5.25 and the exactness of `𝔅_τ` on standardly filtered modules). -/
def halfTwistInclusionEquiv (hQ : KLRSymm Q) (t : Seq μ) (ht : IsRedOrdered t)
    (κ : List (Fin ℓ)) (hκ : ∀ t' : Seq μ, redWord t' = κ → IsRedReversed t')
    (hinj : ∀ v ∈ violCorner k Q Λ ν t κ,
      violShuffleDual (k := k) (Q := Q) (Λ := Λ) t * v = 0 → v = 0) :
    violCorner k Q Λ ν t κ ≃ₗ[k]
      (violCorner k Q Λ ν (redShufflePerm t • t) κ).map
        (LinearMap.mulLeft k (halfTwistY (k := k) (Q := Q) (Λ := Λ) t)) :=
  (LinearEquiv.ofInjective ((LinearMap.mulLeft k
      (violShuffleDual (k := k) (Q := Q) (Λ := Λ) t)).comp (violCorner k Q Λ ν t κ).subtype)
    (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact Subtype.ext (hinj v.1 v.2 hv))).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact map_violShuffleDual_violCorner hQ t ht κ hκ))

end Categorification.Stendhal.BraidedStendhalAlgebra
