/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.G0

/-!
# Euler characteristics of finite resolutions

A finite resolution `0 → M_n → ⋯ → M_0 → N → 0` of finite-dimensional graded modules is recorded
by its chain of short exact sequences `0 → K_{j+1} → M_j → K_j → 0` with `K_0 = N`
(`GFin.Resolution N [M_0, …, M_n]`). Any invariant that is additive in short exact sequences takes
the alternating sum of its values on the terms at `N` (`GFin.Resolution.eq_altSum`). A functor that
preserves the short exact sequences of the chain (an exact functor, or one with vanishing higher
`Tor` against the resolved module) carries a resolution to a resolution
(`GFin.Resolution.map`). This is how classes of modules of finite projective dimension are read
in the Grothendieck group of projectives, as in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v2, proof of Corollary 6.10.

## Main definitions and results

* `altSum l` : `l₀ - l₁ + l₂ - ⋯`.
* `GFin.Resolution N l` : a resolution of `N` by the terms `l`.
* `GFin.Resolution.eq_altSum` : `f N = altSum (l.map f)` for an additive `f`.
* `GFin.Resolution.map` : resolutions are carried along maps preserving their exact sequences.
-/

namespace Categorification.Graded

universe u v w

/-- The alternating sum `l₀ - l₁ + l₂ - ⋯`. -/
def altSum {G : Type*} [AddCommGroup G] : List G → G
  | [] => 0
  | a :: l => a - altSum l

@[simp] theorem altSum_nil {G : Type*} [AddCommGroup G] : altSum ([] : List G) = 0 := rfl

@[simp] theorem altSum_cons {G : Type*} [AddCommGroup G] (a : G) (l : List G) :
    altSum (a :: l) = a - altSum l := rfl

theorem map_altSum {G H F : Type*} [AddCommGroup G] [AddCommGroup H] [FunLike F G H]
    [AddMonoidHomClass F G H] (f : F) : ∀ l : List G, f (altSum l) = altSum (l.map f)
  | [] => map_zero f
  | a :: l => by rw [altSum_cons, map_sub, map_altSum f l, List.map_cons, altSum_cons]

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-- **A resolution of `N` by `l`**: short exact sequences `0 → K_{j+1} → l_j → K_j → 0` with
`K_0 = N`, ending with `K_n ≅ l_n`. -/
inductive GFin.Resolution : GFin 𝒜 → List (GFin 𝒜) → Type (max (u + 1) v)
  | single {N P : GFin 𝒜} : N.Iso P → GFin.Resolution N [P]
  | cons {K P N : GFin 𝒜} {l : List (GFin 𝒜)} :
      GFin.ShortExact K P N → GFin.Resolution K l → GFin.Resolution N (P :: l)

/-- **Euler characteristic**: an invariant additive in short exact sequences takes the alternating
sum of its values on a resolution. -/
theorem GFin.Resolution.eq_altSum {G : Type*} [AddCommGroup G] (f : GFin 𝒜 → G)
    (hiso : ∀ {N N' : GFin 𝒜}, N.Iso N' → f N = f N')
    (hses : ∀ {K P N : GFin 𝒜}, GFin.ShortExact K P N → f P = f K + f N)
    {N : GFin 𝒜} {l : List (GFin 𝒜)} (r : GFin.Resolution N l) : f N = altSum (l.map f) := by
  induction r with
  | single e => simp [hiso e]
  | cons S _ ih => rw [List.map_cons, altSum_cons, ← ih, hses S, add_sub_cancel_left]

variable {B : Type w} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}

/-- `F` preserves the short exact sequences of the resolution `r`: for a right exact `F` this is
the vanishing of its higher left derived functors at the resolved module. -/
def GFin.Resolution.Preserved (F : GFin 𝒜 → GFin ℬ) :
    {N : GFin 𝒜} → {l : List (GFin 𝒜)} → GFin.Resolution N l → Prop
  | _, _, .single _ => True
  | _, _, .cons (K := K) (P := P) (N := N) _ r =>
      Nonempty (GFin.ShortExact (F K) (F P) (F N)) ∧ GFin.Resolution.Preserved F r

/-- A map of modules preserving isomorphisms and the short exact sequences of a resolution
carries it to a resolution. -/
theorem GFin.Resolution.map (F : GFin 𝒜 → GFin ℬ)
    (hiso : ∀ {N N' : GFin 𝒜}, N.Iso N' → Nonempty ((F N).Iso (F N')))
    {N : GFin 𝒜} {l : List (GFin 𝒜)} (r : GFin.Resolution N l) (hr : r.Preserved F) :
    Nonempty (GFin.Resolution (F N) (l.map F)) := by
  induction r with
  | single e => obtain ⟨e'⟩ := hiso e; exact ⟨.single e'⟩
  | cons S r ih =>
    obtain ⟨⟨S'⟩, hr⟩ := hr
    obtain ⟨r'⟩ := ih hr
    exact ⟨.cons S' r'⟩

end Categorification.Graded
