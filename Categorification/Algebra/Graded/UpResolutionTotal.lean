/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolutionBootstrap

/-!
# Resolutions in `C↑` from resolutions by resolved modules

Let `A` be a finite-dimensional graded algebra over a field `k`. Suppose a finite-dimensional
graded module `N` has a resolution `⋯ → X_1 → X_0 → N → 0` by finite-dimensional graded modules,
in which each `X_n` has a graded projective resolution in `C↑` with constant `c - n`. Then `N`
has a resolution in `C↑` with constant `c` (`GFin.UpResolution.ofResolution`): this is the total
complex of the double complex of resolutions, built here one homological degree at a time by the
bootstrapping lemma (`GFin.Bootstrap.upResolution`).

This is the gluing step of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.28 (general case), where the standardization of a
projective resolution is replaced by finite projective resolutions of its standard terms
(Corollary 5.24); the shifts of these finite resolutions are bounded uniformly, which gives the
constants `c - n`.

## Main results

* `GFin.UpResolution.ofResolution`.
-/

noncomputable section

namespace Categorification.Graded

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

namespace GFin

namespace UpResolution

variable (Ω X : ℕ → GFin 𝒜) (c : ℤ)

/-- The syzygies shifted to a uniform constant. -/
private abbrev shiftedSyz (n : ULift.{u} ℕ) : GFin 𝒜 := (Ω n.down).shift (-(n.down : ℤ))

private def shiftIso (n : ℕ) :
    (((Ω (n + 1)).shift (-((n + 1 : ℕ) : ℤ))).shift 1).Iso ((Ω (n + 1)).shift (-(n : ℤ))) :=
  (GMod.shiftShiftIso (Ω (n + 1)).toGMod _ 1).trans
    (GradedEquiv.ofEq (by
      change Graded.shift (Ω (n + 1)).grading _ = Graded.shift (Ω (n + 1)).grading _
      congr 1
      push_cast
      ring))

/-- **Resolutions by resolved modules.** If `0 → Ω_{n+1} → X_n → Ω_n → 0` are short exact and
each `X_n` has a resolution in `C↑` with constant `c - n`, then `Ω_0` has a resolution in `C↑`
with constant `c`. -/
def ofResolution (S : ∀ n, ShortExact (Ω (n + 1)) (X n) (Ω n))
    (R : ∀ n, UpResolution (X n) (c - n)) : UpResolution (Ω 0) c :=
  let pres : ∀ n : ULift.{u} ℕ, Bootstrap.Pres (shiftedSyz Ω) c n := fun n =>
    { M := (X n.down).shift (-(n.down : ℤ))
      K := (Ω (n.down + 1)).shift (-(n.down : ℤ))
      res := ((R n.down).shift (-(n.down : ℤ))).mono (by omega)
      ses := (S n.down).shift (-(n.down : ℤ))
      cert := .iso (shiftIso Ω n.down)
        (Bootstrap.Cert.atom (L := shiftedSyz Ω) ⟨n.down + 1⟩ 1 (by omega)) }
  (Bootstrap.upResolution pres ⟨0⟩).congr
    (GradedEquiv.ofEq (by
      change Graded.shift (Ω 0).grading _ = (Ω 0).grading
      rw [Nat.cast_zero, neg_zero]
      exact Graded.shift_zero _))

end UpResolution

end GFin

end Categorification.Graded
