/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolution

/-!
# Resolutions in `C↑` by bootstrapping along positive shifts

Let `A` be a finite-dimensional graded algebra over a field `k`, and let `L_i` be a family of
finite-dimensional graded modules. Suppose each `L_i` is a quotient `M_i ↠ L_i` of a module
with a graded projective resolution in `C↑` (constant `c`), whose kernel is built by extensions
from modules with resolutions (constant `c - 1`) and from *positive* shifts `L_j{s}`, `s ≥ 1`,
of the family. Then every `L_i` has a resolution in `C↑` with constant `c`
(`GFin.Bootstrap.upResolution`).

The kernel may contain shifted copies of the module being resolved: the resolution is built one
homological degree at a time, and the shift `s ≥ 1` of each copy compensates the step in
homological degree. This is the bookkeeping behind the inductive step of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of Theorem 5.28,
where the cyclotomic induction of a simple module has its head in degree zero and further copies
of the head only in positive degrees.

## Main definitions and results

* `GFin.Bootstrap.Cert L c₀ N c` : a certificate that `N` has a resolution in `C↑` with constant
  `c`, built from resolutions, positive shifts of the family `L` and extensions.
* `GFin.Bootstrap.Cert.step` : one step of the resolution (a projective cover in the right
  degrees, and a certificate for its kernel with constant `c - 1`).
* `GFin.Bootstrap.Cert.toUpResolution`, `GFin.Bootstrap.upResolution`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Function

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

namespace GFin

namespace Bootstrap

variable {ι : Type u} (L : ι → GFin 𝒜) (c₀ : ℤ)

/-- Certificates that `N` has a resolution in `C↑` with constant `c`: resolutions, shifts
`L_i{s}` with `c₀ - s ≤ c`, extensions and isomorphisms. -/
inductive Cert : GFin 𝒜 → ℤ → Type (u + 1)
  | res {N : GFin 𝒜} {c : ℤ} (R : UpResolution N c) : Cert N c
  | atom (i : ι) (s : ℤ) {c : ℤ} (h : c₀ - s ≤ c) : Cert ((L i).shift s) c
  | ext {N' N N'' : GFin 𝒜} {c : ℤ} (S : ShortExact N' N N'') (h' : Cert N' c)
      (h'' : Cert N'' c) : Cert N c
  | iso {N N' : GFin 𝒜} {c : ℤ} (e : N.Iso N') (h : Cert N c) : Cert N' c

variable {L c₀}

/-- A larger constant. -/
def Cert.mono : {N : GFin 𝒜} → {c : ℤ} → Cert L c₀ N c → {c' : ℤ} → c ≤ c' → Cert L c₀ N c'
  | _, _, .res R, _, h => .res (R.mono h)
  | _, _, .atom i s h₀, _, h => .atom i s (h₀.trans h)
  | _, _, .ext S h' h'', _, h => .ext S (h'.mono h) (h''.mono h)
  | _, _, .iso e h₀, _, h => .iso e (h₀.mono h)

/-- Shifting a certificate. -/
def Cert.shift : {N : GFin 𝒜} → {c : ℤ} → Cert L c₀ N c → (a : ℤ) →
    Cert L c₀ (N.shift a) (c - a)
  | _, _, .res R, a => .res (R.shift a)
  | _, _, .atom i s h, a =>
    .iso (GMod.shiftShiftIso (L i).toGMod s a).symm (.atom i (s + a) (by omega))
  | _, _, .ext S h' h'', a => .ext (S.shift a) (h'.shift a) (h''.shift a)
  | _, _, .iso e h, a => .iso (e.shift a) (h.shift a)

variable (L c₀) in
/-- The presentation of `L_i`: `0 → K_i → M_i → L_i → 0` with a resolution of `M_i` with
constant `c₀` and a certificate for `K_i` with constant `c₀ - 1`. -/
structure Pres (i : ι) where
  /-- The module `M_i`. -/
  M : GFin 𝒜
  /-- The kernel `K_i`. -/
  K : GFin 𝒜
  /-- The resolution of `M_i`. -/
  res : UpResolution M c₀
  /-- `0 → K_i → M_i → L_i → 0`. -/
  ses : ShortExact K M (L i)
  /-- The certificate for `K_i`. -/
  cert : Cert L c₀ K (c₀ - 1)

variable (L c₀) in
/-- One step of a resolution of `N` with constant `c`: a projective `P` vanishing in degrees
`< -c`, a short exact sequence `0 → K → P → N → 0` and a certificate for `K` with constant
`c - 1`. -/
structure Step (N : GFin 𝒜) (c : ℤ) where
  /-- The projective term. -/
  P : GFin 𝒜
  /-- The kernel. -/
  K : GFin 𝒜
  /-- `P` is projective. -/
  projective : Module.Projective A P.carrier
  /-- `P` vanishes in degrees `< -c`. -/
  vanish : ∀ j : ℤ, j < -c → P.grading j = ⊥
  /-- `0 → K → P → N → 0`. -/
  ses : ShortExact K P N
  /-- The certificate for the kernel. -/
  cert : Cert L c₀ K (c - 1)

variable (pres : ∀ i, Pres L c₀ i)

/-- One step of the resolution, by recursion on the certificate. -/
def Cert.step : {N : GFin 𝒜} → {c : ℤ} → Cert L c₀ N c → Step L c₀ N c
  | _, _, .res R =>
    { P := R.term 0
      K := R.syz 1
      projective := R.projective 0
      vanish := fun j hj => R.vanish 0 j (by omega)
      ses := (R.ses 0).congr (GradedEquiv.refl _) R.iso
      cert := .res R.tail }
  | _, c, .atom i s h =>
    let RM := ((pres i).res.shift s).mono (show c₀ - s ≤ c from h)
    let S := (pres i).ses.shift s
    { P := RM.term 0
      K := ker (UpResolution.quotMap S RM) (UpResolution.preservesGrading_quotMap S RM)
      projective := RM.projective 0
      vanish := fun j hj => RM.vanish 0 j (by omega)
      ses := kerShortExact _ _ (UpResolution.quotMap_surjective S RM)
      cert := .ext (UpResolution.quotSES S RM) (.res RM.tail)
        (((pres i).cert.shift s).mono (by omega)) }
  | _, _, .ext S h' h'' =>
    let T' := h'.step
    let T'' := h''.step
    letI := T''.projective
    { P := T'.P.prod T''.P
      K := UpResolution.horseKer S T'.ses T''.ses
      projective := by
        have := T'.projective
        exact inferInstanceAs (Module.Projective A (T'.P.carrier × T''.P.carrier))
      vanish := fun j hj => by
        change Submodule.prod (T'.P.grading j) (T''.P.grading j) = ⊥
        rw [T'.vanish j hj, T''.vanish j hj, Submodule.prod_bot]
      ses := UpResolution.horseCover S T'.ses T''.ses
      cert := .ext (UpResolution.horseSES S T'.ses T''.ses) T'.cert T''.cert }
  | _, _, .iso e h =>
    let T := h.step
    { P := T.P
      K := T.K
      projective := T.projective
      vanish := T.vanish
      ses := T.ses.congr (GradedEquiv.refl _) e
      cert := T.cert }

/-- The syzygies of the resolution built from a certificate. -/
def Cert.state {N : GFin 𝒜} {c : ℤ} (h : Cert L c₀ N c) :
    (n : ℕ) → Σ X : GFin 𝒜, Cert L c₀ X (c - n)
  | 0 => ⟨N, h.mono (by simp)⟩
  | n + 1 => ⟨((h.state n).2.step pres).K, ((h.state n).2.step pres).cert.mono (by push_cast; omega)⟩

/-- **A resolution in `C↑` from a certificate.** -/
def Cert.toUpResolution {N : GFin 𝒜} {c : ℤ} (h : Cert L c₀ N c) : UpResolution N c where
  syz n := (h.state pres n).1
  term n := ((h.state pres n).2.step pres).P
  projective n := ((h.state pres n).2.step pres).projective
  iso := GradedEquiv.refl _
  ses n := ((h.state pres n).2.step pres).ses
  vanish n j hj := ((h.state pres n).2.step pres).vanish j (by omega)

/-- **Bootstrapping resolutions in `C↑`.** If each `L_i` is the quotient of a module with a
resolution with constant `c₀` by a kernel certified with constant `c₀ - 1` (built from
resolutions and positive shifts `L_j{s}`, `s ≥ 1`), then each `L_i` has a resolution with
constant `c₀`. -/
def upResolution (i : ι) : UpResolution (L i) c₀ :=
  (Cert.iso (GMod.shiftZeroIso (L i).toGMod) (Cert.atom i 0 (c := c₀) (by omega))).toUpResolution
    pres

end Bootstrap

end GFin

end Categorification.Graded
