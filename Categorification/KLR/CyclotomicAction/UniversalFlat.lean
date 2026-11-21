/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Universal
import Categorification.KLR.CyclotomicBaseProjective

/-!
# `Ř^λ` is a flat deformation

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
**Corollary 3.26**, flatness: the universal cyclotomic quotient `Ř^λ_ν` is a projective, hence
flat, module over the polynomial ring `Ř^λ_λ` of universal cyclotomic coefficients
(`UnivCyc.projective`, `UnivCyc.flat`). This holds for every nontrivial commutative ring `k`
and every `Q` of Webster's form, and follows from the projectivity of cyclotomic quotients over an arbitrary
base ring (`CycKLR.projective_base`, the induction of Kang–Kashiwara, arXiv:1102.4677v4, §4),
applied over `Ř^λ_λ`.

Webster states the stronger assertion that `Ř^λ_ν` is free over `Ř^λ_λ`; over a field this is
`UnivCyc.free` (`Categorification.KLR.CyclotomicAction.UniversalGrading`).
-/

namespace Categorification.KLR.CyclotomicAction

open QuantumGroup

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}

/-- **Webster, arXiv:1309.3796v2, Corollary 3.26** (projectivity): `Ř^λ_ν` is a projective
`Ř^λ_λ`-module. -/
theorem UnivCyc.projective (hQ : IsRouquierQ C Q) (ν : Multiset I) :
    Module.Projective (UnivCycRing k lam) (UnivCyc k lam Q ν) :=
  CycKLR.projective_base (univCycPoly k lam) hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
    (univCycPoly_monic k lam) ν

/-- **Webster, arXiv:1309.3796v2, Corollary 3.26** (flatness): `Ř^λ_ν` is a flat
`Ř^λ_λ`-module, so `Ř^λ` is a flat deformation of its specializations. -/
theorem UnivCyc.flat (hQ : IsRouquierQ C Q) (ν : Multiset I) :
    Module.Flat (UnivCycRing k lam) (UnivCyc k lam Q ν) :=
  have := UnivCyc.projective (lam := lam) hQ ν
  inferInstance

end Categorification.KLR.CyclotomicAction
