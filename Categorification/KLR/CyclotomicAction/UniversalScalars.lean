/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Universal
import Categorification.TwoRep.LinearCatRestrict

/-!
# `Ř^λ`-modules as a module category over the presentation over `k`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.4: the
category of `Ř^λ`-modules carries an action of `𝒰`, the Cautis–Lauda 2-category over the ground
ring `k`; this is the module category of Corollary 3.27. `univCyclotomicPresCL` gives the action
of the presentation over `Ř^λ_λ`, with the KLR polynomials `cycQ Q` extended from `k`. Here the
weight spaces are regarded as `k`-linear categories by restriction of scalars along
`k → Ř^λ_λ`, and the presentation over `k` with the scalars of `Q` acts:

* `univFamily_brundanUpKLR`: the cyclotomic Rouquier family over `Ř^λ_λ` satisfies Brundan's
  upward relations with the Cautis–Lauda scalars of `Q` over `k` (the relations over `Ř^λ_λ`
  are the images of those over `k`, `TwoRep.RouqUpKLR.restrictScalars`);
* `univCyclotomicPresCLk`: the resulting pseudofunctor from the presentation over `k` into
  `LinearCat k`, through `LinearCat.restrictScalars`. Its weight spaces are the categories of
  `Ř^λ_ν`-modules, with `E_i`, `F_i` acting by cyclotomic restriction and induction.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- The cyclotomic Rouquier family on the weight spaces of `Ř^λ`, over `Ř^λ_λ`. -/
abbrev univFamily :=
  cyclotomicFamily.{u, max u v, w} hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
    (univCycPoly_monic k lam) RD Λ (univCycPoly_natDegree_pair RD Λ hΛ)
    (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)

/-- The Cautis–Lauda scalars of `Q`, over `k`. -/
abbrev univScalars : KL3.Diagram.CL.CLScalars C k :=
  cyclotomicScalars hQ.klrSymm hQ.polyInY_leading RD
    (fun i j hji => hQ.polyInY_degree_pair RD i j hji)

/-- The cyclotomic family over `Ř^λ_λ` satisfies the KLR relations with `Q` over `k`. -/
theorem univFamily_upKLR : RouqUpKLR (k := k) (univFamily (lam := lam) hQ RD Λ hΛ) Q :=
  RouqUpKLR.restrictScalars (L := UnivCycRing k lam)
    (cyclotomicFamily_upKLR hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
      (univCycPoly_monic k lam) RD Λ (univCycPoly_natDegree_pair RD Λ hΛ)
      (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji))

/-- **Brundan's upward relations over `k`** for the cyclotomic family over `Ř^λ_λ`, with the
Cautis–Lauda scalars of `Q`. -/
theorem univFamily_brundanUpKLR :
    BrundanUpKLR (univFamily (lam := lam) hQ RD Λ hΛ) (univScalars hQ RD) :=
  (univFamily_upKLR hQ RD Λ hΛ).of_eq fun _ _ h =>
    eq_brundanQ C hQ.klrSymm _ (fun i j hij p q hpq =>
      coeff_eq_zero_of_lt_of_hom C (hQ.homogeneous i j hij) p q hpq) h

/-- The action of the presentation over `k` on the weight spaces of `Ř^λ`, with values in
`Ř^λ_λ`-linear categories regarded as `k`-linear ones. -/
def univCyclotomicPresCLL :
    Pseudofunctor (RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat)
      (LinearCat.{max u v, max (max u (max u v)) w, max (max u (max u v)) w + 1}
        (UnivCycRing k lam)) :=
  (univFamily hQ RD Λ hΛ).presCLPseudofunctor (univScalars hQ RD)
    (univFamily_brundanUpKLR hQ RD Λ hΛ)
    (cyclotomicFamily_mixedInversion RD Λ hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
      (univCycPoly_monic k lam) (univCycPoly_natDegree_pair RD Λ hΛ)
      (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji))
    (fun _ => rfl) (kkScalars_s_eq_zero C hQ.klrSymm _ hQ.homogeneous)

/-- **`Ř^λ`-modules as a module category over the Cautis–Lauda presentation over `k`**
(Webster, arXiv:1309.3796v2, §3.4, the action of `𝒰` on `Ř^λ`-modules used in
Corollary 3.27): the action `univCyclotomicPresCLL` followed by restriction of scalars along
`k → Ř^λ_λ`. -/
def univCyclotomicPresCLk :
    Pseudofunctor (RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat)
      (LinearCat.{v, max (max u (max u v)) w, max (max u (max u v)) w + 1} k) :=
  (univCyclotomicPresCLL hQ RD Λ hΛ).comp (LinearCat.restrictScalars k (UnivCycRing k lam))

end

end Categorification.KLR.CyclotomicAction
