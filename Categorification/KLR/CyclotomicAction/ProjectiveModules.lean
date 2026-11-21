/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.UniversalScalars
import Categorification.KLR.CyclotomicAction.Projective
import Categorification.TwoRep.PresentedClosure
import Categorification.TwoRep.SubPseudofunctor

/-!
# Finitely generated projective `Ř^λ`-modules as a module category

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.4: the
category `Ř^λ-pmod` of finitely generated projective `Ř^λ`-modules is a module category over
the Cautis–Lauda 2-category `𝒰` over `k` (the module category of Corollary 3.27).

The action `univCyclotomicPresCLk` of the presentation over `k` on all `Ř^λ`-modules preserves
finitely generated projective modules: a single strand acts by cyclotomic induction or
restriction, which preserve them (`isFGProj_globalE`, `isFGProj_globalF`, the latter by
Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.6, over every commutative ring), and every
1-morphism is a word in strands (`LinearCat.map_closed_of_letters`). So the action restricts to
the full subcategories (`univCyclotomicPresCLPmod`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

/-- **Finitely generated projective `Ř^λ`-modules** in the weight space of a region. -/
def univPmod (a : RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat) :
    ObjectProperty ((univCyclotomicPresCLk hQ RD Λ hΛ).obj a) :=
  IsFGProj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ a.as.region

instance (a : RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat) :
    (univPmod.{u, v, w} hQ RD Λ hΛ a).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_isFGProj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ
    a.as.region

/-- A single strand preserves finitely generated projective `Ř^λ`-modules. -/
theorem univPmod_letter {a b : RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat}
    (x : a ⟶ b) (c) (hx : (LinearCat.revHom x).obj.word = [c])
    (M : (univCyclotomicPresCLk hQ RD Λ hΛ).obj a) (hM : univPmod.{u, v, w} hQ RD Λ hΛ a M) :
    univPmod.{u, v, w} hQ RD Λ hΛ b (((univCyclotomicPresCLk hQ RD Λ hΛ).map x).obj.obj M) := by
  obtain ⟨⟨ra⟩⟩ := a
  obtain ⟨⟨rb⟩⟩ := b
  obtain ⟨⟨st, w⟩, h1, h2, h3⟩ := x
  change w = [c] at hx
  subst hx
  obtain ⟨⟨_ | _, i⟩, r⟩ := c
  · exact isFGProj_globalF _ _ RD Λ hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
      (univCycPoly_monic k lam) i _ hM
  · exact isFGProj_globalE _ _ RD Λ i _ hM

/-- Every 1-morphism of the presentation preserves finitely generated projective
`Ř^λ`-modules. -/
theorem univPmod_map {a b : RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat}
    (x : a ⟶ b) (M : (univCyclotomicPresCLk hQ RD Λ hΛ).obj a)
    (hM : univPmod.{u, v, w} hQ RD Λ hΛ a M) :
    univPmod.{u, v, w} hQ RD Λ hΛ b (((univCyclotomicPresCLk hQ RD Λ hΛ).map x).obj.obj M) :=
  LinearCat.map_closed_of_letters _ _ (fun x c hx M hM => univPmod_letter hQ RD Λ hΛ x c hx M hM)
    _ x rfl M hM

/-- **`Ř^λ-pmod` as a module category over the Cautis–Lauda presentation over `k`**
(Webster, arXiv:1309.3796v2, §3.4, the module category of Corollary 3.27): the action
`univCyclotomicPresCLk` restricted to finitely generated projective `Ř^λ`-modules. -/
def univCyclotomicPresCLPmod :=
  LinearCat.fullSub (univCyclotomicPresCLk hQ RD Λ hΛ) (univPmod.{u, v, w} hQ RD Λ hΛ)
    fun x M hM => univPmod_map hQ RD Λ hΛ x M hM

end

end Categorification.KLR.CyclotomicAction
