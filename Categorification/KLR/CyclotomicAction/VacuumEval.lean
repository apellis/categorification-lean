/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumUpward

/-!
# Upward diagrams evaluated at the vacuum of `Ř^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. The comparison map `End_𝒰(⊕_𝐢 F_𝐢 λ) → Ř^λ` evaluates a 2-morphism at the
projective module `P_∅` and reads off the `(t, s)` entry through the generator of the word `t`
applied to the vacuum and the coordinate of the word `s`.

* `vacCoeff φ t s ∈ Ř^λ(ν)`: this entry for a matrix `φ` of 2-morphisms between upward words at
  the region of `P_∅`, evaluated through the cyclotomic Rouquier family;
* `vacCoeff_vacUpHom`: on upward KLR diagrams, `vacCoeff (vacUpHom r) t s` is the class of
  `hflip (σ (e(s) r e(t)))` of the image of `r` in the KLR algebra over `Ř^λ_λ`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- The generator of the vacuum `P_∅` in its empty block. -/
def vacGen : emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ
    ⟨0, rfl⟩ := fun _ => ULift.up 1

/-- The coordinate of the vacuum `P_∅` in its empty block. -/
def vacCoord : emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ ⟨0, rfl⟩
    →ₗ[CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) 0]
      CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) 0 where
  toFun f := (f ⟨rfl⟩).down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Nontrivial k] in
theorem vacCoord_vacGen : vacCoord.{u, v, w} (Q := Q) (lam := lam) RD Λ (vacGen RD Λ) = 1 := rfl

/-- **The vacuum entry of a matrix of upward 2-morphisms**: the `(t, s)` entry in `Ř^λ(ν)` of the
evaluation of `φ` at `P_∅` through the cyclotomic Rouquier family. -/
def vacCoeff (ν : Multiset I)
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t)))))
    (t s : KLR.Seq ν) :
    CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν :=
  wcoord hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
      (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
      (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ) rfl
      (vacCoord RD Λ) s
    ((((univFamily hQ RD Λ hΛ).upActP (univScalars hQ RD)
        (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) ν
        φ t s).hom.app (familyObj _ _ _ _ _ _) (topBlk rfl)).hom
      (wgen hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
        (univCycPoly_natDegree_pair RD Λ hΛ)
        (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) _ rfl (vacGen RD Λ) t))

/-- **Upward KLR diagrams at the vacuum** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25): the
vacuum entry of `vacUpHom r` is the class of `hflip (σ (e(s) r e(t)))` in `Ř^λ(ν)`, for the image
of `r` in the KLR algebra over `Ř^λ_λ`. -/
theorem vacCoeff_vacUpHom (ν : Multiset I) (r : KLRAlgebra k (KL3.Diagram.CL.qCL
    (univScalars hQ RD)) ν) (t s : KLR.Seq ν) :
    vacCoeff hQ RD Λ hΛ ν (vacUpHom hQ RD Λ ν r) t s =
      CycKLR.mk _ (cycQ k lam Q) (univCycPoly k lam) ν
        (hflip (sigma hQ.cycQ.klrSymm (e s * vacKLRMap hQ RD ν r * e t))) := by
  unfold vacCoeff
  rw [upActP_vacUpHom]
  exact wcoord_klrAct_wgen _ _ _ _ _ _ rfl _ (vacCoord_vacGen RD Λ) _ t s
