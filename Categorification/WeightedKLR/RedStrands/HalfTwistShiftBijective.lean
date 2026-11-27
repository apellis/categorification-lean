/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidHomBijective
import Categorification.WeightedKLR.RedStrands.HalfTwistExt
import Categorification.Algebra.ShiftBijective
import Categorification.Algebra.ExtShortExact

set_option backward.isDefEq.respectTransparency false

/-!
# The half twist is bijective on morphisms between shifted loading projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. The derived half twist `𝔅_w = - ⊗ᴸ B(1, κ)` is bijective on the morphisms
`e(t) T^λ⟦n⟧ → e(t') T^λ⟦m⟧` for all `n`, `m`: in degree `0` this is
`bijective_braidingFunctor_map_halfTwist`, and in every other degree both sides vanish, the
source because `e(t) T^λ` is projective and the target because the higher `Ext` between the
cuts `e(t) V e_κ` vanish (`halfTwist_hom_shift_eq_zero`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv MulOpposite DG
open scoped DG.DegreeZero

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1)))
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "CL" κ => ViolOrderCorner (k := k) (Q := QL) (Λ := Λ) (ν := ν) κ
local notation "PL" h => ModuleCat.of (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ
  (rIdeal (violLoadingIdem (k := k) (Q := QL) (Λ := Λ) h))

variable (k) in
/-- The loading projective `e(t) T^λ`, as an object of the derived category of right modules over
the corner `e_λ V e_λ`. -/
abbrev loadingProjectiveObj {t : Seq (stendhalWeight (ℓ + 1) ν)}
    (ht : redWord t = List.finRange (ℓ + 1)) :
    DG.DerivedCategory.{0} (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ :=
  DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (CL (List.finRange (ℓ + 1)))ᵐᵒᵖ).obj (PL ht))

include hR H hwt hw in
/-- **The derived half twist is bijective on morphisms between shifted loading projectives**
(Webster, arXiv:1309.3796v3, proof of Theorem 6.15), at the Khovanov–Lauda scalars, for a red
order `κ = w(1, …, ℓ)` reversing every pair of red strands. Route hypothesis: the injectivity of
Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem bijective_braidingFunctor_map_shift_halfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {t t' : Seq (stendhalWeight (ℓ + 1) ν)} (ht : redWord t = List.finRange (ℓ + 1))
    (ht' : redWord t' = List.finRange (ℓ + 1)) (n m : ℤ) :
    Function.Bijective ((braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1))
        ((List.finRange (ℓ + 1)).map w)).map :
      ((loadingProjectiveObj k C Λ ν ht)⟦n⟧ ⟶ (loadingProjectiveObj k C Λ ν ht')⟦m⟧) → _) := by
  let F := braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1)) ((List.finRange (ℓ + 1)).map w)
  have := rIdeal_projective (isIdempotentElem_violLoadingIdem (k := k) (Q := QL) (Λ := Λ) ht)
  refine map_bijective_shift_shift F (fun d => ?_) n m
  by_cases hd : d = 0
  · subst hd
    exact map_bijective_shift_zero F
      (bijective_braidingFunctor_map_halfTwist C hQ Λ ν w hR H wt hwt hw hκ ht ht')
  · have htO := (redWord_eq_finRange_iff t).1 ht
    have htO' := (redWord_eq_finRange_iff t').1 ht'
    have hz : ∀ g : F.obj (loadingProjectiveObj k C Λ ν ht) ⟶
        (F.obj (loadingProjectiveObj k C Λ ν ht'))⟦d⟧, g = 0 := fun g =>
      hom_shift_eq_zero_of_iso
        (braidingFunctorObjLoadingProjectiveIso (κ := (List.finRange (ℓ + 1)).map w) ht)
        (braidingFunctorObjLoadingProjectiveIso (κ := (List.finRange (ℓ + 1)).map w) ht') d
        (halfTwist_hom_shift_eq_zero C hQ Λ ν w hR H wt hwt hw hκ htO htO' d hd) g
    refine map_bijective_of_forall_eq F (fun f g => ?_) (fun f g => ?_) 0
    · rw [hom_shift_eq_zero_of_projective (PL ht) (PL ht') hd f,
        hom_shift_eq_zero_of_projective (PL ht) (PL ht') hd g]
    · have e : ∀ f : F.obj (loadingProjectiveObj k C Λ ν ht) ⟶
          F.obj ((loadingProjectiveObj k C Λ ν ht')⟦d⟧), f = 0 := fun f => by
        have := hz (f ≫ (F.commShiftIso d).hom.app _)
        exact (cancel_mono ((F.commShiftIso d).hom.app _)).1
          (this.trans Limits.zero_comp.symm)
      rw [e f, e g]

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
