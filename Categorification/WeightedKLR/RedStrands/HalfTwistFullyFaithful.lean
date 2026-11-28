/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistShiftBijective
import Categorification.WeightedKLR.RedStrands.HalfTwistDimension
import Categorification.WeightedKLR.RedStrands.LoadingGenerators
import Categorification.Algebra.Graded.CompactResolution
import Categorification.Algebra.CompactGeneratorEquivalence
import Categorification.Algebra.DerivedTensorCoproducts

set_option backward.isDefEq.respectTransparency false

/-!
# The half twist is fully faithful

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. The derived half twist `𝔅_w = - ⊗ᴸ B(1, κ)` is fully faithful
(`fullyFaithfulBraidingFunctorHalfTwist`): it preserves coproducts, the loading projectives
`e(t) T^λ` compactly generate (`compactlyGenerates_loadingProjective`), their images, the cuts
`e(t) V e_κ`, are compact because they have finite resolutions by finitely generated projectives
(`isCompact_braidingFunctor_obj_halfTwist`), and `𝔅_w` is bijective on the morphisms between
shifted loading projectives (`bijective_braidingFunctor_map_shift_halfTwist`).
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


local notation "G" Ω => stendhalGradingDatum Ω hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)

include hR H hwt hw in
/-- The image of a loading projective under the half twist, the cut `e(t) V e_κ`, is compact. -/
theorem isCompact_braidingFunctor_obj_halfTwist {t : Seq (stendhalWeight (ℓ + 1) ν)}
    (ht : redWord t = List.finRange (ℓ + 1)) :
    IsCompact.{0} ((braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1))
      ((List.finRange (ℓ + 1)).map w)).obj (loadingProjectiveObj k C Λ ν ht)) := by
  have htO := (redWord_eq_finRange_iff t).1 ht
  have hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective QL Λ' hQ.klrSymm :=
    fun _ _ => allFiniteDeltaInjective_of_rouquier hQ hQ.klrSymm
  obtain ⟨Ps, ⟨r⟩⟩ := exists_resolution_of_hasCornerStandardFiltration
    (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm hQ hall
    (FirstWeight.hasCornerStandardFiltration_braidF.{0} C hQ hR H w hw Λ wt hwt t htO)
  have hc := Graded.isCompact_resModule_of_resolution (braidCutRingEquiv Λ ν C hQ w) r
    (fun P hP => by
      obtain ⟨P', -, rfl⟩ := List.mem_map.1 hP
      exact ⟨P'.projective, P'.finite⟩)
  exact hc.of_iso (braidingFunctorObjLoadingProjectiveIso (κ := (List.finRange (ℓ + 1)).map w) ht ≪≫
    DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
      (braidCutEquiv (Λ := Λ) C hQ w htO).toModuleIso.symm))

include hR H hwt hw in
/-- **The derived half twist is fully faithful** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.15), at the Khovanov–Lauda scalars, for a red order `κ = w(1, …, ℓ)` reversing every
pair of red strands. Route hypothesis: the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
def fullyFaithfulBraidingFunctorHalfTwist
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t') :
    (braidingFunctor.{0} k QL Λ ν (List.finRange (ℓ + 1))
      ((List.finRange (ℓ + 1)).map w)).FullyFaithful :=
  fullyFaithfulOfCompactlyGenerates _
    (compactlyGenerates_loadingProjective (k := k) (Q := QL) (Λ := Λ) (ν := ν)
      (List.finRange (ℓ + 1)))
    (fun J => by
      unfold braidingFunctor
      exact derivedRightTensor_preservesCoproducts _ _ _ J)
    (fun t => isCompact_braidingFunctor_obj_halfTwist C hQ Λ ν w hR H wt hwt hw t.2)
    (fun t t' n m => bijective_braidingFunctor_map_shift_halfTwist C hQ Λ ν w hR H wt hwt hw hκ
      t.2 t'.2 n m)

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
