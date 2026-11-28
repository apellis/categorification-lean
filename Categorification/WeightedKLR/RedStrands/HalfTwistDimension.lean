/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistExt
import Categorification.WeightedKLR.RedStrands.BraidEquivalenceDimension

set_option backward.isDefEq.respectTransparency false

/-!
# `dim Hom(𝔅_τ P_t, 𝔅_τ P_{t'}) = dim Hom(P_t, P_{t'})` for the half twist

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15: "the dimension of Hom between tilting modules is read off from their classes".
The braid `𝔅_σ (e(t) T^λ)` is the cut `e(t) V e_{σλ}` as a module over the corner, which is
`T^{λ ∘ σ}` after relabelling (`braidCutEquiv`). For the half twist the higher Ext between the
cuts vanish (`halfTwist_hom_shift_eq_zero`), so `dim Hom(𝔅_τ P_t, 𝔅_τ P_{t'})` is the Euler
characteristic along a projective resolution (`Graded.finrank_hom_eq_altSum`), which is
`dim Hom(P_t, P_{t'})` (`FirstWeight.altSum_finrank_hom_braidF`): this is
`finrank_hom_halfTwist_braidF`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Morphisms into a shift vanish along isomorphisms of source and target. -/
theorem hom_shift_eq_zero_of_iso {𝒟 : Type*} [Category 𝒟] [HasZeroMorphisms 𝒟] [HasShift 𝒟 ℤ]
    {X X' Y Y' : 𝒟} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℤ)
    (h : ∀ g : X' ⟶ Y'⟦n⟧, g = 0) (f : X ⟶ Y⟦n⟧) : f = 0 := by
  have hf : f = eX.hom ≫ (eX.inv ≫ f ≫ (shiftFunctor 𝒟 n).map eY.hom) ≫
      (shiftFunctor 𝒟 n).map eY.inv := by
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hf, h (eX.inv ≫ f ≫ (shiftFunctor 𝒟 n).map eY.hom), zero_comp, comp_zero]

section General

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (𝔠 : QuantumGroup.CartanDatum I) (hR : IsRouquierQ 𝔠 Q) (σ : Perm (Fin ℓ))

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

variable (Λ ν) in
/-- The ring isomorphism `(T^{λ ∘ σ})ᵐᵒᵖ ≅ (e_{σλ} V e_{σλ})ᵐᵒᵖ`: the corner of the identity red
order of `λ ∘ σ`, relabelled to the corner at `σλ` for `λ`. -/
abbrev braidCutRingEquiv : (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ ≃+* (C (List.map σ (List.finRange ℓ)))ᵐᵒᵖ :=
  (rightCornerEquiv (Λ := Λ ∘ σ) (ν := ν) (FirstWeight.isReducedChoice_canChoice ν)
    hR.klrSymm).trans (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ (List.finRange ℓ)).symm

variable [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **The braid of a sequence projective is a cut** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11), as modules over the corner at `σλ`: `𝔅_σ (e(t) T^λ) ≅ e(t) V e_{σλ}` along
`braidCutRingEquiv`. -/
def braidCutEquiv {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) :
    Graded.resModule (braidCutRingEquiv Λ ν 𝔠 hR σ)
        (FirstWeight.braidF 𝔠 hR Λ σ ν (rightSequenceProj (stendhalGradingDatum Λ
          hR.gradingDatum (fun i => 𝔠.dot i i / 2) (dotDegree 𝔠 hR)) t ht).toGFin) ≃ₗ[(C (List.map σ (List.finRange ℓ)))ᵐᵒᵖ]
      violCorner k Q Λ ν t (List.map σ (List.finRange ℓ)) :=
  let e := braidRightSequenceCutEquiv (FirstWeight.isReducedChoice_canChoice ν) hR.klrSymm hR σ t ht
  { toFun := fun x => e x
    invFun := fun y => e.symm y
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := fun c x => by
      rw [RingHom.id_apply, ← LinearEquiv.map_smul] }

end General

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

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
local notation "G" Ω => stendhalGradingDatum Ω hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)

include hR H hwt hw in
/-- **`dim Hom(𝔅_τ P_t, 𝔅_τ P_{t'}) = dim Hom(P_t, P_{t'})`** (Webster, arXiv:1309.3796v3, proof
of Theorem 6.15), at the Khovanov–Lauda scalars: for a red order `κ = w(1, …, ℓ)` reversing every
pair of red strands and red-ordered loadings `t`, `t'`, the braid functor `𝔅_w` preserves the
dimension of `Hom` between the sequence projectives `e(t) T^λ`, `e(t') T^λ`. Route hypothesis:
the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`). -/
theorem finrank_hom_halfTwist_braidF
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    {t t' : Seq (stendhalWeight (ℓ + 1) ν)} (ht : IsRedOrdered t) (ht' : IsRedOrdered t') :
    Module.finrank k ((FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t ht).toGFin).carrier
        →ₗ[(TensorProductAlgebra k QL (Λ ∘ w) ν)ᵐᵒᵖ]
        (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' ht').toGFin).carrier) =
      Module.finrank k ((rightSequenceProj (G Λ) t ht).carrier →ₗ[(TensorProductAlgebra k QL Λ ν)ᵐᵒᵖ]
        (rightSequenceProj (G Λ) t' ht').carrier) := by
  have hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective QL Λ' hQ.klrSymm :=
    fun _ _ => allFiniteDeltaInjective_of_rouquier hQ hQ.klrSymm
  obtain ⟨f, hf, hcls⟩ := FirstWeight.hasCongruentBraidClass.{0} C hQ hR H w hw Λ wt hwt
  obtain ⟨Ps, ⟨r⟩⟩ := exists_resolution_of_hasCornerStandardFiltration
    (FirstWeight.isReducedChoice_canChoice ν) hQ.klrSymm hQ hall
    (FirstWeight.hasCornerStandardFiltration_braidF.{0} C hQ hR H w hw Λ wt hwt t ht)
  let φ := braidCutRingEquiv Λ ν C hQ w
  have hext : ∀ n : ℕ, ∀ g : DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
      (Graded.resModule φ (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t ht).toGFin))) ⟶
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj (Graded.resModule φ
          (FirstWeight.braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' ht').toGFin))))⟦(n : ℤ) + 1⟧,
      g = 0 := fun n g =>
    hom_shift_eq_zero_of_iso
      (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
        (braidCutEquiv (Λ := Λ) C hQ w ht).toModuleIso))
      (DG.DerivedCategory.Q.mapIso ((degreeZeroModuleFunctor _).mapIso
        (braidCutEquiv (Λ := Λ) C hQ w ht').toModuleIso)) _
      (halfTwist_hom_shift_eq_zero C hQ Λ ν w hR H wt hwt hw hκ ht ht' _ (by omega)) g
  have e := Graded.finrank_hom_eq_altSum φ _ r (fun P hP => by
    obtain ⟨P', -, rfl⟩ := List.mem_map.1 hP
    exact P'.projective) hext
  rw [List.map_map] at e
  exact_mod_cast e.trans (FirstWeight.altSum_finrank_hom_braidF C hQ hR Λ wt hwt w f hf hcls ht ht' r)

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
