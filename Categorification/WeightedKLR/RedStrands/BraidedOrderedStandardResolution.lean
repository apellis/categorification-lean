/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedProjectiveResolution
import Categorification.WeightedKLR.RedStrands.BraidedBimoduleFlip
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor

/-!
# Ordered projective resolutions of reflected braid-corner standards

Webster, arXiv:1309.3796v2, §6.1, p. 65, proof of Lemma 6.11. Transport
ordered covers to a braid corner using the coefficient equivalence and the
horizontal flip. Higher loading idempotents kill the opposing loading standard.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits KLR Equiv MulOpposite CornerEndomorphism

universe w
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν

/-- Coefficient change for a reflected right standard at an arbitrary red order. -/
def reflectedLeftCoefficientEquiv : C ≃+* T :=
  (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.trans (leftCoefficientEquiv hρ hQ σ)

/-- The reflected coefficient change carries each corner loading to its tensor loading. -/
theorem reflectedLeftCoefficientEquiv_loadingIdem {s : Seq μ} (hs : IsRedOrdered s) :
    reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ σ
      (violLoadingIdem (redWord_relabel σ hs)) = seqIdem Q (Λ ∘ σ) s hs := by
  rw [reflectedLeftCoefficientEquiv, RingEquiv.trans_apply]
  change leftCoefficientEquiv hρ hQ σ (op (cornerFlip
    (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)))) = _
  have hf : cornerFlip (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
      (redWord_relabel σ hs)) = violLoadingIdem (redWord_relabel σ hs) := by
    apply Subtype.ext
    rw [cornerFlip_val]
    exact (violFlip_violMk _).trans (congrArg (violMk k Q Λ ν) (flip_e _))
  rw [hf, leftCoefficientEquiv_loadingIdem]

/-- Transport the reflected right standard to the tensor product algebra's left standard. -/
def reflectedLoadingStandardLeftEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    (ModuleCat.restrictScalars (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom).obj
      (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ))
      ≃ₛₗ[(reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ σ : C →+* T)]
        leftStandard Q (Λ ∘ σ) s hs where
  toEquiv := (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).toEquiv
  map_add' := (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).map_add
  map_smul' a x := (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).map_smulₛₗ
    ((cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm a) x

include hρ hQ in
/-- The reflected standard has an ordinary projective resolution over its braid corner,
with only strictly higher loading projectives in the positive chain degrees. -/
theorem exists_ordered_projectiveResolution_reflectedLoadingStandard
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {s : Seq μ} (hs : IsRedOrdered s) :
    ∃ P : CategoryTheory.ProjectiveResolution
      ((ModuleCat.restrictScalars (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom).obj
        (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ))),
      ∀ n : ℕ, ∃ (J : Type) (label : J → {t : Seq μ // IsRedOrdered t})
        (inc : ∀ j, lIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ (label j).2)) →ₗ[C]
          P.complex.X (n+1)),
        (∀ j, StendhalLT s (label j).1) ∧ ∀ x : P.complex.X (n+1),
          x ∈ Submodule.span C {y | ∃ j z, inc j z = y} := by
  let ψ := reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ σ
  let c (t : {t : Seq μ // IsRedOrdered t}) := violLoadingIdem
    (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ t.2)
  let S (t : {t : Seq μ // IsRedOrdered t}) :=
    (ModuleCat.restrictScalars (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom).obj
      (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1) κ))
  have hE (t : {t : Seq μ // IsRedOrdered t}) : S t ≃ₗ[C]
      (ModuleCat.restrictScalars ψ.toRingHom).obj
        (ModuleCat.of T (leftStandard Q (Λ ∘ σ) t.1 t.2)) :=
    { (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).toEquiv with
      map_add' := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).map_add
      map_smul' := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).map_smulₛₗ }
  have hc : (fun t : {t : Seq μ // IsRedOrdered t} => ψ.symm (seqIdem Q (Λ ∘ σ) t.1 t.2)) = c := by
    funext t
    apply ψ.injective
    rw [ψ.apply_symm_apply, reflectedLeftCoefficientEquiv_loadingIdem hρ hQ σ t.2]
  let D' : ModuleFiltration.OrderedStandardCovers S c (fun s t => StendhalLT s.1 t.1) :=
    hc ▸ (D.transport ψ.symm).congrLayers (fun t => (hE t).symm)
  refine ⟨D'.projectiveResolution ⟨s, hs⟩, ?_⟩
  exact D'.projectiveResolution_loading_support ⟨s, hs⟩ (by
    intro a b c hab hbc
    exact ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca =>
      hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩)

include hρ hQ in
/-- Higher loading idempotents also annihilate the unreflected right loading
standard in the braid corner. -/
theorem violLoadingIdem_smul_violLoadingStandard_eq_zero
    {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (hst : StendhalLT s t)
    (m : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ) :
    op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ ht)) • m = 0 := by
  let E := loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs
  apply E.injective
  rw [E.map_smulₛₗ, map_zero]
  change leftCoefficientEquiv (Λ := Λ) hρ hQ σ
    (op (violLoadingIdem (redWord_relabel σ ht))) • E m = 0
  rw [leftCoefficientEquiv_loadingIdem]
  exact seqIdem_smul_leftStandard_eq_zero Q (Λ ∘ σ) hs ht hst (E m)

open DG DG.DerivedCategory
open scoped DG.DegreeZero

include hρ hQ in
/-- The ordered-cover input to Webster's Lemma 6.11, p. 65, for two loading
standards in the same braid corner. The right standard is the tensor coefficient
and the reflected right standard is the left argument. -/
theorem isZero_derivedTensorHomology_reflectedLoadingStandard
    [HasDerivedCategory.{w, 0} C] [HasDerivedCategory.{w, 0} ℤ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (hts : StendhalLE t s)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor ℤ C
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of C (InDegreeZero
          ((ModuleCat.restrictScalars (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom).obj
            (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ)
              (Seq.redPerm σ s) κ)))))))) := by
  obtain ⟨P, hP⟩ := exists_ordered_projectiveResolution_reflectedLoadingStandard hρ hQ σ D hs
  refine isZero_derivedTensorHomology_of_projectiveResolution_loading_support P
    (ι := {d : Seq μ // IsRedOrdered d})
    (fun d => violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ d.2)) (fun d => StendhalLT s d.1)
    (fun d => isIdempotentElem_violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ d.2)) hP ?_ n hn
  intro d hd m
  have htd : StendhalLT t d.1 := ⟨fun r i => (hts r i).trans (hd.1 r i),
    fun hdt => hd.2 (fun r i => (hdt r i).trans (hts r i))⟩
  exact violLoadingIdem_smul_violLoadingStandard_eq_zero hρ hQ σ ht d.2 htd m

end Categorification.Stendhal.BraidedStendhalAlgebra
