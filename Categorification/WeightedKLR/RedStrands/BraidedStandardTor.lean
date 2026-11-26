/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorProjectiveCoefficient
import Categorification.WeightedKLR.RedStrands.BraidedOrderedStandardResolution

/-!
# Tor between standards and reflected standards in a braid corner

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Lemma 6.11 (step `f_n → s_n`): `Tor_n(S_t, Ṡ_s) = 0` for `n ≠ 0` and all loadings
`s`, `t`, where `S_t` is the right loading standard of the braid corner (the tensor
coefficient) and `Ṡ_s` the reflected one.

* If `t` is not strictly above `s`, resolve `Ṡ_s` by loadings strictly above `s`; they kill
  `S_t` (`isZero_derivedTensorHomology_reflectedLoadingStandard`).
* If `t` is strictly above `s`, use the ordered covers of the coefficient `S_t`, whose kernels
  are filtered by standards strictly above `t`; the loadings strictly above `s` kill `Ṡ_s`
  (`isZero_derivedTensorHomology_of_orderedStandardCovers_annihilated`).

## Main results

* `rightLoadingStandardCovers`: the ordered covers of the right loading standards.
* `isZero_derivedTensorHomology_loadingStandard`: the Tor vanishing for all `s`, `t`.
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

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

/-- The ordered covers of the right loading standards of the braid corner, transported from
the left standards of the tensor product algebra. -/
def rightLoadingStandardCovers
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1)) :
    ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of Cᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s.1) κ))
      (fun s => op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ s.2)))
      (fun s t => StendhalLT s.1 t.1) := by
  let ψ := leftCoefficientEquiv (Λ := Λ) hρ hQ σ
  have hE (t : {t : Seq μ // IsRedOrdered t}) :
      (ModuleCat.restrictScalars ψ.symm.symm.toRingHom).obj
        (ModuleCat.of T (leftStandard Q (Λ ∘ σ) t.1 t.2)) ≃ₗ[Cᵐᵒᵖ]
      ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1) κ) :=
    { (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).symm.toEquiv with
      map_add' := (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).symm.map_add
      map_smul' := fun a x => by
        convert (loadingStandardLeftEquiv (Λ := Λ) hρ hQ σ t.2).symm.map_smulₛₗ (ψ a) x using 2 <;>
          first | rfl | exact (ψ.symm_apply_apply a).symm }
  have hc : (fun t : {t : Seq μ // IsRedOrdered t} => ψ.symm (seqIdem Q (Λ ∘ σ) t.1 t.2)) =
      fun t => op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ t.2)) := by
    funext t
    apply ψ.injective
    rw [ψ.apply_symm_apply, leftCoefficientEquiv_loadingIdem hρ hQ σ t.2]
  exact hc ▸ (D.transport ψ.symm).congrLayers hE

open DG DG.DerivedCategory
open scoped DG.DegreeZero

include hρ hQ in
/-- **Tor between standards and reflected standards** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11, step `f_n → s_n`): the derived tensor of the right loading standard at `t` with
the reflected right loading standard at `s` vanishes in every nonzero degree. -/
theorem isZero_derivedTensorHomology_loadingStandard
    [HasDerivedCategory.{w, 0} C] [HasDerivedCategory.{w, 0} ℤ]
    (D : ModuleFiltration.OrderedStandardCovers
      (fun s : {s : Seq μ // IsRedOrdered s} => ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2))
      (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor ℤ C
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t) κ)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of C (InDegreeZero
          ((ModuleCat.restrictScalars (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom).obj
            (ModuleCat.of Cᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ)
              (Seq.redPerm σ s) κ)))))))) := by
  by_cases hst : StendhalLT s t
  swap
  · exact isZero_derivedTensorHomology_reflectedLoadingStandard hρ hQ σ D hs ht hst n hn
  let L := {s : Seq μ // IsRedOrdered s}
  let r : L → L → Prop := fun a b => StendhalLT b.1 a.1
  have : IsTrans L r := ⟨fun a b c hab hbc =>
    ⟨fun r i => (hbc.1 r i).trans (hab.1 r i),
      fun hac => hbc.2 (fun r i => (hab.1 r i).trans (hac r i))⟩⟩
  have : Std.Irrefl r := ⟨fun a ha => ha.2 fun _ _ => le_rfl⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine isZero_derivedTensorHomology_of_orderedStandardCovers_annihilated
    (rightLoadingStandardCovers hρ hQ σ D) hwf {d : L | StendhalLT s d.1}
    (fun c d hc hcd => ⟨fun r i => (hc.1 r i).trans (hcd.1 r i),
      fun hds => hc.2 (fun r i => (hcd.1 r i).trans (hds r i))⟩)
    (fun d _ => ?_) _ (fun d hd x => ?_) ⟨t, ht⟩ hst n
  · exact congrArg op (isIdempotentElem_violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
      (redWord_relabel σ d.2))
  · change op (cornerFlip (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
      (redWord_relabel σ d.2))) •
        (x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ) = 0
    rw [cornerFlip_violLoadingIdem σ d.2]
    exact violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_le hρ hQ σ hs d.2 hd.2 x

end Categorification.Stendhal.BraidedStendhalAlgebra
