/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientExact
import Categorification.Algebra.OrderedProjectiveResolution

/-!
# Derived tensor products with coefficients that have ordered covers

Let `B` be a ring and `P` a K-projective dg `B`-module whose underlying module is projective.
For a right `B`-module `M` (a `Bᵐᵒᵖ`-module) write `M ⊗ᴸ P` for the derived tensor product.

* `HasFiltration.isZero_derivedTensorHomology_coefficient`: vanishing in degree `n` on every
  layer of a finite filtration of the coefficient gives vanishing on the filtered coefficient.
* `isZero_derivedTensorHomology_of_orderedStandardCovers`: let the coefficients `S c` have
  ordered covers `0 → U_c → e_c Bᵐᵒᵖ → S c → 0` with `U_c` filtered by `S d`, `d` above `c`.
  On a set of labels closed upwards, if `S c ⊗ᴸ P` vanishes in degree `0` and the projective
  covers are concentrated in degree `0`, then `S c ⊗ᴸ P` vanishes in every degree.

This is the descending induction on the coefficient standard in B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v2, proof of Lemma 6.11 (step `f_n → s_n`,
`Tor_k(S, Ṡ') = 0`).
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]
  {P : DGModuleCat.{0} B} (hP : IsKProjective.{0} B P) [Module.Projective B P]

omit [Module.Projective B P] in
include hP in
theorem isZero_derivedTensorHomology_coefficient_of_subsingleton (M : ModuleCat.{0} Bᵐᵒᵖ)
    [Subsingleton M] (n : ℤ) : IsZero ((homologyFunctor ℤ n).obj
        ((derivedTensor.{w} ℤ B (M)).obj (Q.obj P))) := by
  have : Subsingleton (TensorProductOver B (InDegreeZero (M : Type)) P) := by
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ z : TensorProductOver B (InDegreeZero (M : Type)) P, z = 0 := fun z => by
      induction z using TensorProductOver.induction_on with
      | zero => rfl
      | tmul m p =>
        rw [show m = 0 from Subsingleton.elim (α := M) m 0]
        exact TensorProductOver.zero_tmul p
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h0 x, h0 y]
  refine ((homologyFunctor ℤ n).map_isZero (Q.map_isZero ?_)).of_iso
    ((homologyFunctor ℤ n).mapIso (derivedTensorObjIso hP))
  exact @DGModuleCat.isZero_of_subsingleton _ _ _ _ this

include hP in
/-- Vanishing of `L c ⊗ᴸ P` in degree `n` on every layer of a finite filtration of the
coefficient `Y` gives vanishing of `Y ⊗ᴸ P` in degree `n`. -/
theorem ModuleFiltration.HasFiltration.isZero_derivedTensorHomology_coefficient {ι : Type*}
    {L : ι → ModuleCat.{0} Bᵐᵒᵖ} {m : List ι} {Y : ModuleCat.{0} Bᵐᵒᵖ}
    (h : ModuleFiltration.HasFiltration L m Y) (n : ℤ)
    (hL : ∀ c ∈ m, IsZero ((homologyFunctor ℤ n).obj
        ((derivedTensor.{w} ℤ B (L c)).obj (Q.obj P)))) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} ℤ B (Y)).obj (Q.obj P))) := by
  induction h with
  | zero hY =>
    have := hY
    exact isZero_derivedTensorHomology_coefficient_of_subsingleton hP _ n
  | @cons X Y Z f g m c hf hex hg _ he ih =>
    obtain ⟨e⟩ := he
    let g' : Y →ₗ[Bᵐᵒᵖ] L c := e.toLinearMap.comp g
    have hex' : Function.Exact f g' := by
      intro y
      rw [← hex y]
      simp only [g', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      exact ⟨fun h0 => e.injective (h0.trans e.map_zero.symm), fun h0 => by rw [h0, e.map_zero]⟩
    exact isZero_derivedTensorHomology_coefficient_middle (f.restrictScalars ℤ)
      (fun b x => f.map_smul (op b) x) (g'.restrictScalars ℤ) (fun b x => g'.map_smul (op b) x)
      (LinearMap.ext fun x => hex'.apply_apply_eq_zero x) hf hex'
      (show Function.Surjective (g'.restrictScalars ℤ) from e.surjective.comp hg) hP n
      (ih fun d hd => hL d (List.mem_cons_of_mem _ hd))
      (hL c List.mem_cons_self)

include hP in
/-- **Derived tensor products with coefficients that have ordered covers**: on a set `G` of
labels closed under `above`, assume `S c ⊗ᴸ P` vanishes in degree `0` and the covers
`e_c Bᵐᵒᵖ ⊗ᴸ P` are concentrated in degree `0`. Then `S c ⊗ᴸ P` vanishes in every degree,
by descending induction along `above`. -/
theorem isZero_derivedTensorHomology_of_orderedStandardCovers {ι : Type*}
    {S : ι → ModuleCat.{0} Bᵐᵒᵖ} {e : ι → Bᵐᵒᵖ} {above : ι → ι → Prop}
    (D : ModuleFiltration.OrderedStandardCovers S e above)
    (hwf : WellFounded fun a b => above b a) (G : Set ι)
    (hG : ∀ c d, c ∈ G → above c d → d ∈ G)
    (h₀ : ∀ c ∈ G, IsZero ((homologyFunctor ℤ 0).obj ((derivedTensor.{w} ℤ B (S c)).obj (Q.obj P))))
    (hcov : ∀ c ∈ G, ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor ℤ n).obj
        ((derivedTensor.{w} ℤ B (ModuleCat.of Bᵐᵒᵖ (lIdeal (e c)))).obj (Q.obj P))))
    (c : ι) (hc : c ∈ G) (n : ℤ) : IsZero ((homologyFunctor ℤ n).obj
        ((derivedTensor.{w} ℤ B (S c)).obj (Q.obj P))) := by
  induction c using hwf.induction generalizing n with
  | _ c ih =>
  obtain ⟨m, hm, hK⟩ := D.kernel c
  have hU : ∀ j : ℤ, IsZero ((homologyFunctor ℤ j).obj
      ((derivedTensor.{w} ℤ B (ModuleCat.of Bᵐᵒᵖ (LinearMap.ker (D.quotient c)))).obj
        (Q.obj P))) := fun j =>
    hK.isZero_derivedTensorHomology_coefficient hP j fun d hd =>
      ih d (hm d hd) (hG c d hc (hm d hd)) j
  rcases eq_or_ne n 0 with rfl | hn
  · exact h₀ c hc
  · let f := (LinearMap.ker (D.quotient c)).subtype
    exact isZero_derivedTensorHomology_coefficient_quotient (f.restrictScalars ℤ)
      (fun b x => f.map_smul (op b) x) ((D.quotient c).restrictScalars ℤ)
      (fun b x => (D.quotient c).map_smul (op b) x)
      (LinearMap.ext fun x => LinearMap.mem_ker.1 x.2) (Subtype.val_injective)
      (fun y => ⟨fun hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩,
        fun ⟨x, hx⟩ => hx ▸ LinearMap.mem_ker.1 x.2⟩) (D.surjective c) hP hU
      (hcov c hc) n hn

end Categorification
