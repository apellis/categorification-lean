/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTensorStandardTor
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltration

/-!
# Tor against standardizations of factor projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `E²` terms for resolutions by standardizations (Proposition 7.8). The
standardization `S(T^{λ'} e(t) ⊠ R^{λ_{ℓ+1}} e(u))` of a factor projective is filtered by the
standard modules of the two-piece loadings `t' λ_{ℓ+1} u`, with `t'` running over a standard
filtration of `T^{λ'} e(t)` (Proposition 5.20, filtration form: `HasStandardFiltrations`). So it
has no Tor against a right module filtered by right standards whose labels are inequivalent to
every two-piece loading `t' λ_{ℓ+1} u`, and no higher Tor against any such module.

## Main results

* `hasFiltration_stdLayer_tensorProj`: the standard filtration of `S(T^{λ'} e(t) ⊠ R e(u))`.
* `isZero_derivedTensorHomology_stdLayer_tensorProj`,
  `isZero_derivedTensorHomology_stdLayer_tensorProj_of_ne_zero`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)

/-- **The standard filtration of a standardized factor projective** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.20): given a standard filtration of `T^{λ'} e(t)` with
labels `m'`, the standardization `S(T^{λ'} e(t) ⊠ R e(u))` is filtered by the standard modules of
the two-piece loadings `t' λ_{ℓ+1} u`, `t' ∈ m'`. -/
theorem hasFiltration_stdLayer_tensorProj {θ β ν : Multiset I} (h : θ + β = ν)
    {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β)
    {m' : List {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}}
    (hm' : HasFiltration (stdModule Q (Λ ∘ Fin.castSucc) θ) m'
      (ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
        (lIdeal (seqIdem Q (Λ ∘ Fin.castSucc) t ht)))) :
    HasFiltration (stdModule Q Λ ν) (m'.map (twoPieceLabel h u))
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h (oldProj Q Λ θ t ht) (cycProj Q Λ β u))) := by
  have h₁ := hasFiltration_tensorLayer Q Λ hQ h (cycProj Q Λ β u)
    (X := oldProj Q Λ θ t ht) hm'
  have h₂ : HasFiltration (fun d => stdModule Q Λ ν (twoPieceLabel h u d)) m'
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h (oldProj Q Λ θ t ht) (cycProj Q Λ β u))) :=
    h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ h d.2 u
  exact HasFiltration.relabel (L := stdModule Q Λ ν) (twoPieceLabel h u) h₂

variable {ν : Multiset I} {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **No Tor against a standardized factor projective** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, off-diagonal `E²` terms): if `N` is filtered by right standards whose
labels are inequivalent to every two-piece loading `t' λ_{ℓ+1} u`, then
`N ⊗ᴸ S(T^{λ'} e(t) ⊠ R e(u))` has no cohomology. -/
theorem isZero_derivedTensorHomology_stdLayer_tensorProj
    (D : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (Λ ∘ Fin.castSucc))
    {θ β : Multiset I} (h : θ + β = ν) {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t)
    (u : Seq β) {m : List {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s}}
    {N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    (hN : HasFiltration (fun t' : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ 1 t'.1) m N)
    (hlab : ∀ t' ∈ m, ∀ d, ¬ (StendhalLE (twoPieceLabel h u d).1 t'.1 ∧
      StendhalLE t'.1 (twoPieceLabel h u d).1)) (n : ℤ) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) N).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (stdLayerModule Q Λ hQ (tensorLayer Q Λ h (oldProj Q Λ θ t ht)
            (cycProj Q Λ β u))))))) := by
  obtain ⟨m', hm'⟩ := hold θ t ht
  let : HasDerivedCategory.{w, 0}
      (TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin (ℓ + 1)))) ν) :=
    ‹HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)›
  exact isZero_derivedTensorHomology_tensor_of_standardFiltrations hρ hQ 1 D hN
    (hasFiltration_stdLayer_tensorProj Q Λ hQ h ht u hm')
    (fun t' ht' s hs => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hs
      exact hlab t' ht' d) n

include hρ in
/-- **No higher Tor against a standardized factor projective** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22, diagonal `E²` term). -/
theorem isZero_derivedTensorHomology_stdLayer_tensorProj_of_ne_zero
    (D : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (Λ ∘ Fin.castSucc))
    {θ β : Multiset I} (h : θ + β = ν) {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t)
    (u : Seq β) {m : List {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s}}
    {N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    (hN : HasFiltration (fun t' : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ 1 t'.1) m N) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ (TensorProductAlgebra k Q Λ ν) N).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (TensorProductAlgebra k Q Λ ν)).obj
          (stdLayerModule Q Λ hQ (tensorLayer Q Λ h (oldProj Q Λ θ t ht)
            (cycProj Q Λ β u))))))) := by
  obtain ⟨m', hm'⟩ := hold θ t ht
  let : HasDerivedCategory.{w, 0}
      (TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin (ℓ + 1)))) ν) :=
    ‹HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)›
  exact isZero_derivedTensorHomology_tensor_of_standardFiltrations_of_ne_zero hρ hQ 1 D hN
    (hasFiltration_stdLayer_tensorProj Q Λ hQ h ht u hm') n hn

end Categorification.Stendhal
