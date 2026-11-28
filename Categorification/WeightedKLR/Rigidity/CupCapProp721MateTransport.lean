/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapAdjoint
import Categorification.WeightedKLR.Rigidity.CupCapProp721CapMateDerived

/-!
# Mates transported along comparison functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21: the compatibility of `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` and `𝕂 ∘ 𝔉_i ≅ 𝔉_i ∘ 𝕂` with the
units and counits of `𝔉_i ⊣ 𝔈_i` passes from Mathlib's derived categories of modules to derived
categories of dg modules. This file gives the generic step. The counit of an adjunction
transported along equivalences (`CupCap.adjunctionOfComparison`) is expressed through the
comparison isomorphisms and the original counit (`CupCap.adjunctionOfComparison_counit_map`),
and squares corresponding under comparison functors to a pair of mates are mates
(`CupCap.mateEquiv_eq_of_comparison`).

## Main results

* `CupCap.adjunctionOfComparison_counit_map`.
* `CupCap.mateEquiv_eq_of_comparison`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Counit

variable {DA : Type u₁} {DB : Type u₂} {MA : Type u₃} {MB : Type u₄}
  [Category.{v₁} DA] [Category.{v₂} DB] [Category.{v₃} MA] [Category.{v₄} MB]
  (eA : DA ≌ MA) (eB : DB ≌ MB) {F : DA ⥤ DB} {G : DB ⥤ DA} {F' : MA ⥤ MB} {G' : MB ⥤ MA}

/-- **The counit of a transported adjunction**: under `eB`, the counit of
`adjunctionOfComparison eA eB adj iF iG` at `d` is `iF` followed by `F'` of `iG` and the counit of
`adj`. -/
theorem adjunctionOfComparison_counit_map (adj : F' ⊣ G') (iF : F ⋙ eB.functor ≅ eA.functor ⋙ F')
    (iG : G ⋙ eA.functor ≅ eB.functor ⋙ G') (d : DB) :
    eB.functor.map ((adjunctionOfComparison eA eB adj iF iG).counit.app d) =
      iF.hom.app (G.obj d) ≫ F'.map (iG.hom.app d) ≫ adj.counit.app (eB.functor.obj d) := by
  simp only [adjunctionOfComparison, Adjunction.ofNatIsoLeft, Adjunction.ofNatIsoRight,
    Adjunction.comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]
  simp
  have h1 := iF.hom.naturality (eA.unitIso.hom.app (G.obj d))
  have h2 := iF.hom.naturality (eA.inverse.map (iG.hom.app d))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  rw [reassoc_of% h2, reassoc_of% h1, ← F'.map_comp_assoc, ← F'.map_comp_assoc]
  congr 3
  rw [Category.assoc, Equivalence.counit_naturality, ← Category.assoc,
    Equivalence.functor_unit_comp, Category.id_comp]

end Counit

section Transport

universe v₅ v₆ v₇ v₈ u₅ u₆ u₇ u₈

variable {A : Type u₁} {Aᵢ : Type u₂} {P : Type u₃} {Pᵢ : Type u₄}
  [Category.{v₁} A] [Category.{v₂} Aᵢ] [Category.{v₃} P] [Category.{v₄} Pᵢ]
  {A' : Type u₅} {Aᵢ' : Type u₆} {P' : Type u₇} {Pᵢ' : Type u₈}
  [Category.{v₅} A'] [Category.{v₆} Aᵢ'] [Category.{v₇} P'] [Category.{v₈} Pᵢ']
  {cA : A ⥤ A'} {cAᵢ : Aᵢ ⥤ Aᵢ'} {cP : P ⥤ P'} {cPᵢ : Pᵢ ⥤ Pᵢ'}
  {F : A ⥤ Aᵢ} {E : Aᵢ ⥤ A} {Fp : P ⥤ Pᵢ} {Ep : Pᵢ ⥤ P} {K : A ⥤ P} {Kᵢ : Aᵢ ⥤ Pᵢ}
  {F' : A' ⥤ Aᵢ'} {E' : Aᵢ' ⥤ A'} {Fp' : P' ⥤ Pᵢ'} {Ep' : Pᵢ' ⥤ P'} {K' : A' ⥤ P'}
  {Kᵢ' : Aᵢ' ⥤ Pᵢ'}
  {adj : F ⊣ E} {adjP : Fp ⊣ Ep} {adj' : F' ⊣ E'} {adjP' : Fp' ⊣ Ep'}
  (iF : F ⋙ cAᵢ ≅ cA ⋙ F') (iE : E ⋙ cA ≅ cAᵢ ⋙ E') (iFp : Fp ⋙ cPᵢ ≅ cP ⋙ Fp')
  (iEp : Ep ⋙ cP ≅ cPᵢ ⋙ Ep') (iK : K ⋙ cP ≅ cA ⋙ K') (iKᵢ : Kᵢ ⋙ cPᵢ ≅ cAᵢ ⋙ Kᵢ')

/-- **Mates transport along comparison functors**: if the comparisons `c` intertwine the two
pairs of adjunctions on the counits (`hε`, `hεP`), the comparison of `Pᵢ` is faithful, and the
squares `α`, `β` correspond under the comparisons to squares `α'`, `β'` with `β'` the mate of
`α'`, then `β` is the mate of `α`. -/
theorem mateEquiv_eq_of_comparison [cPᵢ.Faithful]
    (hε : ∀ d, cAᵢ.map (adj.counit.app d) =
      iF.hom.app (E.obj d) ≫ F'.map (iE.hom.app d) ≫ adj'.counit.app (cAᵢ.obj d))
    (hεP : ∀ d, cPᵢ.map (adjP.counit.app d) =
      iFp.hom.app (Ep.obj d) ≫ Fp'.map (iEp.hom.app d) ≫ adjP'.counit.app (cPᵢ.obj d))
    (α' : K' ⋙ Fp' ⟶ F' ⋙ Kᵢ') (β' : E' ⋙ K' ⟶ Kᵢ' ⋙ Ep')
    (hmate : (mateEquiv adj' adjP' (TwoSquare.mk _ _ _ _ α')).natTrans = β')
    (α : K ⋙ Fp ⟶ F ⋙ Kᵢ) (β : E ⋙ K ⟶ Kᵢ ⋙ Ep)
    (hα : ∀ a, cPᵢ.map (α.app a) = iFp.hom.app (K.obj a) ≫ Fp'.map (iK.hom.app a) ≫
      α'.app (cA.obj a) ≫ Kᵢ'.map (iF.inv.app a) ≫ iKᵢ.inv.app (F.obj a))
    (hβ : ∀ d, cP.map (β.app d) = iK.hom.app (E.obj d) ≫ K'.map (iE.hom.app d) ≫
      β'.app (cAᵢ.obj d) ≫ Ep'.map (iKᵢ.inv.app d) ≫ iEp.inv.app (Kᵢ.obj d)) :
    (mateEquiv adj adjP (TwoSquare.mk _ _ _ _ α)).natTrans = β := by
  have hmod : ∀ x, Fp'.map (β'.app x) ≫ adjP'.counit.app (Kᵢ'.obj x) =
      α'.app (E'.obj x) ≫ Kᵢ'.map (adj'.counit.app x) := fun x => by
    rw [← hmate]
    exact mateEquiv_counit adj' adjP' (TwoSquare.mk _ _ _ _ α') x
  refine congrArg TwoSquare.natTrans (mateEquiv_eq_of_counit adj adjP _
    (TwoSquare.mk _ _ _ _ β) fun d => cPᵢ.map_injective ?_)
  have nFp := NatIso.naturality_2 iFp (β.app d)
  have nK := NatIso.naturality_2 iKᵢ (adj.counit.app d)
  simp only [Functor.comp_map, Functor.comp_obj] at nFp nK
  simp only [Functor.map_comp, hεP, hα]
  erw [← nFp, ← nK]
  rw [hβ, hε]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Fp'.map_comp_assoc (iEp.inv.app _), Iso.inv_hom_id_app, Fp'.map_id,
    Category.id_comp]
  erw [adjP'.counit_naturality]
  rw [reassoc_of% hmod,
    ← Kᵢ'.map_comp_assoc (iF.inv.app _), Iso.inv_hom_id_app, Kᵢ'.map_id, Category.id_comp]
  have nα := α'.naturality (iE.hom.app d)
  simp only [Functor.comp_map] at nα
  rw [reassoc_of% nα]
  rfl

end Transport

end Categorification.Stendhal.CupCap
