/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumUniversal
import Categorification.TwoRep.GeneratedHomTensor

/-!
# Morphisms of strongly equivariant images of `Ř^λ-pmod`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Cor. 3.27 (2). For a strongly equivariant functor `φ_C : Ř^λ-pmod ⟶ 𝒞` and objects `M`, `N` of
`Ř^λ-pmod` at the region of `P_∅`, the map
`Hom_{Ř^λ}(M, N) ⊗_{Ř^λ_λ} End(φ_C P_∅) → Hom_𝒞(φ_C M, φ_C N)`, `h ⊗ c ↦ φ_C(h) ≫ c_N`, is
bijective (`vacuum_homTensorMap_bijective`). Here `Ř^λ_λ = End(P_∅)`
(`univVacuum_smul_id_bijective`) and `c_N` is the component at `N` of the modification extending
`c`. Webster's proof reduces to `Hom(F_𝐢 P_∅, N) ≅ Hom(P_∅, E_𝐢 N)` by adjunction; the general
argument is `Categorification.TwoRep.Generated.homTensorMap_bijective`.
-/

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory CategoryTheory.Limits TwoRep
noncomputable section
open QuantumGroup StringDiagrams Diagrams.BicatInterp KL3.Diagram
open Bicategory Pseudofunctor.StrongTrans
open scoped TensorProduct
universe u v w u₁
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

instance univPmodObjLinearL (c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :
    Linear (UnivCycRing k lam) ((univCyclotomicPresCLk.{u, v, w} hQ RD Λ hΛ).obj c) :=
  inferInstanceAs (Linear (UnivCycRing k lam) ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).obj c))

instance univPmodLinearL (c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :
    Linear (UnivCycRing k lam) ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj c) :=
  inferInstanceAs (Linear (UnivCycRing k lam)
    (ObjectProperty.FullSubcategory (univPmod.{u, v, w} hQ RD Λ hΛ c)))

/-- The scalar ring of the empty block, `Ř^λ(∅)`. -/
abbrev VacRing := CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) 0

/-- The block at the empty multiset of a scalar multiple of the identity of `P_∅`. -/
theorem smul_id_hom_apply (r : UnivCycRing k lam)
    (x : emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ ⟨0, rfl⟩) :
    ((r • 𝟙 (univVacuum.{u, v, w} hQ RD Λ hΛ)).hom ⟨0, rfl⟩).hom x =
      algebraMap (UnivCycRing k lam) (VacRing (k := k) (lam := lam) (Q := Q)) r • x :=
  rfl

omit [Nontrivial k] in
/-- `cyclotomicZeroEquiv` inverts the structure map of `Ř^λ(∅)`. -/
theorem vacRing_zeroEquiv_algebraMap (r : UnivCycRing k lam) :
    KLRAlgebra.cyclotomicZeroEquiv (cycQ k lam Q) (univCycPoly k lam)
      (algebraMap (UnivCycRing k lam) (VacRing (k := k) (lam := lam) (Q := Q)) r) = r :=
  AlgEquiv.commutes _ r

omit [Nontrivial k] in
/-- The vacuum coordinate of a multiple of the generator. -/
theorem univVacCoord_smul_gen (z : VacRing (k := k) (lam := lam) (Q := Q)) :
    univVacCoord.{u, v, w} (Q := Q) (lam := lam) RD Λ (z • univVacGen RD Λ) = z := by
  rw [map_smul, univVacCoord_univVacGen, smul_eq_mul, mul_one]

omit [Nontrivial k] in
/-- Commuting elements of `Ř^λ(∅)` act in either order on the generator of `P_∅`. -/
theorem smul_smul_gen_comm (z c : VacRing (k := k) (lam := lam) (Q := Q))
    (h : c * z = z * c) :
    z • c • univVacGen.{u, v, w} (Q := Q) (lam := lam) RD Λ = c • z • univVacGen RD Λ := by
  rw [smul_smul, smul_smul, h]

/-- `End(P_∅) = Ř^λ_λ` (Webster, arXiv:1309.3796v2, proof of Cor. 3.27 (2)). -/
theorem univVacuum_smul_id_bijective :
    Function.Bijective (fun r : UnivCycRing k lam => r • 𝟙 (univVacuum.{u, v, w} hQ RD Λ hΛ)) := by
  refine ⟨fun r s h => ?_, fun φ => ?_⟩
  · have h1 := congrArg (fun f : univVacuum.{u, v, w} hQ RD Λ hΛ ⟶ univVacuum hQ RD Λ hΛ =>
      univVacCoord.{u, v, w} (Q := Q) (lam := lam) RD Λ
        ((f.hom ⟨0, rfl⟩).hom (univVacGen RD Λ))) h
    rw [smul_id_hom_apply, smul_id_hom_apply, univVacCoord_smul_gen,
      univVacCoord_smul_gen] at h1
    rw [← vacRing_zeroEquiv_algebraMap (Q := Q) r, ← vacRing_zeroEquiv_algebraMap (Q := Q) s, h1]
  · set z := univVacCoord.{u, v, w} (Q := Q) (lam := lam) RD Λ
      ((φ.hom ⟨0, rfl⟩).hom (univVacGen RD Λ)) with hz
    refine ⟨KLRAlgebra.cyclotomicZeroEquiv (cycQ k lam Q) (univCycPoly k lam) z, ?_⟩
    have hzr : algebraMap (UnivCycRing k lam) (VacRing (k := k) (lam := lam) (Q := Q))
        (KLRAlgebra.cyclotomicZeroEquiv (cycQ k lam Q) (univCycPoly k lam) z) = z := by
      apply (KLRAlgebra.cyclotomicZeroEquiv (cycQ k lam Q) (univCycPoly k lam)).injective
      rw [vacRing_zeroEquiv_algebraMap]
    have hgen : (φ.hom ⟨0, rfl⟩).hom (univVacGen RD Λ) = z • univVacGen RD Λ := by
      obtain ⟨z', hz'⟩ :=
        univVac_cyclic (Q := Q) RD Λ ((φ.hom ⟨0, rfl⟩).hom (univVacGen RD Λ))
      rw [hz', hz, hz', univVacCoord_smul_gen]
      rfl
    refine ObjectProperty.hom_ext _ (funext fun β => ?_)
    obtain ⟨b, hb⟩ := β
    by_cases h0 : b = 0
    · subst h0
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨c, rfl⟩ := univVac_cyclic (Q := Q) RD Λ x
      have hc : c * z = z * c := by
        rw [← hzr]
        exact (Algebra.commutes _ c).symm
      show ((KLRAlgebra.cyclotomicZeroEquiv (cycQ k lam Q) (univCycPoly k lam) z •
          𝟙 (univVacuum.{u, v, w} hQ RD Λ hΛ)).hom ⟨0, rfl⟩).hom (c • univVacGen RD Λ) =
        (φ.hom ⟨0, rfl⟩).hom (c • univVacGen RD Λ)
      refine (smul_id_hom_apply hQ RD Λ hΛ _ _).trans ?_
      refine Eq.trans ?_ (map_smul (φ.hom ⟨0, rfl⟩).hom c (univVacGen RD Λ)).symm
      refine Eq.trans ?_ (congrArg (fun y => c • y) hgen).symm
      rw [hzr]
      exact smul_smul_gen_comm (Q := Q) RD Λ z c hc
    · exact (isZero_emptyBlockObj (β := ⟨b, hb⟩) h0).eq_of_src _ _
omit [DecidableEq I] in
theorem wd_map_l (μ : X) (s : List (Letter I)) : (wd RD μ s).map Col.l = s := by
  induction s with
  | nil => rfl
  | cons l s ih => simp [ih]

abbrev PCL := CL.presCL RD k (univScalars hQ RD)

/-- The letters of the dual of an upward word `t` are the downward letters of `t` reversed. -/
theorem dualHom_ups_map_l {l m : (PCL hQ RD).Bicat} (x : l ⟶ m) (μ : X) (t : List I)
    (hx : x.obj.word = wd RD μ (ups t)) :
    ((PCL hQ RD).dualHom (inv RD).toColourDuality.pivotal x).obj.word.map Col.l =
      dns t.reverse := by
  rw [StringDiagrams.Presentation.dualHom_obj]
  show List.map Col.l (Signature.ColourDuality.dualWord (inv RD).toColourDuality.pivotal
    x.obj.word) = _
  rw [Signature.ColourDuality.dualWord_eq, hx]
  change List.map Col.l ((List.map (fun c : Col I X => (⟨c.l.dual, sh RD c.l + c.r⟩ : Col I X))
    (wd RD μ (ups t))).reverse) = _
  rw [List.map_reverse, List.map_map]
  have : (Col.l ∘ fun c : Col I X => (⟨c.l.dual, sh RD c.l + c.r⟩ : Col I X)) =
      Letter.dual ∘ Col.l := rfl
  rw [this, ← List.map_map, wd_map_l]
  simp [List.map_reverse, Function.comp_def, up]

/-- The dual of a loop at the vacuum region. -/
abbrev vacDual (x : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ) : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ :=
  RevBicat.of ((PCL hQ RD).dualHom (inv RD).toColourDuality.pivotal (LinearCat.revHom x))

/-- **The dual of a nonempty upward loop kills `P_∅`**: its strand next to the vacuum is
downward. -/
theorem isZero_vacImg_vacDual (x : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ) (t : List I)
    (ht : t ≠ []) (hx : (LinearCat.revHom x).obj = ob RD (vacWt RD Λ) (ups t)) :
    IsZero (vacImg.{u, v, w} hQ RD Λ hΛ (vacDual hQ RD Λ x)) := by
  obtain ⟨s, hs, hf⟩ := exists_eq_vacHom hQ RD Λ (vacDual hQ RD Λ x)
  have hsw : s = dns t.reverse := by
    have h1 := congrArg (fun g : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ =>
      (LinearCat.revHom g).obj.word.map Col.l) hf
    have h2 := dualHom_ups_map_l hQ RD (LinearCat.revHom x) (vacWt RD Λ) t
      (by rw [hx]; rfl)
    simp only [vacHom_obj, ob_word, wd_map_l] at h1
    exact h1.symm.trans h2
  rw [hf]
  have hm := comp_mem_vacIdeal_of_dn hQ RD Λ hs hs (z := s) (a := []) (b := t.reverse)
    (by simp [hsw]) (by simpa using ht) rfl (𝟙 _) (𝟙 _)
  have h0 := univVacuum_map₂_eq_zero_of_mem_vacIdeal.{u, v, w} hQ RD Λ hΛ hm
  rw [IsZero.iff_id_eq_zero, ← h0]
  erw [Category.comp_id, PrelaxFunctor.map₂_id]
  rfl


/-- The loops of `Ř^λ-pmod` commute with the action of `Ř^λ_λ` on identities. -/
theorem univPmod_map_smul_id (c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) (f : c ⟶ c)
    (r : UnivCycRing k lam) (M : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj c) :
    ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map f).obj.map (r • 𝟙 M) = r • 𝟙 _ := by
  apply ObjectProperty.hom_ext
  exact (((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map f).obj.map_smul r (𝟙 M.obj)).trans
    (congrArg (r • ·) (((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map f).obj.map_id M.obj))

/-- Every loop at the vacuum region has a right adjoint. -/
theorem vacLoop_exists_adjunction (f : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ) :
    ∃ g : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ, Nonempty (f ⊣ g) :=
  ⟨_, ⟨RevBicat.adjunction
    (Presentation.biadj (CL.biadjColour RD k (univScalars hQ RD)) (LinearCat.revHom f)).right⟩⟩

section HomTensor
variable {ℵ₂ : Pseudofunctor (RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
    (LinearCat.{v, max u v w, max (u + 1) (v + 1) (w + 1)} k)}
  (β : univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ ⟶ ℵ₂)

/-- The map `Hom(M, N) ⊗_{Ř^λ_λ} End(φ_C P_∅) → Hom(φ_C M, φ_C N)` of Webster's Cor. 3.27 (2). -/
abbrev vacHomTensorMap (M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj
    (vacRegion hQ RD Λ)) :=
  Generated.homTensorMap (UnivCycRing k lam) (vacuum_full hQ RD Λ hΛ)
    (vacuum_isDenseFamily hQ RD Λ hΛ) (univPmod_map_smul_id hQ RD Λ hΛ _) β M N

/-- The base case: `P_∅` against the image of `P_∅` under an upward loop. -/
theorem vacHomTensorMap_bijective_up (g : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ) (t : List I)
    (hg : (LinearCat.revHom g).obj = ob RD (vacWt RD Λ) (ups t)) :
    Function.Bijective (vacHomTensorMap hQ RD Λ hΛ β (univVacuum hQ RD Λ hΛ)
      (vacImg hQ RD Λ hΛ g)) := by
  have hF := vacuum_full.{u, v, w} hQ RD Λ hΛ
  have hD := vacuum_isDenseFamily.{u, v, w} hQ RD Λ hΛ
  have hL := univPmod_map_smul_id.{u, v, w} hQ RD Λ hΛ (vacRegion hQ RD Λ)
  by_cases ht : t = []
  · subst ht
    obtain rfl : g = 𝟙 (vacRegion hQ RD Λ) := by
      apply StringDiagrams.Presentation.Bicat.Hom.ext
      have h1 := (LinearCat.revHom g).start_eq
      rw [hg] at h1
      rw [hg]
      exact StringDiagrams.Obj.ext h1 rfl
    exact Generated.homTensorMap_bijective_of_iso (UnivCycRing k lam) hF hD hL β
      (Generated.idApp _ _ _).symm (Generated.homTensorMap_bijective_self _ hF hD hL β
        (univVacuum_smul_id_bijective hQ RD Λ hΛ))
  · let adj : vacDual hQ RD Λ g ⊣ g := RevBicat.adjunction
      (Presentation.biadj (CL.biadjColour RD k (univScalars hQ RD)) (LinearCat.revHom g)).left
    have hZ := isZero_vacImg_vacDual.{u, v, w} hQ RD Λ hΛ g t ht hg
    have : Subsingleton (vacImg hQ RD Λ hΛ (vacDual hQ RD Λ g) ⟶ univVacuum hQ RD Λ hΛ) :=
      ⟨fun _ _ => hZ.eq_of_src _ _⟩
    have : Subsingleton ((β.app _).obj.obj (vacImg hQ RD Λ hΛ (vacDual hQ RD Λ g)) ⟶
        (β.app _).obj.obj (univVacuum hQ RD Λ hΛ)) :=
      ⟨fun _ _ => ((β.app _).obj.map_isZero hZ).eq_of_src _ _⟩
    exact (Generated.homTensorMap_bijective_iff_of_adjunction _ hF hD hL β adj _ _).1
      (Generated.homTensorMap_bijective_of_subsingleton _ hF hD hL β _ _)

/-- The map of `vacHomTensorMap` is bijective on `Hom(P∅, ℵ(f) P∅)` for every endomorphism `f`
of the vacuum region: `ℵ(f) P∅` is a retract of a sum of `ℵ(g) P∅` with `g` upward. -/
theorem vacHomTensorMap_bijective_base (f : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ) :
    Function.Bijective (vacHomTensorMap hQ RD Λ hΛ β (univVacuum hQ RD Λ hΛ)
      (vacImg hQ RD Λ hΛ f)) := by
  have hF := vacuum_full.{u, v, w} hQ RD Λ hΛ
  have hD := vacuum_isDenseFamily.{u, v, w} hQ RD Λ hΛ
  have hL := univPmod_map_smul_id.{u, v, w} hQ RD Λ hΛ (vacRegion hQ RD Λ)
  obtain ⟨n, g, hg, q, p, hs⟩ :=
    exists_vacuum_up_retract.{u, v, w} hQ RD Λ hΛ _ (vacImg hQ RD Λ hΛ f)
  exact Generated.homTensorMap_bijective_of_retract (UnivCycRing k lam) hF hD hL β
    (P := fun g : {g : vacRegion hQ RD Λ ⟶ vacRegion hQ RD Λ //
      ∃ t : List I, (LinearCat.revHom g).obj = ob RD (vacWt RD Λ) (ups t)} =>
        vacImg hQ RD Λ hΛ g.1)
    ⟨n, fun i => ⟨g i, hg i⟩, q, p, hs⟩ fun i => by
      obtain ⟨t, ht⟩ := hg i
      exact vacHomTensorMap_bijective_up hQ RD Λ hΛ β (g i) t ht

/-- **Webster, arXiv:1309.3796v2, Corollary 3.27 (2)** (Hom-tensor form). For a strongly
equivariant functor `β` out of the universal cyclotomic 2-representation, and modules `M`, `N`
over the vacuum region, the map
`Hom(M, N) ⊗_{Ř^λ_λ} End(β P∅) → Hom(β M, β N)`, `h ⊗ c ↦ β(h) ≫ c_N`, is bijective, where
`Ř^λ_λ = End(P∅)` and `c_N` is the component at `N` of the modification extending `c`. -/
theorem vacuum_homTensorMap_bijective
    (M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj (vacRegion hQ RD Λ)) :
    Function.Bijective (vacHomTensorMap hQ RD Λ hΛ β M N) :=
  Generated.homTensorMap_bijective _ _ _ _ β (vacLoop_exists_adjunction hQ RD Λ)
    (vacHomTensorMap_bijective_base hQ RD Λ hΛ β) M N

end HomTensor

end
end Categorification.KLR.CyclotomicAction
