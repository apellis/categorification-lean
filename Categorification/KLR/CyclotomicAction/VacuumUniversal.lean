/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumDense
import Categorification.TwoRep.GeneratedEquivariant

/-!
# The universal property of `Ř^λ-pmod`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Cor. 3.27 (1). For a 2-representation `𝒞` of `𝒰` and an object `C₀` of `𝒞` at the region of the
vacuum module `P_∅`, killed by every `E_i`, there is a strongly equivariant functor
`Ř^λ-pmod ⟶ 𝒞` sending `P_∅` to `C₀` (`vacuumFunctor`, `vacuumFunctorAppIso`), unique up to an
isomorphism extending a given one at `P_∅` (`vacuumFunctorIso`, `vacuumFunctorIso_hom_app`).

The inputs are those of Webster's proof: evaluation at `P_∅` is surjective with kernel the ideal
`I` (`exists_vacEvG_eq`, `mem_vacIdeal_of_vacEvG_eq_zero`, Prop. 3.25), `C₀` is killed by `I`
(`map₂_app_eq_zero_of_mem_vacIdeal`), and the images of `P_∅` are dense
(`exists_vacuum_retract`). The general construction is `Categorification.TwoRep.Generated`.
-/

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory CategoryTheory.Limits TwoRep
noncomputable section
open QuantumGroup StringDiagrams Diagrams.BicatInterp KL3.Diagram
universe u v w u₁ v₂ u₂
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- Every 1-morphism out of the region of `P_∅` is the 1-morphism of a word. -/
theorem exists_eq_vacHom {c : X}
    (f : vacRegion hQ RD Λ ⟶ (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)) :
    ∃ (s : List (Letter I)) (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c),
      f = vacHom (k := k) hQ RD Λ s hs := by
  obtain ⟨Z, h3, hwf, h2⟩ := f
  have h1 := wf_eq_ob Z hwf
  have h2' : Z.endR = vacWt RD Λ := h2
  rw [StringDiagrams.Obj.endR] at h2'
  have h4 : Z = ob RD (vacWt RD Λ) (Z.word.map Col.l) :=
    h1.trans (congrArg (fun m => ob RD m (Z.word.map Col.l)) h2')
  have h5 : Z.start = c := h3
  rw [h4] at h5
  exact ⟨_, h5, StringDiagrams.Presentation.Bicat.Hom.ext h4⟩

/-- The image at `P_∅` of a 1-morphism out of the region of `P_∅`. -/
abbrev vacImg {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    (f : vacRegion hQ RD Λ ⟶ c) : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj c :=
  ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map f).obj.obj (univVacuum hQ RD Λ hΛ)

/-- Evaluation at `P_∅` of a 2-morphism out of the region of `P_∅`. -/
abbrev vacEvG {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g : vacRegion hQ RD Λ ⟶ c} (φ : f ⟶ g) :
    vacImg.{u, v, w} hQ RD Λ hΛ f ⟶ vacImg hQ RD Λ hΛ g :=
  ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂ φ).hom.app (univVacuum hQ RD Λ hΛ)

/-- **The kernel of evaluation at `P_∅` is `I`**, for arbitrary 1-morphisms out of the region
of `P_∅` (Webster, arXiv:1309.3796v2, proof of Prop. 3.25). -/
theorem mem_vacIdeal_of_vacEvG_eq_zero {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g : vacRegion hQ RD Λ ⟶ c} (φ : f ⟶ g) (h : vacEvG.{u, v, w} hQ RD Λ hΛ φ = 0) :
    φ ∈ vacIdeal hQ RD Λ f g := by
  obtain ⟨⟨c⟩⟩ := c
  obtain ⟨s, hs, rfl⟩ := exists_eq_vacHom hQ RD Λ f
  obtain ⟨s', hs', rfl⟩ := exists_eq_vacHom hQ RD Λ g
  exact mem_vacIdeal_of_vacEvW_eq_zero.{u, v, u₁, w} hQ RD Λ hΛ hs hs' φ h

/-- **Evaluation at `P_∅` is surjective**, for arbitrary 1-morphisms out of the region of
`P_∅` (Webster, arXiv:1309.3796v2, proof of Prop. 3.25). -/
theorem exists_vacEvG_eq {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g : vacRegion hQ RD Λ ⟶ c}
    (x : vacImg.{u, v, w} hQ RD Λ hΛ f ⟶ vacImg hQ RD Λ hΛ g) :
    ∃ φ : f ⟶ g, vacEvG.{u, v, w} hQ RD Λ hΛ φ = x := by
  obtain ⟨⟨c⟩⟩ := c
  obtain ⟨s, hs, rfl⟩ := exists_eq_vacHom hQ RD Λ f
  obtain ⟨s', hs', rfl⟩ := exists_eq_vacHom hQ RD Λ g
  obtain ⟨φ, hφ⟩ := exists_vacEvQ_eq.{u, v, w} hQ RD Λ hΛ hs hs' x
  exact ⟨φ, hφ⟩

theorem vacEvG_sub {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g : vacRegion hQ RD Λ ⟶ c} (φ ψ : f ⟶ g) :
    vacEvG.{u, v, w} hQ RD Λ hΛ (φ - ψ) = vacEvG hQ RD Λ hΛ φ - vacEvG hQ RD Λ hΛ ψ := by
  have h := univPmod_map₂_add.{u, v, w} hQ RD Λ hΛ (φ - ψ) ψ (univVacuum hQ RD Λ hΛ)
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

section Target
variable (𝒞 : Pseudofunctor (RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
    (LinearCat.{v, max u v w, max (u + 1) (v + 1) (w + 1)} k))
  (h𝒞 : Generated.Map₂Linear 𝒞) (C₀ : 𝒞.obj (vacRegion hQ RD Λ))
  (hE : ∀ ⦃b : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat⦄
    (e : vacRegion hQ RD Λ ⟶ b) (i : I) (r : X),
      (LinearCat.revHom e).obj.word = [⟨(false, i), r⟩] → IsZero ((𝒞.map e).obj.obj C₀))

include h𝒞 hE in
/-- An object killed by every `E_i` is killed by the ideal `I`. -/
theorem map₂_app_eq_zero_of_mem_vacIdeal
    {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat} {f g : vacRegion hQ RD Λ ⟶ c}
    {φ : f ⟶ g} (hφ : φ ∈ vacIdeal hQ RD Λ f g) : (𝒞.map₂ φ).hom.app C₀ = 0 :=
  map₂_app_eq_zero_of_mem_factorIdeal _ _ _ (fun _ e ⟨i, r, he⟩ => hE e i r he)
    (fun φ ψ => h𝒞.add φ ψ C₀) (fun r φ => h𝒞.smul r φ C₀) hφ

/-- `Ř^λ-pmod` is additive and `k`-linear on 2-morphisms. -/
theorem univPmod_map₂Linear :
    Generated.Map₂Linear (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ) :=
  ⟨fun φ ψ X => univPmod_map₂_add hQ RD Λ hΛ φ ψ X,
    fun r φ X => univPmod_map₂_smul hQ RD Λ hΛ r φ X⟩

/-- Every morphism between images of `P_∅` is the evaluation of a 2-morphism. -/
theorem vacuum_full :
    Generated.Full (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ) (univVacuum hQ RD Λ hΛ) :=
  fun _ _ _ x => exists_vacEvG_eq hQ RD Λ hΛ x

/-- The images of `P_∅` are dense in `Ř^λ-pmod` at every region. -/
theorem vacuum_isDenseFamily (c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :
    IsDenseFamily (Generated.family (univVacuum.{u, v, w} hQ RD Λ hΛ) c) :=
  ⟨fun M => by
    obtain ⟨n, g, q, p, h⟩ := exists_vacuum_retract hQ RD Λ hΛ c M
    exact ⟨⟨n, g, q, p, h⟩⟩⟩

include h𝒞 hE in
/-- A 2-morphism acting by zero on `P_∅` acts by zero on `C₀`. -/
theorem vacuum_kerLe :
    Generated.KerLe (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ) 𝒞
      (univVacuum hQ RD Λ hΛ) C₀ :=
  fun _ _ _ φ h => map₂_app_eq_zero_of_mem_vacIdeal hQ RD Λ 𝒞 h𝒞 C₀ hE
    (mem_vacIdeal_of_vacEvG_eq_zero hQ RD Λ hΛ φ h)

variable [∀ c, HasFiniteBiproducts (𝒞.obj c).carrier] [∀ c, IsIdempotentComplete (𝒞.obj c).carrier]

/-- **Webster, arXiv:1309.3796v2, Cor. 3.27 (1), existence.** For a 2-representation `𝒞` of the
2-category `𝒰` whose categories have finite biproducts and are idempotent complete, and an
object `C₀` at the region of `P_∅` killed by every `E_i`, there is a strongly equivariant functor
`Ř^λ-pmod ⟶ 𝒞` sending `P_∅` to `C₀` (`vacuumFunctorAppIso`).

The categories of `𝒞` are taken in the universes of `Ř^λ-pmod`; this is a restriction of the
formalization, not of the source. -/
noncomputable def vacuumFunctor :
    StronglyEquivariant (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ) 𝒞 :=
  Generated.strongTrans (vacuum_full hQ RD Λ hΛ) (univPmod_map₂Linear hQ RD Λ hΛ) h𝒞
    (vacuum_kerLe hQ RD Λ hΛ 𝒞 h𝒞 C₀ hE) (vacuum_isDenseFamily hQ RD Λ hΛ)

/-- The functor `vacuumFunctor` sends `P_∅` to `C₀`. -/
noncomputable def vacuumFunctorAppIso :
    ((vacuumFunctor hQ RD Λ hΛ 𝒞 h𝒞 C₀ hE).app (vacRegion hQ RD Λ)).obj.obj
      (univVacuum hQ RD Λ hΛ) ≅ C₀ :=
  Generated.strongTransAppIso _ _ _ _ _

end Target

section Uniqueness
open Pseudofunctor.StrongTrans
variable {𝒞 : Pseudofunctor (RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
    (LinearCat.{v, max u v w, max (u + 1) (v + 1) (w + 1)} k)}
  {β β' : univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ ⟶ 𝒞}

/-- **Webster, arXiv:1309.3796v2, Cor. 3.27 (1), uniqueness.** Two strongly equivariant
functors `Ř^λ-pmod ⟶ 𝒞` that agree on `P_∅` are isomorphic, by an isomorphism extending the
given one (`vacuumFunctorIso_hom_app`). -/
noncomputable def vacuumFunctorIso
    (e₀ : (β.app (vacRegion hQ RD Λ)).obj.obj (univVacuum hQ RD Λ hΛ) ≅
      (β'.app (vacRegion hQ RD Λ)).obj.obj (univVacuum hQ RD Λ hΛ)) : β ≅ β' :=
  Generated.strongTransIso (vacuum_full hQ RD Λ hΛ) (vacuum_isDenseFamily hQ RD Λ hΛ) e₀

theorem vacuumFunctorIso_hom_app
    (e₀ : (β.app (vacRegion hQ RD Λ)).obj.obj (univVacuum hQ RD Λ hΛ) ≅
      (β'.app (vacRegion hQ RD Λ)).obj.obj (univVacuum hQ RD Λ hΛ)) :
    (((vacuumFunctorIso hQ RD Λ hΛ e₀).hom.as.app (vacRegion hQ RD Λ)).hom.app
      (univVacuum hQ RD Λ hΛ)) = e₀.hom :=
  Generated.strongTransIso_hom_app _ _ e₀

/-- Morphisms between strongly equivariant functors `Ř^λ-pmod ⟶ 𝒞` are determined by their
component at `P_∅`. -/
theorem vacuumFunctor_modification_ext
    {Γ Γ' : Pseudofunctor.StrongTrans.Modification β β'}
    (h : (Γ.app (vacRegion hQ RD Λ)).hom.app (univVacuum hQ RD Λ hΛ) =
      (Γ'.app (vacRegion hQ RD Λ)).hom.app (univVacuum hQ RD Λ hΛ)) : Γ = Γ' :=
  Generated.modification_ext (vacuum_isDenseFamily hQ RD Λ hΛ) h

end Uniqueness

end
end Categorification.KLR.CyclotomicAction
