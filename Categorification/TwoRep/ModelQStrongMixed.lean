/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongPres
import Categorification.TwoRep.InterpHomogeneous
import Categorification.Diagrams.CL.BrundanMixed

/-!
# The mixed relations in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 1.1 and §6 (the mixed relations `sec:mixedrels`, Proposition 6.3).

CL derive the mixed relations from Hom-space bounds (their Lemma 6.1). Here they come from
J. Brundan's relation chase (arXiv:1501.00350v1, proof of Lemma 5.2), which, read without the
inverse of the sideways crossing, shows that in `U_Q(g)` without the mixed relations (`presNM`)
the sideways crossing `σ = crossl j i` has, at every weight, a one-sided inverse
`t_{ij}^{-1} crossr j i` (`Categorification.Diagrams.CL.BrundanMixed`). In the model, the source
and target of `σ` are isomorphic (CL Definition 1.2 (5), `QStrong.mixed`) by an isomorphism of the
same degree, and the graded Hom spaces are finite-dimensional, so a one-sided inverse is a
two-sided inverse.

## Main results

* `GradedHomCat.isIso_of_comp_eq_smul_id`, `GradedHomCat.isIso_of_comp_eq_smul_id'`: in a
  Hom-finite category, a homogeneous morphism with a one-sided inverse (up to a nonzero scalar)
  between objects isomorphic by an isomorphism of the same degree is an isomorphism;
* `QStrong.mixedIsoG`: the isomorphism `F_i E_j ≅ E_j F_i` of the model, homogeneous of degree
  `-(α_i, α_j)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open KrullSchmidtCat (HomFinite)

universe w v u u₁

/-! ## One-sided inverses in a Hom-finite category -/

section HomFinite

variable {C : Type*} [Category C] [Preadditive C]

/-- In a Hom-finite category, an endomorphism `s` such that `g ≫ s = 0` implies `g = 0` is an
isomorphism. -/
theorem isIso_of_cancel_zero_left (k : Type*) [Field k] [Linear k C] [HomFinite k C] {A : C} (s : A ⟶ A)
    (hs : ∀ (W : C) (g : W ⟶ A), g ≫ s = 0 → g = 0) : IsIso s := by
  let L : (A ⟶ A) →ₗ[k] (A ⟶ A) :=
    { toFun := fun g => g ≫ s
      map_add' := fun g g' => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun c g => Linear.smul_comp _ _ _ _ _ _ }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun g hg => hs A g hg
  obtain ⟨g, hg⟩ := (LinearMap.injective_iff_surjective.1 hinj) (𝟙 A)
  change g ≫ s = 𝟙 A at hg
  refine ⟨g, ?_, hg⟩
  have : (s ≫ g - 𝟙 A) ≫ s = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hg, Category.comp_id, Category.id_comp, sub_self]
  exact sub_eq_zero.1 (hs A _ this)

/-- In a Hom-finite category, an endomorphism `s` such that `s ≫ g = 0` implies `g = 0` is an
isomorphism. -/
theorem isIso_of_cancel_zero_right (k : Type*) [Field k] [Linear k C] [HomFinite k C] {A : C} (s : A ⟶ A)
    (hs : ∀ (W : C) (g : A ⟶ W), s ≫ g = 0 → g = 0) : IsIso s := by
  let L : (A ⟶ A) →ₗ[k] (A ⟶ A) :=
    { toFun := fun g => s ≫ g
      map_add' := fun g g' => Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c g => Linear.comp_smul _ _ _ _ _ _ }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun g hg => hs A g hg
  obtain ⟨g, hg⟩ := (LinearMap.injective_iff_surjective.1 hinj) (𝟙 A)
  change s ≫ g = 𝟙 A at hg
  refine ⟨g, hg, ?_⟩
  have : s ≫ (g ≫ s - 𝟙 A) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hg, Category.comp_id, Category.id_comp, sub_self]
  exact sub_eq_zero.1 (hs A _ this)

variable {k : Type*} [Field k] [Linear k C] [HomFinite k C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k]

open GradedHomCat in
/-- **A homogeneous morphism with a left inverse up to a nonzero scalar**, between objects
isomorphic by an isomorphism of the same degree, is an isomorphism (Hom-finite case). -/
theorem GradedHomCat.isIso_of_comp_eq_smul_id {X Y : GradedHomCat C} {σ : X ⟶ Y} {ψ : Y ⟶ X}
    {d : ℤ} (hσ : IsHomogeneous σ d) (e : X ≅ Y) (he : IsHomogeneous e.hom d) {c : k}
    (hc : c ≠ 0) (h : σ ≫ ψ = c • 𝟙 X) : IsIso σ := by
  have hinv : IsHomogeneous e.inv (-d) := by
    have := he.inv; rwa [IsIso.Iso.inv_hom] at this
  obtain ⟨s, hs⟩ := (hσ.comp hinv (by simp) : IsHomogeneous (σ ≫ e.inv) 0).exists_incl_map
  have key : (incl C).map s ≫ (e.hom ≫ ψ) = c • 𝟙 X := by
    rw [← hs, Category.assoc, e.inv_hom_id_assoc, h]
  have hsi : IsIso s := isIso_of_cancel_zero_left k s fun W g hg => by
    have h1 : (incl C).map g ≫ (incl C).map s ≫ (e.hom ≫ ψ) = 0 := by
      rw [← Category.assoc, ← Functor.map_comp, hg, Functor.map_zero, zero_comp]
    rw [key, Linear.comp_smul, Category.comp_id] at h1
    exact (incl C).map_injective ((smul_eq_zero.1 h1).resolve_left hc |>.trans
      (Functor.map_zero (incl C) _ _).symm)
  have : σ = (incl C).map s ≫ e.hom := by rw [← hs, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [this]; exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

open GradedHomCat in
/-- **A homogeneous morphism with a right inverse up to a nonzero scalar**, between objects
isomorphic by an isomorphism of the same degree, is an isomorphism (Hom-finite case). -/
theorem GradedHomCat.isIso_of_comp_eq_smul_id' {X Y : GradedHomCat C} {σ : X ⟶ Y} {ψ : Y ⟶ X}
    {d : ℤ} (hσ : IsHomogeneous σ d) (e : X ≅ Y) (he : IsHomogeneous e.hom d) {c : k}
    (hc : c ≠ 0) (h : ψ ≫ σ = c • 𝟙 Y) : IsIso σ := by
  have hinv : IsHomogeneous e.inv (-d) := by
    have := he.inv; rwa [IsIso.Iso.inv_hom] at this
  obtain ⟨s, hs⟩ := (hσ.comp hinv (by simp) : IsHomogeneous (σ ≫ e.inv) 0).exists_incl_map
  have key : (e.hom ≫ ψ) ≫ (incl C).map s = c • 𝟙 X := by
    rw [← hs, Category.assoc, ← Category.assoc ψ, h, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, e.hom_inv_id]
  have hsi : IsIso s := isIso_of_cancel_zero_right k s fun W g hg => by
    have h1 : (e.hom ≫ ψ) ≫ (incl C).map s ≫ (incl C).map g = 0 := by
      rw [← Functor.map_comp, hg, Functor.map_zero, comp_zero]
    rw [← Category.assoc, key, Linear.smul_comp, Category.id_comp] at h1
    exact (incl C).map_injective ((smul_eq_zero.1 h1).resolve_left hc |>.trans
      (Functor.map_zero (incl C) _ _).symm)
  have : σ = (incl C).map s ≫ e.hom := by rw [← hs, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [this]; exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

end HomFinite


/-! ## The model -/

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable (S : QStrong B C RD k Q)

/-- **The isomorphism `F_i E_j ≅ E_j F_i` in the model** (CL Definition 1.2 (5), `QStrong.mixed`),
between the images of the words `[up j, dn i]` and `[dn i, up j]`. -/
def mixedIsoG {i j : I} (hji : j ≠ i) {l m p s : X} (h₁ : l + RD.iX j = m)
    (h₂ : p + RD.iX i = m) (h₃ : s + RD.iX i = l) (h₄ : s + RD.iX j = p) :
    S.Rg i h₃ ≫ S.Eg j h₄ ≅ S.Eg j h₁ ≫ S.Rg i h₂ :=
  whiskerRightIso (shiftIso₁ (S.F i h₃) (di C i * (RD.pair (RD.iY i) s + 1))) (S.Eg j h₄) ≪≫
    (incl _).mapIso (S.mixed j i hji h₁ h₂ h₃ h₄).some.symm ≪≫
    whiskerLeftIso (S.Eg j h₁) (shiftIso₁ (S.F i h₂) (di C i * (RD.pair (RD.iY i) p + 1))).symm

theorem mixedIsoG_hom_isHomogeneous {i j : I} (hji : j ≠ i) {l m p s : X}
    (h₁ : l + RD.iX j = m) (h₂ : p + RD.iX i = m) (h₃ : s + RD.iX i = l)
    (h₄ : s + RD.iX j = p) :
    IsHomogeneous (S.mixedIsoG hji h₁ h₂ h₃ h₄).hom (-C.dot i j) := by
  have hdeg : -C.dot i j = -(di C i * (RD.pair (RD.iY i) p + 1)) + 0 +
      di C i * (RD.pair (RD.iY i) s + 1) := by
    rw [← h₄, map_add, RD.pair_iY_iX_eq_A, ← di_mul_A]; ring
  exact ((isHomogeneous_whiskerRight (shiftIso₁_hom_isHomogeneous _ _) _).comp
    ((isHomogeneous_incl_map _).comp (isHomogeneous_whiskerLeft _
      (shiftIso₁_inv_isHomogeneous _ _)) rfl) hdeg.symm)

/-- The degrees of the generators in the model: `-(α_i, α_j)` for the upward crossing, `0` for
the other generators used below (cups and caps of the right adjunction). -/
def degCross : (psig RD).Gen → ℤ := fun g => match g with
  | .gen (.cross true i j _) => -C.dot i j
  | _ => 0

variable (hsl : ∀ i, C.dot i i = 2) (Sc : CL.CLScalars C k)

theorem genHomogeneous_cupDn (i : I) (r : X) :
    GenHomogeneous (S.genImg hsl Sc) degCross (.cup ⟨(false, i), r⟩) := by
  intro a b ha hb hd hde hc hce
  subst hde
  exact isHomogeneous_incl₂ _

theorem genHomogeneous_capDn (i : I) (r : X) :
    GenHomogeneous (S.genImg hsl Sc) degCross (.cap ⟨(false, i), r⟩) := by
  intro a b ha hb hd hde hc hce
  subst hce
  exact isHomogeneous_incl₂ _

theorem genHomogeneous_crossUp (i j : I) (ν : X) :
    GenHomogeneous (S.genImg hsl Sc) degCross (.gen (.cross true i j ν)) := by
  intro a b ha hb hd hde hc hce
  obtain rfl : ν = b := hde
  exact isHomogeneous_of₂ _ _

/-- The image of the sideways crossing `crossl j i` is homogeneous of degree `-(α_i, α_j)`. -/
theorem isHomogeneous_crossl (j i : I) (ν : X) (s₀ t₀ : X) :
    IsHomogeneous ((interp (S.genImg hsl Sc) s₀ t₀).functor.map (crossl RD j i ν))
      (-C.dot i j) := by
  have h := isHomogeneous_interp_map (G := S.genImg hsl Sc) (δ := degCross) s₀ t₀
    (crossl RD j i ν) (by
      intro L hL
      simp only [crossl, mkD, Diagram.layers_mk, layList_cons, layList_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl | rfl
      · exact S.genHomogeneous_cupDn hsl Sc _ _
      · exact S.genHomogeneous_crossUp hsl Sc _ _ _
      · exact S.genHomogeneous_capDn hsl Sc _ _)
  exact h.of_eq (by simp [crossl, mkD, Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen,
    degCross])

theorem cond_up_dn' (j i : I) (ν : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD ν [up j, dn i] : X) ν (ob RD ν [up j, dn i]) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl, rfl⟩

theorem cond_dn_up' (j i : I) (ν : X) :
    Cond (S := psig RD) (KL3.Diagram.wt RD ν [up j, dn i] : X) ν (ob RD ν [dn i, up j]) :=
  ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩

/-- The images of `E_j F_i 1_ν` and `F_i E_j 1_ν` are isomorphic in the model, by an isomorphism
homogeneous of degree `-(α_i, α_j)` (CL Definition 1.2 (5)). -/
def crossObjIso {j i : I} (hji : j ≠ i) (ν : X) {s₀ : X}
    (hs : (KL3.Diagram.wt RD ν [up j, dn i] : X) = s₀) :
    (interp (S.genImg hsl Sc) s₀ ν).obj (ob RD ν [up j, dn i]) ≅
      (interp (S.genImg hsl Sc) s₀ ν).obj (ob RD ν [dn i, up j]) := by
  subst hs
  exact eqToIso (objI_pos (M := S.model) (KL3.Diagram.wt RD ν [up j, dn i] : X) ν
      (cond_up_dn' j i ν)) ≪≫
    S.mixedIsoG hji (l := ν) (m := sh RD (up j) + ν)
      (p := KL3.Diagram.wt RD ν [up j, dn i]) (s := sh RD (dn i) + ν)
      (by show @Eq X _ _; simp only [sh_up, sh_dn, KL3.Diagram.wt_cons, KL3.Diagram.wt_nil]; abel)
      (by show @Eq X _ _; simp only [sh_up, sh_dn, KL3.Diagram.wt_cons, KL3.Diagram.wt_nil]; abel)
      (by show @Eq X _ _; simp only [sh_up, sh_dn, KL3.Diagram.wt_cons, KL3.Diagram.wt_nil]; abel)
      (by show @Eq X _ _; simp only [sh_up, sh_dn, KL3.Diagram.wt_cons, KL3.Diagram.wt_nil]; abel) ≪≫
    eqToIso (objI_pos (M := S.model) (KL3.Diagram.wt RD ν [up j, dn i] : X) ν
      (cond_dn_up' j i ν)).symm

theorem crossObjIso_hom_isHomogeneous {j i : I} (hji : j ≠ i) (ν : X) {s₀ : X}
    (hs : (KL3.Diagram.wt RD ν [up j, dn i] : X) = s₀) :
    IsHomogeneous (S.crossObjIso hsl Sc hji ν hs).hom (-C.dot i j) := by
  subst hs
  simp only [crossObjIso, Iso.trans_hom, eqToIso.hom]
  refine IsHomogeneous.comp ?_ (IsHomogeneous.comp ?_ ?_ (zero_add _)) (add_zero _)
  · apply isHomogeneous_eqToHom
  · exact S.mixedIsoG_hom_isHomogeneous hji _ _ _ _
  · exact isHomogeneous_eqToHom (objI_pos (M := S.model) (KL3.Diagram.wt RD ν [up j, dn i] : X) ν
      (cond_dn_up' j i ν)).symm

theorem not_isMixed_of_nonMixed {r : Rel RD} (h : CL.nonMixed RD r) : ¬ r.IsMixed := by
  cases r <;> simp_all [CL.nonMixed, Rel.IsMixed]

/-- **The model respects `U_Q(g)` without the mixed relations** (`presNM`), for scalars `Sc`
with `r_i = 1` whose KLR polynomials are those of the normalized dots. -/
theorem respects_presNM (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (s₀ t₀ : X) :
    (CL.presNM RD k Sc).Respects (interp (S.genImg hsl Sc) s₀ t₀).functor := by
  refine respects (S.genImg hsl Sc) (CL.presNM RD k Sc) s₀ t₀ ?_
    (fun g => Signature.IsEven.odd_eq_false g)
  intro i _ _ _ _
  rcases i with (i | c | c) | ⟨r, hr'⟩
  · exact i.elim
  · change (freeLift k (interp (S.genImg hsl Sc) _ _).functor).map
      (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id,
      sub_eq_zero]
    exact zigL_eq (S := S) hsl Sc c
  · change (freeLift k (interp (S.genImg hsl Sc) _ _).functor).map
      (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id,
      sub_eq_zero]
    exact zigR_eq (S := S) hsl Sc c
  · exact killedCL_of_not_mixed (S := S) hsl Sc hr hQ hQ2 hQ3 r (not_isMixed_of_nonMixed hr')

section Mixed

variable (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
include hr hQ hQ2 hQ3

/-- Brundan's relation (`KL3.Diagram.CL.dgN_downupEF_le`) in the model:
`crossl j i ≫ crossr j i = t_{ij} · 1` on `E_j F_i 1_ν` for `⟨i, ν - α_i⟩ ≤ 0`. -/
theorem interp_crossl_crossr_le {j i : I} (hji : j ≠ i) (ν s₀ : X)
    (h : KL3.Diagram.ip RD i (KL3.Diagram.wt RD ν [dn i]) ≤ 0) :
    (interp (S.genImg hsl Sc) s₀ ν).functor.map (crossl RD j i ν) ≫
        (interp (S.genImg hsl Sc) s₀ ν).functor.map (crossr RD j i ν) =
      (Sc.t i j : k) • 𝟙 _ := by
  have e := congrArg ((CL.presNM RD k Sc).lift
    (S.respects_presNM hsl Sc hr hQ hQ2 hQ3 s₀ ν)).map (CL.dgN_downupEF_le hr hji.symm ν h)
  rw [← CL.dgC_comp (s := [up j, dn i]) (t := [dn i, up j]) (r := [up j, dn i])
    (A := crosslL j i) (B := crossrL j i) (by schain) (by schain), CL.dgN_crossl, CL.dgN_crossr,
    CL.dgC_nil] at e
  simp only [Functor.map_comp, Presentation.lift_diag, Functor.map_smul,
    CategoryTheory.Functor.map_id] at e
  exact e

/-- Brundan's relation (`KL3.Diagram.CL.dgN_downupFE_ge`) in the model:
`crossr j i ≫ crossl j i = t_{ij} · 1` on `F_i E_j 1_ν` for `⟨i, ν⟩ ≥ d_{ij}`. -/
theorem interp_crossr_crossl_ge {j i : I} (hji : j ≠ i) (ν s₀ : X)
    (h : (C.dij i j : ℤ) ≤ KL3.Diagram.ip RD i ν) :
    (interp (S.genImg hsl Sc) s₀ ν).functor.map (crossr RD j i ν) ≫
        (interp (S.genImg hsl Sc) s₀ ν).functor.map (crossl RD j i ν) =
      (Sc.t i j : k) • 𝟙 _ := by
  have e := congrArg ((CL.presNM RD k Sc).lift
    (S.respects_presNM hsl Sc hr hQ hQ2 hQ3 s₀ ν)).map (CL.dgN_downupFE_ge hr hji.symm ν h)
  rw [← CL.dgC_comp (s := [dn i, up j]) (t := [up j, dn i]) (r := [dn i, up j])
    (A := crossrL j i) (B := crosslL j i) (by schain) (by schain), CL.dgN_crossl, CL.dgN_crossr,
    CL.dgC_nil] at e
  simp only [Functor.map_comp, Presentation.lift_diag, Functor.map_smul,
    CategoryTheory.Functor.map_id] at e
  exact e

/-- **The sideways crossing `crossl j i` is an isomorphism in the model** at every weight where
Brundan's argument gives a one-sided inverse. -/
theorem isIso_interp_crossl {j i : I} (hji : j ≠ i) (ν : X) {s₀ : X}
    (hs : (KL3.Diagram.wt RD ν [up j, dn i] : X) = s₀)
    (hν : KL3.Diagram.ip RD i (KL3.Diagram.wt RD ν [dn i]) ≤ 0 ∨
      (C.dij i j : ℤ) ≤ KL3.Diagram.ip RD i ν) :
    IsIso ((interp (S.genImg hsl Sc) s₀ ν).functor.map (crossl RD j i ν)) := by
  rcases hν with h | h
  · exact GradedHomCat.isIso_of_comp_eq_smul_id (S.isHomogeneous_crossl hsl Sc j i ν s₀ ν)
      (S.crossObjIso hsl Sc hji ν hs) (S.crossObjIso_hom_isHomogeneous hsl Sc hji ν hs)
      (Units.ne_zero _) (S.interp_crossl_crossr_le hsl Sc hr hQ hQ2 hQ3 hji ν s₀ h)
  · exact GradedHomCat.isIso_of_comp_eq_smul_id' (S.isHomogeneous_crossl hsl Sc j i ν s₀ ν)
      (S.crossObjIso hsl Sc hji ν hs) (S.crossObjIso_hom_isHomogeneous hsl Sc hji ν hs)
      (Units.ne_zero _) (S.interp_crossr_crossl_ge hsl Sc hr hQ hQ2 hQ3 hji ν s₀ h)

end Mixed

end QStrong

end Model

end Categorification.TwoRep
