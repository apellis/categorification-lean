/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidAction
import Categorification.WeightedKLR.Rigidity.FundamentalBraidSpan
import Categorification.WeightedKLR.RedStrands.BraidedStandardIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The complex of fundamental braid cuts

For Webster, arXiv:1309.3796v2, Proposition 7.11, the right tensor of the
middle resolution with the fundamental braid bimodule has two identical
middle cuts and a terminal cut between them. The mixed crossings give
a scalar homology line in the middle term.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "V" => ViolQuotient ℚ Q wt ν
local notation "R" => KLRAlgebra ℚ (stendhalQ Q wt) μ
local notation "E" s:arg => braidProject (e s)
local notation "P" => violMk ℚ Q wt ν (redProj ℚ Q wt ν [1,0])
local notation "A" => braidProject (ψ 1 * ψ 0 * e crossedTerminal)
local notation "B" => braidProject (ψ 0 * ψ 1 * e crossedMiddle)
local notation "U" => braidProject (ψ 0 * e crossedTerminal)
local notation "D" => braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal)
local notation "C" => braidProject (ψ 1)
local notation "Cut" s:arg => violCorner ℚ Q wt ν s [1,0]

private noncomputable local instance enumerate : Fintype (Seq μ) :=
  inferInstanceAs (Fintype {f : Fin (Multiset.card μ) → Unit ⊕ Fin 2 // Finset.univ.val.map f = μ})

private theorem crossedOrder_sum : P = E crossedMiddle + E crossedTerminal := by
  let v : Seq μ := Seq.ofList [.inl (),.inr 1,.inr 0] (by decide)
  have hv : IsViolated v := by unfold IsViolated; decide +kernel
  have h : Finset.univ.filter (fun s : Seq μ => redWord s = [1,0]) =
      {crossedMiddle,crossedTerminal,v} := by
    clear hv
    ext s
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    revert s
    decide +kernel +revert
  rw [redProj,redIdem,map_sum,map_sum]
  rw [Subsingleton.elim (Seq.instFintype : Fintype (Seq μ)) enumerate,h]
  rw [Finset.sum_insert (by decide +kernel),Finset.sum_insert (by decide +kernel),Finset.sum_singleton]
  rw [violMk_e hv,add_zero]
  rfl

private theorem supports (s t : Seq μ) (γ : List ℕ)
    (ht : wordProd (Multiset.card μ) γ • s = t) :
    E t * braidProject (ψw γ * e s) = braidProject (ψw γ * e s) ∧
    braidProject (ψw γ * e s) * E s = braidProject (ψw γ * e s) := by
  have he : (ψw γ * e s : R) = e t * ψw γ := by rw [ψw_mul_e,ht]
  exact ⟨by rw [← map_mul,he,← mul_assoc,e_mul_self],
    by rw [← map_mul,mul_assoc,e_mul_self]⟩

private theorem middle_support : E middle * A = A ∧ A * E crossedTerminal = A := by
  simpa [ψw] using supports crossedTerminal middle [1,0] (by decide +kernel)

private theorem terminal_middle_support : E terminal * B = B ∧ B * E crossedMiddle = B := by
  simpa [ψw] using supports crossedMiddle terminal [0,1] (by decide +kernel)

private theorem terminal_support : E terminal * U = U ∧ U * E crossedTerminal = U := by
  simpa [ψw] using supports crossedTerminal terminal [0] (by decide +kernel)

private theorem dotted_support : E terminal * D = D ∧ D * E crossedTerminal = D := by
  have hc : Commute (x ⟨2,by decide⟩ : R) (e crossedTerminal) := x_mul_e _ _
  have hd : D = U * braidProject (x ⟨2,by decide⟩) := by
    rw [← map_mul,mul_assoc,hc.eq,← mul_assoc]
  rw [hd]
  refine ⟨by rw [← mul_assoc,terminal_support.1],?_⟩
  rw [mul_assoc, (hc.map braidProject).eq, ← mul_assoc,terminal_support.2]

private theorem middle_expansion (z : Cut middle) : ∃ a : ℚ, z.val = a • A := by
  obtain ⟨hl,hr⟩ := mem_violCorner_iff.mp z.property
  obtain ⟨a,ha⟩ := (fundamentalBraid_mixed_span z.val).1
  change E middle * z.val = z.val at hl
  rw [hl] at ha
  have h0 := (fundamentalBraid_middle_middle_zero z.val).2
  rw [hl] at h0
  rw [crossedOrder_sum,mul_add,h0,zero_add,ha] at hr
  exact ⟨a,hr.symm⟩

private theorem terminal_expansion (z : Cut terminal) :
    ∃ a b c : ℚ, z.val = a • B + (b • U + c • D) := by
  obtain ⟨hl,hr⟩ := mem_violCorner_iff.mp z.property
  obtain ⟨a,ha⟩ := (fundamentalBraid_mixed_span z.val).2
  obtain ⟨b,c,hb⟩ := fundamentalBraid_terminal_span z.val
  change E terminal * z.val = z.val at hl
  rw [hl] at ha hb
  rw [crossedOrder_sum,mul_add,ha,hb] at hr
  exact ⟨a,b,c,hr.symm⟩

private theorem cross_middle_zero : C * B = 0 := by
  have ht : sadj (Multiset.card μ) 1 • terminal = middle := by decide +kernel
  have h : C * E terminal = E middle * C := by rw [← map_mul,ψ_mul_e,ht,map_mul]
  have hs : E middle * (C * B) = C * B := by rw [← mul_assoc,← h,mul_assoc,terminal_middle_support.1]
  have h' := (fundamentalBraid_middle_middle_zero (C * B)).2
  rwa [hs,mul_assoc,terminal_middle_support.2] at h'

private theorem middle_sep : U * E crossedMiddle = 0 ∧ D * E crossedMiddle = 0 := by
  have h : E crossedTerminal * E crossedMiddle = 0 := by
    rw [← map_mul,e_mul_e,ite_eq_right (by decide +kernel),map_zero]
  exact ⟨by rw [← terminal_support.2,mul_assoc,h,mul_zero],
    by rw [← dotted_support.2,mul_assoc,h,mul_zero]⟩

private theorem inCut (s t : Seq μ) (z : V) (hl : E s * z = z) (hr : z * E t = z)
    (h : redWord t = [1,0]) : z ∈ Cut s := by
  refine mem_violCorner_iff.mpr ⟨hl,?_⟩
  have he : E t * P = E t := by
    change violMk ℚ Q wt ν _ * violMk ℚ Q wt ν _ = _
    rw [← map_mul]
    apply congrArg (violMk ℚ Q wt ν)
    exact (e_mul_redProj [1,0] t).trans (ite_eq_left h)
  calc z * P = (z * E t) * P := congrArg (· * P) hr.symm
       _ = z := by rw [mul_assoc,he,hr]

private def aGen : Cut middle := ⟨A,inCut _ _ _ middle_support.1 middle_support.2 (by decide +kernel)⟩
private def bGen : Cut terminal :=
  ⟨B,inCut _ _ _ terminal_middle_support.1 terminal_middle_support.2 (by decide +kernel)⟩
private def uGen : Cut terminal := ⟨U,inCut _ _ _ terminal_support.1 terminal_support.2 (by decide +kernel)⟩
private def dGen : Cut terminal := ⟨D,inCut _ _ _ dotted_support.1 dotted_support.2 (by decide +kernel)⟩

private def cutCross (s t : Seq μ) (h : sadj (Multiset.card μ) 1 • s = t) : Cut s →ₗ[ℚ] Cut t where
  toFun z := ⟨C * z.val, by
    obtain ⟨hl,hr⟩ := mem_violCorner_iff.mp z.property
    change E s * z.val = z.val at hl
    have he : E t * C = C * E s := by rw [← h,← map_mul,← ψ_mul_e,map_mul]
    apply mem_violCorner_iff.mpr
    exact ⟨by change E t * _ = _; rw [← mul_assoc,he,mul_assoc,hl],by rw [mul_assoc,hr]⟩⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' c z := Subtype.ext (mul_smul_comm _ _ _)

private abbrev d₂ := cutCross middle terminal (by decide +kernel)
private abbrev d₁ := cutCross terminal middle (by decide +kernel)

private theorem d₂_a : d₂ aGen = dGen := Subtype.ext fundamentalBraid_terminal_differentials.1
private theorem d₁_u : d₁ uGen = aGen := Subtype.ext fundamentalBraid_terminal_differentials.2.1
private theorem d₁_d : d₁ dGen = 0 := Subtype.ext fundamentalBraid_terminal_differentials.2.2
private theorem d₁_b : d₁ bGen = 0 := Subtype.ext cross_middle_zero

private theorem mid_repr (z : Cut middle) : ∃ a : ℚ, z = a • aGen := by
  obtain ⟨a,ha⟩ := middle_expansion z
  exact ⟨a,Subtype.ext ha⟩

private theorem term_repr (z : Cut terminal) : ∃ a b c : ℚ, z = a • bGen + (b • uGen + c • dGen) := by
  obtain ⟨a,b,c,h⟩ := terminal_expansion z
  exact ⟨a,b,c,Subtype.ext h⟩

private theorem d₂_inj : Function.Injective d₂ := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a,rfl⟩ := mid_repr z
  rw [map_smul,d₂_a] at hz
  have hh : dGen ≠ 0 := fun he => fundamentalBraid_terminal_linearIndependent.ne_zero 1 (congrArg Subtype.val he)
  rw [(smul_eq_zero.mp hz).resolve_right hh,zero_smul]

private theorem d₁_surj : Function.Surjective d₁ := by
  intro z
  obtain ⟨a,rfl⟩ := mid_repr z
  exact ⟨a • uGen,by rw [map_smul,d₁_u]⟩

open CategoryTheory

/-- The middle, terminal and middle loading cuts with their crossing maps
after tensoring the fundamental projectives in Webster v2, Proposition 7.11. -/
def fundamentalBraidCutComplex : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (ModuleCat.ofHom d₂) (ModuleCat.ofHom d₁) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨a,rfl⟩ := mid_repr z
    change d₁ (d₂ (a • aGen)) = 0
    rw [map_smul,d₂_a,map_smul,d₁_d,smul_zero])

/-- The braid-cut resolution has zero homology in its two outside terms
(Webster v2, Proposition 7.11). -/
theorem fundamentalBraidCutComplex_ends :
    Function.Injective fundamentalBraidCutComplex.f ∧ Function.Surjective fundamentalBraidCutComplex.g :=
  ⟨d₂_inj,d₁_surj⟩

/-- A cycle freely spanning homology over the rationals identifies the middle
homology of a short complex with the rational line. -/
def scalarHomologyIsoOfSpanningCycle (S : ShortComplex (ModuleCat.{0} ℚ)) (v : S.X₂) (hv : S.g v = 0)
    (indep : ∀ (a : ℚ) (m : S.X₁), S.f m = a • v → a = 0)
    (spans : ∀ z : S.X₂, S.g z = 0 → ∃ (a : ℚ) (m : S.X₁), S.f m = a • v - z) :
    S.homology ≅ ModuleCat.of ℚ ℚ := by
  let z₀ : LinearMap.ker S.g.hom := ⟨v,hv⟩
  let f := S.moduleCatToCycles.range.mkQ.comp (LinearMap.toSpanSingleton ℚ (LinearMap.ker S.g.hom) z₀)
  have h₁ : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro a ha
    change Submodule.Quotient.mk (p := S.moduleCatToCycles.range) (a • z₀) = 0 at ha
    obtain ⟨m,hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp ha
    exact indep a m (congrArg Subtype.val hm)
  have h₂ : Function.Surjective f := by
    intro x
    obtain ⟨z,rfl⟩ := S.moduleCatToCycles.range.mkQ_surjective x
    obtain ⟨a,m,hm⟩ := spans z.val z.property
    refine ⟨a,(Submodule.Quotient.eq _).mpr ?_⟩
    exact ⟨m,Subtype.ext hm⟩
  exact S.moduleCatHomologyIso ≪≫ (LinearEquiv.ofBijective f ⟨h₁,h₂⟩).symm.toModuleIso

/-- The reversed middle diagram representing the homology of the fundamental
braid-cut resolution in Webster v2, Proposition 7.11. -/
def fundamentalBraidCycle : Cut terminal := bGen

theorem fundamentalBraidCycle_val :
    fundamentalBraidCycle.val = B := rfl

theorem fundamentalBraidCycle_supported :
    fundamentalBraidCycle.val * E crossedMiddle = fundamentalBraidCycle.val :=
  terminal_middle_support.2

theorem fundamentalBraidCycle_ne_zero : fundamentalBraidCycle.val ≠ 0 :=
  fundamentalBraid_mixed_ne_zero.2

theorem fundamentalBraidCycle_closed : fundamentalBraidCutComplex.g fundamentalBraidCycle = 0 := d₁_b

/-- Every cycle in the tensored resolution differs from a scalar multiple
of the reversed middle diagram by a boundary (Webster v2, Proposition 7.11). -/
theorem fundamentalBraidCycle_mod_boundaries (z : Cut terminal) (hz : fundamentalBraidCutComplex.g z = 0) :
    ∃ (a : ℚ) (y : Cut middle), fundamentalBraidCutComplex.f y = a • fundamentalBraidCycle - z := by
  obtain ⟨a,b,c,he⟩ := term_repr z
  change d₁ z = 0 at hz
  rw [he,map_add,map_add,map_smul,map_smul,map_smul,d₁_b,d₁_u,d₁_d,smul_zero,smul_zero,add_zero,zero_add] at hz
  have ha : aGen ≠ 0 := fun hh => fundamentalBraid_mixed_ne_zero.1 (congrArg Subtype.val hh)
  rw [(smul_eq_zero.mp hz).resolve_right ha,zero_smul,zero_add] at he
  refine ⟨a,(-c) • aGen,?_⟩
  change d₂ ((-c) • aGen) = a • bGen - z
  rw [map_smul,d₂_a,he]
  apply Subtype.ext
  change (-c) • D = a • B - (a • B + c • D)
  rw [neg_smul,sub_add_eq_sub_sub,sub_self,zero_sub]

/-- A closed vector is a boundary precisely when its component at the
reversed middle loading vanishes (Webster v2, Proposition 7.11). -/
theorem fundamentalBraidCycle_boundary_iff (z : Cut terminal) (hz : fundamentalBraidCutComplex.g z = 0) :
    (∃ y : Cut middle, fundamentalBraidCutComplex.f y = z) ↔ z.val * E crossedMiddle = 0 := by
  have hb (y : Cut middle) : (d₂ y).val * E crossedMiddle = 0 := by
    obtain ⟨c,rfl⟩ := mid_repr y
    rw [map_smul,d₂_a]
    change (c • D) * E crossedMiddle = 0
    rw [smul_mul_assoc,middle_sep.2,smul_zero]
  constructor
  · rintro ⟨y,rfl⟩
    exact hb y
  · intro hp
    obtain ⟨a,y,hy⟩ := fundamentalBraidCycle_mod_boundaries z hz
    have h := hb y
    change (fundamentalBraidCutComplex.f y : Cut terminal).val * E crossedMiddle = 0 at h
    rw [hy] at h
    change (a • B - z.val) * E crossedMiddle = 0 at h
    rw [sub_mul,smul_mul_assoc,terminal_middle_support.2,hp,sub_zero] at h
    have ha : a = 0 := (smul_eq_zero.mp h).resolve_right fundamentalBraid_mixed_ne_zero.2
    rw [ha,zero_smul,zero_sub] at hy
    exact ⟨-y,by change d₂ (-y) = z; rw [map_neg,show d₂ y = -z from hy,neg_neg]⟩

/-- Homology in the middle term of the fundamental braid-cut resolution
is the scalar line over ℚ (Webster v2, Proposition 7.11). Its generator
is the reduced diagram with reversed middle loading at the bottom. -/
def fundamentalBraidCutComplex_homologyIso :
    fundamentalBraidCutComplex.homology ≅ ModuleCat.of ℚ ℚ := by
  apply scalarHomologyIsoOfSpanningCycle fundamentalBraidCutComplex bGen d₁_b
  · intro a m he
    change d₂ m = a • bGen at he
    obtain ⟨c,rfl⟩ := mid_repr m
    rw [map_smul,d₂_a] at he
    have hh : c • D = a • B := congrArg Subtype.val he
    have ht := congrArg (· * E crossedMiddle) hh
    simp only [smul_mul_assoc,middle_sep.2,terminal_middle_support.2,smul_zero] at ht
    exact (smul_eq_zero.mp ht.symm).resolve_right fundamentalBraid_mixed_ne_zero.2
  · exact fundamentalBraidCycle_mod_boundaries

end Categorification.Stendhal.FundamentalCorner
