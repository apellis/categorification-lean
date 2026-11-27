/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TiltingSummand
import Categorification.Algebra.OrderedProjectiveResolution

set_option backward.isDefEq.respectTransparency false

/-!
# `Ext¹` between standards in the wrong order

For standards `S c` with ordered covers `0 → K → R e_c → S c → 0` whose kernels are filtered by
standards strictly above `c`: if every idempotent `e_d` with `d` above `s` kills `S a`, then
`Ext¹(S s, S a) = 0` (`OrderedStandardCovers.hom_shift_one_eq_zero`). This is the input of
Ringel's argument used in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 6.14 (second clause): `Ext¹(Δ_s, Δ_a) = 0` unless `s < a`.
In a filtration of a nontrivial module some subquotient is nontrivial
(`HasFiltration.exists_nontrivial`).
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  ModuleFiltration
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [HasDerivedCategory.{0, 0} R]

/-- **`Ext¹` from the cokernel of a projective cover**: if `0 → K → P → Z → 0` is exact with `P`
projective and `Hom(K, Y) = 0`, then `Ext¹(Z, Y) = 0`. -/
theorem hom_shift_one_eq_zero_of_projective_of_linearMap_eq_zero {K P Z Y : ModuleCat.{0} R}
    [Module.Projective R P] (f : K →ₗ[R] P) (g : P →ₗ[R] Z) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (h : ∀ φ : K →ₗ[R] Y, φ = 0)
    (u : moduleObj Z ⟶ (moduleObj Y)⟦(1 : ℤ)⟧) : u = 0 := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module _
    (shortExact_of_linear f g hf hfg hg)
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ _ hT u
    (hom_shift_eq_zero_of_projective P Y one_ne_zero _)
  have hv0 : v = 0 := by
    obtain ⟨w, rfl⟩ := (shiftFunctor (DerivedCategory.{0} R) (1 : ℤ)).map_surjective v
    obtain ⟨φ, rfl⟩ := (degreeZeroModuleFunctor R ⋙ DG.DerivedCategory.Q).map_surjective
      (X := K) (Y := Y) w
    have hφ : φ = 0 := ModuleCat.hom_ext (h φ.hom)
    rw [hφ, Functor.map_zero, Functor.map_zero]
  rw [hv, hv0, comp_zero]

omit [HasDerivedCategory.{0, 0} R] in
/-- `Hom(R e, W) = 0` when the idempotent `e` kills `W`. -/
theorem linearMap_lIdeal_eq_zero {e : R} (he : IsIdempotentElem e) {W : Type} [AddCommGroup W]
    [Module R W] (hW : ∀ x : W, e • x = 0) (φ : lIdeal e →ₗ[R] W) : φ = 0 := by
  have hmem : e ∈ lIdeal e := he
  have h0 : φ ⟨e, hmem⟩ = 0 := by
    have : (⟨e, hmem⟩ : lIdeal e) = e • ⟨e, hmem⟩ := Subtype.ext he.symm
    rw [this, φ.map_smul, hW]
  refine LinearMap.ext fun y => ?_
  have : y = (y : R) • (⟨e, hmem⟩ : lIdeal e) := Subtype.ext y.2.symm
  rw [this, φ.map_smul, h0, smul_zero, LinearMap.zero_apply]

namespace ModuleFiltration

omit [HasDerivedCategory.{0, 0} R] in
/-- In a filtration of a nontrivial module some subquotient is nontrivial. -/
theorem HasFiltration.exists_nontrivial {ι : Type*} {L : ι → ModuleCat.{0} R} {m : List ι}
    {X : ModuleCat.{0} R} (h : HasFiltration L m X) (hX : Nontrivial X) :
    ∃ c ∈ m, Nontrivial (L c) := by
  by_contra hc
  have hc' : ∀ c ∈ m, Subsingleton (L c) := fun c hcm =>
    not_nontrivial_iff_subsingleton.1 fun hn => hc ⟨c, hcm, hn⟩
  have h0 := h.linearMap_eq_zero (W := X) (fun c hcm φ => LinearMap.ext fun x => by
    have := hc' c hcm
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]) (LinearMap.id : X →ₗ[R] X)
  obtain ⟨x, y, hxy⟩ := hX
  exact hxy ((LinearMap.congr_fun h0 x).trans (LinearMap.congr_fun h0 y).symm)

end ModuleFiltration

namespace ModuleFiltration.OrderedStandardCovers

variable {ι : Type} {S : ι → ModuleCat.{0} R} {e : ι → R} {above : ι → ι → Prop}

/-- **`Ext¹` between standards in the wrong order vanishes**: if every idempotent `e_d` with
`d` above `s` kills `S a`, then `Ext¹(S s, S a) = 0`. -/
theorem hom_shift_one_eq_zero (data : OrderedStandardCovers S e above)
    (he : ∀ d, IsIdempotentElem (e d)) {s a : ι}
    (hann : ∀ d, above s d → ∀ x : S a, e d • x = 0)
    (u : moduleObj (S s) ⟶ (moduleObj (S a))⟦(1 : ℤ)⟧) : u = 0 := by
  obtain ⟨m, hm, hK⟩ := data.kernel s
  have := data.projective s
  refine hom_shift_one_eq_zero_of_projective_of_linearMap_eq_zero
    (P := ModuleCat.of R (lIdeal (e s))) (LinearMap.ker (data.quotient s)).subtype
    (data.quotient s) (Submodule.injective_subtype _) (fun x => ?_) (data.surjective s)
    (fun φ => hK.linearMap_eq_zero (fun d hd ψ => ?_) φ) u
  · simp
  · have h0 := linearMap_lIdeal_eq_zero (he d) (hann d (hm d hd)) (ψ ∘ₗ data.quotient d)
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := data.surjective d x
    exact LinearMap.congr_fun h0 y

end ModuleFiltration.OrderedStandardCovers

end Categorification
