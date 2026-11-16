/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Algebra

/-!
# The polynomial representation of the twisted gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5,
Proposition 2.20 (a): the polynomial representation of the category `P`.

The twisted gallery algebra `TwGalleryAlgebra k Γ ν` acts on
`V = (TwChamber Γ ν → k[y_s])`, one copy of the polynomial ring for each chamber of the
arrangement of positions and weights, by the operators of `GalleryRep.lean`: `e C` projects to
the copy of `C`, polynomials act by multiplication, relabellings rename the variables, and a step
across the hyperplane `h` acts by `hypOp Γ h`: multiplication by `Q_e(y_a, y_b)` or the identity
across a wall, the operator `ψ` across a diagonal. These operators depend on the hyperplane
crossed and on the side of the start chamber, not on the weighting.

Every relation is checked by the chamber-independent identities of `GalleryRep.lean`. The loop
block `{d, W, W.comap d.refl}` of an edge `e` from the colour of `d` to itself, the flat where a
strand would meet its own ghost, is covered by `hypOp_mid_diag` and `hypOp_end_diag` as for any
other edge.

## Main definitions

* `twStepOp Γ C C'`: the operator of the step from `C` to `C'`.
* `twGalleryRep k hΓ`: the polynomial representation, for symmetric loop polynomials.
* `twStepOp_toTw`: on one weighting, the steps are those of `galleryRep`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

variable (Γ) in
/-- The operator of the step from `C` to `C'`: zero unless they are adjacent. -/
noncomputable def twStepOp (C C' : TwChamber Γ ν) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  open Classical in
  if hC : ∃ h, C.Adjacent C' h then hypOp Γ hC.choose (C.1 hC.choose) (C'.1 hC.choose) else 0

omit [IsStrictOrderedRing 𝕜] in
theorem twStepOp_eq {C C' : TwChamber Γ ν} {h : Hyp Γ ν} (hh : C.Adjacent C' h) :
    twStepOp (k := k) Γ C C' = hypOp Γ h (C.1 h) (!C.1 h) := by
  have hC : ∃ h, C.Adjacent C' h := ⟨h, hh⟩
  rw [twStepOp, dite_eq_left_of_eq_true (eq_true hC), (hC.choose_spec.unique hh), hh.apply_eq_not]

omit [IsStrictOrderedRing 𝕜] in
theorem twStepOp_of_not {C C' : TwChamber Γ ν} (hh : ∀ h, ¬C.Adjacent C' h) :
    twStepOp (k := k) Γ C C' = 0 := by
  rw [twStepOp, dite_eq_right_of_eq_false (eq_false (not_exists.2 hh))]

theorem ren_comp_twStepOp (g : ColPerm ν) (C C' : TwChamber Γ ν) :
    ren (k := k) g ∘ₗ twStepOp Γ C C' = twStepOp Γ (g • C) (g • C') ∘ₗ ren g := by
  by_cases hC : ∃ h, C.Adjacent C' h
  · obtain ⟨h, hh⟩ := hC
    rw [twStepOp_eq hh, twStepOp_eq (hh.smul g), TwChamber.smul_apply]
    have := ren_comp_hypOp (k := k) g (h.comap g⁻¹) (C.1 h)
    simpa only [Hyp.comap_inv_comap] using this
  · push Not at hC
    have hC' : ∀ h, ¬(g • C).Adjacent (g • C') h := fun h hh => hC _ (hh.of_smul g)
    rw [twStepOp_of_not hC, twStepOp_of_not hC', LinearMap.comp_zero, LinearMap.zero_comp]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.twLeft_ne_twRight (C : TwChamber Γ ν) (d : Diag ν) : d.twLeft C ≠ d.twRight C := by
  unfold Diag.twLeft Diag.twRight
  split_ifs
  · exact d.fst_ne_snd
  · exact d.fst_ne_snd.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.twLeft_label (C : TwChamber Γ ν) (d : Diag ν) : (d.twLeft C).1 = d.fst.1 := by
  unfold Diag.twLeft
  split_ifs
  · rfl
  · exact d.fst_label_eq_snd.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.twRight_label (C : TwChamber Γ ν) (d : Diag ν) : (d.twRight C).1 = d.fst.1 := by
  unfold Diag.twRight
  split_ifs
  · exact d.fst_label_eq_snd.symm
  · rfl

omit [IsStrictOrderedRing 𝕜] in
theorem Diag.swap_twLeft_twRight (C : TwChamber Γ ν) (d : Diag ν) :
    swap (d.twLeft C) (d.twRight C) = swap d.fst d.snd := by
  unfold Diag.twLeft Diag.twRight
  split_ifs
  · rfl
  · exact swap_comm _ _

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.twLeft_of_adjacent {C C' : TwChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) : d.twLeft C' = d.twRight C := by
  unfold Diag.twLeft Diag.twRight
  rw [h.apply_eq_not]
  cases C.1 (.inr d) <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.twRight_of_adjacent {C C' : TwChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) : d.twRight C' = d.twLeft C := by
  unfold Diag.twLeft Diag.twRight
  rw [h.apply_eq_not]
  cases C.1 (.inr d) <;> rfl

omit [IsStrictOrderedRing 𝕜] in
theorem twStepOp_inl {C C' : TwChamber Γ ν} {w : Wall Γ ν} (h : C.Adjacent C' (.inl w)) :
    twStepOp (k := k) Γ C C' = wallOp w (C.1 (.inl w)) (!C.1 (.inl w)) :=
  twStepOp_eq h

omit [IsStrictOrderedRing 𝕜] in
theorem twStepOp_inr {C C' : TwChamber Γ ν} {d : Diag ν} (h : C.Adjacent C' (.inr d)) :
    twStepOp (k := k) Γ C C' = psiOp Γ (d.twLeft C) (d.twRight C) :=
  twStepOp_eq h

omit [IsStrictOrderedRing 𝕜] in
/-- The ghost bigon in the representation. -/
theorem twStepOp_comp_twStepOp_inl {C C' : TwChamber Γ ν} {w : Wall Γ ν}
    (h : C.Adjacent C' (.inl w)) :
    twStepOp (k := k) Γ C' C ∘ₗ twStepOp Γ C C' = LinearMap.mulLeft k w.factor := by
  rw [twStepOp_inl h, twStepOp_inl h.symm, h.apply_eq_not, Bool.not_not]
  exact wallOp_comp_wallOp w (by cases C.1 (.inl w) <;> decide)

omit [IsStrictOrderedRing 𝕜] in
/-- The strand bigon in the representation. -/
theorem twStepOp_twStepOp_inr (hΓ : Γ.PSymm) {C C' : TwChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) (f : PolyRing ν k) :
    twStepOp Γ C' C (twStepOp Γ C C' f) =
      match Γ.loop d.fst.1 with
      | none => 0
      | some P => -2 * loopFactor P (d.twLeft C) (d.twRight C) *
          rename (swap d.fst d.snd) (twStepOp Γ C C' f) := by
  rw [twStepOp_inr h, twStepOp_inr h.symm, Diag.twLeft_of_adjacent h, Diag.twRight_of_adjacent h,
    psiOp_psiOp_swap hΓ (Diag.twLeft_ne_twRight C d)
      (by rw [Diag.twLeft_label C d, Diag.twRight_label C d]),
    Diag.twLeft_label C d, Diag.swap_twLeft_twRight C d]
  rfl

omit [IsStrictOrderedRing 𝕜] in
/-- Polynomials past a diagonal step in the representation. -/
theorem twStepOp_mul_inr {C C' : TwChamber Γ ν} {d : Diag ν} (h : C.Adjacent C' (.inr d))
    (f g : PolyRing ν k) :
    twStepOp Γ C C' (f * g) - f * twStepOp Γ C C' g =
      stepFactor Γ (d.twLeft C) (d.twRight C) f * rename (swap d.fst d.snd) g := by
  rw [twStepOp_inr h, psiOp_leibniz (Diag.twLeft_ne_twRight C d), Diag.swap_twLeft_twRight C d]

omit [IsStrictOrderedRing 𝕜] in
/-- The square relation in the representation. -/
theorem twStepOp_square {C B B' D : TwChamber Γ ν} {h₁ h₂ : Hyp Γ ν} (hne : h₁ ≠ h₂)
    (hi : h₁.Independent h₂) (a₁ : C.Adjacent B h₁) (a₂ : B.Adjacent D h₂)
    (a₃ : C.Adjacent B' h₂) (a₄ : B'.Adjacent D h₁) :
    twStepOp (k := k) Γ B D ∘ₗ twStepOp Γ C B = twStepOp Γ B' D ∘ₗ twStepOp Γ C B' := by
  rw [twStepOp_eq a₁, twStepOp_eq a₂, twStepOp_eq a₃, twStepOp_eq a₄, ← a₁.2 h₂ hne.symm,
    ← a₃.2 h₁ hne]
  exact hypOp_comm hi _ _ _ _

omit [IsStrictOrderedRing 𝕜] in
/-- The operator of the gallery `A₀ → A₁ → A₂ → A₃`, read off the sides of `A₀`. -/
theorem TwHexagon.twStepOp_gal₁ (H : TwHexagon Γ ν) :
    twStepOp (k := k) Γ H.A₂ H.A₃ ∘ₗ twStepOp Γ H.A₁ H.A₂ ∘ₗ twStepOp Γ H.A₀ H.A₁ =
      hypOp Γ H.h₃ (H.A₀.1 H.h₃) (!H.A₀.1 H.h₃) ∘ₗ hypOp Γ H.h₂ (H.A₀.1 H.h₂) (!H.A₀.1 H.h₂) ∘ₗ
        hypOp Γ H.h₁ (H.A₀.1 H.h₁) (!H.A₀.1 H.h₁) := by
  rw [twStepOp_eq H.adj₀₁, twStepOp_eq H.adj₁₂, twStepOp_eq H.adj₂₃, ← H.adj₁₂.2 H.h₃ H.ne₂₃.symm,
    ← H.adj₀₁.2 H.h₃ H.ne₁₃.symm, ← H.adj₀₁.2 H.h₂ H.ne₁₂.symm]

omit [IsStrictOrderedRing 𝕜] in
/-- The operator of the gallery `A₀ → A₅ → A₄ → A₃`, read off the sides of `A₀`. -/
theorem TwHexagon.twStepOp_gal₂ (H : TwHexagon Γ ν) :
    twStepOp (k := k) Γ H.A₄ H.A₃ ∘ₗ twStepOp Γ H.A₅ H.A₄ ∘ₗ twStepOp Γ H.A₀ H.A₅ =
      hypOp Γ H.h₁ (H.A₀.1 H.h₁) (!H.A₀.1 H.h₁) ∘ₗ hypOp Γ H.h₂ (H.A₀.1 H.h₂) (!H.A₀.1 H.h₂) ∘ₗ
        hypOp Γ H.h₃ (H.A₀.1 H.h₃) (!H.A₀.1 H.h₃) := by
  rw [twStepOp_eq H.adj₀₅, twStepOp_eq H.adj₅₄, twStepOp_eq H.adj₄₃, ← H.adj₅₄.2 H.h₁ H.ne₁₂,
    ← H.adj₀₅.2 H.h₁ H.ne₁₃, ← H.adj₀₅.2 H.h₂ H.ne₂₃]

omit [IsStrictOrderedRing 𝕜] in
theorem twHypOp_inr_left (C : TwChamber Γ ν) (d : Diag ν) (σ' : Bool) :
    hypOp (k := k) Γ (.inr d) (C.1 (.inr d)) σ' = psiOp Γ (d.twLeft C) (d.twRight C) := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.twLeft_twRight {d : Diag ν} {a b : Strand ν} (h : d.Joins a b)
    (C : TwChamber Γ ν) : (d.twLeft C = a ∧ d.twRight C = b) ∨ (d.twLeft C = b ∧ d.twRight C = a) := by
  unfold Diag.twLeft Diag.twRight
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> simp

variable (k Γ ν) in
/-- The action of the generators on `V = (TwChamber Γ ν → k[y_s])`. -/
noncomputable def twGenOp : TwGen k Γ ν → Module.End k (TwChamber Γ ν → PolyRing ν k)
  | .idem C => blk k C C LinearMap.id
  | .poly f => diagOp (LinearMap.mulLeft k f)
  | .step C C' => blk k C C' (twStepOp Γ C C')
  | .relabel g C => blk k C (g • C) (ren g)

variable (k Γ ν) in
/-- The action of the free algebra on the generators. -/
noncomputable def twFreeRep :
    FreeAlgebra k (TwGen k Γ ν) →ₐ[k] Module.End k (TwChamber Γ ν → PolyRing ν k) :=
  FreeAlgebra.lift k (twGenOp k Γ ν)

theorem twFreeRep_gal₁ (H : TwHexagon Γ ν) :
    twFreeRep k Γ ν (H.gal₁ k Γ ν) =
      blk k H.A₀ H.A₃ (twStepOp Γ H.A₂ H.A₃ ∘ₗ twStepOp Γ H.A₁ H.A₂ ∘ₗ twStepOp Γ H.A₀ H.A₁) := by
  simp only [TwHexagon.gal₁, twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp,
    Module.End.mul_eq_comp, blk_comp_blk, LinearMap.comp_assoc]

theorem twFreeRep_gal₂ (H : TwHexagon Γ ν) :
    twFreeRep k Γ ν (H.gal₂ k Γ ν) =
      blk k H.A₀ H.A₃ (twStepOp Γ H.A₄ H.A₃ ∘ₗ twStepOp Γ H.A₅ H.A₄ ∘ₗ twStepOp Γ H.A₀ H.A₅) := by
  simp only [TwHexagon.gal₂, twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp,
    Module.End.mul_eq_comp, blk_comp_blk, LinearMap.comp_assoc]

/-- The representation respects the defining relations of the twisted gallery algebra. -/
theorem twFreeRep_rel (hΓ : Γ.PSymm) {x y : FreeAlgebra k (TwGen k Γ ν)} (h : TwGalRel k Γ ν x y) :
    twFreeRep k Γ ν x = twFreeRep k Γ ν y := by
  cases h with
  | idem_mul C D =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp]
    split_ifs with hCD
    · subst hCD
      rw [blk_comp_blk, LinearMap.id_comp, FreeAlgebra.lift_ι_apply]
      rfl
    · rw [blk_comp_blk_of_ne (Ne.symm hCD), map_zero]
  | idem_sum =>
    simp only [twFreeRep, map_sum, FreeAlgebra.lift_ι_apply, twGenOp, map_one]
    exact sum_blk_id
  | poly_add f g =>
    simp only [twFreeRep, map_add, FreeAlgebra.lift_ι_apply, twGenOp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp [add_mul]
  | poly_mul f g =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp
  | poly_C c =>
    simp only [twFreeRep, AlgHom.commutes, FreeAlgebra.lift_ι_apply, twGenOp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp [Module.algebraMap_end_apply, C_mul']
  | poly_idem f C =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp, LinearMap.comp_id, LinearMap.id_comp]
  | step_idem C C' =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, LinearMap.comp_id, LinearMap.id_comp]
  | step_zero C C' hC =>
    simp only [twFreeRep, FreeAlgebra.lift_ι_apply, twGenOp, twStepOp_of_not hC, blk_zero, map_zero]
  | relabel_idem g C =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, LinearMap.comp_id, LinearMap.id_comp]
  | relabel_one C =>
    simp only [twFreeRep, FreeAlgebra.lift_ι_apply, twGenOp, one_smul, ren_one]
  | relabel_mul g h C =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, mul_smul]
    congr 1
    exact LinearMap.ext fun f => (ren_mul_apply g h f).symm
  | relabel_poly g C f =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp]
    congr 1
    refine LinearMap.ext fun p => ?_
    simp [ren, map_mul]
  | relabel_step g C C' =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, ren_comp_twStepOp]
  | wall_bigon C C' w h =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, diagOp_comp_blk, LinearMap.comp_id, twStepOp_comp_twStepOp_inl h]
  | diag_bigon C C' d h =>
    rcases hl : Γ.loop d.fst.1 with _ | P
    · simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
        blk_comp_blk, map_zero]
      convert blk_zero (k := k) C C
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, twStepOp_twStepOp_inr hΓ h f, hl, LinearMap.zero_apply]
    · simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
        blk_comp_blk, diagOp_comp_blk, h.symm.refl_smul]
      congr 1
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, twStepOp_twStepOp_inr hΓ h f, hl, LinearMap.mulLeft_apply]
      rfl
  | wall_poly C C' w h f =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp, twStepOp_inl h, wallOp_eq_mulLeft]
    congr 1
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    ring
  | diag_poly C C' d h f =>
    simp only [twFreeRep, map_mul, map_sub, FreeAlgebra.lift_ι_apply, twGenOp,
      Module.End.mul_eq_comp, diagOp_comp_blk, blk_comp_diagOp, h.refl_smul, ← blk_sub]
    congr 1
    refine LinearMap.ext fun g => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    exact twStepOp_mul_inr h f g
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      blk_comp_blk, twStepOp_square hne hi a₁ a₂ a₃ a₄]
  | hex_walls H e₁ e₂ e₃ =>
    rw [twFreeRep_gal₁, twFreeRep_gal₂, H.twStepOp_gal₁, H.twStepOp_gal₂, hypOp_walls e₁ e₂ e₃]
  | hex_mid_diag H w d h₁ h₂ h₃ hσ hA =>
    have e₁ : H.A₁.1 H.h₂ = H.A₀.1 H.h₂ := (H.adj₀₁.2 _ H.ne₁₂.symm).symm
    rw [h₂] at e₁
    have hl : d.twLeft H.A₁ = d.twLeft H.A₀ := by unfold Diag.twLeft; rw [e₁]
    have hr : d.twRight H.A₁ = d.twRight H.A₀ := by unfold Diag.twRight; rw [e₁]
    rw [map_sub, twFreeRep_gal₁, twFreeRep_gal₂, H.twStepOp_gal₁, H.twStepOp_gal₂, ← blk_sub, h₁, h₂,
      h₃, twHypOp_inr_left, hl, hr]
    simp only [twFreeRep, map_mul, FreeAlgebra.lift_ι_apply, twGenOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, hA]
    congr 1
    exact hypOp_mid_diag w d (Diag.twLeft_ne_twRight _ d) (Diag.swap_twLeft_twRight _ d) hσ
  | hex_end_diag H w d h₂ hd hσ =>
    rw [twFreeRep_gal₁, twFreeRep_gal₂, H.twStepOp_gal₁, H.twStepOp_gal₂]
    congr 1
    rcases hd with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
    · rw [h₁, h₂, h₃, twHypOp_inr_left, ← hσ]
      exact hypOp_end_diag w d (Diag.twLeft_ne_twRight _ d) (Diag.swap_twLeft_twRight _ d) _
    · rw [h₁, h₂, h₃, twHypOp_inr_left, ← hσ]
      exact (hypOp_end_diag w d (Diag.twLeft_ne_twRight _ d) (Diag.swap_twLeft_twRight _ d) _).symm
  | hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA =>
    have huv := j₁.ne
    have huw := j₂.ne
    have hvw := j₃.ne
    have hc₁ := j₁.label_eq
    have hc₂ := j₂.label_eq
    rw [map_sub, twFreeRep_gal₁, twFreeRep_gal₂, H.twStepOp_gal₁, H.twStepOp_gal₂, ← blk_sub, h₁, h₂,
      h₃, twHypOp_inr_left, twHypOp_inr_left, twHypOp_inr_left]
    rcases hl : Γ.loop u.1 with _ | P
    · simp only [map_zero]
      rw [psiOp_braid_of_none huv huw hvw hc₁ hc₂ hl (j₁.twLeft_twRight _) (j₂.twLeft_twRight _)
        (j₃.twLeft_twRight _), sub_self, blk_zero]
    · have hP := hΓ u.1 P hl
      have a₁ : H.A₀.Adjacent H.A₁ (.inr d₁) := h₁ ▸ H.adj₀₁
      have a₅ : H.A₀.Adjacent H.A₅ (.inr d₃) := h₃ ▸ H.adj₀₅
      have g₁ : (d₂.refl * d₁.refl) • H.A₁ = H.A₃ := by
        rw [← a₁.refl_smul, ← mul_smul, mul_assoc, Diag.refl_mul_refl, mul_one, hA]
      have g₂ : (d₂.refl * d₃.refl) • H.A₅ = H.A₃ := by
        rw [← a₅.refl_smul, ← mul_smul, mul_assoc, Diag.refl_mul_refl, mul_one, hA]
      simp only [TwHexagon.loopCorrection, twFreeRep, map_add, map_mul, FreeAlgebra.lift_ι_apply,
        twGenOp, Module.End.mul_eq_comp, blk_comp_blk, diagOp_comp_blk, g₁, g₂, ← blk_add,
        twStepOp_inr a₁, twStepOp_inr a₅]
      congr 1
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, ren_mul_apply]
      have r₁ : ∀ p, ren (k := k) d₁.refl p = rename (swap u v) p := fun p => by
        rw [← j₁.swap_eq]; rfl
      have r₂ : ∀ p, ren (k := k) d₂.refl p = rename (swap u w) p := fun p => by
        rw [← j₂.swap_eq]; rfl
      have r₃ : ∀ p, ren (k := k) d₃.refl p = rename (swap v w) p := fun p => by
        rw [← j₃.swap_eq]; rfl
      rw [r₁, r₂, r₂, r₃]
      exact psiOp_braid_of_some hP huv huw hvw hc₁ hc₂ hl (j₁.twLeft_twRight _) (j₂.twLeft_twRight _)
        (j₃.twLeft_twRight _) f

variable (k) in
/-- The polynomial representation of the twisted gallery algebra: B. Webster,
arXiv:1209.2463v4, §2.5, Proposition 2.20, first assertion (a polynomial ring for each pair of a
loading and a weighting, read here as one for each chamber of the arrangement of positions and
weights, with the action of Proposition `prop:action`), for labelled strands and symmetric
loop polynomials, the hypothesis of `galleryRep`. -/
noncomputable def twGalleryRep (hΓ : Γ.PSymm) :
    TwGalleryAlgebra k Γ ν →ₐ[k] Module.End k (TwChamber Γ ν → PolyRing ν k) :=
  RingQuot.liftAlgHom k ⟨twFreeRep k Γ ν, fun _ _ h => twFreeRep_rel hΓ h⟩

theorem twGalleryRep_mk (hΓ : Γ.PSymm) (x : FreeAlgebra k (TwGen k Γ ν)) :
    twGalleryRep k hΓ (TwGalleryAlgebra.mk k Γ ν x) = twFreeRep k Γ ν x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

/-! ### Comparison with a fixed weighting -/

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hypOp_withWeight (ϑ : Γ.E → 𝕜) (h : Hyp Γ ν) (σ σ' : Bool) :
    hypOp (k := k) (Γ.withWeight ϑ) h σ σ' = hypOp Γ h σ σ' := by
  rcases h with w | d <;> rfl

omit [IsStrictOrderedRing 𝕜] in
/-- On the chambers of the fibre over a weighting `ϑ`, the steps of the twisted representation
are those of the polynomial representation of the gallery algebra of `ϑ`: the representation of
`P` restricts on each weighting to that of Proposition `prop:action`. -/
theorem twStepOp_toTw {ϑ : Γ.E → 𝕜} (C C' : FullChamber (Γ.withWeight ϑ) ν) :
    twStepOp (k := k) Γ C.toTw C'.toTw = stepOp (Γ.withWeight ϑ) C C' := by
  by_cases hC : ∃ h : Hyp Γ ν, C.Adjacent C' h
  · obtain ⟨h, hh⟩ := hC
    exact (twStepOp_eq (Γ := Γ) (FullChamber.adjacent_toTw_iff.2 hh)).trans
      ((hypOp_withWeight ϑ h _ _).symm.trans (stepOp_eq hh).symm)
  · have hC' : ∀ h : Hyp Γ ν, ¬C.toTw.Adjacent C'.toTw h := fun h hh => hC ⟨h, hh⟩
    exact (twStepOp_of_not (Γ := Γ) hC').trans
      (stepOp_of_not (Γ := Γ.withWeight ϑ) (C := C) (C' := C') fun h hh => hC ⟨h, hh⟩).symm

end Categorification.WeightedKLR
