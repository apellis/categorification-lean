/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Gallery
import Categorification.WeightedKLR.GalleryRep

/-!
# The vertical reflection of the gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Definition 2.4.

Turning a weighted KLR diagram upside down reverses the order of multiplication. On galleries it
reverses each step, `t C C' ↦ t C' C`, fixes idempotents and polynomials, and inverts each
relabelling, `r g C ↦ r g⁻¹ (g • C)`. When every loop polynomial is symmetric (`Γ.PSymm`) the
defining relations of Webster's Definition 2.4 are invariant under this reflection, so it is an
anti-involution of the gallery algebra. It exchanges left and right modules; it is used to obtain
the left-handed form of the parabolic decomposition from the right-handed one (restriction of
projective modules, towards Webster's Theorem 2.19).

## Main definitions

* `Hexagon.reverse`: a hexagon read from its last chamber.
* `GalleryAlgebra.reflect hΓ`: the vertical reflection, an anti-homomorphism.
* `GalleryAlgebra.reflectEquiv hΓ`: the reflection as an algebra isomorphism with the opposite
  algebra.

## Main results

* `GalleryAlgebra.reflect_mul`, `GalleryAlgebra.reflect_reflect`: the reflection reverses
  products and is an involution.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv MulOpposite

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-! ### Auxiliary identities -/

section Aux

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A diagonal step operator vanishes on polynomials symmetric in its two strands. -/
theorem stepFactor_eq_zero_of_rename_eq {l r : Strand ν} (hlr : l ≠ r) {f : PolyRing ν k}
    (hf : rename (swap l r) f = f) : stepFactor Γ l r f = 0 := by
  rcases h : Γ.loop l.1 with _ | P
  · simp only [stepFactor, h, ddiff_eq_zero_of_rename_eq hlr hf]
  · simp only [stepFactor, h, hf, sub_self, mul_zero]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Exchanging the two strands of a diagonal step operator. -/
theorem rename_swap_stepFactor {l r : Strand ν} (hlr : l ≠ r) (hc : l.1 = r.1)
    (f : PolyRing ν k) :
    rename (swap l r) (stepFactor Γ l r f) = -stepFactor Γ r l f := by
  rcases h : Γ.loop l.1 with _ | P
  · have h' : Γ.loop r.1 = none := hc ▸ h
    simp only [stepFactor, h, h', rename_swap_ddiff hlr, ddiff_comm hlr, neg_neg]
  · have h' : Γ.loop r.1 = some P := hc ▸ h
    simp only [stepFactor, h, h', map_mul, map_sub, loopFactor_rename, swap_apply_left,
      swap_apply_right, rename_swap_rename_swap, swap_comm r l]
    ring

omit [IsStrictOrderedRing 𝕜] in
theorem Diag.refl_inv (d : Diag ν) : d.refl⁻¹ = d.refl :=
  inv_eq_of_mul_eq_one_right (Diag.refl_mul_refl d)

theorem Diag.refl_smul_symm {d : Diag ν} {C C' : FullChamber Γ ν} (h : d.refl • C = C') :
    d.refl • C' = C := by
  rw [← h, smul_smul, Diag.refl_mul_refl, one_smul]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.symm {d : Diag ν} {a b : Strand ν} (h : d.Joins a b) : d.Joins b a :=
  Or.symm h

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.comap_refl_comap_refl (w : Wall Γ ν) (d : Diag ν) :
    (w.comap d.refl).comap d.refl = w := by
  have h := Hyp.comap_mul (Γ := Γ) d.refl d.refl (.inl w)
  rw [Diag.refl_mul_refl, Hyp.comap_one] at h
  exact (Sum.inl.inj h).symm

theorem swap_mul_swap_of_three {u v w : Strand ν} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    swap u v * swap u w = swap u w * swap v w := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_def]
  split_ifs <;> simp_all

end Aux

/-! ### Reversed hexagons -/

/-- A hexagon read from its last chamber: the two galleries are reversed. -/
@[simps]
def Hexagon.reverse (H : Hexagon Γ ν) : Hexagon Γ ν where
  A₀ := H.A₃
  A₁ := H.A₂
  A₂ := H.A₁
  A₃ := H.A₀
  A₄ := H.A₅
  A₅ := H.A₄
  h₁ := H.h₃
  h₂ := H.h₂
  h₃ := H.h₁
  ne₁₂ := H.ne₂₃.symm
  ne₁₃ := H.ne₁₃.symm
  ne₂₃ := H.ne₁₂.symm
  adj₀₁ := H.adj₂₃.symm
  adj₁₂ := H.adj₁₂.symm
  adj₂₃ := H.adj₀₁.symm
  adj₀₅ := H.adj₄₃.symm
  adj₅₄ := H.adj₅₄.symm
  adj₄₃ := H.adj₀₅.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Hexagon.A₃_apply_h₁ (H : Hexagon Γ ν) : H.A₃.1 H.h₁ = !H.A₀.1 H.h₁ := by
  rw [← H.adj₂₃.2 _ H.ne₁₃, ← H.adj₁₂.2 _ H.ne₁₂, H.adj₀₁.apply_eq_not]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Hexagon.A₃_apply_h₂ (H : Hexagon Γ ν) : H.A₃.1 H.h₂ = !H.A₀.1 H.h₂ := by
  rw [← H.adj₂₃.2 _ H.ne₂₃, H.adj₁₂.apply_eq_not, ← H.adj₀₁.2 _ H.ne₁₂.symm]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Hexagon.A₃_apply_h₃ (H : Hexagon Γ ν) : H.A₃.1 H.h₃ = !H.A₀.1 H.h₃ := by
  rw [H.adj₂₃.apply_eq_not, ← H.adj₁₂.2 _ H.ne₂₃.symm, ← H.adj₀₁.2 _ H.ne₁₃.symm]

namespace GalleryAlgebra

open FullChamber

/-! ### The reflection on generators -/

section Free

theorem poly_zero : (poly 0 : GalleryAlgebra k Γ ν) = 0 := map_zero (polyHom k Γ ν)

theorem poly_neg (f : PolyRing ν k) : (poly (-f) : GalleryAlgebra k Γ ν) = -poly f :=
  map_neg (polyHom k Γ ν) f

variable (k Γ ν) in
/-- The reflection of a generator, in the opposite algebra. -/
noncomputable def reflectGen : Gen k Γ ν → (GalleryAlgebra k Γ ν)ᵐᵒᵖ
  | .idem C => op (e C)
  | .poly f => op (poly f)
  | .step C C' => op (t C' C)
  | .relabel g C => op (r g⁻¹ (g • C))

variable (k Γ ν) in
/-- The reflection on the free algebra. -/
noncomputable def freeReflect : FreeAlgebra k (Gen k Γ ν) →ₐ[k] (GalleryAlgebra k Γ ν)ᵐᵒᵖ :=
  FreeAlgebra.lift k (reflectGen k Γ ν)

@[simp] theorem unop_freeReflect_fe (C : FullChamber Γ ν) :
    unop (freeReflect k Γ ν (fe k Γ ν C)) = e C := by
  simp [freeReflect, reflectGen]

@[simp] theorem unop_freeReflect_fp (f : PolyRing ν k) :
    unop (freeReflect k Γ ν (fp k Γ ν f)) = poly f := by
  simp [freeReflect, reflectGen]

@[simp] theorem unop_freeReflect_ft (C C' : FullChamber Γ ν) :
    unop (freeReflect k Γ ν (ft k Γ ν C C')) = t C' C := by
  simp [freeReflect, reflectGen]

@[simp] theorem unop_freeReflect_fr (g : ColPerm ν) (C : FullChamber Γ ν) :
    unop (freeReflect k Γ ν (fr k Γ ν g C)) = r g⁻¹ (g • C) := by
  simp [freeReflect, reflectGen]

theorem unop_freeReflect_gal₁ (H : Hexagon Γ ν) :
    unop (freeReflect k Γ ν (H.gal₁ k Γ ν)) = mk k Γ ν (H.reverse.gal₁ k Γ ν) := by
  simp only [Hexagon.gal₁, map_mul, unop_mul, unop_freeReflect_ft, mk_ft,
    Hexagon.reverse_A₀, Hexagon.reverse_A₁, Hexagon.reverse_A₂, Hexagon.reverse_A₃, mul_assoc]

theorem unop_freeReflect_gal₂ (H : Hexagon Γ ν) :
    unop (freeReflect k Γ ν (H.gal₂ k Γ ν)) = mk k Γ ν (H.reverse.gal₂ k Γ ν) := by
  simp only [Hexagon.gal₂, map_mul, unop_mul, unop_freeReflect_ft, mk_ft,
    Hexagon.reverse_A₀, Hexagon.reverse_A₃, Hexagon.reverse_A₄, Hexagon.reverse_A₅, mul_assoc]

theorem unop_freeReflect_gal_sub (H : Hexagon Γ ν) :
    unop (freeReflect k Γ ν (H.gal₁ k Γ ν - H.gal₂ k Γ ν)) =
      mk k Γ ν (H.reverse.gal₁ k Γ ν - H.reverse.gal₂ k Γ ν) := by
  rw [map_sub, unop_sub, unop_freeReflect_gal₁, unop_freeReflect_gal₂, map_sub]

end Free

/-! ### The relations are invariant -/

section Relations

/-- The diagonal bigon relation is invariant under the reflection. -/
theorem freeReflect_diag_bigon (hΓ : Γ.PSymm) {C C' : FullChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) :
    unop (freeReflect k Γ ν (ft k Γ ν C' C * ft k Γ ν C C')) =
      unop (freeReflect k Γ ν (match Γ.loop d.fst.1 with
        | none => 0
        | some P => fp k Γ ν (-2 * loopFactor P (d.left C) (d.right C)) *
            fr k Γ ν d.refl C' * ft k Γ ν C C')) := by
  have hb := rel (Rel.diag_bigon (k := k) C C' d h)
  simp only [map_mul, unop_mul, unop_freeReflect_ft, mk_ft] at hb ⊢
  rcases hl : Γ.loop d.fst.1 with _ | P <;> simp only [hl, map_zero, map_mul, mk_fp, mk_fr,
    mk_ft, unop_zero, unop_mul, unop_freeReflect_fp, unop_freeReflect_fr,
    unop_freeReflect_ft] at hb ⊢
  · exact hb
  · have hP := hΓ _ P hl
    have hsw : ((d.refl : ColPerm ν) : Perm (Strand ν)) = swap (d.left C) (d.right C) :=
      (Diag.swap_left_right C d).symm
    have hX : rename (d.refl : ColPerm ν).1 (-2 * loopFactor P (d.left C) (d.right C)) =
        -2 * loopFactor P (d.left C) (d.right C) := by
      rw [hsw, map_mul, rename_swap_loopFactor hP]
      simp [map_ofNat]
    have hSF : stepFactor Γ (d.left C') (d.right C')
        (-2 * loopFactor P (d.left C) (d.right C)) = 0 := by
      rw [Diag.left_of_adjacent h, Diag.right_of_adjacent h]
      apply stepFactor_eq_zero_of_rename_eq (Diag.left_ne_right C d).symm
      rw [swap_comm, ← hsw, hX]
    have hrt : (r d.refl C' * t C C' : GalleryAlgebra k Γ ν) = t C' C * r d.refl C := by
      rw [r_mul_t, h.refl_smul, h.symm.refl_smul]
    rw [hb, h.symm.refl_smul, Diag.refl_inv, r_mul_poly, hX, ← mul_assoc,
      t_mul_poly_inr h.symm, hSF, poly_zero, zero_mul, add_zero, mul_assoc, hrt, mul_assoc]

/-- The relation of a hexagon with a diagonal crossed in the middle is invariant under the
reflection. -/
theorem freeReflect_hex_mid_diag (H : Hexagon Γ ν) (w : Wall Γ ν) (d : Diag ν)
    (e₁ : H.h₁ = .inl w) (e₂ : H.h₂ = .inr d) (e₃ : H.h₃ = .inl (w.comap d.refl))
    (hσ : H.A₀.1 (.inl w) ≠ H.A₀.1 (.inl (w.comap d.refl))) (hA : d.refl • H.A₀ = H.A₃) :
    unop (freeReflect k Γ ν (H.gal₁ k Γ ν - H.gal₂ k Γ ν)) =
      unop (freeReflect k Γ ν
        (fp k Γ ν (stepFactor Γ (d.left H.A₁) (d.right H.A₁) w.factor) *
          fr k Γ ν d.refl H.A₀)) := by
  have s1 : H.A₃.1 (.inl w) = !H.A₀.1 (.inl w) := by rw [← e₁]; exact H.A₃_apply_h₁
  have s3 : H.A₃.1 (.inl (w.comap d.refl)) = !H.A₀.1 (.inl (w.comap d.refl)) := by
    rw [← e₃]; exact H.A₃_apply_h₃
  have hσ' : H.reverse.A₀.1 (.inl (w.comap d.refl)) ≠
      H.reverse.A₀.1 (.inl ((w.comap d.refl).comap d.refl)) := by
    rw [Hexagon.reverse_A₀, Wall.comap_refl_comap_refl, s1, s3]
    exact fun h => hσ (Bool.not_inj h).symm
  have e₁' : H.reverse.h₃ = .inl ((w.comap d.refl).comap d.refl) := by
    rw [Wall.comap_refl_comap_refl]; exact e₁
  have key := rel (Rel.hex_mid_diag (k := k) H.reverse (w.comap d.refl) d e₃ e₂ e₁' hσ'
    (Diag.refl_smul_symm hA))
  have a₁₂ : H.A₁.Adjacent H.A₂ (.inr d) := by rw [← e₂]; exact H.adj₁₂
  have hL : stepFactor Γ (d.left H.A₂) (d.right H.A₂) (w.comap d.refl).factor =
      -stepFactor Γ (d.right H.A₁) (d.left H.A₁) w.factor := by
    rw [Diag.left_of_adjacent a₁₂, Diag.right_of_adjacent a₁₂, Wall.factor_comap_refl,
      ← Diag.swap_left_right H.A₁ d, swap_comm,
      stepFactor_rename_swap (Diag.left_ne_right H.A₁ d).symm]
  have hR : rename (d.refl : ColPerm ν).1 (stepFactor Γ (d.left H.A₁) (d.right H.A₁) w.factor) =
      -stepFactor Γ (d.right H.A₁) (d.left H.A₁) w.factor := by
    rw [show ((d.refl : ColPerm ν) : Perm (Strand ν)) = swap (d.left H.A₁) (d.right H.A₁) from
      (Diag.swap_left_right H.A₁ d).symm,
      rename_swap_stepFactor (Diag.left_ne_right H.A₁ d)
        ((Diag.left_label H.A₁ d).trans (Diag.right_label H.A₁ d).symm)]
  rw [unop_freeReflect_gal_sub, key]
  simp only [map_mul, unop_mul, mk_fp, mk_fr, unop_freeReflect_fp, unop_freeReflect_fr,
    Hexagon.reverse_A₀, Hexagon.reverse_A₁]
  rw [hA, Diag.refl_inv, r_mul_poly, hL, hR]

/-- The braid relation of three diagonals is invariant under the reflection. -/
theorem freeReflect_hex_diags (hΓ : Γ.PSymm) (H : Hexagon Γ ν) (d₁ d₂ d₃ : Diag ν)
    (u v w : Strand ν) (e₁ : H.h₁ = .inr d₁) (e₂ : H.h₂ = .inr d₂) (e₃ : H.h₃ = .inr d₃)
    (j₁ : d₁.Joins u v) (j₂ : d₂.Joins u w) (j₃ : d₃.Joins v w)
    (hA : d₂.refl • H.A₀ = H.A₃) :
    unop (freeReflect k Γ ν (H.gal₁ k Γ ν - H.gal₂ k Γ ν)) =
      unop (freeReflect k Γ ν (match Γ.loop u.1 with
        | none => 0
        | some P => H.loopCorrection k Γ ν d₁ d₂ d₃ u v w P)) := by
  have key := rel (Rel.hex_diags (k := k) H.reverse d₃ d₂ d₁ w v u e₃ e₂ e₁ j₃.symm j₂.symm
    j₁.symm (Diag.refl_smul_symm hA))
  rw [unop_freeReflect_gal_sub, key]
  have hwu : Γ.loop w.1 = Γ.loop u.1 := by rw [j₂.label_eq]
  rcases hl : Γ.loop u.1 with _ | P
  · simp only [hwu, hl, map_zero, unop_zero]
  have hP := hΓ _ P hl
  simp only [hwu, hl, Hexagon.loopCorrection, map_add, map_mul, unop_add, unop_mul, mk_fp,
    mk_fr, mk_ft, unop_freeReflect_fp, unop_freeReflect_fr, unop_freeReflect_ft,
    Hexagon.reverse_A₀, Hexagon.reverse_A₁, Hexagon.reverse_A₅]
  have huv := j₁.ne
  have huw := j₂.ne
  have hvw := j₃.ne
  -- the chambers of the hexagon
  have a₀₁ : H.A₀.Adjacent H.A₁ (.inr d₁) := by rw [← e₁]; exact H.adj₀₁
  have a₁₂ : H.A₁.Adjacent H.A₂ (.inr d₂) := by rw [← e₂]; exact H.adj₁₂
  have a₂₃ : H.A₂.Adjacent H.A₃ (.inr d₃) := by rw [← e₃]; exact H.adj₂₃
  have a₀₅ : H.A₀.Adjacent H.A₅ (.inr d₃) := by rw [← e₃]; exact H.adj₀₅
  have a₅₄ : H.A₅.Adjacent H.A₄ (.inr d₂) := by rw [← e₂]; exact H.adj₅₄
  have a₄₃ : H.A₄.Adjacent H.A₃ (.inr d₁) := by rw [← e₁]; exact H.adj₄₃
  have r₁ := a₀₁.refl_smul
  have r₂ := a₁₂.refl_smul
  have r₃ := a₂₃.refl_smul
  have r₅ := a₀₅.refl_smul
  have r₄ := a₅₄.refl_smul
  have r₆ := a₄₃.refl_smul
  -- the permutations
  have c₁ : ((d₁.refl : ColPerm ν) : Perm (Strand ν)) = swap u v := j₁.swap_eq
  have c₂ : ((d₂.refl : ColPerm ν) : Perm (Strand ν)) = swap u w := j₂.swap_eq
  have c₃ : ((d₃.refl : ColPerm ν) : Perm (Strand ν)) = swap v w := j₃.swap_eq
  have hinv : (d₂.refl * d₁.refl)⁻¹ = d₂.refl * d₃.refl := by
    apply Subtype.ext
    rw [InvMemClass.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, c₁, c₂, c₃, mul_inv_rev,
      swap_inv, swap_inv, swap_mul_swap_of_three huv huw hvw]
  have hinv' : (d₂.refl * d₃.refl)⁻¹ = d₂.refl * d₁.refl := by rw [← hinv, inv_inv]
  have g₁A₁ : (d₂.refl * d₁.refl) • H.A₁ = H.A₃ := by
    rw [mul_smul, Diag.refl_smul_symm r₁, hA]
  have g₃A₅ : (d₂.refl * d₃.refl) • H.A₅ = H.A₃ := by
    rw [mul_smul, Diag.refl_smul_symm r₅, hA]
  have tA : (t H.A₁ H.A₀ * r (d₂.refl * d₃.refl) H.A₃ : GalleryAlgebra k Γ ν) =
      r (d₂.refl * d₃.refl) H.A₂ * t H.A₃ H.A₂ := by
    have := t_mul_r_eq (k := k) (d₂.refl * d₃.refl) H.A₃ H.A₀
    rwa [mul_smul, Diag.refl_smul_symm r₃, Diag.refl_smul_symm r₂, hinv', mul_smul, r₁, r₂]
      at this
  have tB : (t H.A₅ H.A₀ * r (d₂.refl * d₁.refl) H.A₃ : GalleryAlgebra k Γ ν) =
      r (d₂.refl * d₁.refl) H.A₄ * t H.A₃ H.A₄ := by
    have := t_mul_r_eq (k := k) (d₂.refl * d₁.refl) H.A₃ H.A₀
    rwa [mul_smul, Diag.refl_smul_symm r₆, Diag.refl_smul_symm r₄, hinv, mul_smul, r₅, r₄]
      at this
  -- the polynomials
  set Puv := loopFactor (ν := ν) P u v
  set Puw := loopFactor (ν := ν) P u w
  set Pvw := loopFactor (ν := ν) P v w
  have n₁ := loopFactor_comm (ν := ν) hP w v
  have n₂ := loopFactor_comm (ν := ν) hP w u
  have n₃ := loopFactor_comm (ν := ν) hP v u
  have hα : rename (swap v w) (-(Puv * Puw - Pvw * Puw - Pvw * Puv)) =
      -(Puv * Puw - Pvw * Puw - Pvw * Puv) := by
    simp only [Puv, Puw, Pvw, map_neg, map_sub, map_mul, loopFactor_rename, swap_apply_left,
      swap_apply_right, swap_apply_of_ne_of_ne huv huw, n₁]
    ring
  have hβ : rename (swap u v) (-(Puv * Puw + Puv * Pvw - Puw * Pvw)) =
      -(Puv * Puw + Puv * Pvw - Puw * Pvw) := by
    simp only [Puv, Puw, Pvw, map_neg, map_add, map_sub, map_mul, loopFactor_rename,
      swap_apply_left, swap_apply_right, swap_apply_of_ne_of_ne huw.symm hvw.symm,
      n₃]
    ring
  have hSFα : stepFactor Γ (d₃.left H.A₃) (d₃.right H.A₃)
      (-(Puv * Puw - Pvw * Puw - Pvw * Puv)) = 0 :=
    stepFactor_eq_zero_of_rename_eq (Diag.left_ne_right _ _)
      (by rw [Diag.swap_left_right, j₃.swap_eq, hα])
  have hSFβ : stepFactor Γ (d₁.left H.A₃) (d₁.right H.A₃)
      (-(Puv * Puw + Puv * Pvw - Puw * Pvw)) = 0 :=
    stepFactor_eq_zero_of_rename_eq (Diag.left_ne_right _ _)
      (by rw [Diag.swap_left_right, j₁.swap_eq, hβ])
  have hrα : rename ((d₂.refl * d₃.refl : ColPerm ν) : Perm (Strand ν))
      (-(Puv * Puw - Pvw * Puw - Pvw * Puv)) =
      -(loopFactor P w v * loopFactor P w u - loopFactor P v u * loopFactor P w u -
        loopFactor P v u * loopFactor P w v) := by
    rw [Subgroup.coe_mul, c₂, c₃]
    simp only [Puv, Puw, Pvw, map_neg, map_sub, map_mul, loopFactor_rename, Perm.coe_mul,
      Function.comp_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne huv huw]
    simp only [swap_apply_def u w v, huv.symm, hvw, ite_false, n₁, n₂, n₃]
    ring
  have hrβ : rename ((d₂.refl * d₁.refl : ColPerm ν) : Perm (Strand ν))
      (-(Puv * Puw + Puv * Pvw - Puw * Pvw)) =
      -(loopFactor P w v * loopFactor P w u + loopFactor P w v * loopFactor P v u -
        loopFactor P w u * loopFactor P v u) := by
    rw [Subgroup.coe_mul, c₁, c₂]
    simp only [Puv, Puw, Pvw, map_neg, map_add, map_sub, map_mul, loopFactor_rename,
      Perm.coe_mul, Function.comp_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne huw.symm hvw.symm]
    simp only [swap_apply_def u w v, huv.symm, hvw, ite_false, n₁, n₂, n₃]
    ring
  have a₃₂ := a₂₃.symm
  have a₃₄ := a₄₃.symm
  rw [hinv, g₁A₁, hinv', g₃A₅, ← mul_assoc, tA, ← mul_assoc, tB,
    mul_assoc (r (d₂.refl * d₃.refl) H.A₂), mul_assoc (r (d₂.refl * d₁.refl) H.A₄),
    t_mul_poly_inr a₃₂, t_mul_poly_inr a₃₄, hSFα, hSFβ, poly_zero, zero_mul, zero_mul, add_zero,
    add_zero, ← mul_assoc, ← mul_assoc, r_mul_poly, r_mul_poly, hrα, hrβ]

/-- The reflection respects the defining relations. -/
theorem freeReflect_rel (hΓ : Γ.PSymm) {a b : FreeAlgebra k (Gen k Γ ν)} (h : Rel k Γ ν a b) :
    freeReflect k Γ ν a = freeReflect k Γ ν b := by
  apply unop_injective
  cases h with
  | idem_mul C D =>
    split_ifs with hCD
    · subst hCD
      simp [e_mul_e]
    · simp [e_mul_e, Ne.symm hCD]
  | idem_sum => simp [Finset.unop_sum, sum_e]
  | poly_add f g => simpa using map_add (polyHom k Γ ν) f g
  | poly_mul f g =>
    simp only [map_mul, unop_mul, unop_freeReflect_fp]
    rw [poly_mul_poly, mul_comm]
  | poly_C c =>
    simp only [unop_freeReflect_fp, AlgHom.commutes, MulOpposite.algebraMap_apply, unop_op]
    have := (polyHom k Γ ν).commutes c
    rwa [MvPolynomial.algebraMap_eq, polyHom_apply] at this
  | poly_idem f C =>
    simp only [map_mul, unop_mul, unop_freeReflect_fp, unop_freeReflect_fe]
    exact e_mul_poly C f
  | step_idem C C' =>
    simp only [map_mul, unop_mul, unop_freeReflect_ft, unop_freeReflect_fe]
    rw [← mul_assoc]
    exact t_eq C' C
  | step_zero C C' hC =>
    simp only [unop_freeReflect_ft, map_zero, unop_zero]
    exact t_eq_zero fun x hx => hC x hx.symm
  | relabel_idem g C =>
    simp only [map_mul, unop_mul, unop_freeReflect_fr, unop_freeReflect_fe]
    rw [← mul_assoc]
    have := r_eq (k := k) g⁻¹ (g • C)
    rwa [inv_smul_smul] at this
  | relabel_one C => simp [r_one]
  | relabel_mul g h C =>
    simp only [map_mul, unop_mul, unop_freeReflect_fr]
    rw [mul_inv_rev, mul_smul, ← r_mul_r, inv_smul_smul]
  | relabel_poly g C f =>
    simp only [map_mul, unop_mul, unop_freeReflect_fr, unop_freeReflect_fp]
    have hg : (⇑((g⁻¹ : ColPerm ν) : Perm (Strand ν)) ∘ ⇑(g : Perm (Strand ν))) = id := by
      funext s
      simp
    rw [r_mul_poly, rename_rename, hg, rename_id_apply]
  | relabel_step g C C' =>
    simp only [map_mul, unop_mul, unop_freeReflect_fr, unop_freeReflect_ft]
    rw [r_mul_t, inv_smul_smul, inv_smul_smul]
  | wall_bigon C C' w h =>
    have hb := rel (Rel.wall_bigon (k := k) C C' w h)
    simp only [map_mul, mk_ft, mk_fp, mk_fe] at hb
    simp only [map_mul, unop_mul, unop_freeReflect_ft, unop_freeReflect_fp, unop_freeReflect_fe]
    rw [hb, e_mul_poly]
  | diag_bigon C C' d h => exact freeReflect_diag_bigon hΓ h
  | wall_poly C C' w h f =>
    simp only [map_mul, unop_mul, unop_freeReflect_ft, unop_freeReflect_fp]
    exact (t_mul_poly_inl h.symm f).symm
  | diag_poly C C' d h f =>
    simp only [map_mul, map_sub, unop_mul, unop_sub, unop_freeReflect_ft, unop_freeReflect_fp,
      unop_freeReflect_fr]
    have hs : ((d.refl : ColPerm ν) : Perm (Strand ν)) = swap (d.left C) (d.right C) :=
      (Diag.swap_left_right C d).symm
    rw [h.refl_smul, Diag.refl_inv, r_mul_poly, hs,
      rename_swap_stepFactor (Diag.left_ne_right C d)
        ((Diag.left_label C d).trans (Diag.right_label C d).symm),
      t_mul_poly_inr h.symm, Diag.left_of_adjacent h, Diag.right_of_adjacent h, poly_neg,
      neg_mul]
    abel
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    have hb := rel (Rel.square (k := k) D B B' C h₂ h₁ hne.symm
      (Or.imp And.symm (fun h => h.symm) hi) a₂.symm a₁.symm a₄.symm a₃.symm)
    simp only [map_mul, mk_ft] at hb
    simpa only [map_mul, unop_mul, unop_freeReflect_ft] using hb
  | hex_walls H e₁ e₂ e₃ =>
    rw [unop_freeReflect_gal₁, unop_freeReflect_gal₂]
    exact rel (Rel.hex_walls H.reverse e₃ e₂ e₁)
  | hex_mid_diag H w d e₁ e₂ e₃ hσ hA => exact freeReflect_hex_mid_diag H w d e₁ e₂ e₃ hσ hA
  | hex_end_diag H w d e₂ hd hσ =>
    have s2 : H.A₃.1 (.inl w) = !H.A₀.1 (.inl w) := by rw [← e₂]; exact H.A₃_apply_h₂
    have sc : H.A₃.1 (.inl (w.comap d.refl)) = !H.A₀.1 (.inl (w.comap d.refl)) := by
      rcases hd with ⟨-, e⟩ | ⟨e, -⟩
      · rw [← e]; exact H.A₃_apply_h₃
      · rw [← e]; exact H.A₃_apply_h₁
    have hσ' : H.reverse.A₀.1 (.inl w) = H.reverse.A₀.1 (.inl (w.comap d.refl)) := by
      rw [Hexagon.reverse_A₀, s2, sc, hσ]
    rw [unop_freeReflect_gal₁, unop_freeReflect_gal₂]
    exact rel (Rel.hex_end_diag H.reverse w d e₂ (hd.symm.imp And.symm And.symm) hσ')
  | hex_diags H d₁ d₂ d₃ u v w e₁ e₂ e₃ j₁ j₂ j₃ hA =>
    exact freeReflect_hex_diags hΓ H d₁ d₂ d₃ u v w e₁ e₂ e₃ j₁ j₂ j₃ hA

end Relations

/-! ### The reflection -/

variable (k) in
/-- The vertical reflection, as an algebra map to the opposite algebra. -/
noncomputable def reflectHom (hΓ : Γ.PSymm) :
    GalleryAlgebra k Γ ν →ₐ[k] (GalleryAlgebra k Γ ν)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨freeReflect k Γ ν, fun _ _ h => freeReflect_rel hΓ h⟩

variable (k) in
/-- The vertical reflection of the gallery algebra (diagrams turned upside down). -/
noncomputable def reflect (hΓ : Γ.PSymm) (x : GalleryAlgebra k Γ ν) : GalleryAlgebra k Γ ν :=
  unop (reflectHom k hΓ x)

theorem reflect_mk (hΓ : Γ.PSymm) (x : FreeAlgebra k (Gen k Γ ν)) :
    reflect k hΓ (mk k Γ ν x) = unop (freeReflect k Γ ν x) := by
  exact congrArg unop (RingQuot.liftAlgHom_mkAlgHom_apply k (freeReflect k Γ ν) _ x)

@[simp] theorem reflect_e (hΓ : Γ.PSymm) (C : FullChamber Γ ν) : reflect k hΓ (e C) = e C := by
  rw [e, reflect_mk, unop_freeReflect_fe]
  rfl

@[simp] theorem reflect_poly (hΓ : Γ.PSymm) (f : PolyRing ν k) :
    reflect k hΓ (poly f) = poly f := by
  rw [poly, reflect_mk, unop_freeReflect_fp]
  rfl

@[simp] theorem reflect_t (hΓ : Γ.PSymm) (C C' : FullChamber Γ ν) :
    reflect k hΓ (t C C') = t C' C := by
  rw [t, reflect_mk, unop_freeReflect_ft]

@[simp] theorem reflect_r (hΓ : Γ.PSymm) (g : ColPerm ν) (C : FullChamber Γ ν) :
    reflect k hΓ (r g C) = r g⁻¹ (g • C) := by
  rw [r, reflect_mk, unop_freeReflect_fr]

theorem reflect_mul (hΓ : Γ.PSymm) (x y : GalleryAlgebra k Γ ν) :
    reflect k hΓ (x * y) = reflect k hΓ y * reflect k hΓ x := by
  simp only [reflect, map_mul, unop_mul]

theorem reflect_add (hΓ : Γ.PSymm) (x y : GalleryAlgebra k Γ ν) :
    reflect k hΓ (x + y) = reflect k hΓ x + reflect k hΓ y := by
  simp only [reflect, map_add, unop_add]

theorem reflect_smul (hΓ : Γ.PSymm) (c : k) (x : GalleryAlgebra k Γ ν) :
    reflect k hΓ (c • x) = c • reflect k hΓ x := by
  simp only [reflect, map_smul, unop_smul]

@[simp] theorem reflect_one (hΓ : Γ.PSymm) : reflect k hΓ (1 : GalleryAlgebra k Γ ν) = 1 := by
  simp only [reflect, map_one, unop_one]

theorem reflect_reflect (hΓ : Γ.PSymm) (x : GalleryAlgebra k Γ ν) :
    reflect k hΓ (reflect k hΓ x) = x := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, reflect_smul, reflect_smul,
      reflect_one, reflect_one]
  | grade1 g =>
    cases g with
    | idem C =>
      show reflect k hΓ (reflect k hΓ (e C)) = e C
      rw [reflect_e, reflect_e]
    | poly f =>
      show reflect k hΓ (reflect k hΓ (poly f)) = poly f
      rw [reflect_poly, reflect_poly]
    | step C C' =>
      show reflect k hΓ (reflect k hΓ (t C C')) = t C C'
      rw [reflect_t, reflect_t]
    | relabel g C =>
      show reflect k hΓ (reflect k hΓ (r g C)) = r g C
      rw [reflect_r, reflect_r, inv_inv, inv_smul_smul]
  | mul a b ha hb => rw [map_mul, reflect_mul, reflect_mul, ha, hb]
  | add a b ha hb => rw [map_add, reflect_add, reflect_add, ha, hb]

variable (k) in
/-- The vertical reflection as an isomorphism with the opposite algebra. -/
noncomputable def reflectEquiv (hΓ : Γ.PSymm) :
    GalleryAlgebra k Γ ν ≃ₐ[k] (GalleryAlgebra k Γ ν)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reflectHom k hΓ)
    ((AlgEquiv.opOp k (GalleryAlgebra k Γ ν)).symm.toAlgHom.comp (AlgHom.op (reflectHom k hΓ)))
    (by
      ext x
      exact congrArg op (reflect_reflect hΓ (unop x)))
    (by
      ext x
      exact reflect_reflect hΓ x)

end GalleryAlgebra

end Categorification.WeightedKLR
