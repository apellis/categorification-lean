/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DividedPower

/-!
# The dot on `E E` is an isomorphism on the common summand `E^{(2)}⟨1⟩`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, proof of Lemma 3.6 (`lem:Xind`): "the fact that [the dot on the left strand]
`E E 1_n → E E 1_n ⟨2⟩` induces a map `E^{(2)} 1_n ⟨-1⟩ ⊕ E^{(2)} 1_n ⟨1⟩ → E^{(2)} 1_n ⟨1⟩ ⊕
E^{(2)} 1_n ⟨3⟩` which is an isomorphism on the common summand `E^{(2)} ⟨1⟩`. This is a consequence
of the NilHecke algebra action."

For a nilHecke datum `N` on `W` (`NH2`, with `e = r⁻¹ x_L τ`, `W ≅ im e ⊕ im (1 - e)` and
`im (1 - e) ≅ (im e)⟨-2⟩`, `DividedPower.lean`), the summand `E^{(2)}⟨1⟩` of `W` is `P = im e` and the
summand `E^{(2)}⟨1⟩` of `W⟨2⟩` is `(im (1 - e))⟨2⟩`; the claim is that the component
`P → (im (1 - e))⟨2⟩` of `x_L` is an isomorphism.

* `NH2.e_comp_xL_comp_one_sub_e`: `e x_L (1 - e) = h - 2 e x_R` in `NH₂` (from the two dot-slide
  relations and `e τ = 0`; no commutation of the two dots is needed);
* `NH2.exists_decomp_dot`: there is a splitting `W ≅ P ⊕ P⟨-2⟩` (`P = E^{(2)}⟨1⟩`) such that the
  component `P → P⟨-2⟩⟨2⟩` of `x_L` is an isomorphism (it is `r` times the component of
  `v = -r⁻¹ h`, whose inverse is the component of `τ`);
* `StrongSl2.exists_E2_dot`: the same for `E E 1_n` in a strong `sl₂` 2-representation, with the
  dot on the left strand `E 1_{n+2}` (Mathlib: `E r ◁ dot (r + 1)`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module

namespace NH2

variable {k : Type*} [Field k] {H : Type*} [Category H] [Preadditive H] [Linear k H]
  [HasShift H ℤ] [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k]
  {W : H} (N : NH2 (k := k) W)

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `x_R τ = τ x_L - r`. -/
theorem xR_comp_τ : N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) =
    N.τ.comp N.xL (by norm_num : (2 : ℤ) + -2 = 0) - (N.r : k) • one (W := W) := by
  rw [τ_comp_xL]; abel

omit [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `x_L τ - x_R τ = 2r - τ (x_L - x_R)`. -/
theorem xL_comp_τ_sub_xR_comp_τ :
    N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) - N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) =
      (2 * (N.r : k)) • one (W := W) -
        N.τ.comp (N.xL - N.xR) (by norm_num : (2 : ℤ) + -2 = 0) := by
  rw [xL_comp_τ, xR_comp_τ, ShiftedHom.comp_sub', two_mul, add_smul]; abel

/-- **`e x_L (1 - e) = h - 2 e x_R`** in `NH₂`. -/
theorem e_comp_xL_comp_one_sub_e :
    (N.e.comp N.xL (by norm_num : (2 : ℤ) + 0 = 2)).comp (one - N.e)
        (by norm_num : (0 : ℤ) + 2 = 2) =
      N.h - (2 : k) • N.e.comp N.xR (by norm_num : (2 : ℤ) + 0 = 2) := by
  have key : ∀ y : ShiftedHom W W (2 : ℤ),
      (N.e.comp y (by norm_num : (2 : ℤ) + 0 = 2)).comp (one - N.e)
        (by norm_num : (0 : ℤ) + 2 = 2) =
      -(((N.r⁻¹ : kˣ) : k) • N.e.comp ((y.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR
        (by norm_num : (2 : ℤ) + 0 = 2)) (by norm_num : (2 : ℤ) + 0 = 2)) := by
    intro y
    rw [one_sub_e, ShiftedHom.comp_neg, ShiftedHom.comp_smul',
      ShiftedHom.comp_assoc _ _ _ (by norm_num : (2 : ℤ) + 0 = 2) (by norm_num : (0 : ℤ) + 2 = 2)
        (by norm_num),
      ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0)
        (by norm_num : (2 : ℤ) + -2 = 0) (by norm_num)]
  have hh : N.h = -(((N.r⁻¹ : kˣ) : k) • N.e.comp ((N.xR.comp N.τ
      (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR (by norm_num : (2 : ℤ) + 0 = 2))
        (by norm_num : (2 : ℤ) + 0 = 2)) := key N.xR
  have h2 : N.e.comp ((N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR
        (by norm_num : (2 : ℤ) + 0 = 2)) (by norm_num : (2 : ℤ) + 0 = 2) -
      N.e.comp ((N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR
        (by norm_num : (2 : ℤ) + 0 = 2)) (by norm_num : (2 : ℤ) + 0 = 2) =
      (2 * (N.r : k)) • N.e.comp N.xR (by norm_num : (2 : ℤ) + 0 = 2) := by
    rw [← ShiftedHom.comp_sub', ← ShiftedHom.sub_comp', xL_comp_τ_sub_xR_comp_τ,
      ShiftedHom.sub_comp', ShiftedHom.smul_comp', one, ShiftedHom.mk₀_id_comp,
      ShiftedHom.comp_sub', ShiftedHom.comp_smul',
      ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (0 : ℤ) + 0 = 0) (by norm_num : (2 : ℤ) + 0 = 2)
        (by norm_num),
      ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 0 = -2)
        (by norm_num : (2 : ℤ) + -2 = 0) (by norm_num),
      e_comp_τ, ShiftedHom.zero_comp, ShiftedHom.zero_comp, sub_zero]
  have hA : N.e.comp ((N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR
        (by norm_num : (2 : ℤ) + 0 = 2)) (by norm_num : (2 : ℤ) + 0 = 2) =
      N.e.comp ((N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)).comp N.xR
        (by norm_num : (2 : ℤ) + 0 = 2)) (by norm_num : (2 : ℤ) + 0 = 2) +
      (2 * (N.r : k)) • N.e.comp N.xR (by norm_num : (2 : ℤ) + 0 = 2) := by
    rw [← h2]; abel
  rw [key N.xL, hh, hA, smul_add, smul_smul, ← mul_assoc, mul_right_comm, Units.inv_mul, one_mul,
    neg_add, sub_eq_add_neg]

variable [IsIdempotentComplete H]

include N in
/-- **The dot `x_L` is an isomorphism from `E^{(2)}⟨1⟩ ⊆ W` to `E^{(2)}⟨1⟩ ⊆ W⟨2⟩`**: there is a
splitting `W ≅ P ⊕ P⟨-2⟩` (retractions `i, p`, `i', p'`, with `P = im e`) such that the component
`i ≫ x_L ≫ p'⟨2⟩ : P → P⟨-2⟩⟨2⟩` of `x_L` is an isomorphism. -/
theorem exists_decomp_dot : ∃ (P : H) (i : P ⟶ W) (p : W ⟶ P) (i' : P⟦(-2 : ℤ)⟧ ⟶ W)
    (p' : W ⟶ P⟦(-2 : ℤ)⟧), i ≫ p = 𝟙 P ∧ i' ≫ p' = 𝟙 _ ∧ i ≫ p' = 0 ∧ i' ≫ p = 0 ∧
      p ≫ i + p' ≫ i' = 𝟙 W ∧ IsIso (i ≫ N.xL ≫ p'⟦(2 : ℤ)⟧') := by
  obtain ⟨P, i, p, hip, hpi⟩ := IsIdempotentComplete.idempotents_split W N.ebar N.ebar_idem
  obtain ⟨P', i', p', hip', hpi'⟩ := IsIdempotentComplete.idempotents_split W (𝟙 W - N.ebar)
    (KrullSchmidtCat.idem_one_sub N.ebar_idem)
  let v : ShiftedHom W W (2 : ℤ) := -(((N.r⁻¹ : kˣ) : k) • N.h)
  have hτv : N.τ.comp v (by norm_num : (2 : ℤ) + -2 = 0) = one - N.e := by
    rw [ShiftedHom.comp_neg, ShiftedHom.comp_smul', τ_comp_h, smul_neg, smul_smul,
      Units.inv_mul, one_smul, neg_neg]
  have hvτ : v.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) = N.e := by
    rw [ShiftedHom.neg_comp, ShiftedHom.smul_comp', h_comp_τ, smul_neg, smul_smul,
      Units.inv_mul, one_smul, neg_neg]
  have hve : v.comp (one - N.e) (by norm_num : (0 : ℤ) + 2 = 2) = v := by
    rw [ShiftedHom.neg_comp, ShiftedHom.smul_comp', h_comp_one_sub_e]
  let a : ShiftedHom P' P (-2 : ℤ) := shRes i' N.τ p
  let b : ShiftedHom P P' (2 : ℤ) := shRes i v p'
  have hab : a.comp b (by norm_num : (2 : ℤ) + -2 = 0) = ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 P') := by
    rw [shRes_comp_shRes, hpi, mk₀_ebar, τ_comp_e, hτv, ← mk₀_one_sub_ebar, shRes_mk₀]
    congr 1
    rw [← hpi']
    simp only [Category.assoc, reassoc_of% hip', hip']
  have hba : b.comp a (by norm_num : (-2 : ℤ) + 2 = 0) = ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 P) := by
    rw [shRes_comp_shRes, hpi', mk₀_one_sub_ebar, hve, hvτ, ← mk₀_ebar, shRes_mk₀]
    congr 1
    rw [← hpi]
    simp only [Category.assoc, reassoc_of% hip, hip]
  have hee : N.ebar ≫ (𝟙 W - N.ebar) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, N.ebar_idem, sub_self]
  have hee' : (𝟙 W - N.ebar) ≫ N.ebar = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, N.ebar_idem, sub_self]
  have h₃ : i ≫ p' = 0 := by
    have : i ≫ p' = i ≫ (p ≫ i) ≫ (p' ≫ i') ≫ p' := by
      simp only [Category.assoc, reassoc_of% hip, hip', Category.comp_id]
    rw [this, hpi, hpi', ← Category.assoc N.ebar, hee, zero_comp, comp_zero]
  have h₄ : i' ≫ p = 0 := by
    have : i' ≫ p = i' ≫ (p' ≫ i') ≫ (p ≫ i) ≫ p := by
      simp only [Category.assoc, reassoc_of% hip', hip, Category.comp_id]
    rw [this, hpi, hpi', ← Category.assoc (𝟙 W - N.ebar), hee', zero_comp, comp_zero]
  -- the identification `P' ≅ P⟨-2⟩` and the transported splitting
  let σ : P' ≅ P⟦(-2 : ℤ)⟧ := shIsoOfInv a b _ _ hab hba
  refine ⟨P, i, p, σ.inv ≫ i', p' ≫ σ.hom, hip, by
      rw [Category.assoc, ← Category.assoc i' p' σ.hom, hip', Category.id_comp, Iso.inv_hom_id],
    by rw [← Category.assoc, h₃, zero_comp], by rw [Category.assoc, h₄, comp_zero], by
      rw [Category.assoc, ← Category.assoc σ.hom, σ.hom_inv_id, Category.id_comp]
      rw [hpi, hpi', add_sub_cancel], ?_⟩
  -- the component of `x_L` is `r • b`
  have hi : i = i ≫ N.ebar := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hp' : p' = (𝟙 W - N.ebar) ≫ p' := by
    rw [← hpi', Category.assoc, hip', Category.comp_id]
  have hcomp : i ≫ N.xL ≫ p'⟦(2 : ℤ)⟧' = (N.r : k) • (b : P ⟶ P'⟦(2 : ℤ)⟧) := by
    have e1 : i ≫ N.xL ≫ p'⟦(2 : ℤ)⟧' =
        i ≫ ((N.e.comp N.xL (by norm_num : (2 : ℤ) + 0 = 2)).comp (one - N.e)
          (by norm_num : (0 : ℤ) + 2 = 2) : W ⟶ W⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧' := by
      rw [← mk₀_one_sub_ebar, ← mk₀_ebar, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
      conv_lhs => rw [hi, hp']
      simp only [Category.assoc, Functor.map_comp]
    have e2 : ∀ y : ShiftedHom W W (2 : ℤ), i ≫ (N.e.comp y (by norm_num : (2 : ℤ) + 0 = 2) :
        W ⟶ W⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧' = i ≫ ((N.e.comp y (by norm_num : (2 : ℤ) + 0 = 2)).comp
          (one - N.e) (by norm_num : (0 : ℤ) + 2 = 2) : W ⟶ W⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧' := by
      intro y
      rw [← mk₀_one_sub_ebar, ShiftedHom.comp_mk₀]
      conv_lhs => rw [hp']
      simp only [Category.assoc, Functor.map_comp]
    rw [e1, e_comp_xL_comp_one_sub_e]
    change i ≫ (N.h - (2 : k) • N.e.comp N.xR _ : W ⟶ W⟦(2 : ℤ)⟧) ≫ _ = _
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul, e2, h]
    change i ≫ (N.h : W ⟶ W⟦(2 : ℤ)⟧) ≫ _ - (2 : k) • (i ≫ (N.h : W ⟶ W⟦(2 : ℤ)⟧) ≫ _) =
      (N.r : k) • (shRes i v p' : P ⟶ P'⟦(2 : ℤ)⟧)
    rw [shRes_eq]
    change _ = (N.r : k) • (i ≫ (-(((N.r⁻¹ : kˣ) : k) • N.h) : W ⟶ W⟦(2 : ℤ)⟧) ≫ _)
    rw [Preadditive.neg_comp, Preadditive.comp_neg, Linear.smul_comp, Linear.comp_smul, smul_neg,
      smul_smul, Units.mul_inv, one_smul, two_smul]
    abel
  have hsplit : i ≫ N.xL ≫ (p' ≫ σ.hom)⟦(2 : ℤ)⟧' =
      (i ≫ N.xL ≫ p'⟦(2 : ℤ)⟧') ≫ σ.hom⟦(2 : ℤ)⟧' := by
    simp only [Functor.map_comp, Category.assoc]
  rw [hsplit, hcomp]
  haveI : IsIso (b : P ⟶ P'⟦(2 : ℤ)⟧) := (shIsoOfInv b a _ _ hba hab).isIso_hom
  haveI : IsIso ((N.r : k) • (b : P ⟶ P'⟦(2 : ℤ)⟧)) := by
    refine ⟨⟨((N.r⁻¹ : kˣ) : k) • inv (b : P ⟶ P'⟦(2 : ℤ)⟧), ?_, ?_⟩⟩
    · rw [Linear.smul_comp, Linear.comp_smul, IsIso.hom_inv_id, smul_smul, Units.mul_inv, one_smul]
    · rw [Linear.smul_comp, Linear.comp_smul, IsIso.inv_hom_id, smul_smul, Units.inv_mul, one_smul]
  infer_instance

end NH2

namespace StrongSl2

open CategoryTheory.Bicategory

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B)

/-- **The dot on the left strand of `E E 1_n` is an isomorphism on the common summand
`E^{(2)} 1_n ⟨1⟩`** (CL, proof of Lemma 3.6): there is a splitting
`E E 1_n ≅ P ⊕ P⟨-2⟩` (`P = E^{(2)} 1_n ⟨1⟩`) such that the component `P → P⟨-2⟩⟨2⟩` of
`E 1_n ◁ dot` (the dot on `E 1_{n+2}`) is an isomorphism. -/
theorem exists_E2_dot (r : ℤ) : ∃ (P : S.obj r ⟶ S.obj (r + 1 + 1)) (i : P ⟶ S.E r ≫ S.E (r + 1))
    (p : S.E r ≫ S.E (r + 1) ⟶ P) (i' : P⟦(-2 : ℤ)⟧ ⟶ S.E r ≫ S.E (r + 1))
    (p' : S.E r ≫ S.E (r + 1) ⟶ P⟦(-2 : ℤ)⟧), i ≫ p = 𝟙 P ∧ i' ≫ p' = 𝟙 _ ∧ i ≫ p' = 0 ∧
      i' ≫ p = 0 ∧ p ≫ i + p' ≫ i' = 𝟙 _ ∧
      IsIso (i ≫ (shWhiskerLeft (S.E r) (S.dot (r + 1)) : _ ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧) ≫
        p'⟦(2 : ℤ)⟧') :=
  (S.nh r).exists_decomp_dot

end StrongSl2

end Categorification.TwoRep
