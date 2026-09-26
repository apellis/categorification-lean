/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Sl2
import Categorification.TwoRep.QStrongRestrict

/-!
# The divided power `E^(2)` (nilHecke algebra `NH₂`)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §1.2 (after Definition 1.2: "whenever the KLR algebra acts on 1-morphisms in an
additive `k`-linear idempotent complete 2-category `K` one can define divided powers
`E_i^{(a)} 1_λ` as the image of certain idempotents (with an appropriate shift)"), and the proof
of Lemma 3.6 (`lem:Xind`), which uses `E E 1_n ≅ E^{(2)} 1_n ⟨-1⟩ ⊕ E^{(2)} 1_n ⟨1⟩`.

We work with an abstract nilHecke datum on an object `W` of a graded `k`-linear category: shifted
endomorphisms `xL, xR` of degree `2` and `τ` of degree `-2` with `τ τ = 0` and the dot slides
`r · 1 = xL τ - τ xR = τ xL - xR τ` (products read left to right, "first, then"), as for
`W = E E 1_n` in a `StrongSl2` (`StrongSl2.nh`).

* `NH2.e_idem`: `e = r⁻¹ xL τ` is an idempotent of degree `0`;
* `NH2.e_comp_τ`, `NH2.τ_comp_e`: `e τ = 0`, `τ e = τ`; `NH2.one_sub_e`: `1 - e = -r⁻¹ τ xR`;
* `NH2.h_comp_τ`, `NH2.τ_comp_h`: for `h = e xR (1 - e)`, `h τ = -r e` and `τ h = -r (1 - e)`.

These are the identities showing that `τ` and `-r⁻¹ h` are mutually inverse (up to the shift by
`2`) between the images of `1 - e` and `e`: `NH2.exists_iso_biprod` gives `W ≅ P ⊕ P⟨-2⟩` with
`P = im e` (in an idempotent complete category), using the general facts `shRes_comp_shRes`
(composition of restrictions of shifted morphisms) and `shIsoOfInv` (mutually inverse shifted
morphisms give an isomorphism `X ≅ Y⟨d⟩`). For a strong `sl₂` 2-representation,
`StrongSl2.exists_E2` gives `E^{(2)} 1_n := P⟨-1⟩` with `E E 1_n ≅ E^{(2)} 1_n ⟨1⟩ ⊕ E^{(2)} 1_n ⟨-1⟩`.

**Not yet available.** CL's proof of Lemma 3.6 also uses that the dot on the left strand induces an
isomorphism on the common summand `E^{(2)}⟨1⟩`. In `NH₂` this is the component `e xL (1 - e)`,
which equals `-h = r · (-r⁻¹ h)` *provided the two dots commute*, `xL xR = xR xL`. For
`xL = E ◁ x`, `xR = x ▷ E` this is the interchange law for *shifted* 2-morphisms, which needs a
compatibility between the shift-commutation isomorphisms of left and right whiskering; that
compatibility is not part of `GradedBicategory` (see the design notes in `Basic.lean`) and will
have to be added as a new mixin.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module

section ShiftedHomLinear

variable {k : Type*} [Field k] {H : Type*} [Category H] [Preadditive H] [Linear k H]
  [HasShift H ℤ] [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k]

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem ShiftedHom.smul_comp' {X Y Z : H} {a b c : ℤ} (t : k) (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) : (t • f).comp g h = t • f.comp g h := by
  change (t • f) ≫ _ ≫ _ = t • (f ≫ _ ≫ _)
  rw [Linear.smul_comp]

omit [∀ n : ℤ, (shiftFunctor H n).Additive] in
theorem ShiftedHom.comp_smul' {X Y Z : H} {a b c : ℤ} (t : k) (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) : f.comp (t • g) h = t • f.comp g h := by
  change f ≫ (shiftFunctor H a).map (t • g) ≫ _ = t • (f ≫ _ ≫ _)
  rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem ShiftedHom.mk₀_smul {X Y : H} (t : k) (f : X ⟶ Y) :
    ShiftedHom.mk₀ (0 : ℤ) rfl (t • f) = t • ShiftedHom.mk₀ (0 : ℤ) rfl f := by
  change (t • f) ≫ _ = t • (f ≫ _)
  rw [Linear.smul_comp]

omit [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem ShiftedHom.mk₀_sub {X Y : H} (f g : X ⟶ Y) :
    ShiftedHom.mk₀ (0 : ℤ) rfl (f - g) =
      ShiftedHom.mk₀ (0 : ℤ) rfl f - ShiftedHom.mk₀ (0 : ℤ) rfl g := by
  change (f - g) ≫ _ = f ≫ _ - g ≫ _
  rw [Preadditive.sub_comp]

omit [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem ShiftedHom.comp_sub' {X Y Z : H} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g g' : ShiftedHom Y Z b) (h : b + a = c) : f.comp (g - g') h = f.comp g h - f.comp g' h := by
  rw [sub_eq_add_neg, ShiftedHom.comp_add, ShiftedHom.comp_neg, ← sub_eq_add_neg]

omit [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem ShiftedHom.sub_comp' {X Y Z : H} {a b c : ℤ} (f f' : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) : (f - f').comp g h = f.comp g h - f'.comp g h := by
  rw [sub_eq_add_neg, ShiftedHom.add_comp, ShiftedHom.neg_comp, ← sub_eq_add_neg]

/-- The restriction `p ∘ f ∘ i` of a shifted endomorphism `f` of `W` along `i : P ⟶ W`,
`p : W ⟶ Q`. -/
def shRes {P Q W W' : H} (i : P ⟶ W) {d : ℤ} (f : ShiftedHom W W' d) (p : W' ⟶ Q) :
    ShiftedHom P Q d :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl i).comp (f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl p) (zero_add d))
    (add_zero d)

omit [Preadditive H] [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem shRes_eq {P Q W W' : H} (i : P ⟶ W) {d : ℤ} (f : ShiftedHom W W' d) (p : W' ⟶ Q) :
    shRes i f p = (i ≫ f ≫ p⟦d⟧' : P ⟶ Q⟦d⟧) := by
  rw [shRes, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]

omit [Preadditive H] [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- Composition of restrictions. -/
theorem shRes_comp_shRes {P Q R W₁ W₂ W₃ W₄ : H} (i : P ⟶ W₁) {d₁ d₂ d : ℤ}
    (f : ShiftedHom W₁ W₂ d₁) (p : W₂ ⟶ Q) (i' : Q ⟶ W₃) (g : ShiftedHom W₃ W₄ d₂) (p' : W₄ ⟶ R)
    (h : d₂ + d₁ = d) :
    (shRes i f p).comp (shRes i' g p') h =
      shRes i ((f.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (p ≫ i')) (zero_add _)).comp g h) p' := by
  rw [shRes_eq, shRes_eq, shRes_eq, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  have := (shiftFunctorAdd' H d₂ d₁ d h).inv.naturality p'
  simp only [Functor.comp_map] at this
  rw [this]

omit [Preadditive H] [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem shRes_mk₀ {P Q W : H} (i : P ⟶ W) (f : W ⟶ W) (p : W ⟶ Q) :
    shRes i (ShiftedHom.mk₀ (0 : ℤ) rfl f) p = ShiftedHom.mk₀ (0 : ℤ) rfl (i ≫ f ≫ p) := by
  rw [shRes, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]

omit [Preadditive H] [Linear k H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- **Mutually inverse shifted morphisms give an isomorphism** `X ≅ Y⟨d⟩`. -/
def shIsoOfInv {X Y : H} {d d' : ℤ} (a : ShiftedHom X Y d) (b : ShiftedHom Y X d')
    (h : d' + d = 0) (h' : d + d' = 0)
    (hab : a.comp b h = ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X))
    (hba : b.comp a h' = ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 Y)) : X ≅ Y⟦d⟧ where
  hom := a
  inv := b⟦d⟧' ≫ (shiftFunctorCompIsoId H d' d h).hom.app X
  hom_inv_id := by
    have := congrArg (· ≫ (shiftFunctorZero H ℤ).hom.app X) hab
    simp only [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorZero', Category.assoc] at this
    simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simpa using this
  inv_hom_id := by
    have e1 : (shiftFunctorCompIsoId H d' d h).hom.app X ≫ a =
        a⟦d'⟧'⟦d⟧' ≫ (shiftFunctorCompIsoId H d' d h).hom.app (Y⟦d⟧) :=
      ((shiftFunctorCompIsoId H d' d h).hom.naturality a).symm
    have e2 := shift_shiftFunctorCompIsoId_hom_app (C := H) d d' h' Y
    have e3 : b ≫ a⟦d'⟧' ≫ (shiftFunctorCompIsoId H d d' h').hom.app Y = 𝟙 Y := by
      have := congrArg (· ≫ (shiftFunctorZero H ℤ).hom.app Y) hba
      simp only [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorZero', Category.assoc] at this
      simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      simpa using this
    rw [Category.assoc, e1, ← e2, ← Functor.map_comp, ← Functor.map_comp, e3, CategoryTheory.Functor.map_id]

end ShiftedHomLinear

/-! ## The nilHecke algebra `NH₂` -/

/-- **A nilHecke datum on `W`**: dots `xL, xR` (degree `2`) and a crossing `τ` (degree `-2`) with
`τ τ = 0` and the dot slides `r · 1 = xL τ - τ xR = τ xL - xR τ` (CL (2.8), (2.9)). -/
structure NH2 {k : Type*} [Field k] {H : Type*} [Category H] [Preadditive H] [Linear k H]
    [HasShift H ℤ] (W : H) where
  xL : ShiftedHom W W (2 : ℤ)
  xR : ShiftedHom W W (2 : ℤ)
  τ : ShiftedHom W W (-2 : ℤ)
  r : kˣ
  τ_sq : τ.comp τ (by norm_num : (-2 : ℤ) + -2 = -4) = 0
  slide₁ : ShiftedHom.mk₀ (0 : ℤ) rfl ((r : k) • 𝟙 W) =
    xL.comp τ (by norm_num : (-2 : ℤ) + 2 = 0) - τ.comp xR (by norm_num : (2 : ℤ) + -2 = 0)
  slide₂ : ShiftedHom.mk₀ (0 : ℤ) rfl ((r : k) • 𝟙 W) =
    τ.comp xL (by norm_num : (2 : ℤ) + -2 = 0) - xR.comp τ (by norm_num : (-2 : ℤ) + 2 = 0)

namespace NH2

variable {k : Type*} [Field k] {H : Type*} [Category H] [Preadditive H] [Linear k H]
  [HasShift H ℤ] [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k]
  {W : H} (N : NH2 (k := k) W)

/-- The unit `1 ∈ ShiftedHom W W 0`. -/
abbrev one : ShiftedHom W W (0 : ℤ) := ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 W)

/-- The divided power idempotent `e = r⁻¹ xL τ` (degree `0`). -/
def e : ShiftedHom W W (0 : ℤ) :=
  ((N.r⁻¹ : kˣ) : k) • N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0)

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem τ_comp_xL : N.τ.comp N.xL (by norm_num : (2 : ℤ) + -2 = 0) =
    ((N.r : k) • one (W := W)) + N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) := by
  rw [one, ← ShiftedHom.mk₀_smul, N.slide₂, sub_add_cancel]

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem xL_comp_τ : N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) =
    ((N.r : k) • one (W := W)) + N.τ.comp N.xR (by norm_num : (2 : ℤ) + -2 = 0) := by
  rw [one, ← ShiftedHom.mk₀_smul, N.slide₁, sub_add_cancel]

omit [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `e τ = 0`. -/
theorem e_comp_τ : N.e.comp N.τ (by norm_num : (-2 : ℤ) + 0 = -2) = 0 := by
  rw [e, ShiftedHom.smul_comp', ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0)
    (by norm_num : (-2 : ℤ) + -2 = -4) (by norm_num), N.τ_sq, ShiftedHom.comp_zero, smul_zero]

/-- `τ e = τ`. -/
theorem τ_comp_e : N.τ.comp N.e (by norm_num : (0 : ℤ) + -2 = -2) = N.τ := by
  rw [e, ShiftedHom.comp_smul', ← ShiftedHom.comp_assoc _ _ _
    (by norm_num : (2 : ℤ) + -2 = 0) (by norm_num : (-2 : ℤ) + 2 = 0) (by norm_num),
    τ_comp_xL, ShiftedHom.add_comp, ShiftedHom.smul_comp', one, ShiftedHom.mk₀_id_comp,
    ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0)
      (by norm_num : (-2 : ℤ) + -2 = -4) (by norm_num), N.τ_sq, ShiftedHom.comp_zero, add_zero,
    smul_smul, Units.inv_mul, one_smul]

/-- **`e` is idempotent**: `e e = e`. -/
theorem e_idem : N.e.comp N.e (by norm_num : (0 : ℤ) + 0 = 0) = N.e := by
  nth_rewrite 1 [e]
  rw [ShiftedHom.smul_comp', ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0)
    (by norm_num : (0 : ℤ) + -2 = -2) (by norm_num), τ_comp_e]
  rfl

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `1 - e = -r⁻¹ τ xR`. -/
theorem one_sub_e : one (W := W) - N.e =
    -(((N.r⁻¹ : kˣ) : k) • N.τ.comp N.xR (by norm_num : (2 : ℤ) + -2 = 0)) := by
  rw [e, xL_comp_τ, smul_add, smul_smul, Units.inv_mul, one_smul]
  abel

/-- `1 - e` is idempotent. -/
theorem one_sub_e_idem : (one (W := W) - N.e).comp (one - N.e) (by norm_num : (0 : ℤ) + 0 = 0) =
    one - N.e := by
  rw [ShiftedHom.sub_comp', ShiftedHom.comp_sub', ShiftedHom.comp_sub', one,
    ShiftedHom.mk₀_id_comp, ShiftedHom.mk₀_id_comp, ShiftedHom.comp_mk₀_id, e_idem]
  abel

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `τ xR = -r (1 - e)`. -/
theorem τ_comp_xR : N.τ.comp N.xR (by norm_num : (2 : ℤ) + -2 = 0) =
    -((N.r : k) • (one (W := W) - N.e)) := by
  rw [one_sub_e, smul_neg, smul_smul, Units.mul_inv, one_smul, neg_neg]

omit [∀ n : ℤ, (shiftFunctor H n).Linear k] in
/-- `(1 - e) τ = τ`. -/
theorem one_sub_e_comp_τ : (one (W := W) - N.e).comp N.τ (by norm_num : (-2 : ℤ) + 0 = -2) =
    N.τ := by
  rw [ShiftedHom.sub_comp', one, ShiftedHom.mk₀_id_comp, e_comp_τ, sub_zero]

/-- `h = e xR (1 - e)` (degree `2`), the inverse of `τ` up to `-r` between the images of `e` and
`1 - e`. -/
def h : ShiftedHom W W (2 : ℤ) :=
  (N.e.comp N.xR (by norm_num : (2 : ℤ) + 0 = 2)).comp (one - N.e)
    (by norm_num : (0 : ℤ) + 2 = 2)

/-- `h τ = -r e`. -/
theorem h_comp_τ : N.h.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) = -((N.r : k) • N.e) := by
  rw [h, ShiftedHom.comp_assoc _ _ _ (by norm_num : (0 : ℤ) + 2 = 2)
      (by norm_num : (-2 : ℤ) + 0 = -2) (by norm_num), one_sub_e_comp_τ,
    ShiftedHom.comp_assoc _ _ _ (by norm_num : (2 : ℤ) + 0 = 2)
      (by norm_num : (-2 : ℤ) + 2 = 0) (by norm_num)]
  have hx : N.xR.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) =
      N.τ.comp N.xL (by norm_num : (2 : ℤ) + -2 = 0) - (N.r : k) • one (W := W) := by
    rw [τ_comp_xL]; abel
  rw [hx, ShiftedHom.comp_sub', ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 0 = -2)
      (by norm_num : (2 : ℤ) + -2 = 0) (by norm_num), e_comp_τ, ShiftedHom.zero_comp,
    ShiftedHom.comp_smul', one, ShiftedHom.comp_mk₀_id, zero_sub]

/-- `τ h = -r (1 - e)`. -/
theorem τ_comp_h : N.τ.comp N.h (by norm_num : (2 : ℤ) + -2 = 0) =
    -((N.r : k) • (one (W := W) - N.e)) := by
  rw [h, ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (2 : ℤ) + -2 = 0)
      (by norm_num : (0 : ℤ) + 2 = 2) (by norm_num),
    ← ShiftedHom.comp_assoc _ _ _ (by norm_num : (0 : ℤ) + -2 = -2)
      (by norm_num : (2 : ℤ) + 0 = 2) (by norm_num), τ_comp_e, τ_comp_xR,
    ShiftedHom.neg_comp, ShiftedHom.smul_comp', one_sub_e_idem]

/-- `h (1 - e) = h`. -/
theorem h_comp_one_sub_e : N.h.comp (one (W := W) - N.e) (by norm_num : (0 : ℤ) + 2 = 2) = N.h := by
  rw [h, ShiftedHom.comp_assoc _ _ _ (by norm_num : (0 : ℤ) + 2 = 2)
    (by norm_num : (0 : ℤ) + 0 = 0) (by norm_num), one_sub_e_idem]

/-- The degree-`0` idempotent `e` as a morphism `W ⟶ W`. -/
def ebar : W ⟶ W := (ShiftedHom.homEquiv (0 : ℤ) rfl).symm N.e

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem mk₀_ebar : ShiftedHom.mk₀ (0 : ℤ) rfl N.ebar = N.e :=
  (ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply N.e

theorem ebar_idem : N.ebar ≫ N.ebar = N.ebar := by
  apply (ShiftedHom.homEquiv (X := W) (Y := W) (0 : ℤ) rfl).injective
  simp only [ShiftedHom.homEquiv_apply]
  rw [← ShiftedHom.mk₀_comp_mk₀ _ _ (by norm_num : (0 : ℤ) + 0 = 0), mk₀_ebar, e_idem]

omit [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor H n).Linear k] in
theorem mk₀_one_sub_ebar : ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 W - N.ebar) = one - N.e := by
  rw [ShiftedHom.mk₀_sub, mk₀_ebar]

variable [IsIdempotentComplete H] [HasBinaryBiproducts H]

include N in
/-- **`W ≅ P ⊕ P⟨-2⟩`** for `P` the image of the nilHecke idempotent `e`: the images of `1 - e` and
`e` are isomorphic up to the shift by `-2`, via `τ` and `-r⁻¹ h`. -/
theorem exists_iso_biprod : ∃ P : H, Nonempty (W ≅ P ⊞ P⟦(-2 : ℤ)⟧) := by
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
  have e₁ : W ≅ P ⊞ P' := KrullSchmidtCat.isoOfData i p i' p' hip hip' h₃ h₄
    (by rw [hpi, hpi', add_sub_cancel])
  exact ⟨P, ⟨e₁ ≪≫ biprod.mapIso (Iso.refl P) (shIsoOfInv a b _ _ hab hba)⟩⟩

end NH2

/-! ## Divided powers in a strong `sl₂` 2-representation -/

namespace StrongSl2

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The nilHecke datum on `E E 1_n` (CL (2.8), (2.9)). -/
def nh (r : ℤ) : NH2 (k := k) (S.E r ≫ S.E (r + 1)) where
  xL := shWhiskerLeft (S.E r) (S.dot (r + 1))
  xR := shWhiskerRight (S.dot r) (S.E (r + 1))
  τ := S.cross r
  r := S.rQ
  τ_sq := S.cross_sq r
  slide₁ := S.dot_slide_left r
  slide₂ := S.dot_slide_right r

variable [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

/-- **The divided power `E^{(2)} 1_n`** (CL §1.2, after Definition 1.2): there is a 1-morphism
`E^{(2)}` with `E E 1_n ≅ E^{(2)} 1_n ⟨1⟩ ⊕ E^{(2)} 1_n ⟨-1⟩`, namely the image of the nilHecke
idempotent `r⁻¹ x τ`, shifted by `-1`. -/
theorem exists_E2 (r : ℤ) : ∃ E2 : S.obj r ⟶ S.obj (r + 1 + 1),
    Nonempty (S.E r ≫ S.E (r + 1) ≅ E2⟦(1 : ℤ)⟧ ⊞ E2⟦(-1 : ℤ)⟧) := by
  obtain ⟨P, ⟨e⟩⟩ := (S.nh r).exists_iso_biprod
  refine ⟨P⟦(-1 : ℤ)⟧, ⟨e ≪≫ biprod.mapIso
    ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by norm_num)).app P).symm
    ((shiftFunctorAdd' _ (-1 : ℤ) (-1) (-2) (by norm_num)).app P)⟩⟩

end StrongSl2

end Categorification.TwoRep
