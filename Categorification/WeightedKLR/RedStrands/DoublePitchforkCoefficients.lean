/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.Torsion.Field

/-! # Compatibility of the two pitchfork coefficients

Webster, arXiv:1309.3796v2, §2.2, (2.1a), (2.4b), (2.5e).
-/

namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory

/-- At a nonzero boundary with unit bubble closures and equal nonzero bigons,
the cup and cap pitchfork coefficients are reciprocal. -/
theorem pitchforkCoefficients_mul_eq_one
    {k : Type*} [Field k] {Cat : Type*} [Category* Cat] [Preadditive Cat] [Linear k Cat]
    {c d q : k}
    {x a b z : Cat} (ac : x ⟶ a) (dc : a ⟶ z) (dc' : z ⟶ a) (ac' : a ⟶ x)
    (bc : x ⟶ b) (mc : b ⟶ z) (mc' : z ⟶ b) (bc' : b ⟶ x)
    (hid : 𝟙 x ≠ 0) (hq : q ≠ 0)
    (hCup : c • (ac ≫ dc) = bc ≫ mc)
    (hCap : d • (dc' ≫ ac') = mc' ≫ bc')
    (hAA : ac ≫ ac' = 𝟙 x) (hBB : bc ≫ bc' = 𝟙 x)
    (hDD : dc ≫ dc' = q • 𝟙 a) (hMM : mc ≫ mc' = q • 𝟙 b) :
    c * d = 1 := by
  have close {y : Cat} (c : x ⟶ y) (p : y ⟶ z) (p' : z ⟶ y) (c' : y ⟶ x)
      (hc : c ≫ c' = 𝟙 x) (hp : p ≫ p' = q • 𝟙 y) :
      (c ≫ p) ≫ (p' ≫ c') = q • 𝟙 x := by
    calc
      _ = c ≫ (p ≫ p') ≫ c' := by simp only [Category.assoc]
      _ = _ := by rw [hp, Linear.smul_comp, Category.id_comp, Linear.comp_smul, hc]
  have h := congrArg₂ (fun (f : x ⟶ z) (g : z ⟶ x) => f ≫ g) hCup hCap
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul,
    close ac dc dc' ac' hAA hDD, close bc mc mc' bc' hBB hMM, smul_smul] at h
  have hz := sub_eq_zero.mpr h
  rw [← sub_smul] at hz
  have hc := (smul_eq_zero.mp hz).resolve_right hid
  exact mul_right_cancel₀ hq (show (c * d) * q = 1 * q by simpa using sub_eq_zero.mp hc)

/-- At a nonzero boundary with unit bubble closures, the product of the cup
and cap pitchfork coefficients times the downward bigon coefficient equals the
sideways bigon coefficient. With the printed coefficient `tⱼᵢ` on both pitchforks
this holds exactly when the downward bigon is `tⱼᵢ⁻²` times the sideways one, as
for the dual parameters of the downward relations in Cautis–Lauda,
arXiv:1111.1431v3, §2.2. -/
theorem pitchforkCoefficients_mul_bigon
    {k : Type*} [Field k] {Cat : Type*} [Category* Cat] [Preadditive Cat] [Linear k Cat]
    {c d p q : k}
    {x a b z : Cat} (ac : x ⟶ a) (dc : a ⟶ z) (dc' : z ⟶ a) (ac' : a ⟶ x)
    (bc : x ⟶ b) (mc : b ⟶ z) (mc' : z ⟶ b) (bc' : b ⟶ x)
    (hid : 𝟙 x ≠ 0)
    (hCup : c • (ac ≫ dc) = bc ≫ mc)
    (hCap : d • (dc' ≫ ac') = mc' ≫ bc')
    (hAA : ac ≫ ac' = 𝟙 x) (hBB : bc ≫ bc' = 𝟙 x)
    (hDD : dc ≫ dc' = p • 𝟙 a) (hMM : mc ≫ mc' = q • 𝟙 b) :
    c * d * p = q := by
  have close {y : Cat} {r : k} (c : x ⟶ y) (f : y ⟶ z) (f' : z ⟶ y) (c' : y ⟶ x)
      (hc : c ≫ c' = 𝟙 x) (hp : f ≫ f' = r • 𝟙 y) :
      (c ≫ f) ≫ (f' ≫ c') = r • 𝟙 x := by
    calc
      _ = c ≫ (f ≫ f') ≫ c' := by simp only [Category.assoc]
      _ = _ := by rw [hp, Linear.smul_comp, Category.id_comp, Linear.comp_smul, hc]
  have h := congrArg₂ (fun (f : x ⟶ z) (g : z ⟶ x) => f ≫ g) hCup hCap
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul,
    close ac dc dc' ac' hAA hDD, close bc mc mc' bc' hBB hMM, smul_smul] at h
  have hz := sub_eq_zero.mpr h
  rw [← sub_smul] at hz
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hid)

end Categorification.Stendhal.DoubleDiagram
