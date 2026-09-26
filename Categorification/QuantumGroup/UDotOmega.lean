/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotPairing

/-!
# The Chevalley involution `ω` of `U̇`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.2–2.1.3: `ω` is the `ℚ(q)`-linear algebra
involution of `U` with `ω(E_i) = F_i`, `ω(F_i) = E_i`, `ω(K_μ) = K_{-μ}`, extended to `U̇` by
`ω(1_λ) = 1_{-λ}`. On signed sequences it flips every sign:
`ω(E_t 1_λ) = E_{ω t} 1_{-λ}`.

## Main results

* `UDot.Uomega RD q` — `ω` on `U̇`, a linear map;
* `UDot.Uomega_E1`, `UDot.Uomega_one` — `ω(E_t 1_λ) = E_{ωt} 1_{-λ}`, `ω(1_λ) = 1_{-λ}`;
* `UDot.Uomega_mul` — `ω` is an algebra homomorphism;
* `UDot.Uomega_Uomega` — `ω² = 1`;
* `UDot.Uomega_UE`, `UDot.Uomega_UK` — `ω(E_{εi} x) = E_{-εi} ω(x)`, `ω(K_μ x) = K_{-μ} ω(x)`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K]
variable {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (q : Kˣ)

/-- Flip the sign of a signed letter. -/
def flipL (l : Bool × I) : Bool × I := (!l.1, l.2)

/-- `ω` on the free algebra: flip every sign. -/
def omegaF : Free K I →ₐ[K] Free K I := MonoidAlgebra.mapDomainAlgHom K K (FreeMonoid.map flipL)

theorem omegaF_ew (t : List (Bool × I)) : omegaF (ew t : Free K I) = ew (t.map flipL) := by
  simp [omegaF, ew, PreF.word, MonoidAlgebra.mapDomain_single]
  rfl

theorem omegaF_posF (T : PreF K I) : omegaF (posF T : Free K I) = negF T := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word u r =>
    rw [map_smul, map_smul, map_smul, posF_word, negF_word, omegaF_ew]
    congr 2
    simp [posW, negW, flipL]

theorem omegaF_negF (T : PreF K I) : omegaF (negF T : Free K I) = posF T := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word u r =>
    rw [map_smul, map_smul, map_smul, posF_word, negF_word, omegaF_ew]
    congr 2
    simp [posW, negW, flipL]

theorem wX_map_flipL (t : List (Bool × I)) : RD.wX (t.map flipL) = -RD.wX t := by
  induction t with
  | nil => simp
  | cons l t ih => rw [List.map_cons, RD.wX_cons, RD.wX_cons, ih, flipL, sgn_not, neg_smul, neg_add]

theorem qbr_neg (t : Kˣ) (n : ℤ) : qbr t (-n) = -qbr t n := by
  rw [qbr, qbr, neg_neg, ← neg_div, neg_sub]

theorem omegaF_commRel (lam : X) (b : List (Bool × I)) (i j : I) :
    omegaF (commRel C q (RD.ellOf lam) b i j) =
      -commRel C q (RD.ellOf (-lam)) (b.map flipL) j i := by
  simp only [commRel, map_sub, omegaF_ew, map_smul, map_one]
  simp only [List.map_cons, List.map_nil, flipL, Bool.not_true, Bool.not_false]
  have hw : wl C (RD.ellOf (-lam)) (b.map flipL) i = -wl C (RD.ellOf lam) b i := by
    rw [RD.wl_ellOf, RD.wl_ellOf, wX_map_flipL, ← neg_add, map_neg]
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, if_pos rfl, hw, qbr_neg]
    simp only [neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [zero_smul, sub_zero, neg_sub]

theorem omegaF_Lrel (lam : X) : Lrel C q (RD.ellOf lam) ≤
    (Lrel C q (RD.ellOf (-lam))).comap (omegaF (K := K) (I := I)).toLinearMap := by
  rw [Lrel, Submodule.span_le]
  intro z hz
  simp only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply]
  rcases hz with ⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩
  · rw [map_mul, map_mul, omegaF_ew, omegaF_ew, omegaF_commRel, mul_neg, neg_mul]
    exact neg_mem (Submodule.subset_span (Or.inl ⟨_, _, j, i, rfl⟩))
  · rw [map_mul, map_mul, omegaF_ew, omegaF_ew, omegaF_posF]
    exact Submodule.subset_span (Or.inr ⟨_, _, i, j, hij, Or.inr rfl⟩)
  · rw [map_mul, map_mul, omegaF_ew, omegaF_ew, omegaF_negF]
    exact Submodule.subset_span (Or.inr ⟨_, _, i, j, hij, Or.inl rfl⟩)

/-- `ω : U̇ 1_λ → U̇ 1_{-λ}`. -/
def omega (lam : X) : U1 RD q lam →ₗ[K] U1 RD q (-lam) :=
  (Lrel C q (RD.ellOf lam)).mapQ _ omegaF.toLinearMap (omegaF_Lrel RD q lam)

theorem omega_mk_ew (lam : X) (t : List (Bool × I)) :
    omega RD q lam (mk RD q lam (ew t)) = mk RD q (-lam) (ew (t.map flipL)) := by
  change mk RD q (-lam) (omegaF (ew t)) = _
  rw [omegaF_ew]

/-- **The Chevalley involution `ω` of `U̇`** (KL III §2.1.2–2.1.3). -/
def Uomega : UD RD q →ₗ[K] UD RD q :=
  DirectSum.toModule K X _ fun lam => ofB RD q (-lam) ∘ₗ omega RD q lam

theorem Uomega_E1 (t : List (Bool × I)) (lam : X) :
    Uomega RD q (E1 RD q t lam) = E1 RD q (t.map flipL) (-lam) := by
  rw [Uomega, E1, ofB, DirectSum.toModule_lof, LinearMap.comp_apply, omega_mk_ew]; rfl

/-- `ω(1_λ) = 1_{-λ}`. -/
theorem Uomega_one (lam : X) : Uomega RD q (one RD q lam) = one RD q (-lam) := by
  rw [one_eq_E1, Uomega_E1]; rfl

/-- Linear maps out of `U̇` agreeing on the `E_t 1_λ` agree. -/
theorem UD_lin_ext {N : Type*} [AddCommGroup N] [Module K N] {F G : UD RD q →ₗ[K] N}
    (h : ∀ t lam, F (E1 RD q t lam) = G (E1 RD q t lam)) : F = G := by
  refine LinearMap.ext fun x => ?_
  induction x using E1_induction with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul_E1 r t lam => rw [map_smul, map_smul, h]

/-- `ω` is an algebra homomorphism. -/
theorem Uomega_mul (x y : UD RD q) : Uomega RD q (x * y) = Uomega RD q x * Uomega RD q y := by
  have : (mulUD RD q).compr₂ (Uomega RD q) = (mulUD RD q).compl₁₂ (Uomega RD q) (Uomega RD q) := by
    refine UD_lin_ext RD q fun s mu => UD_lin_ext RD q fun t lam => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, ← mul_def, Uomega_E1, E1_mul_E1]
    rw [wX_map_flipL]
    by_cases h : lam + RD.wX t = mu
    · rw [if_pos h, if_pos (by rw [← h]; abel), Uomega_E1, List.map_append]
    · rw [if_neg h, if_neg (fun h' => h (by rw [← neg_inj, ← h']; abel)), map_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun this x) y

/-- `ω² = 1`. -/
theorem Uomega_Uomega (x : UD RD q) : Uomega RD q (Uomega RD q x) = x := by
  have : Uomega RD q ∘ₗ Uomega RD q = LinearMap.id := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, Uomega_E1, Uomega_E1, List.map_map, neg_neg, LinearMap.id_apply]
    congr 1
    conv_rhs => rw [← List.map_id t]
    congr 1
    funext l; simp [flipL]
  exact LinearMap.congr_fun this x

/-- `ω(E_{εi} x) = E_{-εi} ω(x)`. -/
theorem Uomega_UE (l : Bool × I) (x : UD RD q) :
    Uomega RD q (UE RD q l x) = UE RD q (flipL l) (Uomega RD q x) := by
  have : Uomega RD q ∘ₗ UE RD q l = UE RD q (flipL l) ∘ₗ Uomega RD q := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, UE_E1, Uomega_E1, Uomega_E1, UE_E1]
    rfl
  exact LinearMap.congr_fun this x

/-- `ω(K_μ x) = K_{-μ} ω(x)`. -/
theorem Uomega_UK (μ : Y) (x : UD RD q) :
    Uomega RD q (UK RD q μ x) = UK RD q (-μ) (Uomega RD q x) := by
  have : Uomega RD q ∘ₗ UK RD q μ = UK RD q (-μ) ∘ₗ Uomega RD q := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Uomega_E1]
    simp only [UK, E1, blockMap_ofB, Kact_mk_ew, map_smul]
    rw [← E1, Uomega_E1, ← E1, wX_map_flipL, ← neg_add, map_neg, map_neg,
      AddMonoidHom.neg_apply, neg_neg]
  exact LinearMap.congr_fun this x

end UDot

end Categorification.QuantumGroup

end
