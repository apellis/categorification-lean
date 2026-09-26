/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Prop328

/-!
# `[ω̃]` is a ring involution of `K₀(U̇)`; KL III Proposition 3.28 for `ω`, integrally

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(eq. (3.43): "`ω̃` is a strict 2-functor […] its square is the identity"), §3.4 (the extension of
`ω̃` to `U̇`), and §3.6, Proposition 3.28 (TeX label `prop_tilde_lifts`) for `ω`.

The 2-functor `ω̃ : U → U` (`omegaU`) commutes with horizontal composition (`omegaU_hcomp`, from
`omegaU_whisk`) and squares to the identity (`omegaU_omegaU`). Hence on `U̇`:

* `omegaDotHcomp : ω̃(A B) ≅ ω̃(A) ω̃(B)` and `omegaDotOmegaDot : ω̃(ω̃(A)) ≅ A`;
* on `K₀(U̇)`: `omegaK0_mul : [ω̃](x y) = [ω̃](x) [ω̃](y)`, `omegaK0_one : [ω̃][1_λ] = [1_{-λ}]`,
  `omegaK0_omegaK0 : [ω̃]² = 1`, so `[ω̃]` is a `ℤ[q, q⁻¹]`-linear ring involution of `K₀(U̇)`
  (`λ ↦ -λ` on idempotents), the categorical counterpart of `ω` on `_𝒜 U̇`;
* `omegaK0_dp1_true`, `omegaK0_dp1_false`: `[ω̃][E_{±i^{(a)}} 1_μ] = [E_{∓i^{(a)}} 1_{-μ}]`;
* `omegaK0_dpC`: **KL III Proposition 3.28 for `ω` on the generators of `_𝒜 U̇`, exactly**:
  `[ω̃](γ(E_d 1_λ)) = γ(ω(E_d 1_λ))`, i.e. `[ω̃][E_d 1_λ] = [E_{ω d} 1_{-λ}]` in `K₀(U̇)`, with
  `ω(E_d 1_λ) = E_{ω d} 1_{-λ}` in `U̇` (`omega_dpW`). This removes the torsion caveat of
  `Categorification.Diagrams.KL3.Prop328.omegaK0_dpC` (which is the same statement multiplied
  by `∏ [a_r]_{i_r}!`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k] [DecidableEq I]

/-! ## `ω̃` and horizontal composition -/

section Hcomp

/-- The region `-r`. -/
abbrev negR (r : (psig RD).Region) : (psig RD).Region := -Omega.rX (RD := RD) r

omit [DecidableEq I] in
theorem Omega.obj_tensor (a b : Obj (psig RD)) :
    Omega.obj RD (a.tensor b) = (Omega.obj RD a).tensor (Omega.obj RD b) :=
  Obj.ext rfl (by simp [Obj.tensor, Omega.obj, Omega.word, List.map_append])

/-- `ω̃(1_a ⊗ g) = 1_{ω̃ a} ⊗ ω̃(g)`. -/
theorem omegaU_wL (a : Obj (psig RD)) {b b' : Obj (psig RD)}
    (g : (pres RD k).obj b ⟶ (pres RD k).obj b') (hb : b.WF) (hab : a.Composable b) :
    (omegaU RD k).map ((pres RD k).wL a g) =
      eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor a b)) ≫
        (pres RD k).wL (Omega.obj RD a) ((omegaU RD k).map g) ≫
          eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor a b')).symm := by
  have hw : b.WhiskerOK a [] := ⟨hab.left_wf, hab.endR_eq, trivial⟩
  simp only [Presentation.wL, Functor.map_comp, eqToHom_map]
  rw [omegaU_whisk g hb hw]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- `ω̃(f ⊗ 1_b) = ω̃(f) ⊗ 1_{ω̃ b}`. -/
theorem omegaU_wRAt {r : (psig RD).Region} {a a' : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj a')
    (b : Obj (psig RD)) (ha : a.start = r) (ha' : a'.start = r) (haw : a.WF)
    (hab : a.Composable b) :
    (omegaU RD k).map ((pres RD k).wRAt r f b ha ha') =
      eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor a b)) ≫
        (pres RD k).wRAt (negR r) ((omegaU RD k).map f) (Omega.obj RD b)
          (show negR a.start = negR r by rw [ha]) (show negR a'.start = negR r by rw [ha']) ≫
          eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor a' b)).symm := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, hab.ok_endR⟩
  simp only [Presentation.wRAt, Functor.map_comp, eqToHom_map]
  rw [omegaU_whisk f haw hw]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- **`ω̃` commutes with horizontal composition**: `ω̃(f ∘ g) = ω̃(f) ∘ ω̃(g)`. -/
theorem omegaU_hcomp {l m n : U RD k} {x x' : Bicat.Hom l m} {y y' : Bicat.Hom m n}
    (f : (pres RD k).obj x.obj ⟶ (pres RD k).obj x'.obj)
    (g : (pres RD k).obj y.obj ⟶ (pres RD k).obj y'.obj) :
    (omegaU RD k).map ((pres RD k).hcomp l.region f g x.start_eq x'.start_eq) =
      eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor x.obj y.obj)) ≫
        (pres RD k).hcomp (negR l.region) ((omegaU RD k).map f) ((omegaU RD k).map g)
          (show negR x.obj.start = negR l.region by rw [x.start_eq])
          (show negR x'.obj.start = negR l.region by rw [x'.start_eq]) ≫
        eqToHom (congrArg (pres RD k).obj (Omega.obj_tensor x'.obj y'.obj)).symm := by
  simp only [Presentation.hcomp, Functor.map_comp]
  rw [omegaU_wRAt f y.obj x.start_eq x'.start_eq x.wf (x.composable y),
    omegaU_wL x'.obj g y.wf (x'.composable y)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

end Hcomp

/-! ## `ω̃` on objects of `U̇`: composition and involutivity -/

section Dot

variable {ρ μ lam : X}

/-- **`ω̃(A B) ≅ ω̃(A) ω̃(B)`** in `U̇`. -/
def omegaDotHcomp (A : UKar RD k ρ μ) (B : UKar RD k μ lam) :
    (omegaDot ρ lam (-ρ) (-lam) rfl rfl).obj ((hcompDot (deg RD)).obj (A, B)) ≅
      (hcompDot (deg RD)).obj ((omegaDot ρ μ (-ρ) (-μ) rfl rfl).obj A,
        (omegaDot μ lam (-μ) (-lam) rfl rfl).obj B) :=
  udIso _ _ (Equiv.refl _) (fun _ => Bicat.Hom.ext (Omega.obj_tensor _ _).symm) (fun _ => rfl)
    (fun i j => by
      obtain ⟨a, b⟩ := i
      obtain ⟨a', b'⟩ := j
      show (pres RD k).hcomp (-ρ) ((omegaU RD k).map (A.p a a').1)
          ((omegaU RD k).map (B.p b b').1) _ _ =
        _ ≫ (omegaU RD k).map ((pres RD k).hcomp ρ (A.p a a').1 (B.p b b').1 _ _) ≫ _
      rw [omegaU_hcomp]
      simp)

/-- **`ω̃(ω̃(A)) ≅ A`** in `U̇` (KL III: "its square is the identity"). -/
def omegaDotOmegaDot (A : UKar RD k ρ μ) (h3 : -(-ρ) = ρ) (h4 : -(-μ) = μ) :
    (omegaDot (-ρ) (-μ) ρ μ h3 h4).obj ((omegaDot ρ μ (-ρ) (-μ) rfl rfl).obj A) ≅ A :=
  udIso _ _ (Equiv.refl _) (fun _ => Bicat.Hom.ext (Omega.obj_obj _).symm) (fun _ => rfl)
    (fun i j => by
      show (A.p i j).1 = _ ≫ (omegaU RD k).map ((omegaU RD k).map (A.p i j).1) ≫ _
      rw [omegaU_omegaU]
      simp [TR])

end Dot

/-! ## `[ω̃]` on `K₀(U̇)` -/

section K0

variable {ρ μ lam ρ' μ' lam' : X}

/-- **`[ω̃]` is multiplicative**: `[ω̃](x y) = [ω̃](x) [ω̃](y)`. -/
theorem omegaK0_mul (hρ : -ρ = ρ') (hμ : -μ = μ') (hl : -lam = lam') (x : K0Kar RD k ρ μ)
    (y : K0Kar RD k μ lam) :
    omegaK0 hρ hl (K0U.mul x y) = K0U.mul (omegaK0 hρ hμ x) (omegaK0 hμ hl y) := by
  subst hρ hμ hl
  induction x using SplitK0.induction_on generalizing y with
  | of A =>
    induction y using SplitK0.induction_on with
    | of B =>
      rw [K0U.mul_of, omegaK0_cl, omegaK0_cl, omegaK0_cl, K0U.mul_of]
      exact SplitK0.of_iso (omegaDotHcomp A B)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

/-- `[ω̃][1_λ] = [1_{-λ}]`. -/
theorem omegaK0_one (lam : X) :
    omegaK0 (RD := RD) (k := k) (lam := lam) (μ := lam) rfl rfl (K0U.one (deg := deg RD) _) =
      K0U.one (deg := deg RD) (wtObj RD k (-lam)) := by
  rw [K0U.one, omegaK0_cl, omegaDot_objOf]
  rfl

/-- **`[ω̃]² = 1`** (with the target weights identified with `ρ`, `μ` by any proofs). -/
theorem omegaK0_omegaK0 (hρ : -ρ = ρ') (hμ : -μ = μ') (h3 : -ρ' = ρ) (h4 : -μ' = μ)
    (x : K0Kar RD k ρ μ) : omegaK0 h3 h4 (omegaK0 hρ hμ x) = x := by
  subst hρ hμ
  induction x using SplitK0.induction_on with
  | of A =>
    rw [omegaK0_cl, omegaK0_cl]
    exact SplitK0.of_iso (omegaDotOmegaDot A h3 h4)
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | neg x hx => rw [map_neg, map_neg, hx]

theorem omegaK0_omegaK0_cast (hρ : -ρ = ρ') (hμ : -μ = μ') {ρ'' : X} (h3 : -ρ' = ρ'')
    (h4 : -μ' = μ) (e : ρ = ρ'') (x : K0Kar RD k ρ μ) :
    omegaK0 h3 h4 (omegaK0 hρ hμ x) = e ▸ x := by
  subst e
  exact omegaK0_omegaK0 hρ hμ h3 h4 x

end K0

/-! ## `[ω̃]` on divided powers -/

section Divided

variable (i : I) (a : ℕ)

theorem omegaK0_cast {ρ₁ ρ₂ μ ρ' μ' : X} (e : ρ₁ = ρ₂) (hρ : -ρ₂ = ρ') (hμ : -μ = μ')
    (x : K0Kar RD k ρ₁ μ) :
    omegaK0 hρ hμ (e ▸ x) = omegaK0 (e ▸ hρ : -ρ₁ = ρ') hμ x := by
  subst e; rfl

/-- The general form of `ω̃(E_{+i^{(a)}} 1_ν)`, for congruence in all weights. -/
theorem cl_omegaDot_objEdiv_congr {ν₁ ν₂ ρ₁ ρ₂ μ' : X} (e : ν₁ = ν₂) (eρ : ρ₁ = ρ₂)
    (hl₁ : -(wν RD (Multiset.replicate a i) + ν₁) = ρ₁) (hm₁ : -ν₁ = μ')
    (hl₂ : -(wν RD (Multiset.replicate a i) + ν₂) = ρ₂) (hm₂ : -ν₂ = μ') :
    (eρ ▸ K0U.cl ((omegaDot _ ν₁ ρ₁ μ' hl₁ hm₁).obj (objEdiv RD k i a ν₁ 0)) :
        K0Kar RD k ρ₂ μ') =
      K0U.cl ((omegaDot _ ν₂ ρ₂ μ' hl₂ hm₂).obj (objEdiv RD k i a ν₂ 0)) := by
  subst e eρ; rfl

/-- **`[ω̃][E_{+i^{(a)}} 1_μ] = [E_{-i^{(a)}} 1_{-μ}]`**. -/
theorem omegaK0_dp1_true {μ ρ μ' ρ' : X} (h : wt RD μ (List.replicate a (true, i)) = ρ)
    (hρ : -ρ = ρ') (hμ : -μ = μ') (h' : wt RD μ' (List.replicate a (false, i)) = ρ') :
    omegaK0 hρ hμ (dp1 RD k true i a μ ρ h) = dp1 RD k false i a μ' ρ' h' := by
  subst hρ hμ
  have hE := (wt_rep_up i a μ).trans h
  subst hE
  show omegaK0 rfl rfl (K0U.cl (objEdiv RD k i a μ 0)) = K0U.cl (h' ▸ objFdiv RD k i a (-μ) 0)
  rw [omegaK0_cl, cl_cast]
  exact (cl_omegaDot_objEdiv_congr i a (neg_neg μ) h' _ _ _ _).symm

/-- **`[ω̃][E_{-i^{(a)}} 1_μ] = [E_{+i^{(a)}} 1_{-μ}]`** (from `ω̃² = 1`). -/
theorem omegaK0_dp1_false {μ ρ μ' ρ' : X} (h : wt RD μ (List.replicate a (false, i)) = ρ)
    (hρ : -ρ = ρ') (hμ : -μ = μ') (h' : wt RD μ' (List.replicate a (true, i)) = ρ') :
    omegaK0 hρ hμ (dp1 RD k false i a μ ρ h) = dp1 RD k true i a μ' ρ' h' := by
  subst hρ hμ h
  show omegaK0 rfl rfl (K0U.cl (objFdiv RD k i a μ 0)) =
    K0U.cl (((wt_rep_up i a (-μ)).trans h') ▸ objEdiv RD k i a (-μ) 0)
  rw [← omegaK0_cl, omegaK0_omegaK0_cast _ _ _ _ ((wt_rep_up i a (-μ)).trans h'), cl_cast]

end Divided

/-! ## KL III Proposition 3.28 for `ω`, exactly on generators -/

section Dpss

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem dpLetters_flip (e : Bool × I × ℕ) :
    dpLetters (!e.1, e.2.1, e.2.2) = List.replicate e.2.2 (!e.1, e.2.1) := rfl

/-- `[ω̃][E_{εi^{(a)}} 1_μ] = [E_{-εi^{(a)}} 1_{-μ}]`. -/
theorem omegaK0_dp1 (e : Bool × I × ℕ) {μ ρ μ' ρ' : X}
    (h : wt RD μ (List.replicate e.2.2 (e.1, e.2.1)) = ρ) (hρ : -ρ = ρ') (hμ : -μ = μ')
    (h' : wt RD μ' (List.replicate e.2.2 (!e.1, e.2.1)) = ρ') :
    omegaK0 hρ hμ (dp1 RD k e.1 e.2.1 e.2.2 μ ρ h) = dp1 RD k (!e.1) e.2.1 e.2.2 μ' ρ' h' := by
  obtain ⟨ε, i, a⟩ := e
  cases ε with
  | true => exact omegaK0_dp1_true i a h hρ hμ h'
  | false => exact omegaK0_dp1_false i a h hρ hμ h'

/-- **KL III Proposition 3.28 for `ω`, integrally, on the generators `E_d 1_λ` of `_𝒜 U̇`**:
`[ω̃][E_d 1_λ] = [E_{ω d} 1_{-λ}]` exactly in `K₀(U̇)`; together with `ω(E_d 1_λ) = E_{ω d} 1_{-λ}`
(`omega_dpW`) this is `[ω̃] ∘ γ = γ ∘ ω` on generators. -/
theorem omegaK0_dpC_exact (d : List (Bool × I × ℕ)) {lam ρ lam' ρ' : X}
    (h : wt RD lam (dpWord d) = ρ) (hρ : -ρ = ρ') (hl : -lam = lam')
    (h' : wt RD lam' (dpWord (flipd d)) = ρ') :
    omegaK0 hρ hl (dpC RD k d lam ρ h) = dpC RD k (flipd d) lam' ρ' h' := by
  induction d generalizing ρ ρ' with
  | nil =>
    subst h hl
    have e : ρ' = -lam := by rw [← hρ]; rfl
    subst e
    exact omegaK0_one lam
  | cons e d ih =>
    have hν : wt RD lam' (dpWord (flipd d)) = -wt RD lam (dpWord d) := by
      rw [dpWord_flipd, ← hl, Omega.wt_map_dual]
    have h1 : wt RD (wt RD lam (dpWord d)) (dpLetters e) = ρ := by
      rw [← h, dpWord_cons, wt_append]
    have h1' : wt RD (-wt RD lam (dpWord d)) (dpLetters (!e.1, e.2.1, e.2.2)) = ρ' := by
      rw [← hρ, ← h1, ← Omega.wt_map_dual (RD := RD) (wt RD lam (dpWord d)) (dpLetters e)]
      congr 1
      simp [dpLetters, List.map_replicate]
    rw [dpC_cons e d lam _ ρ rfl h1 h, omegaK0_mul hρ rfl hl, ih rfl rfl hν,
      omegaK0_dp1 e h1 hρ rfl h1']
    exact (dpC_cons (!e.1, e.2.1, e.2.2) (flipd d) lam' _ ρ' hν h1' h').symm

end Dpss

end Categorification.KL3.Diagram
