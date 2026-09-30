/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Independence

/-!
# Rescaled polynomial representations of KLR algebras

Auxiliary material for the nondegeneracy argument of Khovanov–Lauda III (arXiv:0807.3250v1,
§6.4, TeX `sln-2008-ArXiv.tex` l. 9598–9790): "the action on `Pol_ν(ξ)` given by the 2-functor
`Γ^G` coincides with the action of `R(ν)` on `Pol_ν` defined in [KL]".

The action of `R(ν)` of KL III on `Γ_N(E_ν 1_λ)` passes through the isomorphism `Σ` of KL III
§4.2.1 (upward dots and crossings multiplied by signs `d_i = ±1`, `Categorification.KL3.Diagram.
CL.Sln.sigmaDatum`). On polynomials it therefore acts by *rescaled* operators: the dot on a strand
of colour `c` by `d_c x_a` (`opXd`), the crossing by `κ_{cd}` times the operator of KL I §2.3
(`opΨκ`). Conjugating by the substitution `x_a ↦ d_{t_a} x_a` on each component `t` (`conjD`, an
involution) turns them into the operators of the polynomial representation of KL I §2.3 for the
modified polynomials `rescaleP` (`conjD_opXd`, `conjD_opΨκ`), provided `κ_{cc} d_c = 1`. Hence
their linear independence follows from `Categorification.KLR.PolyRep.linearIndependent_opΨw`.
-/

noncomputable section

namespace Categorification.KLR.PolyRep

open MvPolynomial TypeA Equiv

variable {I : Type*} {k : Type*} [CommRing k] {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ## Rescaling the variables -/

/-- The substitution `x_a ↦ ε_a x_a`. -/
def scaleS (ε : Fin m → k) : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  aeval fun a => C (ε a) * X a

theorem scaleS_X (ε : Fin m → k) (a : Fin m) : scaleS ε (X a) = C (ε a) * X a := aeval_X _ _

theorem scaleS_scaleS (ε : Fin m → k) (hε : ∀ a, ε a * ε a = 1) (g : MvPolynomial (Fin m) k) :
    scaleS ε (scaleS ε g) = g := by
  have : (scaleS ε).comp (scaleS ε) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, scaleS_X, map_mul, algHom_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← C_mul, hε, C_1, one_mul]
  exact congrArg (fun φ => φ g) this

theorem scaleS_rename_swap (ε : Fin m → k) {a b : Fin m} (h : ε a = ε b)
    (g : MvPolynomial (Fin m) k) :
    scaleS ε (rename (swap a b) g) = rename (swap a b) (scaleS ε g) := by
  have : (scaleS ε).comp (rename (swap a b)) = (rename (swap a b)).comp (scaleS ε) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, rename_X, scaleS_X, map_mul, rename_C]
    congr 2
    by_cases hca : c = a
    · subst hca; rw [swap_apply_left, h]
    · by_cases hcb : c = b
      · subst hcb; rw [swap_apply_right, h]
      · rw [swap_apply_of_ne_of_ne hca hcb]
  exact congrArg (fun φ => φ g) this

/-- The divided difference and a rescaling which is uniform on the two variables:
`∂(S g) = ε S(∂ g)`. -/
theorem ddiff_scaleS (ε : Fin m → k) {a b : Fin m} (hab : a ≠ b) (h : ε a = ε b)
    (g : MvPolynomial (Fin m) k) :
    ddiff a b (scaleS ε g) = C (ε a) * scaleS ε (ddiff a b g) := by
  apply ddiff_eq_of_mul hab
  have hs := congrArg (scaleS ε) (ddiff_spec hab g)
  rw [map_mul, map_sub, map_sub, scaleS_X, scaleS_X, ← h, scaleS_rename_swap ε h] at hs
  rw [← hs]
  ring

theorem sadj_val_eq_swap' {j : ℕ} (h : j + 1 < m) (a : Fin m) :
    sadj m j a = swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ a := by
  apply Fin.ext
  rw [sadj_val_of_lt h]
  by_cases ha : (a : ℕ) = j
  · rw [show a = ⟨j, by omega⟩ from Fin.ext ha, swap_apply_left]; simp [swapNat]
  · by_cases ha' : (a : ℕ) = j + 1
    · rw [show a = ⟨j + 1, h⟩ from Fin.ext ha', swap_apply_right]; simp [swapNat]
    · rw [swap_apply_of_ne_of_ne (fun e => ha (congrArg Fin.val e))
        (fun e => ha' (congrArg Fin.val e))]
      simp [swapNat, ha, ha']

theorem sadj_symm_eq (n j : ℕ) : (sadj n j).symm = sadj n j := by
  rw [← Equiv.Perm.inv_def, sadj_inv]

theorem sadj_sadj_apply (n j : ℕ) (a : Fin n) : sadj n j (sadj n j a) = a := by
  rw [← Equiv.Perm.mul_apply, sadj_mul_self, Equiv.Perm.one_apply]

theorem sadj_smul_sadj_smul' (j : ℕ) (i : Seq ν) : sadj m j • sadj m j • i = i := by
  rw [← mul_smul, sadj_mul_self, one_smul]

theorem sadj_smul_eq_self' {j : ℕ} (h : j + 1 < m) {i : Seq ν}
    (hi : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩) : sadj m j • i = i := by
  apply Subtype.ext; funext a
  rw [Seq.smul_apply, sadj_symm_eq, sadj_val_eq_swap' h]
  by_cases ha : a = ⟨j, by omega⟩
  · subst ha; rw [swap_apply_left]; exact hi.symm
  · by_cases hb : a = ⟨j + 1, h⟩
    · subst hb; rw [swap_apply_right]; exact hi
    · rw [swap_apply_of_ne_of_ne ha hb]

/-! ## The rescaled operators -/

variable (d : I → k)

/-- The substitution `x_a ↦ d_{t_a} x_a` on each component `t`. -/
def conjD : Module.End k (Pol k ν) :=
  LinearMap.pi fun t => (scaleS (fun a => d (t.1 a))).toLinearMap.comp (LinearMap.proj t)

@[simp] theorem conjD_apply (f : Pol k ν) (t : Seq ν) :
    conjD d f t = scaleS (fun a => d (t.1 a)) (f t) := rfl

theorem conjD_conjD (hd : ∀ c, d c * d c = 1) : conjD (ν := ν) d * conjD d = 1 := by
  ext f t : 2
  simp only [Module.End.mul_apply, conjD_apply, Module.End.one_apply]
  exact scaleS_scaleS _ (fun a => hd _) _

/-- The rescaled dot: `d_{t_a} x_a` on the component `t`. -/
def opXd (a : Fin m) : Module.End k (Pol k ν) :=
  LinearMap.pi fun t => (C (d (t.1 a)) * X a : MvPolynomial (Fin m) k) • LinearMap.proj t

@[simp] theorem opXd_apply (a : Fin m) (f : Pol k ν) (t : Seq ν) :
    opXd d a f t = C (d (t.1 a)) * X a * f t := rfl

theorem conjD_opXd (hd : ∀ c, d c * d c = 1) (a : Fin m) :
    conjD (ν := ν) d * opXd d a * conjD d = opX a := by
  ext f t : 2
  simp only [Module.End.mul_apply, conjD_apply, opXd_apply, opX_apply, map_mul, scaleS_X,
    algHom_C, MvPolynomial.algebraMap_eq]
  rw [scaleS_scaleS _ (fun b => hd _), ← mul_assoc, ← C_mul, hd, C_1, one_mul]

variable [DecidableEq I]

theorem conjD_opE (hd : ∀ c, d c * d c = 1) (i : Seq ν) :
    conjD (ν := ν) d * opE i * conjD d = opE i := by
  refine LinearMap.ext fun f => funext fun t => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, conjD_apply, opE_apply, opE_apply]
  split_ifs with h
  · subst h; exact scaleS_scaleS _ (fun b => hd _) _
  · exact map_zero _

variable (κ : I → I → k)

/-- The rescaled crossing: `κ_{cd}` times the operator of KL I §2.3, `(c, d)` the colours of the
two strands of the source. -/
def opΨκ (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) : Module.End k (Pol k ν) :=
  if h : j + 1 < m then
    LinearMap.pi fun t => κ ((sadj m j • t).1 ⟨j, by omega⟩) ((sadj m j • t).1 ⟨j + 1, h⟩) •
      (crossComp P j h (sadj m j • t)).comp (LinearMap.proj (sadj m j • t))
  else 0

/-- The polynomials after conjugation: `P''_{cd}(u, v) = κ_{cd} P_{cd}(d_d u, d_c v)`. -/
def rescaleP (P : I → I → MvPolynomial (Fin 2) k) : I → I → MvPolynomial (Fin 2) k :=
  fun c e => C (κ c e) * aeval ![C (d e) * X 0, C (d c) * X 1] (P c e)

theorem conjD_opΨκ (hd : ∀ c, d c * d c = 1) (hκ : ∀ c, κ c c * d c = 1)
    (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) :
    conjD (ν := ν) d * opΨκ κ P j * conjD d = opΨ (rescaleP d κ P) j := by
  by_cases hj : j + 1 < m
  · refine LinearMap.ext fun f => funext fun t => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, conjD_apply, opΨ_apply _ _ hj, opΨκ, dite_eq_left hj]
    simp only [LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, conjD_apply]
    set src := sadj m j • t with hsrc
    have ht : t = sadj m j • src := by rw [hsrc, sadj_smul_sadj_smul']
    have hta : ∀ a, t.1 a = src.1 (sadj m j a) := fun a => by
      rw [ht, Seq.smul_apply, sadj_symm_eq]
    rw [map_smul]
    unfold crossComp
    split_ifs with hc
    · -- equal colours: `t = src`
      have hts : t = src := by rw [ht]; exact sadj_smul_eq_self' hj hc
      have hε : (fun a => d (src.1 a)) ⟨j, by omega⟩ = (fun a => d (src.1 a)) ⟨j + 1, hj⟩ := by
        simp only [hc]
      have hc' : src.1 ⟨j, by omega⟩ = src.1 ⟨j + 1, hj⟩ := hc
      rw [show (fun a => d (t.1 a)) = fun a => d (src.1 a) by rw [hts]]
      rw [ddiff_scaleS _ (by simp [Fin.ext_iff]) hε, map_mul, algHom_C, MvPolynomial.algebraMap_eq,
        scaleS_scaleS _ (fun a => hd _), smul_eq_C_mul, ← mul_assoc, ← C_mul]
      rw [hc', hκ, C_1, one_mul]
    · -- distinct colours
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply]
      rw [map_mul, rescaleP, smul_eq_C_mul]
      have e1 : scaleS (fun a => d (t.1 a)) (rename (sadj m j) (scaleS (fun a => d (src.1 a))
          (f src))) = rename (sadj m j) (f src) := by
        have : (scaleS (fun a => d (t.1 a))).comp ((rename (sadj m j)).comp
            (scaleS (fun a => d (src.1 a)))) = rename (sadj m j) := by
          apply MvPolynomial.algHom_ext
          intro a
          simp only [AlgHom.comp_apply, scaleS_X, map_mul, rename_X, algHom_C,
            MvPolynomial.algebraMap_eq]
          rw [hta (sadj m j a), sadj_sadj_apply, ← mul_assoc, ← C_mul, hd, C_1, one_mul]
        exact congrArg (fun φ => φ (f src)) this
      have e2 : scaleS (fun a => d (t.1 a)) (rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, hj⟩]
          (P (src.1 ⟨j, by omega⟩) (src.1 ⟨j + 1, hj⟩))) =
          rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, hj⟩]
            (aeval ![C (d (src.1 ⟨j + 1, hj⟩)) * X 0, C (d (src.1 ⟨j, by omega⟩)) * X 1]
              (P (src.1 ⟨j, by omega⟩) (src.1 ⟨j + 1, hj⟩))) := by
        have : (scaleS (fun a => d (t.1 a))).comp (rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, hj⟩]) =
            (rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, hj⟩]).comp
              (aeval ![C (d (src.1 ⟨j + 1, hj⟩)) * X 0, C (d (src.1 ⟨j, by omega⟩)) * X 1]) := by
          apply MvPolynomial.algHom_ext
          intro a
          fin_cases a
          · simp [scaleS_X, hta, sadj_apply_left hj]
          · simp [scaleS_X, hta, sadj_apply_right hj]
        exact DFunLike.congr_fun this _
      rw [e1, e2, map_mul, rename_C]
      ring
  · simp [opΨκ, opΨ, dite_eq_right hj]

end Categorification.KLR.PolyRep

end
