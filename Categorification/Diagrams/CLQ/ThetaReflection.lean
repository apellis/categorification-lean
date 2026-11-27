/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SymmetryPsi
import Categorification.Diagrams.CL.RotateAll
import Categorification.Diagrams.KL3.SymmetrySigmaOmega

/-!
# The reflection with inverted orientations of `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.2 (`sec:cycbiadjoint`, `eq_almost_cyclic`); M. Khovanov, A. Lauda,
*A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2 (the symmetries `ψ̃`, `σ̃`,
`ω̃` and the remark that `ψ̃ ω̃ σ̃` is the rotation by `180°`).

`Categorification.Diagrams.KL3.SymmetrySigmaOmega` shows that the reflection of a diagram in a
vertical axis with inverted orientations (`thetaD`, `thetaLin`, same weights, no sign) maps the
relations of KL III's `U` to relations of `U`. Here we prove the analogue for `U_Q(g)` with
`r = 1` (`CLQ.pres RD k sc`). In `U_Q(g)` 2-morphisms are cyclic only up to the scalars
`t_{ij}`, and the reflected relations hold in `U_{Q^θ}(g)` for the scalars `Q^θ = thetaScalars sc`:

* `t^θ_{ij} = t_{ji}^{-1}`, `s^{θ, pq}_{ij} = (t_{ij} t_{ji})^{-1} s^{pq}_{ij}`, `r^θ = 1`,

i.e. CL's dual scalars `Q'` (§2.1.1) except for `r` (which `Q'` negates).

## Method

The reflection with inverted orientations is the reflection `ψ̃` in a horizontal axis
(`CLQ.psiUQ`, a symmetry of `U_Q(g)` for every `Q` with `r = 1`) composed with the rotation by
`180°` (`CL.rotC`, defined for every `Q`). By `CL.rotC_dgCL` the rotation multiplies a diagram by
`t_{ij}` for every upward crossing `E_j E_i ⟶ E_i E_j` and by `t_{ji}^{-1}` for every downward
crossing `F_j F_i ⟶ F_i F_j`. These are the scalars `thetaDatum sc` of a rescaling of `U_Q(g)`
(`CL.RescaleDatum`) evaluated on the reflected generators (`chi_thetaDatum`), so `ψ̃ ∘ τ` is the
reflection followed by that rescaling (`lin_scL_thetaLin`). Undoing the rescaling gives the
result in `U_{Q^θ}(g)`, with `Q^θ = (thetaDatum sc).inv.mapScalars`.

## Main results

* `thetaObj_ob`, `layers_thetaD_mkD`: the reflection of normal forms;
* `lin_scL_thetaLin`: **`ψ̃ ∘ τ` is the reflection with inverted orientations followed by the
  rescaling by `thetaDatum sc`**;
* `lin_thetaLin_eq_zero_of_ob`, `lin_thetaLin_eq_zero`: **the reflection with inverted
  orientations of a linear combination of diagrams that vanishes in `U_Q(g)` vanishes in
  `U_{Q^θ}(g)`**;
* `thetaScalars_t_of_ne`, `thetaScalars_s`, `thetaScalars_r`: the scalars `Q^θ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite CL

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-! ## The reflection of normal forms -/

/-- The reflection with inverted orientations of the layers of a normal-form diagram is `ψ̃` of
its rotation. -/
theorem rls_rotLs (ls : List (LayerData I)) :
    Psi.rls (rotLs ls) = Sig.sls (Omega.wls ls) := by
  simp only [Psi.rls, rotLs, Sig.sls, Omega.wls, List.map_reverse, List.reverse_reverse,
    List.map_map]
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨u, g, v⟩ := x
  simp only [Function.comp_apply, Sig.ld, rotLD, Psi.ld, Omega.ld, rd]
  congr 2
  cases g <;> simp [Omega.shape]

/-- The reflection with inverted orientations of `E_t 1_μ` is `E_{t*} 1_ν`, `ν = μ + t_X`. -/
theorem thetaObj_ob (μ : X) (t : List (Letter I)) :
    thetaObj (ob RD μ t) = ob RD (wt RD μ t) (rd t) := by
  show Sig.obj RD (Omega.obj RD (ob RD μ t)) = _
  rw [Omega.trO, Sig.trO (-μ) (wt RD μ t) _ (by rw [Omega.wt_map_dual, neg_neg])]
  rfl

/-- The layers of the reflection with inverted orientations of a normal-form diagram. -/
theorem layers_thetaD_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) :
    Diagram.layers (thetaD (mkD RD μ ls h)) =
      layList RD (wt RD μ s) (Sig.sls (Omega.wls ls)) := by
  rw [thetaD, Sig.layers_reflD, Omega.layers_reflD_mkD, ← layers_mkD RD (-μ) (Omega.wls ls)
    (Omega.sChain_wls h), ← Sig.layers_reflD,
    Sig.layers_reflD_mkD (-μ) (wt RD μ s) _ _ (by rw [Omega.wt_map_dual, neg_neg])]

/-! ## The rescaling by the scalars of the rotation -/

section Datum

variable [DecidableEq I] (sc : CL.CLScalars C k)

variable (RD) in
/-- The rescaling of `U_Q(g)` whose scalars on the reflected generators are those of the rotation
(`CL.sigmaCL`): the upward crossing `E_a E_b ⟶ E_b E_a` is multiplied by `t_{ba}^{-1}`, so that
the downward crossing `F_b F_a ⟶ F_a F_b` is multiplied by `t_{ab}` (`RescaleDatum.dnCross`);
dots, cups and caps are fixed. -/
def thetaDatum : RescaleDatum RD k where
  dot _ := 1
  cross a b := (sc.t b a)⁻¹
  cup _ := 1
  cup_up i x := by simp

/-- The scalars of `thetaDatum` on the reflected generators are those of the rotation. -/
theorem chi_thetaDatum (g : Shape I) (ν : X) :
    (((thetaDatum RD sc).chi ((Sig.shape (Omega.shape g)).gen RD ν) : kˣ) : k) =
      sigmaCL k sc.withRone g := by
  rcases g with l | ⟨_ | _, j, i⟩ | l | l
  · rfl
  · rfl
  · show ((RescaleDatum.dnCross (thetaDatum RD sc) i j ν : kˣ) : k) = (sc.t i j : k)
    unfold RescaleDatum.dnCross
    split_ifs with h
    · subst h; simp [thetaDatum, sc.t_self]
    · simp [thetaDatum]
  · rfl
  · show (((1 : kˣ))⁻¹ : kˣ) = (1 : k)
    simp

/-- The weight of the reflection with inverted orientations of a normal-form diagram, for the
rescaling `thetaDatum`, is the product of the scalars of the rotation of its generators. -/
theorem weight_thetaD_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) :
    ((Rescale.weight (thetaDatum RD sc).chi (Diagram.layers (thetaD (mkD RD μ ls h))) : kˣ) : k) =
      (ls.map fun x => sigmaCL k sc.withRone x.2.1).prod := by
  rw [layers_thetaD_mkD, Rescale.weight, ← Units.coeHom_apply, map_list_prod]
  simp only [layList, Sig.sls, Omega.wls, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun x _ => ?_)
  exact chi_thetaDatum sc x.2.1 _

/-- `ψ̃` on morphisms of `U_Q(g)`, as a `k`-linear map. -/
def psiUnopQ (a b : Obj (psig RD)) :
    ((pres RD k sc).obj a ⟶ (pres RD k sc).obj b) →ₗ[k]
      ((pres RD k sc).obj b ⟶ (pres RD k sc).obj a) where
  toFun f := ((psiUQ RD k sc).map f).unop
  map_add' f g := by rw [Functor.map_add, unop_add]
  map_smul' r f := by rw [Functor.map_smul, unop_smul']; rfl

omit [DecidableEq I] in
theorem thetaObj_ob' (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    thetaObj (ob RD μ t) = ob RD ν (rd t) := by
  rw [thetaObj_ob, h]

/-- **`ψ̃ ∘ τ` is the reflection with inverted orientations followed by the rescaling by
`thetaDatum`**, on linear combinations of diagrams `E_s 1_μ ⟶ E_t 1_μ`. -/
theorem lin_scL_thetaLin (μ : X) {s t : List (Letter I)} (hst : wt RD μ s = wt RD μ t)
    (f : LinDiagram k (ob RD μ s) (ob RD μ t)) :
    (pres RD k sc).lin (Rescale.scL (thetaDatum RD sc).chi (thetaLin k f)) =
      eqToHom (congrArg (pres RD k sc).obj (thetaObj_ob μ s)) ≫
        psiUnopQ sc _ _ (rotC (pres RD k sc) (zigzags RD k sc.withRone) μ (wt RD μ s) s t
          (rd s) (rd t) rfl hst.symm rfl rfl ((pres RD k sc).lin f)) ≫
        eqToHom (congrArg (pres RD k sc).obj (thetaObj_ob' μ _ t hst.symm).symm) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Rescale.scL_add, Presentation.lin_add, hf, hg, Presentation.lin_add, map_add,
      map_add, Preadditive.add_comp, Preadditive.comp_add]
  | single d c =>
    change (pres RD k sc).lin (Rescale.scL _ (Finsupp.mapDomain thetaD (Finsupp.single d c))) = _
    rw [Finsupp.mapDomain_single, Rescale.scL_single, Presentation.lin_smul,
      Presentation.lin_smul, Presentation.lin_of, Presentation.lin_single, map_smul, map_smul,
      Linear.smul_comp, Linear.comp_smul]
    congr 1
    obtain ⟨ls, h, rfl⟩ := exists_mkD RD μ d
    rw [← dgC_of h]
    erw [rotC_dgCL RD k sc.withRone μ (wt RD μ s) ls h rfl hst.symm]
    rw [map_smul, Linear.smul_comp, Linear.comp_smul, weight_thetaD_mkD]
    congr 1
    show _ = _ ≫ ((psiUQ RD k sc).map (NF.dg (pres RD k sc) (wt RD μ s) (rd t) (rd s)
      (rotLs ls))).unop ≫ _
    rw [psiUQ_dg, Quiver.Hom.unop_op]
    have H₁ : IsDgC (pres RD k sc) ((pres RD k sc).diag (thetaD (mkD RD μ ls h)))
        (layList RD (wt RD μ s) (Psi.rls (rotLs ls))) :=
      ⟨_, rfl, by rw [layers_thetaD_mkD, rls_rotLs]⟩
    exact H₁.eq_eqToHom (isDgC_dg (wt RD μ s) (Psi.sChain_rls (sChain_rotLs h))) (thetaObj_ob μ s)
      (thetaObj_ob' μ _ t hst.symm)

/-! ## The reflected relations -/

variable (RD) in
/-- **The scalars `Q^θ` of the reflection with inverted orientations of `U_Q(g)`** (`r = 1`):
`t^θ_{ij} = t_{ji}^{-1}`, `s^{θ, pq}_{ij} = (t_{ij} t_{ji})^{-1} s^{pq}_{ij}`, `r^θ = 1`
(`thetaScalars_t_of_ne`, `thetaScalars_s`, `thetaScalars_r`). -/
def thetaScalars : CL.CLScalars C k := (thetaDatum RD sc).inv.mapScalars sc.withRone

theorem thetaScalars_t_of_ne {i j : I} (h : i ≠ j) :
    (thetaScalars RD sc).t i j = (sc.t j i)⁻¹ := by
  rw [thetaScalars, RescaleDatum.mapScalars_t_of_ne _ _ h]
  simp only [RescaleDatum.inv_dot, RescaleDatum.inv_cross, thetaDatum, inv_inv, one_pow,
    CL.CLScalars.withRone_t, inv_one, mul_one]
  group

@[simp] theorem thetaScalars_s (i j : I) (p q : ℕ) :
    (thetaScalars RD sc).s i j p q =
      (((sc.t i j * sc.t j i)⁻¹ : kˣ) : k) * sc.s i j p q := by
  simp only [thetaScalars, RescaleDatum.mapScalars_s, RescaleDatum.inv_dot,
    RescaleDatum.inv_cross, thetaDatum, inv_inv, inv_one, Units.val_one, one_pow, mul_one,
    CL.CLScalars.withRone_s]
  rw [mul_comm, mul_comm (sc.t j i)]

@[simp] theorem thetaScalars_r (i : I) : (thetaScalars RD sc).r i = 1 := by
  simp [thetaScalars, thetaDatum, sc.t_self]

/-- The reflection with inverted orientations of a linear combination of diagrams between
normal-form objects that vanishes in `U_Q(g)` vanishes in `U_{Q^θ}(g)`. -/
theorem lin_thetaLin_eq_zero_of_ob (μ : X) {s t : List (Letter I)}
    (f : LinDiagram k (ob RD μ s) (ob RD μ t)) (hf : (pres RD k sc).lin f = 0) :
    (presCL RD k (thetaScalars RD sc)).lin (thetaLin k f) = 0 := by
  by_cases hst : wt RD μ s = wt RD μ t
  · have H : (presCL RD k sc.withRone).lin
        (Rescale.scL (thetaDatum RD sc).chi (thetaLin k f)) = 0 := by
      have := lin_scL_thetaLin sc μ hst f
      rw [hf, map_zero, map_zero, Limits.zero_comp, Limits.comp_zero] at this
      exact this
    rw [← Rescale.scL_scL (RescaleDatum.chi_inv (thetaDatum RD sc)) (thetaLin k f)]
    have h₂ := Rescale.functor_lin (RescaleDatum.lin_scL_rel (thetaDatum RD sc).inv
      sc.withRone) (Rescale.scL (thetaDatum RD sc).chi (thetaLin k f))
    rw [H, Functor.map_zero] at h₂
    exact h₂.symm
  · have := isEmpty_hom_ob (RD := RD) hst
    rw [show f = 0 from Finsupp.ext (α := ob RD μ s ⟶ ob RD μ t) fun d => (IsEmpty.false d).elim,
      map_zero, Presentation.lin_zero]

/-- **The reflection with inverted orientations of a linear combination of diagrams that
vanishes in `U_Q(g)` vanishes in `U_{Q^θ}(g)`** (`r = 1`; the source object is well formed). -/
theorem lin_thetaLin_eq_zero {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hf : (pres RD k sc).lin f = 0) : (presCL RD k (thetaScalars RD sc)).lin (thetaLin k f) = 0 := by
  by_cases he : IsEmpty (a ⟶ b)
  · rw [show f = 0 from Finsupp.ext (α := a ⟶ b) fun d => (IsEmpty.false d).elim, map_zero,
      Presentation.lin_zero]
  obtain ⟨d⟩ := not_isEmpty_iff.1 he
  have hb := (Diagram.chain d).wf ha
  obtain ⟨μ, s, rfl⟩ : ∃ μ s, a = ob RD μ s := ⟨_, _, wf_eq_ob a ha⟩
  obtain ⟨ν, t, rfl⟩ : ∃ ν t, b = ob RD ν t := ⟨_, _, wf_eq_ob b hb⟩
  have e : ν = μ := by
    have := (Diagram.chain d).endR_eq
    rwa [ob_endR, ob_endR] at this
  subst e
  exact lin_thetaLin_eq_zero_of_ob sc ν f hf

end Datum

end Categorification.KL3.Diagram.CLQ
