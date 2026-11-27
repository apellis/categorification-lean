/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SymmetrySigma
import Categorification.Diagrams.CLQ.ThetaReflection
import Categorification.Diagrams.KL3.Symmetries

/-!
# The inversion of orientations of `U_Q(g)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2,
the symmetry `ω̃` (eq. (3.43)): invert the orientation of every strand, send `λ ↦ -λ`, and
multiply a diagram by `(-1)` to the number of its crossings of equally labelled strands. For the
2-category `U_Q(g)` of S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1, with `r = 1`
(`CLQ.pres`), the inversion of orientations does not preserve the scalars: it maps the
relations of `U_Q(g)` to relations of `U_{Q^θ}(g)`, with the scalars `Q^θ = thetaScalars sc` of
`Categorification.Diagrams.CLQ.ThetaReflection`
(`t^θ_{ij} = t_{ji}^{-1}`, `s^{θ,pq}_{ij} = (t_{ij} t_{ji})^{-1} s^{pq}_{ij}`, `r^θ = 1`).

## Method

`ω̃ = σ̃ ∘ (σ̃ ω̃)`: the reflection with inverted orientations (`thetaLin`, no sign) maps the
relations of `U_Q(g)` to relations of `U_{Q^θ}(g)` (`CLQ.lin_thetaLin_eq_zero`), and the signed
reflection `σ̃` in a vertical axis is a symmetry of `U_{Q^θ}(g)` with the same scalars
(`CLQ.sigLQ_eq_zero_of_lin`). As `σ̃² = 1` on layers (`Sig.rlay_rlay`), the composite is the
inversion of orientations with the sign of `ω̃` (`sigLQ_thetaLin`).

This is the form of `ω̃` used for the black strands of Webster's double diagrams with general
parameters, arXiv:1309.3796v3, proof of Lemma 4.29.

## Main results

* `omegaSLin`: the inversion of orientations, with the sign of `ω̃`, on linear combinations of
  diagrams;
* `pres_thetaScalars`: `U_{Q^θ}(g)` already has `r = 1`;
* `lin_omegaSLin_eq_zero`: **the inversion of orientations of a linear combination of diagrams
  that vanishes in `U_Q(g)` vanishes in `U_{Q^θ}(g)`** (the source object is well formed).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

namespace CL.CLScalars

variable {I : Type*} {C : QuantumGroup.CartanDatum I} {k : Type*} [CommRing k]

/-- Scalars with `r = 1` are their own normalization. -/
theorem withRone_eq_of_r (S : CL.CLScalars C k) (h : ∀ i, S.r i = 1) : S.withRone = S := by
  obtain ⟨t, s, r, h₁, h₂, h₃⟩ := S
  simp only [CL.CLScalars.withRone, CL.CLScalars.mk.injEq, true_and]
  funext i
  exact (h i).symm

end CL.CLScalars

namespace CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] (sc : CL.CLScalars C k)

theorem omega_obj_wf {a : Obj (psig RD)} (ha : a.WF) : (Omega.obj RD a).WF := by
  rw [wf_eq_ob a ha, Omega.trO]
  exact ob_wf RD _ _

variable [DecidableEq I]

/-- `U_{Q^θ}(g)` already has `r = 1`. -/
theorem pres_thetaScalars :
    pres RD k (thetaScalars RD sc) = CL.presCL RD k (thetaScalars RD sc) := by
  rw [pres, CL.CLScalars.withRone_eq_of_r _ (thetaScalars_r sc)]

variable (k) in
/-- The inversion of orientations of linear combinations of diagrams, with the sign `-1` on
every crossing of equally labelled strands (KL III's `ω̃` on the free 2-category). -/
def omegaSLin {a b : Obj (psig RD)} :
    LinDiagram k a b →ₗ[k] LinDiagram k (Omega.obj RD a) (Omega.obj RD b) :=
  Finsupp.linearCombination k fun d : a ⟶ b =>
    ((Sig.sgn (Diagram.layers d) : ℤ) : k) • LinDiagram.of (Omega.reflD d)

theorem omegaSLin_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    omegaSLin k (Finsupp.single d r) =
      (r * ((Sig.sgn (Diagram.layers d) : ℤ) : k)) • LinDiagram.of (Omega.reflD d) := by
  erw [omegaSLin, Finsupp.linearCombination_single]
  rw [smul_smul]

/-- **`σ̃` of the reflection with inverted orientations is the inversion of orientations with the
sign of `ω̃`**, up to the identifications `σ̃(σ̃(x)) = x`. -/
theorem sigLQ_thetaLin {a b : Obj (psig RD)} (ha : a.WF) (hb : b.WF) (f : LinDiagram k a b) :
    sigLQ RD k sc (thetaLin k f) =
      TRQ RD k sc (Sig.obj_obj _ (omega_obj_wf ha)) (Sig.obj_obj _ (omega_obj_wf hb))
        ((pres RD k sc).lin (omegaSLin k f)) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, sigLQ_zero, map_zero, Presentation.lin_zero, map_zero]
  | add f g hf hg => rw [map_add, sigLQ_add, hf, hg, map_add, Presentation.lin_add, map_add]
  | single d r =>
    change sigLQ RD k sc (Finsupp.mapDomain thetaD (Finsupp.single d r)) = _
    rw [Finsupp.mapDomain_single, sigLQ_single, omegaSLin_single, Presentation.lin_smul,
      Presentation.lin_of, map_smul, TRQ_diag, layers_thetaD, smul_smul]
    have hs : Sig.sgn ((Diagram.layers d).map (Sig.rlay ∘ Omega.rlay)) =
        Sig.sgn (Diagram.layers d) := by
      rw [← List.map_map, Sig.sgn_map_rlay, Omega.sgn_map_rlay]
    rw [hs, mul_comm]
    congr 1
    apply (pres RD k sc).diag_eq_of_layers_eq
    simp only [Sig.layers_reflD, layers_thetaD, Diagram.layers_cast, Omega.layers_reflD,
      List.map_map]
    refine List.map_congr_left fun L hL => ?_
    exact Sig.rlay_rlay _ (Omega.rlay_valid (Sig.chain_mem (Diagram.chain d) hL).1)

/-- **The inversion of orientations (with the sign of `ω̃`) of a linear combination of diagrams
that vanishes in `U_Q(g)` vanishes in `U_{Q^θ}(g)`** (`r = 1`; the source object is well
formed). -/
theorem lin_omegaSLin_eq_zero {a b : Obj (psig RD)} (f : LinDiagram k a b) (ha : a.WF)
    (hf : (pres RD k sc).lin f = 0) :
    (pres RD k (thetaScalars RD sc)).lin (omegaSLin k f) = 0 := by
  by_cases he : IsEmpty (a ⟶ b)
  · rw [show f = 0 from Finsupp.ext (α := a ⟶ b) fun d => (IsEmpty.false d).elim, map_zero,
      Presentation.lin_zero]
  obtain ⟨d⟩ := not_isEmpty_iff.1 he
  have hb := (Diagram.chain d).wf ha
  have h₁ := lin_thetaLin_eq_zero sc f ha hf
  rw [← pres_thetaScalars] at h₁
  have h₂ := sigLQ_eq_zero_of_lin (sc := thetaScalars RD sc) h₁
  rwa [sigLQ_thetaLin _ ha hb, TRQ_eq_zero] at h₂

end CLQ

end Categorification.KL3.Diagram
