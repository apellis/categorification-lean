/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryOmega

/-!
# The reflection with inverted orientations

Khovanov–Lauda, arXiv:0807.3250v1, §3.3.2: the composite `σ̃ ω̃` of the reflection `σ̃` in a
vertical axis and the inversion `ω̃` of orientations. Each of them multiplies a diagram by
`(-1)^{#ii-crossings}` and negates the weights, so their composite maps a diagram to its
reflection with inverted orientations, with no sign and the same weights (`lin_thetaLin`).
In particular the reflection with inverted orientations of a linear combination of diagrams
that vanishes in `U` vanishes in `U` (`lin_thetaLin_eq_zero`).

This is the form in which the black relations of Webster's double diagrams
(arXiv:1309.3796v3, Definition 4.24) are transferred to a representation of `U` in the proof
of Theorem 4.25: they are the reflected relations of `U`, and the reflection with inverted
orientations identifies them with relations of `U` on the same regions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-- The object reflected with inverted orientations. -/
abbrev thetaObj (a : Obj (psig RD)) : Obj (psig RD) := Sig.obj RD (Omega.obj RD a)

/-- A diagram reflected in a vertical axis, with inverted orientations. -/
def thetaD {a b : Obj (psig RD)} (d : a ⟶ b) : thetaObj a ⟶ thetaObj b :=
  Sig.reflD (Omega.reflD d)

@[simp] theorem layers_thetaD {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.layers (thetaD d) = (Diagram.layers d).map (Sig.rlay ∘ Omega.rlay) := by
  simp [thetaD, List.map_map]

variable (k) in
/-- The reflection with inverted orientations of linear combinations of diagrams. -/
def thetaLin {a b : Obj (psig RD)} :
    LinDiagram k a b →ₗ[k] LinDiagram k (thetaObj a) (thetaObj b) :=
  Finsupp.lmapDomain k k thetaD

/-- The targets of the relations of `U` are well formed. -/
theorem pres_cod_wf (r : (pres RD k).Rel) : ((pres RD k).cod r).WF := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · exact Pivotal.colourObj_wf _ c
  · exact Pivotal.dualObj_wf _ c
  · cases r <;> exact ob_wf RD _ _

variable [DecidableEq I]

/-- **`σ̃ ω̃` is the unsigned reflection with inverted orientations.** -/
theorem lin_thetaLin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k).lin (thetaLin k f) =
      (sigU RD k).map ((omegaU RD k).map ((pres RD k).lin f)) := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
  | zero => simp
  | add f g hf hg => rw [map_add, lin_add, hf, hg, lin_add, Functor.map_add, Functor.map_add]
  | single d c =>
    change (pres RD k).lin (Finsupp.mapDomain thetaD (Finsupp.single d c)) = _
    rw [Finsupp.mapDomain_single, lin_single, lin_single,
      Functor.map_smul, Functor.map_smul, omegaU_diag, Functor.map_smul, sigU_diag,
      Omega.layers_reflD, Omega.sgn_map_rlay]
    have hs : ((Sig.sgn (Diagram.layers d) : ℤ) : k) * ((Sig.sgn (Diagram.layers d) : ℤ) : k) = 1 :=
      by rw [← Int.cast_mul, Sig.sgn_sq, Int.cast_one]
    simp only [smul_smul, hs, mul_one]
    rfl

/-- The reflection with inverted orientations of a linear combination of diagrams that vanishes
in `U` vanishes in `U`. -/
theorem lin_thetaLin_eq_zero {a b : Obj (psig RD)} {f : LinDiagram k a b}
    (hf : (pres RD k).lin f = 0) : (pres RD k).lin (thetaLin k f) = 0 := by
  rw [lin_thetaLin, hf, Functor.map_zero, Functor.map_zero]

end Categorification.KL3.Diagram
