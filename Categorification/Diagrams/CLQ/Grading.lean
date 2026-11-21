/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Presentation
import Categorification.Diagrams.KL3.Grading
import Categorification.Diagrams.CL.Homogeneous

/-!
# The grading of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1: the 2-morphisms of `U` are graded, with the degrees of the generators listed in
item ii) (`deg`, `Categorification.Diagrams.KL3.Basic`), and the relations are homogeneous.

This file checks that every defining relation of `pres RD k sc` is homogeneous for `deg`
(`pres_isHomogeneous`), so that the library's grading theory applies: every Hom-space of `U`
is the direct sum of its homogeneous components (`Presentation.isInternal_homDeg`), i.e. the
2-morphisms of degree `t - t'` are KL III's `Hom_U(x{t}, y{t'})`. The degrees of the relations
are:

* zigzags, cyclicity of dots and crossings, sideways double crossings: `0`, `i·i`, `-i·j`, `0`;
* bubbles: a clockwise (counterclockwise) bubble with `m` dots has degree `2 d_i (m + 1 ∓ n)`;
* curls: `∓2 d_i n` (right/left curl); decompositions of `1_{EF}`, `1_{FE}`: `0`;
* `R(ν)`-relations: the degrees of the KLR relations with `deg x = i·i`, `deg ψ = -i·j`.

The homogeneity of the relations involving fake bubbles checks that the infinite Grassmannian
recursion (`grassInv`) produces bubbles of the degrees predicted by KL III.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)












variable {RD}


















/-! ### Homogeneous linear combinations -/

variable {k sc}

local notation "HD" => LinDiagram.homDeg k (deg RD)













/-! ### The `R(ν)`-relations -/

theorem pres_isHomogeneous : (pres RD k sc).IsHomogeneous (deg RD) :=
  CL.presCL_isHomogeneous RD sc.withRone

/-- Every Hom-space of `U` is the direct sum of its homogeneous components. -/
theorem isInternal_homDeg (a b : Obj (psig RD)) :
    DirectSum.IsInternal ((pres RD k sc).homDeg (deg RD) a b) :=
  Presentation.isInternal_homDeg pres_isHomogeneous a b

end Categorification.KL3.Diagram.CLQ
