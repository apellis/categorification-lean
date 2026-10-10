/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqModel
import Categorification.KLR.Basic

/-!
# Mixed upward source equations for ungraded Rouquier families

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Definition 1.1, (1.2)--(1.4). `RouqUpKLR` adds just the mixed upward equations to
`RouqFamily`; every field is a whiskered equation in the original bicategory.
There is no interpretation or target-relation predicate among the fields.

* `slide_left`, `slide_right`: (1.2) for distinct labels.
* `square`: (1.3), with variables ordered by the diagram's left/right strands.
* `braid`: (1.4) with distinct outer labels.
* `braidQ`: (1.4) with repeated outer label, using
  `qbar Q (u,v,w) = (Q(u,v) - Q(w,v))/(u-w)`.

Categorical composition reads the diagram word in reverse: `[i,j]` acts on
`E_j ≫ E_i`, and variable zero acts on the diagram's left strand `i`.
The existing single-colour data are unchanged. The dot normalization is `r_i = 1`.
There is no grading, zero-object, Hom-finiteness or `End(1) = k` hypothesis.

`brundanQ` retains all the source's rectangular deformation coefficients.
`CL.qCL` instead filters by weighted degree; they are not interchangeable for
arbitrary coefficients. `brundanQ_eq_qCL` states the precise coefficient restriction
under which the existing CL presentation can be used. This is not an erratum to
Brundan and is not a grading assumption on the target bicategory.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}
/-- Brundan's ungraded mixed KLR polynomial (Definition 1.1, (1.3)).
Unlike `CL.qCL`, the rectangular sum is not filtered by weighted degree.
Only off-diagonal values are used. -/
def brundanQ (Sc : CL.CLScalars C k) (i j : I) : MvPolynomial (Fin 2) k :=
  if C.dot i j = 0 then MvPolynomial.C (Sc.t i j : k)
  else MvPolynomial.C (Sc.t i j : k) * MvPolynomial.X 0 ^ C.dij i j +
    MvPolynomial.C (Sc.t j i : k) * MvPolynomial.X 1 ^ C.dij j i +
    ∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      MvPolynomial.C (Sc.s i j p q) * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q

/-- Compatibility with the existing homogeneous CL presentation is a restriction on
source coefficients, not a grading assumption on the target bicategory. -/
theorem brundanQ_eq_qCL (Sc : CL.CLScalars C k)
    (h : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    brundanQ Sc = CL.qCL Sc := by
  classical
  funext i j
  unfold brundanQ CL.qCL
  split_ifs
  · rfl
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hd
  · rfl
  · rw [h i j p q (Finset.mem_range.1 hp) (Finset.mem_range.1 hq) hd]
    simp

/-- Brundan Definition 1.1 (1.2)--(1.4), the additional upward KLR equations.
The fields are equations in the original bicategory, not predicates on an interpretation.
The polynomial argument permits ungraded, nonhomogeneous parameters. -/
structure RouqUpKLR (S : RouqFamily (B := B) RD)
    (Q : I → I → MvPolynomial (Fin 2) k) : Prop where
  square : ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d),
    S.cross i j h₁ h₂ h₃ h₄ ≫ S.cross j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (S.E j h₁ ≫ S.E i h₂))
        ![S.E j h₁ ◁ S.dot i h₂, S.dot j h₁ ▷ S.E i h₂] (Q i j)
  slide_left : ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d),
    S.E j h₁ ◁ S.dot i h₂ ≫ S.cross i j h₁ h₂ h₃ h₄ =
      S.cross i j h₁ h₂ h₃ h₄ ≫ S.dot i h₃ ▷ S.E j h₄
  slide_right : ∀ (i j : I), i ≠ j → ∀ {a b c d : X}
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d),
    S.dot j h₁ ▷ S.E i h₂ ≫ S.cross i j h₁ h₂ h₃ h₄ =
      S.cross i j h₁ h₂ h₃ h₄ ≫ S.E i h₃ ◁ S.dot j h₄
  braid : ∀ (i j c : I) (_hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = m) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = m)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = m) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅),
    S.E c e1 ◁ S.cross i j e2 e3 e4 e5 ≫
        ((α_ (S.E c e1) (S.E i e4) (S.E j e5)).inv ≫ S.cross i c e1 e4 e6 e7 ▷ S.E j e5 ≫
          (α_ (S.E i e6) (S.E c e7) (S.E j e5)).hom) ≫
        S.E i e6 ◁ S.cross j c e7 e5 e8 e9 =
      ((α_ (S.E c e1) (S.E j e2) (S.E i e3)).inv ≫ S.cross j c e1 e2 e10 e11 ▷ S.E i e3 ≫
          (α_ (S.E j e10) (S.E c e11) (S.E i e3)).hom) ≫
        S.E j e10 ◁ S.cross i c e11 e3 e12 e9 ≫
        ((α_ (S.E j e10) (S.E i e12) (S.E c e9)).inv ≫ S.cross i j e10 e12 e6 e8 ▷ S.E c e9 ≫
          (α_ (S.E i e6) (S.E j e8) (S.E c e9)).hom)
  braidQ : ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c),
    (S.E i h₁ ◁ S.cross i j h₂ h₃ h₄ h₅ ≫
      ((α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).inv ≫
        S.cross i i h₁ h₄ h₁ h₄ ▷ S.E j h₅ ≫
        (α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).hom) ≫
      S.E i h₁ ◁ S.cross j i h₄ h₅ h₂ h₃) -
    (((α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).inv ≫
      S.cross j i h₁ h₂ h₆ h₇ ▷ S.E i h₃ ≫
      (α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).hom) ≫
      S.E j h₆ ◁ S.cross i i h₇ h₃ h₇ h₃ ≫
      ((α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).inv ≫
        S.cross i j h₆ h₇ h₁ h₂ ▷ S.E i h₃ ≫
        (α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).hom)) =
      KLR.ncEval (A := End (S.E i h₁ ≫ (S.E j h₂ ≫ S.E i h₃)))
        ![S.E i h₁ ◁ (S.E j h₂ ◁ S.dot i h₃),
          S.E i h₁ ◁ (S.dot j h₂ ▷ S.E i h₃),
          S.dot i h₁ ▷ (S.E j h₂ ≫ S.E i h₃)] (KLR.qbar (Q i j))

/-- The genuine ungraded mixed upward source data, with Brundan's scalar polynomial. -/
abbrev BrundanUpKLR (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k) : Prop :=
  RouqUpKLR S (brundanQ Sc)

/-- Restrict the source coefficients to the homogeneous CL parameter convention. -/
theorem BrundanUpKLR.toCL {S : RouqFamily (B := B) RD} {Sc : CL.CLScalars C k}
    (H : BrundanUpKLR S Sc)
    (h : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0) :
    RouqUpKLR S (CL.qCL Sc) := by
  rw [← brundanQ_eq_qCL Sc h]
  exact H

end Categorification.TwoRep
