/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Rescale
import Categorification.Diagrams.CL.DownKLR
import Categorification.WeightedKLR.RedStrands.DoubleBlackDiagram

/-!
# Downward crossing scalars in the all-down comparison

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§2.2, Definition 2.4 and (2.6e), and §4.6, Lemma 4.29, use the original `Q`
on downward Stendhal diagrams. Cautis–Lauda, arXiv:1111.1431v3, Definition 1.1
and §2.2, use their dual parameters for the normalized `F` crossings.
The vertical-axis reflection used in `DoubleBlackDiagram` swaps the two
colours and the two dot positions. It leaves the dual quadratic polynomial
after those swaps. Rescaling the two crossings by `tᵢⱼ` and `tⱼᵢ` recovers
the ordinary quadratic and divided-difference polynomials. The right mate
of the upward crossing already has this rescaling. Its left mate has the
relative factor `tⱼᵢ / tᵢⱼ`.

For two disconnected colours over `ℚ`, `tᵢⱼ = tⱼᵢ = 2` gives constants `2`
and `1/2`. Imposing both formulas on the same unscaled bigon kills its
boundary identity. This tests the comparison with normalized CL generators.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory MvPolynomial QuantumGroup QuantumGroup.UDot KL3.Diagram KL3.Diagram.CL
  StringDiagrams
open scoped Matrix

universe w u v

variable {I : Type u} {C : CartanDatum I} {k : Type w} [CommRing k]

/-- The quadratic polynomial for a reflected normalized CL downward crossing, read
with the physical left dot first. The reversal of the word reverses the dot positions. -/
theorem reflectedDownward_qCL (S : CLScalars C k) (i j : I) :
    rename ![(1 : Fin 2), 0] (qCL S.dual j i) =
      MvPolynomial.C (((S.t i j * S.t j i)⁻¹ : kˣ) : k) * qCL S i j := by
  rw [rename_swap_qCL, qCL_dual, mul_inv_rev, mul_comm ((S.t j i)⁻¹)]

/-- The product of the crossing rescalings converts the reflected CL quadratic
coefficient to the coefficient in Webster v3, Definition 2.4, (2.6e). -/
theorem rescaledDownward_qCL (S : CLScalars C k) (i j : I) :
    MvPolynomial.C ((S.t i j * S.t j i : kˣ) : k) *
      rename ![(1 : Fin 2), 0] (qCL S.dual j i) = qCL S i j := by
  rw [reflectedDownward_qCL, ← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, map_one, one_mul]

/-- The same crossing rescalings convert the divided-difference polynomial used
in the downward braid relation. -/
theorem rescaledDownward_qbar (S : CLScalars C k) (i j : I) :
    MvPolynomial.C ((S.t i j * S.t j i : kˣ) : k) *
      KLR.qbar (rename ![(1 : Fin 2), 0] (qCL S.dual j i)) = KLR.qbar (qCL S i j) := by
  rw [← RescaleDatum.qbar_C_mul, rescaledDownward_qCL]

section Mates

variable {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (S : CLScalars C k)

set_option backward.isDefEq.respectTransparency false in
/-- For the physical downward crossing with bottom `[Fᵢ,Fⱼ]`, choose the
normalization given by `presCL_rotCrossR`. The other mate of the upward
crossing has the indicated relative scalar. The CL word `[Fⱼ,Fᵢ]` reads
`[Fᵢ,Fⱼ]` after the reflection in `DoubleBlackDiagram`. -/
theorem downward_leftMate_eq_smul_rightMate (i j : I) (μ : X) :
    (presCL RD k S).diag (rotCrossL RD j i μ) =
      ((S.t j i : k) * (((S.t i j)⁻¹ : kˣ) : k)) • (presCL RD k S).diag (rotCrossR RD j i μ) := by
  have h := (presCL RD k S).lin_rel_self (.inr (.cycCrossL j i μ))
  change (presCL RD k S).lin
    ((((S.t j i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j i μ) -
      LinDiagram.of (downCross RD j i μ)) = 0 at h
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    sub_eq_zero] at h
  rw [presCL_rotCrossR, tauCL, smul_smul, mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, mul_one, ← h,
    smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Mates

section Disconnected

private abbrev disconnected : CartanDatum Bool := CartanDatum.ofGraph (⊥ : SimpleGraph Bool)

private def twoScalars : CLScalars disconnected ℚ where
  t i j := if i = j then 1 else Units.mk0 2 (by norm_num)
  s _ _ _ _ := 0
  r _ := 1
  t_self _ := by simp
  t_symm i j _ := by simp [eq_comm]
  s_symm _ _ _ _ := rfl

/-- The ordinary and reflected normalized CL quadratic polynomials can differ even
in disconnected rank two. The original scalar is `2` and the dual scalar is `1/2`. -/
theorem disconnected_downward_quadratics :
    qCL twoScalars false true = MvPolynomial.C (2 : ℚ) ∧
    rename ![(1 : Fin 2), 0] (qCL twoScalars.dual true false) = MvPolynomial.C (1 / 2 : ℚ) := by
  have h : disconnected.dot false true = 0 := rfl
  rw [rename_swap_qCL, qCL_of_dot_eq_zero _ h, qCL_of_dot_eq_zero _ h]
  constructor
  · rfl
  · change MvPolynomial.C (((twoScalars.t true false)⁻¹ : ℚˣ) : ℚ) = _
    simp [twoScalars, Units.val_inv_eq_inv_val, one_div]

variable {A : Type*} [Category* A] [Preadditive A] [Linear ℚ A]

/-- At the disconnected rank-two parameters of `disconnected_downward_quadratics`, a
comparison imposing both quadratic formulas on the same bigon kills the boundary identity. -/
theorem id_eq_zero_of_disconnected_unscaled_bigons {a b : A} (f : a ⟶ b) (g : b ⟶ a)
    (h₁ : f ≫ g = (2 : ℚ) • 𝟙 a) (h₂ : f ≫ g = (1 / 2 : ℚ) • 𝟙 a) : 𝟙 a = 0 := by
  have he : (2 - 1 / 2 : ℚ) • 𝟙 a = 0 := by rw [sub_smul, ← h₁, ← h₂, sub_self]
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

end Disconnected

end Categorification.Stendhal.DoubleDiagram
