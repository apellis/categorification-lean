import Categorification

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails. Where cheap, a second
`example` records that the conclusion is not degenerate.

Data: `sl₂` (`UDot.sl2RootDatum`), `sl₃` (`Flag.slRootDatum 2`), a Cartan datum of type `B₂`
(defined below, so that the non-simply-laced case is exercised), and the unfurled datum of one
arrow `false → true` for Kang–Kashiwara Theorem 5.2.

For the Cautis–Lauda condition `(BB_w)` (`TwoRep.StrongSl2.bbw`): the strong `sl₂`
2-representation `TwoRep.Grassmannian.l2` on the cohomology rings of `Gr(0,2)`, `Gr(1,2)`,
`Gr(2,2)` (the categorification of the irreducible representation of highest weight `2`).
`TwoRep.StrongSl2.adjHyp` (CL Prop. 3.9) is not covered: it also needs shift coherence and
idempotent-complete Hom categories, which are not yet established for that bicategory.
-/

open Categorification CategoryTheory QuantumGroup UDot

noncomputable section

namespace NonVacuity

/-! ### Data -/

/-- A Cartan datum of type `B₂`: `0 · 0 = 2`, `1 · 1 = 4`, `0 · 1 = -2`. -/
def cB2 : CartanDatum (Fin 2) where
  dot := ![![2, -2], ![-2, 4]]
  symm := by decide
  dot_self_pos := by decide
  dot_self_even i := by fin_cases i <;> decide
  dot_nonpos := by decide
  dvd_two_mul i j := by fin_cases i <;> fin_cases j <;> decide

/-! ### Khovanov–Lauda I, Theorem 1.1 (`sl₃`) -/

example : Function.Bijective
    (KLR.KLGamma.gammaInt' ℚ (Flag.slGraph 2) (KL.gabberKac (Flag.slGraph 2))) :=
  KLR.KLGamma.theorem_1_1_unconditional ℚ (Flag.slGraph 2)

/-! ### Khovanov–Lauda II, Theorem 8 (`B₂`) -/

example : Function.Bijective (KLR.KL2Gamma.gammaInt2' ℚ cB2 cB2.quantumGabberKac) :=
  KLR.KL2Gamma.theorem_8_unconditional ℚ cB2

/-! ### Quantum Gabber–Kac (`sl₃`, `B₂`) -/

example : (Flag.slCartan 2).QuantumGabberKac := CartanDatum.quantumGabberKac _

example : cB2.QuantumGabberKac := cB2.quantumGabberKac

/-! ### Khovanov–Lauda III, Theorems 1.1–1.2 and nondegeneracy -/

example : KL3.Diagram.CalculusNondeg sl2RootDatum (ZMod 2) := KL3.Diagram.calculusNondeg _ _

example : KL3.Diagram.CalculusNondeg (Flag.slRootDatum 2) ℚ := KL3.Diagram.calculusNondeg _ _

section Gamma

attribute [local instance] KLR.KLGamma.vAlgebra

example := KL3.Diagram.gammaAlg_surjective_unconditional (RD := sl2RootDatum) (k := ℚ)

example := KL3.Diagram.gammaAlg_surjective_unconditional (RD := Flag.slRootDatum 2) (k := ZMod 3)

example := KL3.Diagram.gammaAlg_injective_unconditional sl2RootDatum (ZMod 3)

example : AUD sl2RootDatum vQ ≃+* KL3.Diagram.K0All sl2RootDatum ℚ :=
  KL3.Diagram.gammaAlgEquiv_unconditional sl2RootDatum ℚ

example : AUD (Flag.slRootDatum 2) vQ ≃+* KL3.Diagram.K0All (Flag.slRootDatum 2) (ZMod 2) :=
  KL3.Diagram.gammaAlgEquiv_sl (ZMod 2) 2

end Gamma

/-! ### Kang–Kashiwara, Theorem 5.2 (one arrow `false → true`, level `Λ = ω_false + ω_true`) -/

section KangKashiwara

open KLR.Unfurling

/-- One arrow `false → true`: the unfurled datum of type `A₂`. -/
def arr : Bool → Bool → ℕ := fun a b => if a = false ∧ b = true then 1 else 0

/-- The weight `Λ` with `⟨h_a, Λ⟩ = 1` for both colours. -/
def lam : (Bool → ℤ) × (Bool →₀ ℤ) := (fun _ => 1, 0)

theorem hΛ : ∀ i, ((Polynomial.X : Polynomial ℚ).natDegree : ℤ) =
    (coverWeight arr).pair ((coverWeight arr).iY i) lam := by
  intro i; rw [coverWeight_pair_iY]; simp [lam]

example := KLR.CyclotomicAction.blockLoc (k := ℚ) (Q := unfQ arr) (a := fun _ => Polynomial.X)
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (fun _ => Polynomial.monic_X)
  (coverWeight arr) lam hΛ (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h)
  true (γ := 0) rfl rfl

example := KLR.CyclotomicAction.blockBoundary (k := ℚ) (Q := unfQ arr) (a := fun _ => Polynomial.X)
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (fun _ => Polynomial.monic_X)
  (coverWeight arr) lam hΛ (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h)
  false (β := 0) (by simp) rfl

end KangKashiwara

/-! ### Cautis–Lauda, `(BB_w)` (strong `sl₂` 2-representation on `Gr(•,2)`) -/

example : (TwoRep.Grassmannian.l2 ℚ).BBw := TwoRep.StrongSl2.bbw _

/-- The weight-`0` object `H*(Gr(1,2)) = H*(ℙ¹)` is nonzero. -/
example : ¬ Limits.IsZero (𝟙 ((TwoRep.Grassmannian.l2 ℚ).obj 1)) :=
  TwoRep.Grassmannian.not_isZero_id_l2Obj_one

end NonVacuity
