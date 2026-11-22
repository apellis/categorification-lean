import Categorification.Spec.KL1.Theorem2_5
import Lean.Util.CollectAxioms

/-! # The one-colour two-strand corner of KL I, Theorem 2.5 -/

namespace Categorification.Spec.KL1

open Equiv MvPolynomial TypeA KLR KLRAlgebra

private abbrev ν : Multiset Unit := {(), ()}
private abbrev Γ : SimpleGraph Unit := ⊥
private def ii : Seq ν := ⟨fun _ => (), by decide⟩

/-- In the integral two-strand corner the crossing has square zero and sliding
a dot across it contributes the boundary idempotent. -/
example :
    (ψ 0 * ψ 0 * e ii : R1 ℤ Γ ν) = 0 ∧
    ((x (ν := ν) ⟨0, by decide⟩ * ψ 0 - ψ 0 * x (ν := ν) ⟨1, by decide⟩) * e ii : R1 ℤ Γ ν) = e ii := by
  constructor
  · simpa [ii] using (ψ_sq (k := ℤ) (Q := klQ Γ) 0 (by decide) ii)
  · simpa [ii] using (dot_cross_left (k := ℤ) (Q := klQ Γ) 0 (by decide) ii)

/-- Apply the headline to this corner and use the basis coordinate indexed by the
identity and no dots to detect a nonzero vector. -/
example : ∃ z : corner (Q := klQ (k := ℤ) Γ) ii ii, z ≠ 0 := by
  obtain ⟨B, _⟩ := theorem_2_5 Γ ν (canWord ν.card)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) ii ii
  let b : CornerIdx ii ii := (⟨1, one_smul _ _⟩, 0)
  exact ⟨B b, B.ne_zero b⟩

open Lean Elab Command in
run_cmd do
  for ax in ← Lean.collectAxioms ``theorem_2_5 do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom in KL I Theorem 2.5: {ax}"

end Categorification.Spec.KL1
