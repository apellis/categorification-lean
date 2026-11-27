/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiStepOne

/-!
# The `Eᵢ` filtration of standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `E`-part: for blocks `b` with `b_0 = 0` and total weight `i + ν₀`, and a
right module `M` over the block algebra `B`, `Eᵢ(M ⊗_B S^L_α)` has a filtration whose
subquotients are the `ₖEᵢ M ⊗_{B'} S^L_{α'}`, one for each `k` with `i` in the block `b_{k+1}`
(`eiFiltration`). It is stated over `T(ν₀) ⊗ C` for an algebra `C` acting on `M` by
`B`-linear maps; `C = k` is Webster's statement.

The proof is by induction on `ℓ`: the case `ℓ = 0` is vacuous (`eiFiltration_zero`), and the
step distinguishes whether `i` occurs in the first `ℓ` blocks, in the last one, or in both
(`eiFiltration_step_left`, `eiFiltration_step_right`, `eiFiltration_step_both`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra ModuleFiltration

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I)

/-- **Webster's Proposition 5.5, `E`-part** (arXiv:1309.3796v3): `Eᵢ` of a standardization is
filtered by the standardizations of the restrictions removing one `i`-strand from one block,
each block containing `i` occurring exactly once. -/
theorem eiFiltration (hQ : KLRSymm Q) : ∀ ℓ, EiFiltration (k := k) Q i ℓ
  | 0 => eiFiltration_zero Q i
  | ℓ + 1 => by
    intro Λ b ν₀ h00 hb hα b' h0 hr hκ hb' hα' C _ _ M _ _ _ _ ρ
    by_cases hiθ : i ∈ initWeight b
    · by_cases hiβ : i ∈ lastBlock b
      · exact eiFiltration_step_both Q i hQ (eiFiltration hQ ℓ) Λ b ν₀ h00 hb hα b' h0 hr hκ
          hb' hα' C M ρ hiθ hiβ
      · exact eiFiltration_step_left Q i hQ (eiFiltration hQ ℓ) Λ b ν₀ h00 hb hα b' h0 hr hκ
          hb' hα' C M ρ hiθ hiβ
    · by_cases hiβ : i ∈ lastBlock b
      · exact eiFiltration_step_right Q i hQ Λ b ν₀ h00 hb hα b' h0 hr hκ hb' hα' C M ρ hiθ hiβ
      · exfalso
        have h1 := hb
        rw [blockPrefix_last] at h1
        have h2 : i ∈ initWeight b + lastBlock b := by
          rw [h1]
          exact Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))
        rcases Multiset.mem_add.1 h2 with h | h
        · exact hiθ h
        · exact hiβ h

end StendhalAlgebra

end Categorification.Stendhal
