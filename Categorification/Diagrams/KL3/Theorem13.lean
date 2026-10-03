/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepSln
import Categorification.Diagrams.KL3.GabberKacWrappers

/-!
# Khovanov–Lauda III, Theorem 1.3: `U(sl_n)` is nondegenerate over any field

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1 (TeX source
`sln-2008-ArXiv.tex`), Theorem 1.3 (label `thm-nondegenerate`, l. 1274): "The graphical calculus
is nondegenerate for the root datum of `sl_n` and any field `𝕜`", and Proposition 1.4 (label
`prop-iso`): "The map `γ` is an isomorphism for the root datum of `sl_n` and any field `𝕜`".

The proof (KL III §6.4, l. 9598–9790) reduces nondegeneracy to positive sequences and then to
the linear independence of the spanning family `B_{+i,+j,λ}` of Proposition 3.11
(`positiveNondeg_iff`), which is `Categorification.Flag.Indep.linearIndependent_vB_sln`: the
elements are separated by the 2-representation `Γ_N` of `sl_{n+1}` composed with the embedding
`U(sl_n) → U(sl_{n+1})`, for large `N` (instead of KL III's equivariant `Γ^G_N`; see
`Categorification.Flag.Indep.chernData` for why the extra block is needed in positive
characteristic).

Here `sl_n` is `slRootDatum m` with `n = m + 1`, and `𝕜` is any field.

## Main results

* `simplyLaced_slCartan`: the Cartan datum of `sl_{m+1}` is simply laced;
* `linearIndependent_posB_sl`: the elements of `B_{+i,+j,λ}` of each degree are linearly
  independent;
* **`positiveNondeg_sl`**, **`theorem_1_3`** (`CalculusNondeg (slRootDatum m) 𝕜`): KL III
  Theorem 1.3;
* **`prop_1_4_sl`**, `gammaUA'Equiv_sl`: KL III Proposition 1.4,
  `γ : 1_ρ (_𝒜 U̇(sl_n)) 1_λ → K₀(U̇(λ, ρ))` is bijective (with KL III Proposition 2.5 supplied
  by the quantum Gabber–Kac theorem, `gammaUA'_bijective_unconditional`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams Categorification.QuantumGroup Categorification.QuantumGroup.UDot
  Categorification.Flag Equiv KLR.Diagram

attribute [local instance] KLR.KLGamma.vAlgebra

universe u

variable {K : Type u} [Field K] {m : ℕ}

theorem simplyLaced_slCartan (m : ℕ) : SimplyLaced (slCartan m) := by
  intro i j h
  simp only [slCartan_dot, h, ↓reduceIte]
  split_ifs <;> simp

theorem posPerm_injective {ν : Multiset (Fin m)} {i j : KLR.Seq ν} :
    Function.Injective (posPerm (i := i) (j := j)) := by
  intro σ σ' h
  apply Subtype.ext
  apply (bwE (i := i) (j := j)).injective
  rw [← blockPerm_posPerm, ← blockPerm_posPerm, h]

/-- **The elements of `B_{+i,+j,λ}` of degree `d` are linearly independent** for `sl_{m+1}`, over
any field (KL III §6.4). -/
theorem linearIndependent_posB_sl (μ : Fin m → ℤ) (ν : Multiset (Fin m)) (i j : KLR.Seq ν)
    (d : ℤ) :
    LinearIndependent K fun x : {x : SpanIdx (posW (word i)) (posW (word j)) //
        spanDeg (slCartan m) ((slRootDatum m).ellOf μ) x = d} =>
      posB (slRootDatum m) K μ x.1 := by
  have h := Indep.linearIndependent_vB_sln (K := K) μ ν i j
  let f : {x : SpanIdx (posW (word i)) (posW (word j)) //
      spanDeg (slCartan m) ((slRootDatum m).ellOf μ) x = d} →
      {p : (KLR.Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) ×
        ((Fin m × ℕ) →₀ ℕ) // p.1.1 = i ∧ p.1.2.1 • i = j} :=
    fun x => ⟨((i, posPerm x.1.1, posDots x.1), x.1.2.2), rfl, posPerm_smul x.1.1⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨σ, dx, mx⟩, hx⟩ ⟨⟨σ', dy, my⟩, hy⟩ hxy
    have e := congrArg Subtype.val hxy
    simp only [f, Prod.mk.injEq] at e
    obtain ⟨⟨-, hp, hd⟩, hm⟩ := e
    have hσ : σ = σ' := posPerm_injective hp
    subst hσ hm
    have hdd : dx = dy := funext fun z => by
      obtain ⟨a, rfl⟩ := (posArc_bijective σ).2 z
      have := DFunLike.congr_fun hd a
      simpa [posDots] using this
    subst hdd
    rfl
  exact h.comp f hf

/-- **Nondegeneracy for positive sequences** for `sl_{m+1}` over any field. -/
theorem positiveNondeg_sl (K : Type u) [Field K] (m : ℕ) : PositiveNondeg (slRootDatum m) K :=
  positiveNondeg_iff.2 fun μ _ i j d =>
    linearIndependent_posB_sl μ _ i j d

/-- **Khovanov–Lauda III, Theorem 1.3** (label `thm-nondegenerate`): the graphical calculus is
nondegenerate for the root datum of `sl_{m+1}` and any field `K`. -/
theorem theorem_1_3 (K : Type u) [Field K] (m : ℕ) : CalculusNondeg (slRootDatum m) K :=
  calculusNondeg_of_positive (positiveNondeg_sl K m)

/-- **Khovanov–Lauda III, Proposition 1.4** (label `prop-iso`): for the root datum of `sl_{m+1}`
and any field `K`, `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective. -/
theorem prop_1_4_sl (K : Type u) [Field K] (m : ℕ) (lam ρ : Fin m → ℤ) :
    Function.Bijective
      (gammaUA' (RD := slRootDatum m) (k := K) lam ρ) :=
  gammaUA'_bijective_unconditional (theorem_1_3 K m) lam ρ

/-- `γ` as an isomorphism `1_ρ (_𝒜 U̇(sl_{m+1})) 1_λ ≅ K₀(U̇(λ, ρ))`. -/
def gammaUA'Equiv_sl (K : Type u) [Field K] (m : ℕ) (lam ρ : Fin m → ℤ) :
    LinearMap.range (dpComb (RD := slRootDatum m) lam ρ) ≃ₗ[LaurentPolynomial ℤ]
      K0Kar (slRootDatum m) K ρ lam :=
  gammaUA'Equiv_unconditional (theorem_1_3 K m) lam ρ

end Categorification.KL3.Diagram

end
