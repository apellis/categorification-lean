/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingTransport
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

set_option backward.isDefEq.respectTransparency false

/-!
# Injectivity of pulling red strands left across black strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 5.23:
the map `P_κ^i → P_0^i` given by right multiplication with the diagram `θ_κ` that pulls red
strands left across black strands is injective.

`θ_κ` is a product of single red-black crossings. A single crossing of a red strand over a
black strand `i`, inside a loading, is obtained from the crossing at the last red strand with
the black strand `i` immediately to its right (`redCrossIdem`, `firstIndAffine`; proved
injective in `redCross_eq_zero`) by adding black strands on the right (`appendBlackNU`), adding
red strands on the right (`emptyRedHom`) and identifying equal black weights
(`castTensorProductAlgebra`). `IsRedBlackCrossing` records such pairs `(e, c)` of an idempotent
`e` and a crossing `c`; for them `x e = x` and `x c = 0` force `x = 0`
(`IsRedBlackCrossing.eq_zero`). A product of crossings `c₁ ⋯ cₙ` whose consecutive idempotents
match (`cⱼ e_{j+1} = cⱼ`) is then injective on `T e₁` (`eq_zero_of_mul_crossingChain`).

These hold at the standard Khovanov–Lauda parameters `Q = CL.qCL kl`, for every Rouquier
datum, with no route hypothesis: injectivity of `δ₁` comes from the dimension count
(`firstIndDeltaInjective_std`), and induction along both kinds of strand addition preserves
injections (`appendBlack_ind_map_injective`, `emptyRed_lIdeal_ind_map_injective`).

## Main results

* `IsRedBlackCrossing.eq_zero`: one red-black crossing, in any position, is injective.
* `eq_zero_of_mul_crossingChain`: Lemma 5.23, a product of crossings is injective.
-/

noncomputable section

namespace Categorification.InductionAlong

/-- Transport of `x e = x, x c = 0 ⇒ x = 0` along a ring isomorphism. -/
theorem eq_zero_of_mul_ringEquiv {A B : Type*} [Ring A] [Ring B] (φ : A ≃+* B) {e c : A}
    (h : ∀ x : A, x * e = x → x * c = 0 → x = 0) (x : B) (hx : x * φ e = x)
    (h0 : x * φ c = 0) : x = 0 := by
  have h' := h (φ.symm x) (φ.injective (by rw [map_mul, φ.apply_symm_apply, hx]))
    (φ.injective (by rw [map_mul, φ.apply_symm_apply, h0, map_zero]))
  rw [← φ.apply_symm_apply x, h', map_zero]

end Categorification.InductionAlong

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
open scoped Classical

variable {I : Type} {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

local notation "Si" j => (Singleton.singleton j : Multiset I)

/-- Pairs `(e, c)` of an idempotent `e` and a single crossing `c` of a red strand over a black
strand, in an arbitrary position of a loading: the crossing at the last red strand
(`crossing`), extended by black strands (`appendBlack`) and red strands (`addRed`) on the right
and transported along equalities of black weights (`cast`). -/
inductive IsRedBlackCrossing : {m : ℕ} → (Λ : Fin m → I →₀ ℕ) → (ν : Multiset I) →
    TensorProductAlgebra k Q Λ ν → TensorProductAlgebra k Q Λ ν → Prop
  | crossing {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
      (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
      IsRedBlackCrossing Λ ((Si i) + (θ + 0)) (redCrossIdem Q Λ i θ s hs)
        (firstIndAffine Q Λ i θ 0 (firstG (stendhalQ Q Λ)
          (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
          (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
            (stendhalWeight 1 0)) (Sum.inl i : I ⊕ Fin (ℓ + 1))))
  | appendBlack {m : ℕ} {Λ : Fin m → I →₀ ℕ} {ν : Multiset I} (j : I)
      {e c : TensorProductAlgebra k Q Λ ν} :
      IsRedBlackCrossing Λ ν e c →
        IsRedBlackCrossing Λ ((Si j) + ν) (appendBlackNU (Q := Q) (Λ := Λ) j ν e)
          (appendBlackNU (Q := Q) (Λ := Λ) j ν c)
  | addRed {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {θ : Multiset I}
      {e c : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (θ + 0)} :
      IsRedBlackCrossing (Λ ∘ Fin.castSucc) (θ + 0) e c →
        IsRedBlackCrossing Λ (θ + 0) (emptyRedHom Q Λ θ e) (emptyRedHom Q Λ θ c)
  | cast {m : ℕ} {Λ : Fin m → I →₀ ℕ} {ν ν' : Multiset I} (h : ν = ν')
      {e c : TensorProductAlgebra k Q Λ ν} :
      IsRedBlackCrossing Λ ν e c →
        IsRedBlackCrossing Λ ν' (castTensorProductAlgebra Q Λ h e)
          (castTensorProductAlgebra Q Λ h c)

theorem isIdempotentElem_redCrossIdem {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
    (θ : Multiset I) (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    IsIdempotentElem (redCrossIdem Q Λ i θ s hs) := by
  have h₀ : IsIdempotentElem (leftAppendHom Q Λ i θ 0
      ((emptyFactorToOld Q Λ θ).symm (oldIdem Q Λ θ s hs))) :=
    ((isIdempotentElem_mk_e s hs).map (emptyFactorToOld Q Λ θ).symm).map
      (leftAppendHom Q Λ i θ 0)
  have h₁ : IsIdempotentElem (redFactorHom Q Λ i θ (leftAppendHom Q Λ i θ 0
      ((emptyFactorToOld Q Λ θ).symm (oldIdem Q Λ θ s hs)))) := by
    unfold IsIdempotentElem
    rw [← redFactorHom_mul, h₀.eq]
  exact h₁.map _

/-- `T^{λ'} e(s)` is finite-dimensional. -/
theorem finiteDimensional_redFactorModule {C : CartanDatum I} (hQ : IsRouquierQ C Q) {ℓ : ℕ}
    (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ : Multiset I) (s : Seq (stendhalWeight ℓ (θ + 0)))
    (hs : IsRedOrdered s) :
    FiniteDimensional k (redFactorModule Q Λ θ s hs).carrier := by
  have := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) (θ + 0) hQ
  exact inferInstanceAs (FiniteDimensional k ((lIdeal (oldIdem Q Λ θ s hs)).restrictScalars k))

variable {C : CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

include hR hQs in
/-- **One red-black crossing is injective** (Webster, arXiv:1309.3796v2, Lemma 5.23, one
crossing), at the standard Khovanov–Lauda parameters: `e` is idempotent, and `x e = x`,
`x c = 0` force `x = 0`. -/
theorem IsRedBlackCrossing.eq_zero {m : ℕ} {Λ : Fin m → I →₀ ℕ} {ν : Multiset I}
    {e c : TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν}
    (h : IsRedBlackCrossing (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν e c) :
    IsIdempotentElem e ∧ ∀ x, x * e = x → x * c = 0 → x = 0 := by
  induction h with
  | crossing Λ i θ s hs =>
    refine ⟨isIdempotentElem_redCrossIdem _ Λ i θ s hs, fun x hx h0 => ?_⟩
    have := finiteDimensional_redFactorModule _ hR Λ θ s hs
    exact redCross_eq_zero _ Λ i θ s hs hQs
      (firstIndDeltaInjective_std hR hQs i θ 0 _) x hx h0
  | @appendBlack m Λ ν j e c _ ih =>
    exact ⟨ih.1.map _, fun x hx h0 => eq_zero_of_mul_map
      (appendBlackNU (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Λ) j ν) ih.1 c
      (appendBlack_ind_map_injective C hR (rmulLIdeal_injective ih.2)) x hx h0⟩
  | @addRed ℓ Λ θ e c _ ih =>
    exact ⟨ih.1.map _, fun x hx h0 => eq_zero_of_mul_map
      (emptyRedHom (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ) ih.1 c
      (emptyRed_lIdeal_ind_map_injective (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ hQs
        (rmulLIdeal_injective ih.2)) x hx h0⟩
  | @cast m Λ ν ν' hν e c _ ih =>
    exact ⟨ih.1.map _, eq_zero_of_mul_ringEquiv
      (castTensorProductAlgebra _ Λ hν).toRingEquiv ih.2⟩

end Categorification.Stendhal

namespace Categorification.InductionAlong

variable {A : Type*} [Ring A]

/-- **A product of injective crossings is injective**: for pairs `(eⱼ, cⱼ)` such that
`x eⱼ = x`, `x cⱼ = 0` force `x = 0`, and with `cⱼ e_{j+1} = cⱼ`, `x e₁ = x` and
`x c₁ ⋯ cₙ = 0` force `x = 0`. -/
theorem eq_zero_of_mul_crossingChain (p : A × A) (l : List (A × A))
    (hstep : ∀ q ∈ p :: l, ∀ x : A, x * q.1 = x → x * q.2 = 0 → x = 0)
    (hchain : List.IsChain (fun q r : A × A => q.2 * r.1 = q.2) (p :: l)) (x : A) (hx : x * p.1 = x)
    (h0 : x * ((p :: l).map Prod.snd).prod = 0) : x = 0 := by
  induction l generalizing p x with
  | nil => exact hstep p (by simp) x hx (by simpa using h0)
  | cons q l ih =>
    rw [List.isChain_cons] at hchain
    have hy : x * p.2 = 0 := by
      refine ih q (fun r hr => hstep r (List.mem_cons_of_mem _ hr)) hchain.2 (x * p.2)
        (by rw [mul_assoc, hchain.1 q (by simp)]) ?_
      rw [List.map_cons, List.prod_cons, ← mul_assoc] at h0
      exact h0
    exact hstep p (by simp) x hx hy

end Categorification.InductionAlong
