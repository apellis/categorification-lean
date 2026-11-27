/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerBasis
import Categorification.WeightedKLR.Rigidity.CupCapMidTriple

/-!
# The basis of the model indexed by Webster's triples

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17, for the cap after the red strand `λ_j`. When `L`
is supported on the loadings with `μ` first and `μ*` last (each other idempotent `e(t)` acts by
zero on `L`), the pieces `L e(t)` with `t` not cap-good vanish, and the basis of the model
(`midModelBasis`) is indexed by Webster's index set of `B″`: the triples of an element of the
basis `B` of `T̃^λ`, an element `b′` of a basis `B′` of `L` (through a basis of each `L e(t)`)
and a shuffle of the bottom of `b′` with the `j`-th black block of the bottom of the element of
`B` (`midTripleBasis`).

The elements of this basis are those of `midModelBasis`, the elements `b′ γ_g` of the model;
they are not claimed to be the diagrams of `B″` that Webster draws (the maximum placed after the
black block and the strands of `b` passing under it).

## Main results

* `CupCap.idemPart_eq_bot_of_not_isCapGood`: `L e(t) = 0` for `t` not cap-good.
* `CupCap.midTripleBasis`: the basis of the model indexed by Webster's triples.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

/-- The idempotent `e(t)` of `T̃^{(μ,μ*)}` is the image of the KLR idempotent. -/
theorem cupMap_e_of_isRedOrdered (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t) :
    cupMap k Q Λc ν₀ (KLRAlgebra.e t) = StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht :=
  Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem t).trans (ite_eq_left ht))

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The pieces `L e(t)` vanish for `t` not cap-good** when `L` is supported on the cap-good
loadings. -/
theorem idemPart_eq_bot_of_not_isCapGood
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t) (hc : ¬ IsCapGood ν₀ t) :
    BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  rw [BalancedTensor.mem_idemPart, ← cupMap_e_of_isRedOrdered t ht] at hv
  rw [← hv]
  exact hL t v hc

variable {L}

/-- The index of a basis of a zero piece is empty. -/
theorem isEmpty_of_basis_idemPart [Nontrivial k]
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    {ι : Type*} (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t) (hc : ¬ IsCapGood ν₀ t)
    (B : Module.Basis ι k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    IsEmpty ι := by
  have h := idemPart_eq_bot_of_not_isCapGood L hL t ht hc
  refine ⟨fun x => B.ne_zero x (Subtype.ext ?_)⟩
  have hx : ((B x : _) : L) ∈ (⊥ : Submodule k L) := h ▸ (B x).2
  exact (Submodule.mem_bot k).1 hx

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- The pairs `(g, b′)` of `midModelBasis` are the pairs of a cap-good generator and an element
of `B′_t`, hence (`midTripleEquiv`) the triples with an element of `B′_t`. -/
def midTripleIndexEquiv [Nontrivial k]
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))) :
    (Σ g : MidGen j hj ν ν₀, ι ⟨g.t, g.ht⟩) ≃ Σ τ : MidTriple ℓ j ν ν₀, ι ⟨τ.t, τ.ht⟩ :=
  have hcap : ∀ x : Σ g : MidGen j hj ν ν₀, ι ⟨g.t, g.ht⟩, IsCapGood ν₀ x.1.t := fun x =>
    by_contra fun hc => (isEmpty_of_basis_idemPart hL x.1.t x.1.ht hc (B' ⟨x.1.t, x.1.ht⟩)).false
      x.2
  ((Equiv.subtypeUnivEquiv hcap).symm.trans
    (Equiv.subtypeSigmaEquiv (fun g : MidGen j hj ν ν₀ => ι ⟨g.t, g.ht⟩)
      fun g => IsCapGood ν₀ g.t)).trans
    (Equiv.sigmaCongrLeft (β := fun g : {g : MidGen j hj ν ν₀ // IsCapGood ν₀ g.t} =>
      ι ⟨g.1.t, g.1.ht⟩) (midTripleEquiv j hj ν ν₀)).symm

variable (j hj Q Λ Λc ν ν₀ L ρ₃) in
/-- **The basis of `K̃^{λ⁺}_λ` for a cap after `λ_j`, indexed by Webster's `B″`**
(arXiv:1309.3796v3, Lemma 7.17, for symmetric `Q`, on the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}`).
For `L` supported on the loadings with `μ` first and `μ*` last and bases `B′_t` of the pieces
`L e(t)`, the basis `midModelBasis` is indexed by the triples `(b, b′, shuffle)` of Webster's
index set: `b = x^d ψ_w e(i)` a term of the basis of `T̃^λ` with dots on top, `b′ ∈ B′_t`, and a
shuffle of `t` with the `j`-th black block of `i` (`MidTriple`). Its elements are the elements
`b′ γ_g` of `midModelBasis` for the generator `g` of the triple; in `K̃^{λ⁺}_λ` they are Webster's
diagrams of `B″` (`midCapBasis_apply`). -/
def midTripleBasis [DecidableEq (MidGen j hj ν ν₀)] [Nontrivial k] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2)))) :
    Module.Basis (Σ τ : MidTriple ℓ j ν ν₀, ι ⟨τ.t, τ.ht⟩) k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  (midModelBasis j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ B').reindex (midTripleIndexEquiv hL B')

theorem midTripleBasis_apply [DecidableEq (MidGen j hj ν ν₀)] [Nontrivial k] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    {ι : {t : Seq (stendhalWeight 2 ν₀) // IsRedOrdered t} → Type*}
    (B' : ∀ t, Module.Basis (ι t) k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t.1 t.2))))
    (x : Σ τ : MidTriple ℓ j ν ν₀, ι ⟨τ.t, τ.ht⟩) :
    midTripleBasis j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ hL B' x =
      midModelBasis j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ B' ((midTripleIndexEquiv hL B').symm x) :=
  Module.Basis.reindex_apply _ _ _

end Categorification.Stendhal.CupCap
