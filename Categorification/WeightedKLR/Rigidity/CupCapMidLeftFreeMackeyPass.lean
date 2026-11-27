/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeMackey

/-!
# Staged transparency for several strands

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (steps (I1)–(I2) of the route, in `T̃^{λ⁺}`). If the strands of `s` at positions
`n, …, n + d - 1` are all black, passing them one at a time under the window is an isomorphism
`L ⊗ e_{s,n} T̃^{λ⁺} ≅ L ⊗ e_{s,n+d} T̃^{λ⁺}` of right `T̃^{λ⁺}`-modules when every `κ_i` is a unit
(`posPassEquivIter`). In particular a window anywhere in a run of black strands ending at
`midPos j s` gives a module isomorphic to the staged module at `midPos j s`
(`posModelMidEquiv`), which is a factor of the model of `K̃` (`midModelPiEquiv`).

## Main definitions

* `CupCap.posModelCongr`: the staged modules at equal positions.
* `CupCap.posPassEquivIter`: the composite of `d` single passages.
* `CupCap.posModelMidEquiv`: the staged module at `n` is the staged module at `midPos j s`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (j hj Q Λ Λc ν₀) in
/-- The staged modules at equal positions agree. -/
def posModelCongr (s : Seq (stendhalWeight ℓ ν)) {n n' : ℕ} (hn : n ≤ m) (hn' : n' ≤ m)
    (h : n = n') :
    PosModel j hj Q Λ Λc ν₀ s n hn L ≃ₗ[Tpᵐᵒᵖ] PosModel j hj Q Λ Λc ν₀ s n' hn' L := by
  subst h
  exact LinearEquiv.refl _ _

/-- **Passing `d` black strands under the window, one at a time**, is an isomorphism
`L ⊗ e_{s,n} T̃^{λ⁺} ≅ L ⊗ e_{s,n+d} T̃^{λ⁺}` when every `κ_i` is a unit (Webster,
arXiv:1309.3796v3, §7.3, staged transparency, step (I1) of the left projectivity route). -/
def posPassEquivIter (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) :
    (d : ℕ) → (hd : n + d ≤ m) →
      (∀ q (hq : q < m), n ≤ q → q < n + d → (s.lbl ⟨q, hq⟩).isLeft) →
      (PosModel j hj Q Λ Λc ν₀ s n (by omega) L ≃ₗ[Tpᵐᵒᵖ] PosModel j hj Q Λ Λc ν₀ s (n + d) hd L)
  | 0, _, _ => LinearEquiv.refl _ _
  | d + 1, hd, hb =>
    (posPassEquivIter hP hPL hL hκ s n d (by omega)
      (fun q hq h1 h2 => hb q hq h1 (by omega))).trans
      (posPassRightEquiv L hP hPL hL ((s.lbl ⟨n + d, by omega⟩).getLeft
        (hb (n + d) (by omega) (by omega) (by omega))) s hd
        (Sum.inl_getLeft _ _).symm (hκ _))

variable (j hj Q Λ Λc ν₀) in
/-- **A window in a run of black strands ending at `midPos j s`**: the staged module at `n` is
isomorphic to the staged module at `midPos j s`, a factor of the model of `K̃`, when every `κ_i` is
a unit. -/
def posModelMidEquiv (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n ≤ midPos j s)
    (hb : ∀ q (hq : q < m), n ≤ q → q < midPos j s → (s.lbl ⟨q, hq⟩).isLeft) :
    PosModel j hj Q Λ Λc ν₀ s n (hn.trans (midPos_le j s)) L ≃ₗ[Tpᵐᵒᵖ]
      PosModel j hj Q Λ Λc ν₀ s (midPos j s) (midPos_le j s) L :=
  (posPassEquivIter L hP hPL hL hκ s n (midPos j s - n)
      (by have := midPos_le j s; omega) (fun q hq h1 h2 => hb q hq h1 (by omega))).trans
    (posModelCongr j hj Q Λ Λc ν₀ L s _ _ (by omega))

end Categorification.Stendhal.CupCap
