/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutHeadCorner

/-!
# The bottom corners of the leading Mackey data of `S_+(X)` and `S_cut(Res X)` agree

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the bottom factor).

Let `X` be a module over the three blocks `A | M | R` of `λ⁺`, and let `Res X` be `X` as a module
over the two outer blocks `A | R`, which are the two blocks of `λ` at the cut
(`plusOuterIncl`, `PlusRes`). This is the input of `S_cut` that the leading layer of `S_+(X)` is
compared with: the middle block `T^{μ μ*}(ν₀)` still acts on `Res X`, and commutes with the
outer blocks.

For the leading Mackey datum `q` of the outer cut of `S_+` (weight of the window) and the
leading datum `q'` of the cut of `S_cut` (weight `0`), the bottom corner `E · BlocksMid X` of
`S_+` is identified by `botCornerBlocksEquiv` with a corner `botBlocksCorner` of `X`. There:

* `ε_1` acts as the identity (`cutShuffleIdem_one_smul`), and so does the sum of the
  concatenation idempotents of the middle and last blocks (`sum_concatSet_concatIdem`);
* the head factor of `q`, relabelled to `T^{λ_1…λ_j}(θ)`, is the head factor of `q'`
  (`relabel_botHeadIdem_eq_cutBotHeadIdem`).

Hence the two bottom corners are the same subspace of `X` (`mem_botBlocksCorner_plus_iff`), and
`E · BlocksMid X ≅ E' · Res X` (`plusBotCornerEquiv`), by the identity coordinate of the inner
standardization.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.plusOuterIncl`, `Stendhal.CupCap.PlusRes`,
  `Stendhal.CupCap.plusBotCornerEquiv`.

## Main results

* `KLR.KLRAlgebra.sum_concatSet_concatIdem`, `Stendhal.CupCap.mem_botBlocksCorner_plus_iff`,
  `Stendhal.CupCap.plusBotCornerEquiv_apply`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

/-- **The concatenation idempotents of `ν + ν'` sum to `1`** in `R(ν) ⊗ R(ν')`. -/
theorem sum_concatSet_concatIdem (ν ν' : Multiset I) :
    (∑ t ∈ concatSet ν ν', concatIdem t : TensorKLR Q ν ν') = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _) (fun t _ ht => concatIdem_of_not_mem ht)]
  simp only [concatIdem]
  rw [Finset.sum_fiberwise (s := Finset.univ) (g := fun p : Seq ν × Seq ν' => p.1.append p.2)
    (f := fun p => (e p.1 ⊗ₜ e p.2 : TensorKLR Q ν ν')), ← Finset.univ_product_univ,
    Finset.sum_product]
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, sum_e]
  rfl

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)

/-- **The two blocks of `λ` at the cut inside the three blocks of `λ⁺`**:
`a ⊗ c ↦ a ⊗ (1 ⊗ c)`. -/
def plusOuterIncl :
    cutFactorAlgebra Q (cutLabels j hj Λ) θ γ →ₐ[k] PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ :=
  Algebra.TensorProduct.map (AlgHom.id k (TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ))
    Algebra.TensorProduct.includeRight

theorem plusOuterIncl_tmul (a : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ)
    (c : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ) :
    plusOuterIncl j hj Q Λ Λc θ γ ν₀ (a ⊗ₜ c) = a ⊗ₜ ((1 : TensorProductAlgebra k Q Λc ν₀) ⊗ₜ c) :=
  rfl

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]

/-- **`Res X`**: a module over the three blocks of `λ⁺`, as a module over the two blocks of `λ`
at the cut, through `plusOuterIncl`. -/
@[nolint unusedArguments]
def PlusRes (_j : ℕ) (_hj : _j ≤ ℓ) (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin ℓ → I →₀ ℕ)
    (_Λc : Fin 2 → I →₀ ℕ) (_θ _γ _ν₀ : Multiset I) (X : Type*) : Type _ := X

instance : AddCommGroup (PlusRes j hj Q Λ Λc θ γ ν₀ X) := inferInstanceAs (AddCommGroup X)
instance : Module k (PlusRes j hj Q Λ Λc θ γ ν₀ X) := inferInstanceAs (Module k X)
instance : Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) (PlusRes j hj Q Λ Λc θ γ ν₀ X) :=
  Module.compHom X (plusOuterIncl j hj Q Λ Λc θ γ ν₀).toRingHom

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
theorem plusRes_smul (d : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ)
    (x : PlusRes j hj Q Λ Λc θ γ ν₀ X) :
    d • x = (plusOuterIncl j hj Q Λ Λc θ γ ν₀ d • (show X from x) : X) := rfl

instance : IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ)
    (PlusRes j hj Q Λ Λc θ γ ν₀ X) where
  smul_assoc c d x := by
    rw [plusRes_smul, plusRes_smul, map_smul]
    exact smul_assoc c _ (show X from x)

variable (hQ : KLRSymm Q)

local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))
local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)

/-- The identity of `X`, from the inner input of `S_+(X)` to the input of `S_cut(Res X)`. -/
def innerToRes : Inner ≃ₗ[k] Yc := LinearEquiv.refl k X

variable {j hj Q Λ Λc θ γ ν₀}

include hQ in
/-- **The bottom corners of `S_+(X)` and `S_cut(Res X)` are the same subspace of `X`**, for
the leading Mackey data `q` (weight of the window) and `q'` (weight `0`) at a loading `s` whose
red strands left of `midPos s` are among `λ_1, …, λ_j`. -/
theorem mem_botBlocksCorner_plus_iff (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) (x : Inner) :
    x ∈ botBlocksCorner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) q ↔
      innerToRes j hj Q Λ Λc θ γ ν₀ X x ∈
        botCorner (stendhalQ Q (cutLabels j hj Λ)) q' Yc := by
  rw [mem_botBlocksCorner, mem_botCorner_cutInput_iff_of_β_eq_zero Q (cutLabels j hj Λ) θ γ
    (PlusRes j hj Q Λ Λc θ γ ν₀ X) q' hq', mem_inputLoadCorner, sum_concatSet_concatIdem,
    one_smul, cutShuffleIdem_one_smul Q _ ν₀ γ _ hQ x]
  have hL : blocksHeadEnd Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X)
      (botHeadIdem Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ q) x =
      ((cutBotHeadIdem Q (cutLabels j hj Λ) θ γ q' ⊗ₜ
        (1 : TensorProductAlgebra k Q Λc ν₀ ⊗[k]
          TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) := by
    change (plusFactorEquiv Q Λ Λc j hj θ ν₀ γ (_ ⊗ₜ 1) • (show X from x) : X) = _
    rw [plusFactorEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      map_one, AlgEquiv.coe_toAlgHom,
      relabel_botHeadIdem_eq_cutBotHeadIdem Q Λ Λc s w hs q hq q' hq']
  have hR : ((cutBotHeadIdem Q (cutLabels j hj Λ) θ γ q' ⊗ₜ
        (1 : TensorProductAlgebra k Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ) :
        cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) •
          (show PlusRes j hj Q Λ Λc θ γ ν₀ X from innerToRes j hj Q Λ Λc θ γ ν₀ X x) :
          PlusRes j hj Q Λ Λc θ γ ν₀ X) =
      ((cutBotHeadIdem Q (cutLabels j hj Λ) θ γ q' ⊗ₜ
        (1 : TensorProductAlgebra k Q Λc ν₀ ⊗[k]
          TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ) :
        PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) := rfl
  rw [hL, hR]
  exact ⟨fun h => h.2, fun h => ⟨⟨rfl, rfl⟩, h⟩⟩

local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

/-- **L5, bottom factor: `E · BlocksMid X ≅ E' · Res X`** (Webster v3, Lemma 7.19, trace half).
For a loading `s` of `λ` whose red strands left of `midPos s` are among `λ_1, …, λ_j`, the
bottom corner of the leading Mackey datum `q` of `S_+(X)` (weight of the window) is isomorphic
to the bottom corner of the leading datum `q'` of `S_cut(Res X)` (weight `0`), by the identity
coordinate of the inner standardization (`plusBotCornerEquiv_apply`). -/
def plusBotCornerEquiv (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) :
    botCorner (stendhalQ Q (plusBlockLabels Λ Λc j hj)) q Nₒ ≃ₗ[k]
      botCorner (stendhalQ Q (cutLabels j hj Λ)) q' Yc :=
  (botCornerBlocksEquiv Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X)
      hQ (hq.trans (windowWeight_eq_map j hj ν₀))).trans
    (LinearEquiv.ofSubmodules (innerToRes j hj Q Λ Λc θ γ ν₀ X) _ _ (by
      ext y
      rw [Submodule.mem_map_equiv]
      exact (mem_botBlocksCorner_plus_iff X hQ s w hs q hq q' hq' _).trans Iff.rfl))

theorem plusBotCornerEquiv_apply (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) (z : botCorner (stendhalQ Q (plusBlockLabels Λ Λc j hj)) q Nₒ) :
    (plusBotCornerEquiv X hQ s w hs q hq q' hq' z : Yc) =
      innerToRes j hj Q Λ Λc θ γ ν₀ X
        ((cutStandardShuffleEquiv Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
          (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X)) hQ
          (show CutStandard Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
            (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))
            from (z : Nₒ)) :
            Shuffle (Seq.card_add'
              (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀))
              (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))) →
              Inner) shufOne) := by
  rw [plusBotCornerEquiv, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules_apply,
    botCornerBlocksEquiv_apply]

end Categorification.Stendhal.CupCap
