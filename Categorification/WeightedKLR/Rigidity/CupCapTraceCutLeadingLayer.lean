/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneIntertwine
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLayerCorner

/-!
# The leading summands of the layers of `S_cut(Res X)` and `S_+(X)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (passage from the
identity-shuffle spans to the layers).

`Ξ_λ` is injective for symmetric `Q`, for any choice of reduced words
(`indMackeyLeftMap_injective_of_klrSymm`). So the comparison `leadingTopOneSpanEquiv` of the
identity-shuffle spans of the leading Mackey data `q'` (weight `0`, at `S_cut(Res X)`) and `q`
(the window weight, at `S_+(X)`) passes to their images in the layers of the induced models:

`Ξ_{q'}(mackeyTopOneSpan q' (Res X)) ≅ Ξ_q(mackeyTopOneSpan q (BlocksMid X))`

(`leadingLayerSpanEquiv`). By §67.4 these images contain the corners of the loading idempotents
`e(cutLoading s)` and `e(windowLoading s w)` of the two layers
(`range_indMackeyLayerAct_cutLoading_le`, `range_indMackeyLayerAct_windowLoading_le`). The
layers of the induced model and of `KLRAlgebra.IndMackeyLayer` are the same quotient
(`indLayerCastEquiv`, compatible with the actions: `indLayerCastEquiv_act`), so the corner of
an ordered loading in a layer of `𝕊` is its corner in `IndMackeyLayer`
(`cutLoadingIndLayerEquiv`, from `cutLoadingLayerEquiv`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `KLR.KLRAlgebra.indMackeyLeftMap_injective_of_klrSymm`,
  `Stendhal.indLayerCastEquiv`, `Stendhal.cutLoadingIndLayerEquiv`,
  `Stendhal.CupCap.leadingLayerSpanEquiv`.

## Main results

* `Stendhal.indLayerCastEquiv_act`, `Stendhal.CupCap.leadingLayerSpanEquiv_apply`,
  `Stendhal.CupCap.range_indMackeyLayerAct_windowLoading_le`,
  `Stendhal.CupCap.range_indMackeyLayerAct_cutLoading_le`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

/-- **`Ξ_λ` is injective** for symmetric `Q` (`indMackeyLeftMap_injective` with a choice of
reduced words). -/
theorem indMackeyLeftMap_injective_of_klrSymm (hsym : KLRSymm Q) {c : ℕ}
    (q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c}) :
    Function.Injective (indMackeyLeftMap (Q := Q) h N q.1 q.2) :=
  indMackeyLeftMap_injective (Q := Q) h N hsym
    (σ := fun u => Classical.choose (exists_reduced (Multiset.card (ν'' + ν''')) u.1))
    (fun u => Classical.choose_spec (exists_reduced (Multiset.card (ν'' + ν''')) u.1)) q

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Cast

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable (Q Λ θ β N) in
/-- The layer of the induced model of a cut is `KLRAlgebra.IndMackeyLayer`. -/
def indLayerCastEquiv (n c : ℕ) :
    SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) ≃ₗ[k]
      IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c :=
  Submodule.quotEquivOfEq _ _ (by rw [indMackeyFiltLower_eq_indMackeyLower]; rfl)

theorem indLayerCastEquiv_mk (n c : ℕ) (v : indMackeyFilt Q Λ θ β N n c) :
    indLayerCastEquiv Q Λ θ β N n c (Submodule.Quotient.mk v) = Submodule.Quotient.mk v :=
  rfl

/-- `indLayerCastEquiv` intertwines the actions of an element preserving the Mackey
filtration. -/
theorem indLayerCastEquiv_act {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) (c : ℕ)
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    indLayerCastEquiv Q Λ θ β N n c (indLayerAct hz c y) =
      indMackeyLayerAct (CutInput Q Λ θ β N) z hz c (indLayerCastEquiv Q Λ θ β N n c y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

/-- The corner of `z` corresponds under `indLayerCastEquiv`. -/
theorem map_range_indLayerAct {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) (c : ℕ) :
    (LinearMap.range (indLayerAct (N := N) hz c)).map
        (indLayerCastEquiv Q Λ θ β N n c).toLinearMap =
      LinearMap.range (indMackeyLayerAct (CutInput Q Λ θ β N) z hz c) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨indLayerCastEquiv Q Λ θ β N n c y, (indLayerCastEquiv_act hz c y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨indLayerAct hz c ((indLayerCastEquiv Q Λ θ β N n c).symm y), ⟨_, rfl⟩, ?_⟩
    change indLayerCastEquiv Q Λ θ β N n c _ = _
    rw [indLayerCastEquiv_act, LinearEquiv.apply_symm_apply]

variable [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

/-- **The corner of an ordered loading** in a layer of `𝕊(N)` is the corner of that loading in
the layer `KLRAlgebra.IndMackeyLayer` of `Ind N` (`cutLoadingLayerEquiv` and
`indLayerCastEquiv`). -/
def cutLoadingIndLayerEquiv (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β) (n c : ℕ) :
    LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c) ≃ₗ[k]
      LinearMap.range (indMackeyLayerAct (CutInput Q Λ θ β N) (e l)
        (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c) :=
  (cutLoadingLayerEquiv hQ l hl n c).symm.trans
    ((Submodule.equivMapOfInjective _ (indLayerCastEquiv Q Λ θ β N n c).injective _).trans
      (LinearEquiv.ofEq _ _ (map_range_indLayerAct _ c)))

theorem cutLoadingIndLayerEquiv_symm_apply (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β) (n c : ℕ)
    (y : LinearMap.range (indLayerAct (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c)) :
    (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm
        ⟨indLayerCastEquiv Q Λ θ β N n c y, by
          rw [← map_range_indLayerAct]; exact Submodule.mem_map_of_mem y.2⟩ =
      cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c y := by
  rw [LinearEquiv.symm_apply_eq]
  simp only [cutLoadingIndLayerEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end Cast

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

/-- **The leading summands of the two layers** (Webster v3, Lemma 7.19, trace half, step L5):
`Ξ_{q₁}(mackeyTopOneSpan q₁ (Res X)) ≅ Ξ_{q₀}(mackeyTopOneSpan q₀ (BlocksMid X))`, the image
of `leadingTopOneSpanEquiv` under the injective maps `Ξ`. -/
def leadingLayerSpanEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    (mackeyTopOneSpan (Q := Sc) q₁.1 Yc).map
        (indMackeyLeftMap (Q := Sc)
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          Yc q₁.1 q₁.2) ≃ₗ[k]
      (mackeyTopOneSpan (Q := Sp) q₀.1 Nₒ).map
        (indMackeyLeftMap (Q := Sp)
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm Nₒ q₀.1 q₀.2) :=
  (Submodule.equivMapOfInjective _
      (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _).symm.trans
    ((leadingTopOneSpanEquiv X hQ s w hs q₀.1 hq₀ q₁.1 hq₁).trans
      (Submodule.equivMapOfInjective _ (indMackeyLeftMap_injective_of_klrSymm _ Nₒ hsp q₀) _))

theorem leadingLayerSpanEquiv_apply (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0)
    (z : mackeyTopOneSpan (Q := Sc) q₁.1 Yc) :
    leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
        (Submodule.equivMapOfInjective _
          (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ z) =
      Submodule.equivMapOfInjective _ (indMackeyLeftMap_injective_of_klrSymm _ Nₒ hsp q₀) _
        (leadingTopOneSpanEquiv X hQ s w hs q₀.1 hq₀ q₁.1 hq₁ z) := by
  simp only [leadingLayerSpanEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

include hQ in
/-- **The corner of the window loading** in the leading layer of `S_+(X)` lies in the leading
summand (§67.4, submodule form). -/
theorem range_indMackeyLayerAct_windowLoading_le (hsp : KLRSymm Sp)
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) :
    LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) ≤
      (mackeyTopOneSpan (Q := Sp) q₀.1 Nₒ).map
        (indMackeyLeftMap (Q := Sp)
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm Nₒ q₀.1 q₀.2) := by
  rintro _ ⟨y, rfl⟩
  exact indMackeyLayerAct_windowLoading_mem_leading hQ hsp s w hs y q₀ hq₀

/-- **The corner of the cut loading** in the layer `0` of `S_cut(Res X)` lies in the leading
summand (§67.4, submodule form). -/
theorem range_indMackeyLayerAct_cutLoading_le (hsc : KLRSymm Sc)
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    LinearMap.range (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0) ≤
      (mackeyTopOneSpan (Q := Sc) q₁.1 Yc).map
        (indMackeyLeftMap (Q := Sc)
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          Yc q₁.1 q₁.2) := by
  rintro _ ⟨y, rfl⟩
  exact indMackeyLayerAct_cutLoading_mem_leading _ hsc s hs y q₁ hq₁

end CupCap

end Categorification.Stendhal
