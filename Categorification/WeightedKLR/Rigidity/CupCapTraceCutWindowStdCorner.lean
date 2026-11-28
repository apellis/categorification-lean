/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CutLoadingLayerMap
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLayerEnd

/-!
# (T_w) between corners of partial standardizations

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

The window idempotent `e_w` acts on `Res X` by a map over the factor algebras of the cut
(`cutWindowResEnd`), hence on the layers of `S_cut(Res X) = 𝕊(Res X)`
(`Stendhal.cutStandardLayerMap`). Through `Stendhal.cutLoadingIndLayerMapEquiv`, the target
`Ind(e_w)(e(l) · Lay^c)` of `windowLoadingCornerCutEquiv` is the corner `e_w · e(l) · 𝕊Lay^c`
of the layer `0` of `𝕊(Res X)`, so (T_w) becomes an isomorphism between corners of layers of
two partial standardizations (`windowLoadingCornerStdEquiv`). With the indices of the cuts
rewritten by `Seq.card_prefixWt` (`Stendhal.cutLayerCornerCast`,
`Stendhal.cutLayerMapCornerCast`), the layer of `𝕊(S_+ X)` sits at the cut `midPos s + N` and
that of `𝕊(Res X)` at `midPos s` (`windowLoadingCornerMidPosEquiv`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.cutLayerCornerCast`, `Stendhal.cutLayerMapCornerCast`,
  `Stendhal.CupCap.cutWindowResEnd`, `Stendhal.CupCap.windowLoadingCornerStdEquiv`,
  `Stendhal.CupCap.windowLoadingCornerMidPosEquiv`.

## Main results

* `Stendhal.CupCap.cutWindowResEnd_idem`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

section Cast

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

/-- The corner of a loading in a layer of `𝕊(N)` depends on the cut `n` only through its value. -/
def cutLayerCornerCast {n n' : ℕ} (h : n = n') (l : Seq (α + δ)) (c : ℕ) :
    LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c) ≃ₗ[k]
      LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n')
        (n'' := Multiset.card α) l) c) := by
  subst h
  exact LinearEquiv.refl k _

/-- The corner of a loading moved by a module map depends on the cut `n` only through its
value. -/
def cutLayerMapCornerCast {n n' : ℕ} (h : n = n') (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N)
    (l : Seq (α + δ)) (c : ℕ) :
    (LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c)).map (cutStandardLayerMap g n c) ≃ₗ[k]
      (LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n')
        (n'' := Multiset.card α) l) c)).map (cutStandardLayerMap g n' c) := by
  subst h
  exact LinearEquiv.refl k _

end Cast

namespace CupCap

section WindowStd

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))

variable (Λ Λc) in
/-- **The window idempotent on `Res X`**: `e_w = e(w) ∈ T^{Λc}(ν₀)` acting on `Res X`, a map
over the factor algebras of the cut. -/
def cutWindowResEnd :
    PlusRes j hj Q Λ Λc θ γ ν₀ X →ₗ[cutFactorAlgebra Q (cutLabels j hj Λ) θ γ]
      PlusRes j hj Q Λ Λc θ γ ν₀ X :=
  plusMidEnd X (tensorOfKLR Q Λc ν₀ (e w))

local notation "εR" => cutWindowResEnd Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) X w

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
/-- The window idempotent on `Res X` is an idempotent. -/
theorem cutWindowResEnd_idem (x : PlusRes j hj Q Λ Λc θ γ ν₀ X) : εR (εR x) = εR x :=
  (plusMidEnd_mul (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ) (γ := γ)
    (ν₀ := ν₀) X _ _ x).trans
    (congrArg (fun u => plusMidEnd X u x) (tensorOfKLR_e_mul_self w))

/-- **(T_w) between partial standardizations** (Webster v3, Lemma 7.19, trace half, step L5):
for `s` and `w` red-ordered, with `s` satisfying the head condition, the corner of the window
loading `l⁺_w` in the layer `N` of `𝕊(S_+ X)` is isomorphic to `e_w · e(l) · 𝕊Lay^c`, the
corner of the cut loading `l` in the layer `0` of `S_cut(Res X)` moved by the window idempotent
`e_w` of the middle block. -/
def windowLoadingCornerStdEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    (hq₁ : q₁.1.β = 0) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (cutLayerAct (Λ := plusBlockLabels Λ Λc j hj) hQ
        (N := BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
        (preservesMackeyFilt_e (Q := Sp)
          (n := Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
            (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ)))
          (windowLoading j hj θ γ ν₀ s w)) (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      (LinearMap.range (cutLayerAct (Λ := cutLabels j hj Λ) hQ
        (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := Sc)
          (n := Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
            (midPos_le_card_cut s)))
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0)).map
        (cutStandardLayerMap εR (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s)
          (midPos j s + 0) (midPos_le_card_cut s))) 0) :=
  (windowLoadingCornerCutEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ hsr
    hwr).trans
    (cutLoadingIndLayerMapEquiv (Λ := cutLabels j hj Λ) εR
      (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))) 0 hQ (cutWindowResEnd_idem X w) (cutLoading j hj θ γ s)
      (cutLoading_mem_cutOrderedLoadings hsr)).symm

/-- **(T_w) at the cuts `midPos s + N` and `midPos s`** (Webster v3, Lemma 7.19, trace half,
step L5): `windowLoadingCornerStdEquiv` with the cuts of the two layers written as
`midPos s + N` (for `𝕊(S_+ X)`, `N` the number of window strands) and `midPos s` (for
`S_cut(Res X)`), as in the filtration `plusHeadFilt` of the dévissage. -/
def windowLoadingCornerMidPosEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    (hq₁ : q₁.1.β = 0) (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) :
    LinearMap.range (cutLayerAct (Λ := plusBlockLabels Λ Λc j hj) hQ
        (N := BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
        (preservesMackeyFilt_e (Q := Sp)
          (n := midPos j s + Multiset.card (stendhalWeight 2 ν₀))
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ)))
          (windowLoading j hj θ γ ν₀ s w)) (Multiset.card (stendhalWeight 2 ν₀))) ≃ₗ[k]
      (LinearMap.range (cutLayerAct (Λ := cutLabels j hj Λ) hQ
        (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := Sc) (n := midPos j s)
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0)).map (cutStandardLayerMap εR (midPos j s) 0) :=
  ((cutLayerCornerCast (Λ := plusBlockLabels Λ Λc j hj)
      (N := BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
      hQ (Seq.card_prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
        (midPos_add_le_card (hj := hj) s)).symm
      (windowLoading j hj θ γ ν₀ s w) (Multiset.card (stendhalWeight 2 ν₀))).trans
    (windowLoadingCornerStdEquiv X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ hsr hwr)).trans
    (cutLayerMapCornerCast (Λ := cutLabels j hj Λ) hQ
      (Seq.card_prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      εR (cutLoading j hj θ γ s) 0)

end WindowStd

end CupCap

end Categorification.Stendhal
