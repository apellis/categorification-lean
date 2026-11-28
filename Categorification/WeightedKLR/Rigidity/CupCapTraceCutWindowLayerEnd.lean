/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndLayerMap
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowCornerEquiv

/-!
# The window idempotent on the layers of `S_cut(Res X)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5, the cut side of
(T_w) for one window loading.

The window idempotent `e_w = e(w)` of the middle block `T^{Λc}(ν₀)` acts on `Res X`, hence on
the cut input `Yc` (`cutWindowInputEnd`), and through `Ind` on the layers of the induced model of
`S_cut(Res X)` (`KLRAlgebra.indMackeyLayerMap`). The map `T'` is natural for module maps
(`topOneCornerEquiv_mapRight_botCornerEnd`), so the conjugate `T' ∘ Ind ε_{e(w)} ∘ T'⁻¹` is
intertwined by `Ξ_{q₁}` with this layer map (`indMackeyLeftMap_cutWindowConj`). Since `e(l)`
commutes with it, is idempotent and has its image in `Ξ_{q₁}(span)`, the cut corner of (T_w) is
`Ind(e_w)(e(l) · Lay^c)` (`cutWindowLayer_eq_map_range`). With `windowLoadingCornerEquiv` this
gives (T_w) (`windowLoadingCornerCutEquiv`): the corner of `l⁺_w` in the layer `N` of
`𝕊(S_+ X)` is isomorphic to `Ind(e_w)(e(l) · Lay^c)` inside the layer `0` of the induced model
of `S_cut(Res X)`, the form of "`e(l) · 𝕊 Lay^c(Res(e_w X))`" read inside `Res X`.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.cutWindowInputEnd`, `Stendhal.CupCap.windowLoadingCornerCutEquiv`.

## Main results

* `KLR.KLRAlgebra.topOneCornerEquiv_mapRight_botCornerEnd`.
* `Stendhal.CupCap.map_map_eq_map_range_of_comm`, `Stendhal.CupCap.cutWindowInputEnd_idem`,
  `Stendhal.CupCap.indMackeyLeftMap_cutWindowConj`, `Stendhal.CupCap.cutWindowIndSpan_eq`,
  `Stendhal.CupCap.cutWindowLayer_eq_map_range`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N] (hsym : KLRSymm Q)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

/-- **`T'` is natural for module maps**: `T' ∘ Ind (E g) = (1 ⊗ (1 ⊗ g)) ∘ T'`. -/
theorem topOneCornerEquiv_mapRight_botCornerEnd (g : N →ₗ[TensorKLR Q ν'' ν'''] N)
    (x : Ind Q q.γ q.δ (botCorner Q q N)) :
    (topOneCornerEquiv q N hsym (BalancedTensor.mapRight (botCornerEnd q N g) x) :
        MackeyLeftInd Q N q) =
      BalancedTensor.mapRight (BalancedTensor.mapRight g)
        (topOneCornerEquiv q N hsym x : MackeyLeftInd Q N q) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | tmul b n =>
    rw [BalancedTensor.mapRight_tmul, topOneCornerEquiv_tmul, topOneCornerEquiv_tmul, map_smul,
      BalancedTensor.mapRight_tmul, BalancedTensor.mapRight_tmul]
    rfl
  | add x x' hx hx' => simp only [map_add, Submodule.coe_add, hx, hx']

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-- In a layer, `A(E(S)) = E(range A)` for commuting `A`, `E` with `A` idempotent and
`range A ≤ S`. -/
theorem map_map_eq_map_range_of_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (A E : M →ₗ[R] M) (hAE : ∀ x, A (E x) = E (A x))
    (hAA : ∀ x, A (A x) = A x) (hS : LinearMap.range A ≤ S) :
    (S.map E).map A = (LinearMap.range A).map E := by
  have hcomm : A ∘ₗ E = E ∘ₗ A := LinearMap.ext hAE
  rw [← Submodule.map_comp, hcomm, Submodule.map_comp]
  congr 1
  refine le_antisymm LinearMap.map_le_range ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨A u, hS ⟨u, rfl⟩, hAA u⟩

theorem linearEquiv_conj_coe_apply {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] {P : Submodule R M} (T : V ≃ₗ[R] P) (g : V →ₗ[R] V)
    (y : P) : (T.conj g y : M) = (T (g (T.symm y)) : M) := by
  rw [LinearEquiv.conj_apply]
  rfl

section WindowLayer

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

local notation "wP" => Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w

variable (Λ Λc) in
/-- **The window idempotent on the cut input**: `e_w = e(w) ∈ T^{Λc}(ν₀)` acting on the cut
input of `Res X`. -/
def cutWindowInputEnd : Yc →ₗ[TensorKLR Sc
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))] Yc :=
  cutInputHom (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ γ
    (plusMidEnd X (tensorOfKLR Q Λc ν₀ (e w)))

local notation "εY" => cutWindowInputEnd Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ) X w

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
/-- The window idempotent on the cut input is an idempotent. -/
theorem cutWindowInputEnd_idem :
    εY ∘ₗ εY = εY := by
  ext x
  exact (plusMidEnd_mul (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ) (γ := γ)
    (ν₀ := ν₀) X _ _ (show PlusRes j hj Q Λ Λc θ γ ν₀ X from x)).trans
    (congrArg (fun u => plusMidEnd X u (show PlusRes j hj Q Λ Λc θ γ ν₀ X from x))
      (tensorOfKLR_e_mul_self w))

/-- **`Ξ_{q₁}` intertwines the window conjugate with the window idempotent on the layer**
(Webster v3, Lemma 7.19, trace half, step L5): `Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ y))) =
Ind(e_w)(Ξ_{q₁} y)`. -/
theorem indMackeyLeftMap_cutWindowConj
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0}) (y : mackeyTopOneSpan (Q := Sc) q₁.1 Yc) :
    (indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2)
      ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).conj
        ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k) y :
        MackeyLeftInd Sc Yc q₁.1) =
      (indMackeyLayerMap (εY)
        (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))) 0)
        ((indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2) (y : MackeyLeftInd Sc Yc q₁.1)) := by
  have h1 : ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).conj
        ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k) y :
        MackeyLeftInd Sc Yc q₁.1) =
      BalancedTensor.mapRight (BalancedTensor.mapRight (εY))
        (y : MackeyLeftInd Sc Yc q₁.1) := by
    have hc := linearEquiv_conj_coe_apply
      (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ))
      ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k) y
    have e1 := plusWindowEnd_e_eq (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj) (Q := Q)
      (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X s w q₁.1
    have e2 := topOneCornerEquiv_mapRight_botCornerEnd q₁.1 Yc
      (stendhalQ_symm Q (cutLabels j hj Λ) hQ) εY
      ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)
    have hm : ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ))
        (((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k)
          ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q₁.1) =
        ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ))
          (BalancedTensor.mapRight (botCornerEnd q₁.1 Yc εY)
          ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q₁.1) :=
      congrArg (fun f => ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ))
          (BalancedTensor.mapRight f
          ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q₁.1)) e1
    exact hc.trans (hm.trans (e2.trans (congrArg
      (fun v : mackeyTopOneSpan (Q := Sc) q₁.1 Yc =>
        BalancedTensor.mapRight (BalancedTensor.mapRight εY) (v : MackeyLeftInd Sc Yc q₁.1))
      (LinearEquiv.apply_symm_apply _ y))))
  exact (congrArg (indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2) h1).trans
    (indMackeyLeftMap_mapRight (Q := Sc) (N := Yc) (N' := Yc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm εY
      q₁.1 q₁.2 (y : MackeyLeftInd Sc Yc q₁.1))

/-- **The window image of the leading summand at the cut**:
`Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ span))) = Ind(e_w)(Ξ_{q₁}(span))`. -/
theorem cutWindowIndSpan_eq
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0}) :
    cutWindowIndSpan (Λ := Λ) (Λc := Λc) X hQ s w q₁ =
      ((mackeyTopOneSpan (Q := Sc) q₁.1 Yc).map (indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2)).map
        (indMackeyLayerMap (εY)
        (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))) 0) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, ⟨(y : MackeyLeftInd Sc Yc q₁.1), y.2, rfl⟩,
      (indMackeyLeftMap_cutWindowConj X hQ s w q₁ y).symm⟩
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨⟨y, hy⟩, indMackeyLeftMap_cutWindowConj X hQ s w q₁ ⟨y, hy⟩⟩

/-- **The cut corner of (T_w)** (Webster v3, Lemma 7.19, trace half, step L5): the image under
`Ξ_{q₁}` of the range of the window endomorphism is `Ind(e_w)(e(l) · Lay^c)`, the corner of
`l` in the layer `0` of the induced model of `S_cut(Res X)` moved by the window idempotent `e_w`
of the middle block. -/
theorem cutWindowLayer_eq_map_range (hsc : KLRSymm Sc)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0}) (hq₁ : q₁.1.β = 0) :
    cutWindowLayer (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ =
      (LinearMap.range (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0)).map
        (indMackeyLayerMap (εY)
        (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))) 0) :=
  (cutWindowLayer_eq X hQ s w q₁ hq₁).trans
    ((congrArg (fun S => Submodule.map (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0) S)
      (cutWindowIndSpan_eq X hQ s w q₁)).trans
      (map_map_eq_map_range_of_comm _ _ _
        (fun x => (indMackeyLayerMap_act εY _ _ 0 x).symm)
        (indMackeyLayerAct_e_idem Yc _ 0)
        (range_indMackeyLayerAct_cutLoading_le X hsc s hs q₁ hq₁)))

/-- **(T_w)** (Webster v3, Lemma 7.19, trace half, step L5): for `s` and `w` red-ordered, with
`s` satisfying the head condition, the corner of the window loading `l⁺_w` in the layer `N` of
`𝕊(S_+ X)` is isomorphic to `Ind(e_w)(e(l) · Lay^c)`, the corner of the cut loading `l` in the
layer `0` of the induced model of `S_cut(Res X)` moved by the window idempotent `e_w`. -/
def windowLoadingCornerCutEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
      (LinearMap.range (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0)).map
        (indMackeyLayerMap (εY)
        (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))) 0) :=
  ((windowLoadingCornerEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ hsr
    hwr).trans (cutWindowLayerEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc q₁ hq₁)).trans
    (LinearEquiv.ofEq _ _ (cutWindowLayer_eq_map_range X hQ s w hsc hs q₁ hq₁))

end WindowLayer

end Categorification.Stendhal.CupCap
