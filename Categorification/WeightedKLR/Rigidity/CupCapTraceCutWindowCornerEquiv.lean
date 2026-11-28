/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingRange
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLoadingOrder

/-!
# (T_w) as a linear equivalence

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5, the isomorphism
(T_w) for one window loading.

For a loading `s` with the head condition, `l` the cut loading and `l⁺_w` the window loading,
let `φ` be the `k`-linear endomorphism `y ↦ (e(pre l) ⊗ e(suf l)) · T'(Ind ε_{e(w)} (T'⁻¹ y))`
of the identity-shuffle span at the cut (`cutWindowSpanEnd`). Then:

* `leadingLayerSpanEquiv` restricts to an isomorphism from the range of `φ` onto the corner
  `e(l⁺_w) · Lay⁺` of the leading layer of `S_+(X)` (`windowCornerSpanEquiv`), and hence onto
  the corner of `l⁺_w` in the layer of `𝕊(S_+ X)` (`windowLoadingCornerEquiv`, for `s` and `w`
  red-ordered);
* on the cut side, `Ξ_{q₁} ∘ φ = e(l) · (Ξ_{q₁} ∘ T' ∘ Ind ε_{e(w)} ∘ T'⁻¹)`
  (`indMackeyLeftMap_cutWindowSpanEnd`), so `Ξ_{q₁}` maps the range of `φ` isomorphically onto
  the submodule `e(l) · Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ span)))` of the corner of `l` in the layer
  `0` of the induced model of `S_cut(Res X)` (`cutWindowLayerEquiv`,
  `cutWindowLayer_le_range`), and hence into the corner of `l` in the layer of `𝕊(S_cut Res X)`
  (`cutWindowCornerEquiv`).

Composing gives (T_w) in the form "the corner of `l⁺_w` in `𝕊 Lay⁺` is isomorphic to
`e(l) · Ξ_{q₁}(Ind ε_{e(w)}-span)`" (`windowLoadingCutWindowEquiv`). Identifying the latter with
the corner of `l` in `𝕊 Lay^c(Res(e_w X))` is the next step (§84). No new hypothesis.

## Main definitions

* `Stendhal.CupCap.cutWindowSpanEnd`, `Stendhal.CupCap.leadingSpanLayerMap`.
* `Stendhal.CupCap.windowCornerSpanEquiv`, `Stendhal.CupCap.windowLoadingCornerEquiv`.
* `Stendhal.CupCap.cutWindowLayer`, `Stendhal.CupCap.cutWindowLayerEquiv`,
  `Stendhal.CupCap.cutWindowCornerEquiv`, `Stendhal.CupCap.windowLoadingCutWindowEquiv`.
-/

noncomputable section

namespace Categorification.Stendhal

section Generic

variable {R B M V : Type*} [CommRing R] [Ring B] [Algebra R B] [AddCommGroup M] [Module R M]
  [Module B M] [IsScalarTower R B M] [AddCommGroup V] [Module R V]

/-- The `R`-linear endomorphism `y ↦ t · T(g(T⁻¹ y))` of a submodule `P`, for `T : V ≃ P`,
`g` an endomorphism of `V` and `t` an element of an `R`-algebra acting on the ambient module,
when it preserves `P`. -/
def conjSmulSubmoduleEnd (P : Submodule R M) (T : V ≃ₗ[R] P) (g : V →ₗ[R] V) (t : B)
    (h : ∀ y : P, t • (T (g (T.symm y)) : M) ∈ P) : P →ₗ[R] P where
  toFun y := ⟨_, h y⟩
  map_add' y y' := Subtype.ext (by simp only [map_add, Submodule.coe_add, smul_add])
  map_smul' c y := Subtype.ext (by
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]
    exact smul_algebra_smul_comm c t _)

theorem conjSmulSubmoduleEnd_coe (P : Submodule R M) (T : V ≃ₗ[R] P) (g : V →ₗ[R] V) (t : B)
    (h : ∀ y : P, t • (T (g (T.symm y)) : M) ∈ P) (y : P) :
    (conjSmulSubmoduleEnd P T g t h y : M) = t • (T (g (T.symm y)) : M) :=
  rfl

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- The injective map `p → M₂`, `y ↦ (E (f y)).1`, for `f` injective and `E : f(p) ≃ P₂`. -/
def mapEquivSubtypeMap (p : Submodule R V) (f : V →ₗ[R] M₁) (hf : Function.Injective f)
    (P₂ : Submodule R M₂) (E : p.map f ≃ₗ[R] P₂) : p →ₗ[R] M₂ :=
  P₂.subtype ∘ₗ E.toLinearMap ∘ₗ (Submodule.equivMapOfInjective f hf p).toLinearMap

theorem mapEquivSubtypeMap_apply (p : Submodule R V) (f : V →ₗ[R] M₁)
    (hf : Function.Injective f) (P₂ : Submodule R M₂) (E : p.map f ≃ₗ[R] P₂) (y : p) :
    mapEquivSubtypeMap p f hf P₂ E y = (E (Submodule.equivMapOfInjective f hf p y)).1 :=
  rfl

theorem mapEquivSubtypeMap_injective (p : Submodule R V) (f : V →ₗ[R] M₁)
    (hf : Function.Injective f) (P₂ : Submodule R M₂) (E : p.map f ≃ₗ[R] P₂) :
    Function.Injective (mapEquivSubtypeMap p f hf P₂ E) :=
  Subtype.val_injective.comp (E.injective.comp (Submodule.equivMapOfInjective f hf p).injective)

/-- The image of the range of `φ` under `mapEquivSubtypeMap`, from a membership criterion. -/
theorem map_range_mapEquivSubtypeMap_eq (p : Submodule R V) (f : V →ₗ[R] M₁)
    (hf : Function.Injective f) (P₂ : Submodule R M₂) (E : p.map f ≃ₗ[R] P₂) (φ : p →ₗ[R] p)
    (g : p → V) (hφ : ∀ y, (φ y : V) = g y) (Z : Submodule R M₂)
    (h : ∀ z, z ∈ Z ↔ ∃ y y' : p, (y' : V) = g y ∧
      (E (Submodule.equivMapOfInjective f hf p y')).1 = z) :
    (LinearMap.range φ).map (mapEquivSubtypeMap p f hf P₂ E) = Z := by
  ext z
  rw [h z]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, φ y, hφ y, rfl⟩
  · rintro ⟨y, y', hy, rfl⟩
    exact ⟨y', ⟨y, Subtype.ext ((hφ y).trans hy.symm)⟩, rfl⟩

theorem conjSmulSubmoduleEnd_coe_conj (P : Submodule R M) (T : V ≃ₗ[R] P) (g : V →ₗ[R] V)
    (t : B) (h : ∀ y : P, t • (T (g (T.symm y)) : M) ∈ P) (y : P) :
    (conjSmulSubmoduleEnd P T g t h y : M) = t • (T.conj g y : M) :=
  rfl

/-- The image of the range of `y ↦ t · T(g(T⁻¹ y))` under a map `f` intertwining `t` with `A`
is the image under `A` of the range of `f ∘ T.conj g`. -/
theorem map_range_conjSmulSubmoduleEnd (P : Submodule R M) (T : V ≃ₗ[R] P) (g : V →ₗ[R] V)
    (t : B) (h : ∀ y : P, t • (T (g (T.symm y)) : M) ∈ P) (f : M →ₗ[R] M₁)
    (A : M₁ →ₗ[R] M₁) (hA : ∀ y : P, f (t • (y : M)) = A (f y)) :
    (LinearMap.range (conjSmulSubmoduleEnd P T g t h)).map (f ∘ₗ P.subtype) =
      (LinearMap.range (f ∘ₗ P.subtype ∘ₗ T.conj g)).map A := by
  ext z
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, (hA (T.conj g y)).symm⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, hA (T.conj g y)⟩

theorem injective_linearEquiv_comp_restrict {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    {p : Submodule R V} {q : Submodule R M₁} {Z : Submodule R M₃} (E : q ≃ₗ[R] Z)
    (f : V →ₗ[R] M₁) (hf : ∀ x ∈ p, f x ∈ q) (hinj : Function.Injective f) :
    Function.Injective (E.toLinearMap ∘ₗ f.restrict hf) := fun _ _ h =>
  Subtype.ext (hinj (congrArg Subtype.val (E.injective h)))

end Generic

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section WindowCorner

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
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))

local notation "preC" => Seq.prefixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "sufC" => Seq.suffixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "wP" => Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w
local notation "LayP" => IndMackeyLayer Sp
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))
  Nₒ (Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
  (Multiset.card (stendhalWeight 2 ν₀))
local notation "LayC" => IndMackeyLayer Sc
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))
  Yc (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
    (midPos_le_card_cut s))) 0

/-- The window element `(e(pre l) ⊗ e(suf l)) · T'(Ind ε_{e(w)} (T'⁻¹ y))` lies in the
identity-shuffle span at the cut. -/
theorem cutLoading_window_smul_mem_topOneSpan
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (y : mackeyTopOneSpan (Q := Sc) q₁.1 Yc) :
    (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
      (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
        (BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))
          ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
        MackeyLeftInd Sc Yc q₁.1)) ∈ mackeyTopOneSpan (Q := Sc) q₁.1 Yc := by
  have hex := exists_cutLoading_window_smul_topOneSpan (I := I) (k := k) (ℓ := ℓ)
    (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
    X hQ s w q₁.1 hq₁ y
  obtain ⟨y', hy'⟩ := hex
  rw [← hy']
  exact y'.2

/-- **The window endomorphism of the identity-shuffle span at the cut** (Webster v3,
Lemma 7.19, trace half, step L5): `y ↦ (e(pre l) ⊗ e(suf l)) · T'(Ind ε_{e(w)} (T'⁻¹ y))`. -/
def cutWindowSpanEnd
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    mackeyTopOneSpan (Q := Sc) q₁.1 Yc →ₗ[k] mackeyTopOneSpan (Q := Sc) q₁.1 Yc :=
  conjSmulSubmoduleEnd (mackeyTopOneSpan (Q := Sc) q₁.1 Yc)
    (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ))
    ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k)
    (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _))
    (cutLoading_window_smul_mem_topOneSpan X hQ s w q₁ hq₁)

theorem cutWindowSpanEnd_coe
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (y : mackeyTopOneSpan (Q := Sc) q₁.1 Yc) :
    (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ y : MackeyLeftInd Sc Yc q₁.1) =
      (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
        (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))
            ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q₁.1)) :=
  rfl

/-- The injective map `y ↦ (leadingLayerSpanEquiv (Ξ_{q₁} y)).1` from the identity-shuffle span
at the cut to the leading layer of `S_+(X)`. -/
def leadingSpanLayerMap (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    mackeyTopOneSpan (Q := Sc) q₁.1 Yc →ₗ[k] LayP :=
  mapEquivSubtypeMap (mackeyTopOneSpan (Q := Sc) q₁.1 Yc)
    (indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2)
    (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁)
    ((mackeyTopOneSpan (Q := Sp) q₀.1 Nₒ).map
        (indMackeyLeftMap (Q := Sp)
          (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
            (midPos_add_le_card (hj := hj) s)).symm Nₒ q₀.1 q₀.2))
    (leadingLayerSpanEquiv (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁)

theorem leadingSpanLayerMap_injective (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    Function.Injective
      (leadingSpanLayerMap (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁) :=
  mapEquivSubtypeMap_injective _ _ _ _ _

/-- **The corner of the window loading is the image of the window endomorphism** (Webster v3,
Lemma 7.19, trace half, step L5): `leadingSpanLayerMap` carries the range of `cutWindowSpanEnd`
onto the corner `e(l⁺_w) · Lay⁺`. -/
theorem map_range_cutWindowSpanEnd (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    (LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁)).map
        (leadingSpanLayerMap (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁) =
      LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) := by
  have hiff := mem_range_indMackeyLayerAct_windowLoading_iff (I := I) (k := k) (ℓ := ℓ)
    (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
    X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁
  refine map_range_mapEquivSubtypeMap_eq _ _ _ _ _ _ _ (cutWindowSpanEnd_coe X hQ s w q₁ hq₁) _
    ?_
  intro z
  exact hiff z

/-- **(T_w), leading-layer form** (Webster v3, Lemma 7.19, trace half, step L5): the range of
the window endomorphism `cutWindowSpanEnd` is isomorphic to the corner `e(l⁺_w) · Lay⁺` of the
leading layer of `S_+(X)`, through `leadingLayerSpanEquiv`. -/
def windowCornerSpanEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁) ≃ₗ[k]
      (LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) :
        Submodule k LayP) :=
  (Submodule.equivMapOfInjective
      (leadingSpanLayerMap (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁)
      (leadingSpanLayerMap_injective (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁)
      (LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁))).trans
    (LinearEquiv.ofEq _ _ (map_range_cutWindowSpanEnd (Λ := Λ) (Λc := Λc)
      X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁))

theorem windowCornerSpanEquiv_apply (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
    (y : LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁)) :
    (windowCornerSpanEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ y : LayP) =
      leadingSpanLayerMap (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ y.1 :=
  rfl

/-- **(T_w), plus side** (Webster v3, Lemma 7.19, trace half, step L5): for `s` and `w`
red-ordered, the corner of the window loading `l⁺_w` in the layer `N` of `𝕊(S_+ X)` is
isomorphic to the range of the window endomorphism `cutWindowSpanEnd`. -/
def windowLoadingCornerEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
      LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁) :=
  (cutLoadingIndLayerEquiv (Λ := plusBlockLabels Λ Λc j hj)
      (N := BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
      hQ (windowLoading j hj θ γ ν₀ s w) (windowLoading_mem_cutOrderedLoadings hsr hwr) _
      (Multiset.card (stendhalWeight 2 ν₀))).trans
    (windowCornerSpanEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁).symm

/-- **The cut side of the window endomorphism** (Webster v3, Lemma 7.19, trace half, step L5):
`Ξ_{q₁} ∘ φ = e(l) · (Ξ_{q₁} ∘ T' ∘ Ind ε_{e(w)} ∘ T'⁻¹)` on the layer `0` of the induced
model of `S_cut(Res X)`. -/
theorem indMackeyLeftMap_cutWindowSpanEnd
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (y : mackeyTopOneSpan (Q := Sc) q₁.1 Yc) :
    (indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2)
      ((cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁) y : MackeyLeftInd Sc Yc q₁.1) =
      (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0)
        ((indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2)
        ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).conj
          ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k) y :
          MackeyLeftInd Sc Yc q₁.1)) :=
  indMackeyLeftMap_cutLoading_e_smul X s q₁ _

/-- The image `Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ span)))` in the layer `0` of the induced model of
`S_cut(Res X)`. -/
def cutWindowIndSpan
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0}) : Submodule k LayC :=
  LinearMap.range ((indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2) ∘ₗ (mackeyTopOneSpan (Q := Sc) q₁.1 Yc).subtype ∘ₗ
    (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).conj
      ((BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))).restrictScalars k))

/-- The image under `Ξ_{q₁}` of the range of the window endomorphism. -/
def cutWindowLayer
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) : Submodule k LayC :=
  (LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁)).map
    ((indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2) ∘ₗ
    (mackeyTopOneSpan (Q := Sc) q₁.1 Yc).subtype)

/-- **The cut corner of (T_w)**: the image under `Ξ_{q₁}` of the range of the window
endomorphism is `e(l) · Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ span)))`. -/
theorem cutWindowLayer_eq
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    cutWindowLayer (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ =
      (cutWindowIndSpan (Λ := Λ) (Λc := Λc) X hQ s w q₁).map
        (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0) :=
  map_range_conjSmulSubmoduleEnd _ _ _ _ _ _ _
    (fun y => indMackeyLeftMap_cutLoading_e_smul X s q₁ (y : MackeyLeftInd Sc Yc q₁.1))

/-- The image under `Ξ_{q₁}` of the range of the window endomorphism lies in the corner
`e(l) · Lay^c`. -/
theorem cutWindowLayer_le_range
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    cutWindowLayer (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ ≤
      LinearMap.range (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0) := by
  rw [cutWindowLayer_eq]
  exact LinearMap.map_le_range

/-- **(T_w), cut side**: `Ξ_{q₁}` maps the range of the window endomorphism isomorphically onto
`cutWindowLayer`. -/
def cutWindowLayerEquiv (hsc : KLRSymm Sc)
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) :
    LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁) ≃ₗ[k]
      cutWindowLayer (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ :=
  Submodule.equivMapOfInjective _
    (fun _ _ h => Subtype.ext (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁ h)) _

/-- **(T_w), the map into the cut corner** (Webster v3, Lemma 7.19, trace half, step L5): for
`s` red-ordered, `y ↦ Ξ_{q₁} y` followed by `cutLoadingIndLayerEquiv⁻¹` carries the range of the
window endomorphism into the corner of the cut loading `l` in the layer `0` of `𝕊(S_cut Res X)`;
its image is `cutWindowLayer` (`cutWindowLayer_eq`). -/
def cutWindowCornerMap
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (hsr : IsRedOrdered s) :
    LinearMap.range (cutWindowSpanEnd (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁) →ₗ[k]
      LinearMap.range (cutLayerAct (Λ := cutLabels j hj Λ) hQ
        (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (preservesMackeyFilt_e (Q := Sc)
          (n := Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
            (midPos_le_card_cut s)))
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
          (cutLoading j hj θ γ s)) 0) :=
  (cutLoadingIndLayerEquiv (Λ := cutLabels j hj Λ) (N := PlusRes j hj Q Λ Λc θ γ ν₀ X) hQ
      (cutLoading j hj θ γ s) (cutLoading_mem_cutOrderedLoadings hsr) _ 0).symm.toLinearMap ∘ₗ
    LinearMap.restrict ((indMackeyLeftMap (Q := Sc)
      (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
      Yc q₁.1 q₁.2) ∘ₗ (mackeyTopOneSpan (Q := Sc) q₁.1 Yc).subtype)
      (q := LinearMap.range (indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0))
      (fun _ hy => cutWindowLayer_le_range (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁
        (Submodule.mem_map_of_mem hy))

theorem cutWindowCornerMap_injective (hsc : KLRSymm Sc)
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (hsr : IsRedOrdered s) :
    Function.Injective (cutWindowCornerMap (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ hsr) := by
  exact injective_linearEquiv_comp_restrict _ _ _
    (fun _ _ h => Subtype.ext (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁ h))

/-- **(T_w)** (Webster v3, Lemma 7.19, trace half, step L5): for `s` and `w` red-ordered with the
head condition, the corner of the window loading `l⁺_w` in the layer `N` of `𝕊(S_+ X)` is
isomorphic to the image of `cutWindowCornerMap` in the corner of the cut loading `l` in the
layer `0` of `𝕊(S_cut Res X)`, which corresponds to
`e(l) · Ξ_{q₁}(T'(Ind ε_{e(w)} (T'⁻¹ span)))` (`cutWindowLayer_eq`). -/
def windowLoadingCutWindowEquiv (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
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
      LinearMap.range (cutWindowCornerMap (Λ := Λ) (Λc := Λc) X hQ s w q₁ hq₁ hsr) :=
  (windowLoadingCornerEquiv (Λ := Λ) (Λc := Λc) X hQ s w hsc hsp hs q₀ hq₀ q₁ hq₁ hsr hwr).trans
    (LinearEquiv.ofInjective _
      (cutWindowCornerMap_injective (Λ := Λ) (Λc := Λc) X hQ s w hsc q₁ hq₁ hsr))

end WindowCorner

end Categorification.Stendhal.CupCap
