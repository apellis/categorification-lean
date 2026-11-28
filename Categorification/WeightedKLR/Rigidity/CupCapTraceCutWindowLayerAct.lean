/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowDevissage
import Categorification.Algebra.IdempotentQuotientLayerCorner
import Categorification.Algebra.OrthogonalIdempotentRangeSum

/-!
# The window at one loading on the layers of `𝕊(S_+ X)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the sum over the
window loadings).

The window `ι_s(g)` of the strands at the maximum preserves the head-strand filtration at the
end `midPos s + N` of the window (Claim A), so it acts on its layers (`windowLayerAct`), by a
non-unital ring map (`windowLayerAct_mul`, `windowLayerAct_add`). On a loading idempotent,
`ι_s(e(w))` is the action of `e(l⁺_w)` for the window loading `l⁺_w` (`windowEndAt_e_eq`,
`windowLayerAct_e`). Hence on each layer the `ι_s(e(w))` are orthogonal idempotents
(`windowLayerAct_orthIdem`) whose sum over the red-ordered `w` is the action of
`e'_s = ι_s(1_{red-ordered})` (`windowLayerAct_redOrdered`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.windowLayerAct`.

## Main results

* `Categorification.subLayerAct_add`, `Categorification.subLayerAct_zero`,
  `Stendhal.CupCap.windowEndAt_e_eq`, `Stendhal.CupCap.windowLayerAct_e`,
  `Stendhal.CupCap.windowLayerAct_mul`, `Stendhal.CupCap.windowLayerAct_orthIdem`,
  `Stendhal.CupCap.windowLayerAct_redOrdered`.
-/

noncomputable section

namespace Categorification

section Generic

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V] {G F : Submodule k V}

theorem subLayerAct_add (z z' : V →ₗ[k] V) (hG : ∀ v ∈ G, z v ∈ G) (hF : ∀ v ∈ F, z v ∈ F)
    (hG' : ∀ v ∈ G, z' v ∈ G) (hF' : ∀ v ∈ F, z' v ∈ F) :
    subLayerAct (z + z') (fun v hv => add_mem (hG v hv) (hG' v hv))
        (fun v hv => add_mem (hF v hv) (hF' v hv)) =
      subLayerAct z hG hF + subLayerAct z' hG' hF' :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem subLayerAct_zero (hG : ∀ v ∈ G, (0 : V →ₗ[k] V) v ∈ G)
    (hF : ∀ v ∈ F, (0 : V →ₗ[k] V) v ∈ F) :
    subLayerAct (0 : V →ₗ[k] V) hG hF = 0 :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => (Submodule.Quotient.mk_eq_zero _).2
    (by simp))

end Generic

namespace Stendhal

namespace CupCap

open KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

set_option hygiene false in
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Bp" => BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ

variable (s : Seq (stendhalWeight ℓ (θ + γ)))

/-- **`ι_s(e(w))` is the action of the window loading** `e(l⁺_w)` on `S_+(X)`, read as the
partial standardization of the three blocks of `λ⁺`. -/
theorem windowEndAt_e_eq (w : Seq (stendhalWeight 2 ν₀)) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s (e w) =
      cutStandardAction Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp hQ
        (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
          (e (windowLoading j hj θ γ ν₀ s w))) := by
  have h0 := castLabels_affineToTensor_windowAffine j hj Q Λ Λc θ γ ν₀ s (e w)
  have he := AlgEquiv.symm_apply_apply (castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
    (plusLabels Λ Λc j hj) (θ + (ν₀ + γ))) (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ
      (ν₀ + γ) (windowAffine j hj Q Λ Λc θ γ ν₀ s (e w)))
  have hw := windowAffine_e (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ)
    (γ := γ) (ν₀ := ν₀) s w
  exact (congrArg (plusStandardAction Q Λ Λc j hj θ ν₀ γ X hQ) h0.symm).trans
    ((congrArg (blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ _ hQ) he).trans
      (congrArg (fun z => cutStandardAction Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp hQ
        (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) z)) hw))

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The window at `s` on the layer `c`** of the head-strand filtration at the end
`midPos s + N` of the window. -/
def windowLayerAct (g : Rc) (c : ℕ) :
    SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
      (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c) →ₗ[k]
    SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
      (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c) :=
  subLayerAct (windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g)
    (fun _ hv => plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g hv)
    (fun v hv => windowEndAt_mem_lower X hQ s c g v hv)

set_option hygiene false in
local notation "WL" => windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s

/-- On a loading idempotent the window is the action of the window loading. -/
theorem windowLayerAct_e (w : Seq (stendhalWeight 2 ν₀)) (c : ℕ) :
    WL (e w) c =
      cutLayerAct (Λ := plusBlockLabels Λ Λc j hj) hQ (N := Bp)
        (preservesMackeyFilt_e (Q := Sp)
          (n := midPos j s + Multiset.card (stendhalWeight 2 ν₀))
          (n'' := Multiset.card
            (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ)))
          (windowLoading j hj θ γ ν₀ s w)) c :=
  subLayerAct_congr (windowEndAt_e_eq X hQ s w) _ _ _ _

/-- The window on the layers is multiplicative. -/
theorem windowLayerAct_mul (g g' : Rc) (c : ℕ)
    (y : SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
      (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)) :
    WL g c (WL g' c y) =
      WL (g * g') c y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
  have h1 : WL g' c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g' v,
        plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g' v.2⟩ := rfl
  have h2 : WL g c (Submodule.Quotient.mk
      ⟨windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g' v,
        plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g' v.2⟩) =
      Submodule.Quotient.mk ⟨windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g
        (windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g' v),
        plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g
          (plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g' v.2)⟩ := rfl
  have h3 : WL (g * g') c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s (g * g') v,
        plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s (g * g') v.2⟩ := rfl
  have hm : windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g
      (windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s g' v) =
      windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s (g * g') v := by
    rw [map_mul]
    rfl
  exact (congrArg (WL g c) h1).trans
    (h2.trans ((congrArg Submodule.Quotient.mk (Subtype.ext hm)).trans h3.symm))

theorem windowLayerAct_add (g g' : Rc) (c : ℕ) :
    WL (g + g') c = WL g c + WL g' c :=
  (subLayerAct_congr (map_add (windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s) g g') _ _
    (fun _ hv => add_mem (plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g hv)
      (plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g' hv))
    (fun v hv => add_mem (windowEndAt_mem_lower X hQ s c g v hv)
      (windowEndAt_mem_lower X hQ s c g' v hv))).trans
    (subLayerAct_add _ _ _ _ _ _)

theorem windowLayerAct_zero (c : ℕ) : WL 0 c = 0 := by
  have h := windowLayerAct_add (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s 0 0 c
  have h' : WL 0 c = WL 0 c + WL 0 c :=
    (congrArg (fun g => WL g c) (add_zero (0 : Rc))).symm.trans h
  exact add_left_cancel (h'.symm.trans (add_zero _).symm)

variable (j hj Q Λ Λc θ γ ν₀) in
/-- The window on the layer `c`, as an additive map. -/
def windowLayerActHom (c : ℕ) :
    Rc →+ (SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
      (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c) →ₗ[k]
    SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
      (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)) where
  toFun g := WL g c
  map_zero' := windowLayerAct_zero X hQ s c
  map_add' g g' := windowLayerAct_add X hQ s g g' c

theorem windowLayerAct_sum {ι : Type*} (t : Finset ι) (f : ι → Rc) (c : ℕ) :
    WL (∑ i ∈ t, f i) c = ∑ i ∈ t, WL (f i) c :=
  map_sum (windowLayerActHom j hj Q Λ Λc θ γ ν₀ X hQ s c) f t

open Classical in
/-- **The window loading idempotents are orthogonal on each layer** (indexed by the red-ordered
loadings `w` of the window). -/
theorem windowLayerAct_orthIdem (c : ℕ) :
    OrthIdem (Finset.univ : Finset {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w})
      (fun w => WL (e w.1) c) := by
  intro w _ w' _ y
  refine (windowLayerAct_mul (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s (e w.1) (e w'.1) c y).trans ?_
  by_cases h : w = w'
  · subst h
    refine Eq.trans ?_ (ite_eq_left rfl).symm
    exact congrArg (fun g => WL g c y) (e_mul_self w.1)
  · have h' : w.1 ≠ w'.1 := fun h'' => h (Subtype.ext h'')
    have h2 : (e w.1 * e w'.1 : Rc) = 0 := (e_mul_e _ _).trans (ite_eq_right h')
    refine Eq.trans ?_ (ite_eq_right h).symm
    exact (congrArg (fun g => WL g c y) h2).trans
      (congrArg (fun F => F y) (windowLayerAct_zero (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s c))

open Classical in
/-- **`e'_s` on a layer is the sum of the window loading idempotents.** -/
theorem windowLayerAct_redOrdered (c : ℕ) :
    WL (redOrderedKLR k Q Λc ν₀) c =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w},
        WL (e w.1) c := by
  have hs : (redOrderedKLR k Q Λc ν₀ : Rc) =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w}, (e w.1 : Rc) :=
    Finset.sum_subtype _ (fun _ => by simp) _
  exact (congrArg (fun g => WL g c) hs).trans
    (windowLayerAct_sum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s _ _ c)

end CupCap

end Stendhal

end Categorification
