/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowStdCorner
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLayerAct
import Categorification.Algebra.BalancedTensorEndAction

/-!
# The window idempotents on the cut corner of `S_cut(Res X)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the sum over the
window loadings, cut side).

The action of a module map on the layers of a partial standardization is additive and
multiplicative in the map (`Stendhal.cutStandardLayerMap_add`,
`Stendhal.cutStandardLayerMap_comp`). The middle block `T^{Λc}(ν₀)` acts on `Res X` by maps
over the factor algebras of the cut (`plusMidEnd`), additively (`plusMidEnd_add`). So the
window idempotents `e_w` give orthogonal idempotents `e_w · e(l)` on the layer `0` of
`S_cut(Res X)` at the cut `midPos s` (`cutWindowCorner_orthIdem`), whose sum over the
red-ordered `w` is `e_red · e(l)`, `e_red` the image of the red-ordered idempotent of the window
(`cutWindowCorner_sum`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.cutWindowCorner`.

## Main results

* `Stendhal.cutStandardLayerMap_add`, `Stendhal.cutStandardLayerMap_comp`,
  `Stendhal.CupCap.plusMidEnd_add`, `Stendhal.CupCap.cutWindowCorner_orthIdem`,
  `Stendhal.CupCap.cutWindowCorner_sum`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Generic

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

theorem cutShuffleMap_comp (g g' : N →ₗ[cutFactorAlgebra Q Λ θ β] N)
    (y : CutShuffle Q Λ θ β N) :
    cutShuffleMap Q Λ θ β g (cutShuffleMap Q Λ θ β g' y) = cutShuffleMap Q Λ θ β (g ∘ₗ g') y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b x =>
    simp only [cutShuffleMap, BalancedTensor.mapRight_tmul]
    rfl
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']

theorem cutShuffleMap_add (g g' : N →ₗ[cutFactorAlgebra Q Λ θ β] N) :
    cutShuffleMap Q Λ θ β (g + g') = cutShuffleMap Q Λ θ β g + cutShuffleMap Q Λ θ β g' :=
  BalancedTensor.mapRight_add (cutInputHom Q Λ θ β g) (cutInputHom Q Λ θ β g')

variable (n c : ℕ)

theorem cutStandardLayerMap_add (g g' : N →ₗ[cutFactorAlgebra Q Λ θ β] N) :
    cutStandardLayerMap (g + g') n c = cutStandardLayerMap g n c + cutStandardLayerMap g' n c :=
  (subLayerAct_congr (LinearMap.ext fun z => cutStandardMap_add Q Λ θ β g g' z) _ _
    (fun _ hv => add_mem (cutStandardMap_mem_cutMackeyFilt g hv)
      (cutStandardMap_mem_cutMackeyFilt g' hv))
    (fun _ hv => add_mem (cutStandardMap_mem_cutMackeyFiltLower g hv)
      (cutStandardMap_mem_cutMackeyFiltLower g' hv))).trans
    (subLayerAct_add _ _ _ _ _ _)

theorem cutStandardLayerMap_zero :
    cutStandardLayerMap (0 : N →ₗ[cutFactorAlgebra Q Λ θ β] N) n c = 0 := by
  have h := cutStandardLayerMap_add n c (0 : N →ₗ[cutFactorAlgebra Q Λ θ β] N) 0
  have h' : cutStandardLayerMap (0 : N →ₗ[cutFactorAlgebra Q Λ θ β] N) n c =
      cutStandardLayerMap 0 n c + cutStandardLayerMap 0 n c :=
    (congrArg (fun g => cutStandardLayerMap g n c)
      (add_zero (0 : N →ₗ[cutFactorAlgebra Q Λ θ β] N))).symm.trans h
  exact add_left_cancel (h'.symm.trans (add_zero _).symm)

/-- The layer action of `g ∘ g'` is the composite of the layer actions. -/
theorem cutStandardLayerMap_comp (g g' : N →ₗ[cutFactorAlgebra Q Λ θ β] N)
    (y : SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c)) :
    cutStandardLayerMap g n c (cutStandardLayerMap g' n c y) =
      cutStandardLayerMap (g ∘ₗ g') n c y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
  have h1 : cutStandardLayerMap g' n c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g' v,
        cutStandardMap_mem_cutMackeyFilt g' v.2⟩ := rfl
  have h2 : cutStandardLayerMap g n c (Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g' v,
        cutStandardMap_mem_cutMackeyFilt g' v.2⟩) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g (cutStandardMap Q Λ θ β g' v),
        cutStandardMap_mem_cutMackeyFilt g (cutStandardMap_mem_cutMackeyFilt g' v.2)⟩ := rfl
  have h3 : cutStandardLayerMap (g ∘ₗ g') n c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β (g ∘ₗ g') v,
        cutStandardMap_mem_cutMackeyFilt (g ∘ₗ g') v.2⟩ := rfl
  have hm : cutStandardMap Q Λ θ β g (cutStandardMap Q Λ θ β g' (v : CutStandard Q Λ θ β N)) =
      cutStandardMap Q Λ θ β (g ∘ₗ g') v := by
    obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ (v : CutStandard Q Λ θ β N)
    rw [← hu]
    exact congrArg (Submodule.mkQ _) (cutShuffleMap_comp g g' u)
  exact (congrArg (cutStandardLayerMap g n c) h1).trans
    (h2.trans ((congrArg Submodule.Quotient.mk (Subtype.ext hm)).trans h3.symm))

end Generic

namespace CupCap

section WindowRes

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
theorem plusMidEnd_add (u u' : TensorProductAlgebra k Q Λc ν₀) :
    plusMidEnd (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀)
        X (u + u') = plusMidEnd X u + plusMidEnd X u' := by
  refine LinearMap.ext fun x => ?_
  change (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      ((u + u') ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) =
    (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X) +
    (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u' ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X)
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  exact add_smul _ _ (show X from x)

set_option hygiene false in
local notation "PM" => plusMidEnd (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ)
  (γ := γ) (ν₀ := ν₀) X

variable (s : Seq (stendhalWeight ℓ (θ + γ)))

local notation "Cl" => cutLayerAct (Λ := cutLabels j hj Λ) hQ
  (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
  (preservesMackeyFilt_e (Q := Sc) (n := midPos j s)
    (n'' := Multiset.card
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
    (cutLoading j hj θ γ s)) 0

variable (Λ Λc) in
/-- **The cut corner moved by the middle block**: `u · e(l)` on the layer `0` of
`S_cut(Res X)` at the cut `midPos s`, `u ∈ T^{Λc}(ν₀)` acting on `Res X`. -/
def cutWindowCorner (u : TensorProductAlgebra k Q Λc ν₀) :
    SubLayer (cutMackeyFilt Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0)
      (cutMackeyFiltLower Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0) →ₗ[k]
    SubLayer (cutMackeyFilt Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0)
      (cutMackeyFiltLower Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0) :=
  cutStandardLayerMap (PM u) (midPos j s) 0 ∘ₗ Cl

set_option hygiene false in
local notation "CW" => cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
  (ν₀ := ν₀) X hQ s

/-- The range of `u · e(l)` is `u · (e(l) · 𝕊Lay^c)`. -/
theorem range_cutWindowCorner (u : TensorProductAlgebra k Q Λc ν₀) :
    LinearMap.range (CW u) =
      (LinearMap.range (Cl)).map (cutStandardLayerMap (PM u) (midPos j s) 0) :=
  LinearMap.range_comp _ _

theorem cutWindowCorner_mul (u u' : TensorProductAlgebra k Q Λc ν₀)
    (y : SubLayer (cutMackeyFilt Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0)
      (cutMackeyFiltLower Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
        (midPos j s) 0)) :
    CW u (CW u' y) = CW (u * u') y := by
  have h1 := cutStandardLayerMap_act (PM u') 0 hQ
    (preservesMackeyFilt_e (Q := Sc) (n := midPos j s)
      (n'' := Multiset.card
        (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
      (cutLoading j hj θ γ s)) (Cl y)
  have h2 := cutLayerAct_e_idem (Λ := cutLabels j hj Λ) (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
    (n := midPos j s) 0 hQ (cutLoading j hj θ γ s) y
  have h3 := cutStandardLayerMap_comp (midPos j s) 0 (PM u) (PM u')
    (Cl y)
  have h4 : PM u ∘ₗ PM u' = PM (u * u') :=
    LinearMap.ext fun x => plusMidEnd_mul X u u' x
  change cutStandardLayerMap (PM u) (midPos j s) 0
      (Cl (cutStandardLayerMap (PM u') (midPos j s) 0 (Cl y))) =
    cutStandardLayerMap (PM (u * u')) (midPos j s) 0 (Cl y)
  exact (congrArg (cutStandardLayerMap (PM u) (midPos j s) 0) h1.symm).trans
    ((congrArg (fun t => cutStandardLayerMap (PM u) (midPos j s) 0
      (cutStandardLayerMap (PM u') (midPos j s) 0 t)) h2).trans
      (h3.trans (congrArg (fun g : PlusRes j hj Q Λ Λc θ γ ν₀ X →ₗ[cutFactorAlgebra Q
        (cutLabels j hj Λ) θ γ] PlusRes j hj Q Λ Λc θ γ ν₀ X =>
          cutStandardLayerMap g (midPos j s) 0 (Cl y)) h4)))

theorem cutWindowCorner_add (u u' : TensorProductAlgebra k Q Λc ν₀) :
    CW (u + u') = CW u + CW u' := by
  change cutStandardLayerMap (PM (u + u')) (midPos j s) 0 ∘ₗ Cl =
    cutStandardLayerMap (PM u) (midPos j s) 0 ∘ₗ Cl +
      cutStandardLayerMap (PM u') (midPos j s) 0 ∘ₗ Cl
  exact (congrArg (fun g => cutStandardLayerMap g (midPos j s) 0 ∘ₗ Cl)
    (plusMidEnd_add X u u')).trans
    ((congrArg (· ∘ₗ Cl) (cutStandardLayerMap_add (midPos j s) 0 (PM u) (PM u'))).trans
      (LinearMap.add_comp _ _ _))

theorem cutWindowCorner_zero : CW 0 = 0 := by
  have h := cutWindowCorner_add X hQ s (0 : TensorProductAlgebra k Q Λc ν₀) 0
    (Λ := Λ) (j := j) (hj := hj) (θ := θ) (γ := γ)
  have h' : CW 0 = CW 0 + CW 0 :=
    (congrArg CW (add_zero (0 : TensorProductAlgebra k Q Λc ν₀))).symm.trans h
  exact add_left_cancel (h'.symm.trans (add_zero _).symm)

open Classical in
/-- **The window idempotents on the cut corner are orthogonal.** -/
theorem cutWindowCorner_orthIdem :
    OrthIdem (Finset.univ : Finset {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w})
      (fun w => CW (tensorOfKLR Q Λc ν₀ (e w.1))) := by
  intro w _ w' _ y
  refine (cutWindowCorner_mul X hQ s _ _ y).trans ?_
  have hm : tensorOfKLR Q Λc ν₀ (e w.1) * tensorOfKLR Q Λc ν₀ (e w'.1) =
      tensorOfKLR Q Λc ν₀ (e w.1 * e w'.1) := by
    simp only [tensorOfKLR, map_mul]
  by_cases h : w = w'
  · subst h
    refine Eq.trans ?_ (ite_eq_left rfl).symm
    exact congrArg (fun u => CW u y) (tensorOfKLR_e_mul_self w.1)
  · have h' : w.1 ≠ w'.1 := fun h'' => h (Subtype.ext h'')
    have h2 : tensorOfKLR Q Λc ν₀ (e w.1) * tensorOfKLR Q Λc ν₀ (e w'.1) = 0 := by
      rw [hm, e_mul_e, ite_eq_right h']
      simp only [tensorOfKLR, map_zero]
    refine Eq.trans ?_ (ite_eq_right h).symm
    exact (congrArg (fun u => CW u y) h2).trans
      (congrArg (fun F => F y) (cutWindowCorner_zero (Λ := Λ) (Λc := Λc) (Q := Q) (j := j)
        (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s))

open Classical in
/-- **`e_red · e(l)` is the sum of the `e_w · e(l)`** over the red-ordered loadings `w` of the
window. -/
theorem cutWindowCorner_sum :
    CW (tensorOfKLR Q Λc ν₀ (redOrderedKLR k Q Λc ν₀)) =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w},
        CW (tensorOfKLR Q Λc ν₀ (e w.1)) := by
  have hs₀ : (redOrderedKLR k Q Λc ν₀ : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w},
        (e w.1 : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :=
    Finset.sum_subtype _ (fun _ => by simp) _
  have hs : tensorOfKLR Q Λc ν₀ (redOrderedKLR k Q Λc ν₀) =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w}, tensorOfKLR Q Λc ν₀ (e w.1) :=
    (congrArg (tensorOfKLR Q Λc ν₀) hs₀).trans (by simp only [tensorOfKLR, map_sum])
  have h2 : CW (∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w},
        tensorOfKLR Q Λc ν₀ (e w.1)) =
      ∑ w : {w : Seq (stendhalWeight 2 ν₀) // IsRedOrdered w},
        CW (tensorOfKLR Q Λc ν₀ (e w.1)) :=
    apply_sum_of_additive _ _
      (cutWindowCorner_zero (Λ := Λ) (Λc := Λc) (Q := Q) (j := j) (hj := hj) (θ := θ)
        (γ := γ) (ν₀ := ν₀) X hQ s)
      (cutWindowCorner_add (Λ := Λ) (Λc := Λc) (Q := Q) (j := j) (hj := hj) (θ := θ)
        (γ := γ) (ν₀ := ν₀) X hQ s) _
  have h1 := congrArg (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ) (γ := γ)
    (ν₀ := ν₀) X hQ s) hs
  exact h1.trans h2

end WindowRes

end CupCap

end Categorification.Stendhal
