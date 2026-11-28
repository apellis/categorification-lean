/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLayerAct

/-!
# The top of the dévissage as the window corner of the leading layer

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

The dévissage `plusWindowCorner_devissage` reduces `Hom_W(L', e'_s S_+(X))` to
`Hom_W(L', top_s)`, `top_s = e'_s S_+(X) / (F_{N-1} ∩ e'_s S_+(X))`, `F_{N-1}` the step
`plusHeadFilt s 1` of the head-strand filtration at the end of the window. The window acts on
the layer `F_N / F_{N-1}` by a non-unital ring map (`windowLayerHom`) commuting with
`e'_s = ι_s(1_{red-ordered})` (`windowLayerHom_comm`), so the corner of `e'_s` in the layer is
a `W`-module (`EndCornerPart`). Since `e'_s S_+(X) ⊆ F_N` (`plusWindowCornerFilt_top`) and
`e'_s` is idempotent (`redOrderedKLR_mul_self`), the projection to the layer identifies
`top_s` with that corner, `W`-linearly (`plusWindowTopEquiv`). As a group the corner is the
range of `e'_s` on the layer (`EndCornerPart.rangeEquiv`), the source of (T).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Categorification.EndCornerPart.rangeEquiv`, `Stendhal.CupCap.windowLayerHom`,
  `Stendhal.CupCap.plusWindowTopMap`, `Stendhal.CupCap.plusWindowTopEquiv`.

## Main results

* `Stendhal.CupCap.redOrderedKLR_mul_self`, `Stendhal.CupCap.windowLayerHom_comm`,
  `Stendhal.CupCap.ker_plusWindowTopMap`, `Stendhal.CupCap.plusWindowTopMap_surjective`.
-/

noncomputable section

universe u

namespace Categorification

section Generic

variable {k : Type*} [CommRing k] {R : Type u} [Ring R] {V : Type u} [AddCommGroup V]
  [Module k V] {ψ : R →ₙ+* Module.End k V} {ε : Module.End k V}
  {hcomm : ∀ g, ε * ψ g = ψ g * ε} {hone : ψ 1 * ε = ε}

namespace EndCornerPart

/-- **The corner of an idempotent is its range**, as an additive group. -/
def rangeEquiv (hidem : ∀ v, ε (ε v) = ε v) :
    EndCornerPart ψ ε hcomm hone ≃+ LinearMap.range ε where
  toFun x := ⟨x.val, x.prop ▸ LinearMap.mem_range_self ε x.val⟩
  invFun y := mk y.1 (by
    have hy := y.2
    rw [LinearMap.mem_range] at hy
    obtain ⟨v, hv⟩ := hy
    rw [← hv]
    exact hidem v)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem rangeEquiv_apply_coe (hidem : ∀ v, ε (ε v) = ε v)
    (x : EndCornerPart ψ ε hcomm hone) :
    ((rangeEquiv hidem x : LinearMap.range ε) : V) = x.val := rfl

theorem rangeEquiv_smul (hidem : ∀ v, ε (ε v) = ε v) (g : R)
    (x : EndCornerPart ψ ε hcomm hone) :
    ((rangeEquiv hidem (g • x) : LinearMap.range ε) : V) = ψ g x.val := rfl

end EndCornerPart

end Generic

section Layer

variable {k : Type*} [CommRing k] {R : Type u} [Ring R] {V : Type u} [AddCommGroup V]
  [Module k V] (ψ : R →ₙ+* Module.End k V) {G F : Submodule k V}
  (hG : ∀ g, ∀ v ∈ G, ψ g v ∈ G) (hF : ∀ g, ∀ v ∈ F, ψ g v ∈ F)

/-- **A non-unital action on a layer** `G / F` of submodules preserved by it. -/
def subLayerHom : R →ₙ+* Module.End k (SubLayer G F) where
  toFun g := subLayerAct (ψ g) (hG g) (hF g)
  map_mul' g g' := Submodule.linearMap_qext _ (LinearMap.ext fun v =>
    congrArg Submodule.Quotient.mk (Subtype.ext (by
      change ψ (g * g') v.1 = ψ g (ψ g' v.1)
      rw [map_mul, Module.End.mul_apply])))
  map_zero' := Submodule.linearMap_qext _ (LinearMap.ext fun v =>
    (Submodule.Quotient.mk_eq_zero _).2 (by
      change ψ 0 v.1 ∈ F
      rw [map_zero, LinearMap.zero_apply]
      exact F.zero_mem))
  map_add' g g' := Submodule.linearMap_qext _ (LinearMap.ext fun v =>
    congrArg Submodule.Quotient.mk (Subtype.ext (by
      change ψ (g + g') v.1 = ψ g v.1 + ψ g' v.1
      rw [map_add, LinearMap.add_apply])))

theorem subLayerHom_mk (g : R) (v : G) :
    subLayerHom ψ hG hF g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨ψ g v, hG g v v.2⟩ :=
  rfl

variable (e : R) (he : e * e = e) (hcomm : ∀ g, ψ e * ψ g = ψ g * ψ e)
  (hone : ψ 1 * ψ e = ψ e)

include hcomm in
theorem subLayerHom_comm (g : R) :
    subLayerHom ψ hG hF e * subLayerHom ψ hG hF g =
      subLayerHom ψ hG hF g * subLayerHom ψ hG hF e := by
  rw [← map_mul, ← map_mul]
  exact subLayerAct_congr ((map_mul ψ e g).trans ((hcomm g).trans (map_mul ψ g e).symm))
    (hG (e * g)) (hF (e * g)) (hG (g * e)) (hF (g * e))

include hone in
theorem subLayerHom_one_mul :
    subLayerHom ψ hG hF 1 * subLayerHom ψ hG hF e = subLayerHom ψ hG hF e := by
  rw [← map_mul]
  exact subLayerAct_congr ((map_mul ψ 1 e).trans hone) (hG (1 * e)) (hF (1 * e)) (hG e) (hF e)

/-- **The corner of `ψ e` in the layer `G / F`**, a module over `R`. -/
def LayerCorner : Type u :=
  EndCornerPart (subLayerHom ψ hG hF) (subLayerHom ψ hG hF e)
    (subLayerHom_comm ψ hG hF e hcomm) (subLayerHom_one_mul ψ hG hF e hone)

instance : AddCommGroup (LayerCorner ψ hG hF e hcomm hone) :=
  inferInstanceAs (AddCommGroup (EndCornerPart (subLayerHom ψ hG hF) (subLayerHom ψ hG hF e)
    (subLayerHom_comm ψ hG hF e hcomm) (subLayerHom_one_mul ψ hG hF e hone)))

instance : Module R (LayerCorner ψ hG hF e hcomm hone) :=
  inferInstanceAs (Module R (EndCornerPart (subLayerHom ψ hG hF) (subLayerHom ψ hG hF e)
    (subLayerHom_comm ψ hG hF e hcomm) (subLayerHom_one_mul ψ hG hF e hone)))

local notation "ELay" => LayerCorner ψ hG hF e hcomm hone

/-- The underlying element of the layer. -/
def LayerCorner.val (x : LayerCorner ψ hG hF e hcomm hone) : SubLayer G F :=
  EndCornerPart.val (show EndCornerPart (subLayerHom ψ hG hF) (subLayerHom ψ hG hF e)
    (subLayerHom_comm ψ hG hF e hcomm) (subLayerHom_one_mul ψ hG hF e hone) from x)

theorem LayerCorner.ext {x y : LayerCorner ψ hG hF e hcomm hone}
    (h : LayerCorner.val ψ hG hF e hcomm hone x = LayerCorner.val ψ hG hF e hcomm hone y) :
    x = y :=
  EndCornerPart.ext h

theorem LayerCorner.prop (x : LayerCorner ψ hG hF e hcomm hone) :
    subLayerHom ψ hG hF e (LayerCorner.val ψ hG hF e hcomm hone x) =
      LayerCorner.val ψ hG hF e hcomm hone x :=
  EndCornerPart.prop (ψ := subLayerHom ψ hG hF) x

/-- An element of the layer fixed by `ψ e`. -/
def LayerCorner.mk (y : SubLayer G F) (h : subLayerHom ψ hG hF e y = y) :
    LayerCorner ψ hG hF e hcomm hone :=
  EndCornerPart.mk (ψ := subLayerHom ψ hG hF) y h

theorem LayerCorner.val_mk (y : SubLayer G F) (h : subLayerHom ψ hG hF e y = y) :
    LayerCorner.val ψ hG hF e hcomm hone (LayerCorner.mk ψ hG hF e hcomm hone y h) = y := rfl

theorem LayerCorner.val_zero : LayerCorner.val ψ hG hF e hcomm hone 0 = 0 := rfl

theorem LayerCorner.val_smul (g : R) (x : LayerCorner ψ hG hF e hcomm hone) :
    LayerCorner.val ψ hG hF e hcomm hone (g • x) =
      subLayerHom ψ hG hF g (LayerCorner.val ψ hG hF e hcomm hone x) := rfl

include he in
/-- `ψ e` is idempotent on the layer. -/
theorem subLayerHom_idem (y : SubLayer G F) :
    subLayerHom ψ hG hF e (subLayerHom ψ hG hF e y) = subLayerHom ψ hG hF e y := by
  rw [← Module.End.mul_apply, ← map_mul, he]

variable (htop : ∀ x : EndCornerPart ψ (ψ e) hcomm hone, x.val ∈ G)

/-- **The projection of the corner `ψ(e) V ⊆ G` to the corner of the layer `G / F`.** -/
def endCornerTopMap : EndCornerPart ψ (ψ e) hcomm hone →ₗ[R] ELay where
  toFun x := LayerCorner.mk ψ hG hF e hcomm hone (Submodule.Quotient.mk ⟨x.val, htop x⟩)
    (congrArg Submodule.Quotient.mk (Subtype.ext x.prop))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem endCornerTopMap_val (x : EndCornerPart ψ (ψ e) hcomm hone) :
    LayerCorner.val ψ hG hF e hcomm hone (endCornerTopMap ψ hG hF e hcomm hone htop x) =
      Submodule.Quotient.mk ⟨x.val, htop x⟩ :=
  rfl

/-- The kernel of the projection is `F ∩ ψ(e) V`. -/
theorem ker_endCornerTopMap :
    LinearMap.ker (endCornerTopMap ψ hG hF e hcomm hone htop) =
      endCornerSub ψ (ψ e) hcomm hone F hF := by
  ext x
  rw [LinearMap.mem_ker, mem_endCornerSub]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk ⟨x.val, htop x⟩ : SubLayer G F) = 0 :=
      (congrArg (LayerCorner.val ψ hG hF e hcomm hone) h).trans
        (LayerCorner.val_zero ψ hG hF e hcomm hone)
    exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero (F.comap G.subtype)).1 h1)
  · intro h
    have h1 : (Submodule.Quotient.mk ⟨x.val, htop x⟩ : SubLayer G F) = 0 :=
      (Submodule.Quotient.mk_eq_zero (F.comap G.subtype)).2 (Submodule.mem_comap.2 h)
    exact LayerCorner.ext ψ hG hF e hcomm hone
      (h1.trans (LayerCorner.val_zero ψ hG hF e hcomm hone).symm)

include he in
/-- The projection is onto when `e` is idempotent. -/
theorem endCornerTopMap_surjective :
    Function.Surjective (endCornerTopMap ψ hG hF e hcomm hone htop) := by
  intro y
  have key : ∀ z : SubLayer G F, subLayerHom ψ hG hF e z = z →
      ∃ x : EndCornerPart ψ (ψ e) hcomm hone,
        LayerCorner.val ψ hG hF e hcomm hone (endCornerTopMap ψ hG hF e hcomm hone htop x) =
          z := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H v =>
    intro hz
    refine ⟨EndCornerPart.mk (ψ e v.1) (by rw [← Module.End.mul_apply, ← map_mul, he]), ?_⟩
    exact (congrArg Submodule.Quotient.mk (Subtype.ext rfl)).trans hz
  obtain ⟨x, hx⟩ := key (LayerCorner.val ψ hG hF e hcomm hone y)
    (LayerCorner.prop ψ hG hF e hcomm hone y)
  exact ⟨x, LayerCorner.ext ψ hG hF e hcomm hone hx⟩

/-- **The top of a corner filtration is the corner of its layer**: for `ψ(e) V ⊆ G`, `e`
idempotent, `ψ(e) V / (F ∩ ψ(e) V) ≃ ψ(e) (G / F)` as `R`-modules. -/
def endCornerTopEquiv :
    (EndCornerPart ψ (ψ e) hcomm hone ⧸ endCornerSub ψ (ψ e) hcomm hone F hF) ≃ₗ[R]
      ELay :=
  (Submodule.quotEquivOfEq _ _ (ker_endCornerTopMap ψ hG hF e hcomm hone htop).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (endCornerTopMap_surjective ψ hG hF e he hcomm hone htop))

theorem endCornerTopEquiv_mk (x : EndCornerPart ψ (ψ e) hcomm hone) :
    endCornerTopEquiv ψ hG hF e he hcomm hone htop (Submodule.Quotient.mk x) =
      endCornerTopMap ψ hG hF e hcomm hone htop x := rfl

end Layer

namespace Stendhal

namespace CupCap

open KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

set_option hygiene false in
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)

/-- **The red-ordered idempotent is an idempotent.** -/
theorem redOrderedKLR_mul_self :
    (redOrderedKLR k Q Λc ν₀ * redOrderedKLR k Q Λc ν₀ : Rc) = redOrderedKLR k Q Λc ν₀ := by
  classical
  unfold redOrderedKLR
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [e_mul_e]
  rw [Finset.sum_ite_eq]
  exact ite_eq_left ht

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)
  (s : Seq (stendhalWeight ℓ (θ + γ)))

local notation "Bp" => BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ

set_option hygiene false in
local notation "WL" => windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s

set_option hygiene false in
local notation "WE" => windowEndAt j hj Q Λ Λc θ γ ν₀ X hQ s

set_option hygiene false in
local notation "Lay" c => SubLayer (cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)
  (cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c)

/-- `ε = ι_s(1_{red-ordered})` is an idempotent on `S_+(X)`. -/
theorem windowEndAt_redOrdered_idem (v : PlusStandard Q Λ Λc j hj θ ν₀ γ X hQ) :
    WE (redOrderedKLR k Q Λc ν₀) (WE (redOrderedKLR k Q Λc ν₀) v) =
      WE (redOrderedKLR k Q Λc ν₀) v := by
  rw [← Module.End.mul_apply, ← map_mul, redOrderedKLR_mul_self]

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The window at `s` on the layer `N`**, a non-unital ring map `W → End_k(F_N / F_{N-1})`;
`windowLayerHom … g = windowLayerAct … g N`. -/
def windowLayerHom :=
  subLayerHom (WE) (G := cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (Multiset.card (stendhalWeight 2 ν₀)))
    (F := cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (Multiset.card (stendhalWeight 2 ν₀)))
    (fun g _ hv => plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g hv)
    (fun g v hv => windowEndAt_mem_lower X hQ s (Multiset.card (stendhalWeight 2 ν₀)) g v hv)

theorem windowLayerHom_apply (g : Rc) :
    windowLayerHom j hj Q Λ Λc θ γ ν₀ X hQ s g = WL g (Multiset.card (stendhalWeight 2 ν₀)) :=
  rfl

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The corner `e'_s (F_N / F_{N-1})`** of the layer `N`, a `W`-module. -/
def PlusWindowLayerCorner : Type :=
  LayerCorner (WE) (G := cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (Multiset.card (stendhalWeight 2 ν₀)))
    (F := cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (Multiset.card (stendhalWeight 2 ν₀)))
    (fun g _ hv => plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ X s g hv)
    (fun g v hv => windowEndAt_mem_lower X hQ s (Multiset.card (stendhalWeight 2 ν₀)) g v hv)
    (redOrderedKLR k Q Λc ν₀) (windowEndAt_comm X hQ s) (windowEndAt_one_mul X hQ s)

instance : AddCommGroup (PlusWindowLayerCorner j hj Q Λ Λc θ γ ν₀ X hQ s) :=
  instAddCommGroupLayerCorner _ _ _ _ _ _

instance : Module Rc (PlusWindowLayerCorner j hj Q Λ Λc θ γ ν₀ X hQ s) :=
  instModuleLayerCorner _ _ _ _ _ _

/-- `e'_s S_+(X)` as a `W`-module. -/
local notation "Epart" => EndCornerPart (WE) (WE (redOrderedKLR k Q Λc ν₀))
  (windowEndAt_comm X hQ s) (windowEndAt_one_mul X hQ s)

/-- **top_s is the corner of `e'_s` in the layer `N`** (Webster v3, Lemma 7.19, trace half,
step L5): for `s` satisfying the head condition, `e'_s S_+(X) / (F_{N-1} ∩ e'_s S_+(X))`, the
target of the dévissage `plusWindowCorner_devissage`, is `e'_s (F_N / F_{N-1})`, as
`W`-modules. -/
def plusWindowTopEquiv (hsp : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j) :
    (Epart ⧸ endCornerSub _ _ (windowEndAt_comm X hQ s) (windowEndAt_one_mul X hQ s)
        (plusHeadFilt j hj Q Λ Λc θ γ ν₀ X hQ s 1) (plusHeadFilt_action X hQ s 1)) ≃ₗ[Rc]
      PlusWindowLayerCorner j hj Q Λ Λc θ γ ν₀ X hQ s :=
  endCornerTopEquiv (WE) _ (fun g v hv => windowEndAt_mem_lower X hQ s _ g v hv)
    (redOrderedKLR k Q Λc ν₀) redOrderedKLR_mul_self (windowEndAt_comm X hQ s)
    (windowEndAt_one_mul X hQ s) (fun x => plusWindowCornerFilt_top X hQ hsp s hs x)

theorem plusWindowTopEquiv_mk_val (hsp : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j) (x : Epart) :
    LayerCorner.val _ _ _ _ _ _ (plusWindowTopEquiv (ν₀ := ν₀) X hQ s hsp hs
      (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk ⟨x.val, plusWindowCornerFilt_top X hQ hsp s hs x⟩ := rfl

/-- `e'_s` is an idempotent on the layer `N`. -/
theorem windowLayerHom_redOrdered_idem (y : Lay (Multiset.card (stendhalWeight 2 ν₀))) :
    windowLayerHom j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀)
        (windowLayerHom j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀) y) =
      windowLayerHom j hj Q Λ Λc θ γ ν₀ X hQ s (redOrderedKLR k Q Λc ν₀) y :=
  subLayerHom_idem _ _ _ _ redOrderedKLR_mul_self y

/-- **top_s as the source of (T)**: the corner of `e'_s` in the layer `N` is, as a group, the
range of `e'_s = windowLayerAct … e_red N`. -/
def plusWindowTopRangeEquiv :
    PlusWindowLayerCorner j hj Q Λ Λc θ γ ν₀ X hQ s ≃+
      LinearMap.range (WL (redOrderedKLR k Q Λc ν₀) (Multiset.card (stendhalWeight 2 ν₀))) :=
  EndCornerPart.rangeEquiv (ψ := subLayerHom (WE) _ _) (windowLayerHom_redOrdered_idem X hQ s)

end CupCap

end Stendhal

end Categorification
