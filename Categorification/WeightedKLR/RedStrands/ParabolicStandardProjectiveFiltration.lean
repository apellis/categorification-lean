/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiltration
import Categorification.WeightedKLR.RedStrands.ParabolicStandardEmptyRed
import Categorification.WeightedKLR.RedStrands.Projectives
import Categorification.WeightedKLR.Induction.Generation

/-!
# Projectives filtered by standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, the
induction in the proof of Proposition 5.20, at the last red strand. Every
red-ordered loading of `T^λ_ν` has the form `(s, λ_ℓ, w)`: a loading `s` of `T^{λ'}`, the last
red strand, and a word `w` of black strands to its right. Its projective
`P = T^λ e(s, λ_ℓ, w)` is built in two steps.

* If `w` is empty, `P = T^λ e(s, λ_ℓ)` is the induction of `T^{λ'} e(s)` along the map adding
  the last red strand (Proposition 4.18), which is the standardization of `T^{λ'} e(s)` with
  empty last block (`emptyRedStandardEquiv`). So `P` is a single standard layer
  (`redLayer`).
* Appending a black strand `i` on the right is induction along `appendBlack`, which takes
  `T^λ e(t)` to `T^λ e(t, i)` (`indLIdealEquiv`), so `P ≅ F_w T^λ e(s, λ_ℓ)`.

By `hasFiltration_blackWord_stdLayer`, `P` is therefore filtered by the standardizations
`StdLayer.wordLayers w (redLayer s)` (`hasFiltration_loadingProj`): this is the categorical
form, in the last red strand, of the recursion behind the identity for `v_i^κ` in the
proof of Proposition 5.20 (v3: Lemma 5.19). It uses the route hypothesis
`FirstIndDeltaInjective` of Proposition 5.5 for every layer.

The layers are two-piece standardizations `S_{λ_ℓ}(N)` of modules `N` over
`T^{λ'} ⊗ R^{λ_ℓ}`. Webster's standard modules `S^κ_i` of Proposition 5.20 are obtained by
standardizing again in `T^{λ'}`; that iteration, and the comparison with the submodules
`P^{≥φ}` and `P^{>φ}`, are not part of this file.

## Main definitions

* `loadingProj`: the projective `T^λ e(s)` of a red-ordered loading.
* `blackWordLoading`: the loading `(t, w)` with the black word `w` appended on the right.
* `redLayer`: the standard layer `T^{λ'} e(s)` with empty last block.
* `blackWordMapEquiv`: `F_w` on isomorphisms.

## Main results

* `loadingProjBlackEquiv`: `T^λ e(t, i) ≅ Fᵢ T^λ e(t)`.
* `loadingProjWordEquiv`: `T^λ e(t, w) ≅ F_w T^λ e(t)`.
* `emptyLayerEquiv`: a layer with empty last block is an induced module.
* `loadingProjRedEquiv`: `T^λ e(s, λ_ℓ) ≅ S(T^{λ'} e(s))`.
* `hasFiltration_loadingProj`: `T^λ e(s, λ_ℓ, w)` is filtered by standardizations.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "old" => Λ ∘ Fin.castSucc

/-- The idempotent `e(s)` of a red-ordered loading in `T^λ_ν`. -/
abbrev loadingIdem {ν : Multiset I} (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s) :
    TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)

/-- **The projective `T^λ e(s)`** of a red-ordered loading, as a left module. -/
def loadingProj {ν : Multiset I} (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  ModuleCat.of _ (lIdeal (loadingIdem Q Λ s hs))

/-- **`T^λ e(t, i) ≅ Fᵢ T^λ e(t)`**: appending a black strand on the right is induction along
`appendBlack` (Webster, arXiv:1309.3796v2, §4.6, after Theorem 4.31). -/
def loadingProjBlackEquiv (i : I) {ν : Multiset I} (s : Seq (stendhalWeight (ℓ + 1) ν))
    (hs : IsRedOrdered s) :
    loadingProj Q Λ (appendBlackLoading i ν s) (appendBlackLoading_ordered i ν s hs) ≃ₗ[
      TensorProductAlgebra k Q Λ ((Si i) + ν)]
      blackIndModule Q Λ i (loadingProj Q Λ s hs) :=
  (LinearEquiv.ofEq _ _ (congrArg lIdeal (appendBlack_mk_e Q Λ i ν s hs).symm)).trans
    (indLIdealEquiv (appendBlackNU (Q := Q) (Λ := Λ) i ν)
      (isIdempotentElem_mk_e s hs)).symm

/-- The loading `(t, w)`: the black word `w` appended to `t` on the right, the last letter
first. -/
def blackWordLoading {ν : Multiset I} :
    (w : List I) → Seq (stendhalWeight (ℓ + 1) ν) →
      Seq (stendhalWeight (ℓ + 1) (wordWt w ν))
  | [], s => s
  | j :: w, s => appendBlackLoading j (wordWt w ν) (blackWordLoading w s)

omit [DecidableEq I] in
theorem blackWordLoading_ordered {ν : Multiset I} :
    (w : List I) → (s : Seq (stendhalWeight (ℓ + 1) ν)) → IsRedOrdered s →
      IsRedOrdered (blackWordLoading w s)
  | [], _, hs => hs
  | j :: w, s, hs => appendBlackLoading_ordered j _ _ (blackWordLoading_ordered w s hs)

/-- **`T^λ e(t, w) ≅ F_w T^λ e(t)`**. -/
def loadingProjWordEquiv {ν : Multiset I} :
    (w : List I) → (s : Seq (stendhalWeight (ℓ + 1) ν)) → (hs : IsRedOrdered s) →
      loadingProj Q Λ (blackWordLoading w s) (blackWordLoading_ordered w s hs) ≃ₗ[
        TensorProductAlgebra k Q Λ (wordWt w ν)]
        blackWordModule Q Λ w (loadingProj Q Λ s hs)
  | [], _, _ => LinearEquiv.refl _ _
  | j :: w, s, hs =>
    ((loadingProjBlackEquiv Q Λ j (blackWordLoading w s) (blackWordLoading_ordered w s hs)).trans
      (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) j (wordWt w ν))
        (loadingProjWordEquiv w s hs)) :
      _ ≃ₗ[TensorProductAlgebra k Q Λ ((Si j) + wordWt w ν)] _)

section Red

variable (θ : Multiset I)

/-- The idempotent `e(s)` of a red-ordered loading of `T^{λ'}_{θ}`. -/
abbrev oldIdem (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    TensorProductAlgebra k Q (old) (θ + 0) :=
  TensorProductAlgebra.mk Q (old) (θ + 0) (StendhalAlgebra.e s hs)

/-- The factor-algebra module structure on `T^{λ'} e(s)`, through
`T^{λ'} ⊗ R^{λ_ℓ}_0 ≅ T^{λ'}`. -/
abbrev redFactorInst (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    Module (parabolicFactorAlgebra Q Λ θ 0) (lIdeal (oldIdem Q Λ θ s hs)) :=
  Module.compHom _ (emptyFactorToOld Q Λ θ).toAlgHom.toRingHom

/-- `T^{λ'} e(s)` as a module over `T^{λ'} ⊗ R^{λ_ℓ}_0`. -/
def redFactorModule (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    FactorModule Q Λ θ 0 :=
  letI := redFactorInst Q Λ θ s hs
  { carrier := lIdeal (oldIdem Q Λ θ s hs)
    tower := ⟨fun c t n => by
      change (emptyFactorToOld Q Λ θ (c • t)) • n = c • (emptyFactorToOld Q Λ θ t • n)
      rw [map_smul, smul_assoc]⟩ }

/-- **The standard layer `T^{λ'} e(s)`** with empty last block. -/
def redLayer (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    StdLayer Q Λ (θ + 0) :=
  ⟨θ, 0, rfl, redFactorModule Q Λ θ s hs⟩

variable (hQ : KLRSymm Q)

/-- The input of `EmptyRedInd` for `T^{λ'} e(s)` is `T^{λ'} e(s)`. -/
def redInputEquiv (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    EmptyRedInput Q Λ θ (redFactorModule Q Λ θ s hs).carrier ≃ₗ[
      TensorProductAlgebra k Q (old) (θ + 0)] lIdeal (oldIdem Q Λ θ s hs) where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' t n := by
    rw [RingHom.id_apply]
    change emptyFactorToOld Q Λ θ ((emptyFactorToOld Q Λ θ).symm t) •
      (show lIdeal (oldIdem Q Λ θ s hs) from n) =
        t • (show lIdeal (oldIdem Q Λ θ s hs) from n)
    rw [AlgEquiv.apply_symm_apply]
  left_inv _ := rfl
  right_inv _ := rfl

/-- The module of the layer `⟨θ, β, rfl, M⟩` is `S(M)` over `T(θ + β)`. -/
def layerStandardEquiv (β : Multiset I) (M : FactorModule Q Λ θ β) :
    stdLayerModule Q Λ hQ ⟨θ, β, rfl, M⟩ ≃ₗ[TensorProductAlgebra k Q Λ (θ + β)]
      ParabolicStandardT Q Λ θ β M.carrier hQ :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- A standard layer with empty last block is the induction along adding the last red strand. -/
def emptyLayerEquiv (M : FactorModule Q Λ θ 0) :
    stdLayerModule Q Λ hQ ⟨θ, 0, rfl, M⟩ ≃ₗ[TensorProductAlgebra k Q Λ (θ + 0)]
      EmptyRedInd Q Λ θ M.carrier :=
  (layerStandardEquiv Q Λ θ hQ 0 M).trans (emptyRedStandardEquiv Q Λ θ M.carrier hQ)

/-- **`T^λ e(s, λ_ℓ) ≅ S(T^{λ'} e(s))`**: the projective of a loading ending in the last red
strand is the standardization of `T^{λ'} e(s)` with empty last block (Webster,
arXiv:1309.3796v2, Proposition 4.18 and the case `β = ∅` of the proof of Proposition 5.5). -/
def loadingProjRedEquiv (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    loadingProj Q Λ (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs) ≃ₗ[
      TensorProductAlgebra k Q Λ (θ + 0)] stdLayerModule Q Λ hQ (redLayer Q Λ θ s hs) :=
  have hE : emptyRedHom Q Λ θ (oldIdem Q Λ θ s hs) =
      loadingIdem Q Λ (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs) :=
    (emptyRedHom_apply Q Λ θ _).trans (appendRed_mk_e Q Λ (θ + 0) s hs)
  (((LinearEquiv.ofEq _ _ (congrArg lIdeal hE.symm)).trans
    (indLIdealEquiv (emptyRedHom Q Λ θ) (f := oldIdem Q Λ θ s hs)
      (isIdempotentElem_mk_e s hs)).symm).trans
    (Ind.mapEquiv (φ := emptyRedHom Q Λ θ) (redInputEquiv Q Λ θ s hs)).symm).trans
    (emptyLayerEquiv Q Λ θ hQ (redFactorModule Q Λ θ s hs)).symm

end Red

/-- `F_w` on isomorphisms. -/
def blackWordMapEquiv {ν : Multiset I} :
    (w : List I) → {X Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)} →
      (X ≃ₗ[TensorProductAlgebra k Q Λ ν] Y) →
      blackWordModule Q Λ w X ≃ₗ[TensorProductAlgebra k Q Λ (wordWt w ν)]
        blackWordModule Q Λ w Y
  | [], _, _, e => e
  | j :: w, _, _, e =>
    (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) j (wordWt w ν))
      (blackWordMapEquiv w e) : _ ≃ₗ[TensorProductAlgebra k Q Λ ((Si j) + wordWt w ν)] _)

variable (hQ : KLRSymm Q)

/-- **Projectives with black strands right of the last red strand are filtered by
standardizations** (Webster, arXiv:1309.3796v2, proof of Proposition 5.20, the recursion behind
the identity for `v_i^κ`): for a red-ordered loading `s` of `T^{λ'}` and a black word `w`, the
projective `T^λ e(s, λ_ℓ, w) ≅ F_w S(T^{λ'} e(s))` has a filtration whose layers are the
standardizations `S(N)` produced by `F_w` from `T^{λ'} e(s)`. This uses the route hypothesis
`FirstIndDeltaInjective` for every layer (`AllDeltaInjective`). -/
theorem hasFiltration_loadingProj (C : QuantumGroup.CartanDatum I) (hR : IsRouquierQ C Q)
    (hall : AllDeltaInjective Q Λ hQ) (w : List I) {θ : Multiset I}
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    HasFiltration (stdLayerModule Q Λ hQ) ((redLayer Q Λ θ s hs).wordLayers Q Λ w)
      (loadingProj Q Λ (blackWordLoading w (appendRedLoading s))
        (blackWordLoading_ordered w _ ((appendRedLoading_ordered_iff s).2 hs))) :=
  HasFiltration.of_equiv (hasFiltration_blackWord_stdLayer C hR hall w (redLayer Q Λ θ s hs))
    ((loadingProjWordEquiv Q Λ w (appendRedLoading s)
      ((appendRedLoading_ordered_iff s).2 hs)).trans
      (blackWordMapEquiv Q Λ w (loadingProjRedEquiv Q Λ θ hQ s hs))).symm

end Categorification.Stendhal
