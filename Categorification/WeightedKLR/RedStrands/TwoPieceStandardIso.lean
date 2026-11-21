/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardInverse

/-!
# Standardization of `S_t ⊠ R e(u)` is a standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. For a red-ordered loading `t` of the first `ℓ` red strands and a black
sequence `u`, the standardization `S(S_t ⊠ R^{λ_{ℓ+1}} e(u))` is isomorphic to the standard
module `S_{t λ_{ℓ+1} u}` of Definition 5.1.

The map `S(S_t ⊠ R e(u)) → S_{t λ_{ℓ+1} u}` is the extension (`parabolicDesc`) of
`[a] ⊗ [c] ↦ a · c · [e(t λ_{ℓ+1} u)]`, where `a` acts through the prefix action and `c`
through the last-block action; its inverse sends `[e(t λ_{ℓ+1} u)]` to the unit vector
`1 ⊗ [e(t)] ⊗ [e(u)]`, which is killed by all loadings above the two-piece loading by
`parabolicStandardAction_upper_eq_zero`.

## Main results

* `twoPieceStandardEquiv`: the isomorphism, intertwining the actions of `T^λ_{θ+β}`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) {θ β : Multiset I}
  {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β)

local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β
local notation "tp" => twoPieceLoading θ β t u
local notation "htp" => isRedOrdered_twoPieceLoading ht u
local notation "Z" => leftStandard Q Λ (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u)
local notation "κ" => parabolicDescAction Q Λ θ β (Algebra.lsmul k k Z)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "P" => redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ
local notation "plc" => parabolicLastCyclotomic Q Λ β
local notation "hB" => lastRedBlackWeight (ℓ := ℓ) β
local notation "St" => leftStandard Q (Λ ∘ Fin.castSucc) t ht

/-- The prefix action on `S_{t λ_{ℓ+1} u}`, through `T^{λ'}`. -/
def twoPiecePrefixFactor : Told →ₙₐ[k] Module.End k Z :=
  Classical.choose (exists_twoPiecePrefixAction_factor Q Λ ht u)

theorem twoPiecePrefixAction_eq (z : KLRAlgebra k S α) :
    twoPiecePrefixAction Q Λ ht u z = twoPiecePrefixFactor Q Λ ht u (P z) :=
  Classical.choose_spec (exists_twoPiecePrefixAction_factor Q Λ ht u) z

/-- The last-block action on `S_{t λ_{ℓ+1} u}`, through `R^{λ_{ℓ+1}}`. -/
def twoPieceLastFactor : Cyc →ₙₐ[k] Module.End k Z :=
  Classical.choose (exists_twoPieceLastAction_factor Q Λ ht u)

theorem twoPieceLastAction_eq (z : KLRAlgebra k S _) :
    twoPieceLastAction Q Λ ht u z = twoPieceLastFactor Q Λ ht u (plc (castKLR S hB z)) :=
  Classical.choose_spec (exists_twoPieceLastAction_factor Q Λ ht u) z

theorem twoPiecePrefixFactor_seqIdem {t' : Seq (stendhalWeight ℓ θ)} (ht' : IsRedOrdered t')
    (hlt : StendhalLT t t') :
    twoPiecePrefixFactor Q Λ ht u (seqIdem Q (Λ ∘ Fin.castSucc) t' ht') = 0 := by
  change twoPiecePrefixFactor Q Λ ht u (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ
    (StendhalAlgebra.e t' ht')) = 0
  rw [← redSubfamilyProjection_e Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ t' ht',
    ← twoPiecePrefixAction_eq, twoPiecePrefixAction, concatLeftHom_e]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [twoPieceDescAction_apply Q Λ ht, leftStandardAllOrders_cast_e]
  exact leftStandardAllOrders_e htp (stendhalLT_twoPiece_concatLoading u hlt d)

theorem twoPiecePrefixFactor_leftUpper {w : Told}
    (hw : w ∈ leftUpper Q (Λ ∘ Fin.castSucc) t ht) : twoPiecePrefixFactor Q Λ ht u w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', a, hlt, rfl⟩ := hx
    rw [map_mul, map_mul, twoPiecePrefixFactor_seqIdem Q Λ ht u ht' hlt, zero_mul, zero_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    change twoPiecePrefixFactor Q Λ ht u (a * x) = 0
    rw [map_mul, hx, mul_zero]

/-- The prefix factor as a `k`-linear map on `T^{λ'} e(t)`. -/
def twoPiecePrefixLin : lIdeal (seqIdem Q (Λ ∘ Fin.castSucc) t ht) →ₗ[k] Module.End k Z where
  toFun w := twoPiecePrefixFactor Q Λ ht u w
  map_add' _ _ := map_add _ _ _
  map_smul' c w := by
    change twoPiecePrefixFactor Q Λ ht u (c • (w : Told)) = _
    rw [map_smul]; rfl

/-- `[a] ↦ a`, acting on `S_{t λ_{ℓ+1} u}` through the prefix action. -/
def twoPiecePrefixMap : St →ₗ[k] Module.End k Z :=
  (((leftUpper Q (Λ ∘ Fin.castSucc) t ht).comap
      (lIdeal (seqIdem Q (Λ ∘ Fin.castSucc) t ht)).subtype).restrictScalars k).liftQ
    (twoPiecePrefixLin Q Λ ht u) fun _ hw => twoPiecePrefixFactor_leftUpper Q Λ ht u hw

theorem twoPiecePrefixMap_mk (w : lIdeal (seqIdem Q (Λ ∘ Fin.castSucc) t ht)) :
    twoPiecePrefixMap Q Λ ht u (Submodule.Quotient.mk w) =
      twoPiecePrefixFactor Q Λ ht u w := rfl

local notation "z₀" => leftStandardUnit Q Λ (twoPieceLoading θ β t u)
  (isRedOrdered_twoPieceLoading ht u)
local notation "X" => ModuleCat.of Told St
local notation "Y" => cycProj Q Λ β u

/-- The element of `R^{λ_{ℓ+1}}` underlying a vector of `R^{λ_{ℓ+1}} e(u)`. -/
def cycVal (y : KMod (k := k) Y) : Cyc :=
  ((show lIdeal (CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
    (e u)) from y) : Cyc)

/-- `[c] ↦ c · [e(t λ_{ℓ+1} u)]`, through the last-block action. -/
def twoPieceLastVec : KMod (k := k) Y →ₗ[k] Z where
  toFun y := twoPieceLastFactor Q Λ ht u (cycVal Q Λ u y) z₀
  map_add' y y' := by
    change twoPieceLastFactor Q Λ ht u (cycVal Q Λ u y + cycVal Q Λ u y') z₀ = _
    rw [map_add, LinearMap.add_apply]
  map_smul' c y := by
    change twoPieceLastFactor Q Λ ht u (algebraMap k Cyc c * cycVal Q Λ u y) z₀ = _
    rw [← Algebra.smul_def, map_smul, LinearMap.smul_apply]
    rfl

theorem twoPieceLastVec_apply (y : KMod (k := k) Y) :
    twoPieceLastVec Q Λ ht u y = twoPieceLastFactor Q Λ ht u (cycVal Q Λ u y) z₀ := rfl

/-- `[a] ⊗ [c] ↦ a · c · [e(t λ_{ℓ+1} u)]`, the map `S_t ⊠ R e(u) → S_{t λ_{ℓ+1} u}`. -/
def twoPieceFactorMap : ExtTensor k (KMod (k := k) X) (KMod (k := k) Y) →ₗ[k] Z :=
  ExtTensor.lift (LinearMap.mk₂ k
    (fun (m : KMod (k := k) X) y => twoPiecePrefixMap Q Λ ht u m (twoPieceLastVec Q Λ ht u y))
    (fun m m' y => by
      change twoPiecePrefixMap Q Λ ht u ((show St from m) + (show St from m')) _ = _
      rw [map_add, LinearMap.add_apply])
    (fun c m y => by
      change twoPiecePrefixMap Q Λ ht u (algebraMap k Told c • (show St from m)) _ = _
      rw [algebraMap_smul, map_smul, LinearMap.smul_apply])
    (fun m y y' => (congrArg _ (map_add _ y y')).trans (map_add _ _ _))
    (fun c m y => (congrArg _ (map_smul _ c y)).trans (map_smul _ _ _)))

theorem twoPieceFactorMap_tmul (m : KMod (k := k) X) (y : KMod (k := k) Y) :
    twoPieceFactorMap Q Λ ht u (ExtTensor.tmul m y) =
      twoPiecePrefixMap Q Λ ht u m (twoPieceLastVec Q Λ ht u y) := rfl

theorem twoPieceLastFactor_plc (z : KLRAlgebra k S δ) :
    twoPieceLastFactor Q Λ ht u (plc z) =
      κ (concat S α δ (e (Seq.map (addRedColor ℓ) t) ⊗ₜ z)) := by
  obtain ⟨z, rfl⟩ := (castKLR S hB).surjective z
  rw [← twoPieceLastAction_eq]
  rfl

/-- The composite of the two block actions on `[e(t λ_{ℓ+1} u)]`. -/
theorem twoPieceFactor_formula (w : KLRAlgebra k S α) (z : KLRAlgebra k S δ) :
    twoPiecePrefixFactor Q Λ ht u (P w) (twoPieceLastFactor Q Λ ht u (plc z) z₀) =
      κ (concat S α δ ((w * e (Seq.map (addRedColor ℓ) t)) ⊗ₜ z)) z₀ := by
  have h1 := twoPiecePrefixAction_eq Q Λ ht u w
  have h2 := twoPieceLastFactor_plc Q Λ ht u z
  rw [← h1]
  rw [h2]
  rw [twoPiecePrefixAction_apply]
  have h3 : concat S α δ ((w * e (Seq.map (addRedColor ℓ) t)) ⊗ₜ z) =
      concat S α δ (w ⊗ₜ 1) * concat S α δ (e (Seq.map (addRedColor ℓ) t) ⊗ₜ z) := by
    rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact (congrArg (fun f : Module.End k Z => f z₀) (map_mul κ _ _)).symm.trans
    (congrArg (fun a => κ a z₀) h3.symm)

end Categorification.Stendhal
