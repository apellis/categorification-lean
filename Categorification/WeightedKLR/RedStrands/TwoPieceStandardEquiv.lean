/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardIso

/-!
# Standardization of `S_t ⊠ R e(u)` is a standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, step in
the proof of Proposition 5.20 (identifying the layers of the filtration of projectives). For a
red-ordered loading `t` of the first `ℓ` red strands and a black sequence `u`, the
standardization `S(S_t ⊠ R^{λ_{ℓ+1}} e(u))` is isomorphic, as a module over `T^λ`, to the
standard module `S_{t λ_{ℓ+1} u}` of Definition 5.1.

The map `S(S_t ⊠ R e(u)) → S_{t λ_{ℓ+1} u}` extends the input map through the universal property
of standardization (`parabolicDesc`). The inverse sends the generator `[e(t λ_{ℓ+1} u)]` to
`1 ⊗ [e(t)] ⊗ [e(u)]`; it exists because loadings above `t λ_{ℓ+1} u` act by zero on the
standardization (`parabolicStandardAction_upper_eq_zero`).

## Main results

* `twoPieceStandardEquiv`: the isomorphism `S(S_t ⊠ R e(u)) ≅ S_{t λ_{ℓ+1} u}`.
* `twoPieceStandardEquiv_symm_unit`: it matches the two unit vectors.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) {θ β : Multiset I}
  {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β) (hQ : KLRSymm Q)

local notation "Z" => leftStandard Q Λ (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "St" => leftStandard Q (Λ ∘ Fin.castSucc) t ht
local notation "Nf" =>
  FactorModule.carrier (tensorFactor Q Λ (ModuleCat.of Told St) (cycProj Q Λ β u))


local notation "tp" => twoPieceLoading θ β t u
local notation "htp" => isRedOrdered_twoPieceLoading ht u
local notation "V" => ParabolicStandardT Q Λ θ β Nf hQ
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "C" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "Pr" => redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ
local notation "plc" => parabolicLastCyclotomic Q Λ β
local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)
local notation "z₀" => leftStandardUnit Q Λ (twoPieceLoading θ β t u)
  (isRedOrdered_twoPieceLoading ht u)

local notation "KX" => KMod (k := k) (ModuleCat.of Told St)
local notation "KY" => KMod (k := k) (cycProj Q Λ β u)
local notation "Ext" => ExtTensor k KX KY

/-- The unit vector `[e(t)] ⊗ [e(u)]` of `S_t ⊠ R^{λ_{ℓ+1}} e(u)`. -/
def twoPieceInputUnit : Ext :=
  ExtTensor.tmul (leftStandardUnit Q (Λ ∘ Fin.castSucc) t ht : St) (cycUnit Q Λ u)

local notation "n₀" => twoPieceInputUnit Q Λ ht u

theorem twoPieceExt_upper (c : Seq (stendhalWeight ℓ θ)) (hc : IsRedOrdered c)
    (hlt : StendhalLT t c) (n : Ext) :
    ((TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e c hc) ⊗ₜ[k] (1 : C)) :
      parabolicFactorAlgebra Q Λ θ β) • n = 0 := by
  induction n using ExtTensor.induction_on with
  | zero => exact smul_zero _
  | tmul m y =>
    refine (ExtTensor.smul_tmul (P := KX) (Q := KY) _ _ _ _).trans ?_
    have h0 : (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e c hc) • m :
        KX) = 0 := by
      have h := leftStandard_seqIdem_mul_smul hc hlt 1 (show St from m)
      rw [mul_one] at h
      exact h
    exact (congrArg (fun v : KX => ExtTensor.tmul v ((1 : C) • y)) h0).trans
      (ExtTensor.zero_tmul _)
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- Loadings above `t` kill `S_t ⊠ R^{λ_{ℓ+1}} e(u)`. -/
theorem twoPieceInput_upper (c : Seq (stendhalWeight ℓ θ)) (hc : IsRedOrdered c)
    (hlt : StendhalLT t c) (n : Nf) :
    ((TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e c hc) ⊗ₜ[k] (1 : C)) :
      parabolicFactorAlgebra Q Λ θ β) • n = 0 :=
  twoPieceExt_upper Q Λ ht u c hc hlt n

theorem twoPieceInput_e_smul :
    ((Pr (e (Seq.map (addRedColor ℓ) t)) ⊗ₜ[k] plc (e (Seq.map lc (SingleRed.insertWord β u)))) :
      parabolicFactorAlgebra Q Λ θ β) • (n₀ : Ext) = n₀ := by
  rw [redSubfamilyProjection_e Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ t ht,
    parabolicLastCyclotomic_e Q Λ β u]
  refine (ExtTensor.smul_tmul (P := KX) (Q := KY) _ _ _ _).trans
    (congrArg₂ ExtTensor.tmul ?_ ?_)
  · exact (Submodule.Quotient.mk_smul _ _ _).symm.trans
      (congrArg _ (Subtype.ext (seqIdem_mul_self Q (Λ ∘ Fin.castSucc) t ht)))
  · exact Subtype.ext (isIdempotentElem_cyc_e Q Λ β u).eq

/-- The image of `e(t λ_{ℓ+1} u)` in `T^λ`. -/
theorem twoPieceAffine_e :
    parabolicAffine Q Λ θ β (concat (stendhalQ Q Λ) _ _
      (e (Seq.map (addRedColor ℓ) t) ⊗ₜ e (Seq.map lc (SingleRed.insertWord β u)))) =
      seqIdem Q Λ tp htp := by
  have he : orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.e tp) =
      StendhalAlgebra.e tp htp :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem _).trans (ite_eq_left htp))
  rw [concat_e_tmul_e, parabolicAffine, castKLR_e]
  exact congrArg (TensorProductAlgebra.mk Q Λ (θ + β)) he

/-- The map `S(S_t ⊠ R e(u)) → S_{t λ_{ℓ+1} u}`. -/
def twoPieceStandardTo : V →ₗ[T] Z where
  toFun := parabolicDesc Q Λ θ β (Algebra.lsmul k k Z) (twoPieceInputMap Q Λ ht u)
    (twoPieceInputMap_smul Q Λ ht u)
  map_add' := map_add _
  map_smul' a m := parabolicDesc_smul Q Λ θ β hQ (Algebra.lsmul k k Z)
    (twoPieceInputMap Q Λ ht u) (twoPieceInputMap_smul Q Λ ht u) a m

theorem twoPieceStandardTo_unit (n : Nf) :
    twoPieceStandardTo Q Λ ht u hQ (parabolicStandardUnit Q Λ θ β Nf n) =
      twoPieceInputMap Q Λ ht u n :=
  parabolicDesc_unit Q Λ θ β _ _ _ n

theorem twoPieceStandard_upper (s : Seq (stendhalWeight (ℓ + 1) (θ + β))) (hs : IsRedOrdered s)
    (a : T) (hlt : StendhalLT tp s) (v : V) : (seqIdem Q Λ s hs * a) • v = 0 := by
  rw [mul_smul]
  exact LinearMap.congr_fun (parabolicStandardAction_upper_eq_zero Q Λ θ β hQ t u
    (twoPieceInput_upper Q Λ ht u) s hs hlt) (a • v)

/-- The unit vector `1 ⊗ [e(t)] ⊗ [e(u)]` of the standardization. -/
def twoPieceStandardUnit : V := parabolicStandardUnit Q Λ θ β Nf (twoPieceInputUnit Q Λ ht u)

local notation "v₀" => twoPieceStandardUnit Q Λ ht u hQ

theorem twoPieceStandard_seqIdem_unit : seqIdem Q Λ tp htp • v₀ = v₀ := by
  have h := (parabolicStandardAction_concat_unit Q Λ θ β Nf hQ
    (e (Seq.map (addRedColor ℓ) t) ⊗ₜ e (Seq.map lc (SingleRed.insertWord β u)))
    (twoPieceInputUnit Q Λ ht u)).trans
    (congrArg (parabolicStandardUnit Q Λ θ β Nf) (twoPieceInput_e_smul Q Λ ht u))
  rw [← twoPieceAffine_e Q Λ ht u]
  exact h

/-- The map `S_{t λ_{ℓ+1} u} → S(S_t ⊠ R e(u))`, `[e(t λ_{ℓ+1} u)] ↦ 1 ⊗ [e(t)] ⊗ [e(u)]`. -/
def twoPieceStandardFrom : Z →ₗ[T] V :=
  leftStandardLift tp htp v₀ fun s hs a hlt => twoPieceStandard_upper Q Λ ht u hQ s hs a hlt v₀

theorem twoPieceStandardFrom_unit : twoPieceStandardFrom Q Λ ht u hQ z₀ = v₀ :=
  leftStandardLift_unit tp htp _ (twoPieceStandard_seqIdem_unit Q Λ ht u hQ) _

theorem twoPieceStandardTo_from (z : Z) :
    twoPieceStandardTo Q Λ ht u hQ (twoPieceStandardFrom Q Λ ht u hQ z) = z := by
  have h : (twoPieceStandardTo Q Λ ht u hQ).comp (twoPieceStandardFrom Q Λ ht u hQ) =
      LinearMap.id :=
    leftStandard_hom_ext tp htp ((congrArg (twoPieceStandardTo Q Λ ht u hQ)
      (twoPieceStandardFrom_unit Q Λ ht u hQ)).trans
      ((twoPieceStandardTo_unit Q Λ ht u hQ _).trans (twoPieceFactorMap_unit Q Λ ht u)))
  exact LinearMap.congr_fun h z

local notation "N₀" => ParabolicInput Q Λ θ β Nf
local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)

/-- The unit vector `n₀`, as a vector of the input module of induction. -/
def twoPieceInputUnitP : N₀ := twoPieceInputUnit Q Λ ht u

local notation "m₀" => twoPieceInputUnitP Q Λ ht u

theorem twoPieceStandardFrom_input_smul (b : TensorKLR S α δ) :
    twoPieceStandardFrom Q Λ ht u hQ (twoPieceInputMap Q Λ ht u
      (b • m₀)) =
      parabolicStandardUnit Q Λ θ β Nf (b • m₀) :=
  (congrArg (twoPieceStandardFrom Q Λ ht u hQ)
    (twoPieceInputMap_smul Q Λ ht u b (twoPieceInputUnit Q Λ ht u))).trans <|
  (congrArg (fun z => twoPieceStandardFrom Q Λ ht u hQ
    ((parabolicAffine Q Λ θ β (concat S α δ b) : T) • z))
    (twoPieceFactorMap_unit Q Λ ht u)).trans <|
  (map_smul (twoPieceStandardFrom Q Λ ht u hQ) _ z₀).trans <|
  (congrArg _ (twoPieceStandardFrom_unit Q Λ ht u hQ)).trans
    (parabolicStandardAction_concat_unit Q Λ θ β Nf hQ b (twoPieceInputUnit Q Λ ht u))

theorem twoPieceExt_eq_smul (m : KX) (y : KY) :
    ∃ b : TensorKLR S α δ, (ExtTensor.tmul m y : Ext) = b • m₀ := by
  have hm0 : ∃ w', (Submodule.Quotient.mk w' : St) = m := Submodule.Quotient.mk_surjective _ m
  obtain ⟨w', rfl⟩ := hm0
  have hw0 : ∃ w, Pr w = w'.1 :=
    redSubfamilyProjection_surjective Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ _
  obtain ⟨w, hw⟩ := hw0
  have hz0 : ∃ z, plc z = cycVal Q Λ u y := parabolicLastCyclotomic_surjective Q Λ β _
  obtain ⟨z, hz⟩ := hz0
  refine ⟨w ⊗ₜ z, ?_⟩
  have h1 : parabolicInputMap Q Λ θ β (w ⊗ₜ z) = Pr w ⊗ₜ[k] plc z :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  refine Eq.trans ?_ (congrArg (fun d : parabolicFactorAlgebra Q Λ θ β =>
    d • (twoPieceInputUnit Q Λ ht u : Ext)) h1).symm
  refine Eq.trans (congrArg₂ ExtTensor.tmul ?_ ?_)
    (ExtTensor.smul_tmul (P := KX) (Q := KY) _ _ _ _).symm
  · refine Eq.trans ?_ (Submodule.Quotient.mk_smul _ _ _)
    refine congrArg _ (Subtype.ext ?_)
    change w'.1 = Pr w * seqIdem Q (Λ ∘ Fin.castSucc) t ht
    rw [hw]
    exact w'.2.symm
  · refine Subtype.ext ?_
    change cycVal Q Λ u y = plc z * CycKLR.mk k Q
      (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β (e u)
    rw [hz]
    exact y.2.symm

/-- On the input module, `S_{t λ_{ℓ+1} u} → S(S_t ⊠ R e(u))` inverts the input map. -/
theorem twoPieceStandardFrom_input (n : Ext) :
    twoPieceStandardFrom Q Λ ht u hQ (twoPieceInputMap Q Λ ht u n) =
      parabolicStandardUnit Q Λ θ β Nf n := by
  induction n using ExtTensor.induction_on with
  | zero =>
    exact (congrArg (twoPieceStandardFrom Q Λ ht u hQ) (map_zero (twoPieceInputMap Q Λ ht u))).trans
      ((map_zero _).trans (map_zero (parabolicStandardUnit Q Λ θ β Nf)).symm)
  | tmul m y =>
    obtain ⟨b, hb⟩ := twoPieceExt_eq_smul Q Λ ht u m y
    exact (congrArg (fun x : N₀ => twoPieceStandardFrom Q Λ ht u hQ
      (twoPieceInputMap Q Λ ht u x)) hb).trans
      ((twoPieceStandardFrom_input_smul Q Λ ht u hQ b).trans
        (congrArg (parabolicStandardUnit Q Λ θ β Nf) hb).symm)
  | add x y hx hy =>
    exact (congrArg (twoPieceStandardFrom Q Λ ht u hQ)
      (map_add (twoPieceInputMap Q Λ ht u) x y)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add (parabolicStandardUnit Q Λ θ β Nf) x y).symm))

theorem twoPieceShuffle_tmul (r : IndBimod S α δ) (n : N₀) :
    (BalancedTensor.tmul r n : ParabolicShuffle Q Λ θ β Nf) =
      r.1 • indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀ n := by
  rw [indShuffleUnit, BalancedTensor.smul_tmul']
  congr 1
  exact Subtype.ext r.2.symm

/-- A vector of the standardization, as a vector of the `T^λ`-module. -/
def twoPieceStandardOf (w : ParabolicStandard Q Λ θ β Nf) : V := w

/-- The quotient map from the shuffle module onto the standardization. -/
def twoPieceStandardMk (x : ParabolicShuffle Q Λ θ β Nf) : V :=
  (excludedSpace (parabolicShuffleAction Q Λ θ β Nf) (parabolicOrderedLoadings (ℓ := ℓ) θ β)).mkQ x

/-- The unit vector `1 ⊗ n` of the standardization. -/
def twoPieceStandardUnitOf (n : N₀) : V := parabolicStandardUnit Q Λ θ β Nf n

theorem twoPieceStandard_smul_unitOf (a : T) (n : N₀) :
    a • twoPieceStandardUnitOf Q Λ ht u hQ n =
      twoPieceStandardOf Q Λ ht u hQ (parabolicStandardAction Q Λ θ β Nf hQ a
        (parabolicStandardUnit Q Λ θ β Nf n)) := rfl

theorem twoPieceStandardMk_tmul (r : IndBimod S α δ) (n : N₀) :
    twoPieceStandardMk Q Λ ht u hQ (BalancedTensor.tmul r n) =
      (parabolicAffine Q Λ θ β r.1 : T) • twoPieceStandardUnitOf Q Λ ht u hQ n := by
  rw [twoPieceStandard_smul_unitOf]
  unfold twoPieceStandardOf
  refine Eq.trans ?_
    (LinearMap.congr_fun (parabolicStandardAction_affine Q Λ θ β Nf hQ r.1) _).symm
  refine Eq.trans ?_ (orderedShuffleAction_mkQ _ _ _ r.1
    (indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀ n)).symm
  exact congrArg _ (twoPieceShuffle_tmul Q Λ ht u r n)

theorem twoPieceStandardMk_surjective : Function.Surjective (twoPieceStandardMk Q Λ ht u hQ) :=
  Submodule.mkQ_surjective _

theorem twoPieceStandardFrom_to (v : V) :
    twoPieceStandardFrom Q Λ ht u hQ (twoPieceStandardTo Q Λ ht u hQ v) = v := by
  obtain ⟨x, rfl⟩ := twoPieceStandardMk_surjective Q Λ ht u hQ v
  induction x using BalancedTensor.induction_on with
  | zero =>
    have h0 : twoPieceStandardMk Q Λ ht u hQ (0 : ParabolicShuffle Q Λ θ β Nf) = 0 :=
      map_zero (Submodule.mkQ _)
    rw [h0, map_zero, map_zero]
  | tmul r n =>
    rw [twoPieceStandardMk_tmul]
    have hn : twoPieceStandardFrom Q Λ ht u hQ (twoPieceStandardTo Q Λ ht u hQ
        (twoPieceStandardUnitOf Q Λ ht u hQ n)) = twoPieceStandardUnitOf Q Λ ht u hQ n :=
      (congrArg (twoPieceStandardFrom Q Λ ht u hQ) (twoPieceStandardTo_unit Q Λ ht u hQ n)).trans
        (twoPieceStandardFrom_input Q Λ ht u hQ n)
    exact (congrArg (twoPieceStandardFrom Q Λ ht u hQ)
      (LinearMap.map_smul (twoPieceStandardTo Q Λ ht u hQ) _ _)).trans
      ((LinearMap.map_smul (twoPieceStandardFrom Q Λ ht u hQ) _ _).trans
        (congrArg (fun z : V => (parabolicAffine Q Λ θ β r.1 : T) • z) hn))
  | add x y hx hy =>
    have h : twoPieceStandardMk Q Λ ht u hQ (x + y) =
        twoPieceStandardMk Q Λ ht u hQ x + twoPieceStandardMk Q Λ ht u hQ y :=
      map_add (Submodule.mkQ _) x y
    exact (congrArg (fun w : V => twoPieceStandardFrom Q Λ ht u hQ
      (twoPieceStandardTo Q Λ ht u hQ w)) h).trans <|
      (congrArg (twoPieceStandardFrom Q Λ ht u hQ)
        (LinearMap.map_add (twoPieceStandardTo Q Λ ht u hQ) _ _)).trans <|
      (LinearMap.map_add (twoPieceStandardFrom Q Λ ht u hQ) _ _).trans <|
      (congrArg₂ (· + ·) hx hy).trans h.symm

/-- **Webster, arXiv:1309.3796v2, step in the proof of Proposition 5.20.** For a red-ordered
loading `t` of the first `ℓ` red strands and a black sequence `u`, the standardization of
`S_t ⊠ R^{λ_{ℓ+1}} e(u)` is the standard module `S_{t λ_{ℓ+1} u}` of the two-piece loading. -/
def twoPieceStandardEquiv : V ≃ₗ[T] Z :=
  { twoPieceStandardTo Q Λ ht u hQ with
    invFun := twoPieceStandardFrom Q Λ ht u hQ
    left_inv := twoPieceStandardFrom_to Q Λ ht u hQ
    right_inv := twoPieceStandardTo_from Q Λ ht u hQ }

theorem twoPieceStandardEquiv_symm_unit :
    (twoPieceStandardEquiv Q Λ ht u hQ).symm z₀ = v₀ :=
  twoPieceStandardFrom_unit Q Λ ht u hQ

end Categorification.Stendhal