/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55CountRedEmpty
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndShortExact
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# Pulling the last red strand across a black strand: the standard-module form

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 5.23
(one red and one black strand). Let `N = T^{λ'} e(s)`. The generator `1 ⊗ (1 ⊗ n)` of
`S(₁Fᵢ N)` is sent by `δ₁` to `G [1 ⊗ (1 ⊗ n)]` in `Fᵢ S(N)`, where `G` is the diagram moving
the new black strand `i` across the last block (`firstIndDelta_unitGen`). The module `S(₁Fᵢ N)`
maps onto the left ideal `T e(s, i, λ_ℓ)` (`redCrossProj`), sending this generator to the
idempotent `e(s, i, λ_ℓ)`. Hence injectivity of `δ₁` gives: an element `x` of
`T e(s, i, λ_ℓ)` with `x G = 0` vanishes (`redCross_eq_zero`).

## Main results

* `firstIndDelta_unitGen`: `δ₁ [1 ⊗ (1 ⊗ n)] = G [1 ⊗ (1 ⊗ n)]`.
* `eq_zero_of_smul_firstIndGen`: the abstract injectivity statement.
* `redCrossProj`, `redCrossProj_unitGen`: `S(₁Fᵢ T^{λ'} e(s)) → T`, generator `↦ e(s, i, λ_ℓ)`.
* `redCross_eq_zero`: the injectivity statement for `N = T^{λ'} e(s)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "S" => stendhalQ Q Λ

section General

variable (β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))
local notation "Aₚ₁" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ ((Si i) + θ))
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "affT" => firstIndAffine Q Λ i θ β

/-- The generator `1 ⊗ (1 ⊗ n)` of `S(₁Fᵢ N)`. -/
def firstIndStdGen (n : N) : FirstIndStandardT Q Λ i θ β N hQ :=
  firstIndMk Q Λ i θ β N hQ (BalancedTensor.tmul (oneBimod S Aₚ₁ Aₗ)
    (show ParabolicInput Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) from
      Ind.tmul (unitGen (leftAppendHom Q Λ i θ β)) n))

/-- **`δ₁` on generators**: `δ₁ [1 ⊗ (1 ⊗ n)] = G [1 ⊗ (1 ⊗ n)]` (Webster,
arXiv:1309.3796v2, proof of Proposition 5.5). -/
theorem firstIndDelta_unitGen (n : N) :
    firstIndDelta Q Λ i θ β N hQ (firstIndStdGen Q Λ i θ β N hQ n) =
      firstIndGen Q Λ i θ β N hQ n := by
  rw [firstIndStdGen, firstIndDelta_mk, firstIndShuffle_tmul]
  change firstIndKLRAction Q Λ i θ β N hQ (oneConcat S Aₚ₁ Aₗ) (firstIndLeftMap Q Λ i θ β N hQ
    (Ind.tmul (unitGen (leftAppendHom Q Λ i θ β)) n)) = _
  rw [← concat_one, firstIndKLRAction_concat, map_one, ← firstIndLeftMap_smul, one_smul,
    firstIndLeftMap_tmul]
  have h := firstIndLayerAction_appendLeft Q Λ i θ β N hQ 1 n
  rw [map_one, one_smul] at h
  exact h

/-- **Injectivity of `δ₁` on a cyclic piece**: if a `T′`-linear map out of `S(₁Fᵢ N)` sends the
generator of `n` to `E`, then `x E = x` and `x G [1 ⊗ (1 ⊗ n)] = 0` force `x = 0`. -/
theorem eq_zero_of_smul_firstIndGen (hinj : FirstIndDeltaInjective Q Λ i θ β N hQ)
    (α : FirstIndStandardT Q Λ i θ β N hQ →ₗ[T′] T′) (n : N) (E : T′)
    (hα : α (firstIndStdGen Q Λ i θ β N hQ n) = E) (x : T′) (hx : x * E = x)
    (h0 : x • firstIndGen Q Λ i θ β N hQ n = 0) : x = 0 := by
  have h1 : x • firstIndStdGen Q Λ i θ β N hQ n = 0 := by
    apply hinj
    rw [map_smul, map_zero]
    change x • firstIndDelta Q Λ i θ β N hQ (firstIndStdGen Q Λ i θ β N hQ n) = 0
    rw [firstIndDelta_unitGen, h0]
  have h2 := congrArg α h1
  rw [map_smul, hα, map_zero, smul_eq_mul, hx] at h2
  exact h2

/-- The form used below: `x E = x` and `x G = 0` force `x = 0`. -/
theorem eq_zero_of_mul_firstG (hinj : FirstIndDeltaInjective Q Λ i θ β N hQ)
    (α : FirstIndStandardT Q Λ i θ β N hQ →ₗ[T′] T′) (n : N) (E : T′)
    (hα : α (firstIndStdGen Q Λ i θ β N hQ n) = E) (x : T′) (hx : x * E = x)
    (h0 : x * affT (firstG S Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1))) = 0) : x = 0 :=
  eq_zero_of_smul_firstIndGen Q Λ i θ β N hQ hinj α n E hα x hx (by
    rw [firstIndGen, ← mul_smul, h0, zero_smul])

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- The `T′`-action on `S(₁Fᵢ N)` is the action on standardization through the cast. -/
theorem firstIndStandard_smul_eq (t : T′) (m : FirstIndStandardT Q Λ i θ β N hQ) :
    (show ParabolicStandardT Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ from t • m) =
      castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β) t •
        (show ParabolicStandardT Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ from m) :=
  rfl

end General

section Red

variable (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) (hQ : KLRSymm Q)

local notation "θᵢ" => (Si i) + θ
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + 0))
local notation "Tᵢ" => TensorProductAlgebra k Q Λ (((Si i) + θ) + 0)
local notation "N" => FactorModule.carrier (redFactorModule Q Λ θ s hs)
local notation "Fl" => FirstIndLeft Q Λ i θ 0 N
local notation "cst₁" => castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ 0)

/-- Adding the last red strand to the factor algebra of `(i + θ, ∅)`. -/
def redFactorHom (d : parabolicFactorAlgebra Q Λ θᵢ 0) : Tᵢ :=
  emptyRedHom Q Λ θᵢ (emptyFactorToOld Q Λ θᵢ d)

theorem redFactorHom_mul (d d' : parabolicFactorAlgebra Q Λ θᵢ 0) :
    redFactorHom Q Λ i θ (d * d') = redFactorHom Q Λ i θ d * redFactorHom Q Λ i θ d' := by
  simp only [redFactorHom, map_mul]

theorem redFactorHom_add (d d' : parabolicFactorAlgebra Q Λ θᵢ 0) :
    redFactorHom Q Λ i θ (d + d') = redFactorHom Q Λ i θ d + redFactorHom Q Λ i θ d' := by
  simp only [redFactorHom, map_add]

/-- The image of `n ∈ T^{λ'} e(s)` in `T^λ`: add a black strand `i`, then the last red strand. -/
def redCrossVec (n : N) : Tᵢ :=
  redFactorHom Q Λ i θ (leftAppendHom Q Λ i θ 0 ((emptyFactorToOld Q Λ θ).symm
    (show lIdeal (oldIdem Q Λ θ s hs) from n).1))

theorem redCrossVec_add (n n' : N) :
    redCrossVec Q Λ i θ s hs (n + n') =
      redCrossVec Q Λ i θ s hs n + redCrossVec Q Λ i θ s hs n' := by
  simp only [redCrossVec]
  rw [show (show lIdeal (oldIdem Q Λ θ s hs) from n + n').1 =
    (show lIdeal (oldIdem Q Λ θ s hs) from n).1 + (show lIdeal (oldIdem Q Λ θ s hs) from n').1
    from rfl, map_add, map_add, redFactorHom_add]

theorem redCrossVec_smul (a : parabolicFactorAlgebra Q Λ θ 0) (n : N) :
    redCrossVec Q Λ i θ s hs (a • n) =
      redFactorHom Q Λ i θ (leftAppendHom Q Λ i θ 0 a) * redCrossVec Q Λ i θ s hs n := by
  simp only [redCrossVec]
  rw [show (show lIdeal (oldIdem Q Λ θ s hs) from a • n).1 =
    emptyFactorToOld Q Λ θ a * (show lIdeal (oldIdem Q Λ θ s hs) from n).1 from rfl,
    map_mul, AlgEquiv.symm_apply_apply, map_mul, redFactorHom_mul]

/-- `₁Fᵢ N → T^λ`, `z ⊗ n ↦ z · n` with both strands added. -/
def redCrossLeft : Ind N (leftAppendHom Q Λ i θ 0) →+ Tᵢ :=
  Ind.liftAdd (φ := leftAppendHom Q Λ i θ 0)
    (fun z n => redFactorHom Q Λ i θ z.1 * redCrossVec Q Λ i θ s hs n)
    (fun z z' n => by
      change redFactorHom Q Λ i θ (z.1 + z'.1) * _ = _
      rw [redFactorHom_add, add_mul])
    (fun z n n' => by rw [redCrossVec_add, mul_add])
    (fun z a n => by
      change redFactorHom Q Λ i θ (z.1 * leftAppendHom Q Λ i θ 0 a) * _ = _
      rw [redCrossVec_smul, redFactorHom_mul, mul_assoc])

theorem redCrossLeft_tmul (z : Corner (leftAppendHom Q Λ i θ 0)) (n : N) :
    redCrossLeft Q Λ i θ s hs (Ind.tmul z n) =
      redFactorHom Q Λ i θ z.1 * redCrossVec Q Λ i θ s hs n := rfl

theorem redCrossLeft_smul (d : parabolicFactorAlgebra Q Λ θᵢ 0)
    (y : Ind N (leftAppendHom Q Λ i θ 0)) :
    redCrossLeft Q Λ i θ s hs (d • y) =
      redFactorHom Q Λ i θ d * redCrossLeft Q Λ i θ s hs y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul z n =>
    rw [Ind.smul_tmul, redCrossLeft_tmul, redCrossLeft_tmul]
    change redFactorHom Q Λ i θ (d * z.1) * _ = _
    rw [redFactorHom_mul, mul_assoc]
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', mul_add]

/-- `Ind_{T^{λ'}}^{T^λ} ₁Fᵢ N → T^λ`, `z ⊗ m ↦ z · m`. -/
def redCrossInd : EmptyRedInd Q Λ θᵢ Fl →+ Tᵢ :=
  Ind.liftAdd (φ := emptyRedHom Q Λ θᵢ)
    (fun z m => z.1 * redCrossLeft Q Λ i θ s hs (show Fl from m))
    (fun z z' m => add_mul _ _ _)
    (fun z m m' => by
      change _ * redCrossLeft Q Λ i θ s hs ((show Fl from m) + (show Fl from m')) = _
      rw [map_add, mul_add])
    (fun z a m => by
      change (z.1 * emptyRedHom Q Λ θᵢ a) * _ =
        z.1 * redCrossLeft Q Λ i θ s hs ((emptyFactorToOld Q Λ θᵢ).symm a • (show Fl from m))
      rw [redCrossLeft_smul, redFactorHom, AlgEquiv.apply_symm_apply, mul_assoc])

theorem redCrossInd_tmul (z : Corner (emptyRedHom Q Λ θᵢ)) (m : EmptyRedInput Q Λ θᵢ Fl) :
    redCrossInd Q Λ i θ s hs (Ind.tmul z m) = z.1 * redCrossLeft Q Λ i θ s hs (show Fl from m) :=
  rfl

theorem redCrossInd_smul (t : Tᵢ) (y : EmptyRedInd Q Λ θᵢ Fl) :
    redCrossInd Q Λ i θ s hs (t • y) = t * redCrossInd Q Λ i θ s hs y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul z m =>
    rw [Ind.smul_tmul, redCrossInd_tmul, redCrossInd_tmul]
    change (t * z.1) * _ = _
    rw [mul_assoc]
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', mul_add]

/-- **`S(₁Fᵢ T^{λ'} e(s)) → T^λ`**, the projection onto the left ideal of `e(s, i, λ_ℓ)`. -/
def redCrossProj : FirstIndStandardT Q Λ i θ 0 N hQ →ₗ[T′] T′ where
  toFun m := (cst₁).symm (redCrossInd Q Λ i θ s hs
    (emptyRedStandard Q Λ θᵢ Fl hQ (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from m)))
  map_add' m m' := by
    rw [show (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from m + m') =
      (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from m) +
        (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from m') from rfl, map_add, map_add, map_add]
  map_smul' t m := by
    rw [RingHom.id_apply, smul_eq_mul, firstIndStandard_smul_eq, emptyRedStandard_smul,
      redCrossInd_smul, map_mul, AlgEquiv.symm_apply_apply]

/-- The idempotent `e(s, i, λ_ℓ)`: `e(s)` with the black strand `i` and the last red strand
added. -/
def redCrossIdem : T′ :=
  (cst₁).symm (redFactorHom Q Λ i θ (leftAppendHom Q Λ i θ 0
    ((emptyFactorToOld Q Λ θ).symm (oldIdem Q Λ θ s hs))))

/-- The unit vector `e(s)` of `T^{λ'} e(s)`. -/
def redUnit : N :=
  (⟨oldIdem Q Λ θ s hs, mem_lIdeal.2 (isIdempotentElem_mk_e s hs).eq⟩ :
    lIdeal (oldIdem Q Λ θ s hs))

theorem redCrossProj_unitGen :
    redCrossProj Q Λ i θ s hs hQ (firstIndStdGen Q Λ i θ 0 N hQ (redUnit Q Λ θ s hs)) =
      redCrossIdem Q Λ i θ s hs := by
  change (cst₁).symm (redCrossInd Q Λ i θ s hs (emptyRedStandard Q Λ θᵢ Fl hQ
    (emptyStdMk Q Λ θᵢ Fl hQ (BalancedTensor.tmul _ _)))) = _
  rw [emptyRedStandard_mk_one, emptyRedGen_apply, redCrossInd_tmul]
  change (cst₁).symm (emptyRedHom Q Λ θᵢ 1 * (redFactorHom Q Λ i θ (leftAppendHom Q Λ i θ 0 1) *
    redCrossVec Q Λ i θ s hs (redUnit Q Λ θ s hs))) = _
  rw [redCrossIdem, redCrossVec, ← redFactorHom_mul, ← map_mul, one_mul]
  congr 1
  change emptyRedHom Q Λ θᵢ 1 * emptyRedHom Q Λ θᵢ _ = _
  rw [← map_mul, one_mul]
  rfl

/-- **Pulling the last red strand left across a black strand is injective** (Webster,
arXiv:1309.3796v2, Lemma 5.23, one black strand; `G` as in `firstIndGen`): given injectivity
of `δ₁` (`FirstIndDeltaInjective`, the route hypothesis of Proposition 5.5), an element `x`
of `T e(s, i, λ_ℓ)` with `x G = 0` vanishes. -/
theorem redCross_eq_zero (hinj : FirstIndDeltaInjective Q Λ i θ 0 N hQ) (x : T′)
    (hx : x * redCrossIdem Q Λ i θ s hs = x)
    (h0 : x * firstIndAffine Q Λ i θ 0 (firstG S (Multiset.map (addRedColor ℓ)
      (stendhalWeight ℓ θ)) (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
        (stendhalWeight 1 0)) (Sum.inl i : I ⊕ Fin (ℓ + 1))) = 0) : x = 0 :=
  eq_zero_of_mul_firstG Q Λ i θ 0 N hQ hinj (redCrossProj Q Λ i θ s hs hQ)
    (redUnit Q Λ θ s hs) _ (redCrossProj_unitGen Q Λ i θ s hs hQ) x hx h0

end Red

end Categorification.Stendhal
