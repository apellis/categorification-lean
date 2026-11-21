/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongAssoc
import Categorification.Algebra.InductionAlongCornerSelf
import Categorification.WeightedKLR.RedStrands.Prop55CountCorner
import Categorification.WeightedKLR.RedStrands.Prop55CountRed
import Categorification.WeightedKLR.RedStrands.ParabolicStandardEmptyRed

/-!
# The last-red piece of the dimension count of Proposition 5.5 when `β = ∅`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. When the last block `β` is empty, the summands of `Fᵢ S(N)` and
`S(₁Fᵢ N)` cut out by `e_ℓ` (last strand red) are both isomorphic to `Fᵢ` of `N` viewed as a
`T^{λ'}`-module (Proposition 4.18 and Proposition 4.32), so they have the same dimension.

## Main results

* `lastRedFirstIndFEquiv`: `e_ℓ Fᵢ S(N) ≅ Ind_{appendBlack} N`.
* `firstIndLeftEmptyEquiv`, `lastRedFirstIndStandardTEquiv`: `e_ℓ S(₁Fᵢ N) ≅ ₁Fᵢ N ≅
  Ind_{appendBlack} N`.
* `finrank_lastRed_firstIndF_eq`: the two pieces have the same dimension.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-! ### Generic transport of idempotent pieces -/

section FixSub

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
  {M : Type*} [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
  {M' : Type*} [AddCommGroup M'] [Module K M'] [Module A M'] [IsScalarTower K A M']

/-- An `A`-linear isomorphism restricts to `a M ≅ a M'`. -/
def fixSubLinearCongr (f : M ≃ₗ[A] M') (a : A) : fixSub K M a ≃ₗ[K] fixSub K M' a where
  toFun v := ⟨f v, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 v.2]⟩
  invFun w := ⟨f.symm w, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 w.2]⟩
  map_add' v w := Subtype.ext (map_add f _ _)
  map_smul' c v := Subtype.ext (f.toLinearMap.map_smul_of_tower c v)
  left_inv v := Subtype.ext (f.symm_apply_apply _)
  right_inv w := Subtype.ext (f.apply_symm_apply _)

omit [Algebra K A] [IsScalarTower K A M] in
/-- Equal elements cut out the same piece. -/
def fixSubEqEquiv {a b : A} (h : a = b) : fixSub K M a ≃ₗ[K] fixSub K M b :=
  LinearEquiv.ofEq _ _ (by rw [h])

end FixSub

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [Field k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + 0))

/-! ### Scalar towers -/

section Tower

variable (β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (hQ : KLRSymm Q)

instance : IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ β N hQ) c t) y⟩

end Tower

section TowerFirst

variable (β : Multiset I) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  (hQ : KLRSymm Q)

instance : IsScalarTower k (TensorProductAlgebra k Q Λ ((Si i) + (θ + β)))
    (FirstIndStandardT Q Λ i θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul ((parabolicStandardAction Q Λ ((Si i) + θ) β
    (FirstIndLeft Q Λ i θ β N) hQ).comp
      (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)).toAlgHom) c t) y⟩

end TowerFirst

/-! ### `Fᵢ S(N)` -/

section FirstIndF

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ 0) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] (hQ : KLRSymm Q)

local notation "N₁" => EmptyRedInput Q Λ θ N

/-- `Fᵢ S(N) ≅ Ind_{appendBlack ∘ appendRed} N` for `β = ∅`, as `T′`-modules. -/
def firstIndFEmptyEquiv :
    FirstIndF Q Λ i θ 0 N hQ ≃ₗ[T′] IndK k N₁ (redBlackHom Q Λ i (θ + 0)) :=
  (Ind.mapEquiv (φ := appendBlackHom Q Λ i θ 0) (emptyRedStandardEquiv Q Λ θ N hQ)).trans
    (compEquiv N₁ (emptyRedHom Q Λ θ) (appendBlackHom Q Λ i θ 0))

/-- **`e_ℓ Fᵢ S(N) ≅ Ind_{appendBlack} N`** for `β = ∅` (Webster, arXiv:1309.3796v3,
Propositions 4.18 and 4.32). -/
def lastRedFirstIndFEquiv (hR : IsRouquierQ C Q) :
    fixSub k (FirstIndF Q Λ i θ 0 N hQ) (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0)))
      ≃ₗ[k] IndK k N₁ (appendBlackOldHom Q Λ i (θ + 0)) :=
  (fixSubLinearCongr (firstIndFEmptyEquiv Q Λ i θ N hQ) _).trans
    (lastRedPieceIndEquiv Q Λ i (θ + 0) hR N₁)

end FirstIndF

/-! ### `S(₁Fᵢ N)` -/

section FirstIndStandard

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ 0) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] (hQ : KLRSymm Q)

local notation "Fl" => FirstIndLeft Q Λ i θ 0 N
local notation "θᵢ" => ((Si i) + θ)
local notation "N₂" => EmptyRedInput Q Λ θᵢ Fl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem smul_firstIndStandardT_eq (t : T′) (y : FirstIndStandardT Q Λ i θ 0 N hQ) :
    (t • y : FirstIndStandardT Q Λ i θ 0 N hQ) =
      (show FirstIndStandardT Q Λ i θ 0 N hQ from
        parabolicStandardAction Q Λ θᵢ 0 Fl hQ
          (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ 0) t) y) :=
  rfl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem smul_parabolicStandardT_eq (t : TensorProductAlgebra k Q Λ (θᵢ + 0))
    (y : ParabolicStandardT Q Λ θᵢ 0 Fl hQ) :
    (t • y : ParabolicStandardT Q Λ θᵢ 0 Fl hQ) =
      (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from
        parabolicStandardAction Q Λ θᵢ 0 Fl hQ t y) :=
  rfl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem mem_fixSub_firstIndStandardT_iff (y : ParabolicStandard Q Λ θᵢ 0 Fl) :
    (show FirstIndStandardT Q Λ i θ 0 N hQ from y) ∈
        fixSub k (FirstIndStandardT Q Λ i θ 0 N hQ)
          (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0))) ↔
      (show ParabolicStandardT Q Λ θᵢ 0 Fl hQ from y) ∈
        fixSub k (ParabolicStandardT Q Λ θᵢ 0 Fl hQ)
          (TensorProductAlgebra.lastRedIdem Q Λ (θᵢ + 0)) := by
  rw [mem_fixSub, mem_fixSub, smul_firstIndStandardT_eq]
  have he := castTensorProductAlgebra_lastRedIdem (Q := Q) (Λ := Λ) (firstInd_blackWeight i θ 0)
  rw [he]
  rfl

/-- `e_ℓ S(₁Fᵢ N)` over `T(i + (θ + 0))` is `e_ℓ S(₁Fᵢ N)` over `T((i + θ) + 0)`. -/
def firstIndStandardTFixSubEquiv :
    fixSub k (FirstIndStandardT Q Λ i θ 0 N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0))) ≃ₗ[k]
      fixSub k (ParabolicStandardT Q Λ θᵢ 0 Fl hQ) (TensorProductAlgebra.lastRedIdem Q Λ (θᵢ + 0))
    where
  toFun y := ⟨_, (mem_fixSub_firstIndStandardT_iff Q Λ i θ N hQ y.1).1 y.2⟩
  invFun y := ⟨_, (mem_fixSub_firstIndStandardT_iff Q Λ i θ N hQ y.1).2 y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem emptyRedHom_one' (θ' : Multiset I) :
    emptyRedHom Q Λ θ' 1 = TensorProductAlgebra.lastRedIdem Q Λ (θ' + 0) :=
  appendRed_one_val Q Λ (θ' + 0)

theorem emptyRedHom_algebraMap (θ' : Multiset I) (c : k) :
    emptyRedHom Q Λ θ' (algebraMap k _ c) = algebraMap k _ c * emptyRedHom Q Λ θ' 1 := by
  rw [emptyRedHom_apply, AlgHom.commutes, Corner.val_algebraMap, emptyRedHom_one']

theorem emptyRedHom_corner (θ' : Multiset I) (z : TensorProductAlgebra k Q Λ (θ' + 0)) :
    ∃ a, emptyRedHom Q Λ θ' a = emptyRedHom Q Λ θ' 1 * z * emptyRedHom Q Λ θ' 1 := by
  have he := TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ (θ' + 0)
  set E := TensorProductAlgebra.lastRedIdem Q Λ (θ' + 0)
  obtain ⟨a, ha⟩ := appendRed_surjective Q Λ (θ' + 0)
    (Corner.mk (idem := he) (E * z * E) (by
      rw [← mul_assoc, ← mul_assoc, he.eq, mul_assoc, mul_assoc, mul_assoc, he.eq,
        ← mul_assoc]))
  refine ⟨a, ?_⟩
  rw [emptyRedHom_one', emptyRedHom_apply, ha]
  rfl

theorem emptyRedHom_injective (hR : IsRouquierQ C Q) (θ' : Multiset I) :
    Function.Injective (emptyRedHom Q Λ θ') := fun _ _ h =>
  (appendRedEquiv Q Λ (θ' + 0) hR).injective (Corner.val_injective h)

/-- **`e_ℓ S(₁Fᵢ N) ≅ ₁Fᵢ N`** for `β = ∅` (Webster, arXiv:1309.3796v3, Proposition 4.18). -/
def lastRedFirstIndStandardTLeftEquiv (hR : IsRouquierQ C Q) :
    fixSub k (FirstIndStandardT Q Λ i θ 0 N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0))) ≃ₗ[k] Fl :=
  (firstIndStandardTFixSubEquiv Q Λ i θ N hQ).trans <|
    (fixSubLinearCongr (emptyRedStandardEquiv Q Λ θᵢ Fl hQ) _).trans <|
      (fixSubEqEquiv (emptyRedHom_one' Q Λ θᵢ).symm).trans <|
        (fixSubIndSelfEquiv (emptyRedHom Q Λ θᵢ) (emptyRedHom_injective Q Λ hR θᵢ)
          (emptyRedHom_corner Q Λ θᵢ) k (emptyRedHom_algebraMap Q Λ θᵢ) N₂).trans
          (LinearEquiv.refl k Fl)

/-- `D(i + θ, ∅) ≅ T^{λ'}(i + (θ + 0))`. -/
def emptyFactorToOldFirst :
    parabolicFactorAlgebra Q Λ θᵢ 0 ≃ₐ[k] TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ((Si i) + (θ + 0)) :=
  (emptyFactorToOld Q Λ θᵢ).trans
    (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (firstInd_blackWeight i θ 0).symm)

theorem emptyFactorToOld_tmul (θ' : Multiset I)
    (a : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ')
    (c : CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) 0) :
    emptyFactorToOld Q Λ θ' (a ⊗ₜ c) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (add_zero θ').symm
        (cyclotomicZeroEquiv Q _ c • a) :=
  rfl

/-- `appendBlack` intertwines the identifications of the factor algebras with `T^{λ'}`. -/
theorem appendBlackOld_emptyFactorToOld (t : parabolicFactorAlgebra Q Λ θ 0) :
    appendBlackOldHom Q Λ i (θ + 0) (emptyFactorToOld Q Λ θ t) =
      emptyFactorToOldFirst Q Λ i θ (leftAppendHom Q Λ i θ 0 t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    change appendBlack Q (Λ ∘ Fin.castSucc) i (θ + 0) (emptyFactorToOld Q Λ θ (a ⊗ₜ c)) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (firstInd_blackWeight i θ 0).symm
        (emptyFactorToOld Q Λ θᵢ (appendBlack Q (Λ ∘ Fin.castSucc) i θ a ⊗ₜ c))
    have key : ∀ {μ μ' ν : Multiset I} (h : μ = μ') (h₁ : (Si i) + μ = ν)
        (h₂ : ν = (Si i) + μ') (x : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) μ),
        appendBlack Q (Λ ∘ Fin.castSucc) i μ' (castTensorProductAlgebra Q _ h x) =
          castTensorProductAlgebra Q _ h₂ (castTensorProductAlgebra Q _ h₁
            (appendBlack Q (Λ ∘ Fin.castSucc) i μ x)) := by
      intro μ μ' ν h h₁ h₂ x
      subst h h₁
      rfl
    rw [emptyFactorToOld_tmul, emptyFactorToOld_tmul, map_smul, map_smul, map_smul, map_smul,
      key]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The additive isomorphism underlying `firstIndLeftEmptyEquiv`. -/
def firstIndLeftEmptyAdd :
    Ind N (leftAppendHom Q Λ i θ 0) ≃+
      Ind (EmptyRedInput Q Λ θ N) (appendBlackOldHom Q Λ i (θ + 0)) :=
  Ind.transport (emptyFactorToOld Q Λ θ).toRingEquiv
    (emptyFactorToOldFirst Q Λ i θ).toRingEquiv
    (fun t => appendBlackOld_emptyFactorToOld Q Λ i θ t)
    (AddEquiv.refl N : N ≃+ EmptyRedInput Q Λ θ N)
    (fun t n => by
      change t • n = (emptyFactorToOld Q Λ θ).symm (emptyFactorToOld Q Λ θ t) • n
      rw [AlgEquiv.symm_apply_apply])

/-- **`₁Fᵢ N ≅ Ind_{appendBlack} N`** for `β = ∅`: `D(i + θ, ∅) ⊗_{D(θ, ∅)} N` is the
induction of `N` along `appendBlack : T^{λ'}(θ) → T^{λ'}(i + θ)`. -/
def firstIndLeftEmptyEquiv :
    Fl ≃ₗ[k] IndK k (EmptyRedInput Q Λ θ N) (appendBlackOldHom Q Λ i (θ + 0)) :=
  { firstIndLeftEmptyAdd Q Λ i θ N with
    map_smul' := fun c x => by
      change firstIndLeftEmptyAdd Q Λ i θ N
          (algebraMap k (parabolicFactorAlgebra Q Λ θᵢ 0) c • (x : Ind N (leftAppendHom Q Λ i θ 0))) =
        algebraMap k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ((Si i) + (θ + 0))) c •
          firstIndLeftEmptyAdd Q Λ i θ N x
      rw [firstIndLeftEmptyAdd, Ind.transport_smul]
      exact congrArg (· • _) ((emptyFactorToOldFirst Q Λ i θ).commutes c) }

/-- **`e_ℓ S(₁Fᵢ N) ≅ Ind_{appendBlack} N`** for `β = ∅`. -/
def lastRedFirstIndStandardTEquiv (hR : IsRouquierQ C Q) :
    fixSub k (FirstIndStandardT Q Λ i θ 0 N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0))) ≃ₗ[k]
      IndK k (EmptyRedInput Q Λ θ N) (appendBlackOldHom Q Λ i (θ + 0)) :=
  (lastRedFirstIndStandardTLeftEquiv Q Λ i θ N hQ hR).trans (firstIndLeftEmptyEquiv Q Λ i θ N)

/-- **The last-red pieces of `Fᵢ S(N)` and `S(₁Fᵢ N)` have the same dimension** when `β = ∅`
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem finrank_lastRed_firstIndF_eq (hR : IsRouquierQ C Q) :
    Module.finrank k (fixSub k (FirstIndF Q Λ i θ 0 N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0)))) =
      Module.finrank k (fixSub k (FirstIndStandardT Q Λ i θ 0 N hQ)
        (TensorProductAlgebra.lastRedIdem Q Λ ((Si i) + (θ + 0)))) :=
  ((lastRedFirstIndFEquiv Q Λ i θ N hQ hR).trans
    (lastRedFirstIndStandardTEquiv Q Λ i θ N hQ hR).symm).finrank_eq

end FirstIndStandard

end Categorification.Stendhal
