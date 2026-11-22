/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingStandard
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

set_option backward.isDefEq.respectTransparency false

/-!
# Transporting injectivity of right multiplication along inductions

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 5.23,
the reduction to one red-black crossing at the end of a loading. Under the isomorphism
`Ind_φ (A f) ≅ B φ(f)` (`indLIdealEquiv`), right multiplication by `φ(c)` on `B φ(f)` is the
induction of right multiplication by `c` on `A f` (`indLIdealEquiv_map_rmulLIdeal`). Hence if
induction along `φ` preserves the injectivity of `y ↦ y c`, then so does `x ↦ x φ(c)`
(`eq_zero_of_mul_map`). Two cases are used.

* `φ = appendBlack` (adding a black strand on the right): its corner is projective, so every
  injection is preserved (`appendBlack_ind_map_injective`).
* `φ = emptyRedHom` (adding the last red strand): induction is standardization with an empty
  last block (`emptyRedStandard`), which is natural in the module
  (`emptyRedStandard_map`) and preserves injections (`parabolicStandardMap_injective`); hence
  `emptyRed_ind_map_injective`.

## Main results

* `InductionAlong.eq_zero_of_mul_map`: the transport of `x e = x, x c = 0 ⇒ x = 0` along `φ`.
* `emptyRedStandard_map`: naturality of `S(N) ≅ Ind N` for an empty last block.
* `emptyRed_lIdeal_ind_map_injective`: induction along `emptyRedHom` preserves the injectivity
  of right multiplication on a left ideal.
-/

noncomputable section

namespace Categorification.InductionAlong

universe u

variable {A : Type u} [Ring A] {B : Type u} [Ring B] (φ : A →ₙ+* B)

/-- Right multiplication by `c`, from the left ideal `A f` to `A`. -/
def rmulLIdeal (f c : A) : lIdeal f →ₗ[A] lIdeal (1 : A) where
  toFun y := ⟨y.1 * c, by rw [mem_lIdeal, mul_one]⟩
  map_add' y y' := Subtype.ext (add_mul _ _ _)
  map_smul' a y := Subtype.ext (by
    change a * y.1 * c = a * (y.1 * c)
    rw [mul_assoc])

theorem rmulLIdeal_apply (f c : A) (y : lIdeal f) : (rmulLIdeal f c y).1 = y.1 * c := rfl

/-- `y ↦ y c` is injective on `A f` when `y f = y` and `y c = 0` force `y = 0`. -/
theorem rmulLIdeal_injective {f c : A} (h : ∀ y : A, y * f = y → y * c = 0 → y = 0) :
    Function.Injective (rmulLIdeal f c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  exact Subtype.ext (h y.1 y.2 (congrArg Subtype.val hy))

/-- **Induction of right multiplication**: under `Ind_φ (A f) ≅ B φ(f)`, the induction of
`y ↦ y c` is `x ↦ x φ(c)`. -/
theorem indLIdealEquiv_map_rmulLIdeal {f : A} (hf : IsIdempotentElem f) (c : A)
    (x : Ind (lIdeal f) φ) :
    (indLIdealEquiv φ IsIdempotentElem.one (Ind.map (rmulLIdeal f c) x)).1 =
      (indLIdealEquiv φ hf x).1 * φ c := by
  induction x using Ind.induction_on with
  | zero => simp
  | tmul z a =>
    rw [Ind.map_tmul, indLIdealEquiv_tmul, indLIdealEquiv_tmul, rmulLIdeal_apply, map_mul,
      mul_assoc]
  | add x y hx hy =>
    rw [map_add, map_add, Submodule.coe_add, hx, hy, map_add, Submodule.coe_add, add_mul]

/-- **Transport along `φ`**: if induction along `φ` keeps `y ↦ y c` injective on `A f`, then
`x φ(f) = x` and `x φ(c) = 0` force `x = 0`. -/
theorem eq_zero_of_mul_map {f : A} (hf : IsIdempotentElem f) (c : A)
    (hinj : Function.Injective (Ind.map (φ := φ) (rmulLIdeal f c))) (x : B)
    (hx : x * φ f = x) (h0 : x * φ c = 0) : x = 0 := by
  have hy : Ind.map (φ := φ) (rmulLIdeal f c) ((indLIdealEquiv φ hf).symm ⟨x, hx⟩) = 0 := by
    apply (indLIdealEquiv φ IsIdempotentElem.one).injective
    apply Subtype.ext
    rw [indLIdealEquiv_map_rmulLIdeal φ hf, LinearEquiv.apply_symm_apply, map_zero]
    exact h0
  have h := hinj (hy.trans (map_zero _).symm)
  have h' := congrArg (fun y => ((indLIdealEquiv φ hf) y).1) h
  simpa using h'

end Categorification.InductionAlong

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ : Multiset I)

local notation "old" => Λ ∘ Fin.castSucc
local notation "L₀" => TensorProductAlgebra k Q (old) (θ + 0)

section Natural

universe v

variable {N N' : Type v} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ 0) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ θ 0) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N']

/-- A map of modules over the factor algebra at `β = ∅`, as a map of `T^{λ'}`-modules. -/
def emptyInputMap (g : N →ₗ[parabolicFactorAlgebra Q Λ θ 0] N') :
    EmptyRedInput Q Λ θ N →ₗ[L₀] EmptyRedInput Q Λ θ N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' t n := g.map_smul ((emptyFactorToOld Q Λ θ).symm t) n

variable (hQ : KLRSymm Q)

/-- **Naturality of `S(N) → Ind N`** for an empty last block. -/
theorem emptyRedStandard_map (g : N →ₗ[parabolicFactorAlgebra Q Λ θ 0] N')
    (m : ParabolicStandardT Q Λ θ 0 N hQ) :
    emptyRedStandard Q Λ θ N' hQ (parabolicStandardMap Q Λ θ 0 g m) =
      Ind.map (emptyInputMap Q Λ θ g) (emptyRedStandard Q Λ θ N hQ m) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  change emptyStdShuffle Q Λ θ N' (parabolicShuffleMap Q Λ θ 0 g x) =
    Ind.map (emptyInputMap Q Λ θ g) (emptyStdShuffle Q Λ θ N x)
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r y =>
    rw [parabolicShuffleMap, BalancedTensor.mapRight_tmul, emptyStdShuffle_tmul,
      emptyStdShuffle_tmul]
    exact ((Ind.map (φ := emptyRedHom Q Λ θ) (emptyInputMap Q Λ θ g)).map_smul
      (emptyAffine Q Λ θ r.1) (emptyRedGen Q Λ θ N y)).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

include hQ in
/-- **Induction along adding the last red strand preserves injections** between modules over
the factor algebra at `β = ∅`. -/
theorem emptyRed_ind_map_injective (g : N →ₗ[parabolicFactorAlgebra Q Λ θ 0] N')
    (hg : Function.Injective g) :
    Function.Injective (Ind.map (φ := emptyRedHom Q Λ θ) (emptyInputMap Q Λ θ g)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨m, rfl⟩ := emptyRedStandard_surjective Q Λ θ N hQ y
  have h : parabolicStandardMap Q Λ θ 0 g m = 0 := by
    apply emptyRedStandard_injective Q Λ θ N' hQ
    rw [emptyRedStandard_map, map_zero]
    exact hy
  rw [(injective_iff_map_eq_zero _).1 (parabolicStandardMap_injective Q Λ θ 0 hQ g hg) m h,
    map_zero]

end Natural

section LIdeal

/-- The module structure on a left ideal of `T^{λ'}` over the factor algebra at `β = ∅`. -/
abbrev idemFactorInst (f : L₀) : Module (parabolicFactorAlgebra Q Λ θ 0) (lIdeal f) :=
  Module.compHom _ (emptyFactorToOld Q Λ θ).toAlgHom.toRingHom

/-- A left ideal `T^{λ'} f` as a module over `T^{λ'} ⊗ R^{λ_ℓ}_0`. -/
def idemFactorModule (f : L₀) : FactorModule Q Λ θ 0 :=
  letI := idemFactorInst Q Λ θ f
  { carrier := lIdeal f
    tower := ⟨fun c t n => by
      change (emptyFactorToOld Q Λ θ (c • t)) • n = c • (emptyFactorToOld Q Λ θ t • n)
      rw [map_smul, smul_assoc]⟩ }

/-- The input of `EmptyRedInd` for `T^{λ'} f` is `T^{λ'} f`. -/
def idemInputEquiv (f : L₀) :
    EmptyRedInput Q Λ θ (idemFactorModule Q Λ θ f).carrier ≃ₗ[L₀] lIdeal f where
  toFun n := n
  invFun n := n
  map_add' _ _ := rfl
  map_smul' t n := by
    rw [RingHom.id_apply]
    change emptyFactorToOld Q Λ θ ((emptyFactorToOld Q Λ θ).symm t) •
      (show lIdeal f from n) = t • (show lIdeal f from n)
    rw [AlgEquiv.apply_symm_apply]
  left_inv _ := rfl
  right_inv _ := rfl

/-- Right multiplication by `c` as a map of modules over the factor algebra. -/
def idemRmul (f c : L₀) :
    (idemFactorModule Q Λ θ f).carrier →ₗ[parabolicFactorAlgebra Q Λ θ 0]
      (idemFactorModule Q Λ θ 1).carrier where
  toFun y := rmulLIdeal f c (show lIdeal f from y)
  map_add' y y' := map_add (rmulLIdeal f c) (show lIdeal f from y) (show lIdeal f from y')
  map_smul' d y := (rmulLIdeal f c).map_smul (emptyFactorToOld Q Λ θ d) (show lIdeal f from y)

variable (hQ : KLRSymm Q)

include hQ in
/-- **Induction along adding the last red strand preserves the injectivity of right
multiplication** on a left ideal of `T^{λ'}`. -/
theorem emptyRed_lIdeal_ind_map_injective {f c : L₀}
    (hg : Function.Injective (rmulLIdeal f c)) :
    Function.Injective (Ind.map (φ := emptyRedHom Q Λ θ) (rmulLIdeal f c)) := by
  have h : rmulLIdeal f c = (idemInputEquiv Q Λ θ 1).toLinearMap.comp
      ((emptyInputMap Q Λ θ (idemRmul Q Λ θ f c)).comp
        (idemInputEquiv Q Λ θ f).symm.toLinearMap) := LinearMap.ext fun _ => rfl
  have hinj : Function.Injective (Ind.map (φ := emptyRedHom Q Λ θ)
      (emptyInputMap Q Λ θ (idemRmul Q Λ θ f c))) :=
    emptyRed_ind_map_injective Q Λ θ hQ _ hg
  rw [h, Ind.map_comp, Ind.map_comp]
  exact (Ind.mapEquiv (φ := emptyRedHom Q Λ θ) (idemInputEquiv Q Λ θ 1)).injective.comp
    (hinj.comp (Ind.mapEquiv (φ := emptyRedHom Q Λ θ) (idemInputEquiv Q Λ θ f).symm).injective)

end LIdeal

end Categorification.Stendhal
