/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastKernel

/-!
# Maps out of a standardization are determined on unit vectors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Definition 5.4, for the induced model of standardization. The standardization `S(N)` is
generated as a `T^λ`-module by the unit vectors `1 ⊗ n` (`parabolicStandardT_mk_smul`), so two
`T^λ`-linear maps out of `S(N)` agree as soon as they agree on the unit vectors of a set of
generators of `N` over the factor algebra (`parabolicStandardT_ext_span`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
  (hQ : KLRSymm Q)

local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

/-- The unit vector `1 ⊗ n` of the standardization, as a vector of the `T^λ`-module. -/
abbrev parabolicStandardTUnit (n : N) : ParabolicStandardT Q Λ θ β N hQ :=
  parabolicStandardUnit Q Λ θ β N n

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem parabolicStandardTUnit_zero :
    parabolicStandardTUnit Q Λ θ β hQ (0 : N) = (0 : ParabolicStandardT Q Λ θ β N hQ) :=
  map_zero (parabolicStandardUnit Q Λ θ β N)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem parabolicStandardTUnit_add (n n' : N) :
    parabolicStandardTUnit Q Λ θ β hQ (n + n') =
      (parabolicStandardTUnit Q Λ θ β hQ n + parabolicStandardTUnit Q Λ θ β hQ n' :
        ParabolicStandardT Q Λ θ β N hQ) :=
  map_add (parabolicStandardUnit Q Λ θ β N) n n'

/-- The class of `a · y` is `a` acting on the class of `y`. -/
theorem parabolicStandardT_mkQ_smul
    (a : KLRAlgebra k (stendhalQ Q Λ) (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ) +
      Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)))
    (y : ParabolicShuffle Q Λ θ β N) :
    (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (a • y)) =
      parabolicAffine Q Λ θ β a •
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y) := by
  change _ = parabolicStandardAction Q Λ θ β N hQ (parabolicAffine Q Λ θ β a)
    (Submodule.mkQ _ y)
  rw [parabolicStandardAction_affine]
  rfl

/-- `[r ⊗ n] = r · (1 ⊗ n)`. -/
theorem parabolicStandardT_mk_tmul
    (r : IndBimod (stendhalQ Q Λ) (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
      (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)))
    (n : ParabolicInput Q Λ θ β N) :
    (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (BalancedTensor.tmul r n)) =
      parabolicAffine Q Λ θ β r.1 • parabolicStandardTUnit Q Λ θ β hQ (show N from n) := by
  have h : (BalancedTensor.tmul r n : ParabolicShuffle Q Λ θ β N) =
      r.1 • indShuffleUnit (Q := stendhalQ Q Λ)
        (ν := Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
        (ν' := Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
          (stendhalWeight 1 β)) (ParabolicInput Q Λ θ β N) n := by
    rw [indShuffleUnit, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext r.2.symm
  rw [h, parabolicStandardT_mkQ_smul]
  rfl

/-- **Maps out of a standardization agree when they agree on the unit vectors.** -/
theorem parabolicStandardT_ext {Z : Type*} [AddCommGroup Z] [Module T Z]
    {f g : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] Z}
    (h : ∀ n : N, f (parabolicStandardTUnit Q Λ θ β hQ n) =
      g (parabolicStandardTUnit Q Λ θ β hQ n)) : f = g := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  induction y using BalancedTensor.induction_on with
  | zero =>
    exact (congrArg f (map_zero (Submodule.mkQ _))).trans
      ((map_zero f).trans ((map_zero g).symm.trans (congrArg g (map_zero (Submodule.mkQ _))).symm))
  | tmul r n =>
    change f (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (BalancedTensor.tmul r n)) =
      g (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (BalancedTensor.tmul r n))
    rw [parabolicStandardT_mk_tmul, map_smul, map_smul, h]
  | add y y' hy hy' =>
    have e : (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (y + y')) =
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y) +
          (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y') :=
      map_add (Submodule.mkQ _) y y'
    exact (congrArg f e).trans ((map_add f _ _).trans ((congrArg₂ (· + ·) hy hy').trans
      ((map_add g _ _).symm.trans (congrArg g e).symm)))

/-- The unit vector of `d · n`, for `d` the image of a diagram `b` of the parabolic
subalgebra. -/
theorem parabolicStandardTUnit_smul
    (b : TensorKLR (stendhalQ Q Λ) (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ))
      (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)))
    (n : N) :
    parabolicStandardTUnit Q Λ θ β hQ (parabolicInputMap Q Λ θ β b • n) =
      parabolicAffine Q Λ θ β (concat (stendhalQ Q Λ) _ _ b) •
        parabolicStandardTUnit Q Λ θ β hQ n :=
  (parabolicStandardAction_concat_unit Q Λ θ β N hQ b n).symm

/-- **Maps out of a standardization agree when they agree on the unit vectors of a set of
generators of the input module.** -/
theorem parabolicStandardT_ext_span {Z : Type*} [AddCommGroup Z] [Module T Z]
    {f g : ParabolicStandardT Q Λ θ β N hQ →ₗ[T] Z} {G : Set N}
    (hG : Submodule.span D G = ⊤)
    (h : ∀ n ∈ G, f (parabolicStandardTUnit Q Λ θ β hQ n) =
      g (parabolicStandardTUnit Q Λ θ β hQ n)) : f = g := by
  refine parabolicStandardT_ext Q Λ θ β hQ fun n => ?_
  have hn : n ∈ Submodule.span D G := hG ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem n hn => exact h n hn
  | zero =>
    rw [parabolicStandardTUnit_zero, map_zero, map_zero]
  | add x y _ _ hx hy =>
    rw [parabolicStandardTUnit_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | smul d x _ hx =>
    obtain ⟨b, rfl⟩ := parabolicInputMap_surjective Q Λ θ β d
    rw [parabolicStandardTUnit_smul, map_smul, map_smul, hx]

end Categorification.Stendhal
