/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairRightmostWeightOne
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The middle partial-standard quotient of the second spectator-crossing image

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
At final spectator weight one, the image of the second crossing modulo
the image of the strictly higher terminal kernel is the actual middle
partial standard.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

private abbrev quotientModule {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (K : Submodule S M) : ModuleCat S :=
  ModuleCat.of S (M ⧸ K)

private abbrev quotientImageModule {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (K : Submodule S M) : ModuleCat S :=
  quotientModule (K.map f.rangeRestrict)

/-- Passing to the image of a linear map preserves the quotient by a
submodule containing the kernel. -/
private def quotientImageEquiv {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (K : Submodule S M)
    (h : LinearMap.ker f ≤ K) :
        quotientImageModule f K ≃ₗ[S] quotientModule K := by
  let image := K.map f.rangeRestrict
  let g := image.mkQ.comp f.rangeRestrict
  have hg : Function.Surjective g := by
    apply image.mkQ_surjective.comp
    rintro ⟨_, ⟨x, hx⟩⟩
    exact ⟨x, Subtype.ext hx⟩
  have hk : LinearMap.ker g = K := by
    ext x
    change g x = 0 ↔ x ∈ K
    rw [show g x = image.mkQ (f.rangeRestrict x) from rfl]
    change Submodule.Quotient.mk (f.rangeRestrict x) = 0 ↔ x ∈ K
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      obtain ⟨y, hy, eq⟩ := Submodule.mem_map.mp hx
      have diff : x - y ∈ LinearMap.ker f := by
        apply LinearMap.mem_ker.mpr
        rw [map_sub, show f y = f x from congrArg Subtype.val eq, sub_self]
      exact (sub_add_cancel x y) ▸ K.add_mem (h diff) hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  exact (g.quotKerEquivOfSurjective hg).symm.trans (Submodule.quotEquivOfEq _ _ hk)

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial MulOpposite

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "B" => firstPairOneAfterSpectator true
local notation "D" => sadj N 3 • B
local notation "Rtop" => firstPairTwoAfterSpectator

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" s:arg => F (e s)
local notation "δ" => (ψw [3,2] * e B : A)
local notation "β" => (ψ 3 * e D : A)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν (redWord B)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord B))
local notation "T" => IsIdempotentElem.Corner ord
local notation "P" => rIdeal (orderedLoadingIdem Q Λ B)
private theorem firstPair_rightmost_same_order : redWord Rtop = redWord B := by decide

local notation "P'" =>
  rIdeal (orderedLoadingIdemAt Q Λ (redWord B) Rtop firstPair_rightmost_same_order)
local notation "K" => blockLoadingKernel Q Λ B 0 1
local notation "J" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 B) (redWord B)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem firstPair_secondCrossing_left :
    p Rtop * F δ = F δ := by
  have step : wordProd N [3,2] • B = Rtop := by decide +kernel
  rw [← map_mul F, ← step, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc,e_mul_self]

private theorem firstPair_secondCrossing_right :
    F δ * p B = F δ := by
  rw [← map_mul F,mul_assoc,e_mul_self]

private def secondSpectatorCrossingInCorner : T := by
  have Rcut := (Subsemigroup.mem_corner_iff ord).1
    (orderedLoadingIdemAt Q Λ (redWord B) Rtop firstPair_rightmost_same_order).2
  have Bcut := (Subsemigroup.mem_corner_iff ord).1 (orderedLoadingIdem Q Λ B).2
  change E * p Rtop = p Rtop ∧ p Rtop * E = p Rtop at Rcut
  change E * p B = p B ∧ p B * E = p B at Bcut
  have left := firstPair_secondCrossing_left Q Λ
  have right := firstPair_secondCrossing_right Q Λ
  refine ⟨F δ, (Subsemigroup.mem_corner_iff ord).2 ⟨?_,?_⟩⟩
  · calc
      E * F δ = E * (p Rtop * F δ) := congrArg (E * ·) left.symm
      _ = F δ := by rw [← mul_assoc, Rcut.1, left]
  · calc
      F δ * E = (F δ * p B) * E := congrArg (· * E) right.symm
      _ = F δ := by rw [mul_assoc, Bcut.2, right]

/-- The second spectator crossing as a map of loading projectives in the
original ordered corner. -/
def firstPairSecondSpectatorCrossing : P →ₗ[Tᵐᵒᵖ] P' where
  toFun y := ⟨secondSpectatorCrossingInCorner Q Λ * y.1, by
    apply Subtype.ext
    change p Rtop * (F δ * y.1.1) = F δ * y.1.1
    rw [← mul_assoc,firstPair_secondCrossing_left Q Λ]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c y := Subtype.ext (mul_assoc (secondSpectatorCrossingInCorner Q Λ) y.1 c.unop).symm

local notation "f" => firstPairSecondSpectatorCrossing Q Λ

private theorem firstPairSecondSpectatorCrossing_val (x : P) :
    (f x).1.1 = F δ * x.1.1 := rfl

private theorem firstPair_secondCrossing_kernel_le (one : Λ 2 () = 1) :
    LinearMap.ker f ≤ K := by
  intro y hy
  have l : p B * y.1.1 = y.1.1 := congrArg (fun z : T => z.1) y.2
  have z : F δ * y.1.1 = 0 :=
    (firstPairSecondSpectatorCrossing_val Q Λ y).symm.trans
      (congrArg (fun v : P' => v.1.1) (LinearMap.mem_ker.mp hy))
  obtain ⟨w, _, hw⟩ :=
    firstPairRightmost_secondCrossing_kernel_of_weight_one Q Λ one y.1.1 l z
  change y.1.1 ∈ J
  have strict : adjacentBlockRoot 0 1 B < adjacentBlockRoot 0 1 D := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 0 1 D 2 () ≤ adjacentBlockRoot 0 1 B 2 ()) (h 2 ())
  have dMem : p D ∈ J := TwoSidedIdeal.subset_span ⟨D, by decide, strict, rfl⟩
  have bMem : F β ∈ J := by
    rw [map_mul F]
    exact TwoSidedIdeal.mul_mem_left J _ _ dMem
  exact hw ▸ TwoSidedIdeal.mul_mem_right J _ w bMem

set_option backward.isDefEq.respectTransparency false in
/-- The second spectator-crossing image modulo the image of the strictly
higher terminal kernel, in the original red-order corner. -/
def firstPairSecondSpectatorCrossingResidual : ModuleCat Tᵐᵒᵖ := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup P' := Submodule.addCommGroup P'
  let : Module Tᵐᵒᵖ P' := Submodule.module P'
  exact quotientImageModule (S := Tᵐᵒᵖ) (M := P) («N» := P') f K

set_option backward.isDefEq.respectTransparency false in
/-- At final spectator weight one, the second-crossing image modulo the
image of the terminal higher kernel is the actual middle partial standard. -/
def firstPairSecondSpectatorCrossing_residualEquiv (one : Λ 2 () = 1) :
    firstPairSecondSpectatorCrossingResidual Q Λ ≃ₗ[Tᵐᵒᵖ]
      blockPartialStandardAt Q Λ B 0 1 (redWord B) rfl := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup P' := Submodule.addCommGroup P'
  let : Module Tᵐᵒᵖ P' := Submodule.module P'
  have e := quotientImageEquiv (S := Tᵐᵒᵖ) (M := P) («N» := P') f K
    (firstPair_secondCrossing_kernel_le Q Λ one)
  exact e

end Categorification.Stendhal.BraidedStendhalAlgebra
