/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowFree
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockFlip

/-!
# The black block at the right end: right freeness by the flip

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, input (B3) with the black block at the
right end, in the right-module form. The top–bottom flip of `T̃` (`StendhalAlgebra.flip`)
commutes with placing diagrams at the maximum on the first `N` strands and diagrams of `λ` on the
last `m` strands (`flip_frontStendhal`, `flip_suffixStendhal`), so it carries the juxtaposition
`ι_R` to itself: `flip (ι_R d) = ι_R (flip_D d)`, where `flip_D` flips both tensor factors of
`D_R = T̃^{(μ,μ*)} ⊗ T̃^λ` (`flip_blockTensorR`). It fixes the front idempotent `e_R` and the
idempotents `1_c`. Applied to the left form (`blockSumFEquiv`), it gives

  `⨁_c 1_c D_R → T̃^{λ⁺} e_R`, `(d_c)_c ↦ ∑_c flip(γ_c) ι_R(d_c)`

(`blockSumRF`), a bijection onto `T̃^{λ⁺} e_R` (`blockSumRF_injective`,
`mem_range_blockSumRF_iff`), right `D_R`-linear (`blockSumRF_blockRightMulF`). The generator
`flip(γ_c)` starts at the bottom loading of `c` (`e_mul_flip_genEltF`), so cutting by `e(v)` on
the left keeps the summands with that loading: `e(v) T̃^{λ⁺} e_R` is right free over `D_R` on the
`flip(γ_c)` with bottom `v` (`e_mul_blockSumRF`, `exists_blockSumRF_of_mem`).

For `ℓ = 0` this is the right freeness of `e(v) A e_R` over `D_R = A′ ⊗ R(b)`, with the
`b`-block on the right. Symmetric `Q` for the freeness statements, any commutative ring; the flip
itself needs no hypothesis.

## Main definitions

* `CupCap.flipDF`: the flip of both factors of `D_R`.
* `CupCap.blockRightF`: the right ideal `1_c D_R`.
* `CupCap.blockSumRF`: the map `⨁_c 1_c D_R → T̃^{λ⁺}`.

## Main results

* `CupCap.flip_frontStendhal`, `CupCap.flip_suffixStendhal`, `CupCap.flip_blockTensorR`.
* `CupCap.blockSumRF_injective`, `CupCap.mem_range_blockSumRF_iff`,
  `CupCap.blockSumRF_blockRightMulF`: right freeness of `T̃^{λ⁺} e_R` over `D_R`.
* `CupCap.e_mul_blockSumRF`, `CupCap.exists_blockSumRF_of_mem`: the cut by `e(v)`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "z₀" => Nat.zero_le ℓ
local notation "zm" => Nat.zero_le (Multiset.card (stendhalWeight ℓ ν))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ)) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Rl" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "β" => botMap k Q Λ Λc 0 (Nat.zero_le ℓ) ν ν₀
local notation "Eₑ" =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc 0 (Nat.zero_le ℓ))) (frontSet ν ν₀)
local notation "ins" => insertMap (j := 0) (hj := Nat.zero_le ℓ) (ν₀ := ν₀) Q Λ Λc

/-! ### The flip on the two blocks, at the level of KLR diagrams -/

section KLRFlip

private theorem hflip_eSum_front {ν' : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}
    (S : Finset (Seq ν')) : hflip (KLRAlgebra.eSum Q' S) = KLRAlgebra.eSum Q' S := by
  simp only [KLRAlgebra.eSum, hflip_sum, hflip_e]

private theorem eSum_mul_x_front {ν' : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}
    (S : Finset (Seq ν')) (a : Fin (Multiset.card ν')) :
    KLRAlgebra.eSum Q' S * KLRAlgebra.x a = KLRAlgebra.x a * KLRAlgebra.eSum Q' S := by
  simp only [KLRAlgebra.eSum, Finset.sum_mul, Finset.mul_sum, e_mul_x]

private theorem suffixMapKLR_one : suffixMapKLR Q Λ Λc ν ν₀ (1 : Rl) = Eₑ := by
  classical
  rw [← KLRAlgebra.sum_e, eSum_frontSet]
  have h : ∀ S : Finset (Seq (stendhalWeight ℓ ν)),
      suffixMapKLR Q Λ Λc ν ν₀ (∑ s ∈ S, KLRAlgebra.e s) =
        ∑ s ∈ S, KLRAlgebra.eSum _ (insertSet (j := 0) (hj := z₀) (ν₀ := ν₀) s 0 zm) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, suffixMapKLR_zero]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, suffixMapKLR_add, ih, suffixMapKLR_e]
  exact h Finset.univ

/-- **Placing a diagram of `λ` on the last `m` strands commutes with the flip.** -/
theorem hflip_suffixMapKLR (a : Rl) :
    hflip (suffixMapKLR Q Λ Λc ν ν₀ a) = suffixMapKLR Q Λ Λc ν ν₀ (hflip a) := by
  let S : Subalgebra k Rl :=
    { carrier := {a | hflip (suffixMapKLR Q Λ Λc ν ν₀ a) = suffixMapKLR Q Λ Λc ν ν₀ (hflip a)}
      mul_mem' := fun {a b} (ha : hflip (suffixMapKLR Q Λ Λc ν ν₀ a) = _)
          (hb : hflip (suffixMapKLR Q Λ Λc ν ν₀ b) = _) => by
        change hflip (suffixMapKLR Q Λ Λc ν ν₀ (a * b)) =
          suffixMapKLR Q Λ Λc ν ν₀ (hflip (a * b))
        rw [suffixMapKLR_mul, hflip_mul, hflip_mul, suffixMapKLR_mul, ha, hb]
      add_mem' := fun {a b} (ha : hflip (suffixMapKLR Q Λ Λc ν ν₀ a) = _)
          (hb : hflip (suffixMapKLR Q Λ Λc ν ν₀ b) = _) => by
        change hflip (suffixMapKLR Q Λ Λc ν ν₀ (a + b)) =
          suffixMapKLR Q Λ Λc ν ν₀ (hflip (a + b))
        rw [suffixMapKLR_add, hflip_add, hflip_add, suffixMapKLR_add, ha, hb]
      algebraMap_mem' := fun c => by
        change hflip (suffixMapKLR Q Λ Λc ν ν₀ (algebraMap k Rl c)) =
          suffixMapKLR Q Λ Λc ν ν₀ (hflip (algebraMap k Rl c))
        rw [hflip_algebraMap, Algebra.algebraMap_eq_smul_one, suffixMapKLR_smul, hflip_smul,
          suffixMapKLR_one, hflip_eSum_front] }
  refine mem_of_gens (AlgHom.id k Rl) S (fun w => ?_) (fun b => ?_) (fun q => ?_) a
  · change hflip (suffixMapKLR Q Λ Λc ν ν₀ (e w)) = suffixMapKLR Q Λ Λc ν ν₀ (hflip (e w))
    rw [hflip_e, suffixMapKLR_e, hflip_eSum_front]
  · change hflip (suffixMapKLR Q Λ Λc ν ν₀ (x b)) = suffixMapKLR Q Λ Λc ν ν₀ (hflip (x b))
    rw [hflip_x, suffixMapKLR_x, hflip_mul, hflip_x, hflip_eSum_front, eSum_mul_x_front]
  · change hflip (suffixMapKLR Q Λ Λc ν ν₀ (ψ q)) = suffixMapKLR Q Λ Λc ν ν₀ (hflip (ψ q))
    rw [hflip_ψ]
    by_cases hq : q + 1 < m
    · have hc := eSum_front_mul_ψw_suffix (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (ν := ν)
        (ν₀ := ν₀) (α := [q]) (by simpa [ValidWord] using hq)
      simp only [shiftWord, List.map_cons, List.map_nil, ψw_cons, ψw_nil, mul_one] at hc
      rw [suffixMapKLR_ψ hq, hflip_mul, hflip_ψ, hflip_eSum_front, hc]
    · rw [KLRAlgebra.ψ_eq_zero q (by omega), suffixMapKLR_zero]
      exact hflip_zero

private theorem hflip_insertMap_front (s : Seq (stendhalWeight ℓ ν)) (g : Rc) :
    hflip (ins s 0 zm g) = ins s 0 zm (hflip g) := by
  let S : Subalgebra k Rc :=
    { carrier := {g | hflip (ins s 0 zm g) = ins s 0 zm (hflip g)}
      mul_mem' := fun {a b} (ha : hflip (ins s 0 zm a) = _)
          (hb : hflip (ins s 0 zm b) = _) => by
        change hflip (ins s 0 zm (a * b)) = ins s 0 zm (hflip (a * b))
        rw [insertMap_mul, hflip_mul, hflip_mul, insertMap_mul, ha, hb]
      add_mem' := fun {a b} (ha : hflip (ins s 0 zm a) = _)
          (hb : hflip (ins s 0 zm b) = _) => by
        change hflip (ins s 0 zm (a + b)) = ins s 0 zm (hflip (a + b))
        rw [insertMap_add, hflip_add, hflip_add, insertMap_add, ha, hb]
      algebraMap_mem' := fun c => by
        change hflip (ins s 0 zm (algebraMap k Rc c)) =
          ins s 0 zm (hflip (algebraMap k Rc c))
        rw [hflip_algebraMap, insertMap_algebraMap, hflip_smul, hflip_eSum_front] }
  refine mem_of_gens (AlgHom.id k Rc) S (fun w => ?_) (fun b => ?_) (fun q => ?_) g
  · change hflip (ins s 0 zm (e w)) = ins s 0 zm (hflip (e w))
    rw [hflip_e, insertMap_e, hflip_e]
  · change hflip (ins s 0 zm (x b)) = ins s 0 zm (hflip (x b))
    rw [hflip_x, insertMap_x, hflip_mul, hflip_x, hflip_eSum_front, eSum_mul_x_front]
  · change hflip (ins s 0 zm (ψ q)) = ins s 0 zm (hflip (ψ q))
    rw [hflip_ψ]
    by_cases hq : q + 1 < N
    · rw [insertMap_ψ s zm hq, hflip_mul, hflip_ψ, hflip_eSum_front,
        eSum_insertSet_mul_ψ s zm hq]
    · rw [KLRAlgebra.ψ_eq_zero q (by omega)]
      simp [insertMap]

/-- **Placing a diagram at the maximum on the first `N` strands commutes with the flip.** -/
theorem hflip_frontMapKLR (g : Rc) :
    hflip (frontMapKLR Q Λ Λc ν ν₀ g) = frontMapKLR Q Λ Λc ν ν₀ (hflip g) := by
  rw [frontMapKLR_eq_sum, frontMapKLR_eq_sum, hflip_sum]
  exact Finset.sum_congr rfl fun s _ => hflip_insertMap_front s g

end KLRFlip

/-! ### The flip on `T̃^{λ⁺}` and the two block maps -/

theorem flip_botMap_front (y : Rp) :
    StendhalAlgebra.flip (β y) = β (hflip y) :=
  StendhalAlgebra.flip_topMap y

/-- **The flip commutes with placing a diagram of `λ` on the last `m` strands.** -/
theorem flip_suffixStendhal (z : T) :
    StendhalAlgebra.flip (suffixStendhal Q Λ Λc ν ν₀ z) =
      suffixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  have h1 : suffixStendhal Q Λ Λc ν ν₀ z = β (suffixMapKLR Q Λ Λc ν ν₀ a) := by
    rw [suffixStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]; rfl
  have h2 : suffixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) =
      β (suffixMapKLR Q Λ Λc ν ν₀ (hflip a)) := by
    rw [suffixStendhal, stendhalLift_apply, StendhalAlgebra.flip_val, ← ha,
      StendhalAlgebraAllOrders.flip_ofKLR, allOrdersLift_ofKLR]; rfl
  rw [h1, h2, flip_botMap_front, hflip_suffixMapKLR]

/-- **The flip commutes with placing a diagram at the maximum on the first `N` strands.** -/
theorem flip_frontStendhal (z : Tc) :
    StendhalAlgebra.flip (frontStendhal Q Λ Λc ν ν₀ z) =
      frontStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  have h1 : frontStendhal Q Λ Λc ν ν₀ z = β (frontMapKLR Q Λ Λc ν ν₀ a) := by
    rw [frontStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]; rfl
  have h2 : frontStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) =
      β (frontMapKLR Q Λ Λc ν ν₀ (hflip a)) := by
    rw [frontStendhal, stendhalLift_apply, StendhalAlgebra.flip_val, ← ha,
      StendhalAlgebraAllOrders.flip_ofKLR, allOrdersLift_ofKLR]; rfl
  rw [h1, h2, flip_botMap_front, hflip_frontMapKLR]

/-- The flip fixes the front idempotent `e_R`. -/
theorem flip_frontStendhal_one :
    StendhalAlgebra.flip (frontStendhal Q Λ Λc ν ν₀ 1) = frontStendhal Q Λ Λc ν ν₀ 1 := by
  rw [flip_frontStendhal, StendhalAlgebra.flip_one]

/-! ### The flip on `D_R` -/

variable (Q Λ Λc ν ν₀) in
/-- **The flip of `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ`**, on both factors. -/
def flipDF : Tc ⊗[k] T →ₗ[k] Tc ⊗[k] T := TensorProduct.map (flipLin Q Λc ν₀) (flipLin Q Λ ν)

theorem flipDF_tmul (y : Tc) (x : T) :
    flipDF Q Λ Λc ν ν₀ (y ⊗ₜ x) = StendhalAlgebra.flip y ⊗ₜ StendhalAlgebra.flip x := rfl

theorem flipDF_flipDF (d : Tc ⊗[k] T) : flipDF Q Λ Λc ν ν₀ (flipDF Q Λ Λc ν ν₀ d) = d := by
  induction d using TensorProduct.inductionOn with
  | tmul y x =>
    rw [flipDF_tmul, flipDF_tmul, StendhalAlgebra.flip_flip, StendhalAlgebra.flip_flip]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem flipDF_mul (d d' : Tc ⊗[k] T) :
    flipDF Q Λ Λc ν ν₀ (d * d') = flipDF Q Λ Λc ν ν₀ d' * flipDF Q Λ Λc ν ν₀ d := by
  induction d using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, mul_add]
  | tmul y x =>
    induction d' using TensorProduct.inductionOn with
    | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, add_mul]
    | tmul y' x' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, flipDF_tmul, flipDF_tmul, flipDF_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, StendhalAlgebra.flip_mul, StendhalAlgebra.flip_mul]

/-- **The flip carries the juxtaposition `ι_R` to itself**: `flip (ι_R d) = ι_R (flip_D d)`. -/
theorem flip_blockTensorR (d : Tc ⊗[k] T) :
    StendhalAlgebra.flip (blockTensorR Q Λ Λc ν ν₀ d) =
      blockTensorR Q Λ Λc ν ν₀ (flipDF Q Λ Λc ν ν₀ d) := by
  induction d using TensorProduct.inductionOn with
  | tmul y x =>
    rw [blockTensorR_tmul, StendhalAlgebra.flip_mul, flipDF_tmul, blockTensorR_tmul,
      flip_frontStendhal, flip_suffixStendhal,
      (commute_suffixStendhal_frontStendhal Q Λ Λc _ _).eq]
  | add a b ha hb => rw [map_add, StendhalAlgebra.flip_add, ha, hb, map_add, map_add]

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

theorem flipDF_blockIdemF (c : FrontGen ℓ ν ν₀) :
    flipDF Q Λ Λc ν ν₀ (blockIdemF Q Λ Λc c) = blockIdemF Q Λ Λc c := by
  rw [blockIdemF, flipDF_tmul, StendhalAlgebra.flip_e, StendhalAlgebra.flip_e]

/-! ### The right ideals `1_c D_R` and the map `⨁_c 1_c D_R → T̃^{λ⁺} e_R` -/

variable (Q Λ Λc) in
/-- The right ideal `1_c D_R = {d | 1_c d = d}` of `D_R`, as a `k`-submodule. -/
def blockRightF (c : FrontGen ℓ ν ν₀) : Submodule k (Tc ⊗[k] T) where
  carrier := {d | blockIdemF Q Λ Λc c * d = d}
  add_mem' {d d'} hd hd' := by
    change _ * (d + d') = d + d'
    rw [mul_add, hd, hd']
  zero_mem' := mul_zero _
  smul_mem' r d hd := by
    change _ * (r • d) = r • d
    rw [mul_smul_comm, hd]

theorem mem_blockRightF {c : FrontGen ℓ ν ν₀} {d : Tc ⊗[k] T} :
    d ∈ blockRightF Q Λ Λc c ↔ blockIdemF Q Λ Λc c * d = d := Iff.rfl

theorem flipDF_mem_blockRightF {c : FrontGen ℓ ν ν₀} {d : Tc ⊗[k] T}
    (hd : d ∈ blockLeftF Q Λ Λc c) : flipDF Q Λ Λc ν ν₀ d ∈ blockRightF Q Λ Λc c := by
  rw [mem_blockRightF, ← flipDF_blockIdemF, ← flipDF_mul, mem_blockLeftF.1 hd]

theorem flipDF_mem_blockLeftF {c : FrontGen ℓ ν ν₀} {d : Tc ⊗[k] T}
    (hd : d ∈ blockRightF Q Λ Λc c) : flipDF Q Λ Λc ν ν₀ d ∈ blockLeftF Q Λ Λc c := by
  rw [mem_blockLeftF, ← flipDF_blockIdemF c, ← flipDF_mul, mem_blockRightF.1 hd]

variable (Q Λ Λc ν ν₀) in
/-- The flip `D_R 1_c → 1_c D_R`. -/
def flipLeftRightF (c : FrontGen ℓ ν ν₀) : blockLeftF Q Λ Λc c →ₗ[k] blockRightF Q Λ Λc c where
  toFun d := ⟨flipDF Q Λ Λc ν ν₀ d, flipDF_mem_blockRightF d.2⟩
  map_add' d d' := Subtype.ext (map_add _ d.1 d'.1)
  map_smul' r d := Subtype.ext (map_smul _ r d.1)

variable (Q Λ Λc ν ν₀) in
/-- The flip `1_c D_R → D_R 1_c`. -/
def flipRightLeftF (c : FrontGen ℓ ν ν₀) : blockRightF Q Λ Λc c →ₗ[k] blockLeftF Q Λ Λc c where
  toFun d := ⟨flipDF Q Λ Λc ν ν₀ d, flipDF_mem_blockLeftF d.2⟩
  map_add' d d' := Subtype.ext (map_add _ d.1 d'.1)
  map_smul' r d := Subtype.ext (map_smul _ r d.1)

variable [DecidableEq (FrontGen ℓ ν ν₀)]

variable (Q Λ Λc ρ₃) in
/-- **The map** `⨁_c 1_c D_R → T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c flip(γ_c) ι_R(d_c)`. -/
def blockSumRF : (Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) →ₗ[k] Tp :=
  DFinsupp.lsum ℕ fun c =>
    (LinearMap.mulLeft k (StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c))).comp
      ((blockTensorRLin Q Λ Λc ν ν₀).comp (blockRightF Q Λ Λc c).subtype)

theorem blockSumRF_single (c : FrontGen ℓ ν ν₀) (a : blockRightF Q Λ Λc c) :
    blockSumRF Q Λ Λc ρ₃ (DFinsupp.single c a) =
      StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c) * blockTensorR Q Λ Λc ν ν₀ a := by
  rw [blockSumRF, DFinsupp.lsum_single]
  rfl

/-- The flip turns `⨁_c D_R 1_c` into `⨁_c 1_c D_R`. -/
def flipSumF : (Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) →ₗ[k]
    Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c => flipLeftRightF Q Λ Λc ν ν₀ c

/-- The flip turns `⨁_c 1_c D_R` into `⨁_c D_R 1_c`. -/
def flipSumInvF : (Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) →ₗ[k]
    Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c => flipRightLeftF Q Λ Λc ν ν₀ c

omit [DecidableEq (FrontGen ℓ ν ν₀)] in
theorem flipSumF_flipSumInvF (b : Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) :
    flipSumF (flipSumInvF b) = b := by
  ext c
  simp [flipSumF, flipSumInvF, flipLeftRightF, flipRightLeftF, flipDF_flipDF]

/-- **The flip of `∑_c ι_R(d_c) γ_c` is `∑_c flip(γ_c) ι_R(flip_D d_c)`.** -/
theorem flip_blockSumF (a : Π₀ c : FrontGen ℓ ν ν₀, blockLeftF Q Λ Λc c) :
    StendhalAlgebra.flip (blockSumF Q Λ Λc ρ₃ a) = blockSumRF Q Λ Λc ρ₃ (flipSumF a) := by
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero, map_zero, map_zero, StendhalAlgebra.flip_zero]
  | ha c b f _ _ ih =>
    have hs : flipSumF (DFinsupp.single c b) =
        DFinsupp.single c (flipLeftRightF Q Λ Λc ν ν₀ c b) := by
      simp only [flipSumF, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]
    rw [map_add, StendhalAlgebra.flip_add, ih, map_add, map_add, blockSumF_single, hs,
      blockSumRF_single, StendhalAlgebra.flip_mul, flip_blockTensorR]
    rfl

/-- **Right freeness, uniqueness**: the map `⨁_c 1_c D_R → T̃^{λ⁺} e_R` is injective. -/
theorem blockSumRF_injective (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Injective (blockSumRF Q Λ Λc ρ₃) := by
  intro b b' h
  rw [← flipSumF_flipSumInvF b, ← flipSumF_flipSumInvF b', ← flip_blockSumF,
    ← flip_blockSumF] at h
  have h' := blockSumF_injective (ρ₁ := ρ₁) (ρ₂ := ρ₂) hQ hρ₁ hρ₂ hρ₃
    (StendhalAlgebra.flip_injective h)
  rw [← flipSumF_flipSumInvF b, ← flipSumF_flipSumInvF b', h']

/-- **Right freeness, existence**: `z` is `∑_c flip(γ_c) ι_R(d_c)` for some
`(d_c) ∈ ⨁_c 1_c D_R` if and only if `z e_R = z`. -/
theorem mem_range_blockSumRF_iff (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (z : Tp) :
    z ∈ LinearMap.range (blockSumRF Q Λ Λc ρ₃) ↔ z * frontStendhal Q Λ Λc ν ν₀ 1 = z := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [← flipSumF_flipSumInvF b, ← flip_blockSumF, ← flip_frontStendhal_one,
      ← StendhalAlgebra.flip_mul, frontStendhal_one_mul_blockSumF]
  · intro hz
    have hz' : frontStendhal Q Λ Λc ν ν₀ 1 * StendhalAlgebra.flip z = StendhalAlgebra.flip z := by
      rw [← flip_frontStendhal_one, ← StendhalAlgebra.flip_mul, hz]
    obtain ⟨a, ha⟩ := (mem_range_blockSumF_iff (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃ _).2 hz'
    refine ⟨flipSumF a, ?_⟩
    rw [← flip_blockSumF, ha, StendhalAlgebra.flip_flip]

variable (Q Λ Λc) in
/-- Right multiplication by `d ∈ D_R` on `⨁_c 1_c D_R`, componentwise. -/
def blockRightMulF (d : Tc ⊗[k] T) :
    (Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) →ₗ[k]
      Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c =>
    { toFun := fun b => ⟨b * d, by rw [mem_blockRightF, ← mul_assoc, mem_blockRightF.1 b.2]⟩
      map_add' := fun b b' => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r b => Subtype.ext (smul_mul_assoc _ _ _) }

/-- **Right `D_R`-linearity**: `∑_c flip(γ_c) ι_R(d_c d) = (∑_c flip(γ_c) ι_R(d_c)) ι_R(d)`. -/
theorem blockSumRF_blockRightMulF (d : Tc ⊗[k] T)
    (b : Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) :
    blockSumRF Q Λ Λc ρ₃ (blockRightMulF Q Λ Λc d b) =
      blockSumRF Q Λ Λc ρ₃ b * blockTensorR Q Λ Λc ν ν₀ d := by
  have h : (blockSumRF Q Λ Λc ρ₃).comp (blockRightMulF Q Λ Λc d) =
      (LinearMap.mulRight k (blockTensorR Q Λ Λc ν ν₀ d)).comp (blockSumRF Q Λ Λc ρ₃) := by
    refine DFinsupp.lhom_ext' fun c => LinearMap.ext fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DFinsupp.lsingle_apply, blockRightMulF,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mulRight_apply]
    rw [blockSumRF_single, blockSumRF_single, blockTensorR_mul, mul_assoc]
  exact LinearMap.congr_fun h b

/-! ### The cut by `e(v)` -/

omit [DecidableEq (FrontGen ℓ ν ν₀)] in
/-- `γ_c` ends at the bottom loading of `c`: `γ_c e(t)` is `γ_c` if the bottom of `c` is `t`,
and `0` otherwise. -/
theorem genEltF_mul_e (c : FrontGen ℓ ν ν₀) (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : IsRedOrdered t) :
    genEltF Q Λ Λc ρ₃ c * StendhalAlgebra.e t ht =
      if c.bot = t then genEltF Q Λ Λc ρ₃ c else 0 := by
  have he : (StendhalAlgebra.e t ht : Tp) = β (KLRAlgebra.e t) :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem t).trans (ite_eq_left ht)).symm
  rw [he, genEltF, ← map_mul, genKLRF, mul_assoc, KLRAlgebra.e_mul_e]
  split_ifs
  · rfl
  · rw [mul_zero, map_zero]

omit [DecidableEq (FrontGen ℓ ν ν₀)] in
/-- `flip(γ_c)` starts at the bottom loading of `c`: `e(v) flip(γ_c)` is `flip(γ_c)` if the
bottom of `c` is `v`, and `0` otherwise. -/
theorem e_mul_flip_genEltF (c : FrontGen ℓ ν ν₀) (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hv : IsRedOrdered v) :
    StendhalAlgebra.e v hv * StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c) =
      if c.bot = v then StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c) else 0 := by
  rw [← StendhalAlgebra.flip_e v hv, ← StendhalAlgebra.flip_mul, genEltF_mul_e]
  split_ifs
  · rfl
  · exact StendhalAlgebra.flip_zero

/-- **The cut by `e(v)`**: `e(v) ∑_c flip(γ_c) ι_R(d_c)` keeps the summands whose base generator
has bottom `v`. -/
theorem e_mul_blockSumRF (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hv : IsRedOrdered v)
    (b : Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c) :
    StendhalAlgebra.e v hv * blockSumRF Q Λ Λc ρ₃ b =
      blockSumRF Q Λ Λc ρ₃ (b.filter fun c => c.bot = v) := by
  induction b using DFinsupp.induction with
  | h0 => rw [map_zero, mul_zero, DFinsupp.filter_zero, map_zero]
  | ha c a f _ _ ih =>
    rw [map_add, mul_add, ih, DFinsupp.filter_add, map_add, DFinsupp.filter_single,
      blockSumRF_single, ← mul_assoc, e_mul_flip_genEltF c v hv]
    split_ifs
    · rw [blockSumRF_single]
    · rw [zero_mul, map_zero]

/-- **`e(v) T̃^{λ⁺} e_R` is right free over `D_R`** on the `flip(γ_c)` with bottom `v`: every `z`
with `e(v) z = z` and `z e_R = z` is `∑_c flip(γ_c) ι_R(d_c)` with `d_c = 0` unless the bottom of
`c` is `v`. -/
theorem exists_blockSumRF_of_mem (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hv : IsRedOrdered v) (z : Tp)
    (hvz : StendhalAlgebra.e v hv * z = z) (hz : z * frontStendhal Q Λ Λc ν ν₀ 1 = z) :
    ∃ b : Π₀ c : FrontGen ℓ ν ν₀, blockRightF Q Λ Λc c,
      (∀ c, c.bot ≠ v → b c = 0) ∧ blockSumRF Q Λ Λc ρ₃ b = z := by
  obtain ⟨b, hb⟩ := (mem_range_blockSumRF_iff (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃ z).2 hz
  have hf : b.filter (fun c => c.bot = v) = b := by
    apply blockSumRF_injective (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃
    rw [← e_mul_blockSumRF v hv, hb, hvz]
  refine ⟨b, fun c hc => ?_, hb⟩
  rw [← hf, DFinsupp.filter_apply_neg b hc]

end Categorification.Stendhal.CupCap
