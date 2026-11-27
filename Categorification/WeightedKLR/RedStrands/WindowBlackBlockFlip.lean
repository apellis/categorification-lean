/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockFree
import Categorification.WeightedKLR.RedStrands.TildeFlip

/-!
# The black block beside the window: right freeness by the flip

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, input (B3), the right-module form used for
the bases `ψ_{τ_{P′}}` in the proof of (IC). The top–bottom flip of `T̃` (`StendhalAlgebra.flip`)
commutes with placing diagrams on the first strands and on the last strands
(`flip_prefixStendhal`, `flip_endStendhal`), so it carries the juxtaposition `ι` to itself:
`flip (ι d) = ι (flip_D d)`, where `flip_D` flips both tensor factors of
`D = T̃^λ ⊗ T̃^{(μ,μ*)}` (`flip_blockTensor`). It fixes the end idempotent `e_L` and the
idempotents `1_c`. Applied to (B3-L) (`blockSumEquiv`), it gives the right-module form

  `⨁_c 1_c D → T̃^{λ⁺} e_L`, `(d_c)_c ↦ ∑_c flip(γ_c) ι(d_c)`

(`blockSumR`), a bijection onto `T̃^{λ⁺} e_L` (`blockSumR_injective`,
`mem_range_blockSumR_iff`), right `D`-linear (`blockSumR_blockRightMul`). The generator
`flip(γ_c) = e(u⁻¹(i j)) ψ_{u}^{flip}` starts at the loading `v = u⁻¹(i j)` of `c`
(`e_mul_flip_genElt`), so cutting by `e(v)` on the left keeps the summands with that loading:
`e(v) T̃^{λ⁺} e_L` is right free over `D` on the `flip(γ_c)` with bottom `v` of `c` equal to `v`
(`e_mul_blockSumR`, `exists_blockSumR_of_mem`).

For `ℓ = 0` this is the right freeness of `e(v) A e_L` over `D = R(b) ⊗ A′` with the `b`-block on
the left. The block at the right end, `e(v) A e_R`, is the flip of (B3-R). Symmetric `Q`, any
commutative ring.

## Main definitions

* `CupCap.flipD`: the flip of both factors of `D`.
* `CupCap.blockRight`: the right ideal `1_c D`.
* `CupCap.blockSumR`: the map `⨁_c 1_c D → T̃^{λ⁺}`.

## Main results

* `CupCap.flip_prefixStendhal`, `CupCap.flip_endStendhal`, `CupCap.flip_blockTensor`.
* `CupCap.blockSumR_injective`, `CupCap.mem_range_blockSumR_iff`,
  `CupCap.blockSumR_blockRightMul`: right freeness of `T̃^{λ⁺} e_L` over `D`.
* `CupCap.e_mul_blockSumR`, `CupCap.exists_blockSumR_of_mem`: the cut by `e(v)`.
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
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Rl" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "Eₑ" => KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (endSet ν ν₀)
local notation "ins" => insertMap (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) Q Λ Λc
local notation "Eᵢ" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
    (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl)

/-! ### The flip on the two blocks, at the level of KLR diagrams -/

section KLRFlip

private theorem hflip_eSum {ν' : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}
    (S : Finset (Seq ν')) : hflip (KLRAlgebra.eSum Q' S) = KLRAlgebra.eSum Q' S := by
  simp only [KLRAlgebra.eSum, hflip_sum, hflip_e]

private theorem eSum_mul_x {ν' : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}
    (S : Finset (Seq ν')) (a : Fin (Multiset.card ν')) :
    KLRAlgebra.eSum Q' S * KLRAlgebra.x a = KLRAlgebra.x a * KLRAlgebra.eSum Q' S := by
  simp only [KLRAlgebra.eSum, Finset.sum_mul, Finset.mul_sum, e_mul_x]

private theorem prefixMapKLR_add' (a b : Rl) :
    prefixMapKLR Q Λ Λc ν ν₀ (a + b) = prefixMapKLR Q Λ Λc ν ν₀ a + prefixMapKLR Q Λ Λc ν ν₀ b := by
  unfold prefixMapKLR; rw [map_add, map_add]; rfl

private theorem prefixMapKLR_one : prefixMapKLR Q Λ Λc ν ν₀ (1 : Rl) =
    ∑ s : Seq (stendhalWeight ℓ ν), Eᵢ s := by
  classical
  rw [← KLRAlgebra.sum_e]
  have h : ∀ S : Finset (Seq (stendhalWeight ℓ ν)),
      prefixMapKLR Q Λ Λc ν ν₀ (∑ s ∈ S, KLRAlgebra.e s) = ∑ s ∈ S, Eᵢ s := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      unfold prefixMapKLR; rw [map_zero, map_zero]; rfl
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, prefixMapKLR_add', ih, prefixMapKLR_e]
  exact h Finset.univ

/-- **Placing a diagram of `λ` on the first strands commutes with the flip.** -/
theorem hflip_prefixMapKLR (a : Rl) :
    hflip (prefixMapKLR Q Λ Λc ν ν₀ a) = prefixMapKLR Q Λ Λc ν ν₀ (hflip a) := by
  let S : Subalgebra k Rl :=
    { carrier := {a | hflip (prefixMapKLR Q Λ Λc ν ν₀ a) = prefixMapKLR Q Λ Λc ν ν₀ (hflip a)}
      mul_mem' := fun {a b} (ha : hflip (prefixMapKLR Q Λ Λc ν ν₀ a) = _)
          (hb : hflip (prefixMapKLR Q Λ Λc ν ν₀ b) = _) => by
        change hflip (prefixMapKLR Q Λ Λc ν ν₀ (a * b)) = prefixMapKLR Q Λ Λc ν ν₀ (hflip (a * b))
        rw [prefixMapKLR_mul, hflip_mul, hflip_mul, prefixMapKLR_mul, ha, hb]
      add_mem' := fun {a b} (ha : hflip (prefixMapKLR Q Λ Λc ν ν₀ a) = _)
          (hb : hflip (prefixMapKLR Q Λ Λc ν ν₀ b) = _) => by
        change hflip (prefixMapKLR Q Λ Λc ν ν₀ (a + b)) = prefixMapKLR Q Λ Λc ν ν₀ (hflip (a + b))
        rw [prefixMapKLR_add', hflip_add, hflip_add, prefixMapKLR_add', ha, hb]
      algebraMap_mem' := fun c => by
        change hflip (prefixMapKLR Q Λ Λc ν ν₀ (algebraMap k Rl c)) =
          prefixMapKLR Q Λ Λc ν ν₀ (hflip (algebraMap k Rl c))
        rw [hflip_algebraMap, Algebra.algebraMap_eq_smul_one, prefixMapKLR_smul, hflip_smul,
          prefixMapKLR_one, hflip_sum]
        simp only [hflip_eSum] }
  refine mem_of_gens (AlgHom.id k Rl) S (fun w => ?_) (fun b => ?_) (fun q => ?_) a
  · change hflip (prefixMapKLR Q Λ Λc ν ν₀ (e w)) = prefixMapKLR Q Λ Λc ν ν₀ (hflip (e w))
    rw [hflip_e, prefixMapKLR_e, hflip_eSum]
  · change hflip (prefixMapKLR Q Λ Λc ν ν₀ (x b)) = prefixMapKLR Q Λ Λc ν ν₀ (hflip (x b))
    rw [hflip_x, prefixMapKLR_x, hflip_mul, hflip_x, hflip_eSum, eSum_mul_x]
  · change hflip (prefixMapKLR Q Λ Λc ν ν₀ (ψ q)) = prefixMapKLR Q Λ Λc ν ν₀ (hflip (ψ q))
    rw [hflip_ψ]
    by_cases hq : q + 1 < m
    · have hc := eSum_end_mul_ψw_prefix (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
        (α := [q]) (by simpa [ValidWord] using hq)
      simp only [ψw_cons, ψw_nil, mul_one] at hc
      rw [prefixMapKLR_ψ Q Λ Λc (ν := ν) (ν₀ := ν₀) hq, hflip_mul, hflip_ψ, hflip_eSum, hc]
    · rw [KLRAlgebra.ψ_eq_zero q (by omega)]
      unfold prefixMapKLR
      rw [map_zero, map_zero]
      exact hflip_zero

private theorem hflip_insertMap' (s : Seq (stendhalWeight ℓ ν)) (g : Rc) :
    hflip (ins s m le_rfl g) = ins s m le_rfl (hflip g) := by
  let S : Subalgebra k Rc :=
    { carrier := {g | hflip (ins s m le_rfl g) = ins s m le_rfl (hflip g)}
      mul_mem' := fun {a b} (ha : hflip (ins s m le_rfl a) = _)
          (hb : hflip (ins s m le_rfl b) = _) => by
        change hflip (ins s m le_rfl (a * b)) = ins s m le_rfl (hflip (a * b))
        rw [insertMap_mul, hflip_mul, hflip_mul, insertMap_mul, ha, hb]
      add_mem' := fun {a b} (ha : hflip (ins s m le_rfl a) = _)
          (hb : hflip (ins s m le_rfl b) = _) => by
        change hflip (ins s m le_rfl (a + b)) = ins s m le_rfl (hflip (a + b))
        rw [insertMap_add, hflip_add, hflip_add, insertMap_add, ha, hb]
      algebraMap_mem' := fun c => by
        change hflip (ins s m le_rfl (algebraMap k Rc c)) =
          ins s m le_rfl (hflip (algebraMap k Rc c))
        rw [hflip_algebraMap, insertMap_algebraMap, hflip_smul, hflip_eSum] }
  refine mem_of_gens (AlgHom.id k Rc) S (fun w => ?_) (fun b => ?_) (fun q => ?_) g
  · change hflip (ins s m le_rfl (e w)) = ins s m le_rfl (hflip (e w))
    rw [hflip_e, insertMap_e, hflip_e]
  · change hflip (ins s m le_rfl (x b)) = ins s m le_rfl (hflip (x b))
    rw [hflip_x, insertMap_x, hflip_mul, hflip_x, hflip_eSum, eSum_mul_x]
  · change hflip (ins s m le_rfl (ψ q)) = ins s m le_rfl (hflip (ψ q))
    rw [hflip_ψ]
    by_cases hq : q + 1 < N
    · rw [insertMap_ψ s le_rfl hq, hflip_mul, hflip_ψ, hflip_eSum,
        eSum_insertSet_mul_ψ s le_rfl hq]
    · rw [KLRAlgebra.ψ_eq_zero q (by omega)]
      simp [insertMap]

/-- **Placing a diagram on the last strands commutes with the flip.** -/
theorem hflip_endMapKLR (g : Rc) :
    hflip (endMapKLR Q Λ Λc ν ν₀ g) = endMapKLR Q Λ Λc ν ν₀ (hflip g) := by
  rw [endMapKLR_eq_sum, endMapKLR_eq_sum, hflip_sum]
  exact Finset.sum_congr rfl fun s _ => hflip_insertMap' s g

end KLRFlip

/-! ### The flip on `T̃^{λ⁺}` and the two block maps -/

theorem flip_botMap (y : Rp) :
    StendhalAlgebra.flip (botMap k Q Λ Λc ℓ le_rfl ν ν₀ y) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (hflip y) :=
  StendhalAlgebra.flip_topMap y

/-- **The flip commutes with placing a diagram of `λ` on the first strands.** -/
theorem flip_prefixStendhal (z : T) :
    StendhalAlgebra.flip (prefixStendhal Q Λ Λc ν ν₀ z) =
      prefixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  have h1 : prefixStendhal Q Λ Λc ν ν₀ z =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ a) := by
    rw [prefixStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]; rfl
  have h2 : prefixStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (prefixMapKLR Q Λ Λc ν ν₀ (hflip a)) := by
    rw [prefixStendhal, stendhalLift_apply, StendhalAlgebra.flip_val, ← ha,
      StendhalAlgebraAllOrders.flip_ofKLR, allOrdersLift_ofKLR]; rfl
  rw [h1, h2, flip_botMap, hflip_prefixMapKLR]

/-- **The flip commutes with placing a diagram on the last strands.** -/
theorem flip_endStendhal (z : Tc) :
    StendhalAlgebra.flip (endStendhal Q Λ Λc ν ν₀ z) =
      endStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) := by
  obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  have h1 : endStendhal Q Λ Λc ν ν₀ z =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ a) := by
    rw [endStendhal, stendhalLift_apply, ← ha, allOrdersLift_ofKLR]; rfl
  have h2 : endStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.flip z) =
      botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ (hflip a)) := by
    rw [endStendhal, stendhalLift_apply, StendhalAlgebra.flip_val, ← ha,
      StendhalAlgebraAllOrders.flip_ofKLR, allOrdersLift_ofKLR]; rfl
  rw [h1, h2, flip_botMap, hflip_endMapKLR]

/-- The flip fixes the end idempotent `e_L`. -/
theorem flip_endStendhal_one :
    StendhalAlgebra.flip (endStendhal Q Λ Λc ν ν₀ 1) = endStendhal Q Λ Λc ν ν₀ 1 := by
  rw [flip_endStendhal, StendhalAlgebra.flip_one]

/-! ### The flip on `D` -/

variable (Q Λ ν) in
/-- The flip of `T̃^λ` as a `k`-linear map. -/
def flipLin : T →ₗ[k] T where
  toFun := StendhalAlgebra.flip
  map_add' := StendhalAlgebra.flip_add
  map_smul' := StendhalAlgebra.flip_smul

variable (Q Λ Λc ν ν₀) in
/-- **The flip of `D = T̃^λ ⊗ T̃^{(μ,μ*)}`**, on both factors. -/
def flipD : T ⊗[k] Tc →ₗ[k] T ⊗[k] Tc := TensorProduct.map (flipLin Q Λ ν) (flipLin Q Λc ν₀)

theorem flipD_tmul (x : T) (y : Tc) :
    flipD Q Λ Λc ν ν₀ (x ⊗ₜ y) = StendhalAlgebra.flip x ⊗ₜ StendhalAlgebra.flip y := rfl

theorem flipD_flipD (d : T ⊗[k] Tc) : flipD Q Λ Λc ν ν₀ (flipD Q Λ Λc ν ν₀ d) = d := by
  induction d using TensorProduct.inductionOn with
  | tmul x y => rw [flipD_tmul, flipD_tmul, StendhalAlgebra.flip_flip, StendhalAlgebra.flip_flip]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem flipD_mul (d d' : T ⊗[k] Tc) :
    flipD Q Λ Λc ν ν₀ (d * d') = flipD Q Λ Λc ν ν₀ d' * flipD Q Λ Λc ν ν₀ d := by
  induction d using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, mul_add]
  | tmul x y =>
    induction d' using TensorProduct.inductionOn with
    | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, add_mul]
    | tmul x' y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, flipD_tmul, flipD_tmul, flipD_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, StendhalAlgebra.flip_mul, StendhalAlgebra.flip_mul]

/-- **The flip carries the juxtaposition to itself**: `flip (ι d) = ι (flip_D d)`. -/
theorem flip_blockTensor (d : T ⊗[k] Tc) :
    StendhalAlgebra.flip (blockTensor Q Λ Λc ν ν₀ d) =
      blockTensor Q Λ Λc ν ν₀ (flipD Q Λ Λc ν ν₀ d) := by
  induction d using TensorProduct.inductionOn with
  | tmul x y =>
    rw [blockTensor_tmul, StendhalAlgebra.flip_mul, flipD_tmul, blockTensor_tmul,
      flip_prefixStendhal, flip_endStendhal,
      (commute_prefixStendhal_endStendhal Q Λ Λc _ _).eq]
  | add a b ha hb => rw [map_add, StendhalAlgebra.flip_add, ha, hb, map_add, map_add]

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

theorem flipD_blockIdem (c : BaseGen ν₀ ρ₁) :
    flipD Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) = blockIdem Q Λ Λc c := by
  rw [blockIdem, flipD_tmul, StendhalAlgebra.flip_e, StendhalAlgebra.flip_e]

/-! ### The right ideals `1_c D` and the map `⨁_c 1_c D → T̃^{λ⁺} e_L` -/

variable (Q Λ Λc) in
/-- The right ideal `1_c D = {d | 1_c d = d}` of `D`, as a `k`-submodule. -/
def blockRight (c : BaseGen ν₀ ρ₁) : Submodule k (T ⊗[k] Tc) where
  carrier := {d | blockIdem Q Λ Λc c * d = d}
  add_mem' {d d'} hd hd' := by
    change _ * (d + d') = d + d'
    rw [mul_add, hd, hd']
  zero_mem' := mul_zero _
  smul_mem' r d hd := by
    change _ * (r • d) = r • d
    rw [mul_smul_comm, hd]

theorem mem_blockRight {c : BaseGen ν₀ ρ₁} {d : T ⊗[k] Tc} :
    d ∈ blockRight Q Λ Λc c ↔ blockIdem Q Λ Λc c * d = d := Iff.rfl

theorem flipD_mem_blockRight {c : BaseGen ν₀ ρ₁} {d : T ⊗[k] Tc} (hd : d ∈ blockLeft Q Λ Λc c) :
    flipD Q Λ Λc ν ν₀ d ∈ blockRight Q Λ Λc c := by
  rw [mem_blockRight, ← flipD_blockIdem, ← flipD_mul, mem_blockLeft.1 hd]

theorem flipD_mem_blockLeft {c : BaseGen ν₀ ρ₁} {d : T ⊗[k] Tc} (hd : d ∈ blockRight Q Λ Λc c) :
    flipD Q Λ Λc ν ν₀ d ∈ blockLeft Q Λ Λc c := by
  rw [mem_blockLeft, ← flipD_blockIdem (ρ₁ := ρ₁) c, ← flipD_mul, mem_blockRight.1 hd]

variable (Q Λ Λc ν ν₀) in
/-- The flip `D 1_c → 1_c D`. -/
def flipLeftRight (c : BaseGen ν₀ ρ₁) : blockLeft Q Λ Λc c →ₗ[k] blockRight Q Λ Λc c where
  toFun d := ⟨flipD Q Λ Λc ν ν₀ d, flipD_mem_blockRight d.2⟩
  map_add' d d' := Subtype.ext (map_add _ d.1 d'.1)
  map_smul' r d := Subtype.ext (map_smul _ r d.1)

variable (Q Λ Λc ν ν₀) in
/-- The flip `1_c D → D 1_c`. -/
def flipRightLeft (c : BaseGen ν₀ ρ₁) : blockRight Q Λ Λc c →ₗ[k] blockLeft Q Λ Λc c where
  toFun d := ⟨flipD Q Λ Λc ν ν₀ d, flipD_mem_blockLeft d.2⟩
  map_add' d d' := Subtype.ext (map_add _ d.1 d'.1)
  map_smul' r d := Subtype.ext (map_smul _ r d.1)

variable [DecidableEq (EndGen ν₀ ρ₁)]

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **The map** `⨁_c 1_c D → T̃^{λ⁺}`, `(d_c)_c ↦ ∑_c flip(γ_c) ι(d_c)`. -/
def blockSumR : (Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) →ₗ[k] Tp :=
  DFinsupp.lsum ℕ fun c =>
    (LinearMap.mulLeft k (StendhalAlgebra.flip (genElt Q Λ Λc ρ₁ ρ₃ c.1))).comp
      ((blockTensorLin Q Λ Λc ν ν₀).comp (blockRight Q Λ Λc c).subtype)

theorem blockSumR_single (c : BaseGen ν₀ ρ₁) (a : blockRight Q Λ Λc c) :
    blockSumR Q Λ Λc ρ₁ ρ₃ (DFinsupp.single c a) =
      StendhalAlgebra.flip (genElt Q Λ Λc ρ₁ ρ₃ c.1) * blockTensor Q Λ Λc ν ν₀ a := by
  rw [blockSumR, DFinsupp.lsum_single]
  rfl

/-- The flip turns `⨁_c D 1_c` into `⨁_c 1_c D`. -/
def flipSum : (Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) →ₗ[k]
    Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c => flipLeftRight Q Λ Λc ν ν₀ c

/-- The flip turns `⨁_c 1_c D` into `⨁_c D 1_c`. -/
def flipSumInv : (Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) →ₗ[k]
    Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c => flipRightLeft Q Λ Λc ν ν₀ c

omit [DecidableEq (EndGen ν₀ ρ₁)] in
theorem flipSum_flipSumInv (b : Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) :
    flipSum (flipSumInv b) = b := by
  ext c
  simp [flipSum, flipSumInv, flipLeftRight, flipRightLeft, flipD_flipD]

/-- **The flip of `∑_c ι(d_c) γ_c` is `∑_c flip(γ_c) ι(flip_D d_c)`.** -/
theorem flip_blockSum (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    StendhalAlgebra.flip (blockSum Q Λ Λc ρ₁ ρ₃ a) = blockSumR Q Λ Λc ρ₁ ρ₃ (flipSum a) := by
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero, map_zero, map_zero, StendhalAlgebra.flip_zero]
  | ha c b f _ _ ih =>
    have hs : flipSum (DFinsupp.single c b) =
        DFinsupp.single c (flipLeftRight Q Λ Λc ν ν₀ c b) := by
      simp only [flipSum, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]
    rw [map_add, StendhalAlgebra.flip_add, ih, map_add, map_add, blockSum_single, hs,
      blockSumR_single, StendhalAlgebra.flip_mul, flip_blockTensor]
    rfl

/-- **Right freeness, uniqueness**: the map `⨁_c 1_c D → T̃^{λ⁺} e_L` is injective. -/
theorem blockSumR_injective (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Injective (blockSumR Q Λ Λc ρ₁ ρ₃) := by
  intro b b' h
  rw [← flipSum_flipSumInv b, ← flipSum_flipSumInv b', ← flip_blockSum, ← flip_blockSum] at h
  have h' := blockSum_injective hQ hρ₁ hρ₂ hρ₃ (StendhalAlgebra.flip_injective h)
  rw [← flipSum_flipSumInv b, ← flipSum_flipSumInv b', h']

/-- **Right freeness, existence**: `z` is `∑_c flip(γ_c) ι(d_c)` for some `(d_c) ∈ ⨁_c 1_c D`
if and only if `z e_L = z`. -/
theorem mem_range_blockSumR_iff (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (z : Tp) :
    z ∈ LinearMap.range (blockSumR Q Λ Λc ρ₁ ρ₃) ↔ z * endStendhal Q Λ Λc ν ν₀ 1 = z := by
  constructor
  · rintro ⟨b, rfl⟩
    rw [← flipSum_flipSumInv b, ← flip_blockSum, ← flip_endStendhal_one,
      ← StendhalAlgebra.flip_mul, endStendhal_one_mul_blockSum]
  · intro hz
    have hz' : endStendhal Q Λ Λc ν ν₀ 1 * StendhalAlgebra.flip z = StendhalAlgebra.flip z := by
      rw [← flip_endStendhal_one, ← StendhalAlgebra.flip_mul, hz]
    obtain ⟨a, ha⟩ := (mem_range_blockSum_iff hQ hρ₁ hρ₂ hρ₃ _).2 hz'
    refine ⟨flipSum a, ?_⟩
    rw [← flip_blockSum, ha, StendhalAlgebra.flip_flip]

variable (Q Λ Λc) in
/-- Right multiplication by `d ∈ D` on `⨁_c 1_c D`, componentwise. -/
def blockRightMul (d : T ⊗[k] Tc) :
    (Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) →ₗ[k] Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c :=
  DFinsupp.mapRange.linearMap fun c =>
    { toFun := fun b => ⟨b * d, by rw [mem_blockRight, ← mul_assoc, mem_blockRight.1 b.2]⟩
      map_add' := fun b b' => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r b => Subtype.ext (smul_mul_assoc _ _ _) }

/-- **Right `D`-linearity**: `∑_c flip(γ_c) ι(d_c d) = (∑_c flip(γ_c) ι(d_c)) ι(d)`. -/
theorem blockSumR_blockRightMul (d : T ⊗[k] Tc) (b : Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) :
    blockSumR Q Λ Λc ρ₁ ρ₃ (blockRightMul Q Λ Λc d b) =
      blockSumR Q Λ Λc ρ₁ ρ₃ b * blockTensor Q Λ Λc ν ν₀ d := by
  have h : (blockSumR Q Λ Λc ρ₁ ρ₃).comp (blockRightMul Q Λ Λc d) =
      (LinearMap.mulRight k (blockTensor Q Λ Λc ν ν₀ d)).comp (blockSumR Q Λ Λc ρ₁ ρ₃) := by
    refine DFinsupp.lhom_ext' fun c => LinearMap.ext fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DFinsupp.lsingle_apply, blockRightMul,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mulRight_apply]
    rw [blockSumR_single, blockSumR_single, blockTensor_mul, mul_assoc]
  exact LinearMap.congr_fun h b

/-! ### The cut by `e(v)` -/

omit [DecidableEq (EndGen ν₀ ρ₁)] in
/-- `flip(γ_c)` starts at the bottom loading of `c`: `e(v) flip(γ_c)` is `flip(γ_c)` if the
bottom of `c` is `v`, and `0` otherwise. -/
theorem e_mul_flip_genElt (c : BaseGen ν₀ ρ₁) (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hv : IsRedOrdered v) :
    StendhalAlgebra.e v hv * StendhalAlgebra.flip (genElt Q Λ Λc ρ₁ ρ₃ c.1) =
      if c.1.bot = v then StendhalAlgebra.flip (genElt Q Λ Λc ρ₁ ρ₃ c.1) else 0 := by
  rw [← StendhalAlgebra.flip_e v hv, ← StendhalAlgebra.flip_mul, genElt_mul_e]
  split_ifs
  · rfl
  · exact StendhalAlgebra.flip_zero

/-- **The cut by `e(v)`**: `e(v) ∑_c flip(γ_c) ι(d_c)` keeps the summands whose base generator
has bottom `v`. -/
theorem e_mul_blockSumR (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hv : IsRedOrdered v)
    (b : Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c) :
    StendhalAlgebra.e v hv * blockSumR Q Λ Λc ρ₁ ρ₃ b =
      blockSumR Q Λ Λc ρ₁ ρ₃ (b.filter fun c => c.1.bot = v) := by
  induction b using DFinsupp.induction with
  | h0 => rw [map_zero, mul_zero, DFinsupp.filter_zero, map_zero]
  | ha c a f _ _ ih =>
    rw [map_add, mul_add, ih, DFinsupp.filter_add, map_add, DFinsupp.filter_single,
      blockSumR_single, ← mul_assoc, e_mul_flip_genElt c v hv]
    split_ifs
    · rw [blockSumR_single]
    · rw [zero_mul, map_zero]

/-- **`e(v) T̃^{λ⁺} e_L` is right free over `D`** on the `flip(γ_c)` with bottom `v`: every `z`
with `e(v) z = z` and `z e_L = z` is `∑_c flip(γ_c) ι(d_c)` with `d_c = 0` unless the bottom of
`c` is `v`. -/
theorem exists_blockSumR_of_mem (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (v : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (hv : IsRedOrdered v) (z : Tp)
    (hvz : StendhalAlgebra.e v hv * z = z) (hz : z * endStendhal Q Λ Λc ν ν₀ 1 = z) :
    ∃ b : Π₀ c : BaseGen ν₀ ρ₁, blockRight Q Λ Λc c,
      (∀ c, c.1.bot ≠ v → b c = 0) ∧ blockSumR Q Λ Λc ρ₁ ρ₃ b = z := by
  obtain ⟨b, hb⟩ := (mem_range_blockSumR_iff hQ hρ₁ hρ₂ hρ₃ z).2 hz
  have hf : b.filter (fun c => c.1.bot = v) = b := by
    apply blockSumR_injective hQ hρ₁ hρ₂ hρ₃
    rw [← e_mul_blockSumR v hv, hb, hvz]
  refine ⟨b, fun c hc => ?_, hb⟩
  rw [← hf, DFinsupp.filter_apply_neg b hc]

end Categorification.Stendhal.CupCap
