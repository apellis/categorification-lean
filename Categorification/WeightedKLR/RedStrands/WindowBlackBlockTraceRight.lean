/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockSwap

/-!
# The trace `c` is right `D`-linear

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the induction–coinduction identity (IC),
step 2, at `ℓ = 0`. Let `A = T̃^{λ⁺}` with `λ⁺ = (μ, μ*)` the two red strands of the window,
`D = T̃^λ ⊗ T̃^{(μ,μ*)}`, `ι : D → e_L A e_L` the juxtaposition with the block of `ν` first
(`blockTensor`) and `ι_R : D_R = T̃^{(μ,μ*)} ⊗ T̃^λ → e_R A e_R` the one with it last
(`blockTensorR`). The trace `c = blockTrace : A → D` of `WindowBlackBlockTrace` satisfies

  `c(z ι_R(d')) = c(z) · swap(d')`  for `z ∈ A`, `d' ∈ D_R` (`blockTrace_mul_blockTensorR`),

with `swap : D_R ≅ D` the exchange of the tensor factors. Together with
`blockTrace_blockTensor_mul` this makes `c` a map of `D`-bimodules from `e_L A e_R` to `D`, with
the canonical identification of the two copies of `D`.

Proof. Write `F̄` for the image in `A` of the lower step `F_{m-1}` of the Mackey filtration
(`lowerImage`); `c` vanishes on `F̄` (`blockTrace_botMap_eq_zero`), and `F̄` is stable under
`ι(D)` on the left and `ι_R(D_R)` on the right. Let `ψ = ψ_{w_L}` be the image of the diagram of
the longest block crossing.

* `e_L z ≡ ι(c(z)) ψ` modulo `F̄` (`endStendhal_one_mul_sub_mem`): the generators `γ_c` of the
  left coset decomposition with fewer than `m` crossing strands lie in `F̄`, and the ones with
  `m` crossing strands are `ι(1_c) ψ` modulo `F̄`.
* `ψ ι_R(d') ≡ ι(swap d') ψ` modulo `F̄` (`botMap_ψD_mul_blockTensorR_sub_mem`).
* `c(ψ) = 1` (`blockTrace_botMap_ψD`).

## Main definitions

* `CupCap.lowerImage`: the image `F̄` of `F_{m-1}` in `T̃^{λ⁺}`.

## Main results

* `CupCap.blockTrace_mul_blockTensorR`: right `D`-linearity of the trace.
* `CupCap.endStendhal_one_mul_sub_mem`, `CupCap.botMap_ψD_mul_blockTensorR_sub_mem`,
  `CupCap.blockTrace_botMap_ψD`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight 0 ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (stendhalWeight (0 + 2) (ν + ν₀))
local notation "β" => botMap k Q Λ Λc 0 le_rfl ν ν₀
local notation "hM" => m_add_N_end (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)
local notation "hK" => N_add_m_front (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)
local notation "L" => mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
  (stendhalWeight (0 + 2) (ν + ν₀)) m N m

/-! ### The image of `F_{m-1}` -/

variable (k Q Λ Λc ν ν₀) in
/-- The image `F̄` in `T̃^{λ⁺}` of the lower step `F_{m-1}` of the Mackey filtration for the top
blocks `(m, N)` and the bottom blocks `(N, m)`. -/
def lowerImage : Submodule k Tp := Submodule.map (β).toLinearMap L

theorem mem_lowerImage {z : Tp} : z ∈ lowerImage k Q Λ Λc ν ν₀ ↔ ∃ y ∈ L, β y = z := by
  unfold lowerImage
  rw [Submodule.mem_map]
  simp only [AlgHom.toLinearMap_apply]

theorem botMap_mem_lowerImage {y : Rp} (hy : y ∈ L) : β y ∈ lowerImage k Q Λ Λc ν ν₀ :=
  mem_lowerImage.2 ⟨y, hy, rfl⟩

private theorem prefixStendhal_of_val' (z : T)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight 0 ν))
    (ha : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λ ν a) :
    prefixStendhal Q Λ Λc ν ν₀ z = β (prefixMapKLR Q Λ Λc ν ν₀ a) := by
  rw [prefixStendhal, stendhalLift_apply, ha, allOrdersLift_ofKLR]
  rfl

/-- `F̄` is stable under `ι(D)` on the left. -/
theorem blockTensor_mul_mem_lowerImage (hQ : KLRSymm Q) (x : T ⊗[k] Tc) {z : Tp}
    (hz : z ∈ lowerImage k Q Λ Λc ν ν₀) :
    blockTensor Q Λ Λc ν ν₀ x * z ∈ lowerImage k Q Λ Λc ν ν₀ := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, add_mul]; exact add_mem hx hx'
  | tmul a' y' =>
    obtain ⟨y, hy, rfl⟩ := mem_lowerImage.1 hz
    obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective a'.val
    obtain ⟨b, hb⟩ := StendhalAlgebraAllOrders.ofKLR_surjective y'.val
    rw [blockTensor_tmul, prefixStendhal_of_val' a' a ha.symm, endStendhal_of_val y' b hb.symm,
      ← map_mul, ← map_mul, mul_assoc]
    exact botMap_mem_lowerImage (prefixMapKLR_mul_mem hQ a (endMapKLR_mul_mem hQ b hy))

/-- `F̄` is stable under `ι_R(D_R)` on the right. -/
theorem mul_blockTensorR_mem_lowerImage (hQ : KLRSymm Q) (d' : Tc ⊗[k] T) {z : Tp}
    (hz : z ∈ lowerImage k Q Λ Λc ν ν₀) :
    z * blockTensorR Q Λ Λc ν ν₀ d' ∈ lowerImage k Q Λ Λc ν ν₀ := by
  induction d' using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, mul_add]; exact add_mem hx hx'
  | tmul y' a' =>
    obtain ⟨y, hy, rfl⟩ := mem_lowerImage.1 hz
    obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective a'.val
    obtain ⟨b, hb⟩ := StendhalAlgebraAllOrders.ofKLR_surjective y'.val
    rw [blockTensorR_tmul, frontStendhal_of_val y' b hb.symm, suffixStendhal_of_val a' a ha.symm,
      ← map_mul, ← map_mul, ← mul_assoc]
    exact botMap_mem_lowerImage (mul_suffixMapKLR_mem hQ a (mul_frontMapKLR_mem hQ b hy))

/-- **The longest block crossing intertwines `ι_R` and `ι` modulo `F̄`**:
`ψ_{w_L} ι_R(d') - ι(swap d') ψ_{w_L} ∈ F̄`. -/
theorem botMap_ψD_mul_blockTensorR_sub_mem (hQ : KLRSymm Q) {d : Perm (Fin M)}
    (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m) (d' : Tc ⊗[k] T) :
    β (ψw (canWord M d)) * blockTensorR Q Λ Λc ν ν₀ d' -
      blockTensor Q Λ Λc ν ν₀ (TensorProduct.comm k Tc T d') * β (ψw (canWord M d)) ∈
        lowerImage k Q Λ Λc ν ν₀ := by
  induction d' using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    have := add_mem hx hx'
    rw [map_add, map_add, map_add]
    convert this using 1
    simp only [mul_add, add_mul]; abel
  | tmul y' a' =>
    obtain ⟨a, ha⟩ := StendhalAlgebraAllOrders.ofKLR_surjective a'.val
    obtain ⟨b, hb⟩ := StendhalAlgebraAllOrders.ofKLR_surjective y'.val
    rw [blockTensorR_tmul, TensorProduct.comm_tmul, blockTensor_tmul,
      frontStendhal_of_val y' b hb.symm, suffixStendhal_of_val a' a ha.symm,
      prefixStendhal_of_val' a' a ha.symm, endStendhal_of_val y' b hb.symm, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, ← map_sub]
    exact botMap_mem_lowerImage (ψD_mul_frontSuffix_sub_mem hQ hd hcd a b)

/-! ### The generators modulo `F̄` -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}

theorem mackeyFilt_le_mackeyLower_of_lt {c c' : ℕ} (h : c' < c) :
    mackeyFilt k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (stendhalWeight (0 + 2) (ν + ν₀))
        m N c' ≤
      mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (stendhalWeight (0 + 2) (ν + ν₀))
        m N c := by
  cases c with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ c => rw [mackeyLower_succ]; exact mackeyFilt_mono (Nat.lt_succ_iff.1 h)

/-- A generator with fewer than `m` crossing strands lies in `F̄`. -/
theorem genElt_mem_lowerImage (hQ : KLRSymm Q)
    (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
      wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)
    (g : EndGen ν₀ ρ₁) (hg : crossCount m N g.1.2.2.1 < m) :
    genElt Q Λ Λc ρ₁ ρ₃ g ∈ lowerImage k Q Λ Λc ν ν₀ := by
  have hMN := hM
  have h1 : (ψw (ρ₃ g.1.2.2.1) * e g.bot : Rp) ∈ L := by
    have h := mem_mackeyFilt (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (n := m) (n'' := N) (hρ₃ g.1.2.2.1).1.1 (c := crossCount m N g.1.2.2.1)
      (fun v hv => by
        have := crossCount_le_of_mem_subProds (n := m) (n'' := N) (by omega) (by omega)
          (hρ₃ g.1.2.2.1).1 hv
        rwa [(hρ₃ g.1.2.2.1).2] at this) 1 g.bot
    rw [map_one, mul_one] at h
    exact mackeyFilt_le_mackeyLower_of_lt hg h
  rw [genElt, genKLR, mul_assoc, mul_assoc]
  exact botMap_mem_lowerImage (prefixMapKLR_mul_mem hQ _ (endMapKLR_mul_mem hQ _ h1))

/-- Changing the reduced word of `w_L` changes `ψ_{w_L} e(i)` by an element of `F_{m-1}`. -/
theorem ψw_mul_e_sub_mem (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))
      (ρ₃ w) ∧ wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (w : Seq (stendhalWeight (0 + 2) (ν + ν₀))) :
    (ψw (ρ₃ d) * e w : Rp) - ψw (canWord M d) * e w ∈ L := by
  have hMN := hM
  have hE := braidEquiv_of_isReduced (hρ₃ d).1 (isReduced_canWord M d)
    (by rw [(hρ₃ d).2, wordProd_canWord])
  have h := braidEquiv_sub_mem_lowSpan (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
    hE (hρ₃ d).1.1 1 w
  rw [map_one, mul_one, mul_one] at h
  have hS : ∀ v ∈ subProds M (ρ₃ d), crossCount m N v ≤ crossCount m N d := fun v hv => by
    have := crossCount_le_of_mem_subProds (n := m) (n'' := N) (by omega) (by omega)
      (hρ₃ d).1 hv
    rwa [(hρ₃ d).2] at this
  have hlen : (ρ₃ d).length - 2 ≤ length M d := by rw [(hρ₃ d).1.2, (hρ₃ d).2]; omega
  have hle := lowSpan_le_mackeyLower (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) hM hK
    hd hS hlen
  rw [hcd] at hle
  exact hle h

/-- **A generator with `m` crossing strands** is `ι(1_c) ψ_{w_L}` modulo `F̄`. -/
theorem genElt_sub_mem_lowerImage
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
      wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (c : BaseGen ν₀ ρ₁) (hc : crossCount m N c.1.1.2.2.1 = m) :
    genElt Q Λ Λc ρ₁ ρ₃ c.1 - blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) *
      β (ψw (canWord M d)) ∈ lowerImage k Q Λ Λc ν ν₀ := by
  have hu : c.1.1.2.2.1 = d := eq_of_crossCount_eq hM hK c.1.1.2.2.2 hc hd hcd
  set i := c.1.1.1.1.1
  set j := c.1.1.2.1
  have hx : c.1.1.1.1 = (i, 1, 0) := Prod.ext rfl c.2
  have hbot : c.1.bot = d⁻¹ • endSeq i j := by
    change c.1.1.2.2.1⁻¹ • endSeq c.1.1.1.1.1 c.1.1.2.1 = _
    rw [hu]
  have hgen : genKLR Q Λ Λc ρ₁ ρ₃ c.1 =
      e (endSeq i j) * ψw (ρ₃ d) * e (d⁻¹ • endSeq i j) := by
    rw [genKLR, hx, topElt_base hρ₁, prefixMapKLR_e_mul_endMapKLR_e, hu, hbot]
    rfl
  have hidem : blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) = β (e (endSeq i j)) := by
    rw [blockIdem, blockTensor_tmul, prefixStendhal_of_val' _ (e i) rfl, endStendhal_e,
      ← map_mul, prefixMapKLR_e_mul_endMapKLR_e]
    rfl
  have hψ : (ψw (canWord M d) : Rp) * e (d⁻¹ • endSeq i j) = e (endSeq i j) * ψw (canWord M d) := by
    rw [ψD_mul_e (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (d := d),
      smul_inv_smul]
  rw [genElt, hgen, hidem, ← map_mul, ← map_sub]
  refine botMap_mem_lowerImage ?_
  have h := mackeyLower_e_mul (endSeq i j)
    (ψw_mul_e_sub_mem (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) hρ₃ hd hcd (d⁻¹ • endSeq i j))
  convert h using 1
  rw [mul_sub, hψ, ← mul_assoc, ← mul_assoc, e_mul_self, mul_assoc]

/-! ### Idempotents of `T̃` -/

section Idem

variable {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}

private theorem stendhalE_mul_self (s : Seq (stendhalWeight ℓ' ν')) (hs : IsRedOrdered s) :
    (StendhalAlgebra.e s hs * StendhalAlgebra.e s hs : StendhalAlgebra k Q Λ' ν') =
      StendhalAlgebra.e s hs := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.e s = _
  rw [StendhalAlgebraAllOrders.e_mul_e, ite_eq_left rfl]
  rfl

private theorem sum_stendhalE_eq_one :
    ∑ s : {s : Seq (stendhalWeight ℓ' ν') // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 =
      (1 : StendhalAlgebra k Q Λ' ν') := by
  classical
  apply Subtype.ext
  rw [KLR.Corner.val_sum, KLR.Corner.val_one]
  change (∑ s : {s : Seq (stendhalWeight ℓ' ν') // IsRedOrdered s},
    StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν'
  exact (Finset.sum_subtype _ (fun s => by simp) _).symm

end Idem

/-! ### The trace modulo `F̄` -/

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  [DecidableEq (EndGen ν₀ ρ₁)]

section Trace

variable (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

/-- `c` vanishes on `F̄`. -/
theorem blockTrace_eq_zero_of_mem_lowerImage {z : Tp} (hz : z ∈ lowerImage k Q Λ Λc ν ν₀) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z = 0 := by
  obtain ⟨y, hy, rfl⟩ := mem_lowerImage.1 hz
  exact blockTrace_botMap_eq_zero hQ hρ₁ hρ₂ hρ₃ y hy

/-- `c(z)` only depends on `e_L z`. -/
theorem blockTrace_endStendhal_one_mul (z : Tp) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (endStendhal Q Λ Λc ν ν₀ 1 * z) =
      blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z := by
  have h : endProj Q Λ Λc ν ν₀ (endStendhal Q Λ Λc ν ν₀ 1 * z) = endProj Q Λ Λc ν ν₀ z := by
    apply Subtype.ext
    rw [endProj_apply, endProj_apply, ← mul_assoc, endStendhal_one_mul_self]
  simp only [blockTrace, LinearMap.coe_comp, Function.comp_apply]
  rw [h]

/-- **`e_L z ≡ ι(c(z)) ψ_{w_L}` modulo `F̄`.** -/
theorem endStendhal_one_mul_sub_mem {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (z : Tp) :
    endStendhal Q Λ Λc ν ν₀ 1 * z - blockTensor Q Λ Λc ν ν₀
        (blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z) * β (ψw (canWord M d)) ∈
      lowerImage k Q Λ Λc ν ν₀ := by
  have hMN := hM
  set a := (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm (endProj Q Λ Λc ν ν₀ z)
  have ha : endStendhal Q Λ Λc ν ν₀ 1 * z = blockSum Q Λ Λc ρ₁ ρ₃ a := by
    rw [← blockSumEquiv_apply hQ hρ₁ hρ₂ hρ₃, LinearEquiv.apply_symm_apply, endProj_apply]
  have hc : blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z = traceSum Q Λ Λc ρ₁ a := rfl
  rw [ha, hc]
  clear ha hc
  clear_value a
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha c x f _ _ ih =>
    rw [map_add, map_add, map_add, add_mul]
    have hs : blockSum Q Λ Λc ρ₁ ρ₃ (DFinsupp.single c x) -
        blockTensor Q Λ Λc ν ν₀ (traceSum Q Λ Λc ρ₁ (DFinsupp.single c x)) *
          β (ψw (canWord M d)) ∈ lowerImage k Q Λ Λc ν ν₀ := by
      rw [blockSum_single, traceSum_single]
      by_cases hfull : crossCount m N c.1.1.2.2.1 = m
      · rw [ite_eq_left hfull]
        have hx : blockTensor Q Λ Λc ν ν₀ (x : T ⊗[k] Tc) =
            blockTensor Q Λ Λc ν ν₀ x * blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) := by
          rw [← map_mul, mem_blockLeft.1 x.2]
        have h := blockTensor_mul_mem_lowerImage hQ (x : T ⊗[k] Tc)
          (genElt_sub_mem_lowerImage hρ₁ hρ₃ hd hcd c hfull)
        convert h using 1
        rw [mul_sub, ← mul_assoc, ← hx]
      · rw [ite_eq_right hfull, map_zero, zero_mul, sub_zero]
        have hlt : crossCount m N c.1.1.2.2.1 < m :=
          lt_of_le_of_ne (crossCount_le _ (by omega)) hfull
        exact blockTensor_mul_mem_lowerImage hQ _ (genElt_mem_lowerImage hQ hρ₃ c.1 hlt)
    convert add_mem hs ih using 1
    abel

/-- The base generator `(e(i), j, w_L)`. -/
def fullGen {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (i : {i : Seq (stendhalWeight 0 ν) // IsRedOrdered i})
    (j : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j}) : BaseGen ν₀ ρ₁ :=
  ⟨⟨(⟨(i.1, 1, 0), isTopTerm_base hρ₁ i.2⟩, j.1, ⟨d, hd.1⟩), j.2, by
    change IsRedOrdered (d⁻¹ • endSeq i.1 j.1)
    rw [← smul_frontSeq_eq_endSeq hd hcd, inv_smul_smul]
    exact (isRedOrdered_frontSeq _ _).2 ⟨i.2, j.2⟩⟩, rfl⟩

omit [DecidableEq (EndGen ν₀ ρ₁)] hQ hρ₂ hρ₃ in
theorem blockTensor_blockIdem_mul_genElt (c : BaseGen ν₀ ρ₁) :
    blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) * genElt Q Λ Λc ρ₁ ρ₃ c.1 =
      genElt Q Λ Λc ρ₁ ρ₃ c.1 := by
  rw [blockIdem, blockTensor_tmul, mul_assoc, endStendhal_e_mul_genElt c.1,
    prefixStendhal_e_mul_genElt_base hρ₁ c c.1.1.1.2.1]

/-- **`c(ψ_{w_L}) = 1`.** -/
theorem blockTrace_botMap_ψD {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (β (ψw (canWord M d))) = 1 := by
  classical
  have hterm : ∀ (i : {i : Seq (stendhalWeight 0 ν) // IsRedOrdered i})
      (j : {j : Seq (stendhalWeight 2 ν₀) // IsRedOrdered j}),
      blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (blockTensor Q Λ Λc ν ν₀
        (StendhalAlgebra.e i.1 i.2 ⊗ₜ StendhalAlgebra.e j.1 j.2) * β (ψw (canWord M d))) =
        StendhalAlgebra.e i.1 i.2 ⊗ₜ StendhalAlgebra.e j.1 j.2 := by
    intro i j
    set c := fullGen (ρ₁ := ρ₁) hρ₁ hd hcd i j
    have hc : crossCount m N c.1.1.2.2.1 = m := hcd
    have h0 := blockTrace_eq_zero_of_mem_lowerImage hQ hρ₁ hρ₂ hρ₃
      (genElt_sub_mem_lowerImage (Λ := Λ) (Λc := Λc) hρ₁ hρ₃ hd hcd c hc)
    rw [map_sub, sub_eq_zero] at h0
    change _ = blockIdem Q Λ Λc c
    change blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃
      (blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) * _) = _
    rw [← h0]
    have hs : genElt Q Λ Λc ρ₁ ρ₃ c.1 =
        blockSum Q Λ Λc ρ₁ ρ₃ (DFinsupp.single c ⟨blockIdem Q Λ Λc c, by
          rw [mem_blockLeft, blockIdem, Algebra.TensorProduct.tmul_mul_tmul,
            stendhalE_mul_self, stendhalE_mul_self]⟩) := by
      rw [blockSum_single]
      exact (blockTensor_blockIdem_mul_genElt hρ₁ c).symm
    rw [hs, blockTrace_blockSum, traceSum_single, ite_eq_left hc]
  rw [← blockTrace_endStendhal_one_mul, ← blockTensor_one, Algebra.TensorProduct.one_def,
    ← sum_stendhalE_eq_one (Q := Q) (Λ' := Λ) (ν' := ν),
    ← sum_stendhalE_eq_one (Q := Q) (Λ' := Λc) (ν' := ν₀),
    TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, Finset.sum_mul, hterm]

/-- **The trace is right `D`-linear**: `c(z ι_R(d')) = c(z) · swap(d')` for `d' ∈ D_R`, with
`swap : T̃^{(μ,μ*)} ⊗ T̃^λ ≅ T̃^λ ⊗ T̃^{(μ,μ*)}` the exchange of the factors. -/
theorem blockTrace_mul_blockTensorR (z : Tp) (d' : Tc ⊗[k] T) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (z * blockTensorR Q Λ Λc ν ν₀ d') =
      blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z * TensorProduct.comm k Tc T d' := by
  have hMN := hM
  obtain ⟨d, hd, hcd⟩ := (exists_isDoubleShuffle_iff hM hK m).2 ⟨by omega, le_rfl, le_rfl⟩
  set C := blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃
  set ψ : Tp := β (ψw (canWord M d))
  have h1 := mul_blockTensorR_mem_lowerImage hQ d'
    (endStendhal_one_mul_sub_mem hQ hρ₁ hρ₂ hρ₃ hd hcd z)
  have h2 := blockTensor_mul_mem_lowerImage hQ (C z)
    (botMap_ψD_mul_blockTensorR_sub_mem hQ hd hcd d')
  have h3 := blockTrace_eq_zero_of_mem_lowerImage hQ hρ₁ hρ₂ hρ₃ (add_mem h1 h2)
  have e1 : (endStendhal Q Λ Λc ν ν₀ 1 * z - blockTensor Q Λ Λc ν ν₀ (C z) * ψ) *
        blockTensorR Q Λ Λc ν ν₀ d' +
      blockTensor Q Λ Λc ν ν₀ (C z) * (ψ * blockTensorR Q Λ Λc ν ν₀ d' -
        blockTensor Q Λ Λc ν ν₀ (TensorProduct.comm k Tc T d') * ψ) =
      endStendhal Q Λ Λc ν ν₀ 1 * (z * blockTensorR Q Λ Λc ν ν₀ d') -
        blockTensor Q Λ Λc ν ν₀ (C z) *
          (blockTensor Q Λ Λc ν ν₀ (TensorProduct.comm k Tc T d') * ψ) := by
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  rw [e1, map_sub, sub_eq_zero, blockTrace_endStendhal_one_mul, ← mul_assoc,
    ← map_mul] at h3
  rw [h3, blockTrace_blockTensor_mul, blockTrace_botMap_ψD hQ hρ₁ hρ₂ hρ₃ hd hcd, mul_one]

end Trace

end Categorification.Stendhal.CupCap
