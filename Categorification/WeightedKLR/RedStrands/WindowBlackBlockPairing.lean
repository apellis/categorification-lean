/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockTraceRight
import Categorification.TypeA.BlockSwapLength

/-!
# The matrix of the trace pairing

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the induction–coinduction identity (IC),
step 3, at `ℓ = 0`. Let `A = T̃^{λ⁺}`, let `γ_c` (`c = (e(i), j, u)`, `u` a shuffle for the top
blocks `(m, N)`) be the left `D`-basis of `e_L A` and `flip(γ_{c'})` (`c' = (i', j', u')`, `u'` a
shuffle for the top blocks `(N, m)`) the right `D_R`-basis of `A e_R`. The entries of the matrix
of the trace pairing are

  `c(γ_c flip(γ_{c'})) = 1_c` if `c` and `c'` have the same bottom and `u u'⁻¹ = w_L`,
  and `0` otherwise, provided `ℓ(u) + ℓ(u') ≤ ℓ(w_L)`

(`blockTrace_genElt_mul_flip_genEltF`). The product is the image of the diagram on the word
`ρ₃(u) ρ₃(u')^rev` of length `ℓ(u) + ℓ(u')`, and a word of length at most `ℓ(w_L)` is
`[product = w_L] ψ_{w_L}` modulo the lower step `F_{m-1}` of the Mackey filtration
(`ψw_mul_e_sub_ite_mem`): a shorter subword product, or a product of length `ℓ(w_L)` other than
`w_L`, has fewer than `m` crossing strands (`eq_of_crossCount_eq_of_length_le`).

Since `ℓ(w_L u') + ℓ(u') = ℓ(w_L)` (`length_mul_add_length`), ordering the generators by `ℓ(u)`
makes this matrix unitriangular; this is used in `WindowBlackBlockIC`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.

## Main results

* `CupCap.ψw_mul_e_sub_ite_mem`: words of length at most `ℓ(w_L)` modulo `F_{m-1}`.
* `CupCap.genElt_mul_flip_genEltF`: the product `γ_c flip(γ_{c'})` as one diagram.
* `CupCap.blockTrace_genElt_mul_flip_genEltF`: the matrix entries.
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

/-! ### Words of length at most `ℓ(w_L)` -/

/-- **A word of length at most `ℓ(w_L)`** is `ψ_{w_L}` modulo `F_{m-1}` if its product is `w_L`,
and lies in `F_{m-1}` otherwise. -/
theorem ψw_mul_e_sub_ite_mem {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) {α : List ℕ} (hα : ValidWord M α)
    (hl : α.length ≤ length M d) (w : Seq (stendhalWeight (0 + 2) (ν + ν₀))) :
    (ψw α * e w : Rp) - (if wordProd M α = d then ψw (canWord M d) * e w else 0) ∈ L := by
  have hMN := hM
  by_cases hp : wordProd M α = d
  · rw [ite_eq_left hp]
    have hred : IsReduced M α :=
      ⟨hα, le_antisymm (by rw [hp]; exact hl) (length_wordProd_le hα)⟩
    have hE := braidEquiv_of_isReduced hred (isReduced_canWord M d)
      (by rw [hp, wordProd_canWord])
    have h := braidEquiv_sub_mem_lowSpan (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      hE hα 1 w
    rw [map_one, mul_one, mul_one] at h
    have hS : ∀ v ∈ subProds M α, crossCount m N v ≤ crossCount m N d := fun v _ => by
      rw [hcd]; exact crossCount_le _ (by omega)
    have hlen : α.length - 2 ≤ length M d := by omega
    have hle := lowSpan_le_mackeyLower (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      hM hK hd hS hlen
    rw [hcd] at hle
    exact hle h
  · rw [ite_eq_right hp, sub_zero]
    have hlt : ∀ v ∈ subProds M α, crossCount m N v < m := by
      intro v hv
      refine lt_of_le_of_ne (crossCount_le _ (by omega)) fun hc => ?_
      obtain ⟨δ, hδ, rfl⟩ := hv
      have h1 := hd.length_le_of_crossCount_eq hM hK (hc.trans hcd.symm)
      have h2 := length_wordProd_le (hα.sublist hδ)
      have h3 := hδ.length_le
      have hδα : δ = α := hδ.eq_of_length (by omega)
      subst hδα
      exact hp (eq_of_crossCount_eq_of_length_le hM hK hd hc (by omega))
    have hm0 : 0 < m := by have := hlt 1 (one_mem_subProds α); omega
    have h := mem_mackeyFilt (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (n := m) (n'' := N) hα (c := m - 1) (fun v hv => by have := hlt v hv; omega) 1 w
    rw [map_one, mul_one] at h
    exact mackeyFilt_le_mackeyLower_of_lt (by omega) h

/-! ### The product `γ_c flip(γ_{c'})` -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}

private theorem prefixStendhal_of_val'' (z : T)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight 0 ν))
    (ha : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λ ν a) :
    prefixStendhal Q Λ Λc ν ν₀ z = β (prefixMapKLR Q Λ Λc ν ν₀ a) := by
  rw [prefixStendhal, stendhalLift_apply, ha, allOrdersLift_ofKLR]
  rfl

/-- `ι(1_c)` is the image of the idempotent `e(i j)` at the top of `γ_c`. -/
theorem blockTensor_blockIdem (c : BaseGen ν₀ ρ₁) :
    blockTensor Q Λ Λc ν ν₀ (blockIdem Q Λ Λc c) = β (e (endSeq c.1.1.1.1.1 c.1.1.2.1)) := by
  rw [blockIdem, blockTensor_tmul, prefixStendhal_of_val'' _ (e c.1.1.1.1.1) rfl, endStendhal_e,
    ← map_mul, prefixMapKLR_e_mul_endMapKLR_e]
  rfl

/-- The diagram of a base generator `c = (e(i), j, u)`: `γ_c = e(i j) ψ_{ρ₃(u)} e(u⁻¹(i j))`. -/
theorem genElt_base_eq
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (c : BaseGen ν₀ ρ₁) :
    genElt Q Λ Λc ρ₁ ρ₃ c.1 =
      β (e (endSeq c.1.1.1.1.1 c.1.1.2.1) * ψw (ρ₃ c.1.1.2.2.1) * e c.1.bot) := by
  have hx : c.1.1.1.1 = (c.1.1.1.1.1, 1, 0) := Prod.ext rfl c.2
  rw [genElt, genKLR, hx, topElt_base hρ₁, prefixMapKLR_e_mul_endMapKLR_e]
  rfl

/-- The flip of a front generator `c' = (i', j', u')`:
`flip(γ_{c'}) = e(u'⁻¹(j' i')) ψ_{ρ₃(u')^rev} e(j' i')`. -/
theorem flip_genEltF_eq (c' : FrontGen 0 ν ν₀) :
    StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') =
      β (e c'.bot * ψw (ρ₃ c'.1.2.2.1).reverse * e (frontSeq c'.1.1 c'.1.2.1)) := by
  rw [genEltF, flip_botMap_front, genKLRF, hflip_mul, hflip_mul, hflip_e, hflip_e, hflip_ψw,
    mul_assoc]

/-- **The product `γ_c flip(γ_{c'})`** is the image of `e(i j) ψ_{ρ₃(u) ρ₃(u')^rev} e(j' i')` if
the two generators have the same bottom, and `0` otherwise. -/
theorem genElt_mul_flip_genEltF
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
      wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)
    (c : BaseGen ν₀ ρ₁) (c' : FrontGen 0 ν ν₀) :
    genElt Q Λ Λc ρ₁ ρ₃ c.1 * StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') =
      if c.1.bot = c'.bot then
        β (e (endSeq c.1.1.1.1.1 c.1.1.2.1) *
          (ψw (ρ₃ c.1.1.2.2.1 ++ (ρ₃ c'.1.2.2.1).reverse) * e (frontSeq c'.1.1 c'.1.2.1)))
      else 0 := by
  rw [genElt_base_eq hρ₁, flip_genEltF_eq, ← map_mul]
  simp only [mul_assoc]
  by_cases hb : c.1.bot = c'.bot
  · rw [ite_eq_left hb, hb]
    have h1 : (e c'.bot * ψw (ρ₃ c'.1.2.2.1).reverse : Rp) =
        ψw (ρ₃ c'.1.2.2.1).reverse * e (frontSeq c'.1.1 c'.1.2.1) := by
      rw [e_mul_ψw, wordProd_reverse, inv_inv, (hρ₃ _).2, FrontGen.bot, smul_inv_smul]
    rw [← mul_assoc (e c'.bot) (e c'.bot), e_mul_e, ite_eq_left rfl, ← mul_assoc (e c'.bot),
      h1, mul_assoc, e_mul_e, ite_eq_left rfl, ψw_append, mul_assoc]
  · rw [ite_eq_right hb, ← mul_assoc (e c.1.bot) (e c'.bot), e_mul_e, ite_eq_right hb,
      zero_mul, mul_zero, mul_zero, map_zero]

/-! ### The matrix entries -/

variable [DecidableEq (EndGen ν₀ ρ₁)]

section Matrix

variable (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

/-- **The matrix of the trace pairing** (Webster, proof of Lemma 7.19, (IC), step 3): if
`ℓ(u) + ℓ(u') ≤ ℓ(w_L)`, then `c(γ_c flip(γ_{c'}))` is `1_c` when `c` and `c'` have the same
bottom and `u u'⁻¹ = w_L`, and `0` otherwise. -/
theorem blockTrace_genElt_mul_flip_genEltF {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (c : BaseGen ν₀ ρ₁) (c' : FrontGen 0 ν ν₀)
    (hl : length M c.1.1.2.2.1 + length M c'.1.2.2.1 ≤ length M d) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃
        (genElt Q Λ Λc ρ₁ ρ₃ c.1 * StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c')) =
      if c.1.bot = c'.bot ∧ c.1.1.2.2.1 * (c'.1.2.2.1)⁻¹ = d then blockIdem Q Λ Λc c
      else 0 := by
  rw [genElt_mul_flip_genEltF hρ₁ hρ₃]
  by_cases hb : c.1.bot = c'.bot
  · rw [ite_eq_left hb]
    set u := c.1.1.2.2.1
    set u' := c'.1.2.2.1
    set α := ρ₃ u ++ (ρ₃ u').reverse
    set a := endSeq c.1.1.1.1.1 c.1.1.2.1
    set f := frontSeq c'.1.1 c'.1.2.1
    have hα : ValidWord M α := by
      rw [validWord_append, validWord_reverse]
      exact ⟨(hρ₃ u).1.1, (hρ₃ u').1.1⟩
    have hlen : α.length ≤ length M d := by
      rw [List.length_append, List.length_reverse, (hρ₃ u).1.2, (hρ₃ u').1.2, (hρ₃ u).2,
        (hρ₃ u').2]
      exact hl
    have hprod : wordProd M α = u * u'⁻¹ := by
      rw [wordProd_append, wordProd_reverse, (hρ₃ u).2, (hρ₃ u').2]
    have h0 := blockTrace_eq_zero_of_mem_lowerImage (Λ := Λ) (Λc := Λc) hQ hρ₁ hρ₂ hρ₃
      (botMap_mem_lowerImage (mackeyLower_e_mul a (ψw_mul_e_sub_ite_mem hd hcd hα hlen f)))
    rw [mul_sub, map_sub, map_sub, sub_eq_zero, hprod] at h0
    rw [h0]
    by_cases hπ : u * u'⁻¹ = d
    · rw [ite_eq_left hπ, ite_eq_left ⟨hb, hπ⟩]
      have hf : d • f = a := by
        have h1 : u • c.1.bot = a := smul_bot c.1
        rw [hb, FrontGen.bot, smul_smul, hπ] at h1
        exact h1
      rw [ψD_mul_e (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (d := d), hf,
        ← mul_assoc, e_mul_e, ite_eq_left rfl, map_mul, ← blockTensor_blockIdem,
        blockTrace_blockTensor_mul, blockTrace_botMap_ψD hQ hρ₁ hρ₂ hρ₃ hd hcd, mul_one]
    · rw [ite_eq_right hπ, ite_eq_right fun h => hπ h.2, mul_zero, map_zero, map_zero]
  · rw [ite_eq_right hb, ite_eq_right fun h => hb h.1, map_zero]

end Matrix

end Categorification.Stendhal.CupCap
