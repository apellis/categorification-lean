/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Free

/-!
# Dots and crossings in the flag 2-category: divided differences

Khovanov–Lauda III, arXiv:0807.3250v1, §5.2.3 (TeX `sln-2008-ArXiv.tex`, "Bimodules
`H_{k^{\ii}}`", eq. (5.37)) and §6.1.2 (Definition 6.2, eqs. (6.6)–(6.8)).

KL III define `Γ_N` of an upward crossing of two strands coloured `i` as the bimodule
endomorphism of `H_{+_i k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` given by
`ξ^{α₁} ⊗ ξ^{α₂} ↦ ∑_{f < α₁} ξ^{α₁+α₂-1-f} ⊗ ξ^f - ∑_{g < α₂} ξ^{α₁+α₂-1-g} ⊗ ξ^g`, "the divided
difference operator acting on `ξ_i` and `ξ_j`", and of a dot as multiplication by `ξ`.

## The Borel model of two strands

`Categorification.Flag.tensorEquiv` identifies the tensor product of two consecutive bimodules
`H_{(+_{i₂} k)^{+i₁}} ⊗_{H_{+_{i₂} k}} H_{k^{+i₂}}` with the Borel ring of the labelling in which
both moved variables `v₁` (of the left strand) and `v₂` (of the right strand) are singletons,
provided that the block of `v₁` is not the block receiving `v₂` (`lab v₁ ≠ j₂`; this covers
`E_i E_i`, `E_{i+1} E_i` and `E_i E_j` for `|i - j| > 1`, i.e. exactly the cases in which the
iterated flag variety of KL III eq. (5.37) is a partial flag variety). The identification sends
`m₁ ⊗ m₂ ↦ m₁ m₂`, hence `ξ₁^{α₁} ⊗ ξ₂^{α₂} ↦ x_{v₁}^{α₁} x_{v₂}^{α₂}`.

## Divided differences

For any labelling `S` in which `v₁ ≠ v₂` are singletons, the divided difference
`∂ f = (f - s_{v₁v₂} f) / (x_{v₁} - x_{v₂})` preserves the Young invariants and the ideal
`(Sym⁺)`, hence descends to `ddiffB : BorelRing k S →ₗ[k] BorelRing k S`, with
`ddiffB_xi_pow` (the formula of KL III (6.8)), `ddiffB_ddiffB` (`∂² = 0`),
`ddiffB_xi_mul_left`, `ddiffB_xi_mul_right` (dot slides), `ddiffB_refineHom_mul` (linearity over
coarser labellings in which `v₁`, `v₂` share a block), and for three singletons
`ddiffB_braid` (`∂₁₂ ∂₂₃ ∂₁₂ = ∂₂₃ ∂₁₂ ∂₂₃`) and `ddiffB_comm` (far commutativity).

## `Γ` of crossings

* `crossEE` : `Γ` of the upward crossing of two strands coloured `i` on
  `H_{+_i k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`, defined by transporting `∂_{v₁v₂}` along
  `tensorEquiv`. `crossEE_xi` is KL III's formula (6.8) for `i = j`; `crossEE_left`,
  `crossEE_right` say that it is a bimodule map; `crossEE_crossEE` (`ψ² = 0`),
  `crossEE_xi_left`, `crossEE_xi_right` (the dot-slide relations
  `ψ (ξ ⊗ 1) = 1 + (1 ⊗ ξ) ψ`, `ψ (1 ⊗ ξ) = (ξ ⊗ 1) ψ - 1`) are the nilHecke relations of KL III
  Definition 3.1 for two strands coloured `i`, with dots `Γ(dot) = ` multiplication by `ξ`
  (KL III eqs. (6.6), (6.7)).
* `crossFar` : `Γ` of the crossing `E_i E_j 1_k → E_j E_i 1_k` for distant colours
  (`i · j = 0`), with `crossFar_xi` (`ξ_i^{α₁} ⊗ ξ_j^{α₂} ↦ ξ_j^{α₂} ⊗ ξ_i^{α₁}`),
  `crossFar_crossFar` (the relation `ψ_{ji} ψ_{ij} = 1`) and `crossFar_right` (right linearity).

Not treated: the three-strand analogue of `tensorEquiv` (so the braid relation is proved in the
Borel model of `E_i E_i E_i 1_k`, not yet transported to the iterated tensor product), crossings
of adjacent colours (`i · j = -1`, where one of the two iterated flag varieties is not a partial
flag variety), and gradings.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial Equiv TensorProduct
open Finset (univ range antidiagonal)

/-! ### Divided differences on Borel rings -/

section DDiff

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J] (S : V → J)

omit [Fintype V] [DecidableEq V] [DecidableEq J] in
theorem label_fix {g : Perm V} (hg : S ∘ g = S) {v : V} (h : ∀ w, S w = S v → w = v) :
    g v = v :=
  h _ (congrFun hg v)

omit [Fintype V] in
theorem swap_comm_of_fix {v₁ v₂ : V} {g : Perm V} (hg1 : g v₁ = v₁) (hg2 : g v₂ = v₂) :
    ⇑g ∘ ⇑(swap v₁ v₂) = ⇑(swap v₁ v₂) ∘ ⇑g := by
  funext x
  simp only [Function.comp_apply]
  by_cases hx1 : x = v₁
  · subst hx1; rw [swap_apply_left, hg2, hg1, swap_apply_left]
  by_cases hx2 : x = v₂
  · subst hx2; rw [swap_apply_right, hg1, hg2, swap_apply_right]
  rw [swap_apply_of_ne_of_ne hx1 hx2, swap_apply_of_ne_of_ne]
  · exact fun h => hx1 (g.injective (h.trans hg1.symm))
  · exact fun h => hx2 (g.injective (h.trans hg2.symm))

set_option synthInstance.maxHeartbeats 200000

variable {S} {v₁ v₂ : V} (h₁ : ∀ w, S w = S v₁ → w = v₁) (h₂ : ∀ w, S w = S v₂ → w = v₂)
  (hne : v₁ ≠ v₂)

include h₁ h₂ hne in
omit [Fintype V] [DecidableEq J] in
theorem ddiff_mem_labelInvariants {f : MvPolynomial V k} (hf : f ∈ labelInvariants k S) :
    ddiff v₁ v₂ f ∈ labelInvariants k S := by
  intro g hg
  rw [rename_ddiff_of_fix g.injective hne (label_fix S hg h₁) (label_fix S hg h₂), hf g hg]

include h₁ h₂ in
omit [Fintype V] [DecidableEq J] in
theorem swap_mem_labelInvariants {f : MvPolynomial V k} (hf : f ∈ labelInvariants k S) :
    rename (swap v₁ v₂) f ∈ labelInvariants k S := by
  intro g hg
  rw [rename_rename, swap_comm_of_fix (label_fix S hg h₁) (label_fix S hg h₂), ← rename_rename,
    hf g hg]

include h₁ h₂ hne in
omit [DecidableEq J] in
theorem ddiff_mem_borelIdeal {y : labelInvariants k S} (hy : y ∈ borelIdeal k S) :
    (⟨ddiff v₁ v₂ (y : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne y.2⟩ :
      labelInvariants k S) ∈ borelIdeal k S := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    have : (⟨ddiff v₁ v₂ (x : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne x.2⟩ :
        labelInvariants k S) = 0 := Subtype.ext (ddiff_eq_zero_of_rename_eq hne (hx.1 _))
    rw [this]
    exact (borelIdeal k S).zero_mem
  | zero =>
    have : (⟨ddiff v₁ v₂ ((0 : labelInvariants k S) : MvPolynomial V k),
        ddiff_mem_labelInvariants h₁ h₂ hne (0 : labelInvariants k S).2⟩ :
        labelInvariants k S) = 0 := Subtype.ext (by simp)
    rw [this]
    exact (borelIdeal k S).zero_mem
  | add x y _ _ hx hy =>
    have : (⟨ddiff v₁ v₂ ((x + y : labelInvariants k S) : MvPolynomial V k),
        ddiff_mem_labelInvariants h₁ h₂ hne (x + y).2⟩ : labelInvariants k S) =
        ⟨ddiff v₁ v₂ (x : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne x.2⟩ +
        ⟨ddiff v₁ v₂ (y : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne y.2⟩ :=
      Subtype.ext (by simp [map_add])
    rw [this]
    exact (borelIdeal k S).add_mem hx hy
  | smul c x hx ih =>
    rw [smul_eq_mul]
    have e : (⟨ddiff v₁ v₂ ((c * x : labelInvariants k S) : MvPolynomial V k),
        ddiff_mem_labelInvariants h₁ h₂ hne (c * x).2⟩ : labelInvariants k S) =
        ⟨ddiff v₁ v₂ (c : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne c.2⟩ * x +
        ⟨rename (swap v₁ v₂) (c : MvPolynomial V k), swap_mem_labelInvariants h₁ h₂ c.2⟩ *
          ⟨ddiff v₁ v₂ (x : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne x.2⟩ :=
      Subtype.ext (by simp [ddiff_mul hne])
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ ih)

variable (k) in
/-- `∂_{v₁v₂}` on the Young invariants. -/
def ddiffInv (a : labelInvariants k S) : labelInvariants k S :=
  ⟨ddiff v₁ v₂ (a : MvPolynomial V k), ddiff_mem_labelInvariants h₁ h₂ hne a.2⟩

omit [Fintype V] [DecidableEq J] in
theorem ddiffInv_sub (a b : labelInvariants k S) :
    ddiffInv k h₁ h₂ hne (a - b) = ddiffInv k h₁ h₂ hne a - ddiffInv k h₁ h₂ hne b :=
  Subtype.ext (by simp [ddiffInv, map_sub])

omit [DecidableEq J] in
theorem mkB_ddiffInv_eq {a b : labelInvariants k S} (h : mkB k S a = mkB k S b) :
    mkB k S (ddiffInv k h₁ h₂ hne a) = mkB k S (ddiffInv k h₁ h₂ hne b) := by
  rw [mkB_eq_mkB_iff] at h ⊢
  rw [← ddiffInv_sub]
  exact ddiff_mem_borelIdeal h₁ h₂ hne h

variable (k) in
/-- **The divided difference `∂_{v₁v₂}` on a Borel ring** in which `v₁ ≠ v₂` are singletons. -/
def ddiffB : BorelRing k S →ₗ[k] BorelRing k S where
  toFun z := mkB k S (ddiffInv k h₁ h₂ hne (Function.surjInv (mkB_surjective S) z))
  map_add' z w := by
    obtain ⟨a, rfl⟩ := mkB_surjective S z
    obtain ⟨b, rfl⟩ := mkB_surjective S w
    have e := fun c => mkB_ddiffInv_eq (k := k) h₁ h₂ hne
      (Function.surjInv_eq (mkB_surjective S) (mkB k S c))
    rw [← map_add, e, e, e, ← map_add]
    congr 1
    exact Subtype.ext (by simp [ddiffInv, map_add])
  map_smul' c z := by
    obtain ⟨a, rfl⟩ := mkB_surjective S z
    have e := fun c => mkB_ddiffInv_eq (k := k) h₁ h₂ hne
      (Function.surjInv_eq (mkB_surjective S) (mkB k S c))
    rw [← map_smul, e, e, RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (by simp [ddiffInv, map_smul])

omit [DecidableEq J] in
theorem ddiffB_mk (a : labelInvariants k S) :
    ddiffB k h₁ h₂ hne (mkB k S a) = mkB k S (ddiffInv k h₁ h₂ hne a) :=
  mkB_ddiffInv_eq h₁ h₂ hne (Function.surjInv_eq (mkB_surjective S) (mkB k S a))

variable (k) in
/-- The class of `x_v` for a singleton `v`. -/
abbrev xv {v : V} (h : ∀ w, S w = S v → w = v) : BorelRing k S := xiS k S v h

omit [DecidableEq J] in
theorem ddiffB_ddiffB (z : BorelRing k S) : ddiffB k h₁ h₂ hne (ddiffB k h₁ h₂ hne z) = 0 := by
  obtain ⟨a, rfl⟩ := mkB_surjective S z
  rw [ddiffB_mk, ddiffB_mk, ← map_zero (mkB k S)]
  congr 1
  exact Subtype.ext (by simp [ddiffInv, ddiff_ddiff hne])

omit [DecidableEq J] in
/-- `∂` is linear over classes of `s_{v₁v₂}`-invariant polynomials. -/
theorem ddiffB_mul_of_swap (a : labelInvariants k S)
    (ha : rename (swap v₁ v₂) (a : MvPolynomial V k) = a) (z : BorelRing k S) :
    ddiffB k h₁ h₂ hne (mkB k S a * z) = mkB k S a * ddiffB k h₁ h₂ hne z := by
  obtain ⟨b, rfl⟩ := mkB_surjective S z
  rw [← map_mul, ddiffB_mk, ddiffB_mk, ← map_mul]
  congr 1
  exact Subtype.ext (by simp [ddiffInv, ddiff_mul_of_rename_eq hne ha])

omit [DecidableEq J] in
/-- **Dot slide** `∂ ∘ ξ₁ = 1 + ξ₂ ∘ ∂`. -/
theorem ddiffB_xi_mul_left (z : BorelRing k S) :
    ddiffB k h₁ h₂ hne (xv k h₁ * z) = z + xv k h₂ * ddiffB k h₁ h₂ hne z := by
  obtain ⟨b, rfl⟩ := mkB_surjective S z
  rw [xv, xiS, ← map_mul, ddiffB_mk, ddiffB_mk, xv, xiS, ← map_mul, ← map_add]
  congr 1
  exact Subtype.ext (by simp [ddiffInv, ddiff_mul hne, ddiff_X_left hne])

omit [DecidableEq J] in
/-- **Dot slide** `∂ ∘ ξ₂ = ξ₁ ∘ ∂ - 1`. -/
theorem ddiffB_xi_mul_right (z : BorelRing k S) :
    ddiffB k h₁ h₂ hne (xv k h₂ * z) = xv k h₁ * ddiffB k h₁ h₂ hne z - z := by
  obtain ⟨b, rfl⟩ := mkB_surjective S z
  rw [xv, xiS, ← map_mul, ddiffB_mk, ddiffB_mk, xv, xiS, ← map_mul, ← map_sub]
  congr 1
  exact Subtype.ext (by simp [ddiffInv, ddiff_mul hne, ddiff_X_right hne, sub_eq_neg_add])

omit [Fintype V] in
/-- The polynomial identity behind KL III's formula (6.8):
`∂(x₁^{α₁} x₂^{α₂}) = ∑_{f < α₁} x₁^{α₁+α₂-1-f} x₂^f - ∑_{g < α₂} x₁^{α₁+α₂-1-g} x₂^g`. -/
theorem ddiff_X_pow_mul_X_pow {v₁ v₂ : V} (hne : v₁ ≠ v₂) (α₁ α₂ : ℕ) :
    ddiff v₁ v₂ ((X v₁ : MvPolynomial V k) ^ α₁ * X v₂ ^ α₂) =
      ∑ f ∈ range α₁, X v₁ ^ (α₁ + α₂ - 1 - f) * X v₂ ^ f -
        ∑ g ∈ range α₂, X v₁ ^ (α₁ + α₂ - 1 - g) * X v₂ ^ g := by
  apply ddiff_eq_of_mul hne
  have geo : ∀ n c : ℕ, (X v₁ - X v₂) * ∑ f ∈ range n,
      (X v₁ : MvPolynomial V k) ^ (n + c - 1 - f) * X v₂ ^ f =
      X v₁ ^ c * (X v₁ ^ n - X v₂ ^ n) := by
    intro n c
    rw [← geom_sum₂_mul, ← Finset.sum_range_reflect (fun i => X v₁ ^ i * X v₂ ^ (n - 1 - i)) n,
      Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hf' : f < n := Finset.mem_range.1 hf
    rw [show n + c - 1 - f = c + (n - 1 - f) by omega, show n - 1 - (n - 1 - f) = f by omega,
      pow_add]
    ring
  have g2 := geo α₂ α₁
  rw [show α₂ + α₁ = α₁ + α₂ from add_comm _ _] at g2
  rw [mul_sub, geo α₁ α₂, g2]
  simp only [map_mul, map_pow, rename_X, swap_apply_left, swap_apply_right]
  ring

omit [DecidableEq J] in
/-- **KL III Definition 6.2, eq. (6.8) for `i = j`**: the divided difference of
`ξ₁^{α₁} ξ₂^{α₂}` is `∑_{f < α₁} ξ₁^{α₁+α₂-1-f} ξ₂^f - ∑_{g < α₂} ξ₁^{α₁+α₂-1-g} ξ₂^g`. -/
theorem ddiffB_xi_pow (α₁ α₂ : ℕ) :
    ddiffB k h₁ h₂ hne (xv k h₁ ^ α₁ * xv k h₂ ^ α₂) =
      ∑ f ∈ range α₁, xv k h₁ ^ (α₁ + α₂ - 1 - f) * xv k h₂ ^ f -
        ∑ g ∈ range α₂, xv k h₁ ^ (α₁ + α₂ - 1 - g) * xv k h₂ ^ g := by
  simp only [xv, xiS, ← map_pow, ← map_mul, ← map_sum, ← map_sub]
  rw [ddiffB_mk]
  congr 1
  apply Subtype.ext
  simp only [ddiffInv, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
    AddSubmonoidClass.coe_finset_sum]
  exact ddiff_X_pow_mul_X_pow hne α₁ α₂

omit [DecidableEq J] in
/-- `∂` is linear over any coarser labelling in which `v₁` and `v₂` lie in the same block (in
particular over both outer rings of `E_i E_i 1_k`): `Γ(crossing)` is a bimodule map. -/
theorem ddiffB_refineHom_mul {J₂ : Type*} {T : V → J₂} (h : Refines S T) (hT : T v₁ = T v₂)
    (r : BorelRing k T) (z : BorelRing k S) :
    ddiffB k h₁ h₂ hne (refineHom k h r * z) = refineHom k h r * ddiffB k h₁ h₂ hne z := by
  obtain ⟨c, rfl⟩ := mkB_surjective T r
  rw [refineHom_mk h c ⟨c, labelInvariants_mono k h c.2⟩ rfl]
  refine ddiffB_mul_of_swap h₁ h₂ hne _ ?_ z
  refine c.2 (swap v₁ v₂) (funext fun v => ?_)
  simp only [Function.comp_apply]
  by_cases hv1 : v = v₁
  · subst hv1; rw [swap_apply_left, hT]
  by_cases hv2 : v = v₂
  · subst hv2; rw [swap_apply_right, hT]
  rw [swap_apply_of_ne_of_ne hv1 hv2]

end DDiff

/-! ### Braid relations for three strands -/

section Braid

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [DecidableEq J] {S : V → J} {a b c : V} (ha : ∀ w, S w = S a → w = a)
  (hb : ∀ w, S w = S b → w = b) (hc : ∀ w, S w = S c → w = c)
  (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)

include hac in
omit [DecidableEq J] in
/-- **The nilHecke braid relation** `∂_{ab} ∂_{bc} ∂_{ab} = ∂_{bc} ∂_{ab} ∂_{bc}` on a Borel ring in
which `a, b, c` are singletons (the image of the KLR relation for three strands coloured `i`). -/
theorem ddiffB_braid (z : BorelRing k S) :
    ddiffB k ha hb hab (ddiffB k hb hc hbc (ddiffB k ha hb hab z)) =
      ddiffB k hb hc hbc (ddiffB k ha hb hab (ddiffB k hb hc hbc z)) := by
  obtain ⟨x, rfl⟩ := mkB_surjective S z
  simp only [ddiffB_mk]
  congr 1
  exact Subtype.ext (ddiff_braid hab hbc hac _)

include hac hbc in
omit [DecidableEq J] in
/-- **Far commutativity** of divided differences of disjoint pairs of singletons. -/
theorem ddiffB_comm {d : V} (hd : ∀ w, S w = S d → w = d) (hcd : c ≠ d) (had : a ≠ d)
    (hbd : b ≠ d) (z : BorelRing k S) :
    ddiffB k ha hb hab (ddiffB k hc hd hcd z) = ddiffB k hc hd hcd (ddiffB k ha hb hab z) := by
  obtain ⟨x, rfl⟩ := mkB_surjective S z
  simp only [ddiffB_mk]
  congr 1
  exact Subtype.ext (ddiff_ddiff_comm hab hcd hac had hbc hbd _)

end Braid

/-! ### Two strands: the tensor product as a Borel ring -/

section Tensor

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

omit [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J] in
theorem refines_trans {J₁ J₂ J₃ : Type*} {l₁ : V → J₁} {l₂ : V → J₂} {l₃ : V → J₃}
    (h₁₂ : Refines l₂ l₁) (h₂₃ : Refines l₃ l₂) : Refines l₃ l₁ :=
  fun v w h => h₁₂ v w (h₂₃ v w h)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
theorem refineHom_comp_apply {J₁ J₂ J₃ : Type*} {l₁ : V → J₁} {l₂ : V → J₂} {l₃ : V → J₃}
    (h₁₂ : Refines l₂ l₁) (h₂₃ : Refines l₃ l₂) (z : BorelRing k l₁) :
    refineHom k h₂₃ (refineHom k h₁₂ z) = refineHom k (refines_trans h₁₂ h₂₃) z := by
  obtain ⟨a, rfl⟩ := mkB_surjective l₁ z
  rw [refineHom_mk h₁₂ a ⟨a, labelInvariants_mono k h₁₂ a.2⟩ rfl,
    refineHom_mk h₂₃ _ ⟨a, labelInvariants_mono k (refines_trans h₁₂ h₂₃) a.2⟩ rfl,
    refineHom_mk (refines_trans h₁₂ h₂₃) a ⟨a, labelInvariants_mono k (refines_trans h₁₂ h₂₃) a.2⟩
      rfl]

variable (lab : V → J) (v₁ v₂ : V) (j₂ : J)

/-- The joint labelling of two strands: `v₂` (right strand) and `v₁` (left strand) are
singletons. -/
abbrev jointLab : V → Option (Option J) := splitLab (splitLab lab v₂) v₁

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem refines_joint_left :
    Refines (jointLab lab v₁ v₂) (splitLab (moveLab lab v₂ j₂) v₁) := by
  intro v w h
  simp only [jointLab] at h
  by_cases hv1 : v = v₁
  · subst hv1
    have : w = v := splitLab_eq_none.1 (h.symm.trans splitLab_self)
    rw [this]
  have hw1 : w ≠ v₁ := fun hw => hv1 (splitLab_eq_none.1 (h.trans (hw ▸ splitLab_self)))
  rw [splitLab_of_ne hv1, splitLab_of_ne hw1] at h
  have h' := Option.some_injective _ h
  by_cases hv2 : v = v₂
  · subst hv2
    have : w = v := splitLab_eq_none.1 (h'.symm.trans splitLab_self)
    rw [this]
  have hw2 : w ≠ v₂ := fun hw => hv2 (splitLab_eq_none.1 (h'.trans (hw ▸ splitLab_self)))
  rw [splitLab_of_ne hv2, splitLab_of_ne hw2] at h'
  rw [splitLab_of_ne hv1, splitLab_of_ne hw1, moveLab, Function.update_of_ne hv2,
    Function.update_of_ne hw2, Option.some_injective _ h']

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem joint_singleton_right (hne : v₁ ≠ v₂) :
    ∀ w, jointLab lab v₁ v₂ w = jointLab lab v₁ v₂ v₂ → w = v₂ := by
  intro w h
  simp only [jointLab] at h
  rw [splitLab_of_ne hne.symm] at h
  have hw1 : w ≠ v₁ := by
    rintro rfl
    rw [splitLab_self] at h
    exact Option.noConfusion h
  rw [splitLab_of_ne hw1] at h
  exact (splitLab_singleton lab v₂) w (Option.some_injective _ h)

variable (k)

/-- The middle ring `H_{+_{i₂} k}` acting on the joint Borel ring. -/
def jointAlgebra :
    Algebra (BorelRing k (moveLab lab v₂ j₂)) (BorelRing k (jointLab lab v₁ v₂)) :=
  (refineHom k (refines_trans (refines_splitLab (moveLab lab v₂ j₂) v₁)
    (refines_joint_left lab v₁ v₂ j₂))).toRingHom.toAlgebra

attribute [local instance] rightAlgebra midAlgebra

/-- The left factor `H_{(+_{i₂} k)^{+i₁}} → joint`. -/
def jointLeft :
    letI := jointAlgebra k lab v₁ v₂ j₂
    BorelRing k (splitLab (moveLab lab v₂ j₂) v₁) →ₐ[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (jointLab lab v₁ v₂) :=
  letI := jointAlgebra k lab v₁ v₂ j₂
  { refineHom k (refines_joint_left lab v₁ v₂ j₂) with
    commutes' := fun r => refineHom_comp_apply _ _ r }

/-- The right factor `H_{k^{+i₂}} → joint`. -/
def jointRight :
    letI := jointAlgebra k lab v₁ v₂ j₂
    BorelRing k (splitLab lab v₂) →ₐ[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (jointLab lab v₁ v₂) :=
  letI := jointAlgebra k lab v₁ v₂ j₂
  { pR k (splitLab lab v₂) v₁ with
    commutes' := fun r => refineHom_comp_apply _ _ r }

/-- The multiplication map
`H_{(+_{i₂} k)^{+i₁}} ⊗_{H_{+_{i₂} k}} H_{k^{+i₂}} → BorelRing (joint)`, `m₁ ⊗ m₂ ↦ m₁ m₂`. -/
def jointMap :
    letI := jointAlgebra k lab v₁ v₂ j₂
    BorelRing k (splitLab (moveLab lab v₂ j₂) v₁) ⊗[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (splitLab lab v₂) →ₐ[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (jointLab lab v₁ v₂) :=
  letI := jointAlgebra k lab v₁ v₂ j₂
  Algebra.TensorProduct.productMap (jointLeft k lab v₁ v₂ j₂) (jointRight k lab v₁ v₂ j₂)

variable {k}

omit [Fintype J] [DecidableEq J] in
theorem jointMap_tmul (m₁ : BorelRing k (splitLab (moveLab lab v₂ j₂) v₁))
    (m₂ : BorelRing k (splitLab lab v₂)) :
    jointMap k lab v₁ v₂ j₂ (m₁ ⊗ₜ m₂) =
      refineHom k (refines_joint_left lab v₁ v₂ j₂) m₁ * pR k (splitLab lab v₂) v₁ m₂ :=
  rfl

omit [Fintype J] [DecidableEq J] in
theorem jointLeft_xi :
    refineHom k (refines_joint_left lab v₁ v₂ j₂) (xi k (moveLab lab v₂ j₂) v₁) =
      xi k (splitLab lab v₂) v₁ :=
  refineHom_mk _ _ _ rfl

omit [Fintype J] in
theorem blockCard_joint (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂) :
    blockCard (moveLab lab v₂ j₂) v₁ = blockCard (splitLab lab v₂) v₁ := by
  rw [blockCard, blockCard, moveLab, Function.update_of_ne hne, ← moveLab, labSet_move_eq,
    if_neg hj, splitLab_of_ne hne]

/-- Every element of the tensor product is `∑_a ξ₁^a ⊗ c_a`. -/
theorem tensor_span
    (t : BorelRing k (splitLab (moveLab lab v₂ j₂) v₁) ⊗[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (splitLab lab v₂)) :
    ∃ c : Fin (blockCard (moveLab lab v₂ j₂) v₁) → BorelRing k (splitLab lab v₂),
      t = ∑ a : Fin (blockCard (moveLab lab v₂ j₂) v₁),
        (xi k (moveLab lab v₂ j₂) v₁ ^ (a : ℕ)) ⊗ₜ c a := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m₁ m₂ =>
    obtain ⟨r, hr⟩ := split_span (moveLab lab v₂ j₂) v₁ m₁
    refine ⟨fun a => pL k lab v₂ j₂ (r a) * m₂, ?_⟩
    rw [← hr, sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_right, ← Algebra.smul_def, smul_tmul, Algebra.smul_def, algebraMap_mid]
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by simp [tmul_add, Finset.sum_add_distrib]⟩

omit [Fintype J] in
theorem jointMap_sum
    (c : Fin (blockCard (moveLab lab v₂ j₂) v₁) → BorelRing k (splitLab lab v₂)) :
    jointMap k lab v₁ v₂ j₂ (∑ a : Fin (blockCard (moveLab lab v₂ j₂) v₁),
        (xi k (moveLab lab v₂ j₂) v₁ ^ (a : ℕ)) ⊗ₜ c a) =
      ∑ a : Fin (blockCard (moveLab lab v₂ j₂) v₁),
        pR k (splitLab lab v₂) v₁ (c a) * xi k (splitLab lab v₂) v₁ ^ (a : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [jointMap_tmul, map_pow, jointLeft_xi, mul_comm]

/-- **The tensor product of two consecutive `E`-bimodules is the Borel ring of the joint
labelling** (KL III eq. (5.37) for two strands, when the iterated flag variety is a partial
flag variety): for `v₁ ≠ v₂` and `lab v₁ ≠ j₂`, the multiplication map
`H_{(+_{i₂} k)^{+i₁}} ⊗_{H_{+_{i₂} k}} H_{k^{+i₂}} → BorelRing (joint)` is bijective. -/
theorem jointMap_bijective (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂) :
    Function.Bijective (jointMap k lab v₁ v₂ j₂) := by
  have hb := blockCard_joint lab v₁ v₂ j₂ hne hj
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, rfl⟩ := tensor_span lab v₁ v₂ j₂ t
    rw [jointMap_sum] at ht
    have hc := split_indep (splitLab lab v₂) v₁ (fun a => c (Fin.cast hb.symm a)) (by
      rw [← ht]
      exact Fintype.sum_equiv (finCongr hb.symm) _ _ fun a => rfl)
    have : c = 0 := funext fun a => by
      have := congrFun hc (Fin.cast hb a)
      simpa using this
    simp [this]
  · intro w
    obtain ⟨c, hc⟩ := split_span (splitLab lab v₂) v₁ w
    refine ⟨∑ a : Fin (blockCard (moveLab lab v₂ j₂) v₁),
      (xi k (moveLab lab v₂ j₂) v₁ ^ (a : ℕ)) ⊗ₜ c (Fin.cast hb a), ?_⟩
    rw [jointMap_sum, ← hc]
    exact Fintype.sum_equiv (finCongr hb) _ _ fun a => rfl

variable (k) in
/-- **KL III eq. (5.37), two strands**: `H_{(+_{i₂} k)^{+i₁}} ⊗_{H_{+_{i₂} k}} H_{k^{+i₂}}` is
isomorphic, as an algebra over the middle ring, to the Borel ring of the joint labelling. -/
def tensorEquiv (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂) :
    letI := jointAlgebra k lab v₁ v₂ j₂
    (BorelRing k (splitLab (moveLab lab v₂ j₂) v₁) ⊗[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (splitLab lab v₂)) ≃ₐ[BorelRing k (moveLab lab v₂ j₂)]
      BorelRing k (jointLab lab v₁ v₂) :=
  letI := jointAlgebra k lab v₁ v₂ j₂
  AlgEquiv.ofBijective (jointMap k lab v₁ v₂ j₂) (jointMap_bijective lab v₁ v₂ j₂ hne hj)

theorem tensorEquiv_xi (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂) (α₁ α₂ : ℕ) :
    tensorEquiv k lab v₁ v₂ j₂ hne hj
        ((xi k (moveLab lab v₂ j₂) v₁ ^ α₁) ⊗ₜ (xi k lab v₂ ^ α₂)) =
      xiS k (jointLab lab v₁ v₂) v₁ (splitLab_singleton _ v₁) ^ α₁ *
        xiS k (jointLab lab v₁ v₂) v₂ (joint_singleton_right lab v₁ v₂ hne) ^ α₂ := by
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, map_pow, map_pow, jointLeft_xi]
  congr 2

end Tensor


/-! ### `Γ` of the crossing of two strands coloured `i` -/

section EE

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J] (lab : V → J) (v₁ v₂ : V) (j₂ : J)

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

/-- The ring `H_{+_i k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}` of `E_i E_i 1_k` (KL III eq. (5.37)). -/
abbrev EERing : Type _ :=
  BorelRing k (splitLab (moveLab lab v₂ j₂) v₁) ⊗[BorelRing k (moveLab lab v₂ j₂)]
    BorelRing k (splitLab lab v₂)

variable (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂)

variable (k) in
/-- **`Γ` of the upward crossing of two strands coloured `i`** (KL III Definition 6.2,
eq. (6.8) for `i = j`), transported to the Borel ring of the joint labelling by
`tensorEquiv` and realized there as the divided difference `∂_{v₁v₂}`. -/
def crossEE (t : EERing (k := k) lab v₁ v₂ j₂) : EERing (k := k) lab v₁ v₂ j₂ :=
  (tensorEquiv k lab v₁ v₂ j₂ hne hj).symm
    (ddiffB k (splitLab_singleton _ v₁) (joint_singleton_right lab v₁ v₂ hne) hne
      (tensorEquiv k lab v₁ v₂ j₂ hne hj t))

theorem tensorEquiv_crossEE (t : EERing (k := k) lab v₁ v₂ j₂) :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (crossEE k lab v₁ v₂ j₂ hne hj t) =
      ddiffB k (splitLab_singleton _ v₁) (joint_singleton_right lab v₁ v₂ hne) hne
        (tensorEquiv k lab v₁ v₂ j₂ hne hj t) :=
  AlgEquiv.apply_symm_apply _ _

theorem tE_mul (a b : EERing (k := k) lab v₁ v₂ j₂) :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (a * b) =
      tensorEquiv k lab v₁ v₂ j₂ hne hj a * tensorEquiv k lab v₁ v₂ j₂ hne hj b :=
  map_mul _ a b

theorem tE_add (a b : EERing (k := k) lab v₁ v₂ j₂) :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (a + b) =
      tensorEquiv k lab v₁ v₂ j₂ hne hj a + tensorEquiv k lab v₁ v₂ j₂ hne hj b :=
  map_add _ a b

theorem tE_sub (a b : EERing (k := k) lab v₁ v₂ j₂) :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (a - b) =
      tensorEquiv k lab v₁ v₂ j₂ hne hj a - tensorEquiv k lab v₁ v₂ j₂ hne hj b :=
  map_sub _ a b

theorem tensorEquiv_xi_tmul_one :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (xi k (moveLab lab v₂ j₂) v₁ ⊗ₜ 1) =
      xiS k (jointLab lab v₁ v₂) v₁ (splitLab_singleton _ v₁) := by
  simpa using tensorEquiv_xi (k := k) lab v₁ v₂ j₂ hne hj 1 0

theorem tensorEquiv_one_tmul_xi :
    tensorEquiv k lab v₁ v₂ j₂ hne hj (1 ⊗ₜ xi k lab v₂) =
      xiS k (jointLab lab v₁ v₂) v₂ (joint_singleton_right lab v₁ v₂ hne) := by
  simpa using tensorEquiv_xi (k := k) lab v₁ v₂ j₂ hne hj 0 1

/-- **KL III Definition 6.2, eq. (6.8), `i = j`**: `Γ(crossing)` sends
`ξ^{α₁} ⊗ ξ^{α₂} ↦ ∑_{f < α₁} ξ^{α₁+α₂-1-f} ⊗ ξ^f - ∑_{g < α₂} ξ^{α₁+α₂-1-g} ⊗ ξ^g`. -/
theorem crossEE_xi (α₁ α₂ : ℕ) :
    crossEE k lab v₁ v₂ j₂ hne hj
        ((xi k (moveLab lab v₂ j₂) v₁ ^ α₁) ⊗ₜ[BorelRing k (moveLab lab v₂ j₂)]
          (xi k lab v₂ ^ α₂)) =
      ∑ f ∈ range α₁, (xi k (moveLab lab v₂ j₂) v₁ ^ (α₁ + α₂ - 1 - f)) ⊗ₜ[BorelRing k
          (moveLab lab v₂ j₂)] (xi k lab v₂ ^ f) -
        ∑ g ∈ range α₂, (xi k (moveLab lab v₂ j₂) v₁ ^ (α₁ + α₂ - 1 - g)) ⊗ₜ[BorelRing k
          (moveLab lab v₂ j₂)] (xi k lab v₂ ^ g) := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  rw [tensorEquiv_crossEE, tensorEquiv_xi, ddiffB_xi_pow, map_sub, map_sum, map_sum]
  simp only [tensorEquiv_xi]

/-- **`∂² = 0`** for `Γ(crossing)` (the nilHecke relation of KL III Definition 3.1 for `i = j`). -/
theorem crossEE_crossEE (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossEE k lab v₁ v₂ j₂ hne hj (crossEE k lab v₁ v₂ j₂ hne hj t) = 0 := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  rw [tensorEquiv_crossEE, tensorEquiv_crossEE, ddiffB_ddiffB, map_zero]

/-- **Dot slide** (KL III Definition 3.1, `i = j`): `Γ(crossing) ∘ (ξ ⊗ 1) = 1 + (1 ⊗ ξ) ∘ Γ(crossing)`. -/
theorem crossEE_xi_left (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossEE k lab v₁ v₂ j₂ hne hj ((xi k (moveLab lab v₂ j₂) v₁ ⊗ₜ 1) * t) =
      t + (1 ⊗ₜ xi k lab v₂) * crossEE k lab v₁ v₂ j₂ hne hj t := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  rw [tensorEquiv_crossEE, tE_mul, tE_add, tE_mul, tensorEquiv_crossEE,
    tensorEquiv_xi_tmul_one, tensorEquiv_one_tmul_xi]
  exact ddiffB_xi_mul_left _ _ hne _

/-- **Dot slide** (KL III Definition 3.1, `i = j`): `Γ(crossing) ∘ (1 ⊗ ξ) = (ξ ⊗ 1) ∘ Γ(crossing) - 1`. -/
theorem crossEE_xi_right (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossEE k lab v₁ v₂ j₂ hne hj ((1 ⊗ₜ xi k lab v₂) * t) =
      (xi k (moveLab lab v₂ j₂) v₁ ⊗ₜ 1) * crossEE k lab v₁ v₂ j₂ hne hj t - t := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  rw [tensorEquiv_crossEE, tE_mul, tE_sub, tE_mul, tensorEquiv_crossEE,
    tensorEquiv_xi_tmul_one, tensorEquiv_one_tmul_xi]
  exact ddiffB_xi_mul_right _ _ hne _

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem refines_joint_lab : Refines (jointLab lab v₁ v₂) lab :=
  refines_trans (refines_splitLab lab v₂) (refines_splitLab (splitLab lab v₂) v₁)

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem refines_joint_outer :
    Refines (jointLab lab v₁ v₂) (moveLab (moveLab lab v₂ j₂) v₁ j₂) :=
  refines_trans (refines_splitLab_move (moveLab lab v₂ j₂) v₁ j₂)
    (refines_joint_left lab v₁ v₂ j₂)

/-- **`Γ(crossing)` is a map of right `H_k`-modules** (for `E_i E_i`: `v₁`, `v₂` in the same
block of `k`). -/
theorem crossEE_right (hsame : lab v₁ = lab v₂) (r : BorelRing k lab)
    (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossEE k lab v₁ v₂ j₂ hne hj ((1 ⊗ₜ pR k lab v₂ r) * t) =
      (1 ⊗ₜ pR k lab v₂ r) * crossEE k lab v₁ v₂ j₂ hne hj t := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  have h1 : tensorEquiv k lab v₁ v₂ j₂ hne hj (1 ⊗ₜ pR k lab v₂ r) =
      refineHom k (refines_joint_lab lab v₁ v₂) r := by
    simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
    rw [jointMap_tmul, map_one, one_mul, pR, pR, refineHom_comp_apply]
  rw [tensorEquiv_crossEE, tE_mul, tE_mul, tensorEquiv_crossEE, h1]
  exact ddiffB_refineHom_mul _ _ hne _ hsame _ _

/-- **`Γ(crossing)` is a map of left `H_{+_i +_i k}`-modules**. -/
theorem crossEE_left (r : BorelRing k (moveLab (moveLab lab v₂ j₂) v₁ j₂))
    (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossEE k lab v₁ v₂ j₂ hne hj ((pL k (moveLab lab v₂ j₂) v₁ j₂ r ⊗ₜ 1) * t) =
      (pL k (moveLab lab v₂ j₂) v₁ j₂ r ⊗ₜ 1) * crossEE k lab v₁ v₂ j₂ hne hj t := by
  apply (tensorEquiv k lab v₁ v₂ j₂ hne hj).injective
  have h1 : tensorEquiv k lab v₁ v₂ j₂ hne hj (pL k (moveLab lab v₂ j₂) v₁ j₂ r ⊗ₜ 1) =
      refineHom k (refines_joint_outer lab v₁ v₂ j₂) r := by
    simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
    rw [jointMap_tmul, map_one, mul_one, pL, refineHom_comp_apply]
  have hT : moveLab (moveLab lab v₂ j₂) v₁ j₂ v₁ = moveLab (moveLab lab v₂ j₂) v₁ j₂ v₂ := by
    rw [moveLab_self, moveLab, Function.update_of_ne hne.symm, moveLab_self]
  rw [tensorEquiv_crossEE, tE_mul, tE_mul, tensorEquiv_crossEE, h1]
  exact ddiffB_refineHom_mul _ _ hne _ hT _ _

end EE

/-! ### `Γ` of the crossing of two strands of distant colours -/

section Far

variable {k : Type*} [Field k] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*}
  [Fintype J] [DecidableEq J]

variable (k) in
/-- **Borel rings of two labellings with the same fibres are isomorphic** (mutual refinement). -/
def refineEquiv {J₁ J₂ : Type*} {l₁ : V → J₁} {l₂ : V → J₂} (h₁₂ : Refines l₂ l₁)
    (h₂₁ : Refines l₁ l₂) : BorelRing k l₁ ≃ₐ[k] BorelRing k l₂ :=
  AlgEquiv.ofAlgHom (refineHom k h₁₂) (refineHom k h₂₁)
    (AlgHom.ext fun z => by
      rw [AlgHom.comp_apply, refineHom_comp_apply, AlgHom.id_apply]
      obtain ⟨a, rfl⟩ := mkB_surjective l₂ z
      exact refineHom_mk _ a a rfl)
    (AlgHom.ext fun z => by
      rw [AlgHom.comp_apply, refineHom_comp_apply, AlgHom.id_apply]
      obtain ⟨a, rfl⟩ := mkB_surjective l₁ z
      exact refineHom_mk _ a a rfl)

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem jointLab_eq_iff {lab : V → J} {v₁ v₂ : V} (hne : v₁ ≠ v₂) {v w : V} :
    jointLab lab v₁ v₂ v = jointLab lab v₁ v₂ w ↔
      v = w ∨ (v ≠ v₁ ∧ v ≠ v₂ ∧ w ≠ v₁ ∧ w ≠ v₂ ∧ lab v = lab w) := by
  constructor
  · intro h
    by_cases hv1 : v = v₁
    · subst hv1; exact Or.inl (splitLab_singleton _ v w h.symm).symm
    by_cases hv2 : v = v₂
    · subst hv2; exact Or.inl (joint_singleton_right lab v₁ v hne w h.symm).symm
    by_cases hw1 : w = v₁
    · subst hw1; exact absurd (splitLab_singleton _ w v h) hv1
    by_cases hw2 : w = v₂
    · subst hw2; exact absurd (joint_singleton_right lab v₁ w hne v h) hv2
    simp only [jointLab, splitLab_of_ne hv1, splitLab_of_ne hw1, splitLab_of_ne hv2,
      splitLab_of_ne hw2, Option.some.injEq] at h
    exact Or.inr ⟨hv1, hv2, hw1, hw2, h⟩
  · rintro (rfl | ⟨hv1, hv2, hw1, hw2, h⟩)
    · rfl
    · simp only [jointLab, splitLab_of_ne hv1, splitLab_of_ne hw1, splitLab_of_ne hv2,
        splitLab_of_ne hw2, h]

omit [Fintype V] [Fintype J] [DecidableEq J] in
theorem refines_joint_swap {lab : V → J} {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    Refines (jointLab lab v₂ v₁) (jointLab lab v₁ v₂) := by
  intro v w h
  rw [jointLab_eq_iff hne.symm] at h
  rw [jointLab_eq_iff hne]
  rcases h with h | ⟨h1, h2, h3, h4, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, h1, h4, h3, h5⟩

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

variable (lab : V → J) (v₁ v₂ : V) (j₁ j₂ : J) (hne : v₁ ≠ v₂) (h₁ : lab v₁ ≠ j₂)
  (h₂ : lab v₂ ≠ j₁)

variable (k) in
/-- **`Γ` of the crossing `E_i E_j 1_k → E_j E_i 1_k` for distant colours** (KL III Definition 6.2,
eq. (6.8), `i · j = 0`): `ξ_i^{α₁} ⊗ ξ_j^{α₂} ↦ ξ_j^{α₂} ⊗ ξ_i^{α₁}`. Here `v₂` is moved to block
`j₂` first and then `v₁` to block `j₁` (`E_i E_j`), respectively `v₁` first and then `v₂`
(`E_j E_i`); both iterated flag varieties are partial flag varieties (`h₁`, `h₂`), with the
same Borel ring up to relabelling. -/
def crossFar (t : EERing (k := k) lab v₁ v₂ j₂) : EERing (k := k) lab v₂ v₁ j₁ :=
  (tensorEquiv k lab v₂ v₁ j₁ hne.symm h₂).symm
    (refineHom k (refines_joint_swap hne) (tensorEquiv k lab v₁ v₂ j₂ hne h₁ t))

theorem crossFar_xi (α₁ α₂ : ℕ) :
    crossFar k lab v₁ v₂ j₁ j₂ hne h₁ h₂
        ((xi k (moveLab lab v₂ j₂) v₁ ^ α₁) ⊗ₜ[BorelRing k (moveLab lab v₂ j₂)]
          (xi k lab v₂ ^ α₂)) =
      (xi k (moveLab lab v₁ j₁) v₂ ^ α₂) ⊗ₜ[BorelRing k (moveLab lab v₁ j₁)]
        (xi k lab v₁ ^ α₁) := by
  rw [crossFar, AlgEquiv.symm_apply_eq, tensorEquiv_xi, tensorEquiv_xi, map_mul, map_pow,
    map_pow, mul_comm]
  congr 2

/-- **The KLR relation `ψ_{ji} ψ_{ij} = 1` for distant colours** (KL III Definition 3.1, `i · j = 0`):
the two crossings are mutually inverse. -/
theorem crossFar_crossFar (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossFar k lab v₂ v₁ j₂ j₁ hne.symm h₂ h₁ (crossFar k lab v₁ v₂ j₁ j₂ hne h₁ h₂ t) = t := by
  simp only [crossFar, AlgEquiv.apply_symm_apply]
  rw [refineHom_comp_apply]
  obtain ⟨a, ha⟩ := mkB_surjective _ (tensorEquiv k lab v₁ v₂ j₂ hne h₁ t)
  rw [← ha, refineHom_mk _ a a rfl, ha, AlgEquiv.symm_apply_apply]

/-- `Γ` of the distant crossing is a map of right `H_k`-modules. -/
theorem crossFar_right (r : BorelRing k lab) (t : EERing (k := k) lab v₁ v₂ j₂) :
    crossFar k lab v₁ v₂ j₁ j₂ hne h₁ h₂ ((1 ⊗ₜ pR k lab v₂ r) * t) =
      (1 ⊗ₜ pR k lab v₁ r) * crossFar k lab v₁ v₂ j₁ j₂ hne h₁ h₂ t := by
  have e : ∀ (u₁ u₂ : V) (i₂ : J) (hu : u₁ ≠ u₂) (hi : lab u₁ ≠ i₂),
      tensorEquiv k lab u₁ u₂ i₂ hu hi (1 ⊗ₜ pR k lab u₂ r) =
        refineHom k (refines_joint_lab lab u₁ u₂) r := by
    intro u₁ u₂ i₂ hu hi
    simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
    rw [jointMap_tmul, map_one, one_mul, pR, pR, refineHom_comp_apply]
  rw [crossFar, crossFar, AlgEquiv.symm_apply_eq, map_mul, map_mul, map_mul,
    AlgEquiv.apply_symm_apply, e, e, refineHom_comp_apply]

end Far

end Categorification.Flag

end
