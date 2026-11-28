/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockPairing

/-!
# Induction from the left is coinduction from the right

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the identity (IC), at `ℓ = 0`. Let
`A = T̃^{λ⁺}`, `D = T̃^λ ⊗ T̃^{(μ,μ*)}`, `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ`, `e_L`, `e_R` the idempotents of
the two block orders and `c : A → D` the trace (`blockTrace`). Then

  `Θ : e_L A → Hom_{D_R}(A e_R, D)`, `Θ(z)(y) = c(z y)`,

is bijective (`existsUnique_blockTrace_mul_eq`), where `D` is a right `D_R`-module through the
exchange of the factors: every map `F : A → D` with `F(y ι_R(d')) = F(y) swap(d')` is
`y ↦ c(z y)` for exactly one `z ∈ e_L A`. Since `c(z y) = c(z y e_R)`, this is Θ on `A e_R`.

Proof. Pair the left basis `γ_c` of `e_L A` (`c = (e(i), j, u)`) with
the right basis `flip(γ_{c'})` of `A e_R` (`c' = (i', j', u')`). Each `c` has a partner
`c' = (i, j, w_L⁻¹ u)` (`frontPartner`), each `c'` a partner `(e(i'), j', w_L u')`
(`basePartner`), with the same bottom, and `ℓ(w_L u') + ℓ(u') = ℓ(w_L)`. By
`blockTrace_genElt_mul_flip_genEltF`, ordering by `ℓ(u)` the matrix `c(γ_c flip(γ_{c'}))` is
unitriangular with `1_c` on the diagonal.

* Injectivity (`eq_zero_of_blockTrace_mul_flip_genEltF`): for `z = ∑ ι(d_c) γ_c ≠ 0`, take `c₀`
  with `d_{c₀} ≠ 0` and `ℓ(u)` maximal; then `c(z flip(γ_{c₀'})) = d_{c₀}`.
* Surjectivity (`exists_blockTrace_mul_eq`): solve `c(z flip(γ_{c'})) = F(flip(γ_{c'}))` by
  induction on `ℓ(u')`, correcting `z` by `∑ ι(δ_{c'}) γ_{c'}` over the partners of level `n`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.

## Main definitions

* `CupCap.frontPartner`, `CupCap.basePartner`: the diagonal of the matrix.

## Main results

* `CupCap.eq_zero_of_blockTrace_mul_flip_genEltF`, `CupCap.exists_blockTrace_mul_eq`.
* `CupCap.existsUnique_blockTrace_mul_eq`: (IC), Θ is bijective.
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
local notation "hM" => m_add_N_end (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)
local notation "hK" => N_add_m_front (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}

/-! ### The partners -/

section Partners

omit [DecidableEq I] in
theorem val_inv_wL
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m) (a : Fin M) :
    (d⁻¹ a).val = if a.val < m then N + a.val else a.val - m := by
  split_ifs with ha
  · rw [inv_wL_of_lt hd hcd a ha]
  · rw [inv_wL_of_ge hd hcd a (not_lt.1 ha)]

omit [DecidableEq I] in
/-- `w_L⁻¹ u` is a shuffle for the blocks `(N, m)` if `u` is one for `(m, N)`. -/
theorem isShuffle_inv_wL_mul
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    {u : Perm (Fin M)} (hu : IsShuffle hM u) :
    IsShuffle hK (d⁻¹ * u) := by
  have hMN := hM
  refine (isShuffle_iff_forall hK).2 fun j hj hb => ?_
  rw [mul_inv_rev, inv_inv, Perm.mul_apply, Perm.mul_apply]
  have h1 : (d ⟨j, by omega⟩).val = if j < N then j + m else j - N := val_wL hd hcd _
  have h2 : (d ⟨j + 1, hj⟩).val = if j + 1 < N then j + 1 + m else j + 1 - N := val_wL hd hcd _
  have hxy : (d ⟨j, by omega⟩).val < m ↔ (d ⟨j + 1, hj⟩).val < m := by
    rw [h1, h2]
    split_ifs <;> omega
  refine (hu.inv_lt_inv_iff hM hxy).2 ?_
  rw [Fin.lt_def, h1, h2]
  split_ifs <;> omega

omit [DecidableEq I] in
/-- `w_L u'` is a shuffle for the blocks `(m, N)` if `u'` is one for `(N, m)`. -/
theorem isShuffle_wL_mul
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    {u : Perm (Fin M)} (hu : IsShuffle hK u) : IsShuffle hM (d * u) := by
  have hMN := hM
  refine (isShuffle_iff_forall hM).2 fun j hj hb => ?_
  rw [mul_inv_rev, Perm.mul_apply, Perm.mul_apply]
  have h1 : (d⁻¹ ⟨j, by omega⟩).val = if j < m then N + j else j - m := val_inv_wL hd hcd _
  have h2 : (d⁻¹ ⟨j + 1, hj⟩).val = if j + 1 < m then N + (j + 1) else j + 1 - m :=
    val_inv_wL hd hcd _
  have hxy : (d⁻¹ ⟨j, by omega⟩).val < N ↔ (d⁻¹ ⟨j + 1, hj⟩).val < N := by
    rw [h1, h2]
    split_ifs <;> omega
  refine (hu.inv_lt_inv_iff hK hxy).2 ?_
  rw [Fin.lt_def, h1, h2]
  split_ifs <;> omega

/-- The front partner `(i, j, w_L⁻¹ u)` of a base generator `(e(i), j, u)`. -/
def frontPartner
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (c : BaseGen ν₀ ρ₁) : FrontGen 0 ν ν₀ :=
  ⟨(c.1.1.1.1.1, c.1.1.2.1, ⟨d⁻¹ * c.1.1.2.2.1, isShuffle_inv_wL_mul hd hcd c.1.1.2.2.2⟩),
    c.1.1.1.2.1, c.1.2.1, by
      change IsRedOrdered ((d⁻¹ * c.1.1.2.2.1)⁻¹ • frontSeq c.1.1.1.1.1 c.1.1.2.1)
      rw [mul_inv_rev, inv_inv, mul_smul, smul_frontSeq_eq_endSeq hd hcd]
      exact c.1.2.2⟩

omit [DecidableEq I] in
theorem frontPartner_bot
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (c : BaseGen ν₀ ρ₁) : (frontPartner hd hcd c).bot = c.1.bot := by
  change (d⁻¹ * c.1.1.2.2.1)⁻¹ • frontSeq c.1.1.1.1.1 c.1.1.2.1 =
    c.1.1.2.2.1⁻¹ • endSeq c.1.1.1.1.1 c.1.1.2.1
  rw [mul_inv_rev, inv_inv, mul_smul, smul_frontSeq_eq_endSeq hd hcd]

omit [DecidableEq I] in
theorem frontPartner_perm
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (c : BaseGen ν₀ ρ₁) :
    (frontPartner hd hcd c).1.2.2.1 = d⁻¹ * c.1.1.2.2.1 := rfl

/-- The base partner `(e(i'), j', w_L u')` of a front generator `(i', j', u')`. -/
def basePartner
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (c' : FrontGen 0 ν ν₀) : BaseGen ν₀ ρ₁ :=
  ⟨⟨(⟨(c'.1.1, 1, 0), isTopTerm_base hρ₁ c'.2.1⟩, c'.1.2.1,
      ⟨d * c'.1.2.2.1, isShuffle_wL_mul hd hcd c'.1.2.2.2⟩), c'.2.2.1, by
    change IsRedOrdered ((d * c'.1.2.2.1)⁻¹ • endSeq c'.1.1 c'.1.2.1)
    rw [mul_inv_rev, mul_smul, ← smul_frontSeq_eq_endSeq hd hcd, inv_smul_smul]
    exact c'.2.2.2⟩, rfl⟩

omit [DecidableEq I] in
theorem basePartner_bot
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (c' : FrontGen 0 ν ν₀) : (basePartner hd hcd hρ₁ c').1.bot = c'.bot := by
  change (d * c'.1.2.2.1)⁻¹ • endSeq c'.1.1 c'.1.2.1 = c'.1.2.2.1⁻¹ • frontSeq c'.1.1 c'.1.2.1
  rw [mul_inv_rev, mul_smul, ← smul_frontSeq_eq_endSeq hd hcd, inv_smul_smul]

omit [DecidableEq I] in
theorem basePartner_perm
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (c' : FrontGen 0 ν ν₀) :
    (basePartner hd hcd hρ₁ c').1.1.2.2.1 = d * c'.1.2.2.1 := rfl

theorem blockIdem_basePartner
    {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
      wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
    (c' : FrontGen 0 ν ν₀) :
    blockIdem Q Λ Λc (basePartner hd hcd hρ₁ c') =
      TensorProduct.comm k Tc T (blockIdemF Q Λ Λc c') := by
  rw [blockIdemF, TensorProduct.comm_tmul]
  rfl

end Partners

omit [DecidableEq I] in
/-- A base generator is determined by its bottom and its shuffle. -/
theorem baseGen_ext {c₁ c₂ : BaseGen ν₀ ρ₁} (hb : c₁.1.bot = c₂.1.bot)
    (hu : c₁.1.1.2.2.1 = c₂.1.1.2.2.1) : c₁ = c₂ := by
  have h1 : endSeq c₁.1.1.1.1.1 c₁.1.1.2.1 = endSeq c₂.1.1.1.1.1 c₂.1.1.2.1 := by
    rw [← smul_bot c₁.1, ← smul_bot c₂.1, hb, hu]
  obtain ⟨hi, hj⟩ := endSeq_injective h1
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (Prod.ext hi (c₁.2.trans c₂.2.symm)))
    (Prod.ext hj (Subtype.ext hu))

omit [DecidableEq I] in
/-- A front generator is determined by its bottom and its shuffle. -/
theorem frontGen_ext {c₁ c₂ : FrontGen 0 ν ν₀} (hb : c₁.bot = c₂.bot)
    (hu : c₁.1.2.2.1 = c₂.1.2.2.1) : c₁ = c₂ := by
  have h1 : frontSeq c₁.1.1 c₁.1.2.1 = frontSeq c₂.1.1 c₂.1.2.1 := by
    rw [← smul_frontBot c₁, ← smul_frontBot c₂, hb, hu]
  obtain ⟨hi, hj⟩ := frontSeq_injective h1
  exact Subtype.ext (Prod.ext hi (Prod.ext hj (Subtype.ext hu)))

/-! ### Bijectivity of Θ -/

variable [DecidableEq (EndGen ν₀ ρ₁)]

section Pairing

variable (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

/-- **Θ is injective**: if `z ∈ e_L A` and `c(z flip(γ_{c'})) = 0` for every front generator
`c'`, then `z = 0`. -/
theorem eq_zero_of_blockTrace_mul_flip_genEltF {z : Tp}
    (hz : endStendhal Q Λ Λc ν ν₀ 1 * z = z)
    (h : ∀ c' : FrontGen 0 ν ν₀, blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃
      (z * StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c')) = 0) : z = 0 := by
  classical
  have hMN := hM
  obtain ⟨d, hd, hcd⟩ := (exists_isDoubleShuffle_iff hM hK m).2 ⟨by omega, le_rfl, le_rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, blockSum Q Λ Λc ρ₁ ρ₃ a = z :=
    ⟨(blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm (endProj Q Λ Λc ν ν₀ z), by
      rw [← blockSumEquiv_apply hQ hρ₁ hρ₂ hρ₃, LinearEquiv.apply_symm_apply, endProj_apply,
        hz]⟩
  subst ha
  suffices a = 0 by rw [this, map_zero]
  by_contra ha0
  have hne : a.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, DFinsupp.support_eq_empty]
    exact ha0
  obtain ⟨a₀, ha₀, hmax⟩ := a.support.exists_max_image (fun c => length M c.1.1.2.2.1) hne
  have hsum : blockSum Q Λ Λc ρ₁ ρ₃ a = ∑ c ∈ a.support,
      blockTensor Q Λ Λc ν ν₀ (a c) * genElt Q Λ Λc ρ₁ ρ₃ c.1 := by
    conv_lhs => rw [← DFinsupp.sum_single (f := a)]
    rw [DFinsupp.sum, map_sum]
    simp only [blockSum_single]
  have hl₀ := length_mul_add_length hM hK hd hcd (isShuffle_inv_wL_mul hd hcd a₀.1.1.2.2.2)
  rw [mul_inv_cancel_left] at hl₀
  have key := h (frontPartner hd hcd a₀)
  rw [hsum, Finset.sum_mul, map_sum] at key
  simp only [mul_assoc, blockTrace_blockTensor_mul] at key
  rw [Finset.sum_eq_single a₀] at key
  · rw [blockTrace_genElt_mul_flip_genEltF hQ hρ₁ hρ₂ hρ₃ hd hcd _ _ (by
        rw [frontPartner_perm]; omega),
      ite_eq_left ⟨(frontPartner_bot hd hcd a₀).symm, by
        rw [frontPartner_perm, mul_inv_rev, inv_inv, mul_inv_cancel_left]⟩,
      mem_blockLeft.1 (a a₀).2] at key
    exact (DFinsupp.mem_support_iff.1 ha₀) (Subtype.ext key)
  · intro c hc hca
    have hlc := hmax c hc
    rw [blockTrace_genElt_mul_flip_genEltF hQ hρ₁ hρ₂ hρ₃ hd hcd _ _ (by
        rw [frontPartner_perm]; omega),
      ite_eq_right, mul_zero]
    rintro ⟨hb, hu⟩
    apply hca
    refine baseGen_ext (hb.trans (frontPartner_bot hd hcd a₀)) ?_
    rw [frontPartner_perm] at hu
    exact (eq_mul_of_mul_inv_eq hu).trans (mul_inv_cancel_left d _)
  · intro h0
    exact absurd ha₀ h0

/-- **Θ is surjective**: every map `F : A → D` with `F(y ι_R(d')) = F(y) swap(d')` is
`y ↦ c(z y)` for some `z ∈ e_L A`. -/
theorem exists_blockTrace_mul_eq (F : Tp →ₗ[k] T ⊗[k] Tc)
    (hF : ∀ (y : Tp) (d' : Tc ⊗[k] T),
      F (y * blockTensorR Q Λ Λc ν ν₀ d') = F y * TensorProduct.comm k Tc T d') :
    ∃ z : Tp, endStendhal Q Λ Λc ν ν₀ 1 * z = z ∧
      ∀ y : Tp, blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (z * y) = F y := by
  classical
  have hMN := hM
  obtain ⟨d, hd, hcd⟩ := (exists_isDoubleShuffle_iff hM hK m).2 ⟨by omega, le_rfl, le_rfl⟩
  let _ : Fintype (FrontGen 0 ν ν₀) := Fintype.ofFinite _
  obtain ⟨C, hC⟩ : ∃ C, C = blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : FrontGen 0 ν ν₀ → Tp,
      ∀ c', StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') = g c' := ⟨_, fun _ => rfl⟩
  rw [← hC]
  have hCL : ∀ x z, C (blockTensor Q Λ Λc ν ν₀ x * z) = x * C z := fun x z => by
    rw [hC]; exact blockTrace_blockTensor_mul hQ hρ₁ hρ₂ hρ₃ x z
  have hCR : ∀ z d', C (z * blockTensorR Q Λ Λc ν ν₀ d') =
      C z * TensorProduct.comm k Tc T d' := fun z d' => by
    rw [hC]; exact blockTrace_mul_blockTensorR hQ hρ₁ hρ₂ hρ₃ z d'
  have hCE : ∀ (c : BaseGen ν₀ ρ₁) (c' : FrontGen 0 ν ν₀),
      length M c.1.1.2.2.1 + length M c'.1.2.2.1 ≤ length M d →
      C (genElt Q Λ Λc ρ₁ ρ₃ c.1 * g c') =
        if c.1.bot = c'.bot ∧ c.1.1.2.2.1 * (c'.1.2.2.1)⁻¹ = d then blockIdem Q Λ Λc c
        else 0 := fun c c' hl => by
    rw [hC, ← hg]; exact blockTrace_genElt_mul_flip_genEltF hQ hρ₁ hρ₂ hρ₃ hd hcd c c' hl
  have hgI : ∀ c', g c' * blockTensorR Q Λ Λc ν ν₀ (blockIdemF Q Λ Λc c') = g c' := by
    intro c'
    have h1 : blockTensorR Q Λ Λc ν ν₀ (blockIdemF Q Λ Λc c') * genEltF Q Λ Λc ρ₃ c' =
        genEltF Q Λ Λc ρ₃ c' := by
      rw [blockIdemF, blockTensorR_tmul, mul_assoc, suffixStendhal_e_mul_genEltF,
        frontStendhal_e_mul_genEltF]
    have h2 := congrArg StendhalAlgebra.flip h1
    rw [StendhalAlgebra.flip_mul, flip_blockTensorR, flipDF_blockIdemF, hg] at h2
    exact h2
  have hidF : ∀ c', F (g c') * blockIdem Q Λ Λc (basePartner hd hcd hρ₁ c') = F (g c') := by
    intro c'
    rw [blockIdem_basePartner, ← hF, hgI]
  have hidC : ∀ (z : Tp) (c' : FrontGen 0 ν ν₀),
      C (z * g c') * blockIdem Q Λ Λc (basePartner hd hcd hρ₁ c') = C (z * g c') := by
    intro z c'
    rw [blockIdem_basePartner, ← hCR, mul_assoc, hgI]
  have hsm : ∀ x y w : T ⊗[k] Tc, (x - y) * w = x * w - y * w := fun x y w => sub_mul x y w
  have step : ∀ n : ℕ, ∃ z : Tp, endStendhal Q Λ Λc ν ν₀ 1 * z = z ∧
      ∀ c' : FrontGen 0 ν ν₀, length M c'.1.2.2.1 < n → C (z * g c') = F (g c') := by
    intro n
    induction n with
    | zero => exact ⟨0, mul_zero _, fun c' h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨z, hz, hzc⟩ := ih
      let S := Finset.univ.filter fun c' : FrontGen 0 ν ν₀ => length M c'.1.2.2.1 = n
      refine ⟨z + ∑ c' ∈ S, blockTensor Q Λ Λc ν ν₀ (F (g c') - C (z * g c')) *
        genElt Q Λ Λc ρ₁ ρ₃ (basePartner hd hcd hρ₁ c').1, ?_, ?_⟩
      · rw [mul_add, hz, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [← mul_assoc, endStendhal_one_mul_blockTensor]
      · intro c'' hc''
        have hentry : ∀ c' ∈ S, C (blockTensor Q Λ Λc ν ν₀ (F (g c') - C (z * g c')) *
            genElt Q Λ Λc ρ₁ ρ₃ (basePartner hd hcd hρ₁ c').1 * g c'') =
              if c'' = c' then F (g c'') - C (z * g c'') else 0 := by
          intro c' hc'
          have hn : length M c'.1.2.2.1 = n := (Finset.mem_filter.1 hc').2
          have hl := length_mul_add_length hM hK hd hcd c'.1.2.2.2
          rw [mul_assoc, hCL, hCE _ _ (by rw [basePartner_perm]; omega)]
          by_cases hcc : c'' = c'
          · subst hcc
            rw [ite_eq_left ⟨basePartner_bot hd hcd hρ₁ c'', by
                rw [basePartner_perm, mul_inv_cancel_right]⟩, ite_eq_left rfl, hsm, hidF,
              hidC]
          · rw [ite_eq_right hcc, ite_eq_right, mul_zero]
            rintro ⟨hb, hu⟩
            apply hcc
            rw [basePartner_perm] at hu
            have h2 : c'.1.2.2.1 * (c''.1.2.2.1)⁻¹ = 1 := by
              have := congrArg (fun x => d⁻¹ * x) hu
              simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel] at this
              exact this
            exact frontGen_ext (hb.symm.trans (basePartner_bot hd hcd hρ₁ c'))
              (mul_inv_eq_one.1 h2).symm
        rw [add_mul, map_add, Finset.sum_mul, map_sum, Finset.sum_congr rfl hentry]
        by_cases hn : length M c''.1.2.2.1 = n
        · have hmem : c'' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hn⟩
          have hs : (∑ c' ∈ S, if c'' = c' then F (g c'') - C (z * g c'') else 0) =
              F (g c'') - C (z * g c'') :=
            (Finset.sum_eq_single_of_mem c'' hmem fun b _ hb => ite_eq_right (Ne.symm hb)).trans
              (ite_eq_left rfl)
          refine (congrArg (fun t => C (z * g c'') + t) hs).trans ?_
          show C (z * g c'') + (F (g c'') - C (z * g c'')) = F (g c'')
          abel
        · have hs : (∑ c' ∈ S, if c'' = c' then F (g c'') - C (z * g c'') else 0) = 0 :=
            Finset.sum_eq_zero fun b hb => ite_eq_right fun h => hn (by
              subst h; exact (Finset.mem_filter.1 hb).2)
          refine (congrArg (fun t => C (z * g c'') + t) hs).trans ?_
          show C (z * g c'') + 0 = F (g c'')
          rw [add_zero]
          exact hzc c'' (by omega)
  obtain ⟨z, hz, hzc⟩ := step (length M d + 1)
  have hall : ∀ c', C (z * g c') = F (g c') := fun c' => hzc c' (by
    have := length_mul_add_length hM hK hd hcd c'.1.2.2.2; omega)
  have hcomm1 : TensorProduct.comm k Tc T 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.comm_tmul, Algebra.TensorProduct.one_def]
  refine ⟨z, hz, fun y => ?_⟩
  have e1 : C (z * y) = C (z * (y * blockTensorR Q Λ Λc ν ν₀ 1)) := by
    rw [← mul_assoc, hCR, hcomm1, mul_one]
  have e2 : F y = F (y * blockTensorR Q Λ Λc ν ν₀ 1) := by rw [hF, hcomm1, mul_one]
  rw [e1, e2]
  have hmem : y * blockTensorR Q Λ Λc ν ν₀ 1 ∈ LinearMap.range (blockSumRF Q Λ Λc ρ₃) := by
    rw [mem_range_blockSumRF_iff (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃, mul_assoc, blockTensorR_one,
      ← map_mul, one_mul]
  obtain ⟨b, hb⟩ := hmem
  rw [← hb]
  clear hb
  induction b using DFinsupp.induction with
  | h0 => rw [map_zero, mul_zero, map_zero, map_zero]
  | ha c' x f _ _ ih =>
    rw [map_add, mul_add, map_add, map_add, ih, blockSumRF_single, hg, ← mul_assoc, hCR, hF,
      hall]

/-- **(IC): Θ is bijective.** Every map `F : A → D` with `F(y ι_R(d')) = F(y) swap(d')` is
`y ↦ c(z y)` for exactly one `z ∈ e_L A`. -/
theorem existsUnique_blockTrace_mul_eq (F : Tp →ₗ[k] T ⊗[k] Tc)
    (hF : ∀ (y : Tp) (d' : Tc ⊗[k] T),
      F (y * blockTensorR Q Λ Λc ν ν₀ d') = F y * TensorProduct.comm k Tc T d') :
    ∃! z : Tp, endStendhal Q Λ Λc ν ν₀ 1 * z = z ∧
      ∀ y : Tp, blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (z * y) = F y := by
  obtain ⟨z, hz, hzF⟩ := exists_blockTrace_mul_eq hQ hρ₁ hρ₂ hρ₃ F hF
  refine ⟨z, ⟨hz, hzF⟩, fun z' ⟨hz', hz'F⟩ => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_blockTrace_mul_flip_genEltF hQ hρ₁ hρ₂ hρ₃ (by rw [mul_sub, hz, hz'])
    fun c' => ?_
  rw [sub_mul, map_sub, hzF, hz'F, sub_self]

end Pairing

end Categorification.Stendhal.CupCap
