/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerTensor
import Categorification.WeightedKLR.RedStrands.BraidedRedOrder
import Categorification.TypeA.Cancellation
import Categorification.TypeA.Matsumoto

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: generators and congruences

Supporting material for Webster, arXiv:1309.3796v2, Lemma 6.5, which identifies the
bimodule `B̃_{w'} ⊗ B̃_w` with `B̃_{w'w}` when the lengths add. With the bimodules `B̃` modelled
as corners of the braided Stendhal algebra (`BraidedStendhalAlgebra.cornerSpace`), the tensor
product over the middle corner is the quotient `CornerTensor` of `A ⊗ A`.

This file sets up the comparison: it introduces the classes `gen x y` of `x ⊗ y` for `x, y` in
the KLR algebra, the subspaces `low n` spanned by `gen (ψ_α) (ψ_β x^p e(i))` with
`|α| + |β| ≤ n`, and shows that these exhaust the tensor product (`exists_mem_low`). The main
congruences are:

* `gen_append_eq`: a crossing word can be moved across the tensor sign as long as the middle
  red order is the one cut out by the middle idempotent;
* `gen_sub_mem_low_of_braidEquiv_left`, `gen_sub_mem_low_of_braidEquiv_right`: braid moves
  change `gen` only in lower degree;
* `gen_mem_low_of_hasRepeat_left`, `gen_mem_low_of_hasRepeat_right`: repeated letters lower
  the degree.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

/-! ### The idempotents `redIdem` -/

theorem redIdem_mul_e (κ : List (Fin ℓ)) (j : Seq μ) :
    (redIdem k Q Λ κ * KLRAlgebra.e j : R) = if redWord j = κ then KLRAlgebra.e j else 0 := by
  simp only [redIdem, Finset.sum_mul, KLRAlgebra.e_mul_e]
  rw [Finset.sum_ite_eq']
  simp

theorem e_mul_redIdem (κ : List (Fin ℓ)) (j : Seq μ) :
    (KLRAlgebra.e j * redIdem k Q Λ κ : R) = if redWord j = κ then KLRAlgebra.e j else 0 := by
  simp only [redIdem, Finset.mul_sum, KLRAlgebra.e_mul_e]
  rw [Finset.sum_ite_eq]
  simp

theorem redIdem_mul_redIdem (κ : List (Fin ℓ)) :
    (redIdem k Q Λ κ * redIdem k Q Λ κ : R) = redIdem k Q Λ κ := by
  nth_rewrite 2 [redIdem]
  rw [Finset.mul_sum]
  simp only [redIdem_mul_e]
  rw [Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_filter.1 hj).2]
  rfl

theorem redIdem_commute_pol (κ : List (Fin ℓ)) (p : MvPolynomial (Fin m) k) :
    Commute (redIdem k Q Λ κ : R) (KLRAlgebra.pol p) :=
  Commute.sum_left _ _ _ fun j _ => KLRAlgebra.e_commute_pol j p

omit [DecidableEq I] in
/-- The red labels of `s_c • j` are those of `j` when the strands at positions `c` and `c + 1`
of `j` are not both red. -/
theorem redWord_sadj_smul (j : Seq μ) {c : ℕ} (hc : c + 1 < m)
    (h : ¬ ((j.lbl ⟨c, by omega⟩).isRight ∧ (j.lbl ⟨c + 1, hc⟩).isRight)) :
    redWord (sadj m c • j) = redWord j := by
  have h1 := (redWord_smul_eq_iff j (sadj m c) 1).2 fun s t r r' hs ht => by
    have hs' : (s : ℕ) = c → (t : ℕ) ≠ c + 1 := fun h₁ h₂ => h ⟨by
      rw [show (⟨c, by omega⟩ : Fin m) = s from Fin.ext h₁.symm, hs]; rfl, by
      rw [show (⟨c + 1, hc⟩ : Fin m) = t from Fin.ext h₂.symm, ht]; rfl⟩
    have ht' : (t : ℕ) = c → (s : ℕ) ≠ c + 1 := fun h₁ h₂ => h ⟨by
      rw [show (⟨c, by omega⟩ : Fin m) = t from Fin.ext h₁.symm, ht]; rfl, by
      rw [show (⟨c + 1, hc⟩ : Fin m) = s from Fin.ext h₂.symm, hs]; rfl⟩
    simp only [Perm.coe_one, id, Fin.lt_def, sadj_val_of_lt hc]
    rcases swapNat_cases c s with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ <;>
      rcases swapNat_cases c t with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩ | ⟨h₄, h₅, h₆⟩ <;> omega
  rwa [one_smul] at h1

namespace BraidedStendhalAlgebra

variable (k Q Λ ν) in
/-- The image of the idempotent `redIdem κ` in the braided Stendhal algebra. -/
noncomputable def redProj (κ : List (Fin ℓ)) : BraidedStendhalAlgebra k Q Λ ν :=
  ofKLR k Q Λ ν (redIdem k Q Λ κ)

theorem isIdempotentElem_redProj (κ : List (Fin ℓ)) :
    IsIdempotentElem (redProj k Q Λ ν κ) := by
  rw [IsIdempotentElem, redProj, ← map_mul, redIdem_mul_redIdem]

variable (κ₂ κ₁ κ₀ : List (Fin ℓ))

local notation "CT" => CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂)
  (redProj k Q Λ ν κ₁) (redProj k Q Λ ν κ₀)

/-- The class of `x ⊗ y` in the tensor product over the middle corner, for `x, y` in the
KLR algebra. -/
noncomputable def gen (x y : R) : CT :=
  CornerTensor.tmul (ofKLR k Q Λ ν x) (ofKLR k Q Λ ν y)

/-- The classes `gen (ψ_α) (ψ_β x^p e(i))` with `|α| + |β| ≤ n`. -/
noncomputable def low (n : ℕ) : Submodule k CT :=
  Submodule.span k {t | ∃ (α β : List ℕ) (p : MvPolynomial (Fin m) k) (i : Seq μ),
    ValidWord m α ∧ ValidWord m β ∧ α.length + β.length ≤ n ∧
      t = gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i)}

variable {κ₂ κ₁ κ₀}

theorem low_mono {n n' : ℕ} (h : n ≤ n') :
    low (Q := Q) (Λ := Λ) (ν := ν) κ₂ κ₁ κ₀ n ≤ low κ₂ κ₁ κ₀ n' :=
  Submodule.span_mono fun _ ⟨α, β, p, i, hα, hβ, hl, ht⟩ => ⟨α, β, p, i, hα, hβ, hl.trans h, ht⟩

theorem gen_mem_low {α β : List ℕ} (hα : ValidWord m α) (hβ : ValidWord m β) {n : ℕ}
    (hn : α.length + β.length ≤ n) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ n :=
  Submodule.subset_span ⟨α, β, p, i, hα, hβ, hn, rfl⟩

@[simp] theorem gen_zero_left (y : R) : gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ 0 y = 0 := by
  simp [gen]

@[simp] theorem gen_zero_right (x : R) : gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x 0 = 0 := by
  simp [gen]

theorem gen_add_left (x x' y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (x + x') y = gen κ₂ κ₁ κ₀ x y + gen κ₂ κ₁ κ₀ x' y := by
  simp [gen, CornerTensor.tmul_add_left]

theorem gen_add_right (x y y' : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (y + y') = gen κ₂ κ₁ κ₀ x y + gen κ₂ κ₁ κ₀ x y' := by
  simp [gen, CornerTensor.tmul_add_right]

theorem gen_sub_left (x x' y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (x - x') y = gen κ₂ κ₁ κ₀ x y - gen κ₂ κ₁ κ₀ x' y := by
  simp [gen, CornerTensor.tmul_sub_left]

theorem gen_sub_right (x y y' : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (y - y') = gen κ₂ κ₁ κ₀ x y - gen κ₂ κ₁ κ₀ x y' := by
  simp [gen, CornerTensor.tmul_sub_right]

theorem gen_smul_left (r : k) (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (r • x) y = r • gen κ₂ κ₁ κ₀ x y := by
  simp [gen, CornerTensor.tmul_smul_left]

theorem gen_smul_right (r : k) (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (r • y) = r • gen κ₂ κ₁ κ₀ x y := by
  simp [gen, CornerTensor.tmul_smul_right]

/-- An element of the middle corner can be moved across the tensor sign. -/
theorem gen_mul_corner (x z y : R) (h₁ : redIdem k Q Λ κ₁ * z = z)
    (h₂ : z * redIdem k Q Λ κ₁ = z) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (x * z) y = gen κ₂ κ₁ κ₀ x (z * y) := by
  have hc : redProj k Q Λ ν κ₁ * ofKLR k Q Λ ν z * redProj k Q Λ ν κ₁ = ofKLR k Q Λ ν z := by
    rw [redProj, ← map_mul, ← map_mul, h₁, h₂]
  simp only [gen, map_mul]
  exact CornerTensor.tmul_balance_of hc _ _

/-- Right multiplication by the middle idempotent does not change `gen`. -/
theorem gen_mul_redIdem (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (x * redIdem k Q Λ κ₁) y = gen κ₂ κ₁ κ₀ x y := by
  have h := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₁
  simp only [gen, map_mul]
  rw [CornerTensor.tmul_corner (x := ofKLR k Q Λ ν x * _),
    CornerTensor.tmul_corner (x := ofKLR k Q Λ ν x)]
  congr 1
  simp only [mul_assoc]
  rw [show ofKLR k Q Λ ν (redIdem k Q Λ κ₁) = redProj k Q Λ ν κ₁ from rfl, h.eq]

theorem gen_mem_low_of_mem_filt_right {α : List ℕ} (hα : ValidWord m α) {b : ℕ} {y : R}
    (hy : y ∈ KLRAlgebra.filt k (stendhalQ Q Λ) μ b) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) y ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (α.length + b) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, p, i, hβ, hl, rfl⟩ := hy
    exact gen_mem_low hα hβ (by omega) p i
  | zero => simp
  | add y y' _ _ h h' => rw [gen_add_right]; exact add_mem h h'
  | smul r y _ h => rw [gen_smul_right]; exact Submodule.smul_mem _ r h

/-- **Elements of the filtration give elements of `low`.** If `x` has at most `a` crossings and
`y` at most `b`, then `x ⊗ y` lies in `low (a + b)`. -/
theorem gen_mem_low_of_mem_filt {a b : ℕ} {x y : R}
    (hx : x ∈ KLRAlgebra.filt k (stendhalQ Q Λ) μ a)
    (hy : y ∈ KLRAlgebra.filt k (stendhalQ Q Λ) μ b) :
    gen κ₂ κ₁ κ₀ x y ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, p, j, hα, hl, rfl⟩ := hx
    rw [← gen_mul_redIdem, mul_assoc, e_mul_redIdem]
    split_ifs with hj
    · have h₁ : redIdem k Q Λ κ₁ * (KLRAlgebra.pol p * KLRAlgebra.e j) =
          KLRAlgebra.pol p * KLRAlgebra.e j := by
        rw [← mul_assoc, (redIdem_commute_pol κ₁ p).eq, mul_assoc, redIdem_mul_e, ite_eq_left hj]
      have h₂ : KLRAlgebra.pol p * KLRAlgebra.e j * redIdem k Q Λ κ₁ =
          KLRAlgebra.pol p * KLRAlgebra.e j := by
        rw [mul_assoc, e_mul_redIdem, ite_eq_left hj]
      rw [mul_assoc, gen_mul_corner _ _ _ h₁ h₂]
      refine low_mono (n := α.length + b) (by omega) (gen_mem_low_of_mem_filt_right hα ?_)
      rw [mul_assoc]
      exact KLRAlgebra.pol_mul_mem p (KLRAlgebra.e_mul_mem j hy)
    · simp
  | zero => simp
  | add x x' _ _ h h' => rw [gen_add_left]; exact add_mem h h'
  | smul r x _ h => rw [gen_smul_left]; exact Submodule.smul_mem _ r h

/-- Every element of the tensor product lies in some `low n`. -/
theorem exists_mem_low (t : CT) : ∃ n, t ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ n := by
  induction t using CornerTensor.induction_on with
  | tmul x y =>
    obtain ⟨x, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) x
    obtain ⟨y, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) y
    obtain ⟨a, ha⟩ := KLRAlgebra.exists_mem_filt x
    obtain ⟨b, hb⟩ := KLRAlgebra.exists_mem_filt y
    exact ⟨a + b, gen_mem_low_of_mem_filt ha hb⟩
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, add_mem (low_mono (by omega) ha) (low_mono (by omega) hb)⟩

/-! ### Moving crossings across the tensor sign -/

/-- **Moving a word of crossings across the tensor sign.** If `y = e(j) y`, the red strands of
`j` read `κ₁` and so do those of `γ • j`, then `ψ_α ψ_γ ⊗ y = ψ_α ⊗ ψ_γ y`. -/
theorem gen_mul_ψw_eq (x : R) (γ : List ℕ) {j : Seq μ} {y : R}
    (hy : KLRAlgebra.e j * y = y) (hj : redWord j = κ₁)
    (hj' : redWord (wordProd m γ • j) = κ₁) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (x * KLRAlgebra.ψw γ) y =
      gen κ₂ κ₁ κ₀ x (KLRAlgebra.ψw γ * y) := by
  have he₁ : redIdem k Q Λ κ₁ * KLRAlgebra.e j = KLRAlgebra.e j := by
    rw [redIdem_mul_e, ite_eq_left hj]
  have he₂ : KLRAlgebra.e j * redIdem k Q Λ κ₁ = KLRAlgebra.e j := by
    rw [e_mul_redIdem, ite_eq_left hj]
  have hψ : (KLRAlgebra.ψw γ * KLRAlgebra.e j : R) =
      KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ * KLRAlgebra.e j := by
    conv_lhs => rw [← KLRAlgebra.e_mul_e j j |>.trans (ite_eq_left rfl)]
    rw [← mul_assoc, KLRAlgebra.ψw_mul_e]
  have hz₁ : redIdem k Q Λ κ₁ * (KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ *
      KLRAlgebra.e j) = KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ * KLRAlgebra.e j := by
    rw [← mul_assoc, ← mul_assoc, redIdem_mul_e, ite_eq_left hj']
  have hz₂ : KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ * KLRAlgebra.e j *
      redIdem k Q Λ κ₁ = KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ * KLRAlgebra.e j := by
    rw [mul_assoc, he₂]
  calc gen κ₂ κ₁ κ₀ (x * KLRAlgebra.ψw γ) y
      = gen κ₂ κ₁ κ₀ (x * KLRAlgebra.ψw γ) (KLRAlgebra.e j * y) := by rw [hy]
    _ = gen κ₂ κ₁ κ₀ (x * KLRAlgebra.ψw γ * KLRAlgebra.e j) y := by
        rw [gen_mul_corner _ _ _ he₁ he₂]
    _ = gen κ₂ κ₁ κ₀ (x * (KLRAlgebra.e (wordProd m γ • j) * KLRAlgebra.ψw γ *
          KLRAlgebra.e j)) y := by rw [mul_assoc x, hψ]
    _ = gen κ₂ κ₁ κ₀ x (KLRAlgebra.ψw γ * y) := by
        rw [gen_mul_corner _ _ _ hz₁ hz₂, ← hψ, mul_assoc, hy]

/-- `gen_mul_ψw_eq` for words of crossings applied to a basis vector. -/
theorem gen_append_eq (α γ β : List ℕ) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord (wordProd m β • i) = κ₁) (h' : redWord (wordProd m (γ ++ β) • i) = κ₁) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (KLRAlgebra.ψw (α ++ γ))
        (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) =
      gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α)
        (KLRAlgebra.ψw (γ ++ β) * KLRAlgebra.pol p * KLRAlgebra.e i) := by
  simp only [KLRAlgebra.ψw_append, mul_assoc]
  refine gen_mul_ψw_eq _ γ (j := wordProd m β • i) ?_ h ?_
  · rw [← mul_assoc, KLRAlgebra.e_mul_ψw, inv_smul_smul, mul_assoc, ← mul_assoc (KLRAlgebra.e i),
      (KLRAlgebra.e_commute_pol i p).eq, mul_assoc (KLRAlgebra.pol p), KLRAlgebra.e_mul_e,
      ite_eq_left (Eq.refl i)]
  · rwa [← mul_smul, ← wordProd_append]

/-! ### Braid moves and repeated letters -/

theorem gen_sub_mem_low_of_braidEquiv_left {α α' β : List ℕ} (h : BraidEquiv α α')
    (hα : ValidWord m α) (hβ : ValidWord m β) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) -
        gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α') (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (α.length + β.length - 1) := by
  rw [← gen_sub_left]
  by_cases hne : α = []
  · subst hne
    have : α' = [] := List.length_eq_zero_iff.1 (h.length_eq.symm.trans List.length_nil)
    simp [this]
  have hx := KLRAlgebra.sub_mem_of_braidEquiv h (KLRAlgebra.one_mem_filt (Q := stendhalQ Q Λ)
    (ν := μ) 0)
  simp only [mul_one, add_zero] at hx
  have hl := List.length_pos_of_ne_nil hne
  exact low_mono (by omega) (gen_mem_low_of_mem_filt hx
    (KLRAlgebra.mem_filt hβ le_rfl p i))

theorem gen_sub_mem_low_of_braidEquiv_right {α β β' : List ℕ} (h : BraidEquiv β β')
    (hα : ValidWord m α) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) -
        gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β' * KLRAlgebra.pol p * KLRAlgebra.e i) ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (α.length + β.length - 1) := by
  rw [← gen_sub_right]
  by_cases hne : β = []
  · subst hne
    have : β' = [] := List.length_eq_zero_iff.1 (h.length_eq.symm.trans List.length_nil)
    simp [this]
  have hy := KLRAlgebra.sub_mul_mem_of_braidEquiv (Q := stendhalQ Q Λ) h p i
  rw [sub_mul, sub_mul] at hy
  have hl := List.length_pos_of_ne_nil hne
  exact low_mono (by omega) (gen_mem_low_of_mem_filt_right hα hy)

theorem gen_mem_low_of_hasRepeat_left {α β : List ℕ} (h : HasRepeat α) (hβ : ValidWord m β)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (α.length + β.length - 1) := by
  have hx := KLRAlgebra.mul_mem_of_hasRepeat h (KLRAlgebra.one_mem_filt (Q := stendhalQ Q Λ)
    (ν := μ) 0)
  simp only [mul_one, add_zero] at hx
  obtain ⟨α₁, α₂, a, rfl⟩ := h
  exact low_mono (by simp; omega) (gen_mem_low_of_mem_filt hx
    (KLRAlgebra.mem_filt hβ le_rfl p i))

theorem gen_mem_low_of_hasRepeat_right {α β : List ℕ} (h : HasRepeat β) (hα : ValidWord m α)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (α.length + β.length - 1) := by
  have hy := KLRAlgebra.gen_mem_of_hasRepeat (Q := stendhalQ Q Λ) h p i
  obtain ⟨β₁, β₂, a, rfl⟩ := h
  exact low_mono (by simp; omega) (gen_mem_low_of_mem_filt_right hα hy)

end BraidedStendhalAlgebra

end Categorification.Stendhal
