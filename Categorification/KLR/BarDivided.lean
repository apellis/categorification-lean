/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BarGamma

/-!
# Bar-invariance of the divided-power projectives `P_i`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5 (TeX lines ~1533–1541 and ~1600–1660): for a
divided-power expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` the paper sets
`P_i = R(ν) ψ(1_i) {-⟨i⟩}` and states `P̄_i ≅ P_i`. We prove the `K₀` form of this,
`\overline{[P_i]} = [P_i]` (`KL1.bar_projDiv`), for the KL I grading.

The idempotent `1_i` is `x^δ ψ_{w_0} 1_î` (one nilHecke idempotent per block), and
`ψ(1_i) = ψ_{w_0} x^δ 1_î`: this uses that `ψ_{w_0}` does not depend on the reduced word on a
block of equal labels, so that its reversal (the image under `ψ`) is again `ψ_{w_0}`
(`KLRAlgebra.ψw_blockWord_reverse_mul_e`, from the nilHecke ring, where
`∂_{w_0}` is independent of the reduced word and `w_0⁻¹ = w_0`, `NilHecke.longest_inv`). Hence
`1_i = x y` and `ψ(1_i) = y x` with `x = x^δ 1_î` of degree `2⟨i⟩` and `y = ψ_{w_0} 1_î` of
degree `-2⟨i⟩` (`KLRAlgebra.mul_divY_divX`), so `[R(ν) 1_i] = q^{-2⟨i⟩} [R(ν) ψ(1_i)]`
(`KL1.K0_of_divIdem`), and

`\overline{[P_i]} = q^{⟨i⟩} [R(ν) 1_i] = q^{-⟨i⟩} [R(ν) ψ(1_i)] = [P_i]`.

## Main results

* `NilHecke.longest_inv` : `w_0⁻¹ = w_0` (a permutation with `m choose 2` inversions reverses
  the order, `NilHecke.eq_rev_of_strictAnti`).
* `KLR.NilHecke.IsNilHeckeFamily.prod_reverse_w0Word` : in any nilHecke family,
  `∂_{w_0}` is unchanged by reversing the reduced word `w0Word n`.
* `KLRAlgebra.ψw_blockWord_reverse_mul_e` : `ψ_{w_0}^{rev} 1_i = ψ_{w_0} 1_i` on a block.
* `KLRAlgebra.hflip_divIdem` : `ψ(1_i) = y x`, `KLRAlgebra.divX_mul_divY` : `1_i = x y`.
* `KL1.K0_of_divIdem` : `[R(ν) 1_i] = q^{-2⟨i⟩} [R(ν) ψ(1_i)]`.
* `KL1.bar_projDiv` : **`\overline{[P_i]} = [P_i]`**; `KLGamma.barR_clsDiv` in `K₀(R)`.
-/

noncomputable section

namespace Categorification

open Equiv TypeA

/-! ### `w_0⁻¹ = w_0` -/

namespace NilHecke

theorem card_filter_lt_le_choose (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).filter fun p => p.1 < p.2).card ≤ m.choose 2 := by
  classical
  have ht : ((Finset.univ : Finset (Sym2 (Fin m))).filter fun z => ¬ z.IsDiag).card =
      m.choose 2 := by
    rw [← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]
  rw [← ht]
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    have hp' : p.1 < p.2 := by simpa using hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff]
    exact ne_of_lt hp'
  · intro p hp q hq hpq
    have hp : p.1 < p.2 := by simpa using hp
    have hq : q.1 < q.2 := by simpa using hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ h2 ▸ hq) (not_lt.2 hp.le)

/-- A permutation with the maximal number `m choose 2` of inversions inverts every pair. -/
theorem lt_of_invCount_eq_choose {m : ℕ} {w : Perm (Fin m)} (h : invCount m w = m.choose 2)
    {a b : Fin m} (hab : a < b) : w b < w a := by
  classical
  by_contra hba
  push_neg at hba
  set S := (Finset.univ : Finset (Fin m × Fin m)).filter fun p => p.1 < p.2
  have hmem : (a, b) ∈ S := by simp [S, hab]
  have hsub : invSet m w ⊆ S.erase (a, b) := by
    intro p hp
    rw [mem_invSet] at hp
    refine Finset.mem_erase.2 ⟨?_, by simp [S, hp.1]⟩
    rintro rfl
    exact absurd hp.2 (not_lt.2 hba)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at h1
  have h2 : S.card ≤ m.choose 2 := card_filter_lt_le_choose m
  have h3 := Finset.card_pos.2 ⟨_, hmem⟩
  unfold invCount at h
  omega

/-- A strictly order-reversing permutation of `Fin m` is the reversal `a ↦ m - 1 - a`. -/
theorem eq_rev_of_strictAnti {m : ℕ} {w : Perm (Fin m)} (h : ∀ a b : Fin m, a < b → w b < w a)
    (a : Fin m) : w a = a.rev := by
  have hg : StrictMono fun c : Fin m => w c.rev := fun c d hcd => h _ _ (Fin.rev_lt_rev.2 hcd)
  have hs : Function.Surjective fun c : Fin m => w c.rev := fun y =>
    ⟨(w.symm y).rev, by simp⟩
  have := congrArg (fun e : Fin m ≃o Fin m => e a.rev)
    (Subsingleton.elim (StrictMono.orderIsoOfSurjective _ hg hs) (OrderIso.refl _))
  simpa using this

/-- **`w_0⁻¹ = w_0`**. -/
theorem longest_inv (m : ℕ) : (longest m)⁻¹ = longest m := by
  have h1 : invCount m (longest m) = m.choose 2 := by
    rw [← length_eq_invCount, length_longest]
  have h2 : invCount m (longest m)⁻¹ = m.choose 2 := by
    rw [← length_eq_invCount, length_inv, length_longest]
  refine Equiv.ext fun a => ?_
  rw [eq_rev_of_strictAnti (fun _ _ => lt_of_invCount_eq_choose h2) a,
    eq_rev_of_strictAnti (fun _ _ => lt_of_invCount_eq_choose h1) a]

/-- The reversed word of `w0Word m` is again a reduced word of `w_0`. -/
theorem isReduced_w0Word_reverse (m : ℕ) : IsReduced m (w0Word m).reverse :=
  ⟨validWord_reverse.2 (isReduced_w0Word m).1, by
    rw [List.length_reverse, wordProd_reverse, length_inv]; exact (isReduced_w0Word m).2⟩

/-- `∂_{w_0}` along the reversed word `w0Word m` is `∂_{w_0}`. -/
theorem ddw_w0Word_reverse {k : Type*} [CommRing k] (m : ℕ) :
    ddw (k := k) (m := m) (w0Word m).reverse = ddw (w0Word m) :=
  ddw_eq_of_isReduced (isReduced_w0Word_reverse m) (isReduced_w0Word m)
    (by rw [wordProd_reverse]; exact longest_inv m)

end NilHecke

namespace KLR

open MvPolynomial Categorification.NilHecke KLRAlgebra Graded LaurentPolynomial

namespace NilHecke

variable {B : Type*} [Ring B] {n : ℕ} {X' : Fin n → B} {D : ℕ → B}

private theorem lift_ddw' (hF : IsNilHeckeFamily n X' D) (ρ : List ℕ) :
    lift (k := ℤ) hF ⟨ddw ρ, ddw_mem ρ⟩ = (ρ.map D).prod := by
  induction ρ with
  | nil =>
    have : (⟨ddw [], ddw_mem []⟩ : nilHecke ℤ n) = 1 := rfl
    rw [this, map_one]; rfl
  | cons j ρ ih =>
    have : (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke ℤ n) =
        ⟨dd ℤ n j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := Subtype.ext (ddw_cons j ρ)
    rw [this, map_mul, ih, lift_dd, List.map_cons, List.prod_cons]

/-- In any family satisfying the nilHecke relations, `∂_{w_0}` computed along the reversed word
`w0Word n` equals `∂_{w_0}`. -/
theorem IsNilHeckeFamily.prod_reverse_w0Word (hF : IsNilHeckeFamily n X' D) :
    ((w0Word n).reverse.map D).prod = ((w0Word n).map D).prod := by
  have h : (⟨ddw (w0Word n).reverse, ddw_mem _⟩ : nilHecke ℤ n) = ⟨ddw (w0Word n), ddw_mem _⟩ :=
    Subtype.ext (ddw_w0Word_reverse n)
  have := congrArg (lift (k := ℤ) hF) h
  rwa [lift_ddw', lift_ddw'] at this

end NilHecke

/-! ### `ψ(1_i)` for divided-power idempotents -/

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

private theorem hflip_ψw' (ρ : List ℕ) : hflip (ψw ρ : A) = ψw ρ.reverse := by
  induction ρ with
  | nil => simp [ψw]
  | cons j ρ ih =>
    rw [ψw_cons, hflip_mul, ih, hflip_ψ, List.reverse_cons, ψw_append]
    simp [ψw]

theorem val_prod_cψ_reverse {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m) (hc : IsConstOn i p n) :
    (((w0Word n).reverse.map (cψ (k := k) (Q := Q) i hpn hc)).prod).1 =
      ψw (blockWord p n).reverse := by
  rw [← Subring.coe_subtype, map_list_prod, ψw, blockWord]
  simp only [List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun j hj => ?_
  exact cψ_val_of_lt hpn hc (lt_of_mem_w0Word hj)

/-- **`ψ_{w_0}` is unchanged by reversing its word on a block of equal labels**:
`ψ_{w_0}^{rev} 1_i = ψ_{w_0} 1_i`. -/
theorem ψw_blockWord_reverse_mul_e {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m)
    (hc : IsConstOn i p n) :
    (ψw (blockWord p n).reverse * e i : A) = ψw (blockWord p n) * e i := by
  have key := (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc).prod_reverse_w0Word
  have hW : ∀ l : List ℕ, (l.map fun j =>
      toCorner (e_mul_self i) (cψ (k := k) (Q := Q) i hpn hc j)).prod =
      toCorner (e_mul_self i) (l.map (cψ (k := k) (Q := Q) i hpn hc)).prod := fun l => by
    rw [map_list_prod, List.map_map]; rfl
  rw [hW, hW, toCorner_eq_iff, val_prod_cψ, val_prod_cψ_reverse] at key
  exact key

/-- The crossings `ψ_{w_0}` of the blocks. -/
noncomputable def blocksψ (bs : List (ℕ × ℕ)) : A :=
  (bs.map fun b => ψw (blockWord b.1 b.2)).prod

/-- The dots `x^δ` of the blocks. -/
noncomputable def blocksDelta (bs : List (ℕ × ℕ)) : MvPolynomial (Fin m) k :=
  (bs.map fun b => blockDelta b.1 b.2).prod

@[simp] theorem blocksψ_nil : (blocksψ [] : A) = 1 := rfl

omit [DecidableEq I] in
@[simp] theorem blocksDelta_nil : (blocksDelta [] : MvPolynomial (Fin m) k) = 1 := rfl

theorem blocksψ_cons (b : ℕ × ℕ) (bs : List (ℕ × ℕ)) :
    (blocksψ (b :: bs) : A) = ψw (blockWord b.1 b.2) * blocksψ bs := by
  simp [blocksψ]

omit [DecidableEq I] in
theorem blocksDelta_cons (b : ℕ × ℕ) (bs : List (ℕ × ℕ)) :
    (blocksDelta (b :: bs) : MvPolynomial (Fin m) k) = blockDelta b.1 b.2 * blocksDelta bs := by
  simp [blocksDelta]

theorem blocksψ_mul_e {i : Seq ν} {bs : List (ℕ × ℕ)} (h : ∀ b ∈ bs, IsConstOn i b.1 b.2) :
    (blocksψ bs * e i : A) = e i * blocksψ bs := by
  rw [blocksψ]
  refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  exact blockψ_mul_e (h b hb)

/-- Disjointness of a block from the blocks `bs`, for a word inside the block. -/
private theorem disj_of_mem_blockWord {b c : ℕ × ℕ} (h : b.1 + b.2 ≤ c.1 ∨ c.1 + c.2 ≤ b.1)
    {j : ℕ} (hj : j ∈ blockWord b.1 b.2) : j + 1 < c.1 ∨ c.1 + c.2 ≤ j := by
  have := mem_blockWord hj
  omega

theorem commute_ψw_pol_blockDelta {ρ : List ℕ} {p n : ℕ}
    (h : ∀ j ∈ ρ, j + 1 < p ∨ p + n ≤ j) :
    Commute (ψw ρ : A) (pol (blockDelta p n)) :=
  (commute_pol_blockDelta fun a h1 h2 => commute_x_ψw fun j hj => by
    have := h j hj; omega).symm

theorem commute_ψw_ψw {ρ σ : List ℕ} (h : ∀ j ∈ ρ, ∀ l ∈ σ, j + 1 < l ∨ l + 1 < j) :
    Commute (ψw ρ : A) (ψw σ) := by
  rw [ψw]
  refine Commute.list_prod_left _ _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact commute_ψ_ψw fun l hl => h j hj l hl

/-- `blocksElt bs = x^δ ψ_{w_0}` with all dots to the left. -/
theorem blocksElt_eq {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (blocksElt bs : A) = pol (blocksDelta bs) * blocksψ bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hc : Commute (ψw (blockWord b.1 b.2) : A) (pol (blocksDelta bs)) := by
      rw [blocksDelta, map_list_prod, List.map_map]
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      exact commute_ψw_pol_blockDelta fun j hj =>
        disj_of_mem_blockWord ((List.pairwise_cons.1 h.disj).1 c hc) hj
    rw [blocksElt_cons, ih h.tail, blockElt, blocksDelta_cons, blocksψ_cons, map_mul, mul_assoc,
      ← mul_assoc (ψw _), hc.eq]
    simp only [mul_assoc]

/-- **`ψ(ψ_{w_0}) 1_i = ψ_{w_0} 1_i`** for all the blocks. -/
theorem hflip_blocksψ_mul_e {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (hflip (blocksψ bs) * e i : A) = blocksψ bs * e i := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb := h.const b List.mem_cons_self
    have hc : Commute (ψw (blockWord b.1 b.2) : A) (blocksψ bs) := by
      rw [blocksψ]
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      refine commute_ψw_ψw fun j hj l hl => ?_
      have h1 := mem_blockWord hj
      have h2 := mem_blockWord hl
      have := (List.pairwise_cons.1 h.disj).1 c hc
      omega
    rw [blocksψ_cons, hflip_mul, hflip_ψw', mul_assoc,
      ψw_blockWord_reverse_mul_e (h.le b List.mem_cons_self) hb, blockψ_mul_e hb,
      ← mul_assoc, ih h.tail, mul_assoc, ← blockψ_mul_e hb, ← mul_assoc, ← hc.eq, mul_assoc]

/-- The element `x = x^δ 1_i`. -/
noncomputable def divX (i : Seq ν) (bs : List (ℕ × ℕ)) : A := pol (blocksDelta bs) * e i

/-- The element `y = ψ_{w_0} 1_i`. -/
noncomputable def divY (i : Seq ν) (bs : List (ℕ × ℕ)) : A := blocksψ bs * e i

/-- **`1_i = x y`**. -/
theorem divX_mul_divY {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (divX i bs * divY i bs : A) = divIdem i bs := by
  rw [divX, divY, divIdem, blocksElt_eq h, mul_assoc, ← mul_assoc (e i), ← blocksψ_mul_e h.const,
    mul_assoc, e_mul_self, mul_assoc]

/-- **`ψ(1_i) = y x`**. -/
theorem divY_mul_divX {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (divY i bs * divX i bs : A) = hflip (divIdem i bs) := by
  have h1 : (e i * hflip (blocksψ bs) : A) = hflip (blocksψ bs) * e i := by
    have := congrArg hflip (blocksψ_mul_e (k := k) (Q := Q) h.const)
    rwa [hflip_mul, hflip_mul, hflip_e] at this
  rw [divIdem, blocksElt_eq h, hflip_mul, hflip_mul, hflip_e, hflip_pol, ← mul_assoc, h1,
    hflip_blocksψ_mul_e h, divY, divX]
  simp only [mul_assoc]
  rw [← (e_commute_pol i _).eq, ← mul_assoc (e i) (e i), e_mul_self]

section Grading

variable (G : GradingDatum Q) {δ : ℤ} (hX : ∀ a, G.degX a = δ)

include hX in
theorem pol_blockDelta_mul_e_mem_grade {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m)
    (hc : IsConstOn i p n) :
    (pol (blockDelta p n) * e i : A) ∈ G.grade ν ((n.choose 2 : ℤ) * δ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (blockDelta p 0 : MvPolynomial (Fin m) k) = 1 := by simp [blockDelta]
    rw [this, map_one, one_mul]
    simpa using G.e_mem_grade i
  set c := i.lbl ⟨p, by omega⟩
  have hcl : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → i.lbl a = c :=
    fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have h1 := G.pol_mul_e_mem_grade i (blockDelta_isWeightedHomogeneous G hpn hcl)
  rwa [nsmul_eq_mul, hX] at h1

include hX in
theorem ψw_blockWord_mul_e_mem_grade {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m)
    (hc : IsConstOn i p n) :
    (ψw (blockWord p n) * e i : A) ∈ G.grade ν (-((n.choose 2 : ℤ) * δ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : blockWord p 0 = [] := rfl
    rw [this]
    simpa [ψw] using G.e_mem_grade i
  set c := i.lbl ⟨p, by omega⟩
  have hcl : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → i.lbl a = c :=
    fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have h2 := G.ψw_mul_pol_mul_e_mem_grade (blockWord p n) i (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, degW_of_forall G (c := c)
    (fun j hj => by have := mem_blockWord hj; omega)
    (fun j hj hj' => ⟨hcl _ (mem_blockWord hj).1 (by simp only; have := mem_blockWord hj; omega),
      hcl _ (by simp only; have := mem_blockWord hj; omega)
        (by simp only; have := mem_blockWord hj; omega)⟩), length_blockWord, hX] at h2
  convert h2 using 2
  ring

include hX in
/-- `x = x^δ 1_i` has degree `δ ∑_b (n_b choose 2)` (`δ` the degree of a dot). -/
theorem divX_mem_grade {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (divX i bs : A) ∈ G.grade ν (((bs.map fun b => b.2.choose 2).sum : ℕ) * δ) := by
  induction bs with
  | nil => simpa [divX] using G.e_mem_grade i
  | cons b bs ih =>
    have e1 : (divX i (b :: bs) : A) = (pol (blockDelta b.1 b.2) * e i) * divX i bs := by
      rw [divX, divX, blocksDelta_cons, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (e i) (pol _) (e i), (e_commute_pol i _).eq, mul_assoc, e_mul_self]
    rw [e1, List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
    exact SetLike.mul_mem_graded
      (pol_blockDelta_mul_e_mem_grade G hX (h.le b List.mem_cons_self)
        (h.const b List.mem_cons_self)) (ih h.tail)

include hX in
/-- `y = ψ_{w_0} 1_i` has degree `-δ ∑_b (n_b choose 2)`. -/
theorem divY_mem_grade {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    (divY i bs : A) ∈ G.grade ν (-(((bs.map fun b => b.2.choose 2).sum : ℕ) * δ)) := by
  induction bs with
  | nil => simpa [divY] using G.e_mem_grade i
  | cons b bs ih =>
    have e1 : (divY i (b :: bs) : A) = (ψw (blockWord b.1 b.2) * e i) * divY i bs := by
      rw [divY, divY, blocksψ_cons]
      simp only [mul_assoc]
      rw [← mul_assoc (e i) (blocksψ bs) (e i), ← blocksψ_mul_e h.tail.const, mul_assoc,
        e_mul_self]
    rw [e1, List.map_cons, List.sum_cons, Nat.cast_add, add_mul, neg_add]
    exact SetLike.mul_mem_graded
      (ψw_blockWord_mul_e_mem_grade G hX (h.le b List.mem_cons_self)
        (h.const b List.mem_cons_self)) (ih h.tail)

end Grading

omit [DecidableEq I] in
theorem sum_choose_blocksDiv (d : List (I × ℕ)) (p : ℕ) :
    ((blocksDiv d p).map fun b => b.2.choose 2).sum = divAngle d := by
  induction d generalizing p with
  | nil => rfl
  | cons q d ih =>
    simp only [blocksDiv, List.map_cons, List.sum_cons, ih, divAngle]

end KLRAlgebra

/-! ### KL I: `\overline{[P_i]} = [P_i]` -/

namespace KL1

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Γ : SimpleGraph I}
  [DecidableRel Γ.Adj] {ν : Multiset I}

/-- **`[R(ν) 1_i] = q^{-2⟨i⟩} [R(ν) ψ(1_i)]`** for a divided-power expression `i` (the
expansion `t` and blocks `bs`). -/
theorem K0_of_divIdem {t : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks t bs) :
    K0.of (GProj.ofIdempotent (divIdem t bs : KLRAlgebra k (klQ Γ) ν) (isIdempotentElem_divIdem h)
      (divIdem_mem_grade (klGradingDatum k Γ) h)) =
      (T (-((((bs.map fun b => b.2.choose 2).sum : ℕ) : ℤ) * 2)) : LaurentPolynomial ℤ) •
        K0.of (projFlip k Γ t bs h) :=
  K0.of_ofIdempotent_eq_T_smul
    (divX_mem_grade (klGradingDatum k Γ) (δ := 2) (fun _ => rfl) h)
    (divY_mem_grade (klGradingDatum k Γ) (δ := 2) (fun _ => rfl) h)
    (divX_mul_divY h) (divY_mul_divX h) _ _ _ _

/-- **`P̄_i ≅ P_i` in `K₀`** for the divided-power projectives `P_i = R(ν) ψ(1_i){-⟨i⟩}`
(KL I §2.5): `\overline{[P_i]} = [P_i]`. -/
theorem bar_projDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.bar (psi k Γ ν) (K0.of (projDiv k Γ d h)) = K0.of (projDiv k Γ d h) := by
  have hb := isBlocks_ofList d h
  rw [projDiv, ← K0.T_smul_of, K0.bar_T_smul, neg_neg, projFlip, K0.bar_ofIdempotent]
  have e1 : K0.of (GProj.ofIdempotent ((psi k Γ ν) (hflip (divIdem _ _ : KLRAlgebra k (klQ Γ) ν)))
      ((psi k Γ ν).isIdempotentElem (isIdempotentElem_hflip_divIdem hb))
      ((psi k Γ ν).mem_grade (KL1.hflip_mem_grade (divIdem_mem_grade _ hb)))) =
      K0.of (GProj.ofIdempotent (divIdem _ _ : KLRAlgebra k (klQ Γ) ν)
        (isIdempotentElem_divIdem hb) (divIdem_mem_grade (klGradingDatum k Γ) hb)) :=
    K0.of_ofIdempotent_congr (hflip_hflip _) _ _ _ _
  rw [e1, K0_of_divIdem hb, ← mul_smul, ← T_add, sum_choose_blocksDiv]
  congr 2
  ring

end KL1

namespace KLGamma

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

/-- `[P_d]` is bar-invariant in `K₀(R)`. -/
theorem barR_clsDiv (d : List (I × ℕ)) : barR k Γ (clsDiv k Γ d) = clsDiv k Γ d := by
  rw [clsDiv, GradingDatum.barR_of]
  congr 1
  exact KL1.bar_projDiv d rfl

end KLGamma

end KLR

end Categorification
