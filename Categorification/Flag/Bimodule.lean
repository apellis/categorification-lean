/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Cohomology

/-!
# The bimodules `H_{k^{+i}}` and the graphical-calculus identities (KL III §5.1.1, §5.2)

Khovanov–Lauda III, arXiv:0807.3250v1, §5.1.1 ("Flag varieties for the action of `E_i` and
`F_i`"), eqs. (5.13)–(5.17), and §5.2.1–5.2.2, eqs. (5.25)–(5.29), Proposition 5.3.

For `1 ≤ i ≤ n - 1` and `k_i < k_{i+1}`, the variety `Fl(k^{+i})` of flags
`F_{k_1} ⊂ ⋯ ⊂ F_{k_i} ⊂ F_{k_i + 1} ⊂ F_{k_{i+1}} ⊂ ⋯` maps to `Fl(k)` and to `Fl(+_i k)`, and
the pullbacks `p_1^* : H_k → H_{k^{+i}}`, `p_2^* : H_{+_i k} → H_{k^{+i}}` make `H_{k^{+i}}` an
`(H_{+_i k}, H_k)`-bimodule: the image of `E_i 1_k` in `Flag_N` (Definition 5.6); with the actions
exchanged it is the image of `F_i 1_{+_i k}`.

## The Borel model

We work with a labelled set of variables `lab : V → J` (`Flag.BorelRing k lab`, the Borel ring)
and a variable `v₀`:

* `splitLab lab v₀ : V → Option J` puts `v₀` in a new block `none` of its own; the Borel ring of
  `splitLab lab v₀` is `H_{k^{+i}}` (KL III eq. (5.13)), and the class `xi` of `x_{v₀}` is KL III's
  generator `ξ_i` (the Chern class of the line bundle `F_{k_i+1}/F_{k_i}`, Remark 5.1);
* `moveLab lab v₀ j' = Function.update lab v₀ j'` moves `v₀` to block `j'`;
* `pR : BorelRing k lab → BorelRing k (splitLab lab v₀)` and
  `pL : BorelRing k (moveLab lab v₀ j') → BorelRing k (splitLab lab v₀)` are the forgetful maps
  `p_1^*`, `p_2^*` (`Flag.refineHom`).

For block sizes `d`, vertex `i` (between blocks `i.castSucc` and `i.succ` of `Fin (m+1)`),
`V = Gen d`, `lab = Sigma.fst`, `v₀` a variable of block `i.succ` and `j' = i.castSucc`, the
Borel rings of `lab` and `moveLab lab v₀ j'` are `H_k` and `H_{+_i k}` (`Flag.hEquiv`,
`Flag.borelEquivH'`); see `Flag.ERing`, `Flag.eRight`, `Flag.eLeft`, `Flag.eXi`.

## Main results

* `pR_xB_succ` / `pL_xB_succ` : KL III eqs. (5.15), (5.16) (equivalently (5.17), (5.26),
  (5.27)): `x(k)_{j,α} ↦ ξ x(k^{+i})_{j,α-1} + x(k^{+i})_{j,α}` for the block `j` containing `v₀`
  (resp. receiving `v₀`), and `x(k)_{j,α} ↦ x(k^{+i})_{j,α}` otherwise.
* `pR_xB_eq_pL_xB` : eq. (5.25), bubbles of other colours slide through the line.
* `xB_split_eq_sum` : eqs. (5.28), (5.29), the canonical generators in terms of the
  non-canonical ones, `x(k^{+i})_{j,α} = ∑_f (-ξ)^f x(k)_{j,α-f}`.
* `pR_xbarB_eq_pL_xbarB` (`j ≠ i, i+1`), `pL_xbarB_of_eq` (`j = i + 1`), `pR_xbarB_of_move`
  (`j = i`) : **Proposition 5.3** (eqs. (5.32), (5.33)), sliding the dual generators `x̄_{j,α}`
  through the line; in the Borel model each is an instance of `e(S ∪ {v₀})(t) = (1 + ξt) e(S)(t)`.
* `ERing`, `eRight`, `eLeft`, `eXi` : the data `(H_{+_i k} → H_{k^{+i}} ← H_k, ξ_i)` for block
  sizes `d`, with (5.15) and (5.16) in terms of the generators `x(k)_{j,α}` of the presentation
  (5.2) (`eRight_x`, `eLeft_x`); `card_moveLab` identifies the target of `E_i` as `+_i k`.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial
open Finset (univ range)

variable (k : Type*) [Field k] {V : Type*} [DecidableEq V] {J : Type*}

section Split

variable (lab : V → J) (v₀ : V) (j' : J)

/-- The labelling of `Fl(k^{+i})`: the variable `v₀` forms a block `none` of its own. -/
def splitLab : V → Option J := fun v => if v = v₀ then none else some (lab v)

/-- The labelling obtained by moving `v₀` to block `j'`. -/
def moveLab : V → J := Function.update lab v₀ j'

variable {lab v₀ j'}

@[simp] theorem splitLab_self : splitLab lab v₀ v₀ = none := if_pos rfl

theorem splitLab_of_ne {v : V} (h : v ≠ v₀) : splitLab lab v₀ v = some (lab v) := if_neg h

theorem splitLab_eq_none {v : V} : splitLab lab v₀ v = none ↔ v = v₀ := by
  by_cases h : v = v₀
  · simp [h]
  · simp [splitLab_of_ne h, h]

variable (lab v₀ j')

theorem refines_splitLab : Refines (splitLab lab v₀) lab := by
  intro v w h
  by_cases hv : v = v₀
  · have hw : w = v₀ := splitLab_eq_none.1 (h ▸ splitLab_eq_none.2 hv)
    rw [hv, hw]
  · have hw : w ≠ v₀ := fun hw => hv (splitLab_eq_none.1 (h.symm ▸ splitLab_eq_none.2 hw))
    rw [splitLab_of_ne hv, splitLab_of_ne hw] at h
    exact Option.some_injective _ h

theorem refines_splitLab_move : Refines (splitLab lab v₀) (moveLab lab v₀ j') := by
  intro v w h
  by_cases hv : v = v₀
  · have hw : w = v₀ := splitLab_eq_none.1 (h ▸ splitLab_eq_none.2 hv)
    rw [hv, hw]
  · have hw : w ≠ v₀ := fun hw => hv (splitLab_eq_none.1 (h.symm ▸ splitLab_eq_none.2 hw))
    rw [splitLab_of_ne hv, splitLab_of_ne hw] at h
    simp only [moveLab, Function.update_of_ne hv, Function.update_of_ne hw]
    exact Option.some_injective _ h

variable [Fintype V] [DecidableEq J]

/-- **`p_1^* : H_k → H_{k^{+i}}`** (KL III (5.15)). -/
def pR : BorelRing k lab →ₐ[k] BorelRing k (splitLab lab v₀) :=
  refineHom k (refines_splitLab lab v₀)

/-- **`p_2^* : H_{+_i k} → H_{k^{+i}}`** (KL III (5.16)). -/
def pL : BorelRing k (moveLab lab v₀ j') →ₐ[k] BorelRing k (splitLab lab v₀) :=
  refineHom k (refines_splitLab_move lab v₀ j')

omit [Fintype V] [DecidableEq J] in
theorem X_mem_split : (X v₀ : MvPolynomial V k) ∈ labelInvariants k (splitLab lab v₀) := by
  intro g hg
  have : g v₀ = v₀ := splitLab_eq_none.1 ((congrFun hg v₀).trans splitLab_self)
  rw [rename_X, this]

/-- **The generator `ξ_i ∈ H_{k^{+i}}`**: the class of `x_{v₀}`. -/
def xi : BorelRing k (splitLab lab v₀) := mkB k _ ⟨X v₀, X_mem_split k lab v₀⟩

/-! #### Blocks -/

variable {lab v₀ j'}

theorem labSet_split_some (j : J) :
    labSet (splitLab lab v₀) (· = some j) = (labSet lab (· = j)).erase v₀ := by
  ext v
  by_cases hv : v = v₀
  · simp [hv]
  · simp [hv, splitLab_of_ne hv]

theorem v₀_not_mem_split (j : J) : v₀ ∉ labSet (splitLab lab v₀) (· = some j) := by
  simp

theorem v₀_mem_split_ne (j : J) : v₀ ∈ labSet (splitLab lab v₀) (· ≠ some j) := by
  simp

theorem labSet_lab_eq (j : J) :
    labSet lab (· = j) = if j = lab v₀ then insert v₀ (labSet (splitLab lab v₀) (· = some j))
      else labSet (splitLab lab v₀) (· = some j) := by
  rw [labSet_split_some]
  split_ifs with h
  · rw [Finset.insert_erase]
    simp [h]
  · rw [Finset.erase_eq_of_not_mem]
    simp [Ne.symm h]

theorem labSet_move_eq (j : J) :
    labSet (moveLab lab v₀ j') (· = j) = if j = j' then
      insert v₀ (labSet (splitLab lab v₀) (· = some j))
      else labSet (splitLab lab v₀) (· = some j) := by
  ext v
  by_cases hv : v = v₀
  · subst hv
    split_ifs with h <;> simp [moveLab, h, Ne.symm]
  · split_ifs with h <;> simp [moveLab, hv, splitLab_of_ne hv, Function.update_of_ne hv]

theorem labSet_split_ne (j : J) :
    labSet (splitLab lab v₀) (· ≠ some j) = insert v₀ ((labSet lab (· ≠ j)).erase v₀) := by
  ext v
  by_cases hv : v = v₀
  · simp [hv]
  · simp [hv, splitLab_of_ne hv]

theorem labSet_lab_ne (j : J) :
    labSet lab (· ≠ j) = if j = lab v₀ then (labSet (splitLab lab v₀) (· ≠ some j)).erase v₀
      else labSet (splitLab lab v₀) (· ≠ some j) := by
  rw [labSet_split_ne]
  split_ifs with h
  · rw [Finset.erase_insert (by simp)]
    ext v
    by_cases hv : v = v₀
    · simp [hv, h]
    · simp [hv]
  · rw [Finset.insert_erase]
    simp [Ne.symm h]

theorem labSet_move_ne (j : J) :
    labSet (moveLab lab v₀ j') (· ≠ j) = if j = j' then
      (labSet (splitLab lab v₀) (· ≠ some j)).erase v₀
      else labSet (splitLab lab v₀) (· ≠ some j) := by
  ext v
  by_cases hv : v = v₀
  · subst hv
    split_ifs with h <;> simp [moveLab, h, Ne.symm]
  · split_ifs with h <;> simp [moveLab, hv, splitLab_of_ne hv, Function.update_of_ne hv]

/-! #### Generators -/

omit [DecidableEq J] in
/-- `pR` on classes of invariants. -/
theorem pR_mk (a : labelInvariants k lab) (b : labelInvariants k (splitLab lab v₀))
    (h : (a : MvPolynomial V k) = b) : pR k lab v₀ (mkB k lab a) = mkB k _ b :=
  refineHom_mk _ a b h

omit [DecidableEq J] in
theorem pL_mk (a : labelInvariants k (moveLab lab v₀ j')) (b : labelInvariants k (splitLab lab v₀))
    (h : (a : MvPolynomial V k) = b) : pL k lab v₀ j' (mkB k _ a) = mkB k _ b :=
  refineHom_mk _ a b h

/-- **KL III eq. (5.15)** (and (5.26)): `p_1^* x(k)_{j,α+1} = x(k^{+i})_{j,α+1} + ξ x(k^{+i})_{j,α}`
for the block `j` of `v₀`, and `p_1^* x(k)_{j,α} = x(k^{+i})_{j,α}` for the other blocks. -/
theorem pR_xB_succ (j : J) (α : ℕ) :
    pR k lab v₀ (xB k lab j (α + 1)) = xB k (splitLab lab v₀) (some j) (α + 1) +
      if j = lab v₀ then xi k lab v₀ * xB k (splitLab lab v₀) (some j) α else 0 := by
  split_ifs with h
  · have hs : setEsymm (k := k) (labSet lab (· = j)) (α + 1) =
        setEsymm (labSet (splitLab lab v₀) (· = some j)) (α + 1) +
          X v₀ * setEsymm (labSet (splitLab lab v₀) (· = some j)) α := by
      rw [labSet_lab_eq, if_pos h, setEsymm_insert (v₀_not_mem_split j)]
    rw [xB, pR_mk k (blockElt k lab j (α + 1))
      (blockElt k (splitLab lab v₀) (some j) (α + 1) +
        (⟨X v₀, X_mem_split k lab v₀⟩ : labelInvariants k (splitLab lab v₀)) *
        blockElt k (splitLab lab v₀) (some j) α) hs, map_add, map_mul]
    rfl
  · rw [add_zero, xB, pR_mk k (blockElt k lab j (α + 1))
      (blockElt k (splitLab lab v₀) (some j) (α + 1))]
    · rfl
    change setEsymm _ _ = setEsymm _ _
    rw [labSet_lab_eq, if_neg h]

theorem pR_xB (j : J) (hj : j ≠ lab v₀) (α : ℕ) :
    pR k lab v₀ (xB k lab j α) = xB k (splitLab lab v₀) (some j) α := by
  rw [xB, pR_mk k (blockElt k lab j α) (blockElt k (splitLab lab v₀) (some j) α)]
  · rfl
  change setEsymm _ _ = setEsymm _ _
  rw [labSet_lab_eq, if_neg hj]

/-- **KL III eq. (5.16)** (and (5.27)): `p_2^* x(+_i k)_{j,α+1} = x(k^{+i})_{j,α+1} + ξ x(k^{+i})_{j,α}`
for the block `j = j'` receiving `v₀`, and `p_2^* x(+_i k)_{j,α} = x(k^{+i})_{j,α}` otherwise. -/
theorem pL_xB_succ (j : J) (α : ℕ) :
    pL k lab v₀ j' (xB k (moveLab lab v₀ j') j (α + 1)) =
      xB k (splitLab lab v₀) (some j) (α + 1) +
      if j = j' then xi k lab v₀ * xB k (splitLab lab v₀) (some j) α else 0 := by
  split_ifs with h
  · have hs : setEsymm (k := k) (labSet (moveLab lab v₀ j') (· = j)) (α + 1) =
        setEsymm (labSet (splitLab lab v₀) (· = some j)) (α + 1) +
          X v₀ * setEsymm (labSet (splitLab lab v₀) (· = some j)) α := by
      rw [labSet_move_eq, if_pos h, setEsymm_insert (v₀_not_mem_split j)]
    rw [xB, pL_mk k (blockElt k (moveLab lab v₀ j') j (α + 1))
      (blockElt k (splitLab lab v₀) (some j) (α + 1) +
        (⟨X v₀, X_mem_split k lab v₀⟩ : labelInvariants k (splitLab lab v₀)) *
        blockElt k (splitLab lab v₀) (some j) α) hs, map_add, map_mul]
    rfl
  · rw [add_zero, xB, pL_mk k (blockElt k (moveLab lab v₀ j') j (α + 1))
      (blockElt k (splitLab lab v₀) (some j) (α + 1))]
    · rfl
    change setEsymm _ _ = setEsymm _ _
    rw [labSet_move_eq, if_neg h]

theorem pL_xB (j : J) (hj : j ≠ j') (α : ℕ) :
    pL k lab v₀ j' (xB k (moveLab lab v₀ j') j α) = xB k (splitLab lab v₀) (some j) α := by
  rw [xB, pL_mk k (blockElt k (moveLab lab v₀ j') j α) (blockElt k (splitLab lab v₀) (some j) α)]
  · rfl
  change setEsymm _ _ = setEsymm _ _
  rw [labSet_move_eq, if_neg hj]

/-- **KL III eq. (5.25)**: for `j` different from both blocks involved, the bubble `x_{j,α}` slides
through the line. -/
theorem pR_xB_eq_pL_xB (j : J) (h1 : j ≠ lab v₀) (h2 : j ≠ j') (α : ℕ) :
    pR k lab v₀ (xB k lab j α) = pL k lab v₀ j' (xB k (moveLab lab v₀ j') j α) := by
  rw [pR_xB k j h1, pL_xB k j h2]

/-- **KL III eqs. (5.28), (5.29)**: the canonical generators of `H_{k^{+i}}` in terms of the
non-canonical ones, `x(k^{+i})_{j,α} = ∑_{f ≤ α} (-ξ)^f p_1^* x(k)_{j,α-f}` (`j` the block of
`v₀`). -/
theorem xB_split_eq_sum (α : ℕ) :
    xB k (splitLab lab v₀) (some (lab v₀)) α =
      ∑ f ∈ range (α + 1), (-xi k lab v₀) ^ f * pR k lab v₀ (xB k lab (lab v₀) (α - f)) := by
  have hs := setEsymm_eq_sum_insert (k := k) (v₀_not_mem_split (lab := lab) (v₀ := v₀) (lab v₀)) α
  have hset : insert v₀ (labSet (splitLab lab v₀) (· = some (lab v₀))) = labSet lab (· = lab v₀) :=
    ((labSet_lab_eq (lab := lab) (v₀ := v₀) (lab v₀)).trans (if_pos rfl)).symm
  rw [hset] at hs
  have : ∀ f, pR k lab v₀ (xB k lab (lab v₀) (α - f)) =
      mkB k _ ⟨setEsymm (labSet lab (· = lab v₀)) (α - f),
        labelInvariants_mono k (refines_splitLab lab v₀) (blockElt k lab (lab v₀) (α - f)).2⟩ :=
    fun f => pR_mk k _ _ rfl
  simp only [this, xi, ← map_neg, ← map_pow, ← map_mul, ← map_sum]
  rw [xB]
  congr 1
  apply Subtype.ext
  simp only [blockElt, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, NegMemClass.coe_neg]
  exact hs

/-! #### Dual generators: Proposition 5.3 -/

theorem pR_xbarB (j : J) (hj : j ≠ lab v₀) (α : ℕ) :
    pR k lab v₀ (xbarB k lab j α) = xbarB k (splitLab lab v₀) (some j) α := by
  rw [xbarB, pR_mk k (dualElt k lab j α) (dualElt k (splitLab lab v₀) (some j) α)]
  · rfl
  change setEsymm _ _ = setEsymm _ _
  rw [labSet_lab_ne, if_neg hj]

theorem pL_xbarB (j : J) (hj : j ≠ j') (α : ℕ) :
    pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j α) = xbarB k (splitLab lab v₀) (some j) α := by
  rw [xbarB, pL_mk k (dualElt k (moveLab lab v₀ j') j α) (dualElt k (splitLab lab v₀) (some j) α)]
  · rfl
  change setEsymm _ _ = setEsymm _ _
  rw [labSet_move_ne, if_neg hj]

/-- `x̄(k^{+i})_{j,α+1} = p_1^* x̄(k)_{j,α+1} + ξ p_1^* x̄(k)_{j,α}` for the block `j` of `v₀`. -/
theorem xbarB_split_succ_of_eq (α : ℕ) :
    xbarB k (splitLab lab v₀) (some (lab v₀)) (α + 1) =
      pR k lab v₀ (xbarB k lab (lab v₀) (α + 1)) +
        xi k lab v₀ * pR k lab v₀ (xbarB k lab (lab v₀) α) := by
  have hmem : v₀ ∉ labSet lab (· ≠ lab v₀) := by simp
  have hs : setEsymm (k := k) (labSet (splitLab lab v₀) (· ≠ some (lab v₀))) (α + 1) =
      setEsymm (labSet lab (· ≠ lab v₀)) (α + 1) + X v₀ * setEsymm (labSet lab (· ≠ lab v₀)) α := by
    rw [labSet_split_ne, Finset.erase_eq_of_not_mem hmem, setEsymm_insert hmem]
  have h1 : ∀ β, pR k lab v₀ (xbarB k lab (lab v₀) β) =
      mkB k _ ⟨setEsymm (labSet lab (· ≠ lab v₀)) β,
        labelInvariants_mono k (refines_splitLab lab v₀) (dualElt k lab (lab v₀) β).2⟩ :=
    fun β => pR_mk k _ _ rfl
  rw [h1, h1, xi, ← map_mul, ← map_add, xbarB]
  congr 1
  exact Subtype.ext hs

/-- `x̄(k^{+i})_{j,α+1} = p_2^* x̄(+_i k)_{j,α+1} + ξ p_2^* x̄(+_i k)_{j,α}` for the block `j = j'`
receiving `v₀`. -/
theorem xbarB_split_succ_of_move (α : ℕ) :
    xbarB k (splitLab lab v₀) (some j') (α + 1) =
      pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' (α + 1)) +
        xi k lab v₀ * pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' α) := by
  have hmem : v₀ ∉ labSet (moveLab lab v₀ j') (· ≠ j') := by simp [moveLab]
  have hs : setEsymm (k := k) (labSet (splitLab lab v₀) (· ≠ some j')) (α + 1) =
      setEsymm (labSet (moveLab lab v₀ j') (· ≠ j')) (α + 1) +
        X v₀ * setEsymm (labSet (moveLab lab v₀ j') (· ≠ j')) α := by
    rw [← setEsymm_insert hmem, labSet_move_ne, if_pos rfl, Finset.insert_erase]
    simp
  have h1 : ∀ β, pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' β) =
      mkB k _ ⟨setEsymm (labSet (moveLab lab v₀ j') (· ≠ j')) β,
        labelInvariants_mono k (refines_splitLab_move lab v₀ j')
          (dualElt k (moveLab lab v₀ j') j' β).2⟩ :=
    fun β => pL_mk k _ _ rfl
  rw [h1, h1, xi, ← map_mul, ← map_add, xbarB]
  congr 1
  exact Subtype.ext hs

/-- **KL III Proposition 5.3, `j ≠ i, i + 1`**: dual bubbles of other colours slide through the
line. -/
theorem pR_xbarB_eq_pL_xbarB (j : J) (h1 : j ≠ lab v₀) (h2 : j ≠ j') (α : ℕ) :
    pR k lab v₀ (xbarB k lab j α) = pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j α) := by
  rw [pR_xbarB k j h1, pL_xbarB k j h2]

/-- **KL III Proposition 5.3, eq. (5.33) for `j = i + 1`**: sliding the dual bubble of the block
losing `v₀` from the right region to the left region,
`x̄(+_i k)_{j,α+1} = ξ x̄(k)_{j,α} + x̄(k)_{j,α+1}`. -/
theorem pL_xbarB_of_eq (h : lab v₀ ≠ j') (α : ℕ) :
    pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') (lab v₀) (α + 1)) =
      xi k lab v₀ * pR k lab v₀ (xbarB k lab (lab v₀) α) +
        pR k lab v₀ (xbarB k lab (lab v₀) (α + 1)) := by
  rw [pL_xbarB k _ h, xbarB_split_succ_of_eq, add_comm]

/-- **KL III Proposition 5.3, eq. (5.32) for `j = i`**: sliding the dual bubble of the block
receiving `v₀` from the left region to the right region,
`x̄(k)_{j,α+1} = ξ x̄(+_i k)_{j,α} + x̄(+_i k)_{j,α+1}`. -/
theorem pR_xbarB_of_move (h : j' ≠ lab v₀) (α : ℕ) :
    pR k lab v₀ (xbarB k lab j' (α + 1)) =
      xi k lab v₀ * pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' α) +
        pL k lab v₀ j' (xbarB k (moveLab lab v₀ j') j' (α + 1)) := by
  rw [pR_xbarB k _ h, xbarB_split_succ_of_move, add_comm]

end Split

/-! ### Compositions -/

section Composition

variable {m : ℕ}

/-- The block sizes of `+_i k`: one variable moves from block `i.succ` to block `i.castSucc`
(KL III (5.8), the paper's `k_i ↦ k_i + 1`). -/
def raise (i : Fin m) (d : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ :=
  fun j => if j = i.castSucc then d j + 1 else if j = i.succ then d j - 1 else d j

variable (K : Type*) [Field K]

/-- The variable of `Gen d` moved by `E_i`: the first variable of block `i.succ`. -/
def movedVar (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) : Gen d := ⟨i.succ, ⟨0, h⟩⟩

theorem card_moveLab (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (j : Fin (m + 1)) :
    Fintype.card {v // moveLab (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc v = j}
      = raise i d j := by
  rw [Fintype.card_subtype]
  change (labSet (moveLab (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h) i.castSucc)
    (· = j)).card = _
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ i |>.ne
  rw [labSet_move_eq, labSet_split_some, raise]
  have hv : movedVar i d h ∈ labSet (Sigma.fst : Gen d → Fin (m + 1)) (· = i.succ) := by
    simp [movedVar]
  split_ifs with h1 h2
  · subst h1
    rw [Finset.card_insert_of_not_mem (by simp), Finset.erase_eq_of_not_mem (by
      simp [movedVar, Ne.symm hne]), card_labSet_sigma]
  · subst h2
    rw [Finset.card_erase_of_mem hv, card_labSet_sigma]
  · rw [Finset.erase_eq_of_not_mem (by simp [movedVar, Ne.symm h2]), card_labSet_sigma]

/-- `BorelRing lab ≃ H d` for a labelling with block sizes `d`. -/
def borelEquivH' {V : Type*} [Fintype V] {n : ℕ} (lab : V → Fin n) (d : Fin n → ℕ)
    (hd : ∀ j, Fintype.card {v // lab v = j} = d j) : BorelRing K lab ≃ₐ[K] H K d :=
  (borelEquivOfCard K lab (Sigma.fst : Gen d → Fin n)
    fun j => (hd j).trans (card_fibre_sigma j).symm).trans (hEquiv K d).symm

@[simp] theorem borelEquivH'_xB {V : Type*} [Fintype V] {n : ℕ} (lab : V → Fin n)
    (d : Fin n → ℕ) (hd : ∀ j, Fintype.card {v // lab v = j} = d j) (j : Fin n) (α : ℕ) :
    borelEquivH' K lab d hd (xB K lab j α) = x K d j α := by
  rw [borelEquivH', AlgEquiv.trans_apply, borelEquivOfCard_xB, AlgEquiv.symm_apply_eq, hEquiv_x]

/-- **The ring `H_{k^{+i}}`** of the bimodule of `E_i 1_k` (KL III eq. (5.13)), for block sizes
`d` with `d_{i+1} > 0` (the paper's `k_i < k_{i+1}`), in the Borel model: `v₀` (the first
variable of block `i.succ`) forms a block of its own. -/
abbrev ERing (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) : Type _ :=
  BorelRing K (splitLab (Sigma.fst : Gen d → Fin (m + 1)) (movedVar i d h))

/-- The right action `p_1^* : H_k → H_{k^{+i}}` (KL III (5.15)). -/
def eRight (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) : H K d →ₐ[K] ERing K i d h :=
  (pR K _ _).comp (hEquiv K d).toAlgHom

/-- The left action `p_2^* : H_{+_i k} → H_{k^{+i}}` (KL III (5.16)). -/
def eLeft (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) :
    H K (raise i d) →ₐ[K] ERing K i d h :=
  (pL K _ _ i.castSucc).comp (borelEquivH' K _ (raise i d) (card_moveLab i d h)).symm.toAlgHom

/-- The generator `ξ_i ∈ H_{k^{+i}}`. -/
def eXi (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) : ERing K i d h := xi K _ _

variable {K}

/-- **KL III eq. (5.15)** for a composition: `x(k)_{j,α+1} ↦ x(k^{+i})_{j,α+1} + ξ x(k^{+i})_{j,α}`
for `j = i + 1` (our `i.succ`), and `x(k)_{j,α+1} ↦ x(k^{+i})_{j,α+1}` otherwise. -/
theorem eRight_x (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (j : Fin (m + 1)) (α : ℕ) :
    eRight K i d h (x K d j (α + 1)) =
      xB K (splitLab _ (movedVar i d h)) (some j) (α + 1) +
        if j = i.succ then eXi K i d h * xB K (splitLab _ (movedVar i d h)) (some j) α
        else 0 := by
  rw [eRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_x, pR_xB_succ]
  rfl

/-- **KL III eq. (5.16)** for a composition: `x(+_i k)_{j,α+1} ↦ x(k^{+i})_{j,α+1} +
ξ x(k^{+i})_{j,α}` for `j = i` (our `i.castSucc`), and `x(+_i k)_{j,α+1} ↦ x(k^{+i})_{j,α+1}`
otherwise. -/
theorem eLeft_x (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (j : Fin (m + 1)) (α : ℕ) :
    eLeft K i d h (x K (raise i d) j (α + 1)) =
      xB K (splitLab _ (movedVar i d h)) (some j) (α + 1) +
        if j = i.castSucc then eXi K i d h * xB K (splitLab _ (movedVar i d h)) (some j) α
        else 0 := by
  rw [eLeft, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    (AlgEquiv.symm_apply_eq _).2 (borelEquivH'_xB K _ _ (card_moveLab i d h) j (α + 1)).symm,
    pL_xB_succ]
  rfl

end Composition

end Categorification.Flag

end
