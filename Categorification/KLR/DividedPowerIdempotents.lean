/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.NilHeckeIdempotent
import Categorification.KLR.Examples.NilHecke
import Categorification.KLR.Filtration
import Categorification.KLR.Grading
import Categorification.KLR.Symmetries
import Mathlib.Tactic.NoncommRing

/-!
# The divided-power idempotents `1_i` of `R(ν)`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2:

* §2.2, Example 3 (TeX lines ~685–720): the idempotent `e_m = x_1^{m-1} ⋯ x_{m-1} ∂_{w_0}` of
  the nilHecke ring, of degree `0`, and the corresponding idempotent `e_{i,m}` of `R(m i)`;
* §2.5 (TeX lines ~1600–1612): for an expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)} ∈ Seq'(ν)`
  the idempotent `1_i = e_{i_1,n_1} ⊗ ⋯ ⊗ e_{i_r,n_r}`.

We place the nilHecke idempotent directly on a block of strands of `R(ν)`: for a sequence
`i ∈ Seq ν` which is constant on the positions `[p, p + n)` (zero-indexed),

  `blockIdem i p n = x_p^{n-1} x_{p+1}^{n-2} ⋯ x_{p+n-2} · ψ_{w_0}^{[p, p+n)} · 1_i`,

where `ψ_{w_0}^{[p, p+n)} = ψw (shiftWord p (w0Word n))` is the product of crossings along the
reduced word `w0Word n` of the longest element of `S_n`, shifted to the block. Several blocks
(pairwise disjoint, each with constant labels) give `divIdem i bs`, the paper's `1_i` for the
divided-power expression whose expansion is `i` and whose divided powers sit on the blocks
`bs` (blocks of size `1` may be omitted: `blockElt p 1 = 1`).

## Main results

* `NilHecke.IsNilHeckeFamily.key` : in any ring, a family satisfying the nilHecke relations
  satisfies `∂_{w_0} x^δ ∂_{w_0} = ∂_{w_0}` (transported from `NH_n` over `ℤ` along
  `NilHecke.lift`).
* `isIdempotentElem_blockIdem` : `blockIdem i p n` is an idempotent of `R(ν)` (any `Q`, any
  commutative ring `k`). The proof maps `NH_n` to the corner ring `1_i R(ν) 1_i`.
* `isIdempotentElem_hflip_blockIdem` : so is its image `ψ(e_{i,n})` under the antiinvolution.
* `blockIdem_mem_grade` : `blockIdem i p n` has degree `0` for every grading datum (in
  particular for the KL I grading).
* `toNH_blockIdem`, `nilHeckeEquivOfForall_blockIdem` : for `ν = m i` the block idempotent on
  all strands is the idempotent `e_{i,m}` corresponding to `e_m` under `R(m i) ≅ NH_m`.
* `isIdempotentElem_divIdem`, `divIdem_mem_grade` : the same for several disjoint blocks.
* `divIdemOf d h` : the idempotent `1_i` of a divided-power expression
  `i = i_1^{(n_1)} ⋯ i_r^{(n_r)} ∈ Seq'(ν)`, given as the list `d` of pairs `(i_a, n_a)`
  (`expandDiv d` is the expansion `î`, `blocksDiv d 0` its blocks), with
  `isIdempotentElem_divIdemOf` and `divIdemOf_mem_grade`.
-/

namespace Categorification.KLR

open MvPolynomial Equiv TypeA Categorification.NilHecke KLRAlgebra

/-! ### The key identity for nilHecke families -/

namespace NilHecke

variable {B : Type*} [Ring B] {n : ℕ} {X' : Fin n → B} {D : ℕ → B}

private theorem lift_ddw (hF : IsNilHeckeFamily n X' D) (ρ : List ℕ) :
    lift (k := ℤ) hF ⟨ddw ρ, ddw_mem ρ⟩ = (ρ.map D).prod := by
  induction ρ with
  | nil =>
    have : (⟨ddw [], ddw_mem []⟩ : nilHecke ℤ n) = 1 := rfl
    rw [this, map_one]; rfl
  | cons j ρ ih =>
    have : (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke ℤ n) =
        ⟨dd ℤ n j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := Subtype.ext (ddw_cons j ρ)
    rw [this, map_mul, ih, lift_dd, List.map_cons, List.prod_cons]

private theorem lift_mulPoly_xDelta (hF : IsNilHeckeFamily n X' D) :
    lift (k := ℤ) hF ⟨mulPoly ℤ n (xDelta n), mulPoly_mem _⟩ =
      (List.ofFn fun a => X' a ^ (n - 1 - a)).prod := by
  have : (⟨mulPoly ℤ n (xDelta n), mulPoly_mem _⟩ : nilHecke ℤ n) =
      (List.ofFn fun a => (⟨mulX ℤ n a, mulX_mem a⟩ : nilHecke ℤ n) ^ (n - 1 - a)).prod := by
    apply Subtype.ext
    change mulPoly ℤ n (xDelta n) = (nilHecke ℤ n).val _
    rw [xDelta, ← List.prod_ofFn, map_list_prod]
    rw [map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext a
    simp only [Function.comp_apply, map_pow]
    rfl
  rw [this, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp only [Function.comp_apply, map_pow, lift_mulX]

/-- **The key identity** `∂_{w_0} x^δ ∂_{w_0} = ∂_{w_0}` for any family of elements of a ring
satisfying the nilHecke relations of KL I §2.2, Example 3 (`x^δ = x_0^{n-1} x_1^{n-2} ⋯`,
`∂_{w_0} = ∂_{w0Word n}`). -/
theorem IsNilHeckeFamily.key (hF : IsNilHeckeFamily n X' D) :
    ((w0Word n).map D).prod * (List.ofFn fun a => X' a ^ (n - 1 - a)).prod *
      ((w0Word n).map D).prod = ((w0Word n).map D).prod := by
  have h : (⟨ddw (w0Word n), ddw_mem _⟩ : nilHecke ℤ n) *
      ⟨mulPoly ℤ n (xDelta n), mulPoly_mem _⟩ * ⟨ddw (w0Word n), ddw_mem _⟩ =
      ⟨ddw (w0Word n), ddw_mem _⟩ :=
    Subtype.ext ddw_w0Word_mul_xDelta_mul_ddw_w0Word
  have := congrArg (lift (k := ℤ) hF) h
  rwa [map_mul, map_mul, lift_ddw, lift_mulPoly_xDelta] at this

end NilHecke

/-! ### Corner rings -/

section corner

variable {R : Type*} [Ring R] {E : R} (hE : IsIdempotentElem E)

/-- The underlying element of `R` of an element of the corner ring `E R E`. -/
def idemCornerVal (a : hE.Corner) : R := (show Subsemigroup.corner E from a).1

theorem idemCornerVal_injective : Function.Injective (idemCornerVal hE) :=
  fun _ _ h => Subtype.ext h

/-- The ring homomorphism `y ↦ y E` from the centralizer of `E` to the corner ring `E R E`. -/
def toCorner : Subring.centralizer ({E} : Set R) →+* hE.Corner where
  toFun y := show Subsemigroup.corner E from ⟨y.1 * E, y.1, by
    have := Subring.mem_centralizer_iff.1 y.2 E rfl
    simp only; rw [this, mul_assoc, hE.eq]⟩
  map_one' := idemCornerVal_injective hE (one_mul E)
  map_mul' y z := idemCornerVal_injective hE (by
    change y.1 * z.1 * E = y.1 * E * (z.1 * E)
    have := Subring.mem_centralizer_iff.1 z.2 E rfl
    simp only [mul_assoc]
    rw [← mul_assoc E, this, mul_assoc, hE.eq])
  map_zero' := idemCornerVal_injective hE (zero_mul E)
  map_add' y z := idemCornerVal_injective hE (add_mul y.1 z.1 E)

theorem idemCornerVal_toCorner (y : Subring.centralizer ({E} : Set R)) :
    idemCornerVal hE (toCorner hE y) = y.1 * E := rfl

theorem toCorner_eq_iff {y z : Subring.centralizer ({E} : Set R)} :
    toCorner hE y = toCorner hE z ↔ y.1 * E = z.1 * E :=
  ⟨fun h => congrArg (idemCornerVal hE) h, fun h => idemCornerVal_injective hE h⟩

end corner

/-! ### Blocks of strands -/

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- The sequence `i` has constant labels on the block of positions `[p, p + n)`. -/
def IsConstOn (i : Seq ν) (p n : ℕ) : Prop :=
  ∀ a b : Fin m, p ≤ a → (a : ℕ) < p + n → p ≤ b → (b : ℕ) < p + n → i.lbl a = i.lbl b

omit [DecidableEq I] in
theorem IsConstOn.lbl_succ {i : Seq ν} {p n : ℕ} (hc : IsConstOn i p n) {j : ℕ}
    (h1 : p ≤ j) (h2 : j + 1 < p + n) (h : j + 1 < m) :
    i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ :=
  hc _ _ h1 (by simp only; omega) (by simp only; omega) (by simp only; omega)

/-- The word of crossings `ψ_{w_0}` on the block `[p, p + n)`. -/
def blockWord (p n : ℕ) : List ℕ := (w0Word n).map (p + ·)

theorem mem_blockWord {p n j : ℕ} (h : j ∈ blockWord p n) : p ≤ j ∧ j + 1 < p + n := by
  obtain ⟨j', hj', rfl⟩ := List.mem_map.1 h
  have := lt_of_mem_w0Word hj'
  omega

theorem length_blockWord (p n : ℕ) : (blockWord p n).length = n.choose 2 := by
  rw [blockWord, List.length_map, length_w0Word]

/-- The monomial `x_p^{n-1} x_{p+1}^{n-2} ⋯ x_{p+n-2}` on the block `[p, p + n)`
(factors outside the strands are dropped). -/
noncomputable def blockDelta (p n : ℕ) : MvPolynomial (Fin m) k :=
  ∏ a : Fin n, if h : p + a < m then X ⟨p + a, h⟩ ^ (n - 1 - a) else 1

/-- The nilHecke idempotent `x^δ ∂_{w_0}` on the block `[p, p + n)`, without idempotent. -/
noncomputable def blockElt (p n : ℕ) : A := pol (blockDelta p n) * ψw (blockWord p n)

/-- The idempotent `e_{i_p, n}` placed on the block `[p, p + n)` of the sequence `i`:
`x_p^{n-1} ⋯ x_{p+n-2} ψ_{w_0}^{[p,p+n)} 1_i`. -/
noncomputable def blockIdem (i : Seq ν) (p n : ℕ) : A := blockElt p n * e i

/-- Crossings within a block of equal labels commute with `1_i`. -/
theorem ψw_mul_e_of_forall {ρ : List ℕ} {i : Seq ν}
    (h : ∀ j ∈ ρ, ∀ hj : j + 1 < m, i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, hj⟩) :
    (ψw ρ * e i : A) = e i * ψw ρ := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [ψw_cons, mul_assoc, ih fun l hl => h l (List.mem_cons_of_mem _ hl), ← mul_assoc,
      ← mul_assoc]
    congr 1
    by_cases hj : j + 1 < m
    · rw [ψ_mul_e, sadj_smul_eq_self hj (h j List.mem_cons_self hj)]
    · rw [ψ_eq_zero j (by omega), zero_mul, mul_zero]

theorem blockψ_mul_e {i : Seq ν} {p n : ℕ} (hc : IsConstOn i p n) :
    (ψw (blockWord p n) * e i : A) = e i * ψw (blockWord p n) :=
  ψw_mul_e_of_forall fun _ hj h => hc.lbl_succ (mem_blockWord hj).1 (mem_blockWord hj).2 h

theorem blockElt_mul_e {i : Seq ν} {p n : ℕ} (hc : IsConstOn i p n) :
    (blockElt p n * e i : A) = e i * blockElt p n := by
  rw [blockElt, mul_assoc, blockψ_mul_e hc, ← mul_assoc, ← mul_assoc,
    (e_commute_pol i _).eq]

theorem e_mul_ψ_of_eq {i : Seq ν} {j : ℕ} (h : j + 1 < m)
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) : (e i * ψ j : A) = ψ j * e i := by
  rw [e_mul_ψ, sadj_smul_eq_self h hi]

/-! ### The nilHecke family of a block in the corner ring -/

section family

variable (i : Seq ν) {p n : ℕ}

local notation "Cz" => Subring.centralizer ({(e i : A)} : Set A)

theorem mem_centralizer_iff' {y : A} : y ∈ Subring.centralizer ({(e i : A)} : Set A) ↔
    e i * y = y * e i := by
  rw [Subring.mem_centralizer_iff]; simp

/-- The dot `x_{p+a}` in the centralizer of `1_i`. -/
noncomputable def cx (hpn : p + n ≤ m) (a : Fin n) : Subring.centralizer ({(e i : A)} : Set A) :=
  ⟨x ⟨p + a, by omega⟩, (mem_centralizer_iff' i).2 (e_mul_x _ i)⟩

/-- The crossing `ψ_{p+j}` (`j + 1 < n`) in the centralizer of `1_i`, and `0` otherwise. -/
noncomputable def cψ (hpn : p + n ≤ m) (hc : IsConstOn i p n) (j : ℕ) :
    Subring.centralizer ({(e i : A)} : Set A) :=
  if h : j + 1 < n then ⟨ψ (p + j), (mem_centralizer_iff' i).2
    (e_mul_ψ_of_eq (by omega) (hc.lbl_succ (by omega) (by omega) _))⟩ else 0

variable {i}

theorem cx_val (hpn : p + n ≤ m) (a : Fin n) :
    (cx (k := k) (Q := Q) i hpn a).1 = x ⟨p + a, by omega⟩ := rfl

theorem cψ_val_of_lt (hpn : p + n ≤ m) (hc : IsConstOn i p n) {j : ℕ} (h : j + 1 < n) :
    (cψ (k := k) (Q := Q) i hpn hc j).1 = ψ (p + j) := by
  rw [cψ, dif_pos h]

theorem cψ_of_not_lt (hpn : p + n ≤ m) (hc : IsConstOn i p n) {j : ℕ} (h : ¬ j + 1 < n) :
    cψ (k := k) (Q := Q) i hpn hc j = 0 := by
  rw [cψ, dif_neg h]

/-- The dots and crossings of a block, multiplied by `1_i`, satisfy the nilHecke relations in
the corner ring `1_i R(ν) 1_i`. -/
theorem isNilHeckeFamily_block (hpn : p + n ≤ m) (hc : IsConstOn i p n) :
    NilHecke.IsNilHeckeFamily n (fun a => toCorner (e_mul_self i) (cx (k := k) (Q := Q) i hpn a))
      (fun j => toCorner (e_mul_self i) (cψ (k := k) (Q := Q) i hpn hc j)) where
  x_comm a b := by
    rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext (x_mul_x _ _)
  d_x_comm j a h₁ h₂ := by
    rw [← map_mul, ← map_mul]; congr 1; apply Subtype.ext
    by_cases h : j + 1 < n
    · change (cψ i hpn hc j).1 * (cx i hpn a).1 = (cx i hpn a).1 * (cψ i hpn hc j).1
      rw [cψ_val_of_lt hpn hc h, cx_val]
      exact (x_mul_ψ _ _ (by simp only; omega) (by simp only; omega)).symm
    · rw [cψ_of_not_lt hpn hc h, zero_mul, mul_zero]
  d_comm j l hjl := by
    rw [← map_mul, ← map_mul]; congr 1; apply Subtype.ext
    by_cases h : l + 1 < n
    · change (cψ i hpn hc j).1 * (cψ i hpn hc l).1 = (cψ i hpn hc l).1 * (cψ i hpn hc j).1
      rw [cψ_val_of_lt hpn hc h, cψ_val_of_lt hpn hc (by omega)]
      exact ψ_mul_ψ _ _ (by omega)
    · rw [cψ_of_not_lt hpn hc h, zero_mul, mul_zero]
  d_sq j := by
    rw [← map_mul, ← map_zero (toCorner (e_mul_self i)), toCorner_eq_iff]
    by_cases h : j + 1 < n
    · change (cψ i hpn hc j).1 * (cψ i hpn hc j).1 * e i = 0 * e i
      rw [cψ_val_of_lt hpn hc h, ψ_sq _ (by omega), if_pos (hc.lbl_succ (by omega) (by omega) _),
        zero_mul]
    · rw [cψ_of_not_lt hpn hc h, zero_mul]
  braid j := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, toCorner_eq_iff]
    by_cases h : j + 2 < n
    · change (cψ i hpn hc j).1 * (cψ i hpn hc (j + 1)).1 * (cψ i hpn hc j).1 * e i =
        (cψ i hpn hc (j + 1)).1 * (cψ i hpn hc j).1 * (cψ i hpn hc (j + 1)).1 * e i
      rw [cψ_val_of_lt hpn hc (by omega), cψ_val_of_lt hpn hc h, ← sub_eq_zero, ← sub_mul,
        show p + (j + 1) = p + j + 1 by omega, braid _ (by omega), if_neg]
      rintro ⟨-, hne⟩
      exact hne (hc.lbl_succ (by omega) (by omega) _)
    · rw [cψ_of_not_lt hpn hc (show ¬ j + 1 + 1 < n by omega)]
      simp
  x_d_sub j h := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (toCorner (e_mul_self i)), toCorner_eq_iff]
    change ((cx i hpn ⟨j, by omega⟩).1 * (cψ i hpn hc j).1 -
      (cψ i hpn hc j).1 * (cx i hpn ⟨j + 1, h⟩).1) * e i = 1 * e i
    rw [cψ_val_of_lt hpn hc h, cx_val, cx_val, one_mul]
    exact (dot_cross_left (p + j) (by omega) i).trans
      (if_pos (hc.lbl_succ (by omega) (by omega) _))
  d_x_sub j h := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (toCorner (e_mul_self i)), toCorner_eq_iff]
    change ((cψ i hpn hc j).1 * (cx i hpn ⟨j, by omega⟩).1 -
      (cx i hpn ⟨j + 1, h⟩).1 * (cψ i hpn hc j).1) * e i = 1 * e i
    rw [cψ_val_of_lt hpn hc h, cx_val, cx_val, one_mul]
    exact (dot_cross_right (p + j) (by omega) i).trans
      (if_pos (hc.lbl_succ (by omega) (by omega) _))
  d_zero j h := by
    rw [cψ_of_not_lt hpn hc (by omega), map_zero]

theorem val_prod_cψ (hpn : p + n ≤ m) (hc : IsConstOn i p n) :
    (((w0Word n).map (cψ (k := k) (Q := Q) i hpn hc)).prod).1 = ψw (blockWord p n) := by
  rw [← Subring.coe_subtype, map_list_prod, List.map_map, ψw, blockWord, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact cψ_val_of_lt hpn hc (lt_of_mem_w0Word hj)

theorem val_prod_cx (hpn : p + n ≤ m) :
    ((List.ofFn fun a => cx (k := k) (Q := Q) i hpn a ^ (n - 1 - a)).prod).1 =
      pol (blockDelta p n) := by
  rw [← Subring.coe_subtype, map_list_prod, List.map_ofFn, blockDelta, ← List.prod_ofFn,
    map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp only [Function.comp_apply, map_pow, Subring.coe_subtype, dif_pos
    (show p + (a : ℕ) < m by omega), pol_X]
  rfl

end family

/-- An element `u v E` is idempotent if `E` is an idempotent commuting with `u, v` and
`v u v E = v E`. -/
theorem isIdempotentElem_of_key {R : Type*} [Ring R] {u v E : R} (hE : IsIdempotentElem E)
    (hu : E * u = u * E) (hv : E * v = v * E) (hk : v * u * v * E = v * E) :
    IsIdempotentElem (u * v * E) := by
  unfold IsIdempotentElem
  calc u * v * E * (u * v * E) = u * (v * u * v * E) * E := by
        rw [show u * v * E * (u * v * E) = u * v * (E * u) * v * E by noncomm_ring, hu,
          show u * v * (u * E) * v * E = u * v * u * (E * v) * E by noncomm_ring, hv]
        noncomm_ring
    _ = u * v * E := by rw [hk, mul_assoc, mul_assoc, hE.eq, mul_assoc]

/-- **KL I §2.2, Example 3 and §2.5.** The nilHecke idempotent
`e_{i_p, n} = x_p^{n-1} ⋯ x_{p+n-2} ψ_{w_0} 1_i` on a block `[p, p + n)` of strands with
constant labels is an idempotent of `R(ν)`. -/
theorem isIdempotentElem_blockIdem {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m)
    (hc : IsConstOn i p n) : IsIdempotentElem (blockIdem i p n : A) := by
  have key := (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc).key
  have hW : ((w0Word n).map fun j =>
      toCorner (e_mul_self i) (cψ (k := k) (Q := Q) i hpn hc j)).prod =
      toCorner (e_mul_self i) ((w0Word n).map (cψ (k := k) (Q := Q) i hpn hc)).prod := by
    rw [map_list_prod, List.map_map]; rfl
  have hX : (List.ofFn fun a =>
      toCorner (e_mul_self i) (cx (k := k) (Q := Q) i hpn a) ^ (n - 1 - a)).prod =
      toCorner (e_mul_self i) (List.ofFn fun a => cx i hpn a ^ (n - 1 - a)).prod := by
    rw [map_list_prod, List.map_ofFn]; congr 2; funext a; simp
  rw [hW, hX, ← map_mul, ← map_mul, toCorner_eq_iff] at key
  simp only [Subring.coe_mul, val_prod_cψ, val_prod_cx] at key
  rw [blockIdem, blockElt]
  exact isIdempotentElem_of_key (e_mul_self i) (e_commute_pol i _).eq
    (blockψ_mul_e hc).symm key


/-- **KL I §2.2, Example 3.** The image `ψ(e_{i_p,n}) = 1_i ψ_{w_0}^{rev} x^δ` of the block
idempotent under the antiinvolution `ψ` is an idempotent. -/
theorem isIdempotentElem_hflip_blockIdem {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m)
    (hc : IsConstOn i p n) : IsIdempotentElem (hflip (blockIdem i p n : A)) := by
  unfold IsIdempotentElem
  rw [← hflip_mul, (isIdempotentElem_blockIdem hpn hc).eq]

/-! ### Comparison with the nilHecke ring -/

/-- **KL I §2.2, Example 3**: when all labels are equal (`ν = m i`), the block idempotent on all
strands acts on `k[x_1, …, x_m]` as the nilHecke idempotent `e_m = x^δ ∂_{w_0}`; i.e. it is the
idempotent `e_{i,m}` corresponding to `e_m` under `R(m i) ≅ NH_m`. -/
theorem toNH_blockIdem {c : I} (hν : ∀ a ∈ ν, a = c) (t : Seq ν) :
    toNH hν Q (blockIdem t 0 m) = idemNH k m := by
  rw [blockIdem, blockElt, map_mul, map_mul, toNH_e, mul_one, toNH_pol, toNH_ψw, idemNH]
  congr 2
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [dif_pos (by omega)]
    congr 2
    exact Fin.ext (zero_add _)
  · simp [blockWord]

theorem nilHeckeEquivOfForall_blockIdem [IsDomain k] {c : I} (hν : ∀ a ∈ ν, a = c)
    (t : Seq ν) : nilHeckeEquivOfForall hν Q (blockIdem t 0 m) = ⟨idemNH k m, idemNH_mem⟩ :=
  Subtype.ext ((coe_nilHeckeEquivOfForall hν Q _).trans (toNH_blockIdem hν t))

/-! ### Small blocks -/

theorem blockElt_zero (p : ℕ) : (blockElt p 0 : A) = 1 := by
  simp [blockElt, blockDelta, blockWord, w0Word]

theorem blockElt_one (p : ℕ) : (blockElt p 1 : A) = 1 := by
  simp [blockElt, blockDelta, blockWord, w0Word]

/-- The divided power `i^{(2)}` on the strands `p, p + 1`: `e_{i,2} = x_p ψ_p`. -/
theorem blockElt_two {p : ℕ} (h : p + 1 < m) : (blockElt p 2 : A) = x ⟨p, by omega⟩ * ψ p := by
  simp only [blockElt, blockDelta, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, add_zero,
    dif_pos (show p < m by omega), dif_pos h, pow_zero, mul_one, blockWord, w0Word,
    List.range_zero, List.nil_append, List.range_succ, List.map_cons, List.map_nil, ψw_cons,
    ψw_nil]
  simp

/-! ### Degree zero -/

section grading

variable (G : GradingDatum Q)

omit [DecidableEq I] in
theorem wordProd_smul_of_forall {ρ : List ℕ} {i : Seq ν}
    (h : ∀ j ∈ ρ, ∀ hj : j + 1 < m, i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, hj⟩) :
    wordProd m ρ • i = i := by
  induction ρ with
  | nil => simp [wordProd]
  | cons j ρ ih =>
    rw [wordProd_cons', mul_smul, ih fun l hl => h l (List.mem_cons_of_mem _ hl)]
    by_cases hj : j + 1 < m
    · exact sadj_smul_eq_self hj (h j List.mem_cons_self hj)
    · rw [sadj_of_not_lt hj, one_smul]

omit [DecidableEq I] in
theorem degW_of_forall {ρ : List ℕ} {i : Seq ν} {c : I} (hρ : ∀ j ∈ ρ, j + 1 < m)
    (h : ∀ j ∈ ρ, ∀ hj : j + 1 < m, i.lbl ⟨j, by omega⟩ = c ∧ i.lbl ⟨j + 1, hj⟩ = c) :
    G.degW ρ i = -(ρ.length : ℤ) * G.degX c := by
  induction ρ with
  | nil => simp [GradingDatum.degW]
  | cons j ρ ih =>
    have hρ' : ∀ l ∈ ρ, l + 1 < m := fun l hl => hρ l (List.mem_cons_of_mem _ hl)
    have h' := fun l hl => h l (List.mem_cons_of_mem _ hl)
    rw [GradingDatum.degW, ih hρ' h', wordProd_smul_of_forall
      (fun l hl hl' => (h' l hl hl').1.trans (h' l hl hl').2.symm),
      G.dψ_of_lt (hρ j List.mem_cons_self), (h j List.mem_cons_self (hρ j List.mem_cons_self)).1,
      (h j List.mem_cons_self (hρ j List.mem_cons_self)).2, G.degΨ_self, List.length_cons]
    push_cast; ring

theorem sum_fin_sub_one_sub (n : ℕ) : ∑ a : Fin n, (n - 1 - a : ℕ) = n.choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a) n, Finset.sum_range_reflect (fun j => j) n,
    Finset.sum_range_id, Nat.choose_two_right]

omit [DecidableEq I] in
theorem blockDelta_isWeightedHomogeneous {i : Seq ν} {p n : ℕ} {c : I} (hpn : p + n ≤ m)
    (hcl : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → i.lbl a = c) :
    (blockDelta p n : MvPolynomial (Fin m) k).IsWeightedHomogeneous
      (fun b => G.degX (i.lbl b)) ((n.choose 2 : ℕ) • G.degX c) := by
  rw [← sum_fin_sub_one_sub, Finset.sum_smul]
  refine IsWeightedHomogeneous.prod _ _ _ fun a _ => ?_
  split_ifs with h
  · have := (isWeightedHomogeneous_X k (fun b => G.degX (i.lbl b)) ⟨p + a, h⟩).pow (n - 1 - a)
    rwa [hcl _ (by simp) (by simp)] at this
  · exact absurd (by omega) h

/-- **KL I §2.2, Example 3**: the block idempotent `e_{i_p,n}` has degree `0` (for any grading
datum, in particular for the KL I grading `klGradingDatum`). -/
theorem blockIdem_mem_grade {i : Seq ν} {p n : ℕ} (hpn : p + n ≤ m) (hc : IsConstOn i p n) :
    (blockIdem i p n : A) ∈ G.grade ν 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [blockIdem, blockElt_zero, one_mul]; exact G.e_mem_grade i
  set c := i.lbl ⟨p, by omega⟩
  have hcl : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → i.lbl a = c :=
    fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have h1 := G.pol_mul_e_mem_grade i (blockDelta_isWeightedHomogeneous G hpn hcl)
  have h2 := G.ψw_mul_pol_mul_e_mem_grade (blockWord p n) i (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, degW_of_forall G (c := c)
    (fun j hj => by have := mem_blockWord hj; omega)
    (fun j hj hj' => ⟨hcl _ (mem_blockWord hj).1 (by simp only; have := mem_blockWord hj; omega),
      hcl _ (by simp only; have := mem_blockWord hj; omega)
        (by simp only; have := mem_blockWord hj; omega)⟩)] at h2
  have h3 := SetLike.mul_mem_graded h1 h2
  rw [length_blockWord] at h3
  convert h3 using 2
  · rw [nsmul_eq_mul]; ring
  · rw [blockIdem, blockElt, mul_assoc (pol _) (e i), ← mul_assoc (e i), ← blockψ_mul_e hc,
      mul_assoc (ψw _) (e i) (e i), e_mul_self, ← mul_assoc]

end grading

/-! ### Commutation of blocks with distant generators -/

theorem commute_x_ψw {a : Fin m} {ρ : List ℕ} (h : ∀ j ∈ ρ, (a : ℕ) ≠ j ∧ (a : ℕ) ≠ j + 1) :
    Commute (x a : A) (ψw ρ) := by
  rw [ψw]
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact x_mul_ψ a j (h j hj).1 (h j hj).2

theorem commute_ψ_ψw {j : ℕ} {ρ : List ℕ} (h : ∀ l ∈ ρ, j + 1 < l ∨ l + 1 < j) :
    Commute (ψ j : A) (ψw ρ) := by
  rw [ψw]
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
  rcases h l hl with h' | h'
  · exact ψ_mul_ψ j l h'
  · exact (ψ_mul_ψ l j h').symm

theorem pol_blockDelta_eq (p n : ℕ) : (pol (blockDelta p n) : A) =
    (List.ofFn fun a : Fin n => pol (if h : p + a < m then X ⟨p + a, h⟩ ^ (n - 1 - a) else 1 :
      MvPolynomial (Fin m) k)).prod := by
  rw [blockDelta, ← List.prod_ofFn, map_list_prod, List.map_ofFn]; rfl

/-- The dots of a block commute with every `y` commuting with the dots of the block. -/
theorem commute_pol_blockDelta {p n : ℕ} {y : A}
    (h : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → Commute (x a) y) :
    Commute (pol (blockDelta p n) : A) y := by
  rw [pol_blockDelta_eq]
  refine Commute.list_prod_left _ _ fun z hz => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hz
  split_ifs with ha
  · rw [map_pow, pol_X]; exact (h _ (by simp) (by simp)).pow_left _
  · rw [map_one]; exact Commute.one_left _

theorem commute_x_blockElt {a : Fin m} {p n : ℕ} (h : (a : ℕ) < p ∨ p + n ≤ a) :
    Commute (x a : A) (blockElt p n) := by
  refine Commute.mul_right ?_ (commute_x_ψw fun j hj => ?_)
  · rw [← pol_X]; exact pol_commute _ _
  · have := mem_blockWord hj; omega

theorem commute_ψ_blockElt {j p n : ℕ} (h : j + 1 < p ∨ p + n ≤ j) :
    Commute (ψ j : A) (blockElt p n) := by
  refine Commute.mul_right ?_ (commute_ψ_ψw fun l hl => ?_)
  · exact (commute_pol_blockDelta fun a h1 h2 => x_mul_ψ a j (by omega) (by omega)).symm
  · have := mem_blockWord hl; omega

theorem commute_ψw_blockElt {ρ : List ℕ} {p n : ℕ} (h : ∀ j ∈ ρ, j + 1 < p ∨ p + n ≤ j) :
    Commute (ψw ρ : A) (blockElt p n) := by
  rw [ψw]
  refine Commute.list_prod_left _ _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact commute_ψ_blockElt (h j hj)

/-- Blocks on disjoint sets of strands commute. -/
theorem commute_blockElt_blockElt {p n q l : ℕ} (h : p + n ≤ q ∨ q + l ≤ p) :
    Commute (blockElt p n : A) (blockElt q l) := by
  refine Commute.mul_left ?_ (commute_ψw_blockElt fun j hj => ?_)
  · refine commute_pol_blockDelta fun a h1 h2 => commute_x_blockElt ?_
    omega
  · have := mem_blockWord hj; omega

/-! ### Several blocks: the idempotents `1_i` for divided-power sequences -/

/-- Blocks `(p, n)` (strands `[p, p + n)`) for the sequence `i`: in range, with constant labels,
and pairwise disjoint. -/
structure IsBlocks (i : Seq ν) (bs : List (ℕ × ℕ)) : Prop where
  le : ∀ b ∈ bs, b.1 + b.2 ≤ m
  const : ∀ b ∈ bs, IsConstOn i b.1 b.2
  disj : bs.Pairwise fun b c => b.1 + b.2 ≤ c.1 ∨ c.1 + c.2 ≤ b.1

/-- The product of the nilHecke idempotents `x^δ ψ_{w_0}` of the blocks `bs` (without
idempotent). -/
noncomputable def blocksElt (bs : List (ℕ × ℕ)) : A := (bs.map fun b => blockElt b.1 b.2).prod

/-- **KL I §2.5**: the idempotent `1_i = e_{i_1,n_1} ⊗ ⋯ ⊗ e_{i_r,n_r}` for the divided-power
expression with expansion `î = i` and divided powers on the blocks `bs`. -/
noncomputable def divIdem (i : Seq ν) (bs : List (ℕ × ℕ)) : A := blocksElt bs * e i

@[simp] theorem blocksElt_nil : (blocksElt [] : A) = 1 := rfl

theorem blocksElt_cons (b : ℕ × ℕ) (bs : List (ℕ × ℕ)) :
    (blocksElt (b :: bs) : A) = blockElt b.1 b.2 * blocksElt bs := by
  simp [blocksElt]

@[simp] theorem divIdem_nil (i : Seq ν) : (divIdem i [] : A) = e i := by
  simp [divIdem]

omit [DecidableEq I] in
theorem IsBlocks.tail {i : Seq ν} {b : ℕ × ℕ} {bs : List (ℕ × ℕ)} (h : IsBlocks i (b :: bs)) :
    IsBlocks i bs :=
  ⟨fun c hc => h.le c (List.mem_cons_of_mem _ hc),
    fun c hc => h.const c (List.mem_cons_of_mem _ hc), (List.pairwise_cons.1 h.disj).2⟩

theorem blocksElt_mul_e {i : Seq ν} {bs : List (ℕ × ℕ)}
    (h : ∀ b ∈ bs, IsConstOn i b.1 b.2) : (blocksElt bs * e i : A) = e i * blocksElt bs := by
  rw [blocksElt]
  refine (Commute.list_prod_left _ _ fun y hy => ?_).eq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  exact blockElt_mul_e (h b hb)

theorem commute_blocksElt {bs : List (ℕ × ℕ)} {y : A}
    (h : ∀ b ∈ bs, Commute (blockElt b.1 b.2 : A) y) : Commute (blocksElt bs : A) y := by
  rw [blocksElt]
  refine Commute.list_prod_left _ _ fun z hz => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hz
  exact h b hb

/-- **KL I §2.5**: `1_i` is an idempotent. -/
theorem isIdempotentElem_divIdem {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    IsIdempotentElem (divIdem i bs : A) := by
  induction bs with
  | nil => rw [divIdem_nil]; exact e_mul_self i
  | cons b bs ih =>
    have hb := h.const b List.mem_cons_self
    have hcomm : Commute (blockElt b.1 b.2 : A) (blocksElt bs) :=
      (commute_blocksElt fun c hc => commute_blockElt_blockElt
        ((List.pairwise_cons.1 h.disj).1 c hc).symm).symm
    have : (divIdem i (b :: bs) : A) = blockIdem i b.1 b.2 * divIdem i bs := by
      rw [divIdem, divIdem, blockIdem, blocksElt_cons, mul_assoc, mul_assoc,
        ← mul_assoc (e i), ← blocksElt_mul_e h.tail.const, mul_assoc, e_mul_self]
    rw [this]
    refine IsIdempotentElem.mul_of_commute ?_ (isIdempotentElem_blockIdem
      (h.le b List.mem_cons_self) hb) (ih h.tail)
    rw [Commute, SemiconjBy, blockIdem, divIdem, mul_assoc, ← mul_assoc (e i),
      ← blocksElt_mul_e h.tail.const, mul_assoc, e_mul_self, ← mul_assoc, hcomm.eq,
      mul_assoc, mul_assoc, ← mul_assoc (e i), ← blockElt_mul_e hb, mul_assoc, e_mul_self,
      ← mul_assoc]

/-- The image `ψ(1_i)` of `1_i` under the antiinvolution is an idempotent. -/
theorem isIdempotentElem_hflip_divIdem {i : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks i bs) :
    IsIdempotentElem (hflip (divIdem i bs : A)) := by
  unfold IsIdempotentElem
  rw [← hflip_mul, (isIdempotentElem_divIdem h).eq]

/-- **KL I §2.5**: `1_i` has degree `0`. -/
theorem divIdem_mem_grade (G : GradingDatum Q) {i : Seq ν} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i bs) : (divIdem i bs : A) ∈ G.grade ν 0 := by
  induction bs with
  | nil => rw [divIdem_nil]; exact G.e_mem_grade i
  | cons b bs ih =>
    have : (divIdem i (b :: bs) : A) = blockIdem i b.1 b.2 * divIdem i bs := by
      rw [divIdem, divIdem, blockIdem, blocksElt_cons, mul_assoc, mul_assoc,
        ← mul_assoc (e i), ← blocksElt_mul_e h.tail.const, mul_assoc, e_mul_self]
    rw [this, ← zero_add (0 : ℤ)]
    exact SetLike.mul_mem_graded
      (blockIdem_mem_grade G (h.le b List.mem_cons_self) (h.const b List.mem_cons_self))
      (ih h.tail)


/-! ### Divided-power expressions `Seq'(ν)` -/

section DivSeq

/-- The expansion `î = i_1 ⋯ i_1 ⋯ i_r ⋯ i_r` of a divided-power expression
`i = i_1^{(n_1)} ⋯ i_r^{(n_r)}`, the latter given as the list of pairs `(i_a, n_a)`. -/
def expandDiv (d : List (I × ℕ)) : List I := d.flatMap fun q => List.replicate q.2 q.1

/-- The blocks of strands `[p_a, p_a + n_a)` of a divided-power expression, starting at
position `p`. -/
def blocksDiv : List (I × ℕ) → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | q :: d, p => (p, q.2) :: blocksDiv d (p + q.2)

omit [DecidableEq I] in
theorem le_of_mem_blocksDiv {d : List (I × ℕ)} {p : ℕ} {b : ℕ × ℕ} (h : b ∈ blocksDiv d p) :
    p ≤ b.1 := by
  induction d generalizing p with
  | nil => simp [blocksDiv] at h
  | cons q d ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_rfl
    · have := ih h; omega

omit [DecidableEq I] in
theorem pairwise_blocksDiv (d : List (I × ℕ)) (p : ℕ) :
    (blocksDiv d p).Pairwise fun b c => b.1 + b.2 ≤ c.1 ∨ c.1 + c.2 ≤ b.1 := by
  induction d generalizing p with
  | nil => exact List.Pairwise.nil
  | cons q d ih =>
    refine List.Pairwise.cons (fun c hc => Or.inl (le_of_mem_blocksDiv hc)) (ih _)

omit [DecidableEq I] in
theorem blocksDiv_spec (d : List (I × ℕ)) (pre : List I) :
    ∀ b ∈ blocksDiv d pre.length, b.1 + b.2 ≤ (pre ++ expandDiv d).length ∧
      ∀ a₁ a₂ (h₁ : a₁ < (pre ++ expandDiv d).length) (h₂ : a₂ < (pre ++ expandDiv d).length),
        b.1 ≤ a₁ → a₁ < b.1 + b.2 → b.1 ≤ a₂ → a₂ < b.1 + b.2 →
          (pre ++ expandDiv d)[a₁] = (pre ++ expandDiv d)[a₂] := by
  induction d generalizing pre with
  | nil => simp [blocksDiv]
  | cons q d ih =>
    have hL : pre ++ expandDiv (q :: d) = (pre ++ List.replicate q.2 q.1) ++ expandDiv d := by
      simp [expandDiv, List.flatMap_cons]
    intro b hb
    rw [hL]
    rcases List.mem_cons.1 hb with rfl | hb
    · have hget : ∀ a (l : pre.length ≤ a) (u : a < pre.length + q.2)
          (ha : a < (pre ++ List.replicate q.2 q.1 ++ expandDiv d).length),
          (pre ++ List.replicate q.2 q.1 ++ expandDiv d)[a] = q.1 := by
        intro a l u ha
        have ha' : a < (pre ++ List.replicate q.2 q.1).length := by
          simp only [List.length_append, List.length_replicate]; omega
        rw [List.getElem_append_left ha', List.getElem_append_right l, List.getElem_replicate]
      refine ⟨by simp only [List.length_append, List.length_replicate]; omega,
        fun a₁ a₂ h₁ h₂ l₁ u₁ l₂ u₂ => ?_⟩
      rw [hget a₁ l₁ u₁ h₁, hget a₂ l₂ u₂ h₂]
    · have := ih (pre ++ List.replicate q.2 q.1) b (by simpa using hb)
      exact this

/-- The sequence `Seq ν` given by a list with multiset `ν`. -/
def Seq.ofList {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) : Seq ν :=
  ⟨fun a => l.get (Fin.cast (by rw [← h, Multiset.coe_card]) a), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (by rw [← h, Multiset.coe_card]) l.get,
      List.ofFn_get, h]⟩

omit [DecidableEq I] in
theorem Seq.ofList_lbl {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν)
    (a : Fin (Multiset.card ν)) :
    (Seq.ofList l h).lbl a = l[(a : ℕ)]'(by rw [← Multiset.coe_card, h]; exact a.2) := rfl

omit [DecidableEq I] in
/-- The expansion and the blocks of a divided-power expression of weight `ν`. -/
theorem isBlocks_ofList (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    IsBlocks (Seq.ofList (expandDiv d) h) (blocksDiv d 0) := by
  have hm : (expandDiv d).length = m := by rw [← Multiset.coe_card, h]
  have := blocksDiv_spec d []
  simp only [List.length_nil, List.nil_append] at this
  refine ⟨fun b hb => hm ▸ (this b hb).1, fun b hb a₁ a₂ l₁ u₁ l₂ u₂ => ?_,
    pairwise_blocksDiv d 0⟩
  rw [Seq.ofList_lbl, Seq.ofList_lbl]
  exact (this b hb).2 _ _ (by rw [hm]; exact a₁.2) (by rw [hm]; exact a₂.2) l₁ u₁ l₂ u₂

/-- **KL I §2.5**: the idempotent `1_i = e_{i_1,n_1} ⊗ ⋯ ⊗ e_{i_r,n_r} ∈ R(ν)` of a
divided-power expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)} ∈ Seq'(ν)` (given as the list `d` of
pairs `(i_a, n_a)` with `∑ n_a i_a = ν`). -/
noncomputable def divIdemOf (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) : A :=
  divIdem (Seq.ofList (expandDiv d) h) (blocksDiv d 0)

theorem isIdempotentElem_divIdemOf (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    IsIdempotentElem (divIdemOf d h : A) :=
  isIdempotentElem_divIdem (isBlocks_ofList d h)

theorem divIdemOf_mem_grade (G : GradingDatum Q) (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = ν) : (divIdemOf d h : A) ∈ G.grade ν 0 :=
  divIdem_mem_grade G (isBlocks_ofList d h)

end DivSeq

end KLRAlgebra

end Categorification.KLR
