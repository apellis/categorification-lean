/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Symmetries
import Categorification.KLR.Filtration
import Categorification.TypeA.Parabolic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Concatenation of sequences and the inclusion `R(ν) ⊗ R(ν') → R(ν + ν')`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6 "Induction and restriction": the (non-unital)
inclusion of algebras
`ι_{ν,ν'} : R(ν) ⊗ R(ν') → R(ν + ν')`
"putting diagrams next to each other". It sends `1_i ⊗ 1_j` to `1_{ij}` and the unit to the
idempotent `1_{ν,ν'} = ∑_{i,j} 1_{ij}`.

## Main definitions

* `Seq.append i j : Seq (ν + ν')` — the concatenation `ij` of `i ∈ Seq ν`, `j ∈ Seq ν'`
  (positions are identified through `TypeA.blockEquiv`).
* `KLRAlgebra.oneConcat ν ν' = ∑_{i,j} e (i.append j)` — the idempotent `1_{ν,ν'}`.
* `KLRAlgebra.concatHom : R(ν) ⊗[k] R(ν') →ₐ[k] Corner` — the unital algebra map into the
  corner ring `1_{ν,ν'} R(ν + ν') 1_{ν,ν'}` (whose unit is `1_{ν,ν'}`).
* `KLRAlgebra.concat : R(ν) ⊗[k] R(ν') →ₗ[k] R(ν + ν')` — the paper's `ι_{ν,ν'}`, the
  composite with the inclusion of the corner; it is multiplicative (`concat_mul`) but not
  unital: `concat 1 = oneConcat` (`concat_one`).

The images of generators are `concat_e_tmul_e`, `concat_x_tmul_one`, `concat_one_tmul_x`,
`concat_ψ_tmul_one`, `concat_one_tmul_ψ`. Injectivity is proved in
`Categorification.KLR.InductionFree` (`KLRAlgebra.concat_injective`).

## Implementation

The corner ring is Mathlib's `IsIdempotentElem.Corner`; we equip it with a `k`-algebra
structure (`algebraMap c = c • 1_{ν,ν'}`). The two factors are handled uniformly by
`BlockEmb`: the data of a block of consecutive positions of `ν + ν'` together with the
fibres of the restriction of labels to this block.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*}

/-! ### Concatenation of sequences -/

namespace Seq

variable {ν ν' : Multiset I}

/-- `card ν + card ν' = card (ν + ν')`. -/
theorem card_add' (ν ν' : Multiset I) :
    Multiset.card ν + Multiset.card ν' = Multiset.card (ν + ν') :=
  (Multiset.card_add ν ν').symm

/-- The position `a` of the first block of `ν + ν'`. -/
def posL (ν' : Multiset I) (a : Fin (Multiset.card ν)) : Fin (Multiset.card (ν + ν')) :=
  blockEquiv (card_add' ν ν') (Sum.inl a)

/-- The position `b` of the second block of `ν + ν'` (i.e. `card ν + b`). -/
def posR (ν : Multiset I) (b : Fin (Multiset.card ν')) : Fin (Multiset.card (ν + ν')) :=
  blockEquiv (card_add' ν ν') (Sum.inr b)

@[simp] theorem posL_val (a : Fin (Multiset.card ν)) : (posL ν' a).val = a.val := rfl

@[simp] theorem posR_val (b : Fin (Multiset.card ν')) :
    (posR ν b).val = Multiset.card ν + b.val := rfl

/-- The concatenation `ij` of two sequences. -/
def append (i : Seq ν) (j : Seq ν') : Seq (ν + ν') :=
  ⟨fun a => Sum.elim i.1 j.1 ((blockEquiv (card_add' ν ν')).symm a), by
    show Multiset.map (Sum.elim i.1 j.1 ∘ (blockEquiv (card_add' ν ν')).symm) _ = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, ← Finset.univ_disjSum_univ,
      Finset.val_disjSum, Multiset.disjSum, Multiset.map_add, Multiset.map_map,
      Multiset.map_map]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    rw [i.2, j.2]⟩

@[simp] theorem append_posL (i : Seq ν) (j : Seq ν') (a : Fin (Multiset.card ν)) :
    (i.append j).1 (posL ν' a) = i.1 a := by
  simp [append, posL]

@[simp] theorem append_posR (i : Seq ν) (j : Seq ν') (b : Fin (Multiset.card ν')) :
    (i.append j).1 (posR ν b) = j.1 b := by
  simp [append, posR]

theorem append_inj {i i' : Seq ν} {j j' : Seq ν'} :
    i.append j = i'.append j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro he
    constructor
    · apply Subtype.ext; funext a
      have := congrArg (fun s : Seq (ν + ν') => s.1 (posL ν' a)) he
      simpa using this
    · apply Subtype.ext; funext b
      have := congrArg (fun s : Seq (ν + ν') => s.1 (posR ν b)) he
      simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem blockPerm_smul_append (a : Perm (Fin (Multiset.card ν)))
    (b : Perm (Fin (Multiset.card ν'))) (i : Seq ν) (j : Seq ν') :
    blockPerm (card_add' ν ν') a b • i.append j = (a • i).append (b • j) := by
  apply Subtype.ext; funext v
  obtain ⟨s, rfl⟩ := (blockEquiv (card_add' ν ν')).surjective v
  rw [smul_apply, ← Perm.inv_def, blockPerm_inv]
  cases s with
  | inl x =>
    rw [blockPerm_inl]
    exact (append_posL i j _).trans (append_posL (a • i) (b • j) x).symm
  | inr y =>
    rw [blockPerm_inr]
    exact (append_posR i j _).trans (append_posR (a • i) (b • j) y).symm

theorem sadj_smul_append_left {j₀ : ℕ} (hj : j₀ + 1 < Multiset.card ν) (i : Seq ν)
    (j : Seq ν') :
    sadj (Multiset.card (ν + ν')) j₀ • i.append j = (sadj (Multiset.card ν) j₀ • i).append j := by
  rw [sadj_eq_blockPerm_left (card_add' ν ν') hj, blockPerm_smul_append, one_smul]

theorem sadj_smul_append_right {j₀ : ℕ} (hj : j₀ + 1 < Multiset.card ν') (i : Seq ν)
    (j : Seq ν') :
    sadj (Multiset.card (ν + ν')) (Multiset.card ν + j₀) • i.append j =
      i.append (sadj (Multiset.card ν') j₀ • j) := by
  rw [sadj_eq_blockPerm_right (card_add' ν ν') hj, blockPerm_smul_append, one_smul]

end Seq

/-! ### The corner ring as a `k`-algebra -/

section Corner

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A] {E : A}

/-- The corner ring `E A E` of an idempotent `E` is a `k`-algebra, with
`algebraMap c = c • E`. -/
noncomputable instance cornerAlgebra (idem : IsIdempotentElem E) : Algebra k idem.Corner :=
  RingHom.toAlgebra'
    { toFun := fun c => ⟨algebraMap k A c * E, algebraMap k A c, by
        show E * algebraMap k A c * E = algebraMap k A c * E
        rw [← Algebra.commutes, mul_assoc, idem.eq]⟩
      map_one' := Subtype.ext <| by
        show algebraMap k A 1 * E = E
        rw [map_one, one_mul]
      map_mul' := fun c d => Subtype.ext <| by
        show algebraMap k A (c * d) * E = algebraMap k A c * E * (algebraMap k A d * E)
        have h1 : E * algebraMap k A d = algebraMap k A d * E := (Algebra.commutes d E).symm
        simp only [map_mul, mul_assoc]
        rw [← mul_assoc E, h1, mul_assoc, idem.eq]
      map_zero' := Subtype.ext <| by
        show algebraMap k A 0 * E = 0
        rw [map_zero, zero_mul]
      map_add' := fun c d => Subtype.ext <| by
        show algebraMap k A (c + d) * E = algebraMap k A c * E + algebraMap k A d * E
        rw [map_add, add_mul] }
    (fun c r => Subtype.ext <| by
      obtain ⟨r, s, rfl⟩ := r
      show algebraMap k A c * E * (E * s * E) = E * s * E * (algebraMap k A c * E)
      have h1 : E * (E * s * E) = E * s * E := by rw [← mul_assoc, ← mul_assoc, idem.eq]
      have h2 : E * s * E * E = E * s * E := by rw [mul_assoc, idem.eq]
      rw [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, h1, h2])

variable {idem : IsIdempotentElem E}

/-- The underlying element of `A` of an element of the corner. -/
def Corner.val (a : idem.Corner) : A := a.1

theorem Corner.val_injective : Function.Injective (Corner.val : idem.Corner → A) :=
  fun _ _ h => Subtype.ext h

theorem Corner.ext {a b : idem.Corner} (h : a.val = b.val) : a = b := Corner.val_injective h

@[simp] theorem Corner.val_mul (a b : idem.Corner) : (a * b).val = a.val * b.val := rfl
variable (idem) in
@[simp] theorem Corner.val_one : (1 : idem.Corner).val = E := rfl
@[simp] theorem Corner.val_add (a b : idem.Corner) : (a + b).val = a.val + b.val := rfl
variable (idem) in
@[simp] theorem Corner.val_zero : (0 : idem.Corner).val = 0 := rfl
@[simp] theorem Corner.val_sub (a b : idem.Corner) : (a - b).val = a.val - b.val := rfl
variable (idem) in
@[simp] theorem Corner.val_algebraMap (c : k) :
    (algebraMap k idem.Corner c).val = algebraMap k A c * E := rfl

/-- The underlying element of a corner element built from `r = E * r * E`. -/
def Corner.mk (r : A) (h : E * r * E = r) : idem.Corner := ⟨r, r, h⟩

@[simp] theorem Corner.val_mk (r : A) (h : E * r * E = r) : (Corner.mk (idem := idem) r h).val = r :=
  rfl

variable (idem) in
/-- The inclusion of the corner, as a non-unital ring homomorphism. -/
def cornerVal : idem.Corner →ₙ+* A where
  toFun a := a.val
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem cornerVal_apply (a : idem.Corner) : cornerVal idem a = a.val := rfl

@[simp] theorem Corner.val_sum {ι : Type*} (s : Finset ι) (f : ι → idem.Corner) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  map_sum (cornerVal idem) f s

@[simp] theorem Corner.val_pow (a : idem.Corner) (j : ℕ) (hj : j ≠ 0) :
    (a ^ j).val = a.val ^ j := by
  induction j with
  | zero => exact absurd rfl hj
  | succ j ih =>
    rcases j with _ | j
    · simp
    · rw [pow_succ, Corner.val_mul, ih (by omega), ← pow_succ]

theorem Corner.E_mul_val (a : idem.Corner) : E * a.val = a.val :=
  ((Subsemigroup.mem_corner_iff idem).1 a.2).1

theorem Corner.val_mul_E (a : idem.Corner) : a.val * E = a.val :=
  ((Subsemigroup.mem_corner_iff idem).1 a.2).2

theorem Corner.val_smul (c : k) (a : idem.Corner) : (c • a).val = c • a.val := by
  rw [Algebra.smul_def, Corner.val_mul, Corner.val_algebraMap, mul_assoc, Corner.E_mul_val,
    Algebra.smul_def]

theorem mul_E_mem (hE : IsIdempotentElem E) {r : A} (h : E * r = r * E) :
    E * (r * E) * E = r * E := by
  rw [← mul_assoc, h, mul_assoc, hE.eq, mul_assoc, hE.eq]

theorem mul_E_mul_mul_E (hE : IsIdempotentElem E) (a : A) {b : A} (hb : E * b = b * E) :
    a * E * (b * E) = a * b * E := by
  rw [mul_assoc a E, ← mul_assoc E b, hb, mul_assoc b E E, hE.eq, ← mul_assoc]

/-- The corner element `r * E` for `r` commuting with `E`. -/
def Corner.mkComm (r : A) (h : E * r = r * E) : idem.Corner := Corner.mk (r * E) (mul_E_mem idem h)

@[simp] theorem Corner.val_mkComm (r : A) (h : E * r = r * E) :
    (Corner.mkComm (idem := idem) r h).val = r * E := rfl

end Corner


namespace KLRAlgebra

/-! ### Block embeddings -/

/-- Data for embedding `R(μ)` into the corner `e_T R(ν) e_T`, as the strands at positions
`o, …, o + card μ - 1`: the finite set `T` of sequences is partitioned into the fibres
`F i` (`i ∈ Seq μ`) of sequences whose labels on the block are `i`, compatibly with the
action of the crossings of the block. -/
structure BlockEmb (μ ν : Multiset I) (T : Finset (Seq ν)) where
  /-- The first position of the block. -/
  o : ℕ
  /-- The positions of the block. -/
  pos : Fin (Multiset.card μ) → Fin (Multiset.card ν)
  pos_val : ∀ a, (pos a).val = o + a.val
  /-- The fibre over `i ∈ Seq μ`. -/
  F : Seq μ → Finset (Seq ν)
  disj : ∀ i i', i ≠ i' → Disjoint (F i) (F i')
  mem_T : ∀ s, s ∈ T ↔ ∃ i, s ∈ F i
  lbl : ∀ i s, s ∈ F i → ∀ a, s.1 (pos a) = i.1 a
  sadj_mem : ∀ j, j + 1 < Multiset.card μ → ∀ i s,
    s ∈ F (sadj (Multiset.card μ) j • i) ↔ sadj (Multiset.card ν) (o + j) • s ∈ F i

namespace BlockEmb

variable {μ ν : Multiset I} {T : Finset (Seq ν)} (B : BlockEmb μ ν T)

local notation "n₀" => Multiset.card μ
local notation "M" => Multiset.card ν

theorem lt_card {j : ℕ} (hj : j + 1 < n₀) : B.o + j + 1 < M := by
  have h1 := (B.pos ⟨j + 1, hj⟩).2
  rw [B.pos_val] at h1
  simp only at h1
  omega

theorem pos_eq (a : Fin n₀) : B.pos a = ⟨B.o + a.val, by rw [← B.pos_val]; exact (B.pos a).2⟩ :=
  Fin.ext (B.pos_val a)

theorem subset_T (i : Seq μ) : B.F i ⊆ T := fun s hs => (B.mem_T s).2 ⟨i, hs⟩

theorem sadj_mem_T {j : ℕ} (hj : j + 1 < n₀) (s : Seq ν) :
    s ∈ T ↔ sadj M (B.o + j) • s ∈ T := by
  rw [B.mem_T, B.mem_T]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨sadj n₀ j • i, ?_⟩
    rw [B.sadj_mem j hj, sadj_smul_smul]; exact hi
  · rintro ⟨i, hi⟩
    exact ⟨sadj n₀ j • i, (B.sadj_mem j hj i s).2 hi⟩

end BlockEmb

variable {k : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### Sums of idempotents -/

section eSum

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

variable (Q) in
/-- `e_T = ∑_{s ∈ T} e s` for a finite set `T` of sequences. -/
noncomputable def eSum (T : Finset (Seq ν)) : KLRAlgebra k Q ν := ∑ s ∈ T, e s

theorem e_mul_eSum (s : Seq ν) (T : Finset (Seq ν)) :
    (e s * eSum Q T : KLRAlgebra k Q ν) = if s ∈ T then e s else 0 := by
  rw [eSum, Finset.mul_sum]
  simp_rw [e_mul_e]
  rw [Finset.sum_ite_eq]

theorem eSum_mul_e (T : Finset (Seq ν)) (s : Seq ν) :
    (eSum Q T * e s : KLRAlgebra k Q ν) = if s ∈ T then e s else 0 := by
  rw [eSum, Finset.sum_mul]
  simp_rw [e_mul_e]
  rw [Finset.sum_ite_eq']

theorem eSum_mul_eSum (T T' : Finset (Seq ν)) :
    (eSum Q T * eSum Q T' : KLRAlgebra k Q ν) = eSum Q (T ∩ T') := by
  rw [eSum, Finset.sum_mul]
  simp_rw [e_mul_eSum]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, eSum]

theorem eSum_empty : (eSum Q (∅ : Finset (Seq ν)) : KLRAlgebra k Q ν) = 0 := by simp [eSum]

theorem eSum_idem (T : Finset (Seq ν)) : IsIdempotentElem (eSum Q T : KLRAlgebra k Q ν) := by
  rw [IsIdempotentElem, eSum_mul_eSum, Finset.inter_self]

theorem pol_mul_eSum (p : MvPolynomial (Fin m) k) (T : Finset (Seq ν)) :
    (pol p * eSum Q T : KLRAlgebra k Q ν) = eSum Q T * pol p := by
  rw [eSum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => ((e_commute_pol s p).eq).symm

theorem x_mul_eSum (a : Fin m) (T : Finset (Seq ν)) :
    (x a * eSum Q T : KLRAlgebra k Q ν) = eSum Q T * x a := by
  rw [← pol_X (k := k), pol_mul_eSum]

theorem ψ_mul_eSum (l : ℕ) (T T' : Finset (Seq ν)) (h : ∀ s, s ∈ T' ↔ sadj m l • s ∈ T) :
    (ψ l * eSum Q T : KLRAlgebra k Q ν) = eSum Q T' * ψ l := by
  rw [eSum, eSum, Finset.mul_sum, Finset.sum_mul]
  simp_rw [ψ_mul_e]
  refine Finset.sum_nbij' (sadj m l • ·) (sadj m l • ·) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_coe] at hs ⊢; rw [h, sadj_smul_smul]; exact hs
  · intro s hs; simp only [Finset.mem_coe] at hs ⊢; exact (h s).1 hs
  · intro s _; exact sadj_smul_smul l s
  · intro s _; exact sadj_smul_smul l s
  · intro s _; rfl

theorem ψ_mul_eSum_of_stable (l : ℕ) (T : Finset (Seq ν)) (h : ∀ s, s ∈ T ↔ sadj m l • s ∈ T) :
    (ψ l * eSum Q T : KLRAlgebra k Q ν) = eSum Q T * ψ l :=
  ψ_mul_eSum l T T h

/-- To compute `X * e_T` it suffices to compute each `X * e s`, `s ∈ T`. -/
theorem mul_eSum_congr {X Y : KLRAlgebra k Q ν} {T : Finset (Seq ν)}
    (h : ∀ s ∈ T, X * e s = Y * e s) : X * eSum Q T = Y * eSum Q T := by
  rw [eSum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl h

end eSum

namespace BlockEmb

variable {μ ν : Multiset I} {T : Finset (Seq ν)} (B : BlockEmb μ ν T)

local notation "n₀" => Multiset.card μ
local notation "M" => Multiset.card ν

/-! #### Computations in `R(ν)` -/

/-- `e_{F i}`: the sum of the idempotents of sequences with labels `i` on the block. -/
noncomputable abbrev eF (Q : I → I → MvPolynomial (Fin 2) k) (i : Seq μ) : KLRAlgebra k Q ν :=
  eSum Q (B.F i)

theorem eF_mul_eF (i i' : Seq μ) :
    (B.eF Q i * B.eF Q i' : KLRAlgebra k Q ν) = if i = i' then B.eF Q i else 0 := by
  rw [eSum_mul_eSum]
  split_ifs with h
  · rw [h, Finset.inter_self]
  · rw [Finset.disjoint_iff_inter_eq_empty.1 (B.disj i i' h), eSum_empty]

theorem eF_mul_E (i : Seq μ) : (B.eF Q i * eSum Q T : KLRAlgebra k Q ν) = B.eF Q i := by
  rw [eSum_mul_eSum, Finset.inter_eq_left.2 (B.subset_T i)]

theorem E_mul_eF (i : Seq μ) : (eSum Q T * B.eF Q i : KLRAlgebra k Q ν) = B.eF Q i := by
  rw [eSum_mul_eSum, Finset.inter_eq_right.2 (B.subset_T i)]

theorem sum_eF : (∑ i, B.eF Q i : KLRAlgebra k Q ν) = eSum Q T := by
  simp only [eSum]
  rw [← Finset.sum_biUnion (fun i _ i' _ h => B.disj i i' h)]
  congr 1
  ext s
  simp [B.mem_T]

theorem ψ_mul_eF {j : ℕ} (hj : j + 1 < n₀) (i : Seq μ) :
    (ψ (B.o + j) * B.eF Q i : KLRAlgebra k Q ν) = B.eF Q (sadj n₀ j • i) * ψ (B.o + j) :=
  ψ_mul_eSum _ _ _ fun s => B.sadj_mem j hj i s

theorem ψ_mul_E {j : ℕ} (hj : j + 1 < n₀) :
    (ψ (B.o + j) * eSum Q T : KLRAlgebra k Q ν) = eSum Q T * ψ (B.o + j) :=
  ψ_mul_eSum_of_stable _ _ fun s => B.sadj_mem_T hj s

omit [DecidableEq I] in
theorem lbl_of_mem {i : Seq μ} {s : Seq ν} (hs : s ∈ B.F i) {a : Fin n₀} {b : Fin M}
    (hb : b.val = B.o + a.val) : s.1 b = i.1 a := by
  rw [← B.lbl i s hs a]
  exact congrArg s.1 (Fin.ext (by rw [hb, B.pos_val]))

end BlockEmb

section polCorner

variable {ν : Multiset I}

variable (Q) in
/-- `q ↦ pol q * e_T`: a unital algebra map into the corner ring of `e_T`. -/
noncomputable def polCorner (T : Finset (Seq ν)) :
    MvPolynomial (Fin (Multiset.card ν)) k →ₐ[k] (eSum_idem (Q := Q) T).Corner where
  toFun q := Corner.mkComm (pol q) (pol_mul_eSum q T).symm
  map_one' := Corner.ext (by simp)
  map_mul' p q := Corner.ext (by
    simp only [Corner.val_mkComm, Corner.val_mul, map_mul]
    rw [mul_E_mul_mul_E (eSum_idem T) _ (pol_mul_eSum q T).symm])
  map_zero' := Corner.ext (by simp)
  map_add' p q := Corner.ext (by simp [add_mul])
  commutes' c := Corner.ext (by simp)

@[simp] theorem val_polCorner (T : Finset (Seq ν)) (q : MvPolynomial (Fin (Multiset.card ν)) k) :
    (polCorner Q T q).val = pol q * eSum Q T := rfl

end polCorner

namespace BlockEmb

variable {μ ν : Multiset I} {T : Finset (Seq ν)} (B : BlockEmb μ ν T)

local notation "n₀" => Multiset.card μ
local notation "M" => Multiset.card ν

/-! #### The generators in the corner ring -/

variable (Q) in
/-- The image of `e i`: `e_{F i}`. -/
noncomputable def gE (i : Seq μ) : (eSum_idem (Q := Q) T).Corner :=
  Corner.mk (B.eF Q i) (by rw [E_mul_eF, eF_mul_E])

variable (Q) in
/-- The image of `ψ j`: `ψ (o + j) * e_T` (zero if `j + 1 ≥ card μ`). -/
noncomputable def gψ (j : ℕ) : (eSum_idem (Q := Q) T).Corner :=
  if h : j + 1 < n₀ then Corner.mkComm (ψ (B.o + j)) (B.ψ_mul_E h).symm else 0

@[simp] theorem val_gE (i : Seq μ) : (B.gE Q i).val = B.eF Q i := rfl

theorem val_gψ {j : ℕ} (h : j + 1 < n₀) : (B.gψ Q j).val = ψ (B.o + j) * eSum Q T := by
  rw [gψ, dif_pos h]; rfl

variable (Q) in
/-- The images of the generators. -/
noncomputable def gen : Gen μ → (eSum_idem (Q := Q) T).Corner
  | .idem i => B.gE Q i
  | .dot a => polCorner Q T (X (B.pos a))
  | .cross j => B.gψ Q j

variable (Q) in
/-- The block embedding on the free algebra. -/
noncomputable def freeHom : FreeAlgebra k (Gen μ) →ₐ[k] (eSum_idem (Q := Q) T).Corner :=
  FreeAlgebra.lift k (B.gen Q)

@[simp] theorem freeHom_fe (i : Seq μ) : B.freeHom Q (fe k μ i) = B.gE Q i :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeHom_fx (a : Fin n₀) :
    B.freeHom Q (fx k μ a) = polCorner Q T (X (B.pos a)) :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeHom_fψ (j : ℕ) : B.freeHom Q (fψ k μ j) = B.gψ Q j :=
  FreeAlgebra.lift_ι_apply _ _

theorem freeHom_ncEval {r : ℕ} (f : Fin r → Fin n₀) (p : MvPolynomial (Fin r) k) :
    B.freeHom Q (ncEval (fun c => fx k μ (f c)) p) = polCorner Q T (rename (B.pos ∘ f) p) := by
  rw [ncEval_map]
  simp only [freeHom_fx]
  exact ncEval_algHom_X (polCorner Q T) (B.pos ∘ f) p

theorem pol_X_pos (a : Fin n₀) :
    (pol (X (B.pos a)) : KLRAlgebra k Q ν) = x ⟨B.o + a.val, by rw [← B.pos_val]; exact (B.pos a).2⟩ := by
  rw [pol_X]
  exact congrArg x (Fin.ext (B.pos_val a))

theorem gψ_of_not_lt {j : ℕ} (h : ¬ j + 1 < n₀) : B.gψ Q j = 0 := by
  rw [gψ, dif_neg h]

omit [DecidableEq I] in
theorem pos_mk (j : ℕ) (h : j < n₀) :
    B.pos ⟨j, h⟩ = ⟨B.o + j, by have := (B.pos ⟨j, h⟩).2; rw [B.pos_val] at this; exact this⟩ :=
  Fin.ext (B.pos_val _)

omit [DecidableEq I] in
theorem lbl_j {i : Seq μ} {s : Seq ν} (hs : s ∈ B.F i) (j : ℕ) (h : j < n₀) :
    s.1 ⟨B.o + j, by have := (B.pos ⟨j, h⟩).2; rw [B.pos_val] at this; exact this⟩ = i.1 ⟨j, h⟩ :=
  B.lbl_of_mem hs rfl

omit [DecidableEq I] in
theorem lbl_j1 {i : Seq μ} {s : Seq ν} (hs : s ∈ B.F i) (j : ℕ) (h : j + 1 < n₀) :
    s.1 ⟨B.o + j + 1, B.lt_card h⟩ = i.1 ⟨j + 1, h⟩ :=
  B.lbl_of_mem hs rfl

omit [DecidableEq I] in
theorem lbl_j2 {i : Seq μ} {s : Seq ν} (hs : s ∈ B.F i) (j : ℕ) (h : j + 2 < n₀) :
    s.1 ⟨B.o + j + 2, by have := B.lt_card (j := j + 1) h; omega⟩ = i.1 ⟨j + 2, h⟩ :=
  B.lbl_of_mem hs rfl

omit [DecidableEq I] in
theorem pos_succ (j : ℕ) (h : j + 1 < n₀) : B.pos ⟨j + 1, h⟩ = ⟨B.o + j + 1, B.lt_card h⟩ :=
  Fin.ext (by rw [B.pos_val]; rfl)

omit [DecidableEq I] in
theorem pos_succ_succ (j : ℕ) (h : j + 2 < n₀) :
    B.pos ⟨j + 2, h⟩ = ⟨B.o + j + 2, by have := B.lt_card (j := j + 1) h; omega⟩ :=
  Fin.ext (by rw [B.pos_val]; rfl)

theorem freeHom_ncEval₂ (a b : Fin n₀) (p : MvPolynomial (Fin 2) k) :
    B.freeHom Q (ncEval ![fx k μ a, fx k μ b] p) =
      polCorner Q T (rename ![B.pos a, B.pos b] p) := by
  have : B.pos ∘ ![a, b] = ![B.pos a, B.pos b] := by funext c; fin_cases c <;> rfl
  rw [vec2_fx, freeHom_ncEval, this]

theorem freeHom_ncEval₃ (a b c : Fin n₀) (p : MvPolynomial (Fin 3) k) :
    B.freeHom Q (ncEval ![fx k μ a, fx k μ b, fx k μ c] p) =
      polCorner Q T (rename ![B.pos a, B.pos b, B.pos c] p) := by
  have : B.pos ∘ ![a, b, c] = ![B.pos a, B.pos b, B.pos c] := by
    funext d; fin_cases d <;> rfl
  rw [vec3_fx, freeHom_ncEval, this]

/-! #### The relations in the corner ring -/

theorem gE_mul_gE (i i' : Seq μ) :
    B.gE Q i * B.gE Q i' = if i = i' then B.gE Q i else 0 := by
  split_ifs with hij
  · subst hij; exact Corner.ext (by simp [B.eF_mul_eF])
  · exact Corner.ext (by simp [B.eF_mul_eF, hij])

theorem sum_gE : ∑ i, B.gE Q i = 1 := Corner.ext (by simp [B.sum_eF])

theorem polCorner_mul_gE (q : MvPolynomial (Fin M) k) (i : Seq μ) :
    polCorner Q T q * B.gE Q i = B.gE Q i * polCorner Q T q := by
  refine Corner.ext ?_
  simp only [Corner.val_mul, val_polCorner, val_gE, mul_assoc]
  rw [B.E_mul_eF, ← mul_assoc (B.eF Q i), ← pol_mul_eSum, mul_assoc, B.eF_mul_E]

theorem gψ_mul_gE (j : ℕ) (i : Seq μ) :
    B.gψ Q j * B.gE Q i = B.gE Q (sadj n₀ j • i) * B.gψ Q j := by
  by_cases hj : j + 1 < n₀
  · refine Corner.ext ?_
    simp only [Corner.val_mul, val_gE, B.val_gψ hj, mul_assoc]
    rw [B.E_mul_eF, B.ψ_mul_eF hj, B.ψ_mul_E hj, ← mul_assoc, B.eF_mul_E]
  · rw [B.gψ_of_not_lt hj, zero_mul, mul_zero]

theorem gψ_mul_gψ {j l : ℕ} (h : j + 1 < l) : B.gψ Q j * B.gψ Q l = B.gψ Q l * B.gψ Q j := by
  by_cases hl : l + 1 < n₀
  · have hj : j + 1 < n₀ := by omega
    have hE := eSum_idem (k := k) (Q := Q) T
    refine Corner.ext ?_
    simp only [Corner.val_mul, B.val_gψ hj, B.val_gψ hl]
    rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E hl).symm, mul_E_mul_mul_E hE _ (B.ψ_mul_E hj).symm,
      ψ_mul_ψ _ _ (by omega)]
  · rw [B.gψ_of_not_lt hl, zero_mul, mul_zero]

theorem polCorner_mul_gψ (a : Fin n₀) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    polCorner Q T (X (B.pos a)) * B.gψ Q j = B.gψ Q j * polCorner Q T (X (B.pos a)) := by
  by_cases hj : j + 1 < n₀
  · have hE := eSum_idem (k := k) (Q := Q) T
    refine Corner.ext ?_
    simp only [Corner.val_mul, val_polCorner, B.val_gψ hj]
    rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E hj).symm,
      mul_E_mul_mul_E hE _ (pol_mul_eSum _ T).symm, B.pol_X_pos,
      x_mul_ψ _ _ (by simp only; omega) (by simp only; omega)]
  · rw [B.gψ_of_not_lt hj, zero_mul, mul_zero]

/-- Values of the generator images needed for the local relations. -/
theorem val_polCorner_gψ_gE {j : ℕ} (h : j + 1 < n₀) (a : Fin n₀) (i : Seq μ) :
    (polCorner Q T (X (B.pos a)) * B.gψ Q j * B.gE Q i).val =
      x (B.pos a) * ψ (B.o + j) * B.eF Q i := by
  have hE := eSum_idem (k := k) (Q := Q) T
  simp only [Corner.val_mul, val_polCorner, B.val_gψ h, val_gE]
  rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E h).symm, mul_assoc _ (eSum Q T), B.E_mul_eF, pol_X]

theorem val_gψ_polCorner_gE {j : ℕ} (h : j + 1 < n₀) (a : Fin n₀) (i : Seq μ) :
    (B.gψ Q j * polCorner Q T (X (B.pos a)) * B.gE Q i).val =
      ψ (B.o + j) * x (B.pos a) * B.eF Q i := by
  have hE := eSum_idem (k := k) (Q := Q) T
  simp only [Corner.val_mul, val_polCorner, B.val_gψ h, val_gE]
  rw [mul_E_mul_mul_E hE _ (pol_mul_eSum _ T).symm, mul_assoc _ (eSum Q T), B.E_mul_eF, pol_X]

theorem val_gψ_gψ_gE {j l : ℕ} (hj : j + 1 < n₀) (hl : l + 1 < n₀) (i : Seq μ) :
    (B.gψ Q j * B.gψ Q l * B.gE Q i).val = ψ (B.o + j) * ψ (B.o + l) * B.eF Q i := by
  have hE := eSum_idem (k := k) (Q := Q) T
  simp only [Corner.val_mul, B.val_gψ hj, B.val_gψ hl, val_gE]
  rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E hl).symm, mul_assoc _ (eSum Q T), B.E_mul_eF]

theorem val_gψ_gψ_gψ_gE {j l r : ℕ} (hj : j + 1 < n₀) (hl : l + 1 < n₀) (hr : r + 1 < n₀)
    (i : Seq μ) :
    (B.gψ Q j * B.gψ Q l * B.gψ Q r * B.gE Q i).val =
      ψ (B.o + j) * ψ (B.o + l) * ψ (B.o + r) * B.eF Q i := by
  have hE := eSum_idem (k := k) (Q := Q) T
  simp only [Corner.val_mul, B.val_gψ hj, B.val_gψ hl, B.val_gψ hr, val_gE]
  rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E hl).symm, mul_E_mul_mul_E hE _ (B.ψ_mul_E hr).symm,
    mul_assoc _ (eSum Q T), B.E_mul_eF]

theorem rel_dot_cross_left (j : ℕ) (h : j + 1 < n₀) (i : Seq μ) :
    (polCorner Q T (X (B.pos ⟨j, by omega⟩)) * B.gψ Q j -
        B.gψ Q j * polCorner Q T (X (B.pos ⟨j + 1, h⟩))) * B.gE Q i =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then B.gE Q i else 0 := by
  have hj' : B.o + j + 1 < M := B.lt_card h
  have key : ∀ s ∈ B.F i,
      (x ⟨B.o + j, by omega⟩ * ψ (B.o + j) - ψ (B.o + j) * x ⟨B.o + j + 1, hj'⟩ :
        KLRAlgebra k Q ν) * e s =
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 1 else 0) * e s := by
    intro s hs
    rw [dot_cross_left (B.o + j) hj' s]
    simp only [Seq.lbl, B.lbl_j hs j (by omega), B.lbl_j1 hs j h]
    split_ifs <;> simp
  refine Corner.ext ?_
  rw [sub_mul, Corner.val_sub, B.val_polCorner_gψ_gE h, B.val_gψ_polCorner_gE h,
    ← sub_mul, B.pos_mk, B.pos_succ, mul_eSum_congr key]
  split_ifs <;> simp

theorem rel_dot_cross_right (j : ℕ) (h : j + 1 < n₀) (i : Seq μ) :
    (B.gψ Q j * polCorner Q T (X (B.pos ⟨j, by omega⟩)) -
        polCorner Q T (X (B.pos ⟨j + 1, h⟩)) * B.gψ Q j) * B.gE Q i =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then B.gE Q i else 0 := by
  have hj' : B.o + j + 1 < M := B.lt_card h
  have key : ∀ s ∈ B.F i,
      (ψ (B.o + j) * x ⟨B.o + j, by omega⟩ - x ⟨B.o + j + 1, hj'⟩ * ψ (B.o + j) :
        KLRAlgebra k Q ν) * e s =
        (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 1 else 0) * e s := by
    intro s hs
    rw [dot_cross_right (B.o + j) hj' s]
    simp only [Seq.lbl, B.lbl_j hs j (by omega), B.lbl_j1 hs j h]
    split_ifs <;> simp
  refine Corner.ext ?_
  rw [sub_mul, Corner.val_sub, B.val_polCorner_gψ_gE h, B.val_gψ_polCorner_gE h,
    ← sub_mul, B.pos_mk, B.pos_succ, mul_eSum_congr key]
  split_ifs <;> simp

theorem rel_cross_sq (j : ℕ) (h : j + 1 < n₀) (i : Seq μ) :
    B.gψ Q j * B.gψ Q j * B.gE Q i =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        polCorner Q T (rename ![B.pos ⟨j, by omega⟩, B.pos ⟨j + 1, h⟩]
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩))) * B.gE Q i := by
  have hj' : B.o + j + 1 < M := B.lt_card h
  have key : ∀ s ∈ B.F i, (ψ (B.o + j) * ψ (B.o + j) : KLRAlgebra k Q ν) * e s =
      (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then 0 else
        pol (rename ![B.pos ⟨j, by omega⟩, B.pos ⟨j + 1, h⟩]
          (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)))) * e s := by
    intro s hs
    rw [ψ_sq (B.o + j) hj' s, ncEval_x2, B.pos_mk, B.pos_succ]
    simp only [Seq.lbl, B.lbl_j hs j (by omega), B.lbl_j1 hs j h]
    split_ifs <;> simp
  refine Corner.ext ?_
  rw [B.val_gψ_gψ_gE h h, mul_eSum_congr key]
  split_ifs
  · simp
  · simp only [Corner.val_mul, val_polCorner, val_gE]
    rw [mul_assoc, B.E_mul_eF]

theorem rel_braid (j : ℕ) (h : j + 2 < n₀) (i : Seq μ) :
    (B.gψ Q j * B.gψ Q (j + 1) * B.gψ Q j - B.gψ Q (j + 1) * B.gψ Q j * B.gψ Q (j + 1)) *
        B.gE Q i =
      if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        polCorner Q T (rename ![B.pos ⟨j, by omega⟩, B.pos ⟨j + 1, by omega⟩, B.pos ⟨j + 2, h⟩]
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩)))) * B.gE Q i
      else 0 := by
  have hj' : B.o + j + 2 < M := by have := B.lt_card (j := j + 1) h; omega
  have h1 : j + 1 < n₀ := by omega
  have h2 : j + 1 + 1 < n₀ := by omega
  have key : ∀ s ∈ B.F i, (ψ (B.o + j) * ψ (B.o + j + 1) * ψ (B.o + j) -
        ψ (B.o + j + 1) * ψ (B.o + j) * ψ (B.o + j + 1) : KLRAlgebra k Q ν) * e s =
      (if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 2, h⟩ ∧
          i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, by omega⟩ then
        pol (rename ![B.pos ⟨j, by omega⟩, B.pos ⟨j + 1, by omega⟩, B.pos ⟨j + 2, h⟩]
          (qbar (Q (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, by omega⟩))))
        else 0) * e s := by
    intro s hs
    rw [braid (B.o + j) hj' s, ncEval_x3, B.pos_mk, B.pos_succ, B.pos_succ_succ]
    simp only [Seq.lbl, B.lbl_j hs j (by omega), B.lbl_j1 hs j (by omega), B.lbl_j2 hs j h]
    split_ifs <;> simp
  refine Corner.ext ?_
  rw [sub_mul, Corner.val_sub, B.val_gψ_gψ_gψ_gE h1 h2 h1, B.val_gψ_gψ_gψ_gE h2 h1 h2, ← sub_mul]
  rw [show B.o + (j + 1) = B.o + j + 1 from rfl, mul_eSum_congr key]
  split_ifs
  · simp only [Corner.val_mul, val_polCorner, val_gE]
    rw [mul_assoc, B.E_mul_eF]
  · simp

theorem freeHom_rel ⦃a b : FreeAlgebra k (Gen μ)⦄ (h : Rel k Q μ a b) :
    B.freeHom Q a = B.freeHom Q b := by
  cases h with
  | idem_mul i j =>
    rw [map_mul, freeHom_fe, freeHom_fe, B.gE_mul_gE, apply_ite (B.freeHom Q), freeHom_fe,
      map_zero]
  | idem_sum =>
    rw [map_sum, map_one]
    simp only [freeHom_fe]
    exact B.sum_gE
  | dot_idem a i =>
    rw [map_mul, map_mul, freeHom_fx, freeHom_fe, B.polCorner_mul_gE]
  | cross_idem j i =>
    rw [map_mul, map_mul, freeHom_fψ, freeHom_fe, freeHom_fe, B.gψ_mul_gE]
  | cross_zero j h =>
    rw [freeHom_fψ, map_zero, B.gψ_of_not_lt (by omega)]
  | dot_dot a b =>
    rw [map_mul, map_mul, freeHom_fx, freeHom_fx, ← map_mul, ← map_mul, mul_comm]
  | cross_cross j l h =>
    rw [map_mul, map_mul, freeHom_fψ, freeHom_fψ, B.gψ_mul_gψ h]
  | dot_cross a j h₁ h₂ =>
    rw [map_mul, map_mul, freeHom_fx, freeHom_fψ, B.polCorner_mul_gψ a j h₁ h₂]
  | dot_cross_left j h i =>
    rw [apply_ite (B.freeHom Q), map_zero, freeHom_fe]
    simp only [map_mul, map_sub, freeHom_fx, freeHom_fψ, freeHom_fe]
    exact B.rel_dot_cross_left j h i
  | dot_cross_right j h i =>
    rw [apply_ite (B.freeHom Q), map_zero, freeHom_fe]
    simp only [map_mul, map_sub, freeHom_fx, freeHom_fψ, freeHom_fe]
    exact B.rel_dot_cross_right j h i
  | cross_sq j h i =>
    rw [apply_ite (B.freeHom Q), map_zero, map_mul, map_mul, map_mul, freeHom_fψ, freeHom_fe,
      B.freeHom_ncEval₂]
    exact B.rel_cross_sq j h i
  | braid j h i =>
    rw [apply_ite (B.freeHom Q), map_zero, map_mul, map_mul, freeHom_fe, B.freeHom_ncEval₃]
    simp only [map_mul, map_sub, freeHom_fψ]
    exact B.rel_braid j h i

variable (Q) in
/-- **The block embedding** `R(μ) → e_T R(ν) e_T`, a unital algebra homomorphism into the
corner ring. -/
noncomputable def hom : KLRAlgebra k Q μ →ₐ[k] (eSum_idem (Q := Q) T).Corner :=
  RingQuot.liftAlgHom k ⟨B.freeHom Q, B.freeHom_rel⟩

theorem hom_mk (a : FreeAlgebra k (Gen μ)) : B.hom Q (KLRAlgebra.mk k Q μ a) = B.freeHom Q a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem hom_e (i : Seq μ) : B.hom Q (e i) = B.gE Q i := by
  rw [e, hom_mk, freeHom_fe]

@[simp] theorem hom_x (a : Fin n₀) : B.hom Q (x a) = polCorner Q T (X (B.pos a)) := by
  rw [x, hom_mk, freeHom_fx]

@[simp] theorem hom_ψ (j : ℕ) : B.hom Q (ψ j) = B.gψ Q j := by
  rw [ψ, hom_mk, freeHom_fψ]

theorem hom_pol (p : MvPolynomial (Fin n₀) k) :
    B.hom Q (pol p) = polCorner Q T (rename B.pos p) := by
  have : (B.hom Q).comp pol = (polCorner Q T).comp (rename B.pos) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  exact congrArg (fun φ : MvPolynomial (Fin n₀) k →ₐ[k] _ => φ p) this

theorem eSum_mul_ψw {α : List ℕ} (hα : ValidWord n₀ α) :
    (eSum Q T * ψw (α.map (B.o + ·)) : KLRAlgebra k Q ν) = ψw (α.map (B.o + ·)) * eSum Q T := by
  induction α with
  | nil => simp
  | cons l α ih =>
    rw [validWord_cons] at hα
    rw [List.map_cons, ψw_cons, ← mul_assoc, ← B.ψ_mul_E hα.1, mul_assoc, ih hα.2, mul_assoc]

theorem val_hom_ψw {α : List ℕ} (hα : ValidWord n₀ α) :
    (B.hom Q (ψw α)).val = ψw (α.map (B.o + ·)) * eSum Q T := by
  induction α with
  | nil => simp
  | cons j α ih =>
    rw [validWord_cons] at hα
    rw [ψw_cons, map_mul, Corner.val_mul, ih hα.2, hom_ψ, B.val_gψ hα.1, List.map_cons,
      ψw_cons, mul_E_mul_mul_E (eSum_idem T) _ (B.eSum_mul_ψw hα.2), mul_assoc]

/-- A dot at a position `c` away from the crossing `ψ (o + j)` commutes with its image. -/
theorem polCorner_X_mul_gψ (c : Fin M) (j : ℕ)
    (hc : j + 1 < n₀ → c.val ≠ B.o + j ∧ c.val ≠ B.o + j + 1) :
    polCorner Q T (X c) * B.gψ Q j = B.gψ Q j * polCorner Q T (X c) := by
  by_cases hj : j + 1 < n₀
  · obtain ⟨h₁, h₂⟩ := hc hj
    have hE := eSum_idem (k := k) (Q := Q) T
    refine Corner.ext ?_
    simp only [Corner.val_mul, val_polCorner, B.val_gψ hj]
    rw [mul_E_mul_mul_E hE _ (B.ψ_mul_E hj).symm,
      mul_E_mul_mul_E hE _ (pol_mul_eSum _ T).symm, pol_X, x_mul_ψ _ _ h₁ h₂]
  · rw [B.gψ_of_not_lt hj, zero_mul, mul_zero]

/-- The image of `e i` commutes with the image of a crossing preserving the fibre `F i`. -/
theorem gE_mul_gψ {μ' : Multiset I} (B' : BlockEmb μ' ν T) (i : Seq μ) (j : ℕ)
    (hstab : j + 1 < Multiset.card μ' → ∀ s, s ∈ B.F i ↔ sadj M (B'.o + j) • s ∈ B.F i) :
    B.gE Q i * B'.gψ Q j = B'.gψ Q j * B.gE Q i := by
  by_cases hj : j + 1 < Multiset.card μ'
  · have hstab := hstab hj
    refine Corner.ext ?_
    simp only [Corner.val_mul, val_gE, B'.val_gψ hj]
    rw [mul_assoc (ψ _) (eSum Q T), B.E_mul_eF, ψ_mul_eSum_of_stable _ _ hstab, ← mul_assoc,
      ← ψ_mul_eSum_of_stable _ _ hstab, mul_assoc, B.eF_mul_E]
  · rw [B'.gψ_of_not_lt hj, zero_mul, mul_zero]

/-- Images of distant crossings of two blocks commute. -/
theorem gψ_mul_gψ' {μ' : Multiset I} (B' : BlockEmb μ' ν T) (j l : ℕ)
    (h : j + 1 < n₀ → l + 1 < Multiset.card μ' → B.o + j + 1 < B'.o + l) :
    B.gψ Q j * B'.gψ Q l = B'.gψ Q l * B.gψ Q j := by
  by_cases hj : j + 1 < n₀
  · by_cases hl : l + 1 < Multiset.card μ'
    · have hE := eSum_idem (k := k) (Q := Q) T
      refine Corner.ext ?_
      simp only [Corner.val_mul, B.val_gψ hj, B'.val_gψ hl]
      rw [mul_E_mul_mul_E hE _ (B'.ψ_mul_E hl).symm, mul_E_mul_mul_E hE _ (B.ψ_mul_E hj).symm,
        ψ_mul_ψ _ _ (h hj hl)]
    · rw [B'.gψ_of_not_lt hl, zero_mul, mul_zero]
  · rw [B.gψ_of_not_lt hj, zero_mul, mul_zero]

end BlockEmb

/-! ### Commuting images of generators -/

theorem commute_of_gen {C : Type*} [Ring C] [Algebra k C] {μ₁ μ₂ : Multiset I}
    (f : KLRAlgebra k Q μ₁ →ₐ[k] C) (g : KLRAlgebra k Q μ₂ →ₐ[k] C)
    (h : ∀ a b, Commute (f (KLRAlgebra.mk k Q μ₁ (FreeAlgebra.ι k a)))
      (g (KLRAlgebra.mk k Q μ₂ (FreeAlgebra.ι k b)))) (x y) : Commute (f x) (g y) := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  obtain ⟨y, rfl⟩ := mk_surjective y
  induction x using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes, AlgHom.commutes]; exact Algebra.commute_algebraMap_left _ _
  | grade1 a =>
    induction y using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes, AlgHom.commutes]; exact Algebra.commute_algebraMap_right _ _
    | grade1 b => exact h a b
    | mul y y' hy hy' => rw [map_mul, map_mul]; exact hy.mul_right hy'
    | add y y' hy hy' => rw [map_add, map_add]; exact hy.add_right hy'
  | mul x x' hx hx' => rw [map_mul, map_mul]; exact hx.mul_left hx'
  | add x x' hx hx' => rw [map_add, map_add]; exact hx.add_left hx'

/-! ### The two blocks of `ν + ν'` -/

section Concat

variable {ν ν' : Multiset I}

variable (ν ν') in
/-- The set of concatenations `ij`, `i ∈ Seq ν`, `j ∈ Seq ν'`. -/
noncomputable def concatSet : Finset (Seq (ν + ν')) :=
  Finset.univ.image fun p : Seq ν × Seq ν' => p.1.append p.2

theorem mem_concatSet {s : Seq (ν + ν')} :
    s ∈ concatSet ν ν' ↔ ∃ (i : Seq ν) (j : Seq ν'), i.append j = s := by
  simp [concatSet]

theorem append_mem_concatSet (i : Seq ν) (j : Seq ν') : i.append j ∈ concatSet ν ν' :=
  mem_concatSet.2 ⟨i, j, rfl⟩

variable (ν ν') in
/-- The first block of `ν + ν'`: positions `0, …, card ν - 1`. -/
noncomputable def blockL : BlockEmb ν (ν + ν') (concatSet ν ν') where
  o := 0
  pos := Seq.posL ν'
  pos_val a := by simp
  F i := Finset.univ.image fun j : Seq ν' => i.append j
  disj i i' h := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs hs'
    obtain ⟨j, rfl⟩ := hs
    obtain ⟨j', hj'⟩ := hs'
    exact h (Seq.append_inj.1 hj').1.symm
  mem_T s := by simp [mem_concatSet]
  lbl i s hs a := by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
    exact Seq.append_posL _ _ _
  sadj_mem j hj i s := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, zero_add]
    constructor
    · rintro ⟨j', rfl⟩
      exact ⟨j', by rw [Seq.sadj_smul_append_left hj, sadj_smul_smul]⟩
    · rintro ⟨j', hj'⟩
      refine ⟨j', ?_⟩
      rw [← sadj_smul_smul j s, ← hj', Seq.sadj_smul_append_left hj]

variable (ν ν') in
/-- The second block of `ν + ν'`: positions `card ν, …, card (ν + ν') - 1`. -/
noncomputable def blockR : BlockEmb ν' (ν + ν') (concatSet ν ν') where
  o := Multiset.card ν
  pos := Seq.posR ν
  pos_val b := rfl
  F j := Finset.univ.image fun i : Seq ν => i.append j
  disj j j' h := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs hs'
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨i', hi'⟩ := hs'
    exact h (Seq.append_inj.1 hi').2.symm
  mem_T s := by
    simp only [mem_concatSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_comm
  lbl j s hs b := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact Seq.append_posR _ _ _
  sadj_mem l hl j s := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [Seq.sadj_smul_append_right hl, sadj_smul_smul]⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [← sadj_smul_smul (Multiset.card ν + l) s, ← hi, Seq.sadj_smul_append_right hl]

@[simp] theorem blockL_o : (blockL ν ν').o = 0 := rfl
@[simp] theorem blockR_o : (blockR ν ν').o = Multiset.card ν := rfl
@[simp] theorem blockL_pos : (blockL ν ν').pos = Seq.posL ν' := rfl
@[simp] theorem blockR_pos : (blockR ν ν').pos = Seq.posR ν := rfl

theorem blockL_F_stable (i : Seq ν) {l : ℕ} (hl : l + 1 < Multiset.card ν') (s : Seq (ν + ν')) :
    s ∈ (blockL ν ν').F i ↔
      sadj (Multiset.card (ν + ν')) ((blockR ν ν').o + l) • s ∈ (blockL ν ν').F i := by
  simp only [blockL, blockR, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨sadj (Multiset.card ν') l • j, (Seq.sadj_smul_append_right hl i j).symm⟩
  · rintro ⟨j, hj⟩
    refine ⟨sadj (Multiset.card ν') l • j, ?_⟩
    rw [← Seq.sadj_smul_append_right hl, hj, sadj_smul_smul]

theorem blockR_F_stable (j : Seq ν') {l : ℕ} (hl : l + 1 < Multiset.card ν) (s : Seq (ν + ν')) :
    s ∈ (blockR ν ν').F j ↔
      sadj (Multiset.card (ν + ν')) ((blockL ν ν').o + l) • s ∈ (blockR ν ν').F j := by
  simp only [blockL, blockR, Finset.mem_image, Finset.mem_univ, true_and, zero_add]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨sadj (Multiset.card ν) l • i, (Seq.sadj_smul_append_left hl i j).symm⟩
  · rintro ⟨i, hi⟩
    refine ⟨sadj (Multiset.card ν) l • i, ?_⟩
    rw [← Seq.sadj_smul_append_left hl, hi, sadj_smul_smul]

theorem blockL_F_inter_blockR_F (i : Seq ν) (j : Seq ν') :
    (blockL ν ν').F i ∩ (blockR ν ν').F j = {i.append j} := by
  ext s
  simp only [blockL, blockR, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨j', rfl⟩, ⟨i', hi'⟩⟩
    obtain ⟨rfl, rfl⟩ := Seq.append_inj.1 hi'
    rfl
  · rintro rfl
    exact ⟨⟨j, rfl⟩, ⟨i, rfl⟩⟩

variable (Q ν ν') in
/-- The idempotent `1_{ν,ν'} = ∑_{i,j} 1_{ij}` of `R(ν + ν')`. -/
noncomputable def oneConcat : KLRAlgebra k Q (ν + ν') := eSum Q (concatSet ν ν')

theorem oneConcat_eq :
    (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = ∑ p : Seq ν × Seq ν', e (p.1.append p.2) := by
  rw [oneConcat, eSum, concatSet, Finset.sum_image]
  rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
  obtain ⟨rfl, rfl⟩ := Seq.append_inj.1 h
  rfl

theorem oneConcat_idem : IsIdempotentElem (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) :=
  eSum_idem _

variable (Q ν ν') in
/-- The corner ring `1_{ν,ν'} R(ν + ν') 1_{ν,ν'}`. -/
abbrev ConcatCorner : Type _ := (eSum_idem (Q := Q) (concatSet ν ν')).Corner

noncomputable instance : Ring (ConcatCorner Q ν ν') := inferInstance
noncomputable instance : Algebra k (ConcatCorner Q ν ν') := cornerAlgebra _
noncomputable instance : Module k (ConcatCorner Q ν ν') := Algebra.toModule

theorem commute_hom_blockL_blockR (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    Commute ((blockL ν ν').hom Q a) ((blockR ν ν').hom Q b) := by
  refine commute_of_gen _ _ (fun g g' => ?_) a b
  have hmk : ∀ {μ : Multiset I} (g : Gen μ), KLRAlgebra.mk k Q μ (FreeAlgebra.ι k g) =
      match g with
      | .idem i => e i
      | .dot a => x a
      | .cross j => ψ j := by
    intro μ g; cases g <;> rfl
  rw [hmk, hmk]
  rcases g with i | a | l <;> rcases g' with j | b | l'
  · -- `e i`, `e j`
    simp only [BlockEmb.hom_e]
    refine Corner.ext ?_
    simp only [Corner.val_mul, BlockEmb.val_gE, eSum_mul_eSum, Finset.inter_comm]
  · simp only [BlockEmb.hom_e, BlockEmb.hom_x]
    exact ((blockL ν ν').polCorner_mul_gE _ i).symm
  · simp only [BlockEmb.hom_e, BlockEmb.hom_ψ]
    exact (blockL ν ν').gE_mul_gψ (blockR ν ν') i l' fun hl s => blockL_F_stable i hl s
  · simp only [BlockEmb.hom_e, BlockEmb.hom_x]
    exact (blockR ν ν').polCorner_mul_gE _ j
  · simp only [BlockEmb.hom_x]
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  · simp only [BlockEmb.hom_x, BlockEmb.hom_ψ]
    refine (blockR ν ν').polCorner_X_mul_gψ _ l' fun _ => ?_
    simp only [blockL_pos, Seq.posL_val, blockR_o]
    have := a.2
    omega
  · simp only [BlockEmb.hom_e, BlockEmb.hom_ψ]
    exact ((blockR ν ν').gE_mul_gψ (blockL ν ν') j l fun hl s => blockR_F_stable j hl s).symm
  · simp only [BlockEmb.hom_x, BlockEmb.hom_ψ]
    refine ((blockL ν ν').polCorner_X_mul_gψ _ l fun hl => ?_).symm
    simp only [blockR_pos, Seq.posR_val, blockL_o]
    omega
  · simp only [BlockEmb.hom_ψ]
    refine (blockL ν ν').gψ_mul_gψ' (blockR ν ν') l l' fun hl _ => ?_
    simp only [blockL_o, blockR_o]
    omega

variable (Q ν ν') in
/-- The unital algebra map `R(ν) ⊗ R(ν') → 1_{ν,ν'} R(ν + ν') 1_{ν,ν'}`, "putting diagrams
side by side". -/
noncomputable def concatHom :
    KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' →ₐ[k] ConcatCorner Q ν ν' :=
  Algebra.TensorProduct.lift ((blockL ν ν').hom Q) ((blockR ν ν').hom Q)
    commute_hom_blockL_blockR

theorem concatHom_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    concatHom Q ν ν' (a ⊗ₜ b) = (blockL ν ν').hom Q a * (blockR ν ν').hom Q b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

variable (Q ν ν') in
/-- **The inclusion `ι_{ν,ν'} : R(ν) ⊗ R(ν') → R(ν + ν')`** of KL I §2.6 (non-unital:
see `concat_one`, `concat_mul`). -/
noncomputable def concat :
    KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q (ν + ν') where
  toFun t := (concatHom Q ν ν' t).val
  map_add' s t := by rw [map_add, Corner.val_add]
  map_smul' c t := by
    rw [AlgHom.map_smul_of_tower, Corner.val_smul, RingHom.id_apply]

theorem concat_apply (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    concat Q ν ν' t = (concatHom Q ν ν' t).val := rfl

theorem concat_mul (s t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    concat Q ν ν' (s * t) = concat Q ν ν' s * concat Q ν ν' t := by
  simp only [concat_apply, map_mul, Corner.val_mul]

/-- `ι` takes the unit to the idempotent `1_{ν,ν'}`. -/
theorem concat_one : concat Q ν ν' 1 = oneConcat Q ν ν' := by
  rw [concat_apply, map_one, Corner.val_one]; rfl

theorem concat_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    concat Q ν ν' (a ⊗ₜ b) = ((blockL ν ν').hom Q a).val * ((blockR ν ν').hom Q b).val := by
  rw [concat_apply, concatHom_tmul, Corner.val_mul]

theorem oneConcat_mul_concat (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    oneConcat Q ν ν' * concat Q ν ν' t = concat Q ν ν' t :=
  Corner.E_mul_val _

theorem concat_mul_oneConcat (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    concat Q ν ν' t * oneConcat Q ν ν' = concat Q ν ν' t :=
  Corner.val_mul_E _

/-- `ι (1_i ⊗ 1_j) = 1_{ij}`. -/
theorem concat_e_tmul_e (i : Seq ν) (j : Seq ν') :
    concat Q ν ν' (e i ⊗ₜ e j) = e (i.append j) := by
  rw [concat_tmul, BlockEmb.hom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.val_gE,
    eSum_mul_eSum, blockL_F_inter_blockR_F, eSum, Finset.sum_singleton]

theorem concat_x_tmul_one (a : Fin (Multiset.card ν)) :
    concat Q ν ν' (x a ⊗ₜ 1) = x (Seq.posL ν' a) * oneConcat Q ν ν' := by
  rw [concat_tmul, BlockEmb.hom_x, map_one, Corner.val_one, val_polCorner, mul_assoc,
    (eSum_idem _).eq, blockL_pos, pol_X]; rfl

theorem concat_one_tmul_x (b : Fin (Multiset.card ν')) :
    concat Q ν ν' (1 ⊗ₜ x b) = x (Seq.posR ν b) * oneConcat Q ν ν' := by
  rw [concat_tmul, map_one, Corner.val_one, Corner.E_mul_val, BlockEmb.hom_x, val_polCorner,
    blockR_pos, pol_X]; rfl

theorem concat_ψ_tmul_one {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    concat Q ν ν' (ψ j ⊗ₜ 1) = ψ j * oneConcat Q ν ν' := by
  rw [concat_tmul, BlockEmb.hom_ψ, map_one, Corner.val_one, BlockEmb.val_gψ _ hj, mul_assoc,
    (eSum_idem _).eq, blockL_o, zero_add]; rfl

theorem concat_one_tmul_ψ {j : ℕ} (hj : j + 1 < Multiset.card ν') :
    concat Q ν ν' (1 ⊗ₜ ψ j) = ψ (Multiset.card ν + j) * oneConcat Q ν ν' := by
  rw [concat_tmul, map_one, Corner.val_one, Corner.E_mul_val, BlockEmb.hom_ψ,
    BlockEmb.val_gψ _ hj, blockR_o]; rfl

theorem oneConcat_mul_ψw {α α' : List ℕ} (hα : ValidWord (Multiset.card ν) α)
    (hα' : ValidWord (Multiset.card ν') α') :
    (oneConcat Q ν ν' * ψw (α ++ shiftWord (Multiset.card ν) α') : KLRAlgebra k Q (ν + ν')) =
      ψw (α ++ shiftWord (Multiset.card ν) α') * oneConcat Q ν ν' := by
  have h1 : (eSum Q (concatSet ν ν') * ψw α : KLRAlgebra k Q (ν + ν')) =
      ψw α * eSum Q (concatSet ν ν') := by
    simpa using (blockL ν ν').eSum_mul_ψw (Q := Q) hα
  have h2 : (eSum Q (concatSet ν ν') * ψw (shiftWord (Multiset.card ν) α') :
      KLRAlgebra k Q (ν + ν')) = ψw (shiftWord (Multiset.card ν) α') * eSum Q (concatSet ν ν') :=
    (blockR ν ν').eSum_mul_ψw (Q := Q) hα'
  rw [ψw_append, oneConcat, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem concat_pol_tmul_pol (p : MvPolynomial (Fin (Multiset.card ν)) k)
    (p' : MvPolynomial (Fin (Multiset.card ν')) k) :
    concat Q ν ν' (pol p ⊗ₜ pol p') =
      pol (rename (Seq.posL ν') p * rename (Seq.posR ν) p') * oneConcat Q ν ν' := by
  rw [concat_apply, concatHom_tmul, BlockEmb.hom_pol, BlockEmb.hom_pol, ← map_mul,
    val_polCorner, blockL_pos, blockR_pos]; rfl

theorem concat_ψw_tmul_ψw {α α' : List ℕ} (hα : ValidWord (Multiset.card ν) α)
    (hα' : ValidWord (Multiset.card ν') α') :
    concat Q ν ν' (ψw α ⊗ₜ ψw α') =
      ψw (α ++ shiftWord (Multiset.card ν) α') * oneConcat Q ν ν' := by
  rw [concat_tmul, BlockEmb.val_hom_ψw _ hα, BlockEmb.val_hom_ψw _ hα',
    mul_E_mul_mul_E (eSum_idem _) _ ((blockR ν ν').eSum_mul_ψw hα'), ← ψw_append]
  simp only [blockL_o, zero_add, List.map_id', blockR_o]
  rfl

/-- **Diagrams side by side**: `ι (x^p ψ_α 1_i ⊗ x^{p'} ψ_{α'} 1_j) = x^{p p'} ψ_{α α'} 1_{ij}`,
where `α'` is shifted to the second block. -/
theorem concat_pol_ψw_e (p : MvPolynomial (Fin (Multiset.card ν)) k)
    (p' : MvPolynomial (Fin (Multiset.card ν')) k) {α α' : List ℕ}
    (hα : ValidWord (Multiset.card ν) α) (hα' : ValidWord (Multiset.card ν') α')
    (i : Seq ν) (j : Seq ν') :
    concat Q ν ν' ((pol p * ψw α * e i) ⊗ₜ (pol p' * ψw α' * e j)) =
      pol (rename (Seq.posL ν') p * rename (Seq.posR ν) p') *
        ψw (α ++ shiftWord (Multiset.card ν) α') * e (i.append j) := by
  rw [← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul,
    concat_mul, concat_e_tmul_e, concat_pol_tmul_pol, concat_ψw_tmul_ψw hα hα', oneConcat,
    mul_E_mul_mul_E (eSum_idem _) _ (oneConcat_mul_ψw hα hα'), mul_assoc _ (eSum Q _),
    eSum_mul_e, if_pos (append_mem_concatSet i j)]

end Concat

end KLRAlgebra

end Categorification.KLR
