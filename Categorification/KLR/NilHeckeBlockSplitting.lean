/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerIdempotents
import Categorification.Algebra.NilHeckeSplitting
import Categorification.Algebra.Graded.IdempotentSplitting

/-!
# Splitting divided-power idempotents of KLR algebras

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2 Example 3 and §2.5.

We transport the splitting of `e_n ⊗ 1` in the nilHecke ring `NH_{n+1}`
(`Categorification.Algebra.NilHeckeSplitting`) to a block of `n + 1` strands with constant
labels in `R(ν)`, via the map `NH_{n+1} → 1_i R(ν) 1_i` of the block
(`KLR.NilHecke.lift`, `isNilHeckeFamily_block`). For a block `[p, p + n + 1)` of the sequence
`i` we obtain elements `A_j`, `B_j` (`blockA`, `blockB`, `j ≤ n`) with

* `B_{j'} A_j = δ_{j' j} e_{i_p, n+1}` (`blockB_mul_blockA`), and
* `∑_j A_j B_j = e_{i_p, n} ⊗ 1` (`sum_blockA_mul_blockB`),

where `e_{i_p, n}` is the block idempotent on the first `n` strands of the block. For any
grading datum `G` with `deg x = degX c` on the block, `A_j` has degree `degX c · (j - n)` and
`B_j` degree `degX c · (n - j)` (`blockA_mem_grade`, `blockB_mem_grade`).

In the presence of further divided-power blocks `bs` (disjoint from the block) this gives a
splitting (`Graded.IsSplitting`) of `1_{…i^{(n)} i…} = divIdem i ((p, n) :: bs)` through
`1_{…i^{(n+1)}…} = divIdem i ((p, n + 1) :: bs)` (`isSplitting_divIdem_succ`).
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial Equiv TypeA Categorification.NilHecke

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-! ### Transport from the nilHecke ring to a block -/

section transport

variable {i : Seq ν} {p n : ℕ}

/-- The embedding `a ↦ p + a` of the block `[p, p + n + 1)` into the strands. -/
def blockEmb (hpn : p + (n + 1) ≤ m) (a : Fin (n + 1)) : Fin m := ⟨p + a, by omega⟩

/-- A polynomial with integer coefficients in the variables of the block, placed on the
block `[p, p + n + 1)` of `k[x_0, …, x_{m-1}]`. -/
noncomputable def blockPoly (hpn : p + (n + 1) ≤ m) (P : MvPolynomial (Fin (n + 1)) ℤ) :
    MvPolynomial (Fin m) k :=
  map (Int.castRingHom k) (rename (blockEmb hpn) P)

omit [DecidableEq I] in
theorem blockPoly_X (hpn : p + (n + 1) ≤ m) (a : Fin (n + 1)) :
    (blockPoly hpn (X a) : MvPolynomial (Fin m) k) = X (blockEmb hpn a) := by
  simp [blockPoly]

variable (hpn : p + (n + 1) ≤ Multiset.card ν) (hc : IsConstOn i p (n + 1))

/-- `blockPoly` as a ring homomorphism. -/
noncomputable def blockPolyRingHom (hpn : p + (n + 1) ≤ m) :
    MvPolynomial (Fin (n + 1)) ℤ →+* MvPolynomial (Fin m) k :=
  (map (Int.castRingHom k)).comp (rename (blockEmb hpn)).toRingHom

omit [DecidableEq I] in
theorem blockPolyRingHom_apply (P : MvPolynomial (Fin (n + 1)) ℤ) :
    blockPolyRingHom (k := k) hpn P = blockPoly hpn P := rfl

variable (k Q i) in
/-- The polynomials of the block, as a ring homomorphism to the centralizer of `1_i`. -/
noncomputable def blockPolyHom (hpn : p + (n + 1) ≤ m) :
    MvPolynomial (Fin (n + 1)) ℤ →+* Subring.centralizer ({(e i : A)} : Set A) :=
  RingHom.codRestrict ((pol (k := k) (Q := Q) (ν := ν)).toRingHom.comp (blockPolyRingHom hpn))
    _ fun P => by
      rw [RingHom.comp_apply, blockPolyRingHom_apply]
      exact (mem_centralizer_iff' i).2 (e_commute_pol i (blockPoly hpn P)).eq

theorem blockPolyHom_val (P : MvPolynomial (Fin (n + 1)) ℤ) :
    (blockPolyHom k Q i hpn P : A) = pol (blockPoly hpn P) := rfl

variable (k Q) in
/-- The map `NH_{n+1} → 1_i R(ν) 1_i → R(ν)` of the block `[p, p + n + 1)`. -/
noncomputable def blockVal (hpn : p + (n + 1) ≤ m) (hc : IsConstOn i p (n + 1))
    (z : nilHecke ℤ (n + 1)) : A :=
  idemCornerVal (e_mul_self i)
    (KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc) z)

theorem blockVal_mul (z w : nilHecke ℤ (n + 1)) :
    blockVal k Q hpn hc (z * w) = blockVal k Q hpn hc z * blockVal k Q hpn hc w := by
  exact congrArg (idemCornerVal (e_mul_self i))
    ((KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc)).toRingHom.map_mul' z w)

theorem blockVal_add (z w : nilHecke ℤ (n + 1)) :
    blockVal k Q hpn hc (z + w) = blockVal k Q hpn hc z + blockVal k Q hpn hc w := by
  exact congrArg (idemCornerVal (e_mul_self i))
    ((KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc)).toRingHom.map_add' z w)

theorem blockVal_zero : blockVal k Q hpn hc (0 : nilHecke ℤ (n + 1)) = 0 := by
  exact congrArg (idemCornerVal (e_mul_self i))
    ((KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc)).toRingHom.map_zero')

theorem blockVal_one : blockVal k Q hpn hc (1 : nilHecke ℤ (n + 1)) = e i := by
  exact congrArg (idemCornerVal (e_mul_self i))
    ((KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc)).toRingHom.map_one')

theorem blockVal_sum {ι : Type*} (s : Finset ι) (z : ι → nilHecke ℤ (n + 1)) :
    blockVal k Q hpn hc (∑ j ∈ s, z j) = ∑ j ∈ s, blockVal k Q hpn hc (z j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [blockVal_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, blockVal_add, ih]

/-- The image of a polynomial. -/
theorem blockVal_mulPoly (P : MvPolynomial (Fin (n + 1)) ℤ) :
    blockVal k Q hpn hc ⟨mulPoly ℤ (n + 1) P, mulPoly_mem P⟩ = pol (blockPoly hpn P) * e i := by
  set L := KLR.NilHecke.lift (k := ℤ) (isNilHeckeFamily_block (k := k) (Q := Q) hpn hc)
  let φ₁ : MvPolynomial (Fin (n + 1)) ℤ →+* IsIdempotentElem.Corner (e_mul_self (Q := Q) i) :=
    L.toRingHom.comp ((mulPoly ℤ (n + 1)).codRestrict (nilHecke ℤ (n + 1)) mulPoly_mem).toRingHom
  let φ₂ : MvPolynomial (Fin (n + 1)) ℤ →+* IsIdempotentElem.Corner (e_mul_self (Q := Q) i) :=
    (toCorner (e_mul_self i)).comp (blockPolyHom k Q i hpn)
  have h : φ₁ = φ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun a => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (φ₁.comp C) (φ₂.comp C)) r
    · simp only [φ₁, φ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      have : ((mulPoly ℤ (n + 1)).codRestrict (nilHecke ℤ (n + 1)) mulPoly_mem) (X a) =
          ⟨mulX ℤ (n + 1) a, mulX_mem a⟩ := rfl
      rw [this, KLR.NilHecke.lift_mulX]
      congr 1
      apply Subtype.ext
      simp only [blockPolyHom, cx_val, RingHom.codRestrict_apply, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, blockPolyRingHom_apply, blockPoly_X, pol_X]
      rfl
  have := congrArg (fun φ => idemCornerVal (e_mul_self i) (φ P)) h
  exact this

/-- The image of `∂_ρ` for a word in the letters of the block. -/
theorem blockVal_ddw (ρ : List ℕ) (hρ : ∀ j ∈ ρ, j + 1 < n + 1) :
    blockVal k Q hpn hc ⟨ddw ρ, ddw_mem ρ⟩ = ψw (ρ.map (p + ·)) * e i := by
  induction ρ with
  | nil =>
    have : (⟨ddw [], ddw_mem []⟩ : nilHecke ℤ (n + 1)) = 1 := rfl
    rw [this, blockVal_one]; simp
  | cons j ρ ih =>
    have : (⟨ddw (j :: ρ), ddw_mem _⟩ : nilHecke ℤ (n + 1)) =
        ⟨dd ℤ (n + 1) j, dd_mem j⟩ * ⟨ddw ρ, ddw_mem ρ⟩ := Subtype.ext (ddw_cons j ρ)
    rw [this, blockVal_mul, ih fun l hl => hρ l (List.mem_cons_of_mem _ hl)]
    have hj := hρ j List.mem_cons_self
    have h1 : blockVal k Q hpn hc ⟨dd ℤ (n + 1) j, dd_mem j⟩ = ψ (p + j) * e i := by
      rw [blockVal, KLR.NilHecke.lift_dd, idemCornerVal_toCorner, cψ_val_of_lt hpn hc hj]
    rw [h1, List.map_cons, ψw_cons, mul_assoc, ← mul_assoc (e i),
      ← ψw_mul_e_of_forall (fun l hl hlm => ?_), mul_assoc, e_mul_self, mul_assoc]
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    have := hρ l' (List.mem_cons_of_mem _ hl')
    exact hc.lbl_succ (by omega) (by omega) hlm

end transport

/-! ### The elements `A_j`, `B_j` of a block -/

section blockAB

variable (k Q) in
/-- `A_j = x^{δ'} y^j ψ_{w_0} 1_i` on the block `[p, p + n + 1)` (`y = x_{p+n}`): the image of
`a_j = x^{δ'} y^j ∂_{w_0} ∈ NH_{n+1}`. -/
noncomputable def blockA (i : Seq ν) {p n : ℕ} (hpn : p + (n + 1) ≤ m) (j : ℕ) : A :=
  pol (blockPoly hpn (xDelta n * X (Fin.last n) ^ j)) * ψw (blockWord p (n + 1)) * e i

variable (k Q) in
/-- `B_j = x^δ ψ_{w_0} Q_j x^{δ'} ψ_{w_0'} 1_i` on the block `[p, p + n + 1)`: the image of
`b_j ∈ NH_{n+1}`. -/
noncomputable def blockB (i : Seq ν) {p n : ℕ} (hpn : p + (n + 1) ≤ m) (j : ℕ) : A :=
  pol (blockPoly hpn (xDelta (n + 1))) * ψw (blockWord p (n + 1)) *
    pol (blockPoly hpn (nhDual ℤ n j * xDelta n)) * ψw (blockWord p n) * e i

variable {i : Seq ν} {p n : ℕ} (hpn : p + (n + 1) ≤ Multiset.card ν) (hc : IsConstOn i p (n + 1))

omit [DecidableEq I] in
theorem IsConstOn.mono {t : Seq ν} {q l l' : ℕ} (h : IsConstOn t q l) (hl : l' ≤ l) :
    IsConstOn t q l' :=
  fun a b h1 h2 h3 h4 => h a b h1 (by omega) h3 (by omega)

omit [DecidableEq I] in
theorem blockPoly_xDelta {l : ℕ} (hl : l ≤ n + 1) :
    (blockPoly hpn (xDelta l) : MvPolynomial (Fin m) k) = blockDelta p l := by
  set f : ℕ → MvPolynomial (Fin m) k := fun a =>
    if h : p + a < m then X ⟨p + a, h⟩ ^ (l - 1 - a) else 1
  have h1 : (blockPoly hpn (xDelta l) : MvPolynomial (Fin m) k) = ∏ a ∈ Finset.range (n + 1), f a := by
    rw [blockPoly, xDelta, map_prod, map_prod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [f, map_pow, rename_X, map_X, dif_pos (show p + (a : ℕ) < m by omega)]
    rfl
  have h2 : (blockDelta p l : MvPolynomial (Fin m) k) = ∏ a ∈ Finset.range l, f a := by
    rw [blockDelta, ← Fin.prod_univ_eq_prod_range]
  rw [h1, h2, ← Finset.prod_range_mul_prod_Ico _ hl, Finset.prod_eq_one (s := Finset.Ico _ _)
    (fun a ha => by
      rw [Finset.mem_Ico] at ha
      simp only [f, dif_pos (show p + a < m by omega), show l - 1 - a = 0 by omega, pow_zero]),
    mul_one]

private theorem mul_e_mul_mul_e {y z : A} {t : Seq ν} (hz : e t * z = z * e t) :
    y * e t * (z * e t) = y * z * e t := by
  rw [mul_assoc y, ← mul_assoc (e t), hz, mul_assoc, e_mul_self, ← mul_assoc]

theorem blockVal_nhA (j : ℕ) :
    blockVal k Q hpn hc ⟨nhA ℤ n j, nhA_mem j⟩ = blockA k Q i hpn j := by
  have : (⟨nhA ℤ n j, nhA_mem j⟩ : nilHecke ℤ (n + 1)) =
      ⟨mulPoly ℤ (n + 1) _, mulPoly_mem _⟩ * ⟨ddw (w0Word (n + 1)), ddw_mem _⟩ := rfl
  rw [this, blockVal_mul, blockVal_mulPoly, blockVal_ddw hpn hc _
    (fun j hj => lt_of_mem_w0Word hj), ← blockWord, blockA,
    mul_e_mul_mul_e (blockψ_mul_e hc).symm]

theorem blockVal_nhB (j : ℕ) :
    blockVal k Q hpn hc ⟨nhB ℤ n j, nhB_mem j⟩ = blockB k Q i hpn j := by
  have : (⟨nhB ℤ n j, nhB_mem j⟩ : nilHecke ℤ (n + 1)) =
      ⟨mulPoly ℤ (n + 1) _, mulPoly_mem _⟩ * ⟨ddw (w0Word (n + 1)), ddw_mem _⟩ *
        ⟨mulPoly ℤ (n + 1) _, mulPoly_mem _⟩ * ⟨ddw (w0Word n), ddw_mem _⟩ := rfl
  rw [this, blockVal_mul, blockVal_mul, blockVal_mul, blockVal_mulPoly, blockVal_mulPoly,
    blockVal_ddw hpn hc _ (fun j hj => lt_of_mem_w0Word hj),
    blockVal_ddw hpn hc _ (fun j hj => by have := lt_of_mem_w0Word hj; omega), ← blockWord,
    ← blockWord, blockB, mul_e_mul_mul_e (blockψ_mul_e hc).symm,
    mul_e_mul_mul_e (e_commute_pol i _).eq,
    mul_e_mul_mul_e (blockψ_mul_e (hc.mono (Nat.le_succ n))).symm]

theorem blockVal_idemNH :
    blockVal k Q hpn hc ⟨idemNH ℤ (n + 1), idemNH_mem⟩ = blockIdem i p (n + 1) := by
  have : (⟨idemNH ℤ (n + 1), idemNH_mem⟩ : nilHecke ℤ (n + 1)) =
      ⟨mulPoly ℤ (n + 1) _, mulPoly_mem _⟩ * ⟨ddw (w0Word (n + 1)), ddw_mem _⟩ := rfl
  rw [this, blockVal_mul, blockVal_mulPoly, blockVal_ddw hpn hc _
    (fun j hj => lt_of_mem_w0Word hj), ← blockWord, mul_e_mul_mul_e (blockψ_mul_e hc).symm,
    blockPoly_xDelta hpn le_rfl, blockIdem, blockElt]

theorem blockVal_nhE' :
    blockVal k Q hpn hc ⟨nhE' ℤ n, nhE'_mem⟩ = blockIdem i p n := by
  have : (⟨nhE' ℤ n, nhE'_mem⟩ : nilHecke ℤ (n + 1)) =
      ⟨mulPoly ℤ (n + 1) _, mulPoly_mem _⟩ * ⟨ddw (w0Word n), ddw_mem _⟩ := rfl
  rw [this, blockVal_mul, blockVal_mulPoly, blockVal_ddw hpn hc _
    (fun j hj => by have := lt_of_mem_w0Word hj; omega), ← blockWord,
    mul_e_mul_mul_e (blockψ_mul_e (hc.mono (Nat.le_succ n))).symm,
    blockPoly_xDelta hpn (Nat.le_succ n), blockIdem, blockElt]

include hc in
/-- **The splitting on a block, part 1**: `B_{j'} A_j = δ_{j' j} e_{i_p, n+1}`. -/
theorem blockB_mul_blockA {j' j : ℕ} (hj' : j' ≤ n) (hj : j ≤ n) :
    blockB k Q i hpn j' * blockA k Q i hpn j =
      if j' = j then blockIdem i p (n + 1) else 0 := by
  have h := congrArg (blockVal k Q hpn hc)
    (show (⟨nhB ℤ n j', nhB_mem j'⟩ : nilHecke ℤ (n + 1)) * ⟨nhA ℤ n j, nhA_mem j⟩ =
      if j' = j then ⟨idemNH ℤ (n + 1), idemNH_mem⟩ else 0 from by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, nhB_mul_nhA hj' hj]
        split_ifs <;> rfl)
  rw [blockVal_mul, blockVal_nhB, blockVal_nhA] at h
  rw [h]
  split_ifs
  · exact blockVal_idemNH hpn hc
  · exact blockVal_zero hpn hc

include hc in
/-- **The splitting on a block, part 2**: `∑_{j ≤ n} A_j B_j = e_{i_p, n} ⊗ 1`. -/
theorem sum_blockA_mul_blockB :
    ∑ j : Fin (n + 1), blockA k Q i hpn j * blockB k Q i hpn j = blockIdem i p n := by
  have h := congrArg (blockVal k Q hpn hc)
    (show ∑ j : Fin (n + 1), (⟨nhA ℤ n j, nhA_mem j⟩ : nilHecke ℤ (n + 1)) *
      ⟨nhB ℤ n j, nhB_mem j⟩ = ⟨nhE' ℤ n, nhE'_mem⟩ from by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        exact sum_nhA_mul_nhB)
  rw [blockVal_sum, blockVal_nhE'] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blockVal_mul, blockVal_nhA, blockVal_nhB]

end blockAB

/-! ### Degrees -/

section grading

theorem _root_.MvPolynomial.IsHomogeneous.isWeightedHomogeneous_of_const {σ R : Type*}
    [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ} (hP : P.IsHomogeneous d) {w : σ → ℤ}
    {c : ℤ} (hw : ∀ a, w a = c) : P.IsWeightedHomogeneous w (d * c) := by
  intro s hs
  have h1 := hP hs
  rw [Finsupp.weight_apply] at h1 ⊢
  simp only [hw, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one] at h1 ⊢
  rw [← Finset.sum_smul, h1, nsmul_eq_mul]

variable (G : GradingDatum Q) {i : Seq ν} {p n : ℕ} (hpn : p + (n + 1) ≤ Multiset.card ν)
  {c : I} (hcl : ∀ a : Fin (Multiset.card ν), p ≤ a → (a : ℕ) < p + (n + 1) → i.lbl a = c)

include hcl in
/-- A homogeneous polynomial of degree `d` on the block has degree `d · degX c`. -/
theorem pol_blockPoly_mul_e_mem_grade {P : MvPolynomial (Fin (n + 1)) ℤ} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    (pol (blockPoly hpn P) * e i : A) ∈ G.grade ν (d * G.degX c) := by
  have hw : (map (Int.castRingHom k) P).IsWeightedHomogeneous
      (fun a => G.dx (blockEmb hpn a) i) (d * G.degX c) :=
    (hP.map _).isWeightedHomogeneous_of_const fun a => by
      show G.degX (i.lbl (blockEmb hpn a)) = _
      rw [hcl _ (by simp [blockEmb]) (by simp [blockEmb])]
  have h := G.mk_mem_grade_of_homAt (G.homAt_ncEval (l := i) (blockEmb hpn) _ hw (G.homAt_fe i))
  rw [map_mul, mk_ncEval, add_zero] at h
  change ncEval (fun a => (x (blockEmb hpn a) : A)) _ * e i ∈ _ at h
  rwa [ncEval_eq_pol, ← map_rename] at h

include hpn hcl in
/-- `ψ_{w_0} 1_i` on the first `l` strands of the block has degree `-(l choose 2) degX c`. -/
theorem blockWord_mul_e_mem_grade {l : ℕ} (hl : l ≤ n + 1) :
    (ψw (blockWord p l) * e i : A) ∈ G.grade ν (-(l.choose 2 : ℤ) * G.degX c) := by
  have h2 := G.ψw_mul_pol_mul_e_mem_grade (blockWord p l) i (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, degW_of_forall G (c := c)
    (fun j hj => by have := mem_blockWord hj; omega)
    (fun j hj hj' => ⟨hcl _ (mem_blockWord hj).1 (by simp only; have := mem_blockWord hj; omega),
      hcl _ (by simp only; have := mem_blockWord hj; omega)
        (by simp only; have := mem_blockWord hj; omega)⟩), length_blockWord, add_zero] at h2
  exact h2

omit [DecidableEq I] in
theorem isHomogeneous_xDelta_self (l : ℕ) :
    (xDelta l : MvPolynomial (Fin l) ℤ).IsHomogeneous (l.choose 2) := by
  rw [← sum_fin_sub_one_sub]
  exact IsHomogeneous.prod _ _ _ fun a _ => isHomogeneous_X_pow _ _

variable {G} in
private theorem mul_mem_grade_e {y z : A} {t : Seq ν} {d d' : ℤ}
    (hy : y * e t ∈ G.grade ν d) (hz : z * e t ∈ G.grade ν d') (hze : e t * z = z * e t) :
    y * z * e t ∈ G.grade ν (d + d') := by
  have := SetLike.mul_mem_graded hy hz
  rwa [mul_assoc y, ← mul_assoc (e t), hze, mul_assoc, e_mul_self, ← mul_assoc] at this

include hcl in
/-- `A_j` has degree `degX c · (j - n)`. -/
theorem blockA_mem_grade (hc : IsConstOn i p (n + 1)) (j : ℕ) :
    blockA k Q i hpn j ∈ G.grade ν (G.degX c * ((j : ℤ) - n)) := by
  have h := mul_mem_grade_e
    (pol_blockPoly_mul_e_mem_grade G hpn hcl (isHomogeneous_xDelta.mul (isHomogeneous_X_pow (Fin.last n) j)))
    (blockWord_mul_e_mem_grade G hpn hcl le_rfl) (blockψ_mul_e hc).symm
  convert h using 2
  rw [choose_two_succ]
  push_cast
  ring

include hcl in
/-- `B_j` has degree `degX c · (n - j)` for `j ≤ n`. -/
theorem blockB_mem_grade (hc : IsConstOn i p (n + 1)) {j : ℕ} (hj : j ≤ n) :
    blockB k Q i hpn j ∈ G.grade ν (G.degX c * ((n : ℤ) - j)) := by
  have h1 := mul_mem_grade_e
    (pol_blockPoly_mul_e_mem_grade G hpn hcl (isHomogeneous_xDelta_self (n + 1)))
    (blockWord_mul_e_mem_grade G hpn hcl le_rfl) (blockψ_mul_e hc).symm
  have h2 := mul_mem_grade_e h1
    (pol_blockPoly_mul_e_mem_grade G hpn hcl ((isHomogeneous_nhDual hj).mul isHomogeneous_xDelta))
    (e_commute_pol i _).eq
  have h3 := mul_mem_grade_e h2 (blockWord_mul_e_mem_grade G hpn hcl (Nat.le_succ n))
    (blockψ_mul_e (hc.mono (Nat.le_succ n))).symm
  convert h3 using 2
  rw [Nat.cast_add, Nat.cast_sub hj]
  ring

end grading

/-! ### Divided-power blocks in a context -/

section context

variable {i : Seq ν} {p n : ℕ} (hpn : p + (n + 1) ≤ Multiset.card ν)

theorem commute_blockElt_pol_blockPoly {q l : ℕ} (hq : q + l ≤ p ∨ p + (n + 1) ≤ q)
    (P : MvPolynomial (Fin (n + 1)) ℤ) :
    Commute (blockElt q l : A) (pol (blockPoly hpn P)) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [blockPoly, rename_C, map_C, algHom_C]
    exact Algebra.commute_algebraMap_right _ _
  | add P P' hP hP' => rw [blockPoly, map_add, map_add, map_add]; exact hP.add_right hP'
  | mul_X P a hP =>
    rw [blockPoly, map_mul, map_mul, map_mul, rename_X, map_X, pol_X]
    exact hP.mul_right (commute_x_blockElt (by simp only [blockEmb]; omega)).symm

omit [DecidableEq I] in
theorem IsBlocks.cons_mono {t : Seq ν} {q l l' : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks t ((q, l) :: bs)) (hl : l' ≤ l) : IsBlocks t ((q, l') :: bs) where
  le b hb := by
    rcases List.mem_cons.1 hb with rfl | hb
    · have := h.le _ List.mem_cons_self; simp only at this ⊢; omega
    · exact h.le b (List.mem_cons_of_mem _ hb)
  const b hb := by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (h.const _ List.mem_cons_self).mono hl
    · exact h.const b (List.mem_cons_of_mem _ hb)
  disj := by
    refine List.Pairwise.cons (fun c hc => ?_) (List.pairwise_cons.1 h.disj).2
    have := (List.pairwise_cons.1 h.disj).1 c hc
    simp only at this ⊢; omega

/-- `1_{…} e_{i_q, l} = 1_{…i^{(l)}…}`: adding a block to a context. -/
theorem divIdem_mul_blockIdem {t : Seq ν} {q l : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks t ((q, l) :: bs)) : (divIdem t bs * blockIdem t q l : A) = divIdem t ((q, l) :: bs) := by
  have hb := h.const _ List.mem_cons_self
  have hcomm : Commute (blockElt q l : A) (blocksElt bs) :=
    (commute_blocksElt fun c hc => commute_blockElt_blockElt
      ((List.pairwise_cons.1 h.disj).1 c hc).symm).symm
  rw [divIdem, divIdem, blockIdem, blocksElt_cons, mul_assoc, ← mul_assoc (e t),
    ← blockElt_mul_e hb, mul_assoc, e_mul_self, ← mul_assoc, hcomm.eq]

/-- The context `1_{…} = divIdem i bs` of blocks disjoint from `[p, p + n + 1)` commutes
with `B_j`. -/
theorem commute_divIdem_blockB {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs)
    (hc : IsConstOn i p (n + 1))
    (hdisj : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + (n + 1) ≤ b.1) (j : ℕ) :
    Commute (divIdem i bs : A) (blockB k Q i hpn j) := by
  have hF : ∀ P, Commute (blocksElt bs : A) (pol (blockPoly hpn P)) := fun P =>
    commute_blocksElt fun b hb => commute_blockElt_pol_blockPoly hpn (hdisj b hb) P
  have hW : ∀ l ≤ n + 1, Commute (blocksElt bs : A) (ψw (blockWord p l)) := fun l hl =>
    commute_blocksElt fun b hb => (commute_ψw_blockElt fun j hj => by
      have := mem_blockWord hj; have := hdisj b hb; omega).symm
  have hE : ∀ P, Commute (e i : A) (pol (blockPoly hpn P)) := fun P => e_commute_pol i _
  have hEW : ∀ l ≤ n + 1, Commute (e i : A) (ψw (blockWord p l)) := fun l hl =>
    (blockψ_mul_e (hc.mono hl)).symm
  have hFE : Commute (blocksElt bs : A) (e i) := blocksElt_mul_e hbs.const
  rw [divIdem, blockB]
  refine Commute.mul_left ?_ ?_
  · exact ((((hF _).mul_right (hW _ le_rfl)).mul_right (hF _)).mul_right
      (hW _ (Nat.le_succ n))).mul_right hFE
  · exact ((((hE _).mul_right (hEW _ le_rfl)).mul_right (hE _)).mul_right
      (hEW _ (Nat.le_succ n))).mul_right (Commute.refl _)

/-- **Splitting `1_{…i^{(n)} i…}`** (KL I §2.5): for a divided-power block `(p, n + 1)` in the
context of further blocks `bs`,
`divIdem i ((p, n) :: bs) = ∑_{j ≤ n} (1_{…} A_j) B_j` with
`B_{j'} (1_{…} A_j) = δ_{j' j} divIdem i ((p, n + 1) :: bs)`. -/
theorem isSplitting_divIdem_succ {bs : List (ℕ × ℕ)} (h : IsBlocks i ((p, n + 1) :: bs)) :
    Graded.IsSplitting (divIdem i ((p, n) :: bs) : A)
      (fun _ : Fin (n + 1) => divIdem i ((p, n + 1) :: bs))
      (fun j => divIdem i bs * blockA k Q i (h.le _ List.mem_cons_self) j)
      (fun j => blockB k Q i (h.le _ List.mem_cons_self) j) where
  mul_eq j' j := by
    have hc := h.const _ List.mem_cons_self
    have hdisj : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + (n + 1) ≤ b.1 := fun b hb => by
      have := (List.pairwise_cons.1 h.disj).1 b hb; simp only at this; omega
    rw [← mul_assoc, ← (commute_divIdem_blockB _ h.tail hc hdisj j').eq, mul_assoc,
      blockB_mul_blockA _ hc (by omega) (by omega)]
    simp only [Fin.ext_iff]
    split_ifs
    · exact divIdem_mul_blockIdem h
    · exact mul_zero _
  sum_eq := by
    have hc := h.const _ List.mem_cons_self
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_blockA_mul_blockB _ hc]
    exact divIdem_mul_blockIdem (h.cons_mono (Nat.le_succ n))

end context

end Categorification.KLR.KLRAlgebra
