/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerIdempotents
import Categorification.Algebra.IdempotentEquiv

/-!
# KL I, Proposition 2.13 and Corollary 2.14

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.5, Proposition 2.13 (TeX label `prop-iso-leftright`, lines ~1640–1698)
and Corollary 2.14 (lines ~1700–1708).

**Proposition 2.13.** There are isomorphisms of graded projective right `R(ν)`-modules
`₍…ij…₎P ≅ ₍…ji…₎P` if `i · j = 0`, and `₍…iji…₎P ≅ ₍…i⁽²⁾j…₎P ⊕ ₍…ji⁽²⁾…₎P` if `i · j = -1`,
and similarly for the left projectives `P_i = R(ν) ψ(1_i) {-⟨i⟩}`.

(The printed statement has `P_{…i⁽²⁾j…} ⊕ P_{…ji⁽²⁾…}` on the right of the first display;
the proof, and the right-module setting, show that the right projectives `₍…₎P` are meant.)

We prove the content of the proposition as statements about idempotents of `R(ν)` for the
KL I data `klQ Γ` over an arbitrary commutative ring `k`, in an arbitrary context `…`:
the dots are represented by a sequence `t ∈ Seq ν` together with a list `bs` of divided-power
blocks away from the positions being changed (`divIdem t bs` is the idempotent `1_{…}` of
`Categorification.KLR.DividedPowerIdempotents`). Positions are zero-indexed.

* `i · j = 0` (`prop213_zero`): with `a = F ψ_k 1_{…ji…}` and `b = F ψ_k 1_{…ij…}`
  (`F` the product of the context blocks), `a b = 1_{…ij…}`, `b a = 1_{…ji…}`
  (the paper's "multiplication by the crossing").
* `i · j = -1` (`prop213_neg_one`): `1_{…iji…} = f₁ + f₂` is an orthogonal decomposition into
  idempotents with `f₁ ~ 1_{…i⁽²⁾j…}` and `f₂ ~ 1_{…ji⁽²⁾…}`; the equivalences are given by
  the entries of the paper's matrices
  `B₀ = (x_k ψ_k ψ_{k+1} 1_{…iji…} ; x_{k+1} ψ_{k+1} ψ_k 1_{…iji…})` and
  `B₁ = (-ψ_{k+1} ψ_k 1_{…i⁽²⁾j…}, ψ_k ψ_{k+1} 1_{…ji⁽²⁾…})`, which have degrees `1` and `-1`
  (`prop213_degrees`), matching the grading shift `⟨…i⁽²⁾j…⟩ - ⟨…iji…⟩ = 1`.
  Here `f₁ = -ψ_{k+1} ψ_k ψ_{k+1} 1_{…iji…}` and `f₂ = ψ_k ψ_{k+1} ψ_k 1_{…iji…}`; their sum
  is `1_{…iji…}` by the relation (2.8).

Existential forms: `prop213_zero'` and `prop213_neg_one'`; left (antiinvolution) forms:
`prop213_zero'` and `prop213_neg_one_hflip`. Degrees of the maps, also in the context of the
blocks `bs`: `prop213_zero_degrees`, `prop213_degrees`, `prop213_neg_one_degrees`.

The module isomorphisms follow (`Categorification.Algebra.IdempotentEquiv`):

* `prop213_zero_rIdealEquiv`, `prop213_neg_one_rIdealEquiv` : right projectives `1_i R(ν)`;
* `prop213_zero_lIdealEquiv`, `prop213_neg_one_lIdealEquiv` : left projectives
  `R(ν) ψ(1_i)` (via the antiinvolution `hflip`);
* `cor214_zero`, `cor214_neg_one` : **Corollary 2.14**, `1_{…ij…} M ≅ 1_{…ji…} M` and
  `1_{…iji…} M ≅ 1_{…i⁽²⁾j…} M ⊕ 1_{…ji⁽²⁾…} M` for every left `R(ν)`-module `M`.

These isomorphisms are ungraded; the degrees of the maps are recorded by `prop213_degrees`
(grading shifts are not formalized as a category of graded modules here).
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial Equiv TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-! ### Labels of transposed sequences -/

section labels

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

omit [DecidableEq I] in
theorem lbl_sadj_left {j : ℕ} (h : j + 1 < m) (t : Seq ν) :
    (sadj m j • t).lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ := by
  simp only [Seq.lbl]; rw [sadj_smul_apply, sadj_apply_left h]

omit [DecidableEq I] in
theorem lbl_sadj_right {j : ℕ} (h : j + 1 < m) (t : Seq ν) :
    (sadj m j • t).lbl ⟨j + 1, h⟩ = t.lbl ⟨j, by omega⟩ := by
  simp only [Seq.lbl]; rw [sadj_smul_apply, sadj_apply_right h]

omit [DecidableEq I] in
theorem lbl_sadj_of_ne {j : ℕ} (t : Seq ν) (a : Fin m) (h₁ : (a : ℕ) ≠ j)
    (h₂ : (a : ℕ) ≠ j + 1) : (sadj m j • t).lbl a = t.lbl a := by
  simp only [Seq.lbl]; rw [sadj_smul_apply, sadj_apply_of_ne a h₁ h₂]

omit [DecidableEq I] in
theorem IsConstOn.sadj {t : Seq ν} {p n j : ℕ} (hc : IsConstOn t p n)
    (h : j + 1 < p ∨ p + n ≤ j) : IsConstOn (sadj m j • t) p n := by
  intro a b h1 h2 h3 h4
  rw [lbl_sadj_of_ne t a (by omega) (by omega), lbl_sadj_of_ne t b (by omega) (by omega)]
  exact hc a b h1 h2 h3 h4

omit [DecidableEq I] in
theorem IsBlocks.sadj {t : Seq ν} {bs : List (ℕ × ℕ)} (hb : IsBlocks t bs) {j : ℕ}
    (h : ∀ b ∈ bs, j + 1 < b.1 ∨ b.1 + b.2 ≤ j) : IsBlocks (sadj m j • t) bs :=
  ⟨hb.le, fun b hb' => (hb.const b hb').sadj (h b hb'), hb.disj⟩

end labels

/-! ### Rewriting lemmas in left-associated form -/

section rewriting

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

theorem mul_e_mul_e (y : A) (t : Seq ν) : y * e t * e t = y * e t := by
  rw [mul_assoc, e_mul_self]

theorem mul_e_mul_x (y : A) (t : Seq ν) (a : Fin m) : y * e t * x a = y * x a * e t := by
  rw [mul_assoc, e_mul_x, ← mul_assoc]

theorem mul_e_mul_ψ (y : A) (t : Seq ν) (j : ℕ) :
    y * e t * ψ j = y * ψ j * e (sadj m j • t) := by
  rw [mul_assoc, e_mul_ψ, ← mul_assoc]

theorem mul_e_mul_ψ_of_eq (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩) : y * e t * ψ j = y * ψ j * e t := by
  rw [mul_e_mul_ψ, sadj_smul_eq_self h ht]

theorem mul_ψ_mul_x (y : A) (j : ℕ) (a : Fin m) (h₁ : (a : ℕ) ≠ j) (h₂ : (a : ℕ) ≠ j + 1) :
    y * ψ j * x a = y * x a * ψ j := by
  rw [mul_assoc, ← x_mul_ψ a j h₁ h₂, ← mul_assoc]

theorem mul_ψ_mul_ψ_mul_e_of_eq (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩) : y * ψ j * ψ j * e t = 0 := by
  rw [mul_assoc, mul_assoc, ← mul_assoc (ψ j), ψ_sq j h, if_pos ht, mul_zero]

/-- `ψ_j x_j ψ_j 1_t = ψ_j 1_t` for `t_j = t_{j+1}`. -/
theorem mul_ψ_mul_x_mul_ψ_mul_e_left (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩) :
    y * ψ j * x ⟨j, by omega⟩ * ψ j * e t = y * ψ j * e t := by
  have h1 := dot_cross_right (Q := Q) j h t
  rw [if_pos ht, sub_mul, sub_eq_iff_eq_add] at h1
  calc y * ψ j * x ⟨j, by omega⟩ * ψ j * e t
      = y * (ψ j * x ⟨j, by omega⟩ * e t) * ψ j := by
        rw [mul_assoc (y * ψ j * x _), ← e_mul_ψ_of_eq h ht]; simp only [mul_assoc]
    _ = y * ψ j * e t := by
        rw [h1]
        simp only [mul_add, add_mul, ← mul_assoc]
        rw [mul_e_mul_ψ_of_eq _ h ht, mul_e_mul_ψ_of_eq _ h ht, mul_ψ_mul_ψ_mul_e_of_eq _ h ht,
          add_zero]

/-- `ψ_j x_{j+1} ψ_j 1_t = -ψ_j 1_t` for `t_j = t_{j+1}`. -/
theorem mul_ψ_mul_x_mul_ψ_mul_e_right (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩) :
    y * ψ j * x ⟨j + 1, h⟩ * ψ j * e t = -(y * ψ j * e t) := by
  have h1 := dot_cross_left (Q := Q) j h t
  rw [if_pos ht, sub_mul, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1
  calc y * ψ j * x ⟨j + 1, h⟩ * ψ j * e t
      = y * (ψ j * x ⟨j + 1, h⟩ * e t) * ψ j := by
        rw [mul_assoc (y * ψ j * x _), ← e_mul_ψ_of_eq h ht]; simp only [mul_assoc]
    _ = -(y * ψ j * e t) := by
        rw [← h1]
        simp only [mul_sub, sub_mul, ← mul_assoc]
        rw [mul_e_mul_ψ_of_eq _ h ht, mul_e_mul_ψ_of_eq _ h ht, mul_ψ_mul_ψ_mul_e_of_eq _ h ht,
          zero_sub]

/-- `(x_j ψ_j 1_t)² = x_j ψ_j 1_t` for `t_j = t_{j+1}`. -/
theorem mul_xψe_mul_xψe (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩) :
    y * (x ⟨j, by omega⟩ * ψ j * e t) * (x ⟨j, by omega⟩ * ψ j * e t) =
      y * (x ⟨j, by omega⟩ * ψ j * e t) := by
  simp only [← mul_assoc]
  rw [mul_e_mul_x, mul_e_mul_ψ_of_eq _ h ht, mul_e_mul_e,
    mul_ψ_mul_x_mul_ψ_mul_e_left _ h ht]

end rewriting


/-! ### Context blocks -/

section context

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

theorem blocksElt_mul_blocksElt_mul_e {t : Seq ν} {bs : List (ℕ × ℕ)} (hb : IsBlocks t bs) :
    (blocksElt bs * blocksElt bs * e t : A) = blocksElt bs * e t := by
  have := (isIdempotentElem_divIdem (Q := Q) hb).eq
  rwa [divIdem, mul_assoc, ← mul_assoc (e t), ← blocksElt_mul_e hb.const, mul_assoc,
    e_mul_self, ← mul_assoc] at this

theorem blocksElt_sq_mul_of_commute {t : Seq ν} {bs : List (ℕ × ℕ)} (hb : IsBlocks t bs)
    {y : A} (hy : Commute (blocksElt bs) y) :
    blocksElt bs * blocksElt bs * (y * e t) = blocksElt bs * (y * e t) := by
  calc blocksElt bs * blocksElt bs * (y * e t) = y * (blocksElt bs * blocksElt bs * e t) := by
        rw [← mul_assoc, (hy.mul_left hy).eq]; simp only [mul_assoc]
    _ = _ := by rw [blocksElt_mul_blocksElt_mul_e hb, ← mul_assoc, ← hy.eq, mul_assoc]

end context


/-! ### Relations of KL I in left-associated form -/

section KL

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj] {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => R1 k Γ ν

theorem mul_ψ_mul_ψ_mul_e_of_adj (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩)) :
    y * ψ j * ψ j * e t = y * x ⟨j, by omega⟩ * e t + y * x ⟨j + 1, h⟩ * e t := by
  rw [mul_assoc, mul_assoc, ← mul_assoc (ψ j), KL1.ψ_sq_of_adj j h t hadj, add_mul, mul_add,
    ← mul_assoc, ← mul_assoc]

theorem mul_ψ_mul_ψ_mul_e_of_not_adj (y : A) {t : Seq ν} {j : ℕ} (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩)) :
    y * ψ j * ψ j * e t = y * e t := by
  rw [mul_assoc, mul_assoc, ← mul_assoc (ψ j), KL1.ψ_sq_of_not_adj j h t hne hadj]

/-! ### The case `i · j = 0` -/

section zero

variable {t : Seq ν} {bs : List (ℕ × ℕ)} {j : ℕ}

/-- The local equivalence `1_{…ij…} ~ 1_{…ji…}` for `i · j = 0`, given by the crossing:
`(ψ_j 1_{…ji…}) (ψ_j 1_{…ij…}) = 1_{…ij…}` and `(ψ_j 1_{…ij…}) (ψ_j 1_{…ji…}) = 1_{…ji…}`. -/
theorem isEquivPair_zero (h : j + 1 < m) (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩)) :
    IsEquivPair (ψ j * e (sadj m j • t) : A) (ψ j * e t) (e t) (e (sadj m j • t)) := by
  have hne' : (sadj m j • t).lbl ⟨j, by omega⟩ ≠ (sadj m j • t).lbl ⟨j + 1, h⟩ := by
    rw [lbl_sadj_left h, lbl_sadj_right h]; exact Ne.symm hne
  have hadj' : ¬ Γ.Adj ((sadj m j • t).lbl ⟨j, by omega⟩) ((sadj m j • t).lbl ⟨j + 1, h⟩) := by
    rw [lbl_sadj_left h, lbl_sadj_right h]; exact fun h' => hadj h'.symm
  refine IsEquivPair.of_mul_left ?_ ?_ ?_ ?_
  · rw [← mul_assoc, mul_e_mul_ψ, sadj_smul_smul, mul_e_mul_e, KL1.ψ_sq_of_not_adj j h t hne hadj]
  · rw [← mul_assoc, mul_e_mul_ψ, mul_e_mul_e, KL1.ψ_sq_of_not_adj j h _ hne' hadj']
  · rw [← mul_assoc, ← one_mul (e t), mul_e_mul_ψ, one_mul, mul_e_mul_e]
  · rw [mul_e_mul_e]

variable (Γ) in
/-- The context idempotent `F` (product of the divided-power blocks `bs`) commutes with the
generators near positions `j, …, j + d - 1` when the blocks avoid these positions. -/
theorem commute_blocksElt_of_avoid {bs : List (ℕ × ℕ)} {j d : ℕ}
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + d ≤ b.1) :
    (∀ a : Fin m, j ≤ a → (a : ℕ) < j + d → Commute (blocksElt bs : A) (x a)) ∧
    (∀ l, j ≤ l → l + 1 < j + d → Commute (blocksElt bs : A) (ψ l)) := by
  refine ⟨fun a h1 h2 => commute_blocksElt fun b hb => (commute_x_blockElt ?_).symm,
    fun l h1 h2 => commute_blocksElt fun b hb => (commute_ψ_blockElt ?_).symm⟩
  · have := hbs b hb; omega
  · have := hbs b hb; omega

/-- **KL I, Proposition 2.13, case `i · j = 0`** (idempotent form, in a context `…` of
divided-power blocks `bs` away from the positions `j, j + 1`): with `F = blocksElt bs`,
`a = F ψ_j 1_{…ji…}` and `b = F ψ_j 1_{…ij…}` satisfy `a b = 1_{…ij…}`, `b a = 1_{…ji…}`,
`a b a = a`, `b a b = b`. -/
theorem prop213_zero (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    IsEquivPair (blocksElt bs * (ψ j * e (sadj m j • t)) : A) (blocksElt bs * (ψ j * e t))
      (divIdem t bs) (divIdem (sadj m j • t) bs) := by
  have hb' : IsBlocks (sadj m j • t) bs := hb.sadj fun b hb => by have := hbs b hb; omega
  have hψ := (commute_blocksElt_of_avoid Γ (ν := ν) (k := k) hbs).2 j le_rfl (by omega)
  have het : Commute (blocksElt bs : A) (e t) := blocksElt_mul_e hb.const
  have hes : Commute (blocksElt bs : A) (e (sadj m j • t)) := blocksElt_mul_e hb'.const
  exact (isEquivPair_zero h hne hadj).mul_of_commute'
    (blocksElt_mul_blocksElt_mul_e hb) (blocksElt_mul_blocksElt_mul_e hb')
    (hψ.mul_right hes) (hψ.mul_right het)

/-- **KL I, Proposition 2.13, case `i · j = 0`**: `1_{…ij…} ~ 1_{…ji…}` and (left version,
via the antiinvolution `ψ`) `ψ(1_{…ij…}) ~ ψ(1_{…ji…})`. -/
theorem prop213_zero' (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    IdemEquiv (divIdem t bs : A) (divIdem (sadj m j • t) bs) ∧
      IdemEquiv (hflip (divIdem t bs : A)) (hflip (divIdem (sadj m j • t) bs)) :=
  have H := prop213_zero hb h hne hadj hbs
  ⟨⟨_, _, H⟩, ⟨_, _, H.map_anti hflip hflip_mul⟩⟩

end zero


/-! ### The case `i · j = -1` -/

section negOne

variable {t : Seq ν} {bs : List (ℕ × ℕ)} {j : ℕ}

variable (t) in
/-- The idempotent `1_{…i⁽²⁾j…} = x_j ψ_j 1_{…iij…}` (locally; `…iij… = s_{j+1} (…iji…)`). -/
noncomputable def idemI2J (h : j + 2 < m) : A := x ⟨j, by omega⟩ * ψ j * e (sadj m (j + 1) • t)

variable (t) in
/-- The idempotent `1_{…ji⁽²⁾…} = x_{j+1} ψ_{j+1} 1_{…jii…}` (locally; `…jii… = s_j (…iji…)`). -/
noncomputable def idemJI2 (h : j + 2 < m) : A :=
  x ⟨j + 1, by omega⟩ * ψ (j + 1) * e (sadj m j • t)

variable (t) in
/-- The top entry of the paper's matrix `B₀`: `x_j ψ_j ψ_{j+1} 1_{…iji…}`, written as
`1_{…i⁽²⁾j…} ψ_{j+1}`. -/
noncomputable def b0Top (h : j + 2 < m) : A := idemI2J t h * ψ (j + 1)

variable (t) in
/-- The bottom entry of `B₀`: `x_{j+1} ψ_{j+1} ψ_j 1_{…iji…} = 1_{…ji⁽²⁾…} ψ_j`. -/
noncomputable def b0Bot (h : j + 2 < m) : A := idemJI2 t h * ψ j

variable (t) in
/-- The left entry of the paper's matrix `B₁`: `-ψ_{j+1} ψ_j 1_{…i⁽²⁾j…}`. -/
noncomputable def b1Left (h : j + 2 < m) : A := -(ψ (j + 1) * ψ j * idemI2J t h)

variable (t) in
/-- The right entry of `B₁`: `ψ_j ψ_{j+1} 1_{…ji⁽²⁾…}`. -/
noncomputable def b1Right (h : j + 2 < m) : A := ψ j * ψ (j + 1) * idemJI2 t h

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lblU_eq (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    (sadj m (j + 1) • t).lbl ⟨j, by omega⟩ = (sadj m (j + 1) • t).lbl ⟨j + 1, by omega⟩ := by
  rw [lbl_sadj_of_ne t _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
    lbl_sadj_left (show j + 1 + 1 < m by omega)]
  exact ht

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lblU_adj (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    Γ.Adj ((sadj m (j + 1) • t).lbl ⟨j + 1, by omega⟩)
      ((sadj m (j + 1) • t).lbl ⟨j + 1 + 1, by omega⟩) := by
  rw [lbl_sadj_left (show j + 1 + 1 < m by omega), lbl_sadj_right (show j + 1 + 1 < m by omega)]
  have : t.lbl ⟨j + 1 + 1, by omega⟩ = t.lbl ⟨j, by omega⟩ := ht.symm
  rw [this]; exact hadj

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lblV_eq (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    (sadj m j • t).lbl ⟨j + 1, by omega⟩ = (sadj m j • t).lbl ⟨j + 1 + 1, by omega⟩ := by
  rw [lbl_sadj_right (show j + 1 < m by omega),
    lbl_sadj_of_ne t _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]
  exact ht

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem lblV_adj (h : j + 2 < m) (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    Γ.Adj ((sadj m j • t).lbl ⟨j, by omega⟩) ((sadj m j • t).lbl ⟨j + 1, by omega⟩) := by
  rw [lbl_sadj_left (show j + 1 < m by omega), lbl_sadj_right (show j + 1 < m by omega)]
  exact hadj.symm

theorem isIdempotentElem_idemI2J (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) : IsIdempotentElem (idemI2J t h : A) := by
  have := mul_xψe_mul_xψe (1 : A) (show j + 1 < m by omega) (lblU_eq h ht)
  rwa [one_mul] at this

theorem isIdempotentElem_idemJI2 (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) : IsIdempotentElem (idemJI2 t h : A) := by
  have := mul_xψe_mul_xψe (1 : A) (show j + 1 + 1 < m by omega) (lblV_eq h ht)
  rwa [one_mul] at this

/-- `B₀ B₁` has diagonal entry `1_{…i⁽²⁾j…}` (KL I, proof of Proposition 2.13). -/
theorem b0Top_mul_b1Left (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    (b0Top t h * b1Left t h : A) = idemI2J t h := by
  have hu := lblU_eq h ht
  have hua := lblU_adj h ht hadj
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  simp only [b0Top, b1Left, idemI2J, mul_neg, ← mul_assoc]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_left _ h1 hu,
    ← mul_e_mul_ψ_of_eq (x ⟨j, by omega⟩ * ψ j * e (sadj m (j + 1) • t) * ψ (j + 1) * ψ (j + 1))
      h1 hu, mul_ψ_mul_ψ_mul_e_of_adj _ h2 hua, add_mul]
  simp only [mul_e_mul_x, mul_e_mul_e, fun y => mul_e_mul_ψ_of_eq y h1 hu]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_right _ h1 hu, mul_ψ_mul_x _ j _ (by simp only; omega)
    (by simp only; omega), mul_ψ_mul_ψ_mul_e_of_eq _ h1 hu, add_zero, neg_neg]


/-- `B₀ B₁` has diagonal entry `1_{…ji⁽²⁾…}` (KL I, proof of Proposition 2.13). -/
theorem b0Bot_mul_b1Right (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    (b0Bot t h * b1Right t h : A) = idemJI2 t h := by
  have hv := lblV_eq h ht
  have hva := lblV_adj h hadj
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  simp only [b0Bot, b1Right, idemJI2, ← mul_assoc]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_left _ h2 hv,
    ← mul_e_mul_ψ_of_eq (x ⟨j + 1, by omega⟩ * ψ (j + 1) * e (sadj m j • t) * ψ j * ψ j)
      h2 hv, mul_ψ_mul_ψ_mul_e_of_adj _ h1 hva, add_mul]
  simp only [mul_e_mul_x, mul_e_mul_e, fun y => mul_e_mul_ψ_of_eq y h2 hv]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_left _ h2 hv, mul_ψ_mul_x _ (j + 1) _ (by simp only; omega)
    (by simp only; omega), mul_ψ_mul_ψ_mul_e_of_eq _ h2 hv, zero_add]

theorem b1Left_mul_b0Top (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    (b1Left t h * b0Top t h : A) = -(ψ (j + 1) * ψ j * ψ (j + 1) * e t) := by
  have hu := lblU_eq h ht
  have h1 : j + 1 < m := by omega
  simp only [b1Left, b0Top, idemI2J, neg_mul, ← mul_assoc]
  simp only [mul_e_mul_x, mul_e_mul_e, fun y => mul_e_mul_ψ_of_eq y h1 hu]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_left _ h1 hu, mul_ψ_mul_x_mul_ψ_mul_e_left _ h1 hu, mul_e_mul_ψ,
    sadj_smul_smul]

theorem b1Right_mul_b0Bot (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    (b1Right t h * b0Bot t h : A) = ψ j * ψ (j + 1) * ψ j * e t := by
  have hv := lblV_eq h ht
  have h2 : j + 1 + 1 < m := by omega
  simp only [b1Right, b0Bot, idemJI2, ← mul_assoc]
  simp only [mul_e_mul_x, mul_e_mul_e, fun y => mul_e_mul_ψ_of_eq y h2 hv]
  rw [mul_ψ_mul_x_mul_ψ_mul_e_left _ h2 hv, mul_ψ_mul_x_mul_ψ_mul_e_left _ h2 hv, mul_e_mul_ψ,
    sadj_smul_smul]

/-- `B₁ B₀ = 1_{…iji…}` (KL I, proof of Proposition 2.13, `\BoneBoB`, using (2.8)). -/
theorem b1Left_mul_b0Top_add_b1Right_mul_b0Bot (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    (b1Left t h * b0Top t h + b1Right t h * b0Bot t h : A) = e t := by
  rw [b1Left_mul_b0Top h ht, b1Right_mul_b0Bot h ht, neg_add_eq_sub]
  exact KL1.braid_hard j h t ht hadj

theorem b0Top_mul_e : (b0Top t h * e t : A) = b0Top t h := by
  simp only [b0Top, idemI2J, ← mul_assoc, mul_e_mul_ψ, sadj_smul_smul, mul_e_mul_e]

theorem b0Bot_mul_e : (b0Bot t h * e t : A) = b0Bot t h := by
  simp only [b0Bot, idemJI2, ← mul_assoc, mul_e_mul_ψ, sadj_smul_smul, mul_e_mul_e]

/-- The pair `(B₀ top entry, B₁ left entry)` exhibits `1_{…i⁽²⁾j…} ~ f₁`,
`f₁ = -ψ_{j+1} ψ_j ψ_{j+1} 1_{…iji…}`. -/
theorem isEquivPair_top (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    IsEquivPair (b0Top t h : A) (b1Left t h) (idemI2J t h) (b1Left t h * b0Top t h) := by
  have hi := (isIdempotentElem_idemI2J (k := k) (Γ := Γ) h ht).eq
  refine IsEquivPair.of_mul_left (b0Top_mul_b1Left h ht hadj) rfl ?_ ?_
  · rw [b0Top, ← mul_assoc, hi]
  · rw [b1Left, neg_mul, mul_assoc, hi]

/-- The pair `(B₀ bottom entry, B₁ right entry)` exhibits `1_{…ji⁽²⁾…} ~ f₂`,
`f₂ = ψ_j ψ_{j+1} ψ_j 1_{…iji…}`. -/
theorem isEquivPair_bot (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    IsEquivPair (b0Bot t h : A) (b1Right t h) (idemJI2 t h) (b1Right t h * b0Bot t h) := by
  have hi := (isIdempotentElem_idemJI2 (k := k) (Γ := Γ) h ht).eq
  refine IsEquivPair.of_mul_left (b0Bot_mul_b1Right h ht hadj) rfl ?_ ?_
  · rw [b0Bot, ← mul_assoc, hi]
  · rw [b1Right, mul_assoc, hi]

/-- `1_{…iji…} = f₁ + f₂` is an orthogonal decomposition. -/
theorem isOrthDecomp_local (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    IsOrthDecomp (e t : A) (b1Left t h * b0Top t h) (b1Right t h * b0Bot t h) :=
  IsOrthDecomp.of_add (isEquivPair_top h ht hadj).idem_right
    (isEquivPair_bot h ht hadj).idem_right
    (b1Left_mul_b0Top_add_b1Right_mul_b0Bot h ht hadj)
    (by rw [mul_assoc, b0Top_mul_e]) (by rw [mul_assoc, b0Bot_mul_e])

/-- **KL I, Proposition 2.13, case `i · j = -1`** (idempotent form, in a context `…` of
divided-power blocks `bs` away from the positions `j, j + 1, j + 2`; `F = blocksElt bs`,
`t = …iji…`, `s_{j+1} t = …iij…`, `s_j t = …jii…`):

* `1_{…iji…} = F f₁ + F f₂` is an orthogonal decomposition into idempotents, where
  `f₁ = B₁[left] B₀[top] = -ψ_{j+1} ψ_j ψ_{j+1} 1_{…iji…}` and
  `f₂ = B₁[right] B₀[bottom] = ψ_j ψ_{j+1} ψ_j 1_{…iji…}`;
* `1_{…i⁽²⁾j…} ~ F f₁` via `(F B₀[top], F B₁[left])` and `1_{…ji⁽²⁾…} ~ F f₂` via
  `(F B₀[bottom], F B₁[right])`. -/
theorem prop213_neg_one (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    IsOrthDecomp (divIdem t bs : A) (blocksElt bs * (b1Left t h * b0Top t h))
        (blocksElt bs * (b1Right t h * b0Bot t h)) ∧
      IsEquivPair (blocksElt bs * b0Top t h : A) (blocksElt bs * b1Left t h)
        (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs)) (blocksElt bs * (b1Left t h * b0Top t h)) ∧
      IsEquivPair (blocksElt bs * b0Bot t h : A) (blocksElt bs * b1Right t h)
        (divIdem (sadj m j • t) ((j + 1, 2) :: bs))
        (blocksElt bs * (b1Right t h * b0Bot t h)) := by
  have hbu : IsBlocks (sadj m (j + 1) • t) bs :=
    hb.sadj fun b hb => by have := hbs b hb; omega
  have hbv : IsBlocks (sadj m j • t) bs := hb.sadj fun b hb => by have := hbs b hb; omega
  obtain ⟨hx, hψ⟩ := commute_blocksElt_of_avoid Γ (ν := ν) (k := k) (d := 3) hbs
  have hx0 := hx ⟨j, by omega⟩ le_rfl (by simp only; omega)
  have hx1 := hx ⟨j + 1, by omega⟩ (by simp only; omega) (by simp only; omega)
  have hψ0 := hψ j le_rfl (by omega)
  have hψ1 := hψ (j + 1) (by omega) (by omega)
  have het : Commute (blocksElt bs : A) (e t) := blocksElt_mul_e hb.const
  have heu : Commute (blocksElt bs : A) (e (sadj m (j + 1) • t)) := blocksElt_mul_e hbu.const
  have hev : Commute (blocksElt bs : A) (e (sadj m j • t)) := blocksElt_mul_e hbv.const
  have hTop : Commute (blocksElt bs : A) (b0Top t h) :=
    ((hx0.mul_right hψ0).mul_right heu).mul_right hψ1
  have hBot : Commute (blocksElt bs : A) (b0Bot t h) :=
    ((hx1.mul_right hψ1).mul_right hev).mul_right hψ0
  have hLeft : Commute (blocksElt bs : A) (b1Left t h) :=
    ((hψ1.mul_right hψ0).mul_right ((hx0.mul_right hψ0).mul_right heu)).neg_right
  have hRight : Commute (blocksElt bs : A) (b1Right t h) :=
    (hψ0.mul_right hψ1).mul_right ((hx1.mul_right hψ1).mul_right hev)
  have hf₁ : blocksElt bs * blocksElt bs * (b1Left t h * b0Top t h) =
      (blocksElt bs * (b1Left t h * b0Top t h) : A) := by
    rw [b1Left_mul_b0Top h ht, ← neg_mul]
    exact blocksElt_sq_mul_of_commute hb (((hψ1.mul_right hψ0).mul_right hψ1).neg_right)
  have hf₂ : blocksElt bs * blocksElt bs * (b1Right t h * b0Bot t h) =
      (blocksElt bs * (b1Right t h * b0Bot t h) : A) := by
    rw [b1Right_mul_b0Bot h ht]
    exact blocksElt_sq_mul_of_commute hb ((hψ0.mul_right hψ1).mul_right hψ0)
  have hI2J : (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs) : A) =
      blocksElt bs * idemI2J t h := by
    rw [divIdem, blocksElt_cons, blockElt_two (show j + 1 < m by omega), idemI2J,
      ← (hx0.mul_right hψ0).eq]
    simp only [mul_assoc]
  have hJI2 : (divIdem (sadj m j • t) ((j + 1, 2) :: bs) : A) =
      blocksElt bs * idemJI2 t h := by
    rw [divIdem, blocksElt_cons, blockElt_two (show j + 1 + 1 < m by omega), idemJI2,
      ← (hx1.mul_right hψ1).eq]
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · exact (isOrthDecomp_local h ht hadj).mul_of_commute'
      (by rw [b1Left_mul_b0Top h ht, ← neg_mul] at hf₁ ⊢; exact hf₁) hf₂
      (hLeft.mul_right hTop) (hRight.mul_right hBot)
  · rw [hI2J]
    exact (isEquivPair_top h ht hadj).mul_of_commute'
      (blocksElt_sq_mul_of_commute hbu (hx0.mul_right hψ0)) hf₁ hTop hLeft
  · rw [hJI2]
    exact (isEquivPair_bot h ht hadj).mul_of_commute'
      (blocksElt_sq_mul_of_commute hbv (hx1.mul_right hψ1)) hf₂ hBot hRight

/-- **KL I, Proposition 2.13, case `i · j = -1`**, existential form: `1_{…iji…}` is the sum of
two orthogonal idempotents equivalent to `1_{…i⁽²⁾j…}` and `1_{…ji⁽²⁾…}`. -/
theorem prop213_neg_one' (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    ∃ f₁ f₂ : A, IsOrthDecomp (divIdem t bs) f₁ f₂ ∧
      IdemEquiv (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs)) f₁ ∧
      IdemEquiv (divIdem (sadj m j • t) ((j + 1, 2) :: bs)) f₂ :=
  have H := prop213_neg_one hb h ht hadj hbs
  ⟨_, _, H.1, ⟨_, _, H.2.1⟩, ⟨_, _, H.2.2⟩⟩

/-- **KL I, Proposition 2.13, case `i · j = -1`, left version**: applying the antiinvolution
`ψ`, `ψ(1_{…iji…})` is the sum of two orthogonal idempotents equivalent to `ψ(1_{…i⁽²⁾j…})`
and `ψ(1_{…ji⁽²⁾…})`. -/
theorem prop213_neg_one_hflip (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    ∃ f₁ f₂ : A, IsOrthDecomp (hflip (divIdem t bs : A)) f₁ f₂ ∧
      IdemEquiv (hflip (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs) : A)) f₁ ∧
      IdemEquiv (hflip (divIdem (sadj m j • t) ((j + 1, 2) :: bs) : A)) f₂ :=
  have H := prop213_neg_one hb h ht hadj hbs
  ⟨_, _, H.1.map_anti (AddMonoidHom.mk' hflip hflip_add) hflip_mul,
    ⟨_, _, H.2.1.map_anti hflip hflip_mul⟩, ⟨_, _, H.2.2.map_anti hflip hflip_mul⟩⟩

end negOne


/-! ### Projective modules and Corollary 2.14 -/

section modules

variable {t : Seq ν} {bs : List (ℕ × ℕ)} {j : ℕ}

/-- The antiinvolution `ψ` (`hflip`) as an additive map. -/
noncomputable def hflipAdd : A →+ A := AddMonoidHom.mk' hflip hflip_add

/-- **KL I, Proposition 2.13** (`i · j = 0`, right projectives, ungraded):
`₍…ij…₎P ≅ ₍…ji…₎P`, i.e. `1_{…ij…} R(ν) ≅ 1_{…ji…} R(ν)` as right `R(ν)`-modules. -/
noncomputable def prop213_zero_rIdealEquiv (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    rIdeal (divIdem t bs : A) ≃ₗ[Aᵐᵒᵖ] rIdeal (divIdem (sadj m j • t) bs : A) :=
  (prop213_zero hb h hne hadj hbs).rIdealEquiv

/-- **KL I, Proposition 2.13** (`i · j = 0`, left projectives, ungraded):
`P_{…ij…} ≅ P_{…ji…}`, i.e. `R(ν) ψ(1_{…ij…}) ≅ R(ν) ψ(1_{…ji…})`. -/
noncomputable def prop213_zero_lIdealEquiv (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    lIdeal (hflip (divIdem t bs : A)) ≃ₗ[A] lIdeal (hflip (divIdem (sadj m j • t) bs : A)) :=
  ((prop213_zero hb h hne hadj hbs).map_anti hflip hflip_mul).lIdealEquiv

/-- **KL I, Corollary 2.14** (`i · j = 0`, ungraded): `1_{…ij…} M ≅ 1_{…ji…} M` for every
left `R(ν)`-module `M`. -/
noncomputable def cor214_zero (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    fixSub k M (divIdem t bs : A) ≃ₗ[k] fixSub k M (divIdem (sadj m j • t) bs : A) :=
  (prop213_zero hb h hne hadj hbs).fixSubEquiv

/-- **KL I, Proposition 2.13** (`i · j = -1`, right projectives, ungraded):
`₍…iji…₎P ≅ ₍…i⁽²⁾j…₎P ⊕ ₍…ji⁽²⁾…₎P`, i.e.
`1_{…iji…} R(ν) ≅ 1_{…i⁽²⁾j…} R(ν) ⊕ 1_{…ji⁽²⁾…} R(ν)`; the map is left multiplication by
the column `B₀`. -/
noncomputable def prop213_neg_one_rIdealEquiv (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    rIdeal (divIdem t bs : A) ≃ₗ[Aᵐᵒᵖ]
      rIdeal (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs) : A) ×
        rIdeal (divIdem (sadj m j • t) ((j + 1, 2) :: bs) : A) :=
  have H := prop213_neg_one hb h ht hadj hbs
  H.1.rIdealEquivProd.trans (LinearEquiv.prodCongr H.2.1.symm.rIdealEquiv H.2.2.symm.rIdealEquiv)

/-- **KL I, Proposition 2.13** (`i · j = -1`, left projectives, ungraded):
`P_{…iji…} ≅ P_{…i⁽²⁾j…} ⊕ P_{…ji⁽²⁾…}` with `P_i = R(ν) ψ(1_i)`. -/
noncomputable def prop213_neg_one_lIdealEquiv (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    lIdeal (hflip (divIdem t bs : A)) ≃ₗ[A]
      lIdeal (hflip (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs) : A)) ×
        lIdeal (hflip (divIdem (sadj m j • t) ((j + 1, 2) :: bs) : A)) :=
  have H := prop213_neg_one hb h ht hadj hbs
  (H.1.map_anti hflipAdd hflip_mul).lIdealEquivProd.trans
    (LinearEquiv.prodCongr (H.2.1.map_anti hflip hflip_mul).symm.lIdealEquiv
      (H.2.2.map_anti hflip hflip_mul).symm.lIdealEquiv)

/-- **KL I, Corollary 2.14** (`i · j = -1`, ungraded):
`1_{…iji…} M ≅ 1_{…i⁽²⁾j…} M ⊕ 1_{…ji⁽²⁾…} M` for every left `R(ν)`-module `M`
(the paper's grading shift `{1}` is accounted for by the degrees in `prop213_degrees`). -/
noncomputable def cor214_neg_one (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    fixSub k M (divIdem t bs : A) ≃ₗ[k]
      fixSub k M (divIdem (sadj m (j + 1) • t) ((j, 2) :: bs) : A) ×
        fixSub k M (divIdem (sadj m j • t) ((j + 1, 2) :: bs) : A) :=
  have H := prop213_neg_one hb h ht hadj hbs
  H.1.fixSubEquivProd.trans (LinearEquiv.prodCongr H.2.1.symm.fixSubEquiv H.2.2.symm.fixSubEquiv)

end modules


/-! ### Degrees (KL I grading) -/

section degrees

variable {t : Seq ν} {bs : List (ℕ × ℕ)} {j : ℕ}

theorem cartan_of_adj {a b : I} (hab : Γ.Adj a b) : cartan Γ a b = -1 := by
  rw [cartan, if_neg (Γ.ne_of_adj hab), if_pos hab]

theorem cartan_of_not_adj {a b : I} (hne : a ≠ b) (hab : ¬ Γ.Adj a b) : cartan Γ a b = 0 := by
  rw [cartan, if_neg hne, if_neg hab]

theorem x_mul_e_mem_grade_two (a : Fin m) (s : Seq ν) : (x a * e s : A) ∈
    (klGradingDatum k Γ).grade ν 2 :=
  kl_x_mul_e_mem_grade a s

theorem ψ_mul_e_mem_grade_of_eq {l : ℕ} (hl : l + 1 < m) {s : Seq ν}
    (hs : s.lbl ⟨l, by omega⟩ = s.lbl ⟨l + 1, hl⟩) :
    (ψ l * e s : A) ∈ (klGradingDatum k Γ).grade ν (-2) := by
  have := kl_ψ_mul_e_mem_grade (k := k) (Γ := Γ) hl s
  rwa [hs, cartan_self] at this

theorem ψ_mul_e_mem_grade_of_adj {l : ℕ} (hl : l + 1 < m) {s : Seq ν}
    (hs : Γ.Adj (s.lbl ⟨l, by omega⟩) (s.lbl ⟨l + 1, hl⟩)) :
    (ψ l * e s : A) ∈ (klGradingDatum k Γ).grade ν 1 := by
  have := kl_ψ_mul_e_mem_grade (k := k) (Γ := Γ) hl s
  rwa [cartan_of_adj hs, neg_neg] at this

/-- The crossing of non-adjacent labels has degree `0` (KL I, case `i · j = 0`). -/
theorem ψ_mul_e_mem_grade_of_not_adj {l : ℕ} (hl : l + 1 < m) {s : Seq ν}
    (hne : s.lbl ⟨l, by omega⟩ ≠ s.lbl ⟨l + 1, hl⟩)
    (hs : ¬ Γ.Adj (s.lbl ⟨l, by omega⟩) (s.lbl ⟨l + 1, hl⟩)) :
    (ψ l * e s : A) ∈ (klGradingDatum k Γ).grade ν 0 := by
  have := kl_ψ_mul_e_mem_grade (k := k) (Γ := Γ) hl s
  rwa [cartan_of_not_adj hne hs, neg_zero] at this

omit [DecidableEq I] in
theorem sadj_smul_u (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    sadj m j • sadj m (j + 1) • t = sadj m (j + 1) • t :=
  sadj_smul_eq_self (by omega) (lblU_eq h ht)

omit [DecidableEq I] in
theorem sadj_smul_v (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩) :
    sadj m (j + 1) • sadj m j • t = sadj m j • t :=
  sadj_smul_eq_self (by omega) (lblV_eq h ht)

/-- The entries of the matrices `B₀`, `B₁` of KL I, proof of Proposition 2.13, are homogeneous:
`B₀` of degree `1` and `B₁` of degree `-1` (so that `B₀`, `B₁` are grading preserving
between the shifted projectives, `⟨…i⁽²⁾j…⟩ - ⟨…iji…⟩ = 1`). -/
theorem prop213_degrees (h : j + 2 < m) (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩)) :
    (b0Top t h : A) ∈ (klGradingDatum k Γ).grade ν 1 ∧
      (b0Bot t h : A) ∈ (klGradingDatum k Γ).grade ν 1 ∧
      (b1Left t h : A) ∈ (klGradingDatum k Γ).grade ν (-1) ∧
      (b1Right t h : A) ∈ (klGradingDatum k Γ).grade ν (-1) := by
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  have hu := lblU_eq h ht
  have hua := lblU_adj h ht hadj
  have hv := lblV_eq h ht
  have hva := lblV_adj h hadj
  have hta : Γ.Adj (t.lbl ⟨j + 1, h1⟩) (t.lbl ⟨j + 1 + 1, h2⟩) := by
    have : t.lbl ⟨j + 1 + 1, h2⟩ = t.lbl ⟨j, by omega⟩ := ht.symm
    rw [this]; exact hadj.symm
  have hsu := sadj_smul_u h ht
  have hsv := sadj_smul_v h ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := SetLike.mul_mem_graded (SetLike.mul_mem_graded
      (x_mul_e_mem_grade_two (k := k) (Γ := Γ) ⟨j, by omega⟩ (sadj m (j + 1) • t))
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h1 hu))
      (ψ_mul_e_mem_grade_of_adj (k := k) (Γ := Γ) h2 hta)
    convert this using 2
    simp only [b0Top, idemI2J, ← mul_assoc, mul_e_mul_x, mul_e_mul_ψ, mul_e_mul_e, sadj_smul_smul,
      hsu]
  · have := SetLike.mul_mem_graded (SetLike.mul_mem_graded
      (x_mul_e_mem_grade_two (k := k) (Γ := Γ) ⟨j + 1, by omega⟩ (sadj m j • t))
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h2 hv))
      (ψ_mul_e_mem_grade_of_adj (k := k) (Γ := Γ) h1 hadj)
    convert this using 2
    simp only [b0Bot, idemJI2, ← mul_assoc, mul_e_mul_x, mul_e_mul_ψ, mul_e_mul_e, sadj_smul_smul,
      hsv]
  · have := SetLike.mul_mem_graded (SetLike.mul_mem_graded (SetLike.mul_mem_graded
      (ψ_mul_e_mem_grade_of_adj (k := k) (Γ := Γ) h2 hua)
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h1 hu))
      (x_mul_e_mem_grade_two (k := k) (Γ := Γ) ⟨j, by omega⟩ (sadj m (j + 1) • t)))
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h1 hu)
    rw [b1Left, show (-1 : ℤ) = 1 + -2 + 2 + -2 by norm_num]
    refine Submodule.neg_mem _ ?_
    convert this using 1
    simp only [idemI2J, ← mul_assoc, mul_e_mul_x, mul_e_mul_ψ, mul_e_mul_e, hsu]
  · have := SetLike.mul_mem_graded (SetLike.mul_mem_graded (SetLike.mul_mem_graded
      (ψ_mul_e_mem_grade_of_adj (k := k) (Γ := Γ) h1 hva)
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h2 hv))
      (x_mul_e_mem_grade_two (k := k) (Γ := Γ) ⟨j + 1, by omega⟩ (sadj m j • t)))
      (ψ_mul_e_mem_grade_of_eq (k := k) (Γ := Γ) h2 hv)
    rw [b1Right, show (-1 : ℤ) = 1 + -2 + 2 + -2 by norm_num]
    convert this using 1
    simp only [idemJI2, ← mul_assoc, mul_e_mul_x, mul_e_mul_ψ, mul_e_mul_e, hsv]

/-- The entries of `B₀`, `B₁` in the context `F` of divided-power blocks keep their degrees:
`F B₀[·]` has degree `1` and `F B₁[·]` has degree `-1`. -/
theorem prop213_neg_one_degrees (hb : IsBlocks t bs) (h : j + 2 < m)
    (ht : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 2, h⟩)
    (hadj : Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, by omega⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 3 ≤ b.1) :
    (blocksElt bs * b0Top t h : A) ∈ (klGradingDatum k Γ).grade ν 1 ∧
      (blocksElt bs * b0Bot t h : A) ∈ (klGradingDatum k Γ).grade ν 1 ∧
      (blocksElt bs * b1Left t h : A) ∈ (klGradingDatum k Γ).grade ν (-1) ∧
      (blocksElt bs * b1Right t h : A) ∈ (klGradingDatum k Γ).grade ν (-1) := by
  have hbu : IsBlocks (sadj m (j + 1) • t) bs :=
    hb.sadj fun b hb => by have := hbs b hb; omega
  have hbv : IsBlocks (sadj m j • t) bs := hb.sadj fun b hb => by have := hbs b hb; omega
  have hsu := sadj_smul_u h ht
  have hsv := sadj_smul_v h ht
  obtain ⟨d1, d2, d3, d4⟩ := prop213_degrees (k := k) h ht hadj
  have key : ∀ {s : Seq ν} {y : A} {d : ℤ}, IsBlocks s bs → e s * y = y →
      y ∈ (klGradingDatum k Γ).grade ν d → blocksElt bs * y ∈ (klGradingDatum k Γ).grade ν d :=
    fun {s y d} hs hy hd => by
      rw [← hy, ← mul_assoc, ← zero_add d]
      exact SetLike.mul_mem_graded (divIdem_mem_grade _ hs) hd
  refine ⟨key hbu ?_ d1, key hbv ?_ d2, key hb ?_ d3, key hb ?_ d4⟩
  · simp only [b0Top, idemI2J, ← mul_assoc, e_mul_x, e_mul_ψ, mul_e_mul_x, mul_e_mul_ψ,
      mul_e_mul_e, sadj_smul_smul, hsu]
  · simp only [b0Bot, idemJI2, ← mul_assoc, e_mul_x, e_mul_ψ, mul_e_mul_x, mul_e_mul_ψ,
      mul_e_mul_e, sadj_smul_smul, hsv]
  · simp only [b1Left, idemI2J, mul_neg, ← mul_assoc, e_mul_x, e_mul_ψ, mul_e_mul_x,
      mul_e_mul_ψ, mul_e_mul_e, sadj_smul_smul, hsu]
  · simp only [b1Right, idemJI2, ← mul_assoc, e_mul_x, e_mul_ψ, mul_e_mul_x, mul_e_mul_ψ,
      mul_e_mul_e, sadj_smul_smul, hsv]

/-- In the case `i · j = 0` the crossings `F ψ_j 1_{…ji…}` and `F ψ_j 1_{…ij…}` of
`prop213_zero` have degree `0`. -/
theorem prop213_zero_degrees (hb : IsBlocks t bs) (h : j + 1 < m)
    (hne : t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j + 1, h⟩)
    (hadj : ¬ Γ.Adj (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))
    (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ j ∨ j + 2 ≤ b.1) :
    (blocksElt bs * (ψ j * e (sadj m j • t)) : A) ∈ (klGradingDatum k Γ).grade ν 0 ∧
      (blocksElt bs * (ψ j * e t) : A) ∈ (klGradingDatum k Γ).grade ν 0 := by
  have hb' : IsBlocks (sadj m j • t) bs := hb.sadj fun b hb => by have := hbs b hb; omega
  have hne' : (sadj m j • t).lbl ⟨j, by omega⟩ ≠ (sadj m j • t).lbl ⟨j + 1, h⟩ := by
    rw [lbl_sadj_left h, lbl_sadj_right h]; exact Ne.symm hne
  have hadj' : ¬ Γ.Adj ((sadj m j • t).lbl ⟨j, by omega⟩) ((sadj m j • t).lbl ⟨j + 1, h⟩) := by
    rw [lbl_sadj_left h, lbl_sadj_right h]; exact fun h' => hadj h'.symm
  constructor
  · have hy : (e t * (ψ j * e (sadj m j • t)) : A) = ψ j * e (sadj m j • t) := by
      rw [← mul_assoc, e_mul_ψ, mul_assoc, e_mul_self]
    rw [← hy, ← mul_assoc, ← zero_add (0 : ℤ)]
    exact SetLike.mul_mem_graded (divIdem_mem_grade _ hb)
      (ψ_mul_e_mem_grade_of_not_adj h hne' hadj')
  · have hy : (e (sadj m j • t) * (ψ j * e t) : A) = ψ j * e t := by
      rw [← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, e_mul_self]
    rw [← hy, ← mul_assoc, ← zero_add (0 : ℤ)]
    exact SetLike.mul_mem_graded (divIdem_mem_grade _ hb')
      (ψ_mul_e_mem_grade_of_not_adj h hne hadj)

end degrees

end KL

end Categorification.KLR.KLRAlgebra
