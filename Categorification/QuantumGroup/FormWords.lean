/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Form
import Categorification.TypeA.Inversions

/-!
# Lusztig's form on words: a closed formula

Lusztig, *Introduction to quantum groups*, §1.2.3 (the form) and §1.2.13 (the maps `r_i`); used
in Khovanov–Lauda I (arXiv:0803.4121v2), §3.1, proof of Proposition 3.4, where the form on
`'f` is compared with the form `gdim (1_j R(ν) 1_i)` on `K₀(R)` (KL I §2.5).

For tuples `a, b : Fin m → I` write `θ_a = θ_{a_0} ⋯ θ_{a_{m-1}}` (`PreF.wordFn`). We prove

`(θ_a, θ_b) = (∏_x c_{a_x}) · ∑_{w ∈ S_m, b ∘ w = a} v^{∑_{(x, y) ∈ inv(w)} a_y · a_x}`

(`PreF.form_wordFn`), where `inv(w) = {(x, y) | x < y, w y < w x}` (`TypeA.invSet`) and
`c_i = (θ_i, θ_i)`. No hypothesis on the pairing `dot` is needed (for a symmetric pairing the
exponent is the usual `∑_{inv(w)} a_x · a_y`).

The proof is by induction on `m`, using the recursion `(θ_i x, y) = c_i (x, d_i y)` defining the
form (`PreF.form_θ_mul`) and the explicit formula for the twisted derivation on words
(`PreF.d_wordFn`):

`d_i(θ_b) = ∑_{p : b_p = i} v^{∑_{r < p} b_r · i} θ_{b_0} ⋯ \widehat{θ_{b_p}} ⋯ θ_{b_{m}}`.

On the permutation side, `S_{m+1} ≅ Fin (m+1) × S_m` via `PreF.consPerm`
(`w 0 = p`, `w (x + 1) = p.succAbove (τ x)`), under which the inversions of `w` are those of `τ`
together with the pairs `(0, y + 1)` with `τ y < p` (`PreF.invWt_consPerm`).

## Main results

* `PreF.wordFn`, `PreF.wordFn_succ`.
* `PreF.d_wordFn` — the twisted derivation `d_i` on a word.
* `PreF.invWt`, `PreF.permSum` — the inversion weight and the permutation sum.
* `PreF.consPerm`, `PreF.consPerm_bijective`, `PreF.invWt_consPerm`, `PreF.permSum_succ`.
* `PreF.form_wordFn` — **the closed formula for `(θ_a, θ_b)`**.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Equiv TypeA Finset
open scoped Classical

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K]

/-! ### Words given by tuples -/

/-- The word `θ_{a_0} θ_{a_1} ⋯ θ_{a_{m-1}} ∈ 'f` of a tuple `a : Fin m → I`. -/
def wordFn {m : ℕ} (a : Fin m → I) : PreF K I := word (FreeMonoid.ofList (List.ofFn a))

theorem wordFn_zero (a : Fin 0 → I) : (wordFn a : PreF K I) = 1 := by
  simp [wordFn]

theorem wordFn_succ {m : ℕ} (a : Fin (m + 1) → I) :
    (wordFn a : PreF K I) = θ (a 0) * wordFn (fun x => a x.succ) := by
  rw [wordFn, List.ofFn_succ, FreeMonoid.ofList_cons, word_of_mul]
  rfl

/-! ### The twisted derivation on a word -/

theorem sum_filter_lt_succ {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 2) → M)
    (p : Fin (m + 1)) :
    ∑ r ∈ univ.filter (· < p.succ), f r = f 0 + ∑ r ∈ univ.filter (· < p), f r.succ := by
  rw [sum_filter, sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff]

theorem sum_filter_lt_zero {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 1) → M) :
    ∑ r ∈ univ.filter (· < (0 : Fin (m + 1))), f r = 0 := by
  rw [sum_filter]
  simp [Fin.not_lt_zero]

variable (dot : I → I → ℤ) (v : Kˣ)

/-- **The twisted derivation `d_i` on a word** (compare Lusztig 1.2.13):
`d_i(θ_{b_0} ⋯ θ_{b_m}) = ∑_{p : b_p = i} v^{∑_{r < p} b_r · i} θ_{b_0} ⋯ \widehat{θ_{b_p}} ⋯ θ_{b_m}`. -/
theorem d_wordFn (i : I) {m : ℕ} (b : Fin (m + 1) → I) :
    d dot v i (wordFn b : PreF K I) = ∑ p : Fin (m + 1),
      if b p = i then
        ((v ^ (∑ r ∈ univ.filter (· < p), dot (b r) i) : Kˣ) : K) •
          wordFn (fun x => b (p.succAbove x))
      else 0 := by
  induction m with
  | zero =>
    rw [wordFn_succ, wordFn_zero, mul_one, d_θ, Fin.sum_univ_one, sum_filter_lt_zero, zpow_zero,
      Units.val_one, one_smul, wordFn_zero]
  | succ m ih =>
    rw [wordFn_succ, d_θ_mul, ih, Fin.sum_univ_succ (n := m + 1), sum_filter_lt_zero, zpow_zero,
      Units.val_one, one_smul, Fin.succAbove_zero, Finset.mul_sum, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_filter_lt_succ, zpow_add, Units.val_mul]
    have hw : (wordFn (fun x => b (p.succ.succAbove x)) : PreF K I) =
        θ (b 0) * wordFn (fun x => b (p.succAbove x).succ) := by
      rw [wordFn_succ, Fin.succ_succAbove_zero]
      simp only [Fin.succ_succAbove_succ]
    split_ifs
    · rw [hw, mul_smul_comm, smul_smul]
    · simp

/-! ### Inversion weights and the permutation sum -/

/-- The inversion weight `∑_{(x, y) ∈ inv(w)} a_y · a_x` of a permutation `w` on the tuple `a`. -/
def invWt {m : ℕ} (a : Fin m → I) (w : Perm (Fin m)) : ℤ :=
  ∑ p ∈ invSet m w, dot (a p.2) (a p.1)

/-- The permutation sum `∑_{w ∈ S_m, b ∘ w = a} v^{invWt a w}`. -/
def permSum {m : ℕ} (a b : Fin m → I) : K :=
  ∑ w : Perm (Fin m), if ∀ x, b (w x) = a x then ((v ^ invWt dot a w : Kˣ) : K) else 0

/-- The permutation of `Fin (m + 1)` with `0 ↦ p` and `x + 1 ↦ p.succAbove (τ x)`. -/
def consPerm {m : ℕ} (p : Fin (m + 1)) (τ : Perm (Fin m)) : Perm (Fin (m + 1)) :=
  ((finSuccEquiv m).trans (Equiv.optionCongr τ)).trans (finSuccEquiv' p).symm

@[simp] theorem consPerm_zero {m : ℕ} (p : Fin (m + 1)) (τ : Perm (Fin m)) :
    consPerm p τ 0 = p := by
  simp [consPerm, finSuccEquiv_zero, finSuccEquiv'_symm_none]

@[simp] theorem consPerm_succ {m : ℕ} (p : Fin (m + 1)) (τ : Perm (Fin m)) (x : Fin m) :
    consPerm p τ x.succ = p.succAbove (τ x) := by
  simp [consPerm, finSuccEquiv_succ, finSuccEquiv'_symm_some]

/-- `(p, τ) ↦ consPerm p τ` is a bijection `Fin (m + 1) × S_m ≅ S_{m+1}`. -/
theorem consPerm_bijective (m : ℕ) :
    Function.Bijective (fun q : Fin (m + 1) × Perm (Fin m) => consPerm q.1 q.2) := by
  constructor
  · rintro ⟨p, τ⟩ ⟨p', τ'⟩ h
    have h0 := DFunLike.congr_fun h 0
    simp only [consPerm_zero] at h0
    subst h0
    refine Prod.ext rfl (Equiv.ext fun x => ?_)
    have hx := DFunLike.congr_fun h x.succ
    simp only [consPerm_succ] at hx
    exact Fin.succAbove_right_injective hx
  · intro w
    let e : Option (Fin m) ≃ Option (Fin m) :=
      ((finSuccEquiv m).symm.trans w).trans (finSuccEquiv' (w 0))
    refine ⟨(w 0, Equiv.removeNone e), ?_⟩
    refine Equiv.ext fun x => ?_
    refine Fin.cases ?_ (fun x => ?_) x
    · exact consPerm_zero _ _
    · simp only [consPerm_succ]
      have hne : w x.succ ≠ w 0 := fun h => Fin.succ_ne_zero x (w.injective h)
      have hsome : ∃ x', e (some x) = some x' := by
        refine Option.ne_none_iff_exists'.1 ?_
        simp only [e, Equiv.trans_apply, finSuccEquiv_symm_some]
        rw [Ne, finSuccEquiv'_eq_none]
        exact fun h => hne h.symm
      have h := Equiv.removeNone_some e hsome
      have h' := congrArg (finSuccEquiv' (w 0)).symm h
      rw [finSuccEquiv'_symm_some] at h'
      rw [h']
      simp [e, finSuccEquiv_symm_some]

/-- The inversions of `consPerm p τ`: those of `τ` (shifted), and the pairs `(0, y + 1)` with
`τ y < p`. -/
theorem invWt_consPerm {m : ℕ} (a : Fin (m + 1) → I) (p : Fin (m + 1)) (τ : Perm (Fin m)) :
    invWt dot a (consPerm p τ) =
      (∑ y ∈ univ.filter (fun y => (τ y).castSucc < p), dot (a y.succ) (a 0)) +
        invWt dot (fun x => a x.succ) τ := by
  simp only [invWt, invSet, sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ, consPerm_zero,
    consPerm_succ, lt_self_iff_false, false_and, if_false, Fin.not_lt_zero, Fin.succ_pos,
    true_and, Fin.succAbove_lt_iff_castSucc_lt, Fin.succ_lt_succ_iff,
    Fin.succAbove_lt_succAbove_iff, zero_add]

/-- On the tuples `a` with `b ∘ consPerm p τ = a`, the inversion pairs `(0, y + 1)` contribute
`∑_{r < p} b_r · a_0`. -/
theorem sum_filter_castSucc_lt {m : ℕ} (a b : Fin (m + 1) → I) (p : Fin (m + 1))
    (τ : Perm (Fin m)) (h : ∀ x, b (p.succAbove (τ x)) = a x.succ) :
    ∑ y ∈ univ.filter (fun y => (τ y).castSucc < p), dot (a y.succ) (a 0) =
      ∑ r ∈ univ.filter (· < p), dot (b r) (a 0) := by
  rw [sum_filter, sum_filter]
  have e1 : ∀ y, (if (τ y).castSucc < p then dot (a y.succ) (a 0) else 0) =
      (fun s => if s.castSucc < p then dot (b s.castSucc) (a 0) else 0) (τ y) := by
    intro y
    simp only
    split_ifs with hy
    · rw [← h y, Fin.succAbove_of_castSucc_lt _ _ hy]
    · rfl
  rw [Fintype.sum_congr _ _ e1,
    Equiv.sum_comp τ (fun s => if s.castSucc < p then dot (b s.castSucc) (a 0) else 0),
    Fin.sum_univ_castSucc]
  have hl : ¬ Fin.last m < p := fun hl => absurd (Fin.le_last p) (not_le.2 hl)
  rw [if_neg hl, add_zero]

/-- **The recursion for the permutation sum**, peeling off the first letter of `a`:
`permSum a b = ∑_{p : b_p = a_0} v^{∑_{r < p} b_r · a_0} permSum (a ∘ succ) (b ∘ p.succAbove)`. -/
theorem permSum_succ {m : ℕ} (a b : Fin (m + 1) → I) :
    permSum dot v a b = ∑ p : Fin (m + 1),
      if b p = a 0 then
        ((v ^ (∑ r ∈ univ.filter (· < p), dot (b r) (a 0)) : Kˣ) : K) *
          permSum dot v (fun x => a x.succ) (fun x => b (p.succAbove x))
      else 0 := by
  rw [permSum, ← Fintype.sum_bijective _ (consPerm_bijective m) _ _ (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hcond : ∀ τ : Perm (Fin m), (∀ x, b (consPerm p τ x) = a x) ↔
      (b p = a 0 ∧ ∀ x, b (p.succAbove (τ x)) = a x.succ) := by
    intro τ
    rw [Fin.forall_fin_succ]
    simp only [consPerm_zero, consPerm_succ]
  by_cases hp : b p = a 0
  · rw [if_pos hp, permSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hτ : ∀ x, b (p.succAbove (τ x)) = a x.succ
    · rw [if_pos ((hcond τ).2 ⟨hp, hτ⟩), if_pos hτ, invWt_consPerm,
        sum_filter_castSucc_lt dot a b p τ hτ, zpow_add, Units.val_mul]
    · rw [if_neg (fun h => hτ ((hcond τ).1 h).2), if_neg hτ, mul_zero]
  · rw [if_neg hp]
    exact Finset.sum_eq_zero fun τ _ => if_neg (fun h => hp ((hcond τ).1 h).1)

theorem permSum_zero (a b : Fin 0 → I) : permSum dot v a b = (1 : K) := by
  rw [permSum, Fintype.sum_unique]
  simp [invWt, invSet]

/-! ### The closed formula -/

/-- **Lusztig's form on words**: for `a, b : Fin m → I`,
`(θ_a, θ_b) = (∏_x c_{a_x}) · ∑_{w ∈ S_m, b ∘ w = a} v^{∑_{(x, y) ∈ inv(w)} a_y · a_x}`. -/
theorem form_wordFn (c : I → K) {m : ℕ} (a b : Fin m → I) :
    form dot v c (wordFn a) (wordFn b) = (∏ x, c (a x)) * permSum dot v a b := by
  induction m with
  | zero => rw [wordFn_zero, wordFn_zero, form_one_one, permSum_zero, Fin.prod_univ_zero, one_mul]
  | succ m ih =>
    rw [wordFn_succ a, form_θ_mul, d_wordFn, map_sum, Finset.mul_sum, permSum_succ,
      Finset.mul_sum, Fin.prod_univ_succ]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rw [map_smul, smul_eq_mul, ih]
      ring
    · simp

end PreF

end Categorification.QuantumGroup

end
