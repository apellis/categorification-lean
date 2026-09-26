/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotNondeg
import Categorification.QuantumGroup.FormDivided

/-!
# KL III Proposition 2.5 in rank one, unconditionally

Khovanov–Lauda III, arXiv:0807.3250v1, Proposition 2.5, for a Cartan datum with a single
vertex (e.g. `U̇(sl₂)`). Here there are no Serre relations and the Gabber–Kac hypothesis of
`Categorification.QuantumGroup.UDotNondeg` holds because the form on `'f = K[θ]` is already
nondegenerate: `(θ^a, θ^b) = δ_{ab} ∏_{s=1}^a c (1 + v² + ⋯ + v^{2(s-1)})` (Lusztig 1.4.4,
`PreF.form_θ_pow_self`), which is nonzero when `q` is not a root of unity.

## Main results

* `UDot.radK_eq_bot` — the radical of the form on `'f` is zero when `I` is a subsingleton;
* **`UDot.KL3.formNondeg_rankOne`** — KL III Prop. 2.5 (for `( , )`, hence for `⟨ , ⟩` by
  `UDot.KL3.sform_nondeg`) over `ℚ(q)` for every root datum of rank one, with no hypothesis;
  in particular for `UDot.sl2RootDatum`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] {C : CartanDatum I} {q : Kˣ} {c : I → K}

theorem eq_of_wt_eq_of_subsingleton [Subsingleton I] {u w : FreeMonoid I} (h : wt u = wt w) :
    u = w := by
  have hl : (FreeMonoid.toList u).length = (FreeMonoid.toList w).length := by
    have := congrArg Multiset.card h
    simpa [wt] using this
  apply FreeMonoid.toList.injective
  exact List.ext_get hl fun n _ _ => Subsingleton.elim _ _

theorem word_replicate (i : I) (n : ℕ) :
    (word (FreeMonoid.ofList (List.replicate n i)) : PreF K I) = θ i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, FreeMonoid.ofList_cons, word_of_mul, ih, pow_succ']

theorem fF_word_self_ne_zero [Subsingleton I] (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (hc0 : ∀ i, c i ≠ 0) (w : FreeMonoid I) : fF C q c (word w) (word w) ≠ 0 := by
  cases hw : FreeMonoid.toList w with
  | nil =>
    have : w = 1 := FreeMonoid.toList.injective (by simpa using hw)
    rw [this, word_one, fF, form_one_one]
    exact one_ne_zero
  | cons i t =>
    have hw' : w = FreeMonoid.ofList (List.replicate (t.length + 1) i) := by
      apply FreeMonoid.toList.injective
      rw [FreeMonoid.toList_ofList, hw]
      exact List.ext_get (by simp) fun n _ _ => Subsingleton.elim _ _
    rw [hw', word_replicate, fF, form_θ_pow_self]
    refine Finset.prod_ne_zero_iff.2 fun s _ => mul_ne_zero (hc0 i) ?_
    set y : K := (((q⁻¹ : Kˣ) ^ C.dot i i : Kˣ) : K)
    have hk : ∀ k : ℕ, ((((q⁻¹ : Kˣ) ^ (C.dot i i * (k : ℤ)) : Kˣ)) : K) = y ^ k := by
      intro k
      rw [zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    have hpos := C.dot_self_pos i
    have hy1 : y ≠ 1 := by
      intro h
      have : ((q⁻¹ : Kˣ) ^ C.dot i i) = 1 := Units.ext h
      rw [inv_zpow'] at this
      exact zpow_ne_one_of_hq q hq (by omega) this
    simp only [hk]
    rw [geom_sum_eq hy1]
    refine div_ne_zero (sub_ne_zero.2 fun h => ?_) (sub_ne_zero.2 hy1)
    have : ((q⁻¹ : Kˣ) ^ (C.dot i i * ((s + 1 : ℕ) : ℤ))) = 1 := by
      ext; rw [hk]; exact h
    rw [inv_zpow'] at this
    exact zpow_ne_one_of_hq q hq (by push_cast; nlinarith) this

/-- In rank one the form on `'f` is nondegenerate: its radical is zero. -/
theorem radK_eq_bot [Subsingleton I] (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (hc0 : ∀ i, c i ≠ 0)
    {x : PreF K I} (hx : x ∈ radK C q c) : x = 0 := by
  ext w
  have hsum : x = ∑ u ∈ x.support, x u • (word u : PreF K I) := by
    conv_lhs => rw [← Finsupp.sum_single x]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact single_eq_smul_word u (x u)
  have key : fF C q c x (word w) = x w * fF C q c (word w) (word w) := by
    have e : fF C q c x (word w) = ∑ u ∈ x.support, x u * fF C q c (word u) (word w) := by
      conv_lhs => rw [hsum]
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e, Finset.sum_eq_single w (fun u _ huw => by
      rw [fF_word_eq_zero (fun h => huw (eq_of_wt_eq_of_subsingleton h)), mul_zero])
      (fun h => by rw [Finsupp.not_mem_support_iff.1 h, zero_mul])]
  have h0 : fF C q c x (word w) = 0 := (mem_radK.1 hx) _
  rw [key] at h0
  exact (mul_eq_zero.1 h0).resolve_right (fF_word_self_ne_zero hq hc0 w)

namespace KL3

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- **KL III Proposition 2.5 in rank one** (e.g. `U̇(sl₂)`), over `ℚ(q)`, with no hypothesis. -/
theorem formNondeg_rankOne [Subsingleton I] (RD : RootDatum C X Y) : FormNondeg RD := by
  refine formNondeg RD fun x hx => ?_
  rw [radK_eq_bot hqK (fun i => ?_) hx]
  · exact Submodule.zero_mem _
  · refine inv_ne_zero (sub_ne_zero.2 fun h => ?_)
    have hu : ((qi C qK i) ^ 2 : (RatFunc ℚ)ˣ) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, ← h, Units.val_one])
    rw [qi, ← zpow_natCast, ← zpow_mul] at hu
    exact zpow_ne_one_of_hq qK hqK (by have := di_pos C i; omega) hu

/-- KL III Proposition 2.5 for `U̇(sl₂)` over `ℚ(q)`, for both forms, unconditionally. -/
theorem prop_2_5_sl2 :
    FormNondeg sl2RootDatum ∧ ∀ x, (∀ y, sform sl2RootDatum x y = 0) → x = 0 :=
  ⟨formNondeg_rankOne sl2RootDatum, sform_nondeg (formNondeg_rankOne sl2RootDatum)⟩

end KL3

end UDot

end Categorification.QuantumGroup

end
