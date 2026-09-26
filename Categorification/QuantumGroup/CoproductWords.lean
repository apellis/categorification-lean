/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.PreF

/-!
# Lusztig's `r` on words: the shuffle formula

Lusztig, *Introduction to quantum groups*, §1.2.2; Khovanov–Lauda I (arXiv:0803.4121v2), §3.1
(the twisted multiplication (3.1) = `eq_quasi_commute`, and Proposition 3.2).

For a word `θ_{w_0} θ_{w_1} ⋯ θ_{w_{m-1}}` the algebra homomorphism
`r : 'f → 'f ⊗ 'f` (`PreF.r`, for the twisted multiplication
`(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂`) is the sum over all ways of splitting the word
into two complementary subwords. We encode such a splitting by a *mask* `b : Fin m → Bool`
(`b a = false`: the letter at position `a` goes to the left factor, `b a = true`: to the right
factor), so that

`r(θ_{w_0} ⋯ θ_{w_{m-1}}) = ∑_b v^{inv(w, b)} θ_{w|b=false} ⊗ θ_{w|b=true}`   (`PreF.r_ofFn`),

where `w|b=β` is the subword at the positions `a` with `b a = β` (`PreF.maskWord`) and
`inv(w, b) = ∑_{a < c, b a = true, b c = false} w_a · w_c` (`PreF.maskInv`) is the sum of the
pairings over the pairs of letters whose relative order is reversed by the splitting.

For concatenated words, masks of `w w'` are pairs of masks of `w` and `w'` (`Fin.append`), the
subwords concatenate (`PreF.maskWord_append`) and the exponent is additive up to the crossing of
the right part of the first word with the left part of the second (`PreF.maskInv_append`):

`inv(w w', b b') = inv(w, b) + inv(w', b') + |w|_{b=true}| · |w'|_{b'=false}|`.

These are the combinatorial facts behind KL I, Proposition 3.2 (see
`Categorification.KLR.Prop32Mult`).
-/

noncomputable section

namespace Categorification.QuantumGroup

open TwistedMonoidAlgebra (single single_mul_single)

variable {I : Type*}

namespace TwistedMonoidAlgebra

variable {K M : Type*} [CommRing K] [Monoid M]

/-- The identity of the underlying module `M →₀ K`, viewed as a linear map `K^σ[M] → K^{σ'}[M]`
between the twisted monoid algebras of two cocycles (used to compare twisted algebras whose
cocycles take the same values). -/
def recast (σ σ' : TwistCocycle K M) : TwistedMonoidAlgebra σ →ₗ[K] TwistedMonoidAlgebra σ' where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem recast_single (σ σ' : TwistCocycle K M) (m : M) (r : K) :
    recast σ σ' (single m r) = single m r := rfl

end TwistedMonoidAlgebra

namespace PreF

/-! ### Subwords and inversion pairings of a mask -/

section Mask

variable {m m' : ℕ}

/-- The subword `w|_{b = β}` of `w` at the positions `a` with `b a = β`, in increasing order. -/
def maskWord (w : Fin m → I) (b : Fin m → Bool) (β : Bool) : FreeMonoid I :=
  FreeMonoid.ofList (((List.finRange m).filter fun a => b a == β).map w)

/-- The exponent `inv(w, b) = ∑_{a < c, b a = true, b c = false} w_a · w_c`: the pairing summed
over the pairs of letters whose relative order is reversed when `w` is split by `b`. -/
def maskInv (dot : I → I → ℤ) (w : Fin m → I) (b : Fin m → Bool) : ℤ :=
  ∑ a, ∑ c, if a < c ∧ b a = true ∧ b c = false then dot (w a) (w c) else 0

theorem toList_maskWord (w : Fin m → I) (b : Fin m → Bool) (β : Bool) :
    FreeMonoid.toList (maskWord w b β) = ((List.finRange m).filter fun a => b a == β).map w :=
  rfl

private theorem sum_map_filter {α : Type*} (L : List α) (p : α → Bool) (f : α → ℤ) :
    ((L.filter p).map f).sum = (L.map fun c => if p c then f c else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : p a
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

/-- Sums over the letters of a subword. -/
theorem sum_map_wt_maskWord (w : Fin m → I) (b : Fin m → Bool) (β : Bool) (f : I → ℤ) :
    ((wt (maskWord w b β)).map f).sum = ∑ a, if b a = β then f (w a) else 0 := by
  rw [wt, toList_maskWord, Multiset.map_coe, Multiset.sum_coe, List.map_map, sum_map_filter,
    ← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem wdot_singleton_wt_maskWord (dot : I → I → ℤ) (x : I) (w : Fin m → I)
    (b : Fin m → Bool) (β : Bool) :
    wdot dot {x} (wt (maskWord w b β)) = ∑ a, if b a = β then dot x (w a) else 0 := by
  rw [wdot, Multiset.map_singleton, Multiset.sum_singleton, sum_map_wt_maskWord]

theorem wdot_wt_maskWord (dot : I → I → ℤ) (w : Fin m → I) (b : Fin m → Bool) (β : Bool)
    (w' : Fin m' → I) (b' : Fin m' → Bool) (β' : Bool) :
    wdot dot (wt (maskWord w b β)) (wt (maskWord w' b' β')) =
      ∑ a, ∑ c, if b a = β ∧ b' c = β' then dot (w a) (w' c) else 0 := by
  rw [wdot, sum_map_wt_maskWord]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_map_wt_maskWord]
  by_cases ha : b a = β
  · simp [ha]
  · simp [ha]

/-- The weight of a subword. -/
theorem wt_maskWord (w : Fin m → I) (b : Fin m → Bool) (β : Bool) :
    wt (maskWord w b β) = (Finset.univ.filter fun a => b a = β).val.map w := by
  rw [wt, toList_maskWord, Finset.filter_val, Fin.univ_def]
  simp only [Multiset.filter_coe, Multiset.map_coe, Multiset.coe_eq_coe]
  apply List.Perm.of_eq
  congr 2

theorem maskWord_cons (w : Fin (m + 1) → I) (β : Bool) (b : Fin m → Bool) (β' : Bool) :
    maskWord w (Fin.cons β b) β' =
      if β = β' then FreeMonoid.of (w 0) * maskWord (fun a => w a.succ) b β'
      else maskWord (fun a => w a.succ) b β' := by
  unfold maskWord
  rw [List.finRange_succ, List.filter_cons, List.filter_map]
  have hc : ((fun a => (Fin.cons β b : Fin (m + 1) → Bool) a == β') ∘ Fin.succ) =
      fun a => b a == β' := by
    funext a; simp
  rw [hc]
  by_cases h : β = β'
  · simp [h, List.map_map, Function.comp_def, FreeMonoid.ofList_cons]
  · simp [h, List.map_map, Function.comp_def]

theorem maskInv_cons (dot : I → I → ℤ) (w : Fin (m + 1) → I) (β : Bool) (b : Fin m → Bool) :
    maskInv dot w (Fin.cons β b) =
      (if β = true then wdot dot {w 0} (wt (maskWord (fun a => w a.succ) b false)) else 0) +
        maskInv dot (fun a => w a.succ) b := by
  rw [wdot_singleton_wt_maskWord]
  unfold maskInv
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.sum_univ_succ]
    simp only [lt_self_iff_false, false_and, if_false, zero_add, Fin.cons_zero, Fin.cons_succ,
      Fin.succ_pos, true_and]
    by_cases hβ : β = true
    · simp [hβ]
    · simp [hβ]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_lt_succ_iff]
    simp [Fin.not_lt_zero]

/-- Subwords of a concatenation. -/
theorem maskWord_append (w : Fin m → I) (w' : Fin m' → I) (b : Fin m → Bool)
    (b' : Fin m' → Bool) (β : Bool) :
    maskWord (Fin.append w w') (Fin.append b b') β = maskWord w b β * maskWord w' b' β := by
  unfold maskWord
  rw [← FreeMonoid.ofList_append]
  congr 1
  have hfr : List.finRange (m + m') =
      (List.finRange m).map (Fin.castAdd m') ++ (List.finRange m').map (Fin.natAdd m) := by
    rw [← List.ofFn_id, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
    rfl
  have e1 : ((fun a => Fin.append b b' a == β) ∘ Fin.castAdd m') = fun a => b a == β := by
    funext a; simp
  have e2 : ((fun a => Fin.append b b' a == β) ∘ Fin.natAdd m) = fun a => b' a == β := by
    funext a; simp
  rw [hfr, List.filter_append, List.map_append, List.filter_map, List.filter_map, e1, e2,
    List.map_map, List.map_map]
  congr 2
  · funext a; simp
  · funext a; simp

/-- Masks of a concatenation `w w'` are pairs of masks of `w` and `w'`: the splittings of `w w'`
into two subwords are the pairs of splittings of `w` and of `w'`. -/
def maskAppendEquiv : (Fin m → Bool) × (Fin m' → Bool) ≃ (Fin (m + m') → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun b := (fun a => b (Fin.castAdd m' a), fun c => b (Fin.natAdd m c))
  left_inv p := by ext a <;> simp
  right_inv b := Fin.append_castAdd_natAdd

@[simp] theorem maskAppendEquiv_apply (p : (Fin m → Bool) × (Fin m' → Bool)) :
    maskAppendEquiv p = Fin.append p.1 p.2 := rfl

/-- **The exponent of a concatenation**:
`inv(w w', b b') = inv(w, b) + inv(w', b') + |w|_{b=true}| · |w'|_{b'=false}|`. -/
theorem maskInv_append (dot : I → I → ℤ) (w : Fin m → I) (w' : Fin m' → I) (b : Fin m → Bool)
    (b' : Fin m' → Bool) :
    maskInv dot (Fin.append w w') (Fin.append b b') =
      maskInv dot w b + maskInv dot w' b' +
        wdot dot (wt (maskWord w b true)) (wt (maskWord w' b' false)) := by
  rw [wdot_wt_maskWord]
  unfold maskInv
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.sum_add_distrib]
  have h1 : ∀ (a : Fin m) (c : Fin m'), Fin.castAdd m' a < Fin.natAdd m c := fun a c => by
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]; omega
  have h2 : ∀ (a : Fin m') (c : Fin m), ¬ Fin.natAdd m a < Fin.castAdd m' c := fun a c => by
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]; omega
  have h3 : ∀ (a c : Fin m), Fin.castAdd m' a < Fin.castAdd m' c ↔ a < c := fun a c => by
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd]
  have h4 : ∀ (a c : Fin m'), Fin.natAdd m a < Fin.natAdd m c ↔ a < c := fun a c => by
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_natAdd]; omega
  simp only [h1, h2, h3, h4, true_and, false_and, if_false, Finset.sum_const_zero, add_zero]
  ring

end Mask

/-! ### The shuffle formula for `r` -/

section Shuffle

variable {K : Type*} [CommRing K] (dot : I → I → ℤ) (v : Kˣ)

/-- **Lusztig's `r` on a word** (Lusztig 1.2.2; KL I §3.1):
`r(θ_{w_0} ⋯ θ_{w_{m-1}}) = ∑_b v^{inv(w, b)} θ_{w|b=false} ⊗ θ_{w|b=true}`,
the sum over all masks `b : Fin m → Bool`, i.e. over all ways of writing the word as a shuffle of
two subwords. -/
theorem r_ofFn {m : ℕ} (w : Fin m → I) :
    r dot v (word (FreeMonoid.ofList (List.ofFn w)) : PreF K I) =
      ∑ b : Fin m → Bool,
        (single (maskWord w b false, maskWord w b true) ((v ^ maskInv dot w b : Kˣ) : K) :
          TwSq K I dot v) := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero, Fintype.sum_unique]
    have h1 : ∀ b : Fin 0 → Bool, maskInv dot w b = 0 := fun b => by simp [maskInv]
    have h2 : ∀ (b : Fin 0 → Bool) (β : Bool), maskWord w b β = 1 := fun b β => by
      simp [maskWord]
    rw [h1, h2, h2]
    simp only [zpow_zero, Units.val_one]
    rw [show FreeMonoid.ofList ([] : List I) = 1 from rfl, word_one, map_one]
    rfl
  | succ m ih =>
    rw [List.ofFn_succ, FreeMonoid.ofList_cons, r_word_of_mul, ih, Finset.mul_sum,
      ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
      add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, add_mul, inl_θ_mul_single, inr_θ_mul_single, maskWord_cons,
      maskInv_cons]
    simp [zpow_add]

/-- The shuffle formula in terms of the twisted product: for concatenated words,
`r(θ_{w w'}) = r(θ_w) r(θ_{w'})`, where the right-hand side is the product of the two shuffle
sums; the exponents combine by `maskInv_append`. -/
theorem r_ofFn_append {m m' : ℕ} (w : Fin m → I) (w' : Fin m' → I) :
    r dot v (word (FreeMonoid.ofList (List.ofFn (Fin.append w w'))) : PreF K I) =
      r dot v (word (FreeMonoid.ofList (List.ofFn w))) *
        r dot v (word (FreeMonoid.ofList (List.ofFn w'))) := by
  rw [← map_mul, ← word_mul, ← FreeMonoid.ofList_append, List.ofFn_fin_append]

/-- Product of two basis tensors of shuffle type: the twisted product of the terms of
`r(θ_w)` and `r(θ_{w'})` indexed by masks `b`, `b'` is the term of `r(θ_{w w'})` indexed by the
mask `b b'`. -/
theorem single_mask_mul_single_mask {m m' : ℕ} (w : Fin m → I) (w' : Fin m' → I)
    (b : Fin m → Bool) (b' : Fin m' → Bool) :
    (single (maskWord w b false, maskWord w b true) ((v ^ maskInv dot w b : Kˣ) : K) :
        TwSq K I dot v) *
      single (maskWord w' b' false, maskWord w' b' true) ((v ^ maskInv dot w' b' : Kˣ) : K) =
      single (maskWord (Fin.append w w') (Fin.append b b') false,
          maskWord (Fin.append w w') (Fin.append b b') true)
        ((v ^ maskInv dot (Fin.append w w') (Fin.append b b') : Kˣ) : K) := by
  rw [twSq_single_mul_single, maskWord_append, maskWord_append, maskInv_append]
  congr 1
  simp only [zpow_add, Units.val_mul]
  ring

/-- `inv` for the negated pairing. -/
theorem maskInv_neg {m : ℕ} (w : Fin m → I) (b : Fin m → Bool) :
    maskInv (fun a c => -dot a c) w b = -maskInv dot w b := by
  unfold maskInv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- **Changing `(·, v)` to `(-·, v⁻¹)`**: the twisted squares for the pairing `-dot` with
parameter `v` and for `dot` with `v⁻¹` have the same multiplication, and the two comultiplications
`r` agree. (KL I §3.1: KL's `q` is Lusztig's `v⁻¹`, and the KL I grading has
`deg ψ = -i·j`.) -/
theorem recast_r_neg (x : PreF K I) :
    TwistedMonoidAlgebra.recast _ _ (r (fun a c => -dot a c) v x) = r dot v⁻¹ x := by
  have key : TwistedMonoidAlgebra.recast _ _ ∘ₗ (r (fun a c => -dot a c) v).toLinearMap =
      (r dot v⁻¹ : PreF K I →ₐ[K] TwSq K I dot v⁻¹).toLinearMap := by
    refine lhom_ext fun w => ?_
    obtain ⟨m, f, rfl⟩ : ∃ (m : ℕ) (f : Fin m → I), FreeMonoid.ofList (List.ofFn f) = w :=
      ⟨_, (FreeMonoid.toList w).get, by rw [List.ofFn_get]; rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [r_ofFn, r_ofFn, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [TwistedMonoidAlgebra.recast_single, maskInv_neg, zpow_neg, inv_zpow]
  exact LinearMap.congr_fun key x

end Shuffle

end PreF

end Categorification.QuantumGroup
