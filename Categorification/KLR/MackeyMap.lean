/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeySubquot

/-!
# The map from the balanced tensor products to the Mackey subquotients

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18** (TeX lines 1784–1817). For a
quadruple `q = (α, β, γ, δ)` (the data `λ = β`, `KLRAlgebra.MackeyQuad`) let `d = quadPerm h q` be
the minimal double coset representative with `|λ| = card β` crossing strands and
`ψ_d = ψ_{σ(d)}` (`σ = canWord`). This file constructs the map of bimodules

`mackeyMap h q hc : (_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (_{ν-λ,…} R_{ν''} ⊗ _{λ,…} R_{ν'''}) → F_c / F_{c-1}`,
`t ⊗ b ↦ [ι_{ν,ν'}(t) ψ_d ι_{ν'',ν'''}(b)]`,

where `F = mackeyBimodFilt` is the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` and `c = card β`.

## Main results

* `KLRAlgebra.quadPerm_smul` : `d` carries the bottom sequence `(i_α i_γ)(i_β i_δ)` to the top
  sequence `(i_α i_β)(i_γ i_δ)`.
* `KLRAlgebra.quad_intertwine` : **`ι(ι_T(r)) ψ_d ≡ ψ_d ι''(ι_B(r))` modulo `F_{c-1}`** for all
  `r ∈ R' = R(α) ⊗ R(β) ⊗ R(γ) ⊗ R(δ)`: `ψ_d` intertwines the two embeddings of `R'` modulo lower
  terms (this is the content of the diagrammatic proof of Proposition 2.18).
* `KLRAlgebra.mackeyMap` (well defined by `quad_intertwine`), `KLRAlgebra.mackeyMap_tmul`,
  `KLRAlgebra.mackeyMap_left`, `KLRAlgebra.mackeyMap_right` (bimodule maps).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')

theorem castAlg_self {μ : Multiset I} (h' : μ = μ) (a : KLRAlgebra k Q μ) :
    castAlg Q h' a = a := rfl

/-! ### The minimal double coset representative of a quadruple -/

section QuadPerm

omit [DecidableEq I] in
include h in
theorem exists_quadPerm (q : MackeyQuad ν ν' ν'' ν''') :
    ∃ d, IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) d ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') d = Multiset.card q.β := by
  refine (exists_isDoubleShuffle_iff (Seq.card_add' ν ν') (card_add_bot h) _).2 ?_
  have e1 := congrArg Multiset.card q.h₁
  have e3 := congrArg Multiset.card q.h₃
  have e4 := congrArg Multiset.card q.h₄
  simp only [Multiset.card_add] at e1 e3 e4
  omega

/-- The minimal double coset representative `d` with `|λ| = card β` crossing strands. -/
def quadPerm (q : MackeyQuad ν ν' ν'' ν''') : Perm (Fin (Multiset.card (ν + ν'))) :=
  Classical.choose (exists_quadPerm h q)

omit [DecidableEq I] in
theorem quadPerm_spec (q : MackeyQuad ν ν' ν'' ν''') :
    IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) (quadPerm h q) ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') (quadPerm h q) = Multiset.card q.β :=
  Classical.choose_spec (exists_quadPerm h q)

omit [DecidableEq I] in
/-- The values of `d = quadPerm h q`, with `a = card α`, `b = card β`, `n'' = card ν''`. -/
theorem quadPerm_val (q : MackeyQuad ν ν' ν'' ν''') (p : Fin (Multiset.card (ν + ν'))) :
    ((quadPerm h q) p).val = if p.val < Multiset.card q.α then p.val
      else if p.val < Multiset.card ν'' then p.val + Multiset.card q.β
      else if p.val < Multiset.card ν'' + Multiset.card q.β then
        p.val + Multiset.card q.α - Multiset.card ν''
      else p.val := by
  obtain ⟨hd, hc⟩ := quadPerm_spec h q
  have e1 := congrArg Multiset.card q.h₁
  simp only [Multiset.card_add] at e1
  rw [hd.val_eq_ite, hc]
  have : Multiset.card ν - Multiset.card q.β = Multiset.card q.α := by omega
  rw [this]
  split_ifs <;> omega

section Lbl4

omit [DecidableEq I]

variable {μ₁ μ₂ μ₃ μ₄ X Y : Multiset I} (h₁₂ : μ₁ + μ₂ = X) (h₃₄ : μ₃ + μ₄ = Y) (x : Seq μ₁)
  (y : Seq μ₂) (z : Seq μ₃) (w : Seq μ₄) (t : Fin (Multiset.card (X + Y)))

theorem lbl4_1 (ht : t.val < Multiset.card μ₁) :
    ((seqCast h₁₂ (x.append y)).append (seqCast h₃₄ (z.append w))).1 t = x.1 ⟨t.val, ht⟩ := by
  have := congrArg Multiset.card h₁₂
  simp only [Multiset.card_add] at this
  rw [Seq.append_apply_lt _ _ _ (by omega), seqCast_append_apply_lt _ _ _ _ (by simpa using ht)]

theorem lbl4_2 (ht₁ : Multiset.card μ₁ ≤ t.val) (ht₂ : t.val < Multiset.card X) :
    ((seqCast h₁₂ (x.append y)).append (seqCast h₃₄ (z.append w))).1 t =
      y.1 ⟨t.val - Multiset.card μ₁, by
        have := congrArg Multiset.card h₁₂; simp only [Multiset.card_add] at this; omega⟩ := by
  rw [Seq.append_apply_lt _ _ _ ht₂, seqCast_append_apply_ge _ _ _ _ (by simpa using ht₁)]

theorem lbl4_3 (ht₁ : Multiset.card X ≤ t.val) (ht₂ : t.val < Multiset.card X + Multiset.card μ₃) :
    ((seqCast h₁₂ (x.append y)).append (seqCast h₃₄ (z.append w))).1 t =
      z.1 ⟨t.val - Multiset.card X, by omega⟩ := by
  rw [Seq.append_apply_ge _ _ _ ht₁, seqCast_append_apply_lt _ _ _ _ (by simp; omega)]

theorem lbl4_4 (ht : Multiset.card X + Multiset.card μ₃ ≤ t.val) :
    ((seqCast h₁₂ (x.append y)).append (seqCast h₃₄ (z.append w))).1 t =
      w.1 ⟨t.val - Multiset.card X - Multiset.card μ₃, by
        have := t.2; have := congrArg Multiset.card h₃₄
        simp only [Multiset.card_add] at *; omega⟩ := by
  rw [Seq.append_apply_ge _ _ _ (by omega), seqCast_append_apply_ge _ _ _ _ (by simp; omega)]

end Lbl4

omit [DecidableEq I] in
/-- **`d` carries the bottom sequence to the top sequence**:
`d • (i_α i_γ)(i_β i_δ) = (i_α i_β)(i_γ i_δ)`. -/
theorem quadPerm_smul (q : MackeyQuad ν ν' ν'' ν''') (i₁ : Seq q.α) (i₂ : Seq q.β)
    (i₃ : Seq q.γ) (i₄ : Seq q.δ) :
    quadPerm h q • seqCast h ((seqCast q.h₃ (i₁.append i₃)).append (seqCast q.h₄ (i₂.append i₄))) =
      (seqCast q.h₁ (i₁.append i₂)).append (seqCast q.h₂ (i₃.append i₄)) := by
  have e1 := congrArg Multiset.card q.h₁
  have e2 := congrArg Multiset.card q.h₂
  have e3 := congrArg Multiset.card q.h₃
  have e4 := congrArg Multiset.card q.h₄
  simp only [Multiset.card_add] at e1 e2 e3 e4
  apply Subtype.ext
  funext t
  obtain ⟨p, rfl⟩ := (quadPerm h q).surjective t
  rw [Seq.smul_apply, Equiv.symm_apply_apply, seqCast_apply]
  have hv := quadPerm_val h q p
  have hp := p.2
  simp only [Multiset.card_add] at hp
  by_cases h1 : p.val < Multiset.card q.α
  · rw [if_pos h1] at hv
    rw [lbl4_1 _ _ _ _ _ _ _ (by simpa using h1), lbl4_1 _ _ _ _ _ _ _ (by omega)]
    exact i₁.apply_congr (by simp [hv])
  rw [if_neg h1] at hv
  by_cases h2 : p.val < Multiset.card ν''
  · rw [if_pos h2] at hv
    rw [lbl4_2 _ _ _ _ _ _ _ (by simp; omega) (by simpa using h2),
      lbl4_3 _ _ _ _ _ _ _ (by omega) (by omega)]
    exact i₃.apply_congr (by simp [hv]; omega)
  rw [if_neg h2] at hv
  by_cases h3 : p.val < Multiset.card ν'' + Multiset.card q.β
  · rw [if_pos h3] at hv
    rw [lbl4_3 _ _ _ _ _ _ _ (by simp; omega) (by simp; omega),
      lbl4_2 _ _ _ _ _ _ _ (by omega) (by omega)]
    exact i₂.apply_congr (by simp [hv]; omega)
  · rw [if_neg h3] at hv
    rw [lbl4_4 _ _ _ _ _ _ _ (by simp; omega), lbl4_4 _ _ _ _ _ _ _ (by omega)]
    exact i₄.apply_congr (by simp [hv]; omega)

end QuadPerm

/-! ### The intertwining property of `ψ_d` -/

section Intertwine

variable (q : MackeyQuad ν ν' ν'' ν''')

local notation "ψD" =>
  (ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) : KLRAlgebra k Q (ν + ν'))
local notation "L" =>
  mackeyLower k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') (Multiset.card q.β)

theorem mackeyLower_concat_mul (t : TensorKLR Q ν ν') {c : ℕ} {y : KLRAlgebra k Q (ν + ν')}
    (hy : y ∈ mackeyLower k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c) :
    concat Q ν ν' t * y ∈ mackeyLower k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c :=
  mackeyLower_mul_mem (fun _ _ hy => concat_mul_mem_mackeyFilt t hy) hy

theorem mackeyLower_mul_botConcat (t : TensorKLR Q ν'' ν''') {n c : ℕ}
    {y : KLRAlgebra k Q (ν + ν')}
    (hy : y ∈ mackeyLower k Q (ν + ν') n (Multiset.card ν'') c) :
    y * botConcat Q h t ∈ mackeyLower k Q (ν + ν') n (Multiset.card ν'') c :=
  mul_mackeyLower_mem (fun _ _ hy => mul_botConcat_mem_mackeyFilt h t hy) hy

/-- The **intertwining defect** `r ↦ ι(ι_T(r)) ψ_d - ψ_d ι''(ι_B(r))`. -/
def quadDefect : QuadAlg Q q →ₗ[k] KLRAlgebra k Q (ν + ν') :=
  (LinearMap.mulRight k ψD ∘ₗ concat Q ν ν' ∘ₗ quadTop q) -
    (LinearMap.mulLeft k ψD ∘ₗ botConcat Q h ∘ₗ quadBot q)

theorem quadDefect_apply (r : QuadAlg Q q) :
    quadDefect h q r = concat Q ν ν' (quadTop q r) * ψD - ψD * botConcat Q h (quadBot q r) :=
  rfl

theorem quadDefect_mul {r s : QuadAlg Q q} (hr : quadDefect h q r ∈ L)
    (hs : quadDefect h q s ∈ L) : quadDefect h q (r * s) ∈ L := by
  rw [quadDefect_apply] at hr hs ⊢
  rw [quadTop_mul, concat_mul, quadBot_mul, botConcat_mul]
  have h1 := mackeyLower_concat_mul (quadTop q r) hs
  have h2 := mackeyLower_mul_botConcat h (quadBot q s) hr
  convert add_mem h1 h2 using 1
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

omit [DecidableEq I] in
theorem card_eqs :
    Multiset.card q.α + Multiset.card q.β = Multiset.card ν ∧
      Multiset.card q.γ + Multiset.card q.δ = Multiset.card ν' ∧
      Multiset.card q.α + Multiset.card q.γ = Multiset.card ν'' ∧
      Multiset.card q.β + Multiset.card q.δ = Multiset.card ν''' := by
  have e1 := congrArg Multiset.card q.h₁
  have e2 := congrArg Multiset.card q.h₂
  have e3 := congrArg Multiset.card q.h₃
  have e4 := congrArg Multiset.card q.h₄
  simp only [Multiset.card_add] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

theorem quadDefect_e (i₁ : Seq q.α) (i₂ : Seq q.β) (i₃ : Seq q.γ) (i₄ : Seq q.δ) :
    quadDefect h q (((e i₁ : KLRAlgebra k Q q.α) ⊗ₜ (e i₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((e i₃ : KLRAlgebra k Q q.γ) ⊗ₜ (e i₄ : KLRAlgebra k Q q.δ))) = 0 := by
  rw [quadDefect_apply, quadTop_tmul, quadBot_tmul, concat_e_tmul_e, concat_e_tmul_e,
    concat_e_tmul_e, concat_e_tmul_e, castAlg_e, castAlg_e, castAlg_e, castAlg_e,
    concat_e_tmul_e, botConcat_apply, concat_e_tmul_e, castAlg_e, e_mul_ψD, ← quadPerm_smul h q,
    inv_smul_smul, sub_self]

theorem quadTop_one : quadTop q (1 : QuadAlg Q q) =
    castAlg Q q.h₁ (oneConcat Q q.α q.β) ⊗ₜ castAlg Q q.h₂ (oneConcat Q q.γ q.δ) := by
  simp only [Algebra.TensorProduct.one_def]
  rw [quadTop_tmul,
    ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def, concat_one, concat_one]

theorem quadBot_one : quadBot q (1 : QuadAlg Q q) =
    castAlg Q q.h₃ (oneConcat Q q.α q.γ) ⊗ₜ castAlg Q q.h₄ (oneConcat Q q.β q.δ) := by
  simp only [Algebra.TensorProduct.one_def]
  rw [quadBot_tmul,
    ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def, concat_one, concat_one]

/-- `ψ_d` intertwines the idempotents: `ι(1_{α,β} ⊗ 1_{γ,δ}) ψ_d = ψ_d ι''(1_{α,γ} ⊗ 1_{β,δ})`. -/
theorem quadDefect_one : quadDefect (Q := Q) h q 1 = 0 := by
  have h1 : (1 : QuadAlg Q q) = (((1 : KLRAlgebra k Q q.α) ⊗ₜ (1 : KLRAlgebra k Q q.β)) ⊗ₜ
      ((1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)) : QuadAlg Q q) := by
    simp only [Algebra.TensorProduct.one_def]
  rw [h1, ← sum_e (ν := q.α), ← sum_e (ν := q.β), ← sum_e (ν := q.γ), ← sum_e (ν := q.δ)]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, quadDefect_e,
    Finset.sum_const_zero]

theorem concat_quadTop_one_mul_ψD :
    concat Q ν ν' (quadTop q 1) * ψD = ψD * botConcat Q h (quadBot q 1) := by
  have := quadDefect_one (Q := Q) h q
  rwa [quadDefect_apply, sub_eq_zero] at this

/-! #### Words of crossings -/

theorem ψ_mul_ψw_comm {μ : Multiset I} {j : ℕ} {B : List ℕ} (hB : ∀ l ∈ B, j + 1 < l) :
    (ψ j * ψw B : KLRAlgebra k Q μ) = ψw B * ψ j := by
  induction B with
  | nil => simp
  | cons l B ih =>
    rw [ψw_cons, ← mul_assoc, ψ_mul_ψ _ _ (hB l (by simp)), mul_assoc,
      ih fun l' hl' => hB l' (List.mem_cons_of_mem _ hl'), mul_assoc]

theorem ψw_mul_ψw_comm {μ : Multiset I} {A B : List ℕ} (h : ∀ j ∈ A, ∀ l ∈ B, j + 1 < l) :
    (ψw A * ψw B : KLRAlgebra k Q μ) = ψw B * ψw A := by
  induction A with
  | nil => simp
  | cons j A ih =>
    rw [ψw_cons, mul_assoc, ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), ← mul_assoc,
      ψ_mul_ψw_comm (h j (by simp)), mul_assoc]

theorem concat_quadTop_ψw {α₁ α₂ α₃ α₄ : List ℕ} (h₁ : ValidWord (Multiset.card q.α) α₁)
    (h₂ : ValidWord (Multiset.card q.β) α₂) (h₃ : ValidWord (Multiset.card q.γ) α₃)
    (h₄ : ValidWord (Multiset.card q.δ) α₄) :
    concat Q ν ν' (quadTop q (((ψw α₁ : KLRAlgebra k Q q.α) ⊗ₜ (ψw α₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((ψw α₃ : KLRAlgebra k Q q.γ) ⊗ₜ (ψw α₄ : KLRAlgebra k Q q.δ)))) =
      ψw ((α₁ ++ shiftWord (Multiset.card q.α) α₂) ++
        shiftWord (Multiset.card ν) (α₃ ++ shiftWord (Multiset.card q.γ) α₄)) *
        concat Q ν ν' (quadTop q 1) := by
  obtain ⟨e1, e2, -, -⟩ := card_eqs q
  have hX : ValidWord (Multiset.card ν) (α₁ ++ shiftWord (Multiset.card q.α) α₂) :=
    validWord_append.2 ⟨h₁.of_le (by omega), h₂.shiftWord e1⟩
  have hY : ValidWord (Multiset.card ν') (α₃ ++ shiftWord (Multiset.card q.γ) α₄) :=
    validWord_append.2 ⟨h₃.of_le (by omega), h₄.shiftWord e2⟩
  rw [quadTop_tmul, concat_ψw_tmul_ψw h₁ h₂, concat_ψw_tmul_ψw h₃ h₄, map_mul, map_mul,
    castAlg_ψw, castAlg_ψw, ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul, ← quadTop_one,
    concat_ψw_tmul_ψw hX hY, mul_assoc, oneConcat_mul_concat]

theorem botConcat_quadBot_ψw {α₁ α₂ α₃ α₄ : List ℕ} (h₁ : ValidWord (Multiset.card q.α) α₁)
    (h₂ : ValidWord (Multiset.card q.β) α₂) (h₃ : ValidWord (Multiset.card q.γ) α₃)
    (h₄ : ValidWord (Multiset.card q.δ) α₄) :
    botConcat Q h (quadBot q (((ψw α₁ : KLRAlgebra k Q q.α) ⊗ₜ (ψw α₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((ψw α₃ : KLRAlgebra k Q q.γ) ⊗ₜ (ψw α₄ : KLRAlgebra k Q q.δ)))) =
      ψw ((α₁ ++ shiftWord (Multiset.card q.α) α₃) ++
        shiftWord (Multiset.card ν'') (α₂ ++ shiftWord (Multiset.card q.β) α₄)) *
        botConcat Q h (quadBot q 1) := by
  obtain ⟨-, -, e3, e4⟩ := card_eqs q
  have hX : ValidWord (Multiset.card ν'') (α₁ ++ shiftWord (Multiset.card q.α) α₃) :=
    validWord_append.2 ⟨h₁.of_le (by omega), h₃.shiftWord e3⟩
  have hY : ValidWord (Multiset.card ν''') (α₂ ++ shiftWord (Multiset.card q.β) α₄) :=
    validWord_append.2 ⟨h₂.of_le (by omega), h₄.shiftWord e4⟩
  rw [quadBot_tmul, concat_ψw_tmul_ψw h₁ h₃, concat_ψw_tmul_ψw h₂ h₄, map_mul, map_mul,
    castAlg_ψw, castAlg_ψw, ← Algebra.TensorProduct.tmul_mul_tmul, ← quadBot_one, botConcat_mul,
    botConcat_apply, concat_ψw_tmul_ψw hX hY, map_mul, castAlg_ψw, ← concat_one, ← botConcat_apply,
    botConcat_one, mul_assoc, botOne_mul_botConcat]

omit [DecidableEq I] in
theorem dShift_quadPerm {j : ℕ} (hj : j < Multiset.card (ν + ν')) :
    dShift (quadPerm h q) j = if j < Multiset.card q.α then j
      else if j < Multiset.card ν'' then j + Multiset.card q.β
      else if j < Multiset.card ν'' + Multiset.card q.β then j + Multiset.card q.α - Multiset.card ν''
      else j := by
  rw [dShift, dif_pos hj, quadPerm_val]

theorem quadDefect_ψw {α₁ α₂ α₃ α₄ : List ℕ} (h₁ : ValidWord (Multiset.card q.α) α₁)
    (h₂ : ValidWord (Multiset.card q.β) α₂) (h₃ : ValidWord (Multiset.card q.γ) α₃)
    (h₄ : ValidWord (Multiset.card q.δ) α₄) :
    quadDefect h q (((ψw α₁ : KLRAlgebra k Q q.α) ⊗ₜ (ψw α₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((ψw α₃ : KLRAlgebra k Q q.γ) ⊗ₜ (ψw α₄ : KLRAlgebra k Q q.δ))) ∈ L := by
  obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
  obtain ⟨hd, hc⟩ := quadPerm_spec h q
  have hm : Multiset.card (ν + ν') = Multiset.card ν + Multiset.card ν' := Multiset.card_add _ _
  rw [quadDefect_apply, concat_quadTop_ψw q h₁ h₂ h₃ h₄, botConcat_quadBot_ψw h q h₁ h₂ h₃ h₄,
    mul_assoc, concat_quadTop_one_mul_ψD, ← mul_assoc, ← mul_assoc, ← sub_mul]
  refine mackeyLower_mul_botConcat h _ ?_
  set a := Multiset.card q.α
  set b := Multiset.card q.β
  set g := Multiset.card q.γ
  set n'' := Multiset.card ν''
  set bot' := α₁ ++ shiftWord n'' α₂ ++ shiftWord a α₃ ++ shiftWord (n'' + b) α₄ with hbot'
  have hsh : ∀ (x y : ℕ) (l : List ℕ), shiftWord x (shiftWord y l) = shiftWord (x + y) l := by
    intro x y l; simp only [shiftWord, List.map_map]; congr 1; funext z; simp; omega
  have hs2 : shiftWord n'' (α₂ ++ shiftWord b α₄) = shiftWord n'' α₂ ++ shiftWord (n'' + b) α₄ := by
    simp only [shiftWord, List.map_append, List.map_map]
    congr 2; funext z; simp only [Function.comp_apply]; omega
  have hbot : ψw ((α₁ ++ shiftWord a α₃) ++ shiftWord n'' (α₂ ++ shiftWord b α₄)) =
      (ψw bot' : KLRAlgebra k Q (ν + ν')) := by
    have hcomm : ∀ j ∈ shiftWord a α₃, ∀ l ∈ shiftWord n'' α₂, j + 1 < l := by
      intro j hj l hl
      simp only [shiftWord, List.mem_map] at hj hl
      obtain ⟨j, hj, rfl⟩ := hj
      obtain ⟨l, -, rfl⟩ := hl
      have := h₃ j hj
      omega
    rw [hbot', hs2]
    simp only [ψw_append, mul_assoc]
    rw [← mul_assoc (ψw (shiftWord a α₃)), ψw_mul_ψw_comm hcomm, mul_assoc]
  have htop : (α₁ ++ shiftWord a α₂) ++ shiftWord (Multiset.card ν) (α₃ ++ shiftWord g α₄) =
      bot'.map (dShift (quadPerm h q)) := by
    rw [hbot']
    simp only [shiftWord, List.map_append, List.map_map, List.append_assoc]
    congr 1
    · conv_lhs => rw [← List.map_id α₁]
      refine List.map_congr_left fun j hj => ?_
      have := h₁ j hj
      rw [id, dShift_quadPerm h q (by omega), if_pos (by omega)]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      have := h₂ j hj
      simp only [Function.comp_apply]
      rw [dShift_quadPerm h q (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      omega
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      have := h₃ j hj
      simp only [Function.comp_apply]
      rw [dShift_quadPerm h q (by omega), if_neg (by omega), if_pos (by omega)]
      omega
    · refine List.map_congr_left fun j hj => ?_
      have := h₄ j hj
      simp only [Function.comp_apply]
      rw [dShift_quadPerm h q (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      omega
  rw [htop, hbot, ← hc]
  refine ψw_map_mul_ψD_sub_mem hd fun j hj => ?_
  rw [hc]
  have hna : Multiset.card ν - b = a := by omega
  simp only [SameBlock, hna]
  simp only [hbot', shiftWord, List.mem_append, List.mem_map] at hj
  rcases hj with ((hj | ⟨j', hj', rfl⟩) | ⟨j', hj', rfl⟩) | ⟨j', hj', rfl⟩
  · have := h₁ j hj; omega
  · have := h₂ j' hj'; omega
  · have := h₃ j' hj'; omega
  · have := h₄ j' hj'; omega

/-! #### Polynomials -/

omit [DecidableEq I] in
theorem rename_congr' {a b : ℕ} {f g : Fin a → Fin b} (hfg : ∀ x, f x = g x)
    (p : MvPolynomial (Fin a) k) : rename f p = rename g p := by
  rw [funext hfg]

theorem concat_quadTop_pol (p₁ : MvPolynomial (Fin (Multiset.card q.α)) k)
    (p₂ : MvPolynomial (Fin (Multiset.card q.β)) k) (p₃ : MvPolynomial (Fin (Multiset.card q.γ)) k)
    (p₄ : MvPolynomial (Fin (Multiset.card q.δ)) k) :
    concat Q ν ν' (quadTop q (((pol p₁ : KLRAlgebra k Q q.α) ⊗ₜ (pol p₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((pol p₃ : KLRAlgebra k Q q.γ) ⊗ₜ (pol p₄ : KLRAlgebra k Q q.δ)))) =
      pol (rename (Seq.posL ν') (rename (Fin.cast (congrArg Multiset.card q.h₁))
          (rename (Seq.posL q.β) p₁ * rename (Seq.posR q.α) p₂)) *
        rename (Seq.posR ν) (rename (Fin.cast (congrArg Multiset.card q.h₂))
          (rename (Seq.posL q.δ) p₃ * rename (Seq.posR q.γ) p₄))) *
        concat Q ν ν' (quadTop q 1) := by
  rw [quadTop_tmul, concat_pol_tmul_pol, concat_pol_tmul_pol, map_mul (castAlg Q q.h₁),
    map_mul (castAlg Q q.h₂), castAlg_pol_eq, castAlg_pol_eq,
    ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul, ← quadTop_one,
    concat_pol_tmul_pol, mul_assoc, oneConcat_mul_concat]

theorem botConcat_quadBot_pol (p₁ : MvPolynomial (Fin (Multiset.card q.α)) k)
    (p₂ : MvPolynomial (Fin (Multiset.card q.β)) k) (p₃ : MvPolynomial (Fin (Multiset.card q.γ)) k)
    (p₄ : MvPolynomial (Fin (Multiset.card q.δ)) k) :
    botConcat Q h (quadBot q (((pol p₁ : KLRAlgebra k Q q.α) ⊗ₜ (pol p₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((pol p₃ : KLRAlgebra k Q q.γ) ⊗ₜ (pol p₄ : KLRAlgebra k Q q.δ)))) =
      pol (rename (Fin.cast (congrArg Multiset.card h))
        (rename (Seq.posL ν''') (rename (Fin.cast (congrArg Multiset.card q.h₃))
          (rename (Seq.posL q.γ) p₁ * rename (Seq.posR q.α) p₃)) *
        rename (Seq.posR ν'') (rename (Fin.cast (congrArg Multiset.card q.h₄))
          (rename (Seq.posL q.δ) p₂ * rename (Seq.posR q.β) p₄)))) *
        botConcat Q h (quadBot q 1) := by
  rw [quadBot_tmul, concat_pol_tmul_pol, concat_pol_tmul_pol, map_mul (castAlg Q q.h₃),
    map_mul (castAlg Q q.h₄), castAlg_pol_eq, castAlg_pol_eq,
    ← Algebra.TensorProduct.tmul_mul_tmul, ← quadBot_one, botConcat_mul,
    botConcat_apply, concat_pol_tmul_pol, map_mul (castAlg Q h), castAlg_pol_eq, ← concat_one,
    ← botConcat_apply, botConcat_one, mul_assoc, botOne_mul_botConcat]

theorem quadDefect_pol (p₁ : MvPolynomial (Fin (Multiset.card q.α)) k)
    (p₂ : MvPolynomial (Fin (Multiset.card q.β)) k) (p₃ : MvPolynomial (Fin (Multiset.card q.γ)) k)
    (p₄ : MvPolynomial (Fin (Multiset.card q.δ)) k) :
    quadDefect h q (((pol p₁ : KLRAlgebra k Q q.α) ⊗ₜ (pol p₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((pol p₃ : KLRAlgebra k Q q.γ) ⊗ₜ (pol p₄ : KLRAlgebra k Q q.δ))) ∈ L := by
  obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
  obtain ⟨hd, hc⟩ := quadPerm_spec h q
  have hm : Multiset.card (ν + ν') = Multiset.card ν + Multiset.card ν' := Multiset.card_add _ _
  rw [quadDefect_apply, concat_quadTop_pol q, botConcat_quadBot_pol h q, mul_assoc,
    concat_quadTop_one_mul_ψD, ← mul_assoc, ← mul_assoc, ← sub_mul]
  refine mackeyLower_mul_botConcat h _ ?_
  have hval : ∀ p : Fin (Multiset.card (ν + ν')), ((quadPerm h q) p).val = _ :=
    quadPerm_val h q
  have r1 : rename (Seq.posL ν') (rename (Fin.cast (congrArg Multiset.card q.h₁))
      (rename (Seq.posL q.β) p₁)) = rename (quadPerm h q) (rename (Fin.cast (congrArg
      Multiset.card h)) (rename (Seq.posL ν''') (rename (Fin.cast (congrArg Multiset.card q.h₃))
      (rename (Seq.posL q.γ) p₁)))) := by
    simp only [rename_rename]; refine rename_congr' (fun x => ?_) _; apply Fin.ext
    simp only [Function.comp_apply, hval, Seq.posL_val, Seq.posR_val, Fin.coe_cast]
    have := x.2; split_ifs; omega
  have r2 : rename (Seq.posL ν') (rename (Fin.cast (congrArg Multiset.card q.h₁))
      (rename (Seq.posR q.α) p₂)) = rename (quadPerm h q) (rename (Fin.cast (congrArg
      Multiset.card h)) (rename (Seq.posR ν'') (rename (Fin.cast (congrArg Multiset.card q.h₄))
      (rename (Seq.posL q.δ) p₂)))) := by
    simp only [rename_rename]; refine rename_congr' (fun x => ?_) _; apply Fin.ext
    simp only [Function.comp_apply, hval, Seq.posL_val, Seq.posR_val, Fin.coe_cast]
    have := x.2; split_ifs <;> omega
  have r3 : rename (Seq.posR ν) (rename (Fin.cast (congrArg Multiset.card q.h₂))
      (rename (Seq.posL q.δ) p₃)) = rename (quadPerm h q) (rename (Fin.cast (congrArg
      Multiset.card h)) (rename (Seq.posL ν''') (rename (Fin.cast (congrArg Multiset.card q.h₃))
      (rename (Seq.posR q.α) p₃)))) := by
    simp only [rename_rename]; refine rename_congr' (fun x => ?_) _; apply Fin.ext
    simp only [Function.comp_apply, hval, Seq.posL_val, Seq.posR_val, Fin.coe_cast]
    have := x.2; split_ifs <;> omega
  have r4 : rename (Seq.posR ν) (rename (Fin.cast (congrArg Multiset.card q.h₂))
      (rename (Seq.posR q.γ) p₄)) = rename (quadPerm h q) (rename (Fin.cast (congrArg
      Multiset.card h)) (rename (Seq.posR ν'') (rename (Fin.cast (congrArg Multiset.card q.h₄))
      (rename (Seq.posR q.β) p₄)))) := by
    simp only [rename_rename]; refine rename_congr' (fun x => ?_) _; apply Fin.ext
    simp only [Function.comp_apply, hval, Seq.posL_val, Seq.posR_val, Fin.coe_cast]
    have := x.2; split_ifs <;> omega
  have key : rename (Seq.posL ν') (rename (Fin.cast (congrArg Multiset.card q.h₁))
          (rename (Seq.posL q.β) p₁ * rename (Seq.posR q.α) p₂)) *
        rename (Seq.posR ν) (rename (Fin.cast (congrArg Multiset.card q.h₂))
          (rename (Seq.posL q.δ) p₃ * rename (Seq.posR q.γ) p₄)) =
      rename (quadPerm h q) (rename (Fin.cast (congrArg Multiset.card h))
        (rename (Seq.posL ν''') (rename (Fin.cast (congrArg Multiset.card q.h₃))
          (rename (Seq.posL q.γ) p₁ * rename (Seq.posR q.α) p₃)) *
        rename (Seq.posR ν'') (rename (Fin.cast (congrArg Multiset.card q.h₄))
          (rename (Seq.posL q.δ) p₂ * rename (Seq.posR q.β) p₄)))) := by
    simp only [map_mul] at r1 r2 r3 r4 ⊢
    rw [r1, r2, r3, r4]
    ring
  rw [key]
  have := pol_rename_mul_ψD_sub_mem (Q := Q) hd (rename (Fin.cast (congrArg Multiset.card h))
    (rename (Seq.posL ν''') (rename (Fin.cast (congrArg Multiset.card q.h₃))
      (rename (Seq.posL q.γ) p₁ * rename (Seq.posR q.α) p₃)) *
    rename (Seq.posR ν'') (rename (Fin.cast (congrArg Multiset.card q.h₄))
      (rename (Seq.posL q.δ) p₂ * rename (Seq.posR q.β) p₄))))
  rwa [hc] at this

/-! #### All of `R'` -/

/-- **KL I, Proposition 2.18 (the intertwining property of `ψ_d`)**: for every
`r ∈ R' = R(α) ⊗ R(β) ⊗ R(γ) ⊗ R(δ)`,
`ι_{ν,ν'}(ι_T r) ψ_d ≡ ψ_d ι_{ν'',ν'''}(ι_B r)` modulo the lower step `F_{c-1}` (`c = |λ|`). -/
theorem quad_intertwine (r : QuadAlg Q q) : quadDefect h q r ∈ L := by
  induction r using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | tmul u v =>
    refine tensor_mem_of_gen ((quadDefect h q).comp ((TensorProduct.mk k _ _).flip v)) L
      (fun α₁ p₁ i₁ α₂ p₂ i₂ h₁ h₂ => ?_) u
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply]
    refine tensor_mem_of_gen ((quadDefect h q).comp (TensorProduct.mk k _ _ _)) L
      (fun α₃ p₃ i₃ α₄ p₄ i₄ h₃ h₄ => ?_) v
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply]
    rw [← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul,
      ← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul,
      ← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul]
    refine quadDefect_mul h q (quadDefect_mul h q (quadDefect_ψw h q h₁ h₂ h₃ h₄)
      (quadDefect_pol h q p₁ p₂ p₃ p₄)) ?_
    rw [quadDefect_e]; exact zero_mem _

end Intertwine

/-! ### The subquotients of the Mackey filtration -/

section Subquot

variable (Q) in
/-- The step `F_{c-1}` of the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` below
`F_c = mackeyBimodFilt Q h c` (`⊥` for `c = 0`). -/
def mackeyLowerBimod (c : ℕ) : Submodule k (KLRAlgebra k Q (ν + ν')) :=
  bimod Q h ⊓ mackeyLower k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c

theorem mackeyLowerBimod_le (c : ℕ) : mackeyLowerBimod Q h c ≤ mackeyBimodFilt Q h c :=
  inf_le_inf_left _ (mackeyLower_le c)

theorem mackeyLowerBimod_succ (c : ℕ) :
    mackeyLowerBimod Q h (c + 1) = mackeyBimodFilt Q h c := rfl

theorem mackeyLowerBimod_zero : mackeyLowerBimod Q h 0 = ⊥ := by
  simp [mackeyLowerBimod]

variable (Q) in
/-- **The subquotient `F_c / F_{c-1}` of the Mackey filtration** of `_{ν,ν'}R_{ν'',ν'''}`. -/
def MackeySubquot (c : ℕ) : Type _ :=
  ↥(mackeyBimodFilt Q h c) ⧸ (mackeyLowerBimod Q h c).comap (mackeyBimodFilt Q h c).subtype

instance (c : ℕ) : AddCommGroup (MackeySubquot Q h c) := Submodule.Quotient.addCommGroup _

instance (c : ℕ) : Module k (MackeySubquot Q h c) := Submodule.Quotient.module _

/-- The class `[r] ∈ F_c / F_{c-1}` of `r ∈ F_c`. -/
def subquotOf {c : ℕ} (r : KLRAlgebra k Q (ν + ν')) (hr : r ∈ mackeyBimodFilt Q h c) :
    MackeySubquot Q h c :=
  Submodule.Quotient.mk (⟨r, hr⟩ : mackeyBimodFilt Q h c)

theorem subquotOf_congr {c : ℕ} {r s : KLRAlgebra k Q (ν + ν')} (hrs : r = s)
    (hr : r ∈ mackeyBimodFilt Q h c) (hs : s ∈ mackeyBimodFilt Q h c) :
    subquotOf h r hr = subquotOf h s hs := by
  subst hrs; rfl

theorem subquotOf_add {c : ℕ} {r s : KLRAlgebra k Q (ν + ν')} (hr : r ∈ mackeyBimodFilt Q h c)
    (hs : s ∈ mackeyBimodFilt Q h c) :
    subquotOf h (r + s) (add_mem hr hs) = subquotOf h r hr + subquotOf h s hs := rfl

theorem subquotOf_smul {c : ℕ} (a : k) {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) :
    subquotOf h (a • r) (Submodule.smul_mem _ a hr) = a • subquotOf h r hr := rfl

theorem subquotOf_eq_iff {c : ℕ} {r s : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) (hs : s ∈ mackeyBimodFilt Q h c) :
    subquotOf h r hr = subquotOf h s hs ↔ r - s ∈ mackeyLowerBimod Q h c :=
  Submodule.Quotient.eq _

theorem subquotOf_eq_zero_iff {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) :
    subquotOf h r hr = 0 ↔ r ∈ mackeyLowerBimod Q h c :=
  Submodule.Quotient.mk_eq_zero _

theorem subquotOf_surjective {c : ℕ} (x : MackeySubquot Q h c) :
    ∃ r hr, subquotOf h r hr = x := by
  obtain ⟨⟨r, hr⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨r, hr, rfl⟩

theorem concat_mul_mem_mackeyLowerBimod (t : TensorKLR Q ν ν') {c : ℕ}
    {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ mackeyLowerBimod Q h c) :
    concat Q ν ν' t * r ∈ mackeyLowerBimod Q h c :=
  ⟨concat_mul_mem_bimod h t hr.1, mackeyLower_concat_mul t hr.2⟩

theorem mul_botConcat_mem_mackeyLowerBimod (t : TensorKLR Q ν'' ν''') {c : ℕ}
    {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ mackeyLowerBimod Q h c) :
    r * botConcat Q h t ∈ mackeyLowerBimod Q h c :=
  ⟨mul_botConcat_mem_bimod h t hr.1, mackeyLower_mul_botConcat h t hr.2⟩

/-- The left action of `R(ν) ⊗ R(ν')` on `F_c / F_{c-1}`. -/
def subquotLeft (c : ℕ) (t : TensorKLR Q ν ν') : MackeySubquot Q h c →ₗ[k] MackeySubquot Q h c :=
  Submodule.mapQ _ _ ((LinearMap.mulLeft k (concat Q ν ν' t)).restrict
    fun _ hr => concat_mul_mem_mackeyBimodFilt h t hr)
    fun r hr => concat_mul_mem_mackeyLowerBimod h t (r := (r : KLRAlgebra k Q (ν + ν'))) hr

/-- The right action of `R(ν'') ⊗ R(ν''')` on `F_c / F_{c-1}`. -/
def subquotRight (c : ℕ) (t : TensorKLR Q ν'' ν''') :
    MackeySubquot Q h c →ₗ[k] MackeySubquot Q h c :=
  Submodule.mapQ _ _ ((LinearMap.mulRight k (botConcat Q h t)).restrict
    fun _ hr => mul_botConcat_mem_mackeyBimodFilt h t hr)
    fun r hr => mul_botConcat_mem_mackeyLowerBimod h t (r := (r : KLRAlgebra k Q (ν + ν'))) hr

theorem subquotLeft_of {c : ℕ} (t : TensorKLR Q ν ν') {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) :
    subquotLeft h c t (subquotOf h r hr) =
      subquotOf h (concat Q ν ν' t * r) (concat_mul_mem_mackeyBimodFilt h t hr) := rfl

theorem subquotRight_of {c : ℕ} (t : TensorKLR Q ν'' ν''') {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) :
    subquotRight h c t (subquotOf h r hr) =
      subquotOf h (r * botConcat Q h t) (mul_botConcat_mem_mackeyBimodFilt h t hr) := rfl

end Subquot

/-! ### The map `(t ⊗ b) ↦ [ι(t) ψ_d ι''(b)]` -/

section Map

variable (q : MackeyQuad ν ν' ν'' ν''')

local notation "ψD" =>
  (ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) : KLRAlgebra k Q (ν + ν'))

theorem concat_mul_ψD_mul_mem {c : ℕ} (hc : Multiset.card q.β = c) (t : TensorKLR Q ν ν')
    (b : TensorKLR Q ν'' ν''') :
    concat Q ν ν' t * ψD * botConcat Q h b ∈ mackeyBimodFilt Q h c := by
  refine ⟨(mem_bimod h).2 ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, oneConcat_mul_concat, mul_assoc _ (botConcat Q h b),
      botConcat_mul_botOne]
  · refine mul_botConcat_mem_mackeyFilt h b (concat_mul_mem_mackeyFilt t ?_)
    exact ψw_mem_mackeyFilt h (canWord _) (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)
      _ (by rw [(quadPerm_spec h q).2, hc])

/-- The `k`-bilinear map `(t, b) ↦ [ι(t) ψ_d ι''(b)]`. -/
def mackeyBil {c : ℕ} (hc : Multiset.card q.β = c) :
    MackeyTop Q q →ₗ[k] MackeyBot Q q →ₗ[k] MackeySubquot Q h c :=
  LinearMap.mk₂ k (fun t b => subquotOf h (concat Q ν ν' t * ψD * botConcat Q h b)
      (concat_mul_ψD_mul_mem h q hc _ _))
    (fun t t' b => by
      rw [← subquotOf_add]; exact subquotOf_congr h (by simp [map_add, add_mul]) _ _)
    (fun a t b => by
      rw [← subquotOf_smul]; exact subquotOf_congr h (by simp [map_smul, smul_mul_assoc]) _ _)
    (fun t b b' => by
      rw [← subquotOf_add]; exact subquotOf_congr h (by simp [map_add, mul_add]) _ _)
    (fun a t b => by
      rw [← subquotOf_smul]; exact subquotOf_congr h (by simp [map_smul, mul_smul_comm]) _ _)

theorem mackeyBil_apply {c : ℕ} (hc : Multiset.card q.β = c) (t : MackeyTop Q q)
    (b : MackeyBot Q q) :
    mackeyBil h q hc t b = subquotOf h (concat Q ν ν' t * ψD * botConcat Q h b)
      (concat_mul_ψD_mul_mem h q hc _ _) := rfl

/-- The map is balanced over `R'`: this is where `quad_intertwine` is used. -/
theorem mackeyBil_balanced {c : ℕ} (hc : Multiset.card q.β = c) (t : MackeyTop Q q)
    (r : QuadAlg Q q) (b : MackeyBot Q q) :
    mackeyBil h q hc (op r • t) b = mackeyBil h q hc t (r • b) := by
  rw [mackeyBil_apply, mackeyBil_apply, subquotOf_eq_iff]
  change concat Q ν ν' ((t : TensorKLR Q ν ν') * quadTop q r) * ψD * botConcat Q h b -
    concat Q ν ν' t * ψD * botConcat Q h (quadBot q r * b) ∈ mackeyLowerBimod Q h c
  have key : concat Q ν ν' ((t : TensorKLR Q ν ν') * quadTop q r) * ψD * botConcat Q h b -
      concat Q ν ν' t * ψD * botConcat Q h (quadBot q r * b) =
      concat Q ν ν' t * quadDefect h q r * botConcat Q h b := by
    rw [quadDefect_apply, concat_mul, botConcat_mul]
    simp only [mul_sub, sub_mul, mul_assoc]
  refine ⟨sub_mem (concat_mul_ψD_mul_mem h q hc _ _).1 (concat_mul_ψD_mul_mem h q hc _ _).1, ?_⟩
  rw [key]
  subst hc
  exact mackeyLower_mul_botConcat h _ (mackeyLower_concat_mul _ (quad_intertwine h q r))

/-- **The map of KL I, Proposition 2.18**:
`(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (_{ν-λ,…} R_{ν''} ⊗ _{λ,…} R_{ν'''}) → F_c / F_{c-1}`,
`t ⊗ b ↦ [ι_{ν,ν'}(t) ψ_d ι_{ν'',ν'''}(b)]` (`c = |λ| = card β`). -/
def mackeyMap {c : ℕ} (hc : Multiset.card q.β = c) : MackeyX Q q →ₗ[k] MackeySubquot Q h c :=
  BalancedTensor.lift (mackeyBil h q hc) (fun t r b => mackeyBil_balanced h q hc t r b)

theorem mackeyMap_tmul {c : ℕ} (hc : Multiset.card q.β = c) (t : MackeyTop Q q)
    (b : MackeyBot Q q) :
    mackeyMap h q hc (BalancedTensor.tmul t b) = subquotOf h
      (concat Q ν ν' t * ψD * botConcat Q h b) (concat_mul_ψD_mul_mem h q hc _ _) := rfl

set_option maxHeartbeats 1000000 in
/-- `mackeyMap` is a map of left `R(ν) ⊗ R(ν')`-modules. -/
theorem mackeyMap_left {c : ℕ} (hc : Multiset.card q.β = c) (a : TensorKLR Q ν ν')
    (x : MackeyX Q q) : mackeyMap h q hc (a • x) = subquotLeft h c a (mackeyMap h q hc x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul t b =>
    rw [BalancedTensor.smul_tmul', mackeyMap_tmul, mackeyMap_tmul, subquotLeft_of]
    refine subquotOf_congr h ?_ _ _
    show concat Q ν ν' (a * (t : TensorKLR Q ν ν')) * _ * _ = concat Q ν ν' a * (_ * _ * _)
    rw [concat_mul]; simp only [mul_assoc]
  | add x y hx hy =>
    rw [smul_add, map_add (mackeyMap h q hc), hx, hy, map_add (mackeyMap h q hc),
      map_add (subquotLeft h c a)]

set_option maxHeartbeats 1000000 in
/-- `mackeyMap` is a map of right `R(ν'') ⊗ R(ν''')`-modules. -/
theorem mackeyMap_right {c : ℕ} (hc : Multiset.card q.β = c) (a : TensorKLR Q ν'' ν''')
    (x : MackeyX Q q) :
    mackeyMap h q hc (MackeyX.rightAct a x) = subquotRight h c a (mackeyMap h q hc x) := by
  induction x using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul t b =>
    rw [MackeyX.rightAct_tmul, mackeyMap_tmul, mackeyMap_tmul, subquotRight_of]
    refine subquotOf_congr h ?_ _ _
    show _ * _ * botConcat Q h ((b : TensorKLR Q ν'' ν''') * a) = _ * _ * _ * _
    rw [botConcat_mul]; simp only [mul_assoc]
  | add x y hx hy =>
    rw [map_add (MackeyX.rightAct a), map_add (mackeyMap h q hc), hx, hy,
      map_add (mackeyMap h q hc), map_add (subquotRight h c a)]

end Map

end KLRAlgebra

end Categorification.KLR

end
