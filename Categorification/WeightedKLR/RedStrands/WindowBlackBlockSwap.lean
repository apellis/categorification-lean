/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockTrace
import Categorification.WeightedKLR.RedStrands.FrontWindowFlip
import Categorification.TypeA.BlockSwapShuffle

/-!
# The longest block crossing intertwines the two block embeddings, modulo `F_{m-1}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the induction–coinduction identity (IC),
step 2, at `ℓ = 0`: then the algebra `λ⁺` with the strands at the maximum at the right end and
the one with them at the left end coincide, and there are two embeddings of the black block
algebra `R(ν) ⊗ R^{(μ,μ*)}(ν₀)` into the KLR algebra of `λ⁺`: with the block of `ν` first
(`prefixMapKLR`, `endMapKLR`) and with it last (`frontMapKLR`, `suffixMapKLR`).

Let `w_L` be the minimal double coset representative for the top blocks `(m, N)` and the bottom
blocks `(N, m)` with `m` crossing strands, and `ψ_{w_L}` its diagram. With `F_{m-1}` the lower
step of Khovanov–Lauda's Mackey filtration (`KLRAlgebra.mackeyLower`):

* `ψ_{w_L} · (b ⊗ a)_right - (a ⊗ b)_left · ψ_{w_L} ∈ F_{m-1}` for all `a`, `b`
  (`ψD_mul_frontSuffix_sub_mem`);
* `F_{m-1}` is stable under left multiplication by the left embedding and under right
  multiplication by the right embedding (`prefixMapKLR_mul_mem`, `endMapKLR_mul_mem`,
  `mul_frontMapKLR_mem`, `mul_suffixMapKLR_mem`).

The loading of the bottom of `ψ_{w_L}` with the block of `ν` last is the loading of its top with
the block of `ν` first (`smul_frontSeq_eq_endSeq`), and every shuffle with `m` crossing strands
is `w_L` (`TypeA.eq_of_crossCount_eq`).

## Main results

* `CupCap.smul_frontSeq_eq_endSeq`.
* `CupCap.ψD_mul_frontSuffix_sub_mem`.
* `CupCap.prefixMapKLR_mul_mem`, `CupCap.endMapKLR_mul_mem`, `CupCap.mul_frontMapKLR_mem`,
  `CupCap.mul_suffixMapKLR_mem`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I} {n n'' : ℕ}

theorem mackeyLower_ψw_mul {α : List ℕ} (hα : ∀ j ∈ α, j + 1 < n ∨ n ≤ j) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyLower k Q μ n n'' c) :
    ψw α * y ∈ mackeyLower k Q μ n n'' c := by
  induction α with
  | nil => rwa [ψw_nil, one_mul]
  | cons j α ih =>
    rw [ψw_cons, mul_assoc]
    exact mackeyLower_ψ_mul (hα j (by simp))
      (ih fun j' hj' => hα j' (List.mem_cons_of_mem _ hj'))

theorem mackeyLower_e_mul (s : Seq μ) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : e s * y ∈ mackeyLower k Q μ n n'' c := by
  have h := mackeyLower_eSum_mul {s} hy
  rwa [eSum, Finset.sum_singleton] at h

theorem mackeyLower_mul_e (s : Seq μ) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : y * e s ∈ mackeyLower k Q μ n n'' c := by
  have h := mackeyLower_mul_eSum {s} hy
  rwa [eSum, Finset.sum_singleton] at h

theorem commute_ψw_ψw_of_far {ρ σ : List ℕ} (h : ∀ j ∈ ρ, ∀ l ∈ σ, j + 1 < l ∨ l + 1 < j) :
    Commute (ψw ρ : KLRAlgebra k Q μ) (ψw σ) := by
  induction ρ with
  | nil => rw [ψw_nil]; exact Commute.one_left _
  | cons j ρ ih =>
    rw [ψw_cons]
    exact (commute_ψ_ψw fun l hl => h j (by simp) l hl).mul_left
      (ih fun j' hj' l hl => h j' (List.mem_cons_of_mem _ hj') l hl)

/-- Induction along a basis. -/
theorem basis_induction {ι V : Type*} [AddCommGroup V] [Module k V] (B : Module.Basis ι k V)
    {P : V → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : k) x, P x → P (c • x)) (hB : ∀ i, P (B i)) (v : V) : P v := by
  have hv : v ∈ Submodule.span k (Set.range B) := B.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hB i
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-- Induction over the KLR algebra along the basis `x^u ψ_{w} e(i)` with dots on top. -/
theorem klr_induction (hsym : KLRSymm Q) {P : KLRAlgebra k Q μ → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : k) x, P x → P (c • x))
    (hb : ∀ (u : Fin (Multiset.card μ) →₀ ℕ) (α : List ℕ), ValidWord (Multiset.card μ) α →
      ∀ s : Seq μ, P (pol (monomial u 1) * ψw α * e s)) (a : KLRAlgebra k Q μ) : P a := by
  refine basis_induction (lbasis hsym (canWord (Multiset.card μ))
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)) h0 hadd hsmul (fun b => ?_) a
  rw [lbasis_apply]
  exact hb _ _ (isReduced_canWord _ _).1 _

end Generic

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight 0 ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (stendhalWeight (0 + 2) (ν + ν₀))
local notation "hM" => m_add_N_end (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)
local notation "hK" => N_add_m_front (I := I) (ℓ := 0) (ν := ν) (ν₀ := ν₀)
local notation "L" => mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
  (stendhalWeight (0 + 2) (ν + ν₀)) m N m

/-! ### The longest block crossing -/

omit [DecidableEq I] in
/-- The values of `w_L`: `p ↦ p + m` on the first `N` positions and `p ↦ p - N` on the rest. -/
theorem val_wL {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (p : Fin M) : (d p).val = if p.val < N then p.val + m else p.val - N := by
  have h := hd.val_eq_ite hM hK p
  rw [hcd] at h
  have hp := p.2
  have hM' := hM
  split_ifs at h ⊢ <;> omega

omit [DecidableEq I] in
theorem inv_wL_of_lt {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (a : Fin M) (ha : a.val < m) :
    d⁻¹ a = ⟨N + a.val, by have := hM; omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  apply Fin.ext
  rw [val_wL hd hcd, ite_eq_right (by simp)]
  simp

omit [DecidableEq I] in
theorem inv_wL_of_ge {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (a : Fin M) (ha : m ≤ a.val) :
    d⁻¹ a = ⟨a.val - m, by have := hM; have := a.2; omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  apply Fin.ext
  have := hM
  have := a.2
  rw [val_wL hd hcd, ite_eq_left (by simp; omega)]
  simp; omega

omit [DecidableEq I] in
/-- **`w_L` takes the loading with the block of `ν` last to the loading with it first.** -/
theorem smul_frontSeq_eq_endSeq {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (s : Seq (stendhalWeight 0 ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    d • frontSeq s t = endSeq s t := by
  apply Subtype.ext
  funext a
  change (frontSeq s t).lbl (d⁻¹ a) = (endSeq s t).lbl a
  by_cases ha : a.val < m
  · rw [inv_wL_of_lt hd hcd a ha, frontSeq_lbl_ge _ _ _ (by simp), endSeq_lbl_lt _ _ _ ha]
    congr 2
    apply Fin.ext
    simp
  · have hMN := hM
    have ha' := a.2
    have hlt : (⟨a.val - m, by omega⟩ : Fin M).val < N := by simp; omega
    rw [inv_wL_of_ge hd hcd a (by omega), frontSeq_lbl_lt _ _ _ hlt,
      endSeq_lbl_ge _ _ _ (by omega)]

/-! ### Intertwining on the basis terms -/

omit [DecidableEq I] in
theorem rename_wL {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (p₂ : MvPolynomial (Fin N) k) (p₁ : MvPolynomial (Fin m) k) :
    rename d (rename (frontPos (ℓ := 0) ν) p₂ * rename (suffixPos (ℓ := 0) ν₀) p₁) =
      rename (posL (ℓ := 0) ν₀) p₁ * rename (posR (ℓ := 0) ν) p₂ := by
  have h1 : (⇑d ∘ frontPos (ℓ := 0) ν) = posR (ℓ := 0) ν := by
    funext b
    apply Fin.ext
    rw [Function.comp_apply, val_wL hd hcd, ite_eq_left (by simp)]
    simp; omega
  have h2 : (⇑d ∘ suffixPos (ℓ := 0) ν₀) = posL (ℓ := 0) ν₀ := by
    funext a
    apply Fin.ext
    rw [Function.comp_apply, val_wL hd hcd, ite_eq_right (by simp)]
    simp
  rw [map_mul, rename_rename, rename_rename, h1, h2, mul_comm]

omit [DecidableEq I] in
theorem map_dShift_wL {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) {β α : List ℕ} (hβ : ValidWord N β) (hα : ValidWord m α) :
    (β ++ shiftWord N α).map (dShift d) = shiftWord m β ++ α := by
  have := hM
  rw [List.map_append, shiftWord, shiftWord, List.map_map]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    have hj' := hβ j hj
    rw [dShift, dite_eq_left (by omega), val_wL hd hcd, ite_eq_left (by simp; omega)]
    simp; omega
  · conv_rhs => rw [← List.map_id α]
    refine List.map_congr_left fun j hj => ?_
    have hj' := hα j hj
    rw [Function.comp_apply, dShift, dite_eq_left (by omega), val_wL hd hcd, ite_eq_right (by simp)]
    simp

theorem ψD_mul_basis_sub_mem {d : Perm (Fin M)} (hd : IsDoubleShuffle hM hK d)
    (hcd : crossCount m N d = m) (p₂ : MvPolynomial (Fin N) k) (p₁ : MvPolynomial (Fin m) k)
    {β α : List ℕ} (hβ : ValidWord N β) (hα : ValidWord m α)
    (s : Seq (stendhalWeight 0 ν)) (t : Seq (stendhalWeight 2 ν₀)) :
    (ψw (canWord M d) : Rp) *
        (pol (rename (frontPos (ℓ := 0) ν) p₂ * rename (suffixPos (ℓ := 0) ν₀) p₁) *
          ψw (β ++ shiftWord N α) * e (frontSeq s t)) -
      pol (rename (posL (ℓ := 0) ν₀) p₁ * rename (posR (ℓ := 0) ν) p₂) *
          ψw (α ++ shiftWord m β) * e (endSeq s t) * ψw (canWord M d) ∈ L := by
  have hMN := hM
  set D : Rp := ψw (canWord M d)
  set P := rename (frontPos (ℓ := 0) ν) p₂ * rename (suffixPos (ℓ := 0) ν₀) p₁
  set γ := β ++ shiftWord N α
  have hγ : ∀ j ∈ γ, j + 1 < M ∧ SameBlock m N (crossCount m N d) j := by
    intro j hj
    rw [hcd]
    rcases List.mem_append.1 hj with hj | hj
    · have := hβ j hj
      exact ⟨by omega, Or.inr (Or.inl ⟨by omega, this⟩)⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj
      have := hα l hl
      exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
  have hγr : ∀ j ∈ γ, j + 1 < N ∨ N ≤ j := by
    intro j hj
    rcases List.mem_append.1 hj with hj | hj
    · exact Or.inl (hβ j hj)
    · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hj
      exact Or.inr (by omega)
  have h1 := pol_rename_mul_ψD_sub_mem (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) hd P
  have h2 := ψw_map_mul_ψD_sub_mem (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) hd hγ
  rw [hcd] at h1 h2
  have he := ψD_mul_e (k := k) (Q := stendhalQ Q (plusLabels Λ Λc 0 le_rfl)) (d := d)
    (frontSeq s t)
  rw [smul_frontSeq_eq_endSeq hd hcd] at he
  rw [map_dShift_wL hd hcd hβ hα] at h2
  have hcomm : (ψw (shiftWord m β ++ α) : Rp) = ψw (α ++ shiftWord m β) := by
    rw [ψw_append, ψw_append]
    refine (commute_ψw_ψw_of_far fun j hj l hl => ?_).eq
    obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
    have := hα l hl
    omega
  rw [hcomm] at h2
  rw [← rename_wL hd hcd p₂ p₁]
  have key : D * (pol P * ψw γ * e (frontSeq s t)) -
      pol (rename d P) * ψw (α ++ shiftWord m β) * e (endSeq s t) * D =
      -((pol (rename d P) * D - D * pol P) * ψw γ * e (frontSeq s t)) -
        pol (rename d P) * (ψw (α ++ shiftWord m β) * D - D * ψw γ) * e (frontSeq s t) := by
    rw [mul_assoc _ (e (endSeq s t)), ← he]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  rw [key]
  refine sub_mem (neg_mem (mackeyLower_mul_e _ (mackeyLower_mul_ψw hγr h1))) ?_
  exact mackeyLower_mul_e _ (mackeyLower_pol_mul _ h2)

/-! ### Stability of `F_{c-1}` -/

private theorem endMapKLR_smul' (c : k) (y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ (c • y) = c • endMapKLR Q Λ Λc ν ν₀ y := by
  unfold endMapKLR
  rw [map_smul, AlgHom.map_smul_of_tower, KLR.Corner.val_smul]

private theorem endMapKLR_zero' : endMapKLR Q Λ Λc ν ν₀ 0 = 0 := by
  unfold endMapKLR; rw [map_zero, map_zero]; rfl

variable {c : ℕ}

local notation "Lc" => mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
  (stendhalWeight (0 + 2) (ν + ν₀)) m N c

/-- `F_{c-1}` is stable under left multiplication by `ν`-diagrams on the first `m` strands. -/
theorem prefixMapKLR_mul_mem (hQ : KLRSymm Q)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight 0 ν)) {y : Rp}
    (hy : y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c) :
    prefixMapKLR Q Λ Λc ν ν₀ a * y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c := by
  refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λ) hQ)
    (P := fun a => ∀ y : Rp, y ∈ Lc → prefixMapKLR Q Λ Λc ν ν₀ a * y ∈ Lc) ?_ ?_ ?_ ?_ a y hy
  · intro y _; rw [prefixMapKLR_zero, zero_mul]; exact zero_mem _
  · intro a b ha hb y hy; rw [prefixMapKLR_add, add_mul]; exact add_mem (ha y hy) (hb y hy)
  · intro r a ha y hy
    rw [prefixMapKLR_smul, smul_mul_assoc]; exact Submodule.smul_mem _ r (ha y hy)
  · intro u α hα s y hy
    rw [prefixMapKLR_mul, prefixMapKLR_mul, prefixMapKLR_pol, prefixMapKLR_ψw hα, prefixMapKLR_e]
    simp only [mul_assoc]
    refine mackeyLower_pol_mul _ (mackeyLower_eSum_mul _ (mackeyLower_ψw_mul
      (fun j hj => Or.inl (hα j hj)) (mackeyLower_eSum_mul _ (mackeyLower_eSum_mul _ hy))))

/-- `F_{c-1}` is stable under left multiplication by diagrams at the maximum on the last `N`
strands. -/
theorem endMapKLR_mul_mem (hQ : KLRSymm Q)
    (b : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) {y : Rp}
    (hy : y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c) :
    endMapKLR Q Λ Λc ν ν₀ b * y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c := by
  refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λc) hQ)
    (P := fun b => ∀ y : Rp, y ∈ Lc → endMapKLR Q Λ Λc ν ν₀ b * y ∈ Lc) ?_ ?_ ?_ ?_ b y hy
  · intro y _; rw [endMapKLR_zero', zero_mul]; exact zero_mem _
  · intro a b ha hb y hy; rw [endMapKLR_add, add_mul]; exact add_mem (ha y hy) (hb y hy)
  · intro r a ha y hy; rw [endMapKLR_smul', smul_mul_assoc]; exact Submodule.smul_mem _ r (ha y hy)
  · intro u β hβ t y hy
    rw [endMapKLR_mul, endMapKLR_mul, endMapKLR_pol, endMapKLR_ψw hβ, endMapKLR_e_eq_sum]
    simp only [mul_assoc, Finset.sum_mul]
    refine mackeyLower_pol_mul _ (mackeyLower_eSum_mul _ (mackeyLower_ψw_mul
      (fun j hj => ?_) (mackeyLower_eSum_mul _ (Submodule.sum_mem _ fun s _ =>
        mackeyLower_e_mul _ hy))))
    obtain ⟨j', -, rfl⟩ := List.mem_map.1 hj
    exact Or.inr (by omega)

/-- `F_{c-1}` is stable under right multiplication by diagrams at the maximum on the first `N`
strands. -/
theorem mul_frontMapKLR_mem (hQ : KLRSymm Q)
    (b : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) {y : Rp}
    (hy : y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c) :
    y * frontMapKLR Q Λ Λc ν ν₀ b ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c := by
  refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λc) hQ)
    (P := fun b => ∀ y : Rp, y ∈ Lc → y * frontMapKLR Q Λ Λc ν ν₀ b ∈ Lc) ?_ ?_ ?_ ?_ b y hy
  · intro y _; rw [frontMapKLR_zero, mul_zero]; exact zero_mem _
  · intro a b ha hb y hy; rw [frontMapKLR_add, mul_add]; exact add_mem (ha y hy) (hb y hy)
  · intro r a ha y hy; rw [frontMapKLR_smul, mul_smul_comm]; exact Submodule.smul_mem _ r (ha y hy)
  · intro u β hβ t y hy
    rw [frontMapKLR_mul, frontMapKLR_mul, frontMapKLR_pol, frontMapKLR_ψw hβ,
      frontMapKLR_e_eq_sum]
    simp only [← mul_assoc, Finset.mul_sum]
    refine Submodule.sum_mem _ fun s _ => mackeyLower_mul_e _ (mackeyLower_mul_eSum _
      (mackeyLower_mul_ψw (fun j hj => Or.inl (hβ j hj)) (mackeyLower_mul_eSum _
        (mackeyLower_mul_pol _ hy))))

/-- `F_{c-1}` is stable under right multiplication by `ν`-diagrams on the last `m` strands. -/
theorem mul_suffixMapKLR_mem (hQ : KLRSymm Q)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight 0 ν)) {y : Rp}
    (hy : y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c) :
    y * suffixMapKLR Q Λ Λc ν ν₀ a ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc 0 le_rfl))
      (stendhalWeight (0 + 2) (ν + ν₀)) m N c := by
  refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λ) hQ)
    (P := fun a => ∀ y : Rp, y ∈ Lc → y * suffixMapKLR Q Λ Λc ν ν₀ a ∈ Lc) ?_ ?_ ?_ ?_ a y hy
  · intro y _; rw [suffixMapKLR_zero, mul_zero]; exact zero_mem _
  · intro a b ha hb y hy; rw [suffixMapKLR_add, mul_add]; exact add_mem (ha y hy) (hb y hy)
  · intro r a ha y hy; rw [suffixMapKLR_smul, mul_smul_comm]; exact Submodule.smul_mem _ r (ha y hy)
  · intro u α hα s y hy
    rw [suffixMapKLR_mul, suffixMapKLR_mul, suffixMapKLR_pol, suffixMapKLR_ψw hα,
      suffixMapKLR_e]
    simp only [← mul_assoc]
    refine mackeyLower_mul_eSum _ (mackeyLower_mul_eSum _ (mackeyLower_mul_ψw (fun j hj => ?_)
      (mackeyLower_mul_eSum _ (mackeyLower_mul_pol _ hy))))
    obtain ⟨j', -, rfl⟩ := List.mem_map.1 hj
    exact Or.inr (by omega)

/-! ### Intertwining -/

/-- **The longest block crossing intertwines the two block embeddings modulo `F_{m-1}`**:
`ψ_{w_L} (b ⊗ a)_right - (a ⊗ b)_left ψ_{w_L} ∈ F_{m-1}`, where the right embedding puts `b` on
the first `N` strands and `a` on the last `m`, and the left one puts `a` on the first `m` strands
and `b` on the last `N`. -/
theorem ψD_mul_frontSuffix_sub_mem (hQ : KLRSymm Q) {d : Perm (Fin M)}
    (hd : IsDoubleShuffle hM hK d) (hcd : crossCount m N d = m)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight 0 ν))
    (b : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    (ψw (canWord M d) : Rp) * (frontMapKLR Q Λ Λc ν ν₀ b * suffixMapKLR Q Λ Λc ν ν₀ a) -
      prefixMapKLR Q Λ Λc ν ν₀ a * endMapKLR Q Λ Λc ν ν₀ b * ψw (canWord M d) ∈ L := by
  set D : Rp := ψw (canWord M d)
  revert b
  refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) (P := fun a => ∀ b, D *
    (frontMapKLR Q Λ Λc ν ν₀ b * suffixMapKLR Q Λ Λc ν ν₀ a) - prefixMapKLR Q Λ Λc ν ν₀ a *
      endMapKLR Q Λ Λc ν ν₀ b * D ∈ L) ?_ ?_ ?_ ?_ a
  · intro b; rw [suffixMapKLR_zero, prefixMapKLR_zero]; simp
  · intro a a' ha ha' b
    have := add_mem (ha b) (ha' b)
    rw [suffixMapKLR_add, prefixMapKLR_add]
    convert this using 1
    simp only [mul_add, add_mul]; abel
  · intro r a ha b
    have := Submodule.smul_mem _ r (ha b)
    rw [suffixMapKLR_smul, prefixMapKLR_smul]
    convert this using 1
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  · intro u α hα s b
    refine klr_induction (stendhalQ_symm (Q := Q) (Λ := Λc) hQ) (P := fun b => D *
      (frontMapKLR Q Λ Λc ν ν₀ b * suffixMapKLR Q Λ Λc ν ν₀ (pol (monomial u 1) * ψw α * e s)) -
        prefixMapKLR Q Λ Λc ν ν₀ (pol (monomial u 1) * ψw α * e s) *
          endMapKLR Q Λ Λc ν ν₀ b * D ∈ L) ?_ ?_ ?_ ?_ b
    · rw [frontMapKLR_zero, endMapKLR_zero']; simp
    · intro b b' hb hb'
      have := add_mem hb hb'
      rw [frontMapKLR_add, endMapKLR_add]
      convert this using 1
      simp only [mul_add, add_mul]; abel
    · intro r b hb
      have := Submodule.smul_mem _ r hb
      rw [frontMapKLR_smul, endMapKLR_smul']
      convert this using 1
      simp only [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_sub]
    · intro u' β hβ t
      rw [frontMapKLR_mul_suffixMapKLR _ _ hβ hα, prefixMapKLR_mul_endMapKLR _ _ hα hβ]
      exact ψD_mul_basis_sub_mem hd hcd _ _ hβ hα s t

end Categorification.Stendhal.CupCap
