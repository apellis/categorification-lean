/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorization

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: non-additive pairs

Part of the proof of Webster, arXiv:1309.3796v2, Lemma 6.5. Fix a reduced word `ρ w` for each
permutation `w`. The class `pgen u v p i` of `ψ_u ⊗ ψ_v x^p e(i)` in the tensor product over
the middle corner (`BraidedStendhalAlgebra.pgen`) only depends, modulo lower degree, on the
diagram obtained by stacking: a simple transposition can be moved across the tensor sign
(`pgen_move`), and when the stacked diagram is not reduced the class lies in lower degree
(`pgen_mem_low_of_lt`), provided every crossing of two red strands in `v` survives in `u v`.
This is the part of Webster's argument in which no relation between red strands is used.
-/

namespace Categorification.TypeA

open Equiv

/-- `ρ` chooses a reduced word for every permutation. -/
def IsReducedChoice {n : ℕ} (ρ : Perm (Fin n) → List ℕ) : Prop :=
  ∀ w, IsReduced n (ρ w) ∧ wordProd n (ρ w) = w

end Categorification.TypeA

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)}

omit [DecidableEq I] in
theorem lbl_smul (w : Perm (Fin m)) (i : Seq μ) (a : Fin m) : (w • i).lbl a = i.lbl (w⁻¹ a) :=
  rfl

theorem e_mul_std (β : List ℕ) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (KLRAlgebra.e (wordProd m β • i) * (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) :
      R) = KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i := by
  rw [← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_ψw, inv_smul_smul, mul_assoc (KLRAlgebra.ψw β),
    (KLRAlgebra.e_commute_pol _ p).eq, mul_assoc, mul_assoc, KLRAlgebra.e_mul_e,
    ite_eq_left (Eq.refl i), ← mul_assoc]

/-- `gen x (ψ_β x^p e(i))` vanishes unless the red strands of `β • i` read `κ₁`. -/
theorem gen_eq_zero_of_redWord_ne (x : R) (β : List ℕ) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) (h : redWord (wordProd m β • i) ≠ κ₁) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (KLRAlgebra.ψw β * KLRAlgebra.pol p * KLRAlgebra.e i) =
      0 := by
  rw [← e_mul_std, ← gen_mul_redIdem,
    gen_mul_corner _ _ _ (redIdem_mul_redIdem κ₁) (redIdem_mul_redIdem κ₁), ← mul_assoc,
    redIdem_mul_e, ite_eq_right h, zero_mul, gen_zero_right]

/-- The class of `ψ_u ⊗ ψ_v x^p e(i)`, with `ψ_w` built on the chosen word `ρ w`. -/
noncomputable def pgen (ρ : Perm (Fin m) → List ℕ) (u v : Perm (Fin m))
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁)
      (redProj k Q Λ ν κ₀) :=
  gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw (ρ u)) (KLRAlgebra.ψw (ρ v) * KLRAlgebra.pol p * KLRAlgebra.e i)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ)
include hρ

omit [DecidableEq I] in
theorem length_word (w : Perm (Fin m)) : (ρ w).length = length m w := by
  rw [(hρ w).1.2, (hρ w).2]

theorem pgen_mem_low (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    pgen ρ u v p i ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (length m u + length m v) := by
  rw [← length_word hρ, ← length_word hρ]
  exact gen_mem_low (hρ u).1.1 (hρ v).1.1 le_rfl p i

theorem pgen_eq_zero (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord (v • i) ≠ κ₁) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v p i = 0 :=
  gen_eq_zero_of_redWord_ne _ _ p i (by rwa [(hρ v).2])

omit [DecidableEq I] in
theorem isReduced_append_singleton {u : Perm (Fin m)} {c : ℕ} (hc : c + 1 < m)
    (hu : length m (u * sadj m c) + 1 = length m u) : IsReduced m (ρ (u * sadj m c) ++ [c]) := by
  refine (isReduced_iff_length_le (validWord_append.2 ⟨(hρ _).1.1,
    validWord_cons.2 ⟨hc, fun _ h => by simp at h⟩⟩)).2 ?_
  rw [wordProd_append, (hρ _).2, wordProd_singleton, mul_assoc, sadj_mul_self, mul_one,
    List.length_append, length_word hρ]
  simp [hu]

omit [DecidableEq I] in
theorem isReduced_cons {v : Perm (Fin m)} {c : ℕ} (hc : c + 1 < m)
    (hv : length m v + 1 = length m (sadj m c * v)) : IsReduced m (c :: ρ v) := by
  refine (isReduced_iff_length_le (validWord_cons.2 ⟨hc, (hρ _).1.1⟩)).2 ?_
  rw [wordProd_cons, (hρ _).2, List.length_cons, length_word hρ, hv]

/-- **Moving a simple transposition across the tensor sign.** If `s_c` is a right descent of
`u` and a left ascent of `v`, and the red strands between the two halves read `κ₁` both
before and after `s_c`, then `ψ_u ⊗ ψ_v ≡ ψ_{u s_c} ⊗ ψ_{s_c v}` in lower degree. -/
theorem pgen_move {u v : Perm (Fin m)} {c : ℕ} (hc : c + 1 < m)
    (hu : length m (u * sadj m c) + 1 = length m u)
    (hv : length m v + 1 = length m (sadj m c * v)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (hr : redWord (v • i) = κ₁) (hr' : redWord ((sadj m c * v) • i) = κ₁) :
    pgen ρ u v p i - pgen ρ (u * sadj m c) (sadj m c * v) p i ∈
      low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (length m u + length m v - 1) := by
  have hA := isReduced_append_singleton hρ hc hu
  have hB := isReduced_cons hρ hc hv
  have h1 := gen_sub_mem_low_of_braidEquiv_left (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
    (Q := Q) (Λ := Λ)
    (braidEquiv_of_isReduced (hρ u).1 hA (by
      rw [(hρ u).2, wordProd_append, (hρ _).2, wordProd_singleton, mul_assoc, sadj_mul_self,
        mul_one])) (hρ u).1.1 (hρ v).1.1 p i
  have h2 := gen_append_eq (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) (Q := Q) (Λ := Λ) (ρ (u * sadj m c)) [c]
    (ρ v) p i (by rwa [(hρ v).2]) (by rwa [List.singleton_append, wordProd_cons, (hρ v).2])
  have h3 := gen_sub_mem_low_of_braidEquiv_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
    (Q := Q) (Λ := Λ)
    (braidEquiv_of_isReduced hB (hρ (sadj m c * v)).1 (by rw [wordProd_cons, (hρ v).2,
      (hρ _).2])) (hρ (u * sadj m c)).1.1 p i
  rw [h2, List.singleton_append] at h1
  rw [length_word hρ, length_word hρ] at h1
  rw [List.length_cons, length_word hρ, length_word hρ] at h3
  have := add_mem h1 (low_mono (by omega) h3)
  rwa [sub_add_sub_cancel] at this

/-- **Non-additive pairs lie in lower degree.** If `ℓ(u v) < ℓ(u) + ℓ(v)` and every crossing of
two red strands in `v` is a crossing of `u v`, then `ψ_u ⊗ ψ_v x^p e(i)` lies in degree
`ℓ(u) + ℓ(v) - 1`. -/
theorem pgen_mem_low_of_lt (p : MvPolynomial (Fin m) k) (i : Seq μ) {u v : Perm (Fin m)}
    (hred : ColourAdditive (fun s => (i.lbl s).isRight) u v)
    (h : length m (u * v) < length m u + length m v) :
    pgen ρ u v p i ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (length m u + length m v - 1) := by
  -- the red strands are not both red at the positions `c, c + 1` between `u` and `v`
  have hred' : ∀ (v : Perm (Fin m)) (c g : Fin m), g.val = c.val + 1 →
      ¬ ((i.lbl (v⁻¹ c)).isRight ∧ (i.lbl (v⁻¹ g)).isRight) →
      redWord (v • i) = κ₁ → redWord ((sadj m c * v) • i) = κ₁ := by
    intro v c g hg hnr hr
    have hc : c.val + 1 < m := hg ▸ g.2
    rw [mul_smul, redWord_sadj_smul (v • i) hc ?_]
    · exact hr
    rw [lbl_smul, lbl_smul, show (⟨c.val + 1, hc⟩ : Fin m) = g from Fin.ext hg.symm]
    exact hnr
  refine cancel_induction (fun s => (i.lbl s).isRight)
    (P := fun u v => pgen ρ u v p i ∈ low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀
      (length m u + length m v - 1)) ?_ ?_ ?_ hred h
  · intro u v c g hg hu hv hnr
    have hc : c.val + 1 < m := hg ▸ g.2
    have hg' : (⟨c.val + 1, hc⟩ : Fin m) = g := Fin.ext hg.symm
    by_cases hr : redWord (v • i) = κ₁
    swap
    · rw [pgen_eq_zero hρ u v p i hr]; exact zero_mem _
    have hr' := hred' v c g hg hnr hr
    have hlu := length_mul_sadj_of_gt hc (w := u) (by rw [hg']; exact hu)
    have hlv := length_sadj_mul_of_gt hc (w := v) (by rw [hg']; exact hv)
    have hA := isReduced_append_singleton hρ hc hlu
    have hB := isReduced_cons hρ hc (v := sadj m c * v)
      (by rw [← mul_assoc, sadj_mul_self, one_mul, hlv])
    have h1 := gen_sub_mem_low_of_braidEquiv_left (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ)
      (braidEquiv_of_isReduced (hρ u).1 hA (by
        rw [(hρ u).2, wordProd_append, (hρ _).2, wordProd_singleton, mul_assoc, sadj_mul_self,
          mul_one])) (hρ u).1.1 (hρ v).1.1 p i
    have h2 := gen_sub_mem_low_of_braidEquiv_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ)
      (braidEquiv_of_isReduced (hρ v).1 hB (by
        rw [(hρ v).2, wordProd_cons, (hρ _).2, ← mul_assoc, sadj_mul_self, one_mul]))
      hA.1 p i
    have h3 := gen_append_eq (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) (Q := Q) (Λ := Λ)
      (ρ (u * sadj m c)) [(c : ℕ)]
      ((c : ℕ) :: ρ (sadj m c * v)) p i
      (by rwa [wordProd_cons, (hρ _).2, ← mul_assoc, sadj_mul_self, one_mul])
      (by rwa [List.singleton_append, wordProd_cons, wordProd_cons, (hρ _).2, ← mul_assoc,
        sadj_mul_self, one_mul])
    have h4 := gen_mem_low_of_hasRepeat_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ) (β := [(c : ℕ)] ++ (c : ℕ) :: ρ (sadj m c * v))
      ⟨[], ρ (sadj m c * v), (c : ℕ), rfl⟩
      (hρ (u * sadj m c)).1.1 p i
    rw [length_word hρ, length_word hρ] at h1
    rw [List.length_append, length_word hρ, length_word hρ] at h2
    simp only [List.length_append, List.length_cons, List.length_nil, length_word hρ] at h4
    rw [h3] at h2
    have := add_mem (add_mem h1 (low_mono (by simp; omega) h2)) (low_mono (by simp; omega) h4)
    rwa [sub_add_sub_cancel, sub_add_cancel] at this
  · intro u v c g hg hu hv hnr ih
    have hc : c.val + 1 < m := hg ▸ g.2
    have hg' : (⟨c.val + 1, hc⟩ : Fin m) = g := Fin.ext hg.symm
    by_cases hr : redWord (v • i) = κ₁
    swap
    · rw [pgen_eq_zero hρ u v p i hr]; exact zero_mem _
    have hlu := length_mul_sadj_of_gt hc (w := u) (by rw [hg']; exact hu)
    have hlv := length_sadj_mul_of_lt hc (w := v) (by rw [hg']; exact hv)
    have hm := pgen_move (κ₂ := κ₂) (κ₀ := κ₀) (Q := Q) (Λ := Λ) hρ hc hlu hlv.symm p i hr
      (hred' v c g hg hnr hr)
    have := add_mem hm (low_mono (by omega) ih)
    rwa [sub_add_cancel] at this
  · intro u v c g hg hu hv hnr ih
    have hc : c.val + 1 < m := hg ▸ g.2
    have hg' : (⟨c.val + 1, hc⟩ : Fin m) = g := Fin.ext hg.symm
    by_cases hr : redWord (v • i) = κ₁
    swap
    · rw [pgen_eq_zero hρ u v p i hr]; exact zero_mem _
    have hr' := hred' v c g hg hnr hr
    have hlu := length_mul_sadj_of_lt hc (w := u) (by rw [hg']; exact hu)
    have hlv := length_sadj_mul_of_gt hc (w := v) (by rw [hg']; exact hv)
    have hm := pgen_move (κ₂ := κ₂) (κ₀ := κ₀) (Q := Q) (Λ := Λ) hρ hc (u := u * sadj m c)
      (v := sadj m c * v) (by rw [mul_assoc, sadj_mul_self, mul_one, hlu])
      (by rw [← mul_assoc, sadj_mul_self, one_mul, hlv]) p i hr'
      (by rwa [← mul_assoc, sadj_mul_self, one_mul])
    rw [mul_assoc, sadj_mul_self, mul_one, ← mul_assoc, sadj_mul_self, one_mul] at hm
    have := sub_mem ih (low_mono (by omega) hm)
    rw [sub_sub_cancel] at this
    rwa [show length m (u * sadj m c) + length m (sadj m c * v) - 1 =
      length m u + length m v - 1 by omega] at this

end BraidedStendhalAlgebra

end Categorification.Stendhal
