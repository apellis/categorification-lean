/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSplit

/-!
# Left block inclusions of KLR algebras and their intertwiners

The induction functors of Khovanov–Lauda I (arXiv:0803.4121v2, §2.6) and of Kang–Kashiwara
(arXiv:1102.4677v4, §4.2) add strands on the right. Iterating them gives nonunital maps
`f : R(γ) → R(δ)` which put a diagram on the first `card γ` strands and add strands with
prescribed labels `w 0, w 1, …` on the right. `IsLeftBlock f w` records exactly what is
needed about such a map: `f(e(s)) = e(t)` where `t` is `s` followed by `w`, and `f` sends the
dots and crossings of `R(γ)` to the same dots and crossings of `R(δ)`, cut by `f 1`.

* `IsLeftBlock.intertwines` : if `c ∈ R(δ)` commutes with the dots and crossings on the
  first `card γ` strands, and `e(s w) c = c e(s w')` for every `s`, then
  `f r * c = c * g r` for all `r`. This is the input to the element natural transformations
  of `Categorification.InductionAlong`.
* `lastIncl i h` : `R(β) → R(δ)` for `{i} + β = δ`, the inclusion adding a last strand
  labelled `i` (`isLeftBlock_lastIncl`), and `IsLeftBlock.comp` for composites.
* `IsLeftBlock.intertwines_dot`, `IsLeftBlock.intertwines_cross` : a dot on an added strand
  intertwines a block with itself; the crossing `ψ_{card γ + q}` of two added strands
  intertwines the block with the block whose labels `q`, `q + 1` are exchanged.

Everything is ungraded and holds over any commutative ring, for any `Q`.
-/

namespace Categorification.KLR

open Equiv TypeA

namespace KLRAlgebra

universe u v

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

/-- `t` is the sequence `s` followed by the labels `w 0, w 1, …`. -/
def Labels {γ δ : Multiset I} (s : Seq γ) (w : ℕ → I) (t : Seq δ) : Prop :=
  ∀ c : Fin (Multiset.card δ),
    t.1 c = if h : c.val < Multiset.card γ then s.1 ⟨c.val, h⟩ else w (c.val - Multiset.card γ)

omit [DecidableEq I] in
theorem Labels.unique {γ δ : Multiset I} {s : Seq γ} {w : ℕ → I} {t t' : Seq δ}
    (h : Labels s w t) (h' : Labels s w t') : t = t' :=
  Subtype.ext (funext fun c => by rw [h c, h' c])

/-- `f` puts `R(γ)` on the first strands of `R(δ)` and adds strands labelled `w`. -/
structure IsLeftBlock {γ δ : Multiset I} (f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ)
    (w : ℕ → I) : Prop where
  card_le : Multiset.card γ ≤ Multiset.card δ
  e_eq : ∀ s : Seq γ, ∃ t : Seq δ, f (e s) = e t ∧ Labels s w t
  x_eq : ∀ a : Fin (Multiset.card γ),
    f (x a) = x ⟨a.val, lt_of_lt_of_le a.2 card_le⟩ * f 1
  ψ_eq : ∀ l : ℕ, l + 1 < Multiset.card γ → f (ψ l) = ψ l * f 1

namespace IsLeftBlock

variable {γ β δ : Multiset I}

/-- Every element of `R(ν)` is reached from the generators by sums, products and scalars. -/
theorem induction {ν : Multiset I} {motive : KLRAlgebra k Q ν → Prop}
    (scalar : ∀ c : k, motive (algebraMap k _ c))
    (he : ∀ s, motive (e s)) (hx : ∀ a, motive (x a)) (hψ : ∀ j, motive (ψ j))
    (add : ∀ r r', motive r → motive r' → motive (r + r'))
    (mul : ∀ r r', motive r → motive r' → motive (r * r')) (r : KLRAlgebra k Q ν) :
    motive r := by
  obtain ⟨u, rfl⟩ := mk_surjective r
  induction u using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact scalar c
  | grade1 g =>
    cases g with
    | idem s => exact he s
    | dot a => exact hx a
    | cross j => exact hψ j
  | mul u u' hu hu' => rw [map_mul]; exact mul _ _ hu hu'
  | add u u' hu hu' => rw [map_add]; exact add _ _ hu hu'

theorem map_one_eq {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} :
    f 1 = ∑ s : Seq γ, f (e s) := by
  rw [← map_sum, sum_e]

/-- **Intertwiners of left blocks.** -/
theorem intertwines {f g : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w w' : ℕ → I}
    (hf : IsLeftBlock f w) (hg : IsLeftBlock g w') (c : KLRAlgebra k Q δ)
    (hx : ∀ a : Fin (Multiset.card δ), a.val < Multiset.card γ → Commute (x a) c)
    (hψ : ∀ l : ℕ, l + 1 < Multiset.card γ → Commute (ψ l) c)
    (he : ∀ (s : Seq γ) (t t' : Seq δ), Labels s w t → Labels s w' t' → e t * c = c * e t')
    (r : KLRAlgebra k Q γ) : f r * c = c * g r := by
  have hes : ∀ s : Seq γ, f (e s) * c = c * g (e s) := fun s => by
    obtain ⟨t, ht, hl⟩ := hf.e_eq s
    obtain ⟨t', ht', hl'⟩ := hg.e_eq s
    rw [ht, ht']
    exact he s t t' hl hl'
  have h1 : f 1 * c = c * g 1 := by
    rw [map_one_eq, map_one_eq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => hes s
  induction r using induction with
  | scalar a =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, smul_mul_assoc, h1,
      mul_smul_comm]
  | he s => exact hes s
  | hx a =>
    rw [hf.x_eq, hg.x_eq, mul_assoc, h1, ← mul_assoc, (hx _ a.2).eq, mul_assoc]
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card γ
    · rw [hf.ψ_eq j hj, hg.ψ_eq j hj, mul_assoc, h1, ← mul_assoc, (hψ j hj).eq, mul_assoc]
    · rw [ψ_eq_zero j (by omega), map_zero, map_zero, zero_mul, mul_zero]
  | add r r' hr hr' => rw [map_add, map_add, add_mul, mul_add, hr, hr']
  | mul r r' hr hr' => rw [map_mul, map_mul, mul_assoc, hr', ← mul_assoc, hr, mul_assoc]

/-- Only the labels of the added strands matter. -/
theorem congr_word {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w w' : ℕ → I}
    (hf : IsLeftBlock f w)
    (hw : ∀ n, n + Multiset.card γ < Multiset.card δ → w n = w' n) : IsLeftBlock f w' where
  card_le := hf.card_le
  e_eq s := by
    obtain ⟨t, ht, hl⟩ := hf.e_eq s
    refine ⟨t, ht, fun c => ?_⟩
    rw [hl c]
    by_cases hc : c.val < Multiset.card γ
    · simp [hc]
    · simp only [hc, dite_false]
      exact hw _ (by omega)
  x_eq := hf.x_eq
  ψ_eq := hf.ψ_eq

/-- A dot on an added strand intertwines a left block with itself. -/
theorem intertwines_dot {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w : ℕ → I}
    (hf : IsLeftBlock f w) (p : Fin (Multiset.card δ)) (hp : Multiset.card γ ≤ p.val)
    (r : KLRAlgebra k Q γ) : f r * x p = x p * f r :=
  hf.intertwines hf (x p) (fun a _ => x_mul_x a p)
    (fun l hl => (x_mul_ψ p l (by omega) (by omega)).symm)
    (fun s t t' hl hl' => by rw [hl.unique hl']; exact (x_mul_e p t').symm) r

/-- Exchanging two neighbouring added labels. -/
def swapAt (w : ℕ → I) (q : ℕ) : ℕ → I :=
  fun n => if n = q then w (q + 1) else if n = q + 1 then w q else w n

theorem sadj_smul_of_labels {s : Seq γ} {w : ℕ → I} {t t' : Seq δ} (q : ℕ)
    (hq : Multiset.card γ + q + 1 < Multiset.card δ)
    (hl : Labels s w t) (hl' : Labels s (swapAt w q) t') :
    sadj (Multiset.card δ) (Multiset.card γ + q) • t' = t := by
  apply Subtype.ext
  funext c
  rw [Seq.smul_apply, ← Perm.inv_def, sadj_inv, sadj_eq_swap hq, hl c]
  rcases c with ⟨c, hc⟩
  have e1 : Multiset.card γ + q + 1 - Multiset.card γ = q + 1 := by omega
  have e0 : Multiset.card γ + q - Multiset.card γ = q := by omega
  by_cases h1 : c = Multiset.card γ + q
  · subst h1
    rw [swap_apply_left, hl']
    simp [swapAt, e0, e1]
    omega
  · by_cases h2 : c = Multiset.card γ + q + 1
    · subst h2
      rw [swap_apply_right, hl']
      simp [swapAt, e0, e1]
      omega
    · rw [swap_apply_of_ne_of_ne (fun h => h1 (congrArg Fin.val h))
        (fun h => h2 (congrArg Fin.val h)), hl']
      by_cases h3 : c < Multiset.card γ
      · simp [h3]
      · simp only [h3, dite_false, swapAt]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The crossing `ψ_{card γ + q}` of two added strands intertwines a left block with the
block whose added labels `q`, `q + 1` are exchanged. -/
theorem intertwines_cross {f g : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w : ℕ → I}
    (hf : IsLeftBlock f w) (hg : IsLeftBlock g (swapAt w q))
    (hq : Multiset.card γ + q + 1 < Multiset.card δ) (r : KLRAlgebra k Q γ) :
    f r * ψ (Multiset.card γ + q) = ψ (Multiset.card γ + q) * g r :=
  hf.intertwines hg _ (fun a ha => x_mul_ψ a _ (by omega) (by omega))
    (fun l hl => ψ_mul_ψ l _ (by omega))
    (fun s t t' hl hl' => by
      rw [ψ_mul_e, sadj_smul_of_labels q hq hl hl']) r

/-- Composites of left blocks are left blocks. -/
theorem comp {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q β}
    {g : KLRAlgebra k Q β →ₙₐ[k] KLRAlgebra k Q δ} {w w' : ℕ → I}
    (hf : IsLeftBlock f w) (hg : IsLeftBlock g w') :
    IsLeftBlock (g.comp f) (fun n => if n < Multiset.card β - Multiset.card γ then w n
      else w' (n - (Multiset.card β - Multiset.card γ))) where
  card_le := hf.card_le.trans hg.card_le
  e_eq s := by
    obtain ⟨t, ht, hl⟩ := hf.e_eq s
    obtain ⟨t', ht', hl'⟩ := hg.e_eq t
    refine ⟨t', by rw [NonUnitalAlgHom.comp_apply, ht, ht'], fun c => ?_⟩
    have hγβ := hf.card_le
    rw [hl' c]
    by_cases hc : c.val < Multiset.card β
    · rw [dite_eq_left hc, hl ⟨c.val, hc⟩]
      by_cases hc' : c.val < Multiset.card γ
      · simp [hc']
      · simp only [hc', dite_false]
        rw [ite_eq_left (by omega)]
    · rw [dite_eq_right hc, dite_eq_right (by omega)]
      dsimp only
      rw [ite_eq_right (by omega)]
      congr 1
      omega
  x_eq a := by
    rw [NonUnitalAlgHom.comp_apply, hf.x_eq, map_mul, hg.x_eq, mul_assoc, ← map_mul, one_mul]
    rfl
  ψ_eq l hl := by
    rw [NonUnitalAlgHom.comp_apply, hf.ψ_eq l hl, map_mul, hg.ψ_eq l (by
      have := hf.card_le; omega), mul_assoc, ← map_mul, one_mul]
    rfl

end IsLeftBlock

/-! ### The last-strand inclusion -/

section Last

variable (Q) in
/-- The inclusion `R(β) → R(δ)` adding a last strand labelled `i`, for `{i} + β = δ`. -/
noncomputable def lastIncl (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    KLRAlgebra k Q β →ₙₐ[k] KLRAlgebra k Q δ where
  toFun r := castKLR Q h (cL Q i β r)
  map_zero' := by rw [cL_zero, map_zero]
  map_add' r r' := by rw [cL_add, map_add]
  map_smul' c r := by rw [cL_smul, map_smul]; rfl
  map_mul' r r' := by rw [cL_mul, map_mul]

theorem lastIncl_apply (i : I) {β δ : Multiset I} (h : {i} + β = δ) (r : KLRAlgebra k Q β) :
    lastIncl Q i h r = castKLR Q h (cL Q i β r) := rfl

omit [DecidableEq I] in
theorem card_lastIncl (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    Multiset.card δ = Multiset.card β + 1 := by
  rw [← h, Multiset.card_add, Multiset.card_singleton, add_comm]

/-- The last-strand inclusion is a left block with constant added label `i`. -/
theorem isLeftBlock_lastIncl (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    IsLeftBlock (lastIncl Q i h) (fun _ => i) where
  card_le := by rw [card_lastIncl i h]; omega
  e_eq s := by
    refine ⟨_, by rw [lastIncl_apply, cL_e, castKLR_e], fun c => ?_⟩
    rw [Seq.cast_apply, Seq.cast_apply]
    by_cases hc : c.val < Multiset.card β
    · rw [Seq.append_apply_lt _ _ _ hc, dite_eq_left hc]
      rfl
    · rw [Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega), dite_eq_right hc]
      exact Multiset.mem_singleton.1 (Seq.mem _ _)
  x_eq a := by
    rw [lastIncl_apply, cL_x, map_mul, castKLR_x]
    rfl
  ψ_eq l hl := by
    rw [lastIncl_apply, cL_ψ i β hl, map_mul, castKLR_ψ]
    rfl

end Last

end KLRAlgebra

end Categorification.KLR
