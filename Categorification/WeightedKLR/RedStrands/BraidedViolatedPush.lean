/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationLength
import Categorification.TypeA.ExitsPrefix

set_option backward.isDefEq.respectTransparency false

/-!
# Pushing violated idempotents through a red crossing

Let `e(i)` be a violated idempotent (its leftmost strand is black) whose red strands read
`κ = L ++ a :: b :: M`, and let `κ' = L ++ b :: a :: M`. Every element `e_{κ'} w e(i)` of the
braided Stendhal algebra is a combination of products `u e(j) x` with `e(j)` violated and the
red strands of `j` reading `κ'`.

This is the step used in Webster's quotients `B_w` (arXiv:1309.3796v2, §6, before Lemma 6.5):
a violated diagram of `B̃(κ', κ)` factors through a violated idempotent of red order `κ'`. The
proof expands `w` in the basis of Proposition 6.4 for a choice of reduced words adapted to `i`:
the word of `τ` is a word for a frame `v` of `τ` (which performs the red crossing and fixes the
black strands at the left edge) followed by a word for `τ v⁻¹`.

## Main results

* `BraidedStendhalAlgebra.exists_frame_fix` : frames fixing the strands left of the crossing.
* `TypeA.isReducedChoice_frame` : reduced words through frames.
* `BraidedStendhalAlgebra.redProj_mul_mul_e_mem` : the push.
-/

namespace Categorification.TypeA

open Equiv

/-- Reduced words through frames: if `v τ` is below `τ` in the weak order for every `τ`, then
`ρ (τ (v τ)⁻¹) ++ ρ (v τ)` is a choice of reduced words. -/
theorem isReducedChoice_frame {n : ℕ} {ρ : Perm (Fin n) → List ℕ} (hρ : IsReducedChoice ρ)
    (v : Perm (Fin n) → Perm (Fin n)) (hv : ∀ τ, invSet n (v τ) ⊆ invSet n τ) :
    IsReducedChoice fun τ => ρ (τ * (v τ)⁻¹) ++ ρ (v τ) := by
  intro τ
  have hl := length_add_of_invSet_subset (hv τ)
  refine ⟨⟨validWord_append.2 ⟨(hρ _).1.1, (hρ _).1.1⟩, ?_⟩, ?_⟩
  · rw [List.length_append, wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right,
      (hρ _).1.2, (hρ _).1.2, (hρ _).2, (hρ _).2, hl]
  · rw [wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right]

theorem invSet_one_subset {n : ℕ} (τ : Perm (Fin n)) : invSet n 1 ⊆ invSet n τ := by
  intro x hx
  simp [invSet] at hx
  exact absurd hx.2 (lt_asymm hx.1)

end Categorification.TypeA

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)} {L M : List (Fin ℓ)} {a b : Fin ℓ}

omit [DecidableEq I] in
/-- **Frames fixing the left edge.** As `exists_frame`, with moreover `v • i` violated when `i`
is: the frame fixes every strand left of the crossing. -/
theorem exists_frame_fix (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) {τ : Perm (Fin m)} {i : Seq μ} (hi : redWord i = κ₀)
    (hτ : redWord (τ • i) = κ₂) (hv : IsViolated i) :
    ∃ v, invSet m v ⊆ invSet m τ ∧ redWord (v • i) = κ₁ ∧ IsViolated (v • i) := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr i a
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr i b
  have hi' : redWord i = L ++ a :: b :: M := hi.trans h0
  have hqp := lt_of_redWord_eq_append hi' hq hp
  have hT : (q, p) ∈ invSet m τ :=
    mem_invSet_of_sublist_redWord (by rw [hτ]; exact h2) hqp hq hp
  obtain ⟨v, hS, hfix⟩ : ∃ v, IsSwapBelow τ (redSet i) q p v ∧ ∀ t, t < q → v t = t :=
    exists_isSwapBelow_fix hqp hT fun t ht hqt htp =>
    not_lt_of_redWord_eq_append hi' hq hp (by simpa [redSet] using ht) hqt htp
  refine ⟨v, hS.le, h1 ▸ (redWord_smul_eq_swap_iff' hi' hq hp _).2 hS.red, ?_⟩
  obtain ⟨h, hl⟩ := hv
  refine ⟨h, ?_⟩
  have h0q : (⟨0, h⟩ : Fin m) < q := by
    rw [Fin.lt_def]
    by_contra hc
    have hq0 : q = ⟨0, h⟩ := Fin.ext (by simp only at hc ⊢; omega)
    rw [hq0] at hq
    rw [hq] at hl
    simp at hl
  have hv0 : v⁻¹ ⟨0, h⟩ = ⟨0, h⟩ := by rw [Perm.inv_eq_iff_eq, hfix _ h0q]
  rw [lbl_smul, hv0]
  exact hl

variable (k Q Λ ν) in
/-- The span of the products `u e(j) x` with `e(j)` violated and red strands of `j` reading
`κ`. -/
noncomputable def violSpan (κ : List (Fin ℓ)) : Submodule k (BraidedStendhalAlgebra k Q Λ ν) :=
  Submodule.span k {y | ∃ (u : BraidedStendhalAlgebra k Q Λ ν) (j : Seq μ)
    (x : BraidedStendhalAlgebra k Q Λ ν), IsViolated j ∧
    redWord j = κ ∧ y = u * ofKLR k Q Λ ν (KLRAlgebra.e j) * x}

theorem mem_violSpan {κ : List (Fin ℓ)} (u x : BraidedStendhalAlgebra k Q Λ ν) {j : Seq μ}
    (hj : IsViolated j) (hκ : redWord j = κ) :
    u * ofKLR k Q Λ ν (KLRAlgebra.e j) * x ∈ violSpan k Q Λ ν κ :=
  Submodule.subset_span ⟨u, j, x, hj, hκ, rfl⟩

open Classical in
/-- A frame of `τ` for `i` fixing the left edge, if there is one, and `1` otherwise. -/
noncomputable def violFrame (κ : List (Fin ℓ)) (i : Seq μ) (τ : Perm (Fin m)) : Perm (Fin m) :=
  if h : ∃ v, invSet m v ⊆ invSet m τ ∧ redWord (v • i) = κ ∧ IsViolated (v • i) then
    h.choose else 1

omit [DecidableEq I] in
theorem violFrame_le (κ : List (Fin ℓ)) (i : Seq μ) (τ : Perm (Fin m)) :
    invSet m (violFrame κ i τ) ⊆ invSet m τ := by
  unfold violFrame
  split_ifs with h
  · exact h.choose_spec.1
  · exact invSet_one_subset τ

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)

include hρ hQ in
/-- **Pushing a violated idempotent through a red crossing.** If `e(i)` is violated with red
strands reading `L ++ a :: b :: M`, then `e_{κ'} w e(i)` for `κ' = L ++ b :: a :: M` is a
combination of products through violated idempotents of red order `κ'`. -/
theorem redProj_mul_mul_e_mem {i : Seq μ} (h0 : redWord i = L ++ a :: b :: M)
    (hv : IsViolated i) (w : BraidedStendhalAlgebra k Q Λ ν) :
    redProj k Q Λ ν (L ++ b :: a :: M) * w * ofKLR k Q Λ ν (KLRAlgebra.e i) ∈
      violSpan k Q Λ ν (L ++ b :: a :: M) := by
  set κ' := L ++ b :: a :: M
  set ρ' := fun τ => ρ (τ * (violFrame κ' i τ)⁻¹) ++ ρ (violFrame κ' i τ)
  have hρ' : IsReducedChoice ρ' := isReducedChoice_frame hρ _ (violFrame_le κ' i)
  let F : BraidedStendhalAlgebra k Q Λ ν →ₗ[k] BraidedStendhalAlgebra k Q Λ ν :=
    LinearMap.mulLeft k (redProj k Q Λ ν κ') ∘ₗ
      LinearMap.mulRight k (ofKLR k Q Λ ν (KLRAlgebra.e i))
  have hF : ∀ y, F y = redProj k Q Λ ν κ' * y * ofKLR k Q Λ ν (KLRAlgebra.e i) := fun y => by
    simp [F, mul_assoc]
  rw [← hF, ← Submodule.mem_comap]
  refine Submodule.span_le.2 ?_ ((basis hQ ρ' hρ').mem_span w)
  rintro _ ⟨c, rfl⟩
  obtain ⟨⟨j, τ, u⟩, hu⟩ := c
  rw [SetLike.mem_coe, Submodule.mem_comap, hF, basis_apply, redProj, ← map_mul, ← map_mul]
  dsimp only
  rw [mul_assoc (redIdem k Q Λ κ'), mul_assoc _ (KLRAlgebra.e j), KLRAlgebra.e_mul_e]
  split_ifs with hj
  swap
  · rw [mul_zero, mul_zero, map_zero]; exact zero_mem _
  subst hj
  have hy := e_mul_std (Q := Q) (Λ := Λ) (ρ' τ) (monomial u 1) j
  rw [(hρ' τ).2] at hy
  rw [← hy, ← mul_assoc, redIdem_mul_e]
  split_ifs with hτ
  swap
  · rw [zero_mul, map_zero]; exact zero_mem _
  rw [hy]
  have hex := exists_frame_fix rfl rfl (by simp [κ']) h0 hτ hv
  have hvf : violFrame κ' j τ = hex.choose := by
    unfold violFrame
    split_ifs with h
    · rfl
    · exact absurd hex h
  obtain ⟨-, hv2, hv3⟩ := hex.choose_spec
  set v := hex.choose
  have hz := e_mul_std (Q := Q) (Λ := Λ) (ρ v) (monomial u 1) j
  rw [(hρ v).2] at hz
  have hρτ : ρ' τ = ρ (τ * v⁻¹) ++ ρ v := by simp only [ρ', hvf]
  rw [hρτ, KLRAlgebra.ψw_append, mul_assoc (KLRAlgebra.ψw _), mul_assoc (KLRAlgebra.ψw _),
    ← hz, ← mul_assoc, map_mul, map_mul]
  exact mem_violSpan _ _ hv3 hv2

end BraidedStendhalAlgebra

end Categorification.Stendhal
