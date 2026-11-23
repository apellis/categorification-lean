/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel
import Categorification.WeightedKLR.RedStrands.BraidedRedOrder
import Categorification.TypeA.SwapConnected
import Categorification.TypeA.Matsumoto

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: additive pairs and exits

Part of the proof of Webster, arXiv:1309.3796v2, Lemma 6.5, for one red-red crossing: the
red strands of `κ₀ = L ++ a :: b :: M` and `κ₁ = L ++ b :: a :: M` differ by exchanging the
adjacent labels `a` and `b`, and `b` comes before `a` in `κ₂`.

The class `ψ_u ⊗ ψ_v x^p e(i)` vanishes unless the red strands of `i`, `v • i` and `u v • i`
read `κ₀`, `κ₁` and `κ₂`. In that case `v` inverts exactly the red strands `q < p` of `i`
labelled `a` and `b`, and `u v` inverts them as well. When `ℓ(u v) = ℓ(u) + ℓ(v)`, simple
transpositions of `v` other than the red crossing can be moved to `u` until `v = s e` for an
exit `e` of `u v` (`TypeA.IsExit`), and the class does not depend on the exit modulo lower
degree, since exits are connected by squares and hexagons (`TypeA.exitRel_connected`).
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)}

/-! ### The outer idempotents -/

/-- Left multiplication by the left idempotent does not change `gen`. -/
theorem gen_redIdem_mul (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (redIdem k Q Λ κ₂ * x) y = gen κ₂ κ₁ κ₀ x y := by
  have h := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₂
  simp only [gen, map_mul]
  rw [CornerTensor.tmul_corner (x := ofKLR k Q Λ ν _ * _),
    CornerTensor.tmul_corner (x := ofKLR k Q Λ ν x)]
  congr 1
  rw [show ofKLR k Q Λ ν (redIdem k Q Λ κ₂) = redProj k Q Λ ν κ₂ from rfl, ← mul_assoc,
    h.eq]

/-- Right multiplication by the right idempotent does not change `gen`. -/
theorem gen_mul_redIdem_right (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (y * redIdem k Q Λ κ₀) = gen κ₂ κ₁ κ₀ x y := by
  have h := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₀
  simp only [gen, map_mul]
  rw [CornerTensor.tmul_corner (y := ofKLR k Q Λ ν y * _),
    CornerTensor.tmul_corner (y := ofKLR k Q Λ ν y)]
  congr 1
  rw [show ofKLR k Q Λ ν (redIdem k Q Λ κ₀) = redProj k Q Λ ν κ₀ from rfl, ← mul_assoc,
    mul_assoc _ (redProj k Q Λ ν κ₀), h.eq]

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ)

/-- `pgen u v p i` vanishes unless the red strands of `i` read `κ₀`. -/
theorem pgen_eq_zero_right (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord i ≠ κ₀) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v p i = 0 := by
  rw [pgen, ← gen_mul_redIdem_right, mul_assoc, e_mul_redIdem, ite_eq_right h, mul_zero,
    gen_zero_right]

include hρ

/-- `pgen u v p i` vanishes unless the red strands of `u v • i` read `κ₂`. -/
theorem pgen_eq_zero_left (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord ((u * v) • i) ≠ κ₂) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v p i = 0 := by
  by_cases hv : redWord (v • i) = κ₁
  swap
  · exact pgen_eq_zero hρ u v p i hv
  have hy := e_mul_std (Q := Q) (Λ := Λ) (ρ v) p i
  rw [(hρ v).2] at hy
  have h₁ : (redIdem k Q Λ κ₁ * KLRAlgebra.e (v • i) : R) = KLRAlgebra.e (v • i) := by
    rw [redIdem_mul_e, ite_eq_left hv]
  have h₂ : (KLRAlgebra.e (v • i) * redIdem k Q Λ κ₁ : R) = KLRAlgebra.e (v • i) := by
    rw [e_mul_redIdem, ite_eq_left hv]
  rw [pgen, ← hy, ← gen_mul_corner _ _ _ h₁ h₂, KLRAlgebra.ψw_mul_e, (hρ u).2, ← mul_smul,
    ← gen_redIdem_mul, ← mul_assoc, redIdem_mul_e, ite_eq_right h, zero_mul, gen_zero_left]

/-! ### Frames of a permutation

Fix the red strands `q < p` of `i` carrying the labels `a` and `b` that are exchanged. A *frame*
of `τ` is a permutation `v` with `invSet v ⊆ invSet τ` and `redWord (v • i) = κ₁`. These are the
permutations of `TypeA.IsSwapBelow`, and any two frames are connected by steps `v ↦ s_c v`
through frames (`TypeA.isSwapBelow_connected`). -/

variable {L M : List (Fin ℓ)} {a b : Fin ℓ}

/-- The red strands of `i`. -/
def redSet (i : Seq μ) : Finset (Fin m) := Finset.univ.filter fun s => (i.lbl s).isRight

omit [DecidableEq I] hρ in
theorem lt_of_redWord_eq_append {i : Seq μ} (h : redWord i = L ++ a :: b :: M) {q p : Fin m}
    (hq : i.lbl q = .inr a) (hp : i.lbl p = .inr b) : q < p := by
  have hP := redWord_pairwise_one i
  rw [h, List.pairwise_append, List.pairwise_cons] at hP
  exact hP.2.1.1 b (by simp) q p hq hp

omit [DecidableEq I] hρ in
/-- The red strands of `v • i` read `κ₀` with `a, b` exchanged iff the only red pair inverted
by `v` is `(q, p)`. -/
theorem redWord_smul_eq_swap_iff' {i : Seq μ} (h : redWord i = L ++ a :: b :: M) {q p : Fin m}
    (hq : i.lbl q = .inr a) (hp : i.lbl p = .inr b) (v : Perm (Fin m)) :
    redWord (v • i) = L ++ b :: a :: M ↔ ∀ s t, s ∈ redSet i → t ∈ redSet i →
      ((s, t) ∈ invSet m v ↔ s = q ∧ t = p) := by
  have hqp := lt_of_redWord_eq_append h hq hp
  rw [redWord_smul_eq_swap_iff h hq hp v]
  simp only [redSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_invSet_pair]
  constructor
  · intro H s t hs ht
    constructor
    · rintro ⟨hst, hv⟩
      exact (H s t hs ht hst).1 hv
    · rintro ⟨h1, h2⟩
      subst h1 h2
      exact ⟨hqp, (H _ _ hs ht hqp).2 ⟨rfl, rfl⟩⟩
  · intro H s t hs ht hst
    rw [← H s t hs ht]
    exact ⟨fun hv => ⟨hst, hv⟩, fun h => h.2⟩

/-- One step `v ↦ s_c v` up between frames of `τ` changes the class by lower degree. -/
theorem pgen_frame_step {τ v : Perm (Fin m)} {c : ℕ} (hc : c + 1 < m)
    (hv : invSet m v ⊆ invSet m τ) (hv' : invSet m (sadj m c * v) ⊆ invSet m τ)
    (hlen : length m (sadj m c * v) = length m v + 1) (f : MvPolynomial (Fin m) k) (i : Seq μ)
    (hr : redWord (v • i) = κ₁) (hr' : redWord ((sadj m c * v) • i) = κ₁) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₀ := κ₀) ρ (τ * v⁻¹) v f i -
        pgen ρ (τ * (sadj m c * v)⁻¹) (sadj m c * v) f i ∈
      low κ₂ κ₁ κ₀ (length m τ - 1) := by
  have h1 := length_add_of_invSet_subset hv
  have h2 := length_add_of_invSet_subset hv'
  have e : τ * (sadj m c * v)⁻¹ = τ * v⁻¹ * sadj m c := by
    rw [mul_inv_rev, sadj_inv, mul_assoc]
  have := pgen_move (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₀ := κ₀) hρ hc (u := τ * v⁻¹) (v := v)
    (by rw [← e]; omega) (by omega) f i hr hr'
  rw [e]
  rwa [show length m (τ * v⁻¹) + length m v - 1 = length m τ - 1 by omega] at this

/-- A step `v ↦ s_c v` between frames of `τ` changes the class by lower degree. -/
theorem pgen_frame_sub_mem_low {τ v : Perm (Fin m)} {c : ℕ} (hc : c + 1 < m)
    (hv : invSet m v ⊆ invSet m τ) (hv' : invSet m (sadj m c * v) ⊆ invSet m τ)
    (f : MvPolynomial (Fin m) k) (i : Seq μ)
    (hr : redWord (v • i) = κ₁) (hr' : redWord ((sadj m c * v) • i) = κ₁) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₀ := κ₀) ρ (τ * v⁻¹) v f i -
        pgen ρ (τ * (sadj m c * v)⁻¹) (sadj m c * v) f i ∈
      low κ₂ κ₁ κ₀ (length m τ - 1) := by
  have hne : v⁻¹ ⟨c, by omega⟩ ≠ v⁻¹ ⟨c + 1, hc⟩ := fun h => by
    have := Fin.ext_iff.1 (v⁻¹.injective h)
    simp at this
  rcases lt_or_gt_of_ne hne with h | h
  · exact pgen_frame_step (Q := Q) (Λ := Λ) hρ hc hv hv' (length_sadj_mul_of_lt hc h) f i
      hr hr'
  · have hvv : sadj m c * (sadj m c * v) = v := by rw [← mul_assoc, sadj_mul_self, one_mul]
    have hl := length_sadj_mul_of_gt hc h
    have := pgen_frame_step (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₀ := κ₀) hρ hc hv'
      (by rwa [hvv]) (by rw [hvv]; omega)
      f i hr' (by rwa [hvv])
    rw [hvv] at this
    simpa using neg_mem this

/-- Frames of `τ` connected by steps have classes congruent modulo lower degree. -/
theorem pgen_frame_eqvGen {i : Seq μ} (hi : redWord i = L ++ a :: b :: M)
    (h1 : κ₁ = L ++ b :: a :: M) {q p : Fin m} (hq : i.lbl q = .inr a) (hp : i.lbl p = .inr b)
    (f : MvPolynomial (Fin m) k) {τ v v' : Perm (Fin m)}
    (H : Relation.EqvGen (SwapStep τ (redSet i) q p) v v') :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ (τ * v⁻¹) v f i -
        pgen ρ (τ * v'⁻¹) v' f i ∈ low κ₂ κ₁ κ₀ (length m τ - 1) := by
  induction H with
  | rel x y hxy =>
    obtain ⟨hx, hy, c, hc, rfl⟩ := hxy
    exact pgen_frame_sub_mem_low (Q := Q) (Λ := Λ) hρ hc hx.le hy.le f i
      (h1 ▸ (redWord_smul_eq_swap_iff' hi hq hp x).2 hx.red)
      (h1 ▸ (redWord_smul_eq_swap_iff' hi hq hp _).2 hy.red)
  | refl x => simp
  | symm x y _ ih => simpa using neg_mem ih
  | trans x y z _ _ ih1 ih2 => simpa using add_mem ih1 ih2

open Classical in
/-- The class of a frame of `τ`: `pgen (τ v⁻¹) v` for a chosen permutation `v` with
`invSet v ⊆ invSet τ` and `redWord (v • i) = κ₁`, and `0` if there is none. -/
noncomputable def frameClass (ρ : Perm (Fin m) → List ℕ) (τ : Perm (Fin m))
    (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁)
      (redProj k Q Λ ν κ₀) :=
  if h : ∃ v, invSet m v ⊆ invSet m τ ∧ redWord (v • i) = κ₁ then
    pgen ρ (τ * h.choose⁻¹) h.choose f i
  else 0

/-- **The class of an additive pair does not depend on the frame**, modulo lower degree: for
`ℓ(u) + ℓ(v) = ℓ(u v)` and red strands of `i`, `v • i` reading `κ₀`, `κ₁`, the class
`pgen u v` is congruent to the class of the chosen frame of `u v`. -/
theorem pgen_sub_frameClass_mem_low (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    {u v : Perm (Fin m)} (hl : length m u + length m v = length m (u * v))
    (f : MvPolynomial (Fin m) k) (i : Seq μ) (hi : redWord i = κ₀) (hr : redWord (v • i) = κ₁) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) ρ u v f i - frameClass ρ (u * v) f i ∈
      low κ₂ κ₁ κ₀ (length m u + length m v - 1) := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr i a
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr i b
  have hi' : redWord i = L ++ a :: b :: M := hi.trans h0
  have hvτ : invSet m v ⊆ invSet m (u * v) := invSet_subset_of_length_add hl
  have hex : ∃ v', invSet m v' ⊆ invSet m (u * v) ∧ redWord (v' • i) = κ₁ := ⟨v, hvτ, hr⟩
  rw [frameClass, dite_eq_left hex]
  obtain ⟨hv'1, hv'2⟩ := hex.choose_spec
  have S1 : IsSwapBelow (u * v) (redSet i) q p v :=
    ⟨hvτ, (redWord_smul_eq_swap_iff' hi' hq hp v).1 (hr.trans h1)⟩
  have S2 : IsSwapBelow (u * v) (redSet i) q p hex.choose :=
    ⟨hv'1, (redWord_smul_eq_swap_iff' hi' hq hp _).1 (hv'2.trans h1)⟩
  have hqR : q ∈ redSet i := by simp [redSet, hq]
  have hpR : p ∈ redSet i := by simp [redSet, hp]
  have := pgen_frame_eqvGen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₀ := κ₀) hρ hi' h1 hq hp f
    (isSwapBelow_connected (lt_of_redWord_eq_append hi' hq hp) hqR hpR S1 S2)
  rwa [mul_inv_cancel_right, ← hl] at this

end BraidedStendhalAlgebra

end Categorification.Stendhal
