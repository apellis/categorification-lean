/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotBlock
import Categorification.Flag.Bimodule

/-!
# The root datum of `sl_{m+1}` and the weights of compositions

Khovanov–Lauda III, arXiv:0807.3250v1, §4.1 (TeX subsection "Forms of quantum sl_n") and §5.2.1,
eq. (5.18).

KL III §4.1 uses the root datum of the Dynkin graph `1 — 2 — ⋯ — (n-1)` in which a weight is
`λ = (λ_1, …, λ_{n-1})`, `λ_i = ⟨i, λ⟩`, and `λ + i_X` is given by eq. (4.9): `λ_i` increases by
`2` and `λ_{i±1}` decrease by `1`. We take `n = m + 1`, vertices `Fin m`, `X = Y = ℤ^m` with the
standard pairing `⟨y, x⟩ = ∑_a y_a x_a`, `i ∈ Y` the `i`-th unit vector and `i_X` the `i`-th
column of the Cartan matrix (`slRootDatum`).

A sequence `0 = k_0 ≤ ⋯ ≤ k_n = N` is recorded by its block sizes `d : Fin (m+1) → ℕ`
(`d_j = k_{j+1} - k_j` in 0-based indexing), and eq. (5.18) `λ_α = -k_{α+1} + 2k_α - k_{α-1}` reads
`λ_i = d_i - d_{i+1}` (`compWeight`). Moving one unit from block `i + 1` to block `i` (the
paper's `+_i k`, `Flag.raise`) changes the weight by `i_X` (`compWeight_raise`, "comparing with
(4.9) it is clear that `λ(+_i k) = λ + i_X`"), and for fixed `N` the weight determines the
composition (`compWeight_injective`).
-/

namespace Categorification.Flag

open QuantumGroup UDot

/-- The Dynkin graph of type `A_m`: `i — j` iff `|i - j| = 1`. -/
def slGraph (m : ℕ) : SimpleGraph (Fin m) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm _ _ h := h.symm
  loopless i h := by omega

instance (m : ℕ) : DecidableRel (slGraph m).Adj := fun i j =>
  inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))

/-- The Cartan datum of `sl_{m+1}`. -/
abbrev slCartan (m : ℕ) : CartanDatum (Fin m) := CartanDatum.ofGraph (slGraph m)

theorem slCartan_dot (m : ℕ) (i j : Fin m) :
    (slCartan m).dot i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := rfl

/-- The pairing `⟨y, x⟩ = ∑_a y_a x_a` on `ℤ^m`. -/
def slPair (m : ℕ) : (Fin m → ℤ) →+ (Fin m → ℤ) →+ ℤ where
  toFun y :=
    { toFun := fun x => ∑ a, y a * x a
      map_zero' := by simp
      map_add' := fun x x' => by simp [mul_add, Finset.sum_add_distrib] }
  map_zero' := by ext; simp
  map_add' y y' := by ext; simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem slPair_apply (m : ℕ) (y x : Fin m → ℤ) : slPair m y x = ∑ a, y a * x a := rfl

theorem slPair_single_left (m : ℕ) (i : Fin m) (x : Fin m → ℤ) :
    slPair m (Pi.single i 1) x = x i := by
  simp [Pi.single_apply]

theorem slPair_single_right (m : ℕ) (y : Fin m → ℤ) (i : Fin m) :
    slPair m y (Pi.single i 1) = y i := by
  simp [Pi.single_apply]

/-- Every additive map `ℤ^m → ℤ` is `x ↦ ∑_a c_a x_a`. -/
theorem addMonoidHom_eq_sum {m : ℕ} (f : (Fin m → ℤ) →+ ℤ) (x : Fin m → ℤ) :
    f x = ∑ a, f (Pi.single a 1) * x a := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : Pi.single a (x a) = x a • (Pi.single a 1 : Fin m → ℤ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_zsmul, smul_eq_mul, mul_comm]

/-- **The root datum of `sl_{m+1}`** (KL III §4.1): `X = Y = ℤ^m`, `i = e_i`, `i_X` the `i`-th
column of the Cartan matrix. -/
def slRootDatum (m : ℕ) : RootDatum (slCartan m) (Fin m → ℤ) (Fin m → ℤ) where
  pair := slPair m
  perfect_left := by
    refine ⟨fun y y' h => funext fun a => ?_, fun f => ⟨fun a => f (Pi.single a 1), ?_⟩⟩
    · have := DFunLike.congr_fun h (Pi.single a 1)
      rwa [slPair_single_right, slPair_single_right] at this
    · refine AddMonoidHom.ext fun x => ?_
      exact (addMonoidHom_eq_sum f x).symm
  perfect_right := by
    refine ⟨fun x x' h => funext fun a => ?_, fun f => ⟨fun a => f (Pi.single a 1), ?_⟩⟩
    · have := DFunLike.congr_fun h (Pi.single a 1)
      simp only [AddMonoidHom.flip_apply] at this
      rwa [slPair_single_left, slPair_single_left] at this
    · refine AddMonoidHom.ext fun y => ?_
      change ∑ a, y a * f (Pi.single a 1) = f y
      rw [addMonoidHom_eq_sum f y]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  free_X := inferInstance
  finite_X := inferInstance
  free_Y := inferInstance
  finite_Y := inferInstance
  iX j := fun a => (slCartan m).dot a j
  iY i := Pi.single i 1
  pair_iY_iX i j := by
    rw [slPair_single_left, CartanDatum.ofGraph_dot_self]
    omega

@[simp] theorem slRootDatum_iX_apply (m : ℕ) (j a : Fin m) :
    (slRootDatum m).iX j a = (slCartan m).dot a j := rfl

theorem slRootDatum_ellOf (m : ℕ) (lam : Fin m → ℤ) (i : Fin m) :
    (slRootDatum m).ellOf lam i = lam i := slPair_single_left m i lam

/-! ### Weights of compositions -/

variable {m : ℕ}

/-- **KL III eq. (5.18)**: the weight `λ_i = -k_{i+1} + 2k_i - k_{i-1} = d_i - d_{i+1}` of the block
sizes `d` (0-based: `λ_i = d_{i.castSucc} - d_{i.succ}`). -/
def compWeight (d : Fin (m + 1) → ℕ) : Fin m → ℤ := fun i => d i.castSucc - d i.succ

theorem raise_cast (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) (j : Fin (m + 1)) :
    (raise i d j : ℤ) = d j + (if j = i.castSucc then 1 else 0) - (if j = i.succ then 1 else 0) := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ i).ne
  unfold raise
  by_cases h1 : j = i.castSucc
  · subst h1
    simp [hne]
  · by_cases h2 : j = i.succ
    · subst h2
      simp only [if_neg h1, if_true, add_zero]
      rw [Nat.cast_sub h]
      push_cast
      ring
    · simp [h1, h2]

/-- **`λ(+_i k) = λ + i_X`** (KL III §5.2.1, after eq. (5.18); compare eq. (4.9)). -/
theorem compWeight_raise (i : Fin m) (d : Fin (m + 1) → ℕ) (h : 0 < d i.succ) :
    compWeight (raise i d) = compWeight d + (slRootDatum m).iX i := by
  funext a
  simp only [compWeight, raise_cast i d h, Pi.add_apply, slRootDatum_iX_apply, slCartan_dot,
    Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- **The weight determines the composition of `N`.** -/
theorem compWeight_injective {d d' : Fin (m + 1) → ℕ} (hw : compWeight d = compWeight d')
    (hN : ∑ j, d j = ∑ j, d' j) : d = d' := by
  set c : Fin (m + 1) → ℤ := fun j => (d j : ℤ) - d' j with hc
  have hstep : ∀ a : Fin m, c a.castSucc = c a.succ := by
    intro a
    have := congrFun hw a
    simp only [compWeight] at this
    simp only [hc]
    omega
  have hconst : ∀ j, c j = c 0 := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ a ih => rw [← hstep a, ih]
  have hsum : ∑ j, c j = 0 := by
    have hN' : (∑ j, (d j : ℤ)) = ∑ j, (d' j : ℤ) := by exact_mod_cast hN
    simp only [hc, Finset.sum_sub_distrib, hN', sub_self]
  rw [Finset.sum_congr rfl fun j _ => hconst j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have h0 : c 0 = 0 := by
    rcases mul_eq_zero.1 hsum with h | h
    · omega
    · exact h
  funext j
  have := hconst j
  rw [h0] at this
  simp only [hc] at this
  omega

end Categorification.Flag
