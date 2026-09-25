/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.DividedPowers
import Categorification.QuantumGroup.Cartan

/-!
# `'f`, `f` and `_𝒜 f` over `ℚ(v)` for a Cartan datum, and the KL I specialisation

We specialise the general constructions to `K = ℚ(v) = RatFunc ℚ` with `v = X`
(`vQ`), and to Lusztig's normalisation `(θ i, θ i) = (1 - v_i^{-2})⁻¹ = (1 - v^{-i·i})⁻¹`
(`lusztigC`, Lusztig 1.2.3(a)).

For a simple graph `Γ` (Khovanov–Lauda, arXiv:0803.4121v2, §1 and §3.1) we record:

* `KL.form_θ_θ` — the normalisation `(θ i, θ j) = δ_{ij} (1 - q²)⁻¹` with `q = v⁻¹`
  (KL I Prop. 3.3(2) = `prop-pairing-prop`, "our `q` is Lusztig's `v⁻¹`");
* `KL.serre_comm`, `KL.serre_cubic` — the defining relations of `U⁻` in KL I §1 hold in `f`:
  `θ_iθ_j = θ_jθ_i` if `i · j = 0` and `(q + q⁻¹)θ_iθ_jθ_i = θ_i²θ_j + θ_jθ_i²` if
  `i · j = -1`;
* `KL.qfact_ne_zero` — the quantum factorials are nonzero, so the divided powers
  `θ_i^{(a)}` generating `_𝒜 f` (`KL.Af`) are honest.

The Gabber–Kac theorem (that these relations generate the radical) is not proved; see
`PreF.GabberKac`.
-/

noncomputable section

namespace Categorification.QuantumGroup

/-! ### Lusztig's normalisation -/

/-- Lusztig's value `(θ i, θ i) = (1 - v_i^{-2})⁻¹ = (1 - v^{-(i·i)})⁻¹` (Lusztig 1.2.3(a)). -/
def lusztigC {I K : Type*} [Field K] (dot : I → I → ℤ) (v : Kˣ) (i : I) : K :=
  (1 - ((v ^ (-dot i i) : Kˣ) : K))⁻¹

/-! ### `ℚ(v)` -/

/-- The indeterminate `v ∈ ℚ(v)ˣ`. -/
def vQ : (RatFunc ℚ)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero

@[simp] theorem vQ_val : (vQ : RatFunc ℚ) = RatFunc.X := rfl

theorem vQ_pow_ne_one {m : ℕ} (hm : 0 < m) : vQ ^ m ≠ 1 := by
  intro h
  have h' : (RatFunc.X : RatFunc ℚ) ^ m = 1 := by
    have := congrArg Units.val h
    simpa using this
  rw [← RatFunc.algebraMap_X, ← map_pow, ← map_one (algebraMap (Polynomial ℚ) (RatFunc ℚ))]
    at h'
  have := congrArg Polynomial.natDegree (RatFunc.algebraMap_injective ℚ h')
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one,
    Polynomial.natDegree_one] at this
  omega

theorem vQ_zpow_ne_one {n : ℤ} (hn : n ≠ 0) : vQ ^ n ≠ 1 := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact vQ_pow_ne_one (by omega)
  · rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]
    exact vQ_pow_ne_one (by omega)

/-- For `n ≠ 0`, `1 - v^n ≠ 0` in `ℚ(v)`; in particular Lusztig's normalisation
`(1 - v^{-(i·i)})⁻¹` is an honest inverse. -/
theorem one_sub_vQ_zpow_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (1 : RatFunc ℚ) - ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) ≠ 0 := by
  rw [sub_ne_zero, ne_comm, Ne, Units.val_eq_one]
  exact vQ_zpow_ne_one hn

/-! ### `f` over `ℚ(v)` for a Cartan datum -/

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- Lusztig's normalisation constants for `C` over `ℚ(v)`. -/
def c : I → RatFunc ℚ := lusztigC C.dot vQ

theorem c_mul_one_sub (i : I) :
    C.c i * (1 - ((vQ ^ (-C.dot i i) : (RatFunc ℚ)ˣ) : RatFunc ℚ)) = 1 :=
  inv_mul_cancel₀ (one_sub_vQ_zpow_ne_zero (by have := C.dot_self_pos i; omega))

/-- Lusztig's bilinear form on `'f` for `C` (Lusztig 1.2.3); it is symmetric. -/
def form : PreF (RatFunc ℚ) I →ₗ[RatFunc ℚ] PreF (RatFunc ℚ) I →ₗ[RatFunc ℚ] RatFunc ℚ :=
  PreF.form C.dot vQ C.c

theorem form_symm (x y : PreF (RatFunc ℚ) I) : C.form x y = C.form y x := PreF.form_symm C.symm x y

/-- Lusztig's algebra `f` over `ℚ(v)` for the Cartan datum `C`. -/
abbrev F := PreF.F C.dot vQ C.c

/-- The integral form `_𝒜 f` for `C`. -/
def Af : Subring C.F := PreF.Af C.dot vQ C.c

/-- The divided powers are honest: `[a]_{v_i}^! ≠ 0` in `ℚ(v)`. -/
theorem qfact_ne_zero (i : I) (a : ℕ) : qfact (PreF.vi C.dot vQ i) a ≠ 0 := by
  refine Categorification.QuantumGroup.qfact_ne_zero (fun m hm => ?_) a
  have h2 : 0 < C.dot i i / 2 := by
    obtain ⟨k, hk⟩ := C.dot_self_even i
    have := C.dot_self_pos i
    omega
  rw [PreF.vi, ← zpow_natCast, ← zpow_mul]
  exact vQ_zpow_ne_one (mul_ne_zero h2.ne' (by exact_mod_cast hm.ne'))

end CartanDatum

/-! ### Khovanov–Lauda I: the simply-laced case of a graph `Γ` -/

namespace KL

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- The Cartan datum of the graph `Γ` (KL I §1). -/
abbrev C : CartanDatum I := CartanDatum.ofGraph Γ

/-- KL I's algebra `f` for the graph `Γ`, over `ℚ(v)`, `v = q⁻¹`. -/
abbrev F := (C Γ).F

/-- KL I's integral form `_𝒜 f` for the graph `Γ`. -/
abbrev Af := (C Γ).Af

/-- The quotient map `'f → f`. -/
abbrev π := PreF.π (C Γ).dot vQ (C Γ).c

/-- KL I Prop. 3.3(2) normalisation: `(θ i, θ j) = δ_{ij} (1 - q²)⁻¹` with `q = v⁻¹`. -/
theorem form_θ_θ (i j : I) :
    (C Γ).form (PreF.θ i) (PreF.θ j) =
      if i = j then (1 - ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ 2)⁻¹ else 0 := by
  rw [CartanDatum.form, PreF.form_θ_θ]
  split_ifs with h
  · subst h
    simp only [CartanDatum.c, lusztigC, CartanDatum.ofGraph_dot_self]
    rw [zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val]
  · rfl

/-- KL I §1: `θ_i θ_j = θ_j θ_i` in `f` if `i ≠ j` are not joined by an edge. -/
theorem serre_comm {i j : I} (hij : i ≠ j) (h : ¬ Γ.Adj i j) :
    π Γ (PreF.θ i) * π Γ (PreF.θ j) = π Γ (PreF.θ j) * π Γ (PreF.θ i) := by
  rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub, PreF.π_eq_zero_iff]
  exact PreF.serreComm_mem_radical (C Γ).symm hij (CartanDatum.ofGraph_dot_of_not_adj Γ hij h)

/-- KL I §1: `(q + q⁻¹) θ_i θ_j θ_i = θ_i² θ_j + θ_j θ_i²` in `f` if `i` and `j` are joined by
an edge (`q = v⁻¹`). -/
theorem serre_cubic {i j : I} (h : Γ.Adj i j) :
    (((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) + (vQ : RatFunc ℚ)) •
        (π Γ (PreF.θ i) * π Γ (PreF.θ j) * π Γ (PreF.θ i)) =
      π Γ (PreF.θ i) ^ 2 * π Γ (PreF.θ j) + π Γ (PreF.θ j) * π Γ (PreF.θ i) ^ 2 := by
  have hmem := PreF.serreCubic_mem_radical (c := (C Γ).c) (v := vQ) (C Γ).symm h.ne
    (CartanDatum.ofGraph_dot_self Γ i) (CartanDatum.ofGraph_dot_of_adj Γ h)
  rw [← PreF.π_eq_zero_iff, PreF.serreCubic_eq] at hmem
  simp only [map_add, map_sub, map_smul, map_mul, map_pow] at hmem
  rw [← sub_eq_zero, ← neg_eq_zero, ← hmem]
  abel_nf

/-- The divided powers of KL I are honest: `[a]^! ≠ 0` in `ℚ(v)`, so
`[a]^! θ_i^{(a)} = θ_i^a`. -/
theorem qfact_smul_dpow (i : I) (a : ℕ) :
    qfact (PreF.vi (C Γ).dot vQ i) a • PreF.dpow (C Γ).dot vQ i a = PreF.θ i ^ a :=
  PreF.qfact_smul_dpow ((C Γ).qfact_ne_zero i a)

end KL

end Categorification.QuantumGroup

end
