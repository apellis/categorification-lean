/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DividedDifference
import Categorification.KLR.Basic

/-!
# The polynomial shadow of `Γ_N` on three upward strands

KL III, arXiv:0807.3250v1, §6.2, proof of Proposition 6.8 (TeX `sln-2008-ArXiv.tex`, eqs. (6.20),
(6.21)): "The proof of these remaining relations is the same as the proof that rings `R(ν)` act
on `Pol_ν` […] Replacing the variables `x_k(i)` with the Chern classes of line bundles `ξ_k` […]
turns formulas in [16, Section 2.3] for the action of dots and crossings into formulas (6.6) and
(6.8), with the signs taken into account."

On a monomial `ξ_left^a ξ_right^b` of two upward strands coloured `c` (left) and `d` (right),
`Γ_N` of the crossing (KL III (6.8), `Categorification.Flag.GammaLocal`) acts by

* the divided difference `∂` if `c = d`;
* `F_{cd}(x_left, x_right) · s` otherwise, where `s` swaps the two variables and
  `F_{cd} = x_right - x_left` if `c = d + 1` (the push-forward `-crossFN`), `F_{cd} = 1` otherwise.

This file proves the resulting identities in `k[x₀, x₁, x₂]`:

* `braid_poly` : for colours `c, d, e`, with `ψ₀`, `ψ₁` the operators on the positions `(0, 1)`,
  `(1, 2)` (`op0`, `op1`),
  `ψ₀ ψ₁ ψ₀ − ψ₁ ψ₀ ψ₁ = [c = e ≠ d] · Q̄_{cd}(x₀, x₁, x₂)` (multiplication), where
  `Q_{cd}(u, v) = F_{dc}(u, v) F_{cd}(v, u)` (`Qf`) is the double crossing and `Q̄` is
  `Categorification.KLR.qbar`. This is exactly the KLR braid relation (KL III (4.13), (4.14))
  for the polynomials `Q = Qf`; `Qf` is the signed `Q^τ` of Definition 4.1
  (`Categorification.Diagrams.KL3.GammaFlagBraid`).

The generic identities behind it (`sss`, `dds`, `sdd`, `sds`) hold for arbitrary factor
polynomials. `eval_twisted` is the abstract induction turning "dot slide" rules for an additive
map into its values on all polynomials in the dots.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial Equiv

section Ops

variable {k : Type*} [CommRing k]

/-- `s₀` (swap `x₀`, `x₁`). -/
abbrev sw0 : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k := rename (swap (0 : Fin 3) 1)

/-- `s₁` (swap `x₁`, `x₂`). -/
abbrev sw1 : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k := rename (swap (1 : Fin 3) 2)

/-- `A(x₀, x₁)`. -/
abbrev at01 (A : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 3) k := rename ![0, 1] A

/-- `A(x₁, x₂)`. -/
abbrev at12 (A : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 3) k := rename ![1, 2] A

/-- `f ↦ A(x₀, x₁) · s₀ f`. -/
def mS0 (A : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  at01 A * sw0 f

/-- `f ↦ A(x₁, x₂) · s₁ f`. -/
def mS1 (A : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  at12 A * sw1 f

/-- `∂₀ = ∂_{x₀ x₁}`. -/
abbrev dd0 : MvPolynomial (Fin 3) k →ₗ[k] MvPolynomial (Fin 3) k := ddiff (0 : Fin 3) 1

/-- `∂₁ = ∂_{x₁ x₂}`. -/
abbrev dd1 : MvPolynomial (Fin 3) k →ₗ[k] MvPolynomial (Fin 3) k := ddiff (1 : Fin 3) 2

theorem c_s0_12 : (⇑(swap (0 : Fin 3) 1) ∘ (![1, 2] : Fin 2 → Fin 3)) = ![0, 2] := by decide
theorem c_s1_01 : (⇑(swap (1 : Fin 3) 2) ∘ (![0, 1] : Fin 2 → Fin 3)) = ![0, 2] := by decide
theorem c_s0_02 : (⇑(swap (0 : Fin 3) 1) ∘ (![0, 2] : Fin 2 → Fin 3)) = ![1, 2] := by decide
theorem c_s1_02 : (⇑(swap (1 : Fin 3) 2) ∘ (![0, 2] : Fin 2 → Fin 3)) = ![0, 1] := by decide
theorem c_s0_01 : (⇑(swap (0 : Fin 3) 1) ∘ (![0, 1] : Fin 2 → Fin 3)) = ![1, 0] := by decide
theorem c_s1_12 : (⇑(swap (1 : Fin 3) 2) ∘ (![1, 2] : Fin 2 → Fin 3)) = ![2, 1] := by decide
theorem c_s0_10 : (⇑(swap (0 : Fin 3) 1) ∘ (![1, 0] : Fin 2 → Fin 3)) = ![0, 1] := by decide
theorem c_s1_21 : (⇑(swap (1 : Fin 3) 2) ∘ (![2, 1] : Fin 2 → Fin 3)) = ![1, 2] := by decide
theorem c_braid : (⇑(swap (0 : Fin 3) 1) ∘ ⇑(swap (1 : Fin 3) 2) ∘ ⇑(swap (0 : Fin 3) 1)) =
    (⇑(swap (1 : Fin 3) 2) ∘ ⇑(swap (0 : Fin 3) 1) ∘ ⇑(swap (1 : Fin 3) 2)) := by decide

theorem sw0_at12 (A : MvPolynomial (Fin 2) k) : sw0 (at12 A) = rename ![0, 2] A := by
  rw [rename_rename, c_s0_12]

theorem sw1_at01 (A : MvPolynomial (Fin 2) k) : sw1 (at01 A) = rename ![0, 2] A := by
  rw [rename_rename, c_s1_01]

theorem sw0_at02 (A : MvPolynomial (Fin 2) k) : sw0 (rename ![0, 2] A) = at12 A := by
  rw [rename_rename, c_s0_02]

theorem sw1_at02 (A : MvPolynomial (Fin 2) k) : sw1 (rename ![0, 2] A) = at01 A := by
  rw [rename_rename, c_s1_02]

/-- **`ψ₀ ψ₁ ψ₀ = ψ₁ ψ₀ ψ₁` for three swaps with factors.** -/
theorem sss (A B C : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) :
    mS0 C (mS1 B (mS0 A f)) = mS1 A (mS0 B (mS1 C f)) := by
  simp only [mS0, mS1, map_mul, sw0_at12, sw1_at01, sw0_at02, sw1_at02]
  have hf : sw0 (sw1 (sw0 f)) = sw1 (sw0 (sw1 f)) := by
    simp only [rename_rename]
    exact congrArg (fun φ => rename φ f) (by simpa [Function.comp_assoc] using c_braid)
  rw [hf]
  ring

theorem sw0_sw1_dd0 (f : MvPolynomial (Fin 3) k) : sw0 (sw1 (dd0 f)) = dd1 (sw0 (sw1 f)) := by
  rw [rename_ddiff (swap (1 : Fin 3) 2).injective (by decide),
    rename_ddiff (swap (0 : Fin 3) 1).injective (by decide)]
  rfl

theorem sw1_sw0_dd1 (f : MvPolynomial (Fin 3) k) : sw1 (sw0 (dd1 f)) = dd0 (sw1 (sw0 f)) := by
  rw [rename_ddiff (swap (0 : Fin 3) 1).injective (by decide),
    rename_ddiff (swap (1 : Fin 3) 2).injective (by decide)]
  rfl

theorem sym12 (A : MvPolynomial (Fin 2) k) :
    sw1 (at01 A * rename ![0, 2] A) = at01 A * rename ![0, 2] A := by
  rw [map_mul, sw1_at01, sw1_at02, mul_comm]

theorem sym01 (A : MvPolynomial (Fin 2) k) :
    sw0 (at12 A * rename ![0, 2] A) = at12 A * rename ![0, 2] A := by
  rw [map_mul, sw0_at12, sw0_at02, mul_comm]

/-- **`ψ₀ ψ₁ ∂₀ = ∂₁ ψ₀ ψ₁`** (strands `c c e`). -/
theorem dds (A : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) :
    mS0 A (mS1 A (dd0 f)) = dd1 (mS0 A (mS1 A f)) := by
  simp only [mS0, mS1, map_mul, sw0_at12]
  rw [← mul_assoc, ← mul_assoc,
    ddiff_mul_of_rename_eq (by decide) (sym12 A), sw0_sw1_dd0]

/-- **`∂₀ ψ₁ ψ₀ = ψ₁ ψ₀ ∂₁`** (strands `c d d`). -/
theorem sdd (A : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) :
    dd0 (mS1 A (mS0 A f)) = mS1 A (mS0 A (dd1 f)) := by
  simp only [mS0, mS1, map_mul, sw1_at01]
  rw [← mul_assoc, ← mul_assoc,
    ddiff_mul_of_rename_eq (by decide) (sym01 A), sw1_sw0_dd1]

theorem sw0_dd1_sw0 (f : MvPolynomial (Fin 3) k) :
    sw0 (dd1 (sw0 f)) = ddiff (0 : Fin 3) 2 f := by
  rw [rename_ddiff (swap (0 : Fin 3) 1).injective (by decide), rename_swap_rename_swap]
  rfl

theorem sw1_dd0_sw1 (f : MvPolynomial (Fin 3) k) :
    sw1 (dd0 (sw1 f)) = ddiff (0 : Fin 3) 2 f := by
  rw [rename_ddiff (swap (1 : Fin 3) 2).injective (by decide), rename_swap_rename_swap]
  rfl

theorem sw0_dd1 (g : MvPolynomial (Fin 3) k) :
    sw0 (dd1 g) = ddiff (0 : Fin 3) 2 (sw0 g) := by
  rw [rename_ddiff (swap (0 : Fin 3) 1).injective (by decide)]
  rfl

theorem sw1_dd0 (g : MvPolynomial (Fin 3) k) :
    sw1 (dd0 g) = ddiff (0 : Fin 3) 2 (sw1 g) := by
  rw [rename_ddiff (swap (1 : Fin 3) 2).injective (by decide)]
  rfl

/-- **The braid relation on `c d c`**: `ψ₀ ∂₁ ψ₀ − ψ₁ ∂₀ ψ₁ = Q̄(x₀, x₁, x₂)` with
`Q(u, v) = B(u, v) A(v, u)`, for the factors `A` (crossing `c d`) and `B` (crossing `d c`). -/
theorem sds (A B : MvPolynomial (Fin 2) k) (f : MvPolynomial (Fin 3) k) :
    mS0 B (dd1 (mS0 A f)) - mS1 A (dd0 (mS1 B f)) =
      KLR.qbar (B * rename ![1, 0] A) * f := by
  have hL : sw0 (dd1 (at01 A * sw0 f)) =
      ddiff (0 : Fin 3) 2 (rename ![1, 0] A) * f + at12 A * ddiff (0 : Fin 3) 2 f := by
    rw [ddiff_mul (by decide), map_add, map_mul, map_mul, sw0_dd1, sw0_dd1_sw0,
      rename_swap_rename_swap, sw1_at01, sw0_at02, rename_rename, c_s0_01]
  have hR : sw1 (dd0 (at12 B * sw1 f)) =
      ddiff (0 : Fin 3) 2 (rename ![2, 1] B) * f + at01 B * ddiff (0 : Fin 3) 2 f := by
    rw [ddiff_mul (by decide), map_add, map_mul, map_mul, sw1_dd0, sw1_dd0_sw1,
      rename_swap_rename_swap, sw0_at12, sw1_at02, rename_rename, c_s1_12]
  -- the claim: `B₀₁ ∂₀₂(A₁₀) − A₁₂ ∂₀₂(B₂₁) = Q̄`
  have key : at01 B * ddiff (0 : Fin 3) 2 (rename ![1, 0] A) -
      at12 A * ddiff (0 : Fin 3) 2 (rename ![2, 1] B) = KLR.qbar (B * rename ![1, 0] A) := by
    apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
    rw [KLR.qbar_spec, mul_sub, ← mul_assoc, mul_comm (X 0 - X 2 : MvPolynomial (Fin 3) k),
      mul_assoc, ddiff_spec (by decide), ← mul_assoc, mul_comm (X 0 - X 2 : MvPolynomial (Fin 3) k),
      mul_assoc, ddiff_spec (by decide), map_mul, map_mul, rename_rename, rename_rename,
      rename_rename, rename_rename]
    rw [show (⇑(swap (0 : Fin 3) 2) ∘ (![1, 0] : Fin 2 → Fin 3)) = ![1, 2] by decide,
      show (⇑(swap (0 : Fin 3) 2) ∘ (![2, 1] : Fin 2 → Fin 3)) = ![0, 1] by decide,
      show ((![0, 1] : Fin 2 → Fin 3) ∘ (![1, 0] : Fin 2 → Fin 2)) = ![1, 0] by decide,
      show ((![2, 1] : Fin 2 → Fin 3) ∘ (![1, 0] : Fin 2 → Fin 2)) = ![1, 2] by decide]
    ring
  simp only [mS0, mS1]
  rw [hL, hR, ← key]
  ring

end Ops

/-! ### Colours -/

section Colours

variable (k : Type*) [CommRing k] {m : ℕ}

/-- The factor of the crossing `c d → d c` (left colour `c`): `x_right − x_left` if `c = d + 1`,
`1` otherwise. -/
def Fc (c d : Fin m) : MvPolynomial (Fin 2) k :=
  if c.castSucc = d.succ then X 1 - X 0 else 1

/-- The double crossing on `c d`: `Q_{cd}(u, v) = F_{dc}(u, v) F_{cd}(v, u)`. -/
def Qf (c d : Fin m) : MvPolynomial (Fin 2) k := Fc k d c * rename ![1, 0] (Fc k c d)

variable {k}

/-- `Γ` of the crossing of the strands `0, 1` with colours `c`, `d`, on polynomials. -/
def op0 (c d : Fin m) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  if c = d then dd0 f else mS0 (Fc k c d) f

/-- `Γ` of the crossing of the strands `1, 2` with colours `c`, `d`, on polynomials. -/
def op1 (c d : Fin m) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  if c = d then dd1 f else mS1 (Fc k c d) f

/-- **The braid relation for `Γ_N` on polynomials** (KL III (4.13), (4.14), (6.20), (6.21)):
`ψ₀ ψ₁ ψ₀ − ψ₁ ψ₀ ψ₁ = [c = e ≠ d] Q̄_{cd}` on strands `c d e`. -/
theorem braid_poly (c d e : Fin m) (f : MvPolynomial (Fin 3) k) :
    op0 d e (op1 c e (op0 c d f)) - op1 c d (op0 c e (op1 d e f)) =
      if c = e ∧ c ≠ d then KLR.qbar (Qf k c d) * f else 0 := by
  by_cases hcd : c = d
  · subst hcd
    by_cases hce : c = e
    · subst hce
      simp only [op0, op1, if_true]
      rw [ddiff_braid (by decide) (by decide) (by decide), sub_self, if_neg (by simp)]
    · simp only [op0, op1, if_true, if_neg hce]
      rw [dds, sub_self, if_neg (by simp)]
  · by_cases hce : c = e
    · subst hce
      simp only [op0, op1, if_true, if_neg hcd, if_neg (Ne.symm hcd)]
      rw [sds, Qf, if_pos (by simpa using hcd)]
    · rw [if_neg (fun h => hce h.1)]
      by_cases hde : d = e
      · subst hde
        simp only [op0, op1, if_true, if_neg hcd]
        rw [sdd, sub_self]
      · simp only [op0, op1, if_neg hcd, if_neg hce, if_neg hde]
        rw [sss, sub_self]

end Colours

/-! ### Values on polynomials from dot-slide rules -/

section Eval

variable {k σ : Type*} [CommRing k] [DecidableEq σ] {T T' : Type*} [CommRing T] [CommRing T']

/-- **Twisted-Leibniz induction.** Let `φ, τ : T → T'` be additive, where `T`, `T'` receive ring
maps `ev`, `ev'` from `k[x_σ]`. If `τ` commutes with all `ev (X i)`, and `φ` is additive, commutes
with scalars and with `ev (X i)` for `i ≠ a, b`, and satisfies the nilHecke dot slides
`φ(x_a y) = τ y + x_b φ y`, `φ(x_b y) = x_a φ y − τ y`, then
`φ(q y) = (∂_{ab} q) τ y + (s_{ab} q) φ y` for all polynomials `q`. (With `τ = 0` this covers maps
which merely swap `x_a` and `x_b`.) -/
theorem eval_twisted (ev : MvPolynomial σ k →+* T) (ev' : MvPolynomial σ k →+* T')
    (φ τ : T → T') (a b : σ) (hab : a ≠ b)
    (hφadd : ∀ y z, φ (y + z) = φ y + φ z)
    (hτX : ∀ i y, τ (ev (X i) * y) = ev' (X i) * τ y)
    (hφC : ∀ c y, φ (ev (C c) * y) = ev' (C c) * φ y)
    (hφa : ∀ y, φ (ev (X a) * y) = τ y + ev' (X b) * φ y)
    (hφb : ∀ y, φ (ev (X b) * y) = ev' (X a) * φ y - τ y)
    (hφo : ∀ i, i ≠ a → i ≠ b → ∀ y, φ (ev (X i) * y) = ev' (X i) * φ y) :
    ∀ (q : MvPolynomial σ k) (y : T),
      φ (ev q * y) = ev' (ddiff a b q) * τ y + ev' (rename (swap a b) q) * φ y := by
  intro q
  induction q using MvPolynomial.induction_on with
  | C c => intro y; rw [hφC, ddiff_C hab, rename_C]; simp
  | add p q hp hq =>
    intro y
    rw [map_add, add_mul, hφadd, hp, hq, map_add, map_add, map_add, map_add]; ring
  | mul_X p i hp =>
    intro y
    rw [map_mul, mul_assoc, hp, ddiff_mul hab, map_mul, map_mul]
    by_cases hia : i = a
    · subst hia
      rw [hτX, hφa, ddiff_X_left hab, rename_X, swap_apply_left, map_add, map_mul, map_mul,
        map_one]
      ring
    · by_cases hib : i = b
      · subst hib
        rw [hτX, hφb, ddiff_X_right hab, rename_X, swap_apply_right, map_add, map_mul, map_mul,
          map_neg, map_one]
        ring
      · rw [hτX, hφo i hia hib, ddiff_X_of_ne hab hia hib, rename_X,
          swap_apply_of_ne_of_ne hia hib, map_add, map_mul, map_mul, map_zero]
        ring

end Eval

end Categorification.Flag

end
