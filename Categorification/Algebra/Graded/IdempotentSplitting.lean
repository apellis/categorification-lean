/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Dimension
import Categorification.Algebra.IdempotentEquiv

/-!
# Graded dimensions of `e M` under splittings of idempotents

Background for M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
groups I*, arXiv:0803.4121v2, §2.5 (the equality `gdim (1_î M) = q^{-⟨i⟩} i! gdim (1_i M)`,
Corollary 2.14 and Corollary 2.15).

Let `(A, 𝒜)` be a `ℤ`-graded `k`-algebra and `(M, ℳ)` a graded `A`-module. Suppose that an
element `E' ∈ A` *splits* as `E' = ∑_j a_j b_j` with `b_i a_j = δ_{ij} E_j`, where
`a_j ∈ 𝒜_{d_j}` and `b_j ∈ 𝒜_{-d_j}` (for instance: `E'` is a sum of orthogonal idempotents
`a_j b_j`, each equivalent to `E_j = b_j a_j` via homogeneous elements). Then
`m ↦ (b_j m)_j` is an isomorphism `(E' M)_d ≅ ∏_j (E_j M)_{d - d_j}` with inverse
`(m_j) ↦ ∑_j a_j m_j`, so

  `gdim (E' M) = ∑_j q^{d_j} gdim (E_j M)`.

## Main results

* `Graded.IsSplitting` : the splitting data `E' = ∑_j a_j b_j`, `b_i a_j = δ_{ij} E_j`.
* `Graded.idemSplitEquiv` : `(E' M)_d ≅ ∏_j (E_j M)_{d - d_j}`.
* `Graded.gdim_idem_eq_sum_of_isSplitting` : `gdim (E' M) = ∑_j q^{d_j} gdim (E_j M)`.
* `Graded.gdim_idem_of_isEquivPair` : for equivalent idempotents `f = a b`, `f' = b a` with
  `a ∈ 𝒜_d`, `b ∈ 𝒜_{-d}`: `gdim (f M) = q^d gdim (f' M)`.
* `Graded.gdim_idem_of_isOrthDecomp` : for `e = f₁ + f₂` orthogonal with `f₁ ~ E₁`, `f₂ ~ E₂`
  via homogeneous pairs of degrees `d₁, d₂`: `gdim (e M) = q^{d₁} gdim (E₁ M) + q^{d₂} gdim (E₂ M)`.
-/

namespace Categorification.Graded

open Module

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {ℳ : ℤ → Submodule k M} [SetLike.GradedSMul 𝒜 ℳ]

/-- A *splitting* of `E'` through the family `E`: `E' = ∑_j a_j b_j` and `b_i a_j = δ_{ij} E_j`. -/
structure IsSplitting {ι : Type*} [Fintype ι] [DecidableEq ι] (E' : A) (E a b : ι → A) :
    Prop where
  mul_eq : ∀ i j, b i * a j = if i = j then E j else 0
  sum_eq : ∑ j, a j * b j = E'

namespace IsSplitting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E' : A} {E a b : ι → A}

theorem mul_self (h : IsSplitting E' E a b) (j : ι) : b j * a j = E j := by
  rw [h.mul_eq, if_pos rfl]

theorem mul_ne (h : IsSplitting E' E a b) {i j : ι} (hij : i ≠ j) : b i * a j = 0 := by
  rw [h.mul_eq, if_neg hij]

theorem left_mul_a (h : IsSplitting E' E a b) (j : ι) : E' * a j = a j * E j := by
  rw [← h.sum_eq, Finset.sum_mul]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [mul_assoc, h.mul_ne hij, mul_zero])
    (fun h' => absurd (Finset.mem_univ j) h'), mul_assoc, h.mul_self]

theorem b_mul_right (h : IsSplitting E' E a b) (j : ι) : b j * E' = E j * b j := by
  rw [← h.sum_eq, Finset.mul_sum]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [← mul_assoc, h.mul_ne (Ne.symm hij),
    zero_mul]) (fun h' => absurd (Finset.mem_univ j) h'), ← mul_assoc, h.mul_self]

end IsSplitting

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E' : A} {E a b : ι → A} {dg : ι → ℤ}

omit [IsScalarTower k A M] in
private theorem smul_mem_shift {x : A} {m : M} {d e : ℤ} (hx : x ∈ 𝒜 e) (hm : m ∈ ℳ d) :
    x • m ∈ ℳ (e + d) :=
  SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) hx hm

/-- The isomorphism `(E' M)_d ≅ ∏_j (E_j M)_{d - d_j}`, `m ↦ (b_j m)_j`, for a splitting
`E' = ∑_j a_j b_j` with `a_j ∈ 𝒜_{d_j}`, `b_j ∈ 𝒜_{-d_j}`. -/
noncomputable def idemSplitEquiv (h : IsSplitting E' E a b) (ha : ∀ j, a j ∈ 𝒜 (dg j))
    (hb : ∀ j, b j ∈ 𝒜 (-dg j)) (d : ℤ) :
    idem ℳ E' d ≃ₗ[k] ((j : ι) → idem ℳ (E j) (d - dg j)) where
  toFun x j := ⟨⟨b j • ((x : idemSubspace k M E') : M), by
      rw [mem_idemSubspace, smul_smul, ← h.b_mul_right, ← smul_smul,
        (x : idemSubspace k M E').2]⟩, by
      rw [mem_idem]
      have := smul_mem_shift (ℳ := ℳ) (hb j) (show ((x : idemSubspace k M E') : M) ∈ ℳ d from x.2)
      rwa [neg_add_eq_sub] at this⟩
  invFun y := ⟨⟨∑ j, a j • ((y j : idemSubspace k M (E j)) : M), by
      rw [mem_idemSubspace, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, h.left_mul_a j, ← smul_smul, (y j : idemSubspace k M (E j)).2]⟩, by
      rw [mem_idem]
      refine Submodule.sum_mem _ fun j _ => ?_
      have := smul_mem_shift (ℳ := ℳ) (ha j)
        (show ((y j : idemSubspace k M (E j)) : M) ∈ ℳ (d - dg j) from (y j).2)
      rwa [add_sub_cancel] at this⟩
  map_add' x y := by
    funext j
    exact Subtype.ext (Subtype.ext (smul_add _ _ _))
  map_smul' c x := by
    funext j
    exact Subtype.ext (Subtype.ext (smul_comm (b j) c _))
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    change ∑ j, a j • b j • ((x : idemSubspace k M E') : M) = _
    simp only [smul_smul, ← Finset.sum_smul, h.sum_eq]
    exact (x : idemSubspace k M E').2
  right_inv y := by
    funext i
    refine Subtype.ext (Subtype.ext ?_)
    change b i • ∑ j, a j • ((y j : idemSubspace k M (E j)) : M) = _
    rw [Finset.smul_sum, Finset.sum_eq_single i (fun j _ hji => by
      rw [smul_smul, h.mul_ne (Ne.symm hji), zero_smul]) (fun h' => absurd (Finset.mem_univ i) h'),
      smul_smul, h.mul_self]
    exact (y i : idemSubspace k M (E i)).2

theorem finrank_idem_eq_sum_of_isSplitting [HasGdim ℳ]
    (h : IsSplitting E' E a b) (ha : ∀ j, a j ∈ 𝒜 (dg j)) (hb : ∀ j, b j ∈ 𝒜 (-dg j)) (d : ℤ) :
    finrank k (idem ℳ E' d) = ∑ j, finrank k (idem ℳ (E j) (d - dg j)) := by
  rw [(idemSplitEquiv h ha hb d).finrank_eq, Module.finrank_pi_fintype]

/-- **Graded dimensions under a splitting**: `gdim (E' M) = ∑_j q^{d_j} gdim (E_j M)` for
`E' = ∑_j a_j b_j`, `b_i a_j = δ_{ij} E_j`, `a_j ∈ 𝒜_{d_j}`, `b_j ∈ 𝒜_{-d_j}`. -/
theorem gdim_idem_eq_sum_of_isSplitting [HasGdim ℳ]
    (h : IsSplitting E' E a b) (ha : ∀ j, a j ∈ 𝒜 (dg j)) (hb : ∀ j, b j ∈ 𝒜 (-dg j)) :
    gdim (idem ℳ E') = ∑ j, HahnSeries.single (dg j) 1 * gdim (idem ℳ (E j)) := by
  ext d
  rw [coeff_gdim, finrank_idem_eq_sum_of_isSplitting h ha hb, HahnSeries.coeff_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sub_add_cancel d (dg j), HahnSeries.coeff_single_mul_add, one_mul, coeff_gdim,
    add_sub_cancel_right]

end Split

/-! ### Equivalent idempotents and orthogonal decompositions -/

section Pairs

/-- A single equivalence `f = a b`, `f' = b a` is a splitting of `f` through `f'`. -/
theorem isSplitting_of_isEquivPair {a b f f' : A} (h : IsEquivPair a b f f') :
    IsSplitting (ι := Unit) f (fun _ => f') (fun _ => a) (fun _ => b) where
  mul_eq _ _ := by simp [h.2.1]
  sum_eq := by simp [h.1]

/-- An orthogonal decomposition `e = f₁ + f₂` with `E₁ = a₁ b₁`, `f₁ = b₁ a₁` and
`E₂ = a₂ b₂`, `f₂ = b₂ a₂` is a splitting of `e` through `(E₁, E₂)` (with the roles
`a ↦ b`, `b ↦ a`). -/
theorem isSplitting_of_isOrthDecomp {e f₁ f₂ E₁ E₂ a₁ b₁ a₂ b₂ : A}
    (h : IsOrthDecomp e f₁ f₂) (h₁ : IsEquivPair a₁ b₁ E₁ f₁) (h₂ : IsEquivPair a₂ b₂ E₂ f₂) :
    IsSplitting e ![E₁, E₂] ![b₁, b₂] ![a₁, a₂] where
  mul_eq i j := by
    fin_cases i <;> fin_cases j
    · simp [h₁.1]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, zero_ne_one, ↓reduceIte]
      rw [← h₁.mul_right, ← h₂.left_mul', mul_assoc, ← mul_assoc f₁, h.2.2.1, zero_mul,
        mul_zero]
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero, one_ne_zero, ↓reduceIte]
      rw [← h₂.mul_right, ← h₁.left_mul', mul_assoc, ← mul_assoc f₂, h.2.2.2.1, zero_mul,
        mul_zero]
    · simp [h₂.1]
  sum_eq := by
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    rw [h₁.2.1, h₂.2.1, h.2.2.2.2]

variable [HasGdim ℳ]

/-- **Equivalent idempotents**: if `f = a b` and `f' = b a` with `a ∈ 𝒜_d`, `b ∈ 𝒜_{-d}`, then
`f M ≅ (f' M){d}`, so `gdim (f M) = q^d gdim (f' M)`. -/
theorem gdim_idem_of_isEquivPair {a b f f' : A} {d : ℤ} (h : IsEquivPair a b f f')
    (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 (-d)) :
    gdim (idem ℳ f) = HahnSeries.single d 1 * gdim (idem ℳ f') := by
  have := gdim_idem_eq_sum_of_isSplitting (ℳ := ℳ) (dg := fun _ => d)
    (isSplitting_of_isEquivPair h) (fun _ => ha) (fun _ => hb)
  simpa using this

/-- **Orthogonal decompositions**: if `e = f₁ + f₂` (orthogonal idempotents) with
`E₁ = a₁ b₁`, `f₁ = b₁ a₁`, `a₁ ∈ 𝒜_{-d₁}`, `b₁ ∈ 𝒜_{d₁}` and similarly for `f₂`, then
`gdim (e M) = q^{d₁} gdim (E₁ M) + q^{d₂} gdim (E₂ M)`. -/
theorem gdim_idem_of_isOrthDecomp {e f₁ f₂ E₁ E₂ a₁ b₁ a₂ b₂ : A} {d₁ d₂ : ℤ}
    (h : IsOrthDecomp e f₁ f₂) (h₁ : IsEquivPair a₁ b₁ E₁ f₁) (h₂ : IsEquivPair a₂ b₂ E₂ f₂)
    (ha₁ : a₁ ∈ 𝒜 (-d₁)) (hb₁ : b₁ ∈ 𝒜 d₁) (ha₂ : a₂ ∈ 𝒜 (-d₂)) (hb₂ : b₂ ∈ 𝒜 d₂) :
    gdim (idem ℳ e) = HahnSeries.single d₁ 1 * gdim (idem ℳ E₁) +
      HahnSeries.single d₂ 1 * gdim (idem ℳ E₂) := by
  have := gdim_idem_eq_sum_of_isSplitting (ℳ := ℳ) (dg := ![d₁, d₂])
    (isSplitting_of_isOrthDecomp h h₁ h₂)
    (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa)
  simpa [Fin.sum_univ_two] using this

end Pairs

end Categorification.Graded
