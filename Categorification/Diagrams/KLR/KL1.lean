/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.Comparison
import Categorification.KLR.KL1

/-!
# The diagrammatic relations of KL I

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.1, relations (2.3)–(2.8) (TeX labels `eq_UUzero`, `eq_ijslide`,
`eq_iislide1`, `eq_iislide2`, `eq_r3_easy`, `eq_r3_hard`).

For a simple graph `Γ` on `I` and the KL I data `Q = klQ Γ` (`Q_ij = u + v` for an edge,
`1` otherwise), the defining relations of the presented category `pres k (klQ Γ)` specialise
to the local relations of KL I, read bottom to top (`x₀`, `x₁` are dots on the left and right
strands, `ψ` is a crossing, and `ψ₀`, `ψ₁` are crossings of the left and right pairs of
three strands):

* (2.3): `ψ ≫ ψ` on `[i, j]` is `0` if `i = j`, the identity if `i ≠ j` are not joined, and
  `x₀ + x₁` if `i`, `j` are joined (`kl1_sq_eq`, `kl1_sq_nonadj`, `kl1_sq_adj`);
* (2.4): for `i ≠ j`, `ψ ≫ x₀ = x₁ ≫ ψ` and `x₀ ≫ ψ = ψ ≫ x₁` (`kl1_slideL_ne`,
  `kl1_slideR_ne`);
* (2.5), (2.6): on `[i, i]`, `ψ ≫ x₀ - x₁ ≫ ψ = 1` and `x₀ ≫ ψ - ψ ≫ x₁ = 1`
  (`kl1_slideL_eq`, `kl1_slideR_eq`);
* (2.7): `ψ₀ ≫ ψ₁ ≫ ψ₀ = ψ₁ ≫ ψ₀ ≫ ψ₁` on `[i, j, k]` unless `i = k` and `i`, `j` are
  joined (`kl1_braid`);
* (2.8): `ψ₀ ≫ ψ₁ ≫ ψ₀ - ψ₁ ≫ ψ₀ ≫ ψ₁ = 1` on `[i, j, i]` if `i`, `j` are joined
  (`kl1_braid_adj`).

With `diagREquiv` this identifies the ring `R(ν)` of KL I (`R1 k Γ ν`) with the diagrammatic
algebra (`kl1Equiv`).
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams MvPolynomial

universe u

variable {I : Type u} (Γ : SimpleGraph I) [DecidableRel Γ.Adj]
  {k : Type*} [CommRing k]

section ncEval

variable {A : Type*} [Ring A] [Algebra k A]

theorem ncEval_add' {n : ℕ} (y : Fin n → A) (p q : MvPolynomial (Fin n) k) :
    ncEval y (p + q) = ncEval y p + ncEval y q :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem ncEval_monomial' {n : ℕ} (y : Fin n → A) (s : Fin n →₀ ℕ) (c : k) :
    ncEval y (monomial s c) = algebraMap k A c * (List.ofFn fun a => y a ^ s a).prod :=
  Finsupp.sum_single_index (by simp)

theorem ncEval_one' {n : ℕ} (y : Fin n → A) : ncEval y (1 : MvPolynomial (Fin n) k) = 1 := by
  rw [← C_1, C_apply, ncEval_monomial']
  simp

theorem ncEval_zero' {n : ℕ} (y : Fin n → A) : ncEval y (0 : MvPolynomial (Fin n) k) = 0 := by
  simp [ncEval]

theorem ncEval_X_add_X (y : Fin 2 → A) :
    ncEval y (X 0 + X 1 : MvPolynomial (Fin 2) k) = y 0 + y 1 := by
  rw [ncEval_add', X, X, ncEval_monomial', ncEval_monomial']
  simp [List.ofFn_succ, Finsupp.single_apply]

end ncEval

local notation "P" => pres k (klQ (k := k) Γ)

variable {Γ}

/-- KL I (2.3), `i = j`: a double crossing of two strands of the same colour vanishes. -/
theorem kl1_sq_eq (c : I) : (P).diag (X2 c c ≫ X2 c c) = 0 :=
  sqEq_at (klQ Γ) (u := []) (v := []) _ rfl

/-- KL I (2.3), `i · j = 0`: a double crossing of non-joined colours is the identity. -/
theorem kl1_sq_nonadj {c d : I} (hne : c ≠ d) (h : ¬ Γ.Adj c d) :
    (P).diag (X2 c d ≫ X2 d c) = 𝟙 _ := by
  rw [sqNe_at (klQ Γ) (u := []) (v := []) hne _ (D0 c d) (D1 c d) rfl rfl rfl]
  simp only [klQ, if_neg h]
  exact ncEval_one' (A := End ((P).obj (ob [c, d]))) _

/-- KL I (2.3), `i · j = -1`: a double crossing of joined colours is `x₀ + x₁`. -/
theorem kl1_sq_adj {c d : I} (h : Γ.Adj c d) :
    (P).diag (X2 c d ≫ X2 d c) = (P).diag (D0 c d) + (P).diag (D1 c d) := by
  rw [sqNe_at (klQ Γ) (u := []) (v := []) (Γ.ne_of_adj h) _ (D0 c d) (D1 c d) rfl rfl rfl]
  simp only [klQ, if_pos h]
  exact ncEval_X_add_X (A := End ((P).obj (ob [c, d]))) _

/-- KL I (2.4), left: for `i ≠ j`, `ψ ≫ x₀ = x₁ ≫ ψ` on `[i, j]`. -/
theorem kl1_slideL_ne {c d : I} (hne : c ≠ d) :
    (P).diag (X2 c d ≫ D0 d c) = (P).diag (D1 c d ≫ X2 c d) :=
  slideLNe_at (klQ Γ) (u := []) (v := []) hne _ _ rfl rfl

/-- KL I (2.4), right: for `i ≠ j`, `x₀ ≫ ψ = ψ ≫ x₁` on `[i, j]`. -/
theorem kl1_slideR_ne {c d : I} (hne : c ≠ d) :
    (P).diag (D0 c d ≫ X2 c d) = (P).diag (X2 c d ≫ D1 d c) :=
  slideRNe_at (klQ Γ) (u := []) (v := []) hne _ _ rfl rfl

/-- KL I (2.5): `ψ ≫ x₀ - x₁ ≫ ψ = 1` on `[i, i]`. -/
theorem kl1_slideL_eq (c : I) :
    (P).diag (X2 c c ≫ D0 c c) - (P).diag (D1 c c ≫ X2 c c) = 𝟙 _ :=
  slideLEq_at (klQ Γ) (u := []) (v := []) _ _ rfl rfl

/-- KL I (2.6): `x₀ ≫ ψ - ψ ≫ x₁ = 1` on `[i, i]`. -/
theorem kl1_slideR_eq (c : I) :
    (P).diag (D0 c c ≫ X2 c c) - (P).diag (X2 c c ≫ D1 c c) = 𝟙 _ :=
  slideREq_at (klQ Γ) (u := []) (v := []) _ _ rfl rfl

/-- KL I (2.7): the braid relation on `[i, j, k]` unless `i = k` and `i`, `j` are joined. -/
theorem kl1_braid {c d e : I} (h : ¬ (c = e ∧ Γ.Adj c d)) :
    (P).diag (braidL c d e) = (P).diag (braidR c d e) := by
  by_cases h' : c = e ∧ c ≠ d
  · obtain ⟨rfl, hne⟩ := h'
    have hadj : ¬ Γ.Adj c d := fun ha => h ⟨rfl, ha⟩
    have := braidQ_at (klQ (k := k) Γ) (u := []) (v := []) hne (braidL c d c) (braidR c d c)
      (E0 c d c) (E1 c d c) (E2 c d c) rfl rfl rfl rfl rfl
    rw [klQ, if_neg hadj, qbar_one (k := k), ncEval_zero', sub_eq_zero] at this
    exact this
  · exact braid_at (klQ Γ) (u := []) (v := []) h' _ _ rfl rfl

/-- KL I (2.8): `ψ₀ ≫ ψ₁ ≫ ψ₀ - ψ₁ ≫ ψ₀ ≫ ψ₁ = 1` on `[i, j, i]` if `i`, `j` are joined. -/
theorem kl1_braid_adj {c d : I} (h : Γ.Adj c d) :
    (P).diag (braidL c d c) - (P).diag (braidR c d c) = 𝟙 _ := by
  rw [braidQ_at (klQ Γ) (u := []) (v := []) (Γ.ne_of_adj h) _ _ (E0 c d c) (E1 c d c)
    (E2 c d c) rfl rfl rfl rfl rfl, klQ, if_pos h, qbar_X_add_X]
  exact ncEval_one' (A := End ((P).obj (ob [c, d, c]))) _

variable (k Γ) in
/-- **KL I, §2.1.** The ring `R(ν)` of KL I is the diagrammatic algebra of the category
presented by the KL I relations. -/
def kl1Equiv [DecidableEq I] (ν : Multiset I) : R1 k Γ ν ≃ₐ[k] DiagR k (klQ (k := k) Γ) ν :=
  diagREquiv k (klQ Γ) ν

end Categorification.KLR.Diagram

end
