/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.GradedBasis
import Categorification.Algebra.Graded.HomForm

/-!
# The bilinear form on `K₀(R(ν))`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, equation `eq_bil_pair2`: the form
`([P], [Q]) = gdim (P^ψ ⊗_{R(ν)} Q)` on `K₀(R(ν))`, with
`([P_j], [P_i]) = gdim (1_j R(ν) 1_i)` (paper, displayed equation after `eq-bil-ten`) and
`ch(M, i) = gdim HOM(P_i, M)` (equation `eq_char1`).

We use the form `K0.homForm (G.grade ν)`, `([P], [Q]) = gdim HOM(P, Q)`, constructed on all of
`K₀(R(ν))` in `Categorification.Algebra.Graded.HomForm` (it is biadditive and sesquilinear:
`(q^a x, y) = q^{-a} (x, y)`, `(x, q^a y) = q^a (x, y)`). The paper's form is
`(x, y) ↦ homForm x̄ y` (because `P^ψ ⊗_{R(ν)} Q ≅ HOM(P̄, Q)` with `P̄ = HOM(P, R(ν))^ψ`); on the
modules `P_i = R(ν) 1_i`, which are self-dual (`P̄_i ≅ P_i`, KL I §2.5), the two coincide, and we
prove the values stated in the paper:

* `GradingDatum.homForm_projP_left` : `([P_j], [M]) = gdim HOM(P_j, M) = gdim (1_j M) = ch(M, j)`
  (equation `eq_char1`);
* `GradingDatum.homForm_projP` : `([P_j], [P_i]) = gdim (1_j R(ν) 1_i)`;
* `GradingDatum.homForm_projP_eq_sum` : the explicit value
  `∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg x_{a,i}})⁻¹`;
* `KL1.homForm_projP` : for KL I,
  `([P_j], [P_i]) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b} (1 - q²)^{-m}`;
* `KL1.homForm_projP_comm` : `([P_j], [P_i]) = ([P_i], [P_j])` (the form is symmetric on the
  `P_i`, as stated in the paper).

## Scope

The bar involution on `K₀` and the bilinear symmetric form `pform x y = homForm (x̄) y` are in
`Categorification.Algebra.Graded.Duality` and `Categorification.KLR.BarK0`. The graded tensor
product description `P^ψ ⊗_{R(ν)} Q ≅ HOM(P̄, Q)` of the paper's form is not formalized. The
values `([P_j], [P_i])` and `([P_j], [M])` agree with the paper's.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA Graded KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) {ν : Multiset I}

namespace GradingDatum

/-- **KL I, equation `eq_char1`**: `([P_j], [M]) = gdim HOM(P_j, M) = gdim (1_j M) = ch(M, j)`. -/
theorem homForm_projP_left [HasGdim (G.grade ν)] (j : Seq ν) (M : GProj (G.grade ν)) :
    K0.homForm (G.grade ν) (K0.of (G.projP j)) (K0.of M) = G.ch M.toGMod j :=
  K0.homForm_ofIdempotent (e_mul_self j) (G.e_mem_grade j) M

/-- **KL I, §2.5**: `([P_j], [P_i]) = gdim (1_j R(ν) 1_i)`. -/
theorem homForm_projP [HasGdim (G.grade ν)] (j i : Seq ν) :
    K0.homForm (G.grade ν) (K0.of (G.projP j)) (K0.of (G.projP i)) =
      gdim (G.cornerGrade j i) := by
  rw [homForm_projP_left, ch_projP]

include hPQ hP in
/-- The explicit value `([P_j], [P_i]) = ∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)}
∏_a (1 - q^{deg x_{a,i}})⁻¹`, for any choice `ρ` of reduced words (all dots of positive
degree). -/
theorem homForm_projP_eq_sum [HasGdim (G.grade ν)] (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
    (hX : ∀ a, 0 < G.degX a) (j i : Seq ν) :
    K0.homForm (G.grade ν) (K0.of (G.projP j)) (K0.of (G.projP i)) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (G.degW (ρ w) i) 1 * ∏ a, geomSeries (G.degX (i.lbl a)) := by
  rw [homForm_projP, G.gdim_cornerGrade hPQ hP ρ hρ hX]

end GradingDatum

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- **KL I, §2.5, for the rings of KL I**:
`([P_j], [P_i]) = gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b}
(1 - q²)^{-m}`, where `(1 - q²)^{-1} = geomSeries 2`. -/
theorem homForm_projP (j i : Seq ν) :
    K0.homForm ((klGradingDatum k Γ).grade ν) (K0.of ((klGradingDatum k Γ).projP j))
      (K0.of ((klGradingDatum k Γ).projP i)) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, cartan Γ (i.lbl p.1) (i.lbl p.2)) 1 *
          geomSeries 2 ^ Multiset.card ν := by
  rw [GradingDatum.homForm_projP, gdim_cornerGrade]

/-- The crossing degree of `w⁻¹` on `w • i` equals that of `w` on `i` (the Cartan form is
symmetric). -/
theorem sum_invSet_inv (w : Perm (Fin (Multiset.card ν))) (i : Seq ν) :
    ∑ p ∈ invSet (Multiset.card ν) w⁻¹, cartan Γ ((w • i).lbl p.1) ((w • i).lbl p.2) =
      ∑ p ∈ invSet (Multiset.card ν) w, cartan Γ (i.lbl p.1) (i.lbl p.2) := by
  refine Finset.sum_nbij' (fun p => (w⁻¹ p.2, w⁻¹ p.1)) (fun p => (w p.2, w p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_invSet] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · intro p hp
    rw [mem_invSet] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · intro p _; simp
  · intro p _; simp
  · intro p _
    simp only [Seq.lbl, Seq.smul_apply, ← Perm.inv_def, inv_inv]
    exact cartan_symm Γ _ _

/-- **The form is symmetric on the `P_i`** (KL I, §2.5): `([P_j], [P_i]) = ([P_i], [P_j])`. -/
theorem homForm_projP_comm (j i : Seq ν) :
    K0.homForm ((klGradingDatum k Γ).grade ν) (K0.of ((klGradingDatum k Γ).projP j))
      (K0.of ((klGradingDatum k Γ).projP i)) =
    K0.homForm ((klGradingDatum k Γ).grade ν) (K0.of ((klGradingDatum k Γ).projP i))
      (K0.of ((klGradingDatum k Γ).projP j)) := by
  rw [homForm_projP, homForm_projP]
  refine Finset.sum_nbij' (fun w => w⁻¹) (fun w => w⁻¹) ?_ ?_ (fun _ _ => inv_inv _)
    (fun _ _ => inv_inv _) ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [← hw, inv_smul_smul]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [← hw, inv_smul_smul]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    congr 3
    rw [← hw, sum_invSet_inv]

end KL1

end Categorification.KLR
