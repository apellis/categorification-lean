/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Grading
import Categorification.KLR.Symmetries

/-!
# The antiinvolution `ψ` preserves degrees

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.1 and §2.5: the antiinvolution `ψ` of `R(ν)` (reflecting diagrams in a
horizontal axis, `hflip`) is degree-preserving, which is used to define the graded projective
modules `P_i = R(ν) ψ(1_i) {-⟨i⟩}`.

For a grading datum `G` whose crossing degrees are symmetric (`degΨ a b = degΨ b a`; true for the
KL I grading, `deg ψ_{k,i} = - i_k · i_{k+1}`) we show that the coaction defining the grading
intertwines `hflip` with the coefficientwise flip of `R(ν)[ℤ]` (`coaction_hflip`), so that
`hflip` maps `R(ν)_d` to `R(ν)_d` (`hflip_mem_grade`, `KL1.hflip_mem_grade`).
-/

noncomputable section

namespace Categorification.KLR

open KLRAlgebra AddMonoidAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν

namespace GradingDatum

/-- `hflip` as an additive map. -/
def hflipAddHom : A →+ A := AddMonoidHom.mk' hflip hflip_add

/-- The coefficientwise flip `∑ single d a_d ↦ ∑ single d (ψ a_d)` of `R(ν)[ℤ]`. -/
def flipCoeff : AddMonoidAlgebra A ℤ →+ AddMonoidAlgebra A ℤ :=
  Finsupp.mapRange.addMonoidHom hflipAddHom

theorem flipCoeff_single (d : ℤ) (a : A) : flipCoeff (single d a) = single d (hflip a) :=
  Finsupp.mapRange_single (hf := map_zero hflipAddHom)

/-- The coefficientwise flip is an antihomomorphism (`ℤ` is commutative). -/
theorem flipCoeff_mul (X Y : AddMonoidAlgebra A ℤ) :
    flipCoeff (X * Y) = flipCoeff Y * flipCoeff X := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X X' hX hX' => rw [add_mul, map_add, hX, hX', map_add, mul_add]
  | single d a =>
    induction Y using Finsupp.induction_linear with
    | zero => simp
    | add Y Y' hY hY' => rw [mul_add, map_add, hY, hY', map_add, add_mul]
    | single e b =>
      rw [single_mul_single, flipCoeff_single, flipCoeff_single, flipCoeff_single,
        single_mul_single, hflip_mul, add_comm]

variable (G : GradingDatum Q)

omit [DecidableEq I] in
theorem dψ_sadj_smul (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) (j : ℕ) (i : Seq ν) :
    G.dψ j (sadj (Multiset.card ν) j • i) = G.dψ j i := by
  unfold dψ
  split_ifs with h
  · rw [lbl_sadj_smul, lbl_sadj_smul, sadj_apply_left h, sadj_apply_right h, hsymm]
  · rfl

/-- **The coaction intertwines `ψ`** (for symmetric crossing degrees):
`coaction (ψ a) = flip (coaction a)`. -/
theorem coaction_hflip (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) (u : A) :
    G.coaction (hflip u) = flipCoeff (G.coaction u) := by
  obtain ⟨u, rfl⟩ := mk_surjective u
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, hflip_algebraMap, AlgHom.commutes, AddMonoidAlgebra.coe_algebraMap,
      Function.comp_apply, flipCoeff_single, hflip_algebraMap]
  | grade1 g =>
    cases g with
    | idem i =>
      change G.coaction (hflip (e i)) = flipCoeff (G.coaction (e i))
      rw [hflip_e, coaction_e, flipCoeff_single, hflip_e]
    | dot a =>
      change G.coaction (hflip (x a)) = flipCoeff (G.coaction (x a))
      rw [hflip_x, coaction_x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [flipCoeff_single, hflip_mul, hflip_x, hflip_e, e_mul_x]
    | cross j =>
      change G.coaction (hflip (ψ j)) = flipCoeff (G.coaction (ψ j))
      rw [hflip_ψ, coaction_ψ, map_sum]
      simp only [flipCoeff_single, hflip_mul, hflip_ψ, hflip_e, e_mul_ψ]
      refine (Fintype.sum_equiv (MulAction.toPerm (sadj (Multiset.card ν) j)) _ _
        fun i => ?_).symm
      simp only [MulAction.toPerm_apply, sadj_smul_smul, G.dψ_sadj_smul hsymm]
  | mul u v hu hv =>
    rw [map_mul, hflip_mul, map_mul, hu, hv, map_mul, flipCoeff_mul]
  | add u v hu hv =>
    rw [map_add, hflip_add, map_add, hu, hv, map_add, map_add]

/-- **`ψ` preserves degrees** (for symmetric crossing degrees). -/
theorem hflip_mem_grade (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) {d : ℤ} {a : A}
    (ha : a ∈ G.grade ν d) : hflip a ∈ G.grade ν d := by
  rw [mem_grade] at ha ⊢
  rw [coaction_hflip G hsymm, ha, flipCoeff_single]

end GradingDatum

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- **KL I**: the antiinvolution `ψ` of `R(ν)` preserves degrees. -/
theorem hflip_mem_grade {d : ℤ} {a : R1 k Γ ν} (ha : a ∈ (klGradingDatum k Γ).grade ν d) :
    hflip a ∈ (klGradingDatum k Γ).grade ν d :=
  (klGradingDatum k Γ).hflip_mem_grade (fun a b => by
    show -cartan Γ a b = -cartan Γ b a
    rw [cartan_symm]) ha

end KL1

end Categorification.KLR
