/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived

/-!
# Webster's internal degree of a two-red braid coefficient

The rectangular coefficient of a two-red swap is supported in one coset
of the integers in the complex degree group. The coset offset is
`2 - ⟨λ_r, λ_d⟩`, replacing the auxiliary red/red degree of minus two.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR QuantumGroup TypeA

variable {I : Type} {k : Type*} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 2 → I →₀ ℕ} {ν : Multiset I}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin 2 → Module.Dual ℂ H)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))
local notation "μ" => stendhalWeight 2 ν
local notation "m" => Multiset.card (stendhalWeight 2 ν)
local notation "q" => violMk k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "δ" r:arg d:arg => (2 - B (η r) (η d))

private theorem intOffset_injective (c : ℂ) : Function.Injective (fun j : ℤ => (j : ℂ) + c) :=
  fun _ _ h => Int.cast_injective (add_right_cancel h)

/-- Webster's complex-valued grading of the whole two-red swap coefficient.
The coefficient ring itself is unchanged. -/
def twoRedSwapWeight (r d : Fin 2) (z : ℂ) :
    AddSubgroup (braidingBimodule k Q Λ ν [d, r] [r, d]) :=
  Function.extend (fun j : ℤ => (j : ℂ) + δ r d)
    (diagramCornerWeight (e := q (redProj k Q Λ ν [d, r]))
      (e' := q (redProj k Q Λ ν [r, d])) (violAuxiliaryGrade (ν := ν) G)) (fun _ => ⊥) z

@[simp] theorem twoRedSwapWeight_intAdd (r d : Fin 2) (j : ℤ) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d ((j : ℂ) + δ r d) =
      diagramCornerWeight (e := q (redProj k Q Λ ν [d, r]))
        (e' := q (redProj k Q Λ ν [r, d])) (violAuxiliaryGrade (ν := ν) G) j :=
  (intOffset_injective _).extend_apply _ _ _

/-- A tensor coefficient in integer coordinates acquires Webster's degree
when the output coordinate is based at the input origin plus the red swap offset. -/
theorem twoRedSwapWeight_coordinate (r d : Fin 2) (c : ℂ) (a b : ℤ) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d
      ((c + δ r d + (a : ℂ)) - (c + (b : ℂ))) =
      diagramCornerWeight (e := q (redProj k Q Λ ν [d, r]))
        (e' := q (redProj k Q Λ ν [r, d])) (violAuxiliaryGrade (ν := ν) G) (a - b) := by
  rw [← twoRedSwapWeight_intAdd C hQ B η]
  congr 1
  push_cast
  ring

theorem twoRedSwapWeight_eq_bot (r d : Fin 2) {z : ℂ}
    (hz : ¬ ∃ j : ℤ, (j : ℂ) + δ r d = z) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d z = ⊥ :=
  Function.extend_apply' _ _ _ hz

local notation "E" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "V" => violAuxiliaryGrade (ν := ν) G

/-- Multiplication on the left by a homogeneous corner element adds its
integer degree to the normalized coefficient degree. -/
theorem twoRedSwapWeight_left {r d : Fin 2} {i j : ℤ} {a : (E [d, r]).Corner}
    {x : braidingBimodule k Q Λ ν [d, r] [r, d]}
    (ha : a.val ∈ V i)
    (hx : x ∈ twoRedSwapWeight C hQ B η r d ((j : ℂ) + δ r d)) :
    a • x ∈ twoRedSwapWeight C hQ B η r d ((i : ℂ) + ((j : ℂ) + δ r d)) := by
  rw [← add_assoc, ← Int.cast_add, twoRedSwapWeight_intAdd]
  rw [twoRedSwapWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) ha hx

/-- Multiplication on the right adds the degree of the source corner element. -/
theorem twoRedSwapWeight_right {r d : Fin 2} {i j : ℤ} {a : (E [r, d]).Corner}
    {x : braidingBimodule k Q Λ ν [d, r] [r, d]}
    (ha : a.val ∈ V i)
    (hx : x ∈ twoRedSwapWeight C hQ B η r d ((j : ℂ) + δ r d)) :
    MulOpposite.op a • x ∈
      twoRedSwapWeight C hQ B η r d (((j : ℂ) + δ r d) + (i : ℂ)) := by
  rw [add_right_comm, ← Int.cast_add, twoRedSwapWeight_intAdd]
  rw [twoRedSwapWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) hx ha

/-- A reduced diagram from the source red order to the swapped order, with
homogeneous dots, lies in the piece prescribed by Webster's local degrees. -/
theorem twoRedSwap_mem_weight {t : Seq μ} {γ : List ℕ} {r d : Fin 2}
    (hγ : IsReduced m γ) (ht : redWord t = [r, d])
    (hs : redWord (wordProd m γ • t) = [d, r])
    {p : MvPolynomial (Fin m) k} {N : ℤ}
    (hp : p.IsWeightedHomogeneous (fun i => (G).degX (t.lbl i)) N) :
    ∃ x : braidingBimodule k Q Λ ν [d, r] [r, d],
      x.val = q (π (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t)) ∧
      x ∈ twoRedSwapWeight C hQ B η r d
        ((∑ a ∈ invSet m (wordProd m γ),
            websterCrossingDegree (Λ := Λ) C hQ B η (t.lbl a.1) (t.lbl a.2)) + (N : ℂ)) := by
  let y : KLRAlgebra k (stendhalQ Q Λ) μ := KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t
  have hfix : redIdem k Q Λ [d, r] * y * redIdem k Q Λ [r, d] = y := by
    change _ * (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t) * _ = _
    rw [redIdem_mul_std, ite_eq_left ⟨hs, ht⟩]
  have hfix' : q (redProj k Q Λ ν [d, r]) * q (π y) * q (redProj k Q Λ ν [r, d]) = q (π y) := by
    simpa only [redProj, map_mul] using congrArg (fun a => q (π a)) hfix
  have hL := isIdempotentElem_violMk_redProj k Q Λ ν [d, r]
  have hR := isIdempotentElem_violMk_redProj k Q Λ ν [r, d]
  refine ⟨⟨q (π y), mem_cornerBimodule.mpr ⟨?_, ?_⟩⟩, rfl, ?_⟩
  · nth_rw 1 [← hfix']
    rw [← mul_assoc, ← mul_assoc, hL.eq, hfix']
  · nth_rw 1 [← hfix']
    rw [mul_assoc, hR.eq, hfix']
  · rw [twoRedSwap_crossingDegree (Λ := Λ) C hQ B η hγ ht hs]
    rw [add_right_comm, ← Int.cast_add, twoRedSwapWeight_intAdd]
    exact Graded.mem_map_of_mem _ (q).toLinearMap
      (Graded.mem_map_of_mem _ (π).toLinearMap
        (GradingDatum.ψw_mul_pol_mul_e_mem_grade G γ t hp))

end Categorification.Stendhal.BraidedStendhalAlgebra
