/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentRedSwapNormalization

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

/-- Webster's complex-valued grading of the whole two-red swap coefficient.
The coefficient ring itself is unchanged. -/
def twoRedSwapWeight (r d : Fin 2) (z : ℂ) :
    AddSubgroup (braidingBimodule k Q Λ ν [d, r] [r, d]) :=
  adjacentRedSwapWeight C hQ B η [] [] r d z

@[simp] theorem twoRedSwapWeight_intAdd (r d : Fin 2) (j : ℤ) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d ((j : ℂ) + δ r d) =
      diagramCornerWeight (e := q (redProj k Q Λ ν [d, r]))
        (e' := q (redProj k Q Λ ν [r, d])) (violAuxiliaryGrade (ν := ν) G) j :=
  adjacentRedSwapWeight_intAdd C hQ B η [] [] r d j

/-- A tensor coefficient in integer coordinates acquires Webster's degree
when the output coordinate is based at the input origin plus the red swap offset. -/
theorem twoRedSwapWeight_coordinate (r d : Fin 2) (c : ℂ) (a b : ℤ) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d
      ((c + δ r d + (a : ℂ)) - (c + (b : ℂ))) =
      diagramCornerWeight (e := q (redProj k Q Λ ν [d, r]))
        (e' := q (redProj k Q Λ ν [r, d])) (violAuxiliaryGrade (ν := ν) G) (a - b) :=
  adjacentRedSwapWeight_coordinate C hQ B η [] [] r d c a b

theorem twoRedSwapWeight_eq_bot (r d : Fin 2) {z : ℂ}
    (hz : ¬ ∃ j : ℤ, (j : ℂ) + δ r d = z) :
    twoRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η r d z = ⊥ :=
  adjacentRedSwapWeight_eq_bot (Λ := Λ) C hQ B η [] [] r d hz

local notation "E" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "V" => violAuxiliaryGrade (ν := ν) G

/-- Multiplication on the left by a homogeneous corner element adds its
integer degree to the normalized coefficient degree. -/
theorem twoRedSwapWeight_left {r d : Fin 2} {i j : ℤ} {a : (E [d, r]).Corner}
    {x : braidingBimodule k Q Λ ν [d, r] [r, d]}
    (ha : a.val ∈ V i)
    (hx : x ∈ twoRedSwapWeight C hQ B η r d ((j : ℂ) + δ r d)) :
    a • x ∈ twoRedSwapWeight C hQ B η r d ((i : ℂ) + ((j : ℂ) + δ r d)) :=
  adjacentRedSwapWeight_left C hQ B η ha hx

/-- Multiplication on the right adds the degree of the source corner element. -/
theorem twoRedSwapWeight_right {r d : Fin 2} {i j : ℤ} {a : (E [r, d]).Corner}
    {x : braidingBimodule k Q Λ ν [d, r] [r, d]}
    (ha : a.val ∈ V i)
    (hx : x ∈ twoRedSwapWeight C hQ B η r d ((j : ℂ) + δ r d)) :
    MulOpposite.op a • x ∈
      twoRedSwapWeight C hQ B η r d (((j : ℂ) + δ r d) + (i : ℂ)) :=
  adjacentRedSwapWeight_right C hQ B η ha hx

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
  have hdegree : websterCrossingDegree (Λ := Λ) C hQ B η = crossingDegree (Λ := Λ) C hQ B η := by
    funext a b
    cases a <;> cases b <;> rfl
  rw [hdegree]
  exact adjacentRedSwap_mem_weight (L := []) (M := []) (r := r) (d := d) (t := t) (γ := γ)
    (p := p) (N := N) C hQ B η hγ ht hs hp

end Categorification.Stendhal.BraidedStendhalAlgebra
