/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived

/-!
# The graded coefficient for an adjacent red swap

An adjacent swap in an arbitrary red order changes the relative order
of exactly one pair of red strands. Its rectangular bimodule is graded
in the integer coset with offset determined by that pair's weight pairing.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR QuantumGroup TypeA

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "q" => violMk k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "δ" r:arg d:arg => (2 - B (η r) (η d))

private theorem intOffset_injective (c : ℂ) : Function.Injective (fun j : ℤ => (j : ℂ) + c) :=
  fun _ _ h => Int.cast_injective (add_right_cancel h)

/-- Webster's local degree specializes the red/red contribution to the weight pairing. -/
def crossingDegree : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℂ
  | .inr a, .inr b => -B (η a) (η b)
  | a, b => ((G).degΨ a b : ℂ)

omit [DecidableEq I] in
/-- In a reduced adjacent transposition, the only changed contribution is the
unique inverted pair of red strands. -/
theorem adjacentRedSwap_crossingDegree {t : Seq μ} {L M : List (Fin ℓ)} {r d : Fin ℓ} {γ : List ℕ}
    (hγ : TypeA.IsReduced m γ) (ht : redWord t = L ++ r :: d :: M)
    (hs : redWord (wordProd m γ • t) = L ++ d :: r :: M) :
    (∑ p ∈ invSet m (wordProd m γ), crossingDegree (Λ := Λ) C hQ B η (t.lbl p.1) (t.lbl p.2)) =
      ((G).degW γ t : ℂ) + (2 - B (η r) (η d)) := by
  obtain ⟨a, ha⟩ := exists_lbl_eq_inr t r
  obtain ⟨b, hb⟩ := exists_lbl_eq_inr t d
  have hab : a < b := by
    have h := redWord_pairwise_one t
    rw [ht, List.pairwise_append, List.pairwise_cons] at h
    exact h.2.1.1 d (by simp) a b ha hb
  have hswap := (redWord_smul_eq_swap_iff ht ha hb (wordProd m γ)).1 hs
  let S := invSet m (wordProd m γ)
  have hmem : (a, b) ∈ S := mem_invSet.mpr ⟨hab,
    (hswap a b (by simp [ha]) (by simp [hb]) hab).2 ⟨rfl, rfl⟩⟩
  have hrest : (∑ p ∈ S.erase (a, b), crossingDegree (Λ := Λ) C hQ B η (t.lbl p.1) (t.lbl p.2)) =
      ∑ p ∈ S.erase (a, b), ((G).degΨ (t.lbl p.1) (t.lbl p.2) : ℂ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hi := mem_invSet.mp ((Finset.mem_erase.mp hp).2 : p ∈ invSet m (wordProd m γ))
    rcases hx : t.lbl p.1 with i | x <;> rcases hy : t.lbl p.2 with j | y <;> try rfl
    obtain ⟨h₁, h₂⟩ := (hswap p.1 p.2 (by simp [hx]) (by simp [hy]) hi.1).1 hi.2
    exact ((Finset.mem_erase.mp hp).1 (Prod.ext h₁ h₂)).elim
  rw [GradingDatum.degW_eq_sum_invSet _ hγ]
  let f : Fin m × Fin m → ℂ := fun p => crossingDegree (Λ := Λ) C hQ B η (t.lbl p.1) (t.lbl p.2)
  let fZ : Fin m × Fin m → ℤ := fun p => (G).degΨ (t.lbl p.1) (t.lbl p.2)
  change (∑ p ∈ S, f p) = ((∑ p ∈ S, fZ p : ℤ) : ℂ) + _
  calc
    (∑ p ∈ S, f p) = (∑ p ∈ S.erase (a, b), f p) + f (a, b) :=
      (Finset.sum_erase_add S f hmem).symm
    _ = ((∑ p ∈ S.erase (a, b), fZ p : ℤ) : ℂ) - B (η r) (η d) := by
      change (∑ p ∈ S.erase (a, b), crossingDegree (Λ := Λ) C hQ B η (t.lbl p.1) (t.lbl p.2)) + _ = _
      rw [hrest, Int.cast_sum, sub_eq_add_neg]
      simp only [f, ha, hb, crossingDegree]
      rfl
    _ = ((∑ p ∈ S, fZ p : ℤ) : ℂ) + (2 - B (η r) (η d)) := by
      have hsum := Finset.sum_erase_add S fZ hmem
      have hlast : fZ (a, b) = -2 := by
        change (G).degΨ (t.lbl a) (t.lbl b) = -2
        rw [ha, hb]
        rfl
      rw [← hsum, hlast, Int.cast_add, Int.cast_neg, Int.cast_two]
      ring

/-- Webster's complex-valued grading of the whole adjacent-swap coefficient.
The coefficient ring itself is unchanged. -/
def adjacentRedSwapWeight (L M : List (Fin ℓ)) (r d : Fin ℓ) (z : ℂ) :
    AddSubgroup (braidingBimodule k Q Λ ν (L ++ d :: r :: M) (L ++ r :: d :: M)) :=
  Function.extend (fun j : ℤ => (j : ℂ) + δ r d)
    (diagramCornerWeight (e := q (redProj k Q Λ ν (L ++ d :: r :: M)))
      (e' := q (redProj k Q Λ ν (L ++ r :: d :: M))) (violAuxiliaryGrade (ν := ν) G)) (fun _ => ⊥) z

@[simp] theorem adjacentRedSwapWeight_intAdd (L M : List (Fin ℓ)) (r d : Fin ℓ) (j : ℤ) :
    adjacentRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η L M r d ((j : ℂ) + δ r d) =
      diagramCornerWeight (e := q (redProj k Q Λ ν (L ++ d :: r :: M)))
        (e' := q (redProj k Q Λ ν (L ++ r :: d :: M))) (violAuxiliaryGrade (ν := ν) G) j :=
  (intOffset_injective _).extend_apply _ _ _

/-- A tensor coefficient in integer coordinates acquires Webster's degree
when the output coordinate is based at the input origin plus the red swap offset. -/
theorem adjacentRedSwapWeight_coordinate (L M : List (Fin ℓ)) (r d : Fin ℓ) (c : ℂ) (a b : ℤ) :
    adjacentRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η L M r d
      ((c + δ r d + (a : ℂ)) - (c + (b : ℂ))) =
      diagramCornerWeight (e := q (redProj k Q Λ ν (L ++ d :: r :: M)))
        (e' := q (redProj k Q Λ ν (L ++ r :: d :: M))) (violAuxiliaryGrade (ν := ν) G) (a - b) := by
  rw [← adjacentRedSwapWeight_intAdd C hQ B η L M]
  congr 1
  push_cast
  ring

theorem adjacentRedSwapWeight_eq_bot (L M : List (Fin ℓ)) (r d : Fin ℓ) {z : ℂ}
    (hz : ¬ ∃ j : ℤ, (j : ℂ) + δ r d = z) :
    adjacentRedSwapWeight (Λ := Λ) (ν := ν) C hQ B η L M r d z = ⊥ :=
  Function.extend_apply' _ _ _ hz

local notation "E" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "V" => violAuxiliaryGrade (ν := ν) G

/-- Multiplication on the left by a homogeneous corner element adds its
integer degree to the normalized coefficient degree. -/
theorem adjacentRedSwapWeight_left {L M : List (Fin ℓ)} {r d : Fin ℓ} {i j : ℤ} {a : (E (L ++ d :: r :: M)).Corner}
    {x : braidingBimodule k Q Λ ν (L ++ d :: r :: M) (L ++ r :: d :: M)}
    (ha : a.val ∈ V i)
    (hx : x ∈ adjacentRedSwapWeight C hQ B η L M r d ((j : ℂ) + δ r d)) :
    a • x ∈ adjacentRedSwapWeight C hQ B η L M r d ((i : ℂ) + ((j : ℂ) + δ r d)) := by
  rw [← add_assoc, ← Int.cast_add, adjacentRedSwapWeight_intAdd]
  rw [adjacentRedSwapWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) ha hx

/-- Multiplication on the right adds the degree of the source corner element. -/
theorem adjacentRedSwapWeight_right {L M : List (Fin ℓ)} {r d : Fin ℓ} {i j : ℤ} {a : (E (L ++ r :: d :: M)).Corner}
    {x : braidingBimodule k Q Λ ν (L ++ d :: r :: M) (L ++ r :: d :: M)}
    (ha : a.val ∈ V i)
    (hx : x ∈ adjacentRedSwapWeight C hQ B η L M r d ((j : ℂ) + δ r d)) :
    MulOpposite.op a • x ∈
      adjacentRedSwapWeight C hQ B η L M r d (((j : ℂ) + δ r d) + (i : ℂ)) := by
  rw [add_right_comm, ← Int.cast_add, adjacentRedSwapWeight_intAdd]
  rw [adjacentRedSwapWeight_intAdd] at hx
  exact SetLike.GradedMul.mul_mem (A := V) hx ha

/-- A reduced diagram from the source red order to the swapped order, with
homogeneous dots, lies in the piece prescribed by Webster's local degrees. -/
theorem adjacentRedSwap_mem_weight {t : Seq μ} {γ : List ℕ} {L M : List (Fin ℓ)} {r d : Fin ℓ}
    (hγ : IsReduced m γ) (ht : redWord t = (L ++ r :: d :: M))
    (hs : redWord (wordProd m γ • t) = (L ++ d :: r :: M))
    {p : MvPolynomial (Fin m) k} {N : ℤ}
    (hp : p.IsWeightedHomogeneous (fun i => (G).degX (t.lbl i)) N) :
    ∃ x : braidingBimodule k Q Λ ν (L ++ d :: r :: M) (L ++ r :: d :: M),
      x.val = q (π (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t)) ∧
      x ∈ adjacentRedSwapWeight C hQ B η L M r d
        ((∑ a ∈ invSet m (wordProd m γ),
            crossingDegree (Λ := Λ) C hQ B η (t.lbl a.1) (t.lbl a.2)) + (N : ℂ)) := by
  let y : KLRAlgebra k (stendhalQ Q Λ) μ := KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t
  have hfix : redIdem k Q Λ (L ++ d :: r :: M) * y * redIdem k Q Λ (L ++ r :: d :: M) = y := by
    change _ * (KLRAlgebra.ψw γ * KLRAlgebra.pol p * KLRAlgebra.e t) * _ = _
    rw [redIdem_mul_std, ite_eq_left ⟨hs, ht⟩]
  have hfix' : q (redProj k Q Λ ν (L ++ d :: r :: M)) * q (π y) * q (redProj k Q Λ ν (L ++ r :: d :: M)) = q (π y) := by
    simpa only [redProj, map_mul] using congrArg (fun a => q (π a)) hfix
  have hL := isIdempotentElem_violMk_redProj k Q Λ ν (L ++ d :: r :: M)
  have hR := isIdempotentElem_violMk_redProj k Q Λ ν (L ++ r :: d :: M)
  refine ⟨⟨q (π y), mem_cornerBimodule.mpr ⟨?_, ?_⟩⟩, rfl, ?_⟩
  · nth_rw 1 [← hfix']
    rw [← mul_assoc, ← mul_assoc, hL.eq, hfix']
  · nth_rw 1 [← hfix']
    rw [mul_assoc, hR.eq, hfix']
  · rw [adjacentRedSwap_crossingDegree (Λ := Λ) C hQ B η hγ ht hs]
    rw [add_right_comm, ← Int.cast_add, adjacentRedSwapWeight_intAdd]
    exact Graded.mem_map_of_mem _ (q).toLinearMap
      (Graded.mem_map_of_mem _ (π).toLinearMap
        (GradingDatum.ψw_mul_pol_mul_e_mem_grade G γ t hp))

end Categorification.Stendhal.BraidedStendhalAlgebra
