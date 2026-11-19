/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global

/-!
# The vacuum supported on the empty block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. At the weight `-Λ` of the empty block,
`emptyBlockObj` carries the vacuum `R^Λ(∅) = k` on the empty block and zero on every other block
of that weight. Cyclotomic induction `F_i^Λ` kills it when `a_i = 1` (`isZero_globalE_obj`), since
`R^Λ({i}) = 0` (Kang–Kashiwara, arXiv:1102.4677v4, Lemma 4.4 for `⟨h_i, Λ⟩ = 0`), and cyclotomic
restriction kills it in every colour (`isZero_globalF_obj`).
-/

namespace Categorification.KLR

open CategoryTheory CategoryTheory.Limits

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

namespace CycKLR

/-- **`R^Λ(ν) = 0` when every colour of `ν` has `a_j = 1`** (`ν ≠ 0`). -/
theorem subsingleton_of_forall_eq_one {ν : Multiset I} (hν : ν ≠ 0) (ha : ∀ j ∈ ν, a j = 1) :
    Subsingleton (CycKLR k Q a ν) := by
  have hc : 0 < Multiset.card ν := Multiset.card_pos.mpr hν
  have h1 : (1 : CycKLR k Q a ν) = 0 := by
    rw [← map_one (mk k Q a ν), ← KLRAlgebra.sum_e, map_sum]
    refine Finset.sum_eq_zero fun s _ => mk_e_eq_zero_of_eq_one s hc (ha _ ?_)
    exact (congrArg (fun m => s.lbl ⟨0, hc⟩ ∈ m) s.2).mp
      (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))
  exact subsingleton_of_zero_eq_one h1.symm

end CycKLR

namespace CyclotomicAction

noncomputable section

variable {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}

variable (Q a RD Λ) in
/-- **The vacuum supported on the empty block**: `R^Λ(∅)` on the empty block and zero on the
other blocks of weight `-Λ`. -/
def emptyBlockObj : weightSpace.{u, v, w} Q a RD Λ (blockWeight RD Λ 0) :=
  fun β => ModuleCat.of (CycKLR k Q a β.1)
    (PLift (β.1 = 0) → ULift.{max (max u v) w} (CycKLR k Q a β.1))

theorem isZero_emptyBlockObj {β : WeightBlocks RD Λ (blockWeight RD Λ 0)} (hβ : β.1 ≠ 0) :
    IsZero (emptyBlockObj.{u, v, w} Q a RD Λ β) := by
  have : IsEmpty (PLift (β.1 = 0)) := ⟨fun p => hβ p.down⟩
  have : Subsingleton (emptyBlockObj.{u, v, w} Q a RD Λ β) :=
    show Subsingleton (PLift (β.1 = 0) → _) from inferInstance
  exact ModuleCat.isZero_of_subsingleton _

/-- An object of a weight space is zero if all its blocks are. -/
theorem isZero_of_forall {x : X} {V : weightSpace.{u, v, w} Q a RD Λ x}
    (hV : ∀ β, IsZero (V β)) : IsZero V where
  unique_to W := ⟨⟨⟨fun β => (hV β).to_ (W β)⟩, fun _ => funext fun β => (hV β).eq_of_src _ _⟩⟩
  unique_from W := ⟨⟨⟨fun β => (hV β).from_ (W β)⟩, fun _ => funext fun β => (hV β).eq_of_tgt _ _⟩⟩

/-- A biproduct of zero objects is zero. -/
theorem isZero_biproduct {D : Type*} [Category D] [Preadditive D] {J : Type*} [Finite J]
    [HasFiniteBiproducts D] (f : J → D) (hf : ∀ j, IsZero (f j)) : IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext _ _ fun j => (hf j).eq_of_tgt _ _

/-- **Induction kills objects supported on the empty block** in a colour with `a_i = 1`. -/
theorem isZero_globalE_obj (i : I) (hai : a i = 1) {x y : X} (h : x + RD.iX i = y)
    {V : weightSpace.{u, v, w} Q a RD Λ x} (hV : ∀ β, β.1 ≠ 0 → IsZero (V β)) :
    IsZero ((globalE.{u, v, w} Q a RD Λ i h).obj.obj V) := by
  refine isZero_of_forall fun δ => isZero_biproduct _ fun p => ?_
  by_cases hp : p.1.1 = 0
  · have hδ : δ.1 = {i} := by rw [← blockSucc_eq RD Λ i p.2, hp, add_zero]
    have : Subsingleton (CycKLR k Q a δ.1) :=
      CycKLR.subsingleton_of_forall_eq_one (by simp [hδ]) fun j hj => by
        rw [hδ, Multiset.mem_singleton] at hj
        rw [hj, hai]
    have : Subsingleton (((indBlock Q a RD Λ i h p.1 δ p.2).obj (V p.1) : ModuleCat _) :
        Type _) := Module.subsingleton (CycKLR k Q a δ.1) _
    exact ModuleCat.isZero_of_subsingleton _
  · exact Functor.map_isZero _ (hV _ hp)

/-- **Restriction kills objects supported on the empty block.** -/
theorem isZero_globalF_obj (i : I) {x y : X} (h : x + RD.iX i = y)
    {V : weightSpace.{u, v, w} Q a RD Λ y} (hV : ∀ β, β.1 ≠ 0 → IsZero (V β)) :
    IsZero ((globalF.{u, v, w} Q a RD Λ i h).obj.obj V) :=
  isZero_of_forall fun β => Functor.map_isZero (resBlock Q a RD Λ i h β _ rfl)
    (hV (blockSucc RD Λ i h β) (by simp))

end

end CyclotomicAction

end Categorification.KLR
