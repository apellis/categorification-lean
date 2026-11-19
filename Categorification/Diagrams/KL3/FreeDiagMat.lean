/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Upward

/-!
# KLR diagrams before imposing relations

The map `toDiagFree k Q ν` from the free algebra on the KLR generators to the diagrammatic KLR
algebra `DiagR k Q ν` depends on the parameters `Q` only through the quotient functor of the
presentation `pres k Q`. This file lifts it to the matrix algebra of linear combinations of
diagrams in the free category (`freeDiagMat`, independent of `Q`), with
`matEndMap_freeDiagMat`: the quotient functor of any `pres k Q` recovers `toDiagFree k Q ν`.
This lets one evaluate the same linear combinations of diagrams in two presentations with
different parameters, as in the proof of Webster, arXiv:1309.3796v3, Lemma 4.29.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams TypeA MatEnd

universe u

variable {I : Type u} [DecidableEq I] {k : Type*} [CommRing k] {ν : Multiset I}

local notation "m" => Multiset.card ν

variable (k ν) in
/-- The matrix algebra of linear combinations of diagrams between the words of `Seq ν`, in the
free linear category on the KLR signature. -/
abbrev FreeDiagR : Type _ :=
  MatEnd (fun i : Seq ν => (Free.of k (ob (word i)) : Free k (Obj (sig I))))

variable (k) in
/-- The crossing of strands `j` and `j + 1` of `word i`, as a linear combination of diagrams
(zero if `j + 1 ≥ m`). -/
def freeCross (i : Seq ν) (j : ℕ) : LinDiagram k (ob (word i)) (ob (word (sadj m j • i))) :=
  if h : j + 1 < m then LinDiagram.of (crossD i h) else 0

variable (k ν) in
/-- Images of the KLR generators in `FreeDiagR`. -/
def freeGen : KLR.Gen ν → FreeDiagR k ν
  | .idem i => single i i (𝟙 _)
  | .dot a => ∑ i, single i i (LinDiagram.of (dotD i a))
  | .cross j => ∑ i, single i (sadj m j • i) (freeCross k i j)

variable (k ν) in
/-- The free algebra on the KLR generators, mapped to linear combinations of diagrams. -/
def freeDiagMat : FreeAlgebra k (KLR.Gen ν) →ₐ[k] FreeDiagR k ν :=
  FreeAlgebra.lift k (freeGen k ν)

/-- The quotient functor of `pres k Q` sends `freeGen` to the generator images `genImg`. -/
theorem matEndMap_freeGen (Q : I → I → MvPolynomial (Fin 2) k) (g : KLR.Gen ν) :
    KL3.Diagram.matEndMap k (pres k Q).linFunctor _ (freeGen k ν g) = genImg k Q ν g := by
  cases g with
  | idem i =>
    change KL3.Diagram.matEndMap k _ _ (single i i (𝟙 _)) = single i i (𝟙 _)
    rw [KL3.Diagram.matEndMap_single]
    exact congrArg _ (CategoryTheory.Functor.map_id _ _)
  | dot a =>
    unfold freeGen genImg DiagR.X
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [KL3.Diagram.matEndMap_single]
    rfl
  | cross j =>
    unfold freeGen genImg DiagR.Ψ
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [KL3.Diagram.matEndMap_single]
    congr 1
    unfold freeCross crossE
    split_ifs
    · rfl
    · exact Functor.map_zero _ _ _

/-- The quotient functor of `pres k Q` sends `freeDiagMat` to `toDiagFree k Q ν`, for every
parameter `Q`. -/
theorem matEndMap_freeDiagMat (Q : I → I → MvPolynomial (Fin 2) k)
    (a : FreeAlgebra k (KLR.Gen ν)) :
    KL3.Diagram.matEndMap k (pres k Q).linFunctor _ (freeDiagMat k ν a) =
      toDiagFree k Q ν a := by
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]; rfl
  | grade1 g =>
    rw [freeDiagMat, toDiagFree, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    exact matEndMap_freeGen Q g
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]; rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; rfl

/-- Entrywise form of `matEndMap_freeDiagMat`. -/
theorem lin_freeDiagMat (Q : I → I → MvPolynomial (Fin 2) k)
    (a : FreeAlgebra k (KLR.Gen ν)) (s t : Seq ν) :
    (pres k Q).lin (freeDiagMat k ν a s t) = toDiagFree k Q ν a s t :=
  congrFun (congrFun (matEndMap_freeDiagMat Q a) s) t

end Categorification.KLR.Diagram
