/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicWordRestriction
import Categorification.KLR.CyclotomicGradedFrobenius
import Categorification.KLR.CyclotomicGradedCharacter
import Categorification.KLR.Prop31G0

/-!
# Graded dimensions of arbitrary cyclotomic sequence corners

Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 and Definition 3.2. Removing the
rightmost source letter pairs it in turn with every matching target letter.
Its prefix supplies the grading shift, while the remaining target prefix
supplies the signed quantum integer. This gives a finite calculation involving
only the Cartan pairing, highest weight and two words.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean.QuantumGroup
local notation "LP" => LaurentPolynomial ℤ
local notation "LS" => LaurentSeries ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)

local notation "G" => hP.gradingDatum
local notation "M" => projectiveK0 G Λ
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))
local notation "raising" => fun i => raise G Λ i hP.klrSymm hP.polyInY_leading C
local notation "lowering" => lower G Λ
local notation "W" => sequenceClass hP Λ

private abbrev blockFinite (β : Multiset I) :
    Module.Finite k (CycKLR k Q (fun j => (Polynomial.X : Polynomial k)^Λ j) β) :=
  module_finite (fun i j hij => by obtain ⟨c,hc,he⟩ := hP.polyInY_leading i j hij; rw [he]; exact hc.map Polynomial.C)
    (fun _ => Polynomial.monic_X_pow _)

private local instance hasGdimBlock (β : Multiset I) : HasGdim (grade G Λ β) := by
  let := blockFinite hP Λ β
  exact HasGdim.of_finiteDimensional _

/-- The graded projective Hom form extended by orthogonality of distinct
cyclotomic weight blocks. -/
def totalHomForm : M →+ M →+ LS :=
  DirectSum.toAddMonoid fun β =>
    { toFun := fun x => (K0.homForm (grade G Λ β) x).comp
        (DirectSum.component LP _ (fun ν => K0 (grade G Λ ν)) β).toAddMonoidHom
      map_zero' := by ext z; simp only [map_zero,AddMonoidHom.zero_apply,AddMonoidHom.comp_apply]
      map_add' := fun x y => by
        ext z
        simp only [map_add,AddMonoidHom.add_apply,AddMonoidHom.comp_apply] }

private theorem total_lof (β : Multiset I) (x : K0 (grade G Λ β)) (y : M) :
    totalHomForm hP Λ (ι β x) y = K0.homForm (grade G Λ β) x (y β) := by
  unfold totalHomForm
  dsimp only [DirectSum.lof_eq_of]
  rw [DirectSum.toAddMonoid_of]
  rfl

private theorem total_lof_same (β : Multiset I) (x y : K0 (grade G Λ β)) :
    totalHomForm hP Λ (ι β x) (ι β y) = K0.homForm (grade G Λ β) x y := by
  rw [total_lof,DirectSum.lof_apply]

private theorem total_lof_ne {β γ : Multiset I} (h : β ≠ γ)
    (x : K0 (grade G Λ β)) (y : K0 (grade G Λ γ)) :
    totalHomForm hP Λ (ι β x) (ι γ y) = 0 := by
  rw [total_lof]
  change K0.homForm _ _ (DirectSum.component LP _ _ β (ι γ y)) = 0
  rw [DirectSum.component.of,dite_eq_right h.symm,map_zero]

private theorem total_smul_right (x y : M) (a : LP) :
    totalHomForm hP Λ x (a • y) = toLaurentSeries a * totalHomForm hP Λ x y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,AddMonoidHom.zero_apply,mul_zero]
  | add x z hx hz => simp only [map_add,AddMonoidHom.add_apply,hx,hz,mul_add]
  | of β z =>
    change totalHomForm hP Λ (ι β z) (a • y) = _ * totalHomForm hP Λ (ι β z) y
    rw [total_lof,total_lof]
    change K0.homForm _ _ ((DirectSum.component LP _ _ β) (a • y)) = _
    rw [map_smul]
    exact K0.map_smul_of_T (F := K0.homForm _ z) (fun d v => K0.homForm_T_smul_right d z v) a _

private theorem total_lower_lof (i : I) (β : Multiset I) (x : K0 (grade G Λ β)) (y : M) :
    totalHomForm hP Λ (lowering i (ι β x)) y =
      HahnSeries.single (-raiseShift Λ i β C) 1 * totalHomForm hP Λ (ι β x) (raising i y) := by
  rw [lower_lof]
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero,mul_zero]
  | add a b ha hb => rw [map_add,ha,hb,map_add,map_add,mul_add]
  | of γ z =>
    change totalHomForm hP Λ _ (ι γ z) = _ * totalHomForm hP Λ _ (raise G Λ i hP.klrSymm hP.polyInY_leading C (ι γ z))
    by_cases hi : i ∈ γ
    · obtain ⟨δ,hδ⟩ := Multiset.exists_cons_of_mem hi
      rw [← Multiset.singleton_add] at hδ
      subst γ
      rw [raise_lof]
      by_cases he : β = δ
      · subst δ
        rw [total_lof_same,total_lof_same,homForm_ind_res G Λ i β hP.klrSymm hP.polyInY_leading,
          raiseK0,LinearMap.smul_apply,K0.homForm_T_smul_right,←mul_assoc,
          HahnSeries.single_mul_single,neg_add_cancel,one_mul,HahnSeries.single_zero_one,one_mul]
      · rw [total_lof_ne hP Λ (fun h => he (add_left_cancel h)),total_lof_ne hP Λ he,mul_zero]
    · have hn : ({i} : Multiset I)+β ≠ γ := fun h => hi (h ▸ (by simp))
      rw [total_lof_ne hP Λ hn,raise_lof_of_notMem (h := hi),map_zero,mul_zero]

private abbrev wordBlock (w : List I) :=
  quotientK0 G Λ (w : Multiset I) (K0.of ((G).projP (Seq.ofList w rfl)))

private theorem word_lof (w : List I) : W w = ι (w : Multiset I) (wordBlock hP Λ w) :=
  totalQuotientK0_lof ..

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k)^Λ j)
local notation "π" => mk k Q aΛ

private abbrev eSeq {β : Multiset I} (w : Seq β) := π β (e w)

private theorem eSeq_idem {β : Multiset I} (w : Seq β) :
    IsIdempotentElem (eSeq (Q := Q) Λ w) :=
  (show IsIdempotentElem (e (Q := Q) w) from e_mul_self w).map (π β)

private abbrev wordProj {β : Multiset I} (w : Seq β) : GProj (grade G Λ β) :=
  GProj.ofIdempotent _ (eSeq_idem (Q := Q) Λ w)
    (Graded.mem_map_of_mem _ (π β).toLinearMap ((G).e_mem_grade w))

private theorem word_lof_at {β : Multiset I} (w : List I) (h : (w : Multiset I) = β) :
    W w = ι β (K0.of (wordProj hP Λ (Seq.ofList w h))) := by
  subst β
  rw [word_lof]
  exact congrArg _ (quotientK0_ofIdempotent G Λ _ _ _)

private theorem range_corner {β : Multiset I} (s t : Seq β) :
    LinearMap.range (((leftIdeal (eSeq (Q := Q) Λ t)).subtype.restrictScalars k).comp
      (idemSubspace k (leftIdeal (eSeq (Q := Q) Λ t)) (eSeq (Q := Q) Λ s)).subtype) =
      corner k Q aΛ s t := by
  apply le_antisymm
  · rintro _ ⟨⟨⟨x,hx⟩,hy⟩,rfl⟩
    have h₁ : x * eSeq Λ t = x := hx
    have h₂ : eSeq Λ s * x = x := congrArg Subtype.val hy
    exact ⟨x,show eSeq Λ s * (x * eSeq Λ t) = x by rw [h₁,h₂]⟩
  · rintro _ ⟨x,rfl⟩
    refine ⟨⟨⟨eSeq Λ s * (x * eSeq Λ t),?_⟩,Subtype.ext ?_⟩,rfl⟩
    · change eSeq Λ s * (x * eSeq Λ t) * eSeq Λ t = _
      simp only [mul_assoc,(eSeq_idem (Q := Q) Λ t).eq]
    · change eSeq Λ s * (eSeq Λ s * (x * eSeq Λ t)) = _
      rw [← mul_assoc _ _ (x * eSeq Λ t),(eSeq_idem (Q := Q) Λ s).eq]

private theorem coeff_totalHom_words {β : Multiset I} (s t : List I)
    (hs : (s : Multiset I) = β) (ht : (t : Multiset I) = β) (d : ℤ) :
    (totalHomForm hP Λ (W s) (W t)).coeff d =
      (Module.finrank k ↥(grade G Λ β d ⊓ corner k Q aΛ (Seq.ofList s hs) (Seq.ofList t ht)) : ℤ) := by
  rw [word_lof_at hP Λ s hs,word_lof_at hP Λ t ht,total_lof_same,K0.homForm_of,GProj.homGdim,coeff_gdim]
  congr 1
  let j := Seq.ofList s hs
  let i := Seq.ofList t ht
  have he := (homGradeIdemEquiv (𝒜 := grade G Λ β) (ℳ := (wordProj hP Λ i).grading)
    (eSeq_idem (Q := Q) Λ j) (Graded.mem_map_of_mem _ (π β).toLinearMap ((G).e_mem_grade j)) d).finrank_eq
  refine he.trans ?_
  have hc := finrank_comap (grade G Λ β) (f :=
    ((leftIdeal (eSeq (Q := Q) Λ i)).subtype.restrictScalars k).comp
      (idemSubspace k (leftIdeal (eSeq (Q := Q) Λ i)) (eSeq (Q := Q) Λ j)).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) d
  rw [range_corner] at hc
  exact hc

private theorem total_vacuum_words (t : List I) :
    totalHomForm hP Λ (W []) (W t) = toLaurentSeries (if t = [] then 1 else 0) := by
  cases t with
  | nil =>
    rw [ite_eq_left rfl,←LaurentPolynomial.T_zero,K0.toLaurentSeries_T]
    ext d
    rw [coeff_totalHom_words hP Λ [] [] (β := 0) rfl rfl]
    have hc : corner (ν := (0 : Multiset I)) k Q aΛ (Seq.ofList [] rfl)
        (Seq.ofList [] rfl) = ⊤ := by
      apply top_unique
      intro x _
      refine ⟨x, ?_⟩
      change π (0 : Multiset I) (e (Seq.ofList [] (show (([] : List I) : Multiset I) = 0 from rfl))) *
        (x * π (0 : Multiset I) (e (Seq.ofList [] (show (([] : List I) : Multiset I) = 0 from rfl)))) = x
      simp only [e_eq_one,map_one,mul_one,one_mul]
    rw [hc,inf_top_eq,finrank_emptyGrade,HahnSeries.coeff_single]
    split_ifs <;> simp_all
  | cons a t =>
    rw [word_lof hP Λ [],word_lof hP Λ (a::t),ite_eq_right (by simp),map_zero]
    apply total_lof_ne
    exact fun he => Multiset.cons_ne_zero (show a ::ₘ (t : Multiset I) = 0 from he.symm)

private theorem total_word_snoc (s t : List I) (i : I) :
    totalHomForm hP Λ (W (s++[i])) (W t) =
      toLaurentSeries (T (di C i * (prefixPair C Λ i s - 1))) *
        totalHomForm hP Λ (W s) (raising i (W t)) := by
  rw [sequenceClass_append,word_lof hP Λ s,total_lower_lof,K0.toLaurentSeries_T]
  have he : -raiseShift Λ i (s : Multiset I) C = di C i * (prefixPair C Λ i s - 1) := by
    simp only [raiseShift,prefixPair,Multiset.map_coe,Multiset.sum_coe]
    ring
  rw [he]

/-- Hu–Shi's two-word dimension polynomial. The source is passed in reverse
order so that the recursion consumes its rightmost strand first. The list of
marked target words sums over all choices of a matching letter. -/
def huShiFromRight (C : CartanDatum I) (Λ : I → ℕ) : List I → List I → LP
  | [], t => if t = [] then 1 else 0
  | i::s, t => T (di C i * (prefixPair C Λ i s.reverse-1)) *
      ((markedWords t).map fun z => if i = z.2.1 then
        qIntU (qUnitLP ^ di C i) (prefixPair C Λ i z.1) *
        huShiFromRight C Λ s (z.1++z.2.2) else 0).sum

/-- The two words in their usual left-to-right order. -/
def huShiPolynomial (C : CartanDatum I) (Λ : I → ℕ) (s t : List I) : LP :=
  huShiFromRight C Λ s.reverse t

include hΛ in
private theorem homForm_fromRight (rev t : List I) :
    totalHomForm hP Λ (W rev.reverse) (W t) = toLaurentSeries (huShiFromRight C Λ rev t) := by
  induction rev generalizing t with
  | nil => exact total_vacuum_words hP Λ t
  | cons i s ih =>
    rw [List.reverse_cons,total_word_snoc,raise_sequenceClass hP Λ RD highest hΛ,
      huShiFromRight,toLaurentSeries_mul,map_list_sum,map_list_sum]
    apply congrArg (_ * ·)
    apply congrArg List.sum
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro z _
    split_ifs
    · rw [total_smul_right,ih,toLaurentSeries_mul]
    · rw [map_zero,map_zero]

private def pairingDatum (C : CartanDatum I) : WeightDatum C (I → ℤ) ((I → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A C i j
  iY i := { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  pair_iY_iX _ _ := rfl

/-- Hu–Shi, arXiv:2108.05508v5, Theorem 1.1, expressed by recursively choosing
the matching position for the rightmost source letter. The grading shift uses
the undisturbed source prefix, and the quantum integer uses the surviving
target prefix (Definition 3.2). This applies to repeated and adjacent colours
in arbitrary positions, for homogeneous Rouquier parameters. -/
theorem finrank_cornerGrade_huShi {β : Multiset I} (s t : Seq β) (d : ℤ) :
    (Module.finrank k ↥(grade G Λ β d ⊓ corner k Q aΛ s t) : ℤ) =
      (huShiPolynomial C Λ (List.ofFn s.1) (List.ofFn t.1)).coeff d := by
  have hc := coeff_totalHom_words hP Λ _ _ (Seq.coe_ofFn s) (Seq.coe_ofFn t) d
  rw [Seq.ofList_ofFn,Seq.ofList_ofFn] at hc
  rw [← hc,huShiPolynomial,← List.reverse_reverse (List.ofFn s.1),
    homForm_fromRight hP Λ (pairingDatum C) (fun i => (Λ i : ℤ)) (fun _ => rfl),
    coeff_toLaurentSeries,List.reverse_reverse]

end Categorification.KLR.CycKLR
