/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Grading
import Categorification.WeightedKLR.KLR.SpacedSurjective
import Categorification.WeightedKLR.Mackey.ShuffleDegree

/-!
# The grading on the evenly spaced loading family

Supporting the map from the positive quantum group to graded projective `K₀` in B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19,
roadmap C. Proposition 2.14 identifies the ordinary KLR algebra with the algebra on the
family of evenly spaced loadings, retaining one copy for each sequence even when two
sequences determine the same chamber. This file compares its grading with the weighted
gallery grading over any commutative coefficient ring. The degree convention is the
library's doubled normalization of Webster's degree convention.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum

section ComponentPreimage

variable {k A B : Type*} [CommRing k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (ℬ : ℤ → Submodule k B) (φ : A →ₐ[k] B)

private def componentPreimage : Submodule k A where
  carrier := {a | ∀ d, φ (decompose 𝒜 a d : A) ∈ ℬ d}
  zero_mem' d := by simp
  add_mem' ha hb d := by
    simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add, map_add]
    exact (ℬ d).add_mem (ha d) (hb d)
  smul_mem' c a ha d := by
    simp only [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, map_smul]
    exact (ℬ d).smul_mem c (ha d)

private theorem mem_componentPreimage_of_homogeneous {a : A} {d : ℤ}
    (ha : a ∈ 𝒜 d) (hb : φ a ∈ ℬ d) : a ∈ componentPreimage 𝒜 ℬ φ := by
  intro i
  by_cases hi : d = i
  · subst i
    rwa [decompose_of_mem_same _ ha]
  · rw [decompose_of_mem_ne _ ha hi, map_zero]
    exact (ℬ i).zero_mem

private theorem componentPreimage_mul
    (hmul : ∀ i j, ∀ x ∈ ℬ i, ∀ y ∈ ℬ j, x * y ∈ ℬ (i + j))
    {a b : A} (ha : a ∈ componentPreimage 𝒜 ℬ φ)
    (hb : b ∈ componentPreimage 𝒜 ℬ φ) : a * b ∈ componentPreimage 𝒜 ℬ φ := by
  classical
  intro d
  have he : a * b = ∑ i ∈ (decompose 𝒜 a).support, ∑ j ∈ (decompose 𝒜 b).support,
      (decompose 𝒜 a i : A) * (decompose 𝒜 b j : A) := by
    simp only [← Finset.mul_sum, sum_support_decompose, ← Finset.sum_mul]
  have he' := congrArg (fun x => (decompose 𝒜 x d : A)) he
  simp only [decompose_sum, DirectSum.sum_apply, Submodule.coe_sum] at he'
  rw [he', map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_sum]
  apply Submodule.sum_mem
  intro j _
  have hsrc : (decompose 𝒜 a i : A) * (decompose 𝒜 b j : A) ∈ 𝒜 (i + j) :=
    SetLike.GradedMul.mul_mem (decompose 𝒜 a i).property (decompose 𝒜 b j).property
  have htgt : φ ((decompose 𝒜 a i : A) * (decompose 𝒜 b j : A)) ∈ ℬ (i + j) := by
    rw [map_mul]
    exact hmul i j _ (ha i) _ (hb j)
  exact mem_componentPreimage_of_homogeneous 𝒜 ℬ φ hsrc htgt d

end ComponentPreimage

end Categorification.Graded

namespace Categorification.WeightedKLR

open MvPolynomial GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GradingDatum

variable (G : GradingDatum Γ)

private def edgeDegree (a b : I) : ℤ :=
  ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = a ∧ Γ.head e = b), G.wall e

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem edgeProd_homogeneous (a b : I) :
    (Γ.edgeProd a b).IsWeightedHomogeneous ![G.dot b, G.dot a]
      (2 * G.edgeDegree a b) := by
  classical
  have h := IsWeightedHomogeneous.prod
    (Finset.univ.filter (fun e => Γ.tail e = a ∧ Γ.head e = b)) Γ.Q
    (fun e => 2 * G.wall e) (fun e he => by
      obtain ⟨ht, hh⟩ := (Finset.mem_filter.1 he).2
      simpa only [ht, hh] using G.isWeightedHomogeneous_Q e)
  simpa only [WeightedGraph.edgeProd, edgeDegree, Finset.mul_sum] using h

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem edgeDegree_sum (a b : I) :
    G.edgeDegree a b = ∑ e, if b = Γ.head e ∧ a = Γ.tail e then G.wall e else 0 := by
  classical
  unfold edgeDegree
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  apply propext
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂.symm, h₁.symm⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem pairDeg_of_ne {a b : I} (hab : a ≠ b) :
    G.pairDeg a b = G.edgeDegree b a + G.edgeDegree a b := by
  rw [pairDeg, ite_eq_right hab, add_zero, G.edgeDegree_sum, G.edgeDegree_sum]

/-- The ordinary KLR grading corresponding to a loop-free weighted grading. Its crossing
degree is the total degree of the walls and diagonal joining the two strands. -/
def toKLRGrading (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) :
    KLR.GradingDatum Γ.klrQ where
  degX := G.dot
  degΨ := G.pairDeg
  degΨ_self a := by
    simp only [pairDeg]
    have he : ∀ e : Γ.E, ¬(a = Γ.head e ∧ a = Γ.tail e) := by
      intro e h
      exact hne e (h.1.symm.trans h.2)
    simp only [he, ite_false, Finset.sum_const_zero, ite_true, zero_add]
    exact G.cross_of_loop_none a (hl a)
  isWeightedHomogeneous a b hab := by
    have h₁ := G.edgeProd_homogeneous b a
    have h₂ := isWeightedHomogeneous_rename ![1, 0]
      (w := ![G.dot b, G.dot a]) (w' := ![G.dot a, G.dot b])
      (by intro c; fin_cases c <;> rfl) (G.edgeProd_homogeneous a b)
    have h := h₁.mul h₂
    have heq : G.pairDeg a b + G.pairDeg b a =
        2 * G.edgeDegree b a + 2 * G.edgeDegree a b := by
      rw [G.pairDeg_of_ne hab, G.pairDeg_of_ne (Ne.symm hab)]
      ring
    rw [heq]
    exact h

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem toKLRGrading_degX (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none) (i : I) : (G.toKLRGrading hne hl).degX i = G.dot i := rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem toKLRGrading_degΨ (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none) (i j : I) :
    (G.toKLRGrading hne hl).degΨ i j = G.pairDeg i j := rfl

/-- The degree of the gallery swapping two adjacent positions is the pair crossing degree. -/
theorem galDeg_crossWord {ν : Multiset I} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < ν.card) :
    G.galDeg (spacedFull Γ i) (crossWord Γ i n h) =
      G.pairDeg (i.lbl ⟨n, by omega⟩) (i.lbl ⟨n + 1, h⟩) := by
  classical
  let a := leftStrand i n h
  let b := rightStrand i n h
  have hab : a ≠ b := leftStrand_ne_rightStrand i n h
  have hset : (crossWord Γ i n h).toFinset = Finset.univ.filter
      (fun x : Hyp Γ ν.toFinsupp => (x.lo = a ∧ x.hi = b) ∨ (x.lo = b ∧ x.hi = a)) := by
    ext x
    simp only [List.mem_toFinset, mem_crossWord, Finset.mem_filter, Finset.mem_univ, true_and]
    cases x <;> rfl
  rw [G.galDeg_of_goodWord (goodWord_crossWord i n h hD hZ).1,
    ← List.sum_toFinset _ (nodup_crossWord i n h), hset]
  have hs := G.sum_hypDeg_joins (fun s : Strand ν.toFinsupp => s = a) (fun s => s = b)
    (fun s ha hb => hab (ha.symm.trans hb))
  simpa only [Finset.filter_eq', Finset.mem_univ, ite_true, Finset.sum_singleton,
    a, b, leftStrand, rightStrand, KLR.Seq.label_strandAt] using hs

/-- The crossing matrix entry of Proposition 2.14 is homogeneous, including the same-colour
relabelling, whose degree is zero. -/
theorem crossElt_mem_grade {ν : Multiset I} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < ν.card) :
    crossElt k Γ i n h ∈ G.grade ν.toFinsupp
      (G.pairDeg (i.lbl ⟨n, by omega⟩) (i.lbl ⟨n + 1, h⟩)) := by
  have hg := G.galList_mem_grade (spacedFull Γ i) (crossWord Γ i n h)
  rw [G.galDeg_crossWord hD hZ i n h] at hg
  unfold crossElt
  split_ifs
  · simpa only [zero_add] using SetLike.GradedMul.mul_mem (G.r_mem_grade _ _) hg
  · exact hg

private def familyGrade (ν : Multiset I) (d : ℤ) : Submodule k (SpacedAlgebra k Γ ν) where
  carrier := {a | ∀ i j, a.1 i j ∈ G.grade ν.toFinsupp d}
  zero_mem' _ _ := (G.grade ν.toFinsupp d).zero_mem
  add_mem' ha hb i j := (G.grade ν.toFinsupp d).add_mem (ha i j) (hb i j)
  smul_mem' c _a ha i j := (G.grade ν.toFinsupp d).smul_mem c (ha i j)

private theorem one_mem_familyGrade (ν : Multiset I) :
    (1 : SpacedAlgebra k Γ ν) ∈ G.familyGrade ν 0 := by
  intro i j
  change spacedIdem k Γ ν i j ∈ G.grade ν.toFinsupp 0
  by_cases hij : i = j
  · subst j
    simpa only [spacedIdem, Matrix.diagonal_apply_eq] using G.e_mem_grade (spacedFull Γ i)
  · simp only [spacedIdem, Matrix.diagonal_apply_ne _ hij]
    exact (G.grade ν.toFinsupp 0).zero_mem

private theorem mul_mem_familyGrade {ν : Multiset I} {d e : ℤ}
    {a b : SpacedAlgebra k Γ ν} (ha : a ∈ G.familyGrade ν d) (hb : b ∈ G.familyGrade ν e) :
    a * b ∈ G.familyGrade ν (d + e) := by
  intro i j
  change (∑ l, a.1 i l * b.1 l j) ∈ G.grade ν.toFinsupp (d + e)
  exact Submodule.sum_mem _ fun l _ => SetLike.GradedMul.mul_mem (ha i l) (hb l j)

private theorem genImg_idem_val {ν : Multiset I} (i : KLR.Seq ν) :
    (genImg k Γ (.idem i)).1 = Matrix.single i i (e (spacedFull Γ i)) := by
  rw [genImg_idem, cornerLin_val, e_mul_e_self, e_mul_e_self]

private theorem genImg_mul_idem_entry {ν : Multiset I} (g : KLR.Gen ν) (i j l : KLR.Seq ν) :
    (genImg k Γ g * genImg k Γ (.idem i)).1 j l =
      if l = i then e (spacedFull Γ j) * genMat k Γ g j i * e (spacedFull Γ i) else 0 := by
  change ((genImg k Γ g).1 * (genImg k Γ (.idem i)).1) j l = _
  rw [genImg_idem_val]
  by_cases hli : l = i
  · subst l
    rw [ite_eq_left rfl, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.single_apply_same, SpacedAlgebra.mul_e]
      exact spacedIdem_mul_mul_apply (genMat k Γ g) j i
    · intro t _ hti
      simp only [Matrix.single_apply, Ne.symm hti, false_and, ite_false, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  · rw [ite_eq_right hli, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    simp only [Matrix.single_apply, Ne.symm hli, and_false, ite_false, mul_zero]

private theorem genImg_idem_mem_familyGrade {ν : Multiset I} (i : KLR.Seq ν) :
    genImg k Γ (.idem i) ∈ G.familyGrade ν 0 := by
  intro j l
  rw [genImg_idem_val, Matrix.single_apply]
  split_ifs
  · exact G.e_mem_grade (spacedFull Γ i)
  · exact (G.grade ν.toFinsupp 0).zero_mem

private theorem genImg_dot_mul_idem_mem_familyGrade {ν : Multiset I}
    (a : Fin ν.card) (i : KLR.Seq ν) :
    genImg k Γ (.dot a) * genImg k Γ (.idem i) ∈ G.familyGrade ν (G.dot (i.lbl a)) := by
  intro j l
  rw [genImg_mul_idem_entry]
  split_ifs with hli
  · change e (spacedFull Γ j) * Matrix.diagonal (fun i : KLR.Seq ν => poly (X (i.strandAt a))) j i *
      e (spacedFull Γ i) ∈ _
    by_cases hji : j = i
    · subst j
      rw [Matrix.diagonal_apply_eq]
      have hpoly : poly (X (i.strandAt a)) ∈ G.grade ν.toFinsupp (G.dot (i.lbl a)) := by
        exact G.poly_mem_grade (isWeightedHomogeneous_X k G.wt (i.strandAt a))
      simpa only [zero_add, add_zero] using SetLike.GradedMul.mul_mem
        (SetLike.GradedMul.mul_mem (G.e_mem_grade (spacedFull Γ i)) hpoly)
        (G.e_mem_grade (spacedFull Γ i))
    · rw [Matrix.diagonal_apply_ne _ hji, mul_zero, zero_mul]
      exact (G.grade ν.toFinsupp _).zero_mem
  · exact (G.grade ν.toFinsupp _).zero_mem

private theorem genImg_cross_mul_idem_mem_familyGrade {ν : Multiset I}
    (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    (n : ℕ) (i : KLR.Seq ν) :
    genImg k Γ (.cross n) * genImg k Γ (.idem i) ∈
      G.familyGrade ν ((G.toKLRGrading hne hl).dψ n i) := by
  have hZ : Γ.NoZeroLoops := fun e he => (hne e he).elim
  intro j l
  rw [genImg_mul_idem_entry]
  split_ifs with hli
  · by_cases hn : n + 1 < ν.card
    · rw [KLR.GradingDatum.dψ_of_lt _ hn]
      simp only [genMat, hn, ↓reduceDIte, Matrix.of_apply, toKLRGrading_degΨ]
      split_ifs
      · simpa only [zero_add, add_zero] using SetLike.GradedMul.mul_mem
          (SetLike.GradedMul.mul_mem (G.e_mem_grade (spacedFull Γ j))
            (G.crossElt_mem_grade hD hZ i n hn)) (G.e_mem_grade (spacedFull Γ i))
      · rw [mul_zero, zero_mul]
        exact (G.grade ν.toFinsupp _).zero_mem
    · simp only [genMat, hn, dite_false, Matrix.zero_apply, mul_zero, zero_mul]
      exact (G.grade ν.toFinsupp _).zero_mem
  · exact (G.grade ν.toFinsupp _).zero_mem

private theorem spacedHom_gen {ν : Multiset I} (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none) (g : KLR.Gen ν) :
    spacedHom k hS hD hne hl (KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k g)) =
      genImg k Γ g := by
  rw [spacedHom_mk, spacedFreeHom, FreeAlgebra.lift_ι_apply]

/-- Proposition 2.14 preserves the grading entry by entry on the loading family.
Copies indexed by different sequences are retained even when their chambers coincide. -/
theorem spacedHom_entry_mem_grade {ν : Multiset I}
    (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none) {a : KLR.KLRAlgebra k Γ.klrQ ν} {d : ℤ}
    (ha : a ∈ (G.toKLRGrading hne hl).grade ν d) (i j : KLR.Seq ν) :
    (spacedHom k hS hD hne hl a).1 i j ∈ G.grade ν.toFinsupp d := by
  let H := G.toKLRGrading hne hl
  let φ := spacedHom k (ν := ν) hS hD hne hl
  let S := Graded.componentPreimage (H.grade ν) (G.familyGrade ν) φ
  have hh {x : KLR.KLRAlgebra k Γ.klrQ ν} {e : ℤ}
      (hx : x ∈ H.grade ν e) (hy : φ x ∈ G.familyGrade ν e) : x ∈ S :=
    Graded.mem_componentPreimage_of_homogeneous (H.grade ν) (G.familyGrade ν) φ hx hy
  have hone : (1 : KLR.KLRAlgebra k Γ.klrQ ν) ∈ S :=
    hh (SetLike.one_mem_graded _) (by simpa only [map_one] using G.one_mem_familyGrade ν)
  have hgood : ∀ x : KLR.KLRAlgebra k Γ.klrQ ν, x ∈ S := by
    intro x
    obtain ⟨u, rfl⟩ := KLR.KLRAlgebra.mk_surjective x
    induction u using FreeAlgebra.induction with
    | grade0 c =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact S.smul_mem c hone
    | grade1 g =>
      cases g with
      | idem l =>
        apply hh (H.e_mem_grade l)
        exact (spacedHom_gen hS hD hne hl (.idem l)) ▸ G.genImg_idem_mem_familyGrade l
      | dot b =>
        have hsum : (KLR.KLRAlgebra.x b : KLR.KLRAlgebra k Γ.klrQ ν) =
            ∑ l, KLR.KLRAlgebra.x b * KLR.KLRAlgebra.e l := by
          rw [← Finset.mul_sum, KLR.KLRAlgebra.sum_e, mul_one]
        change KLR.KLRAlgebra.x b ∈ S
        rw [hsum]
        apply S.sum_mem
        intro l _
        apply hh (H.x_mul_e_mem_grade b l)
        rw [map_mul]
        change spacedHom k hS hD hne hl (KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k (.dot b))) *
          spacedHom k hS hD hne hl (KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k (.idem l))) ∈ _
        rw [spacedHom_gen, spacedHom_gen]
        exact G.genImg_dot_mul_idem_mem_familyGrade b l
      | cross n =>
        have hsum : (KLR.KLRAlgebra.ψ n : KLR.KLRAlgebra k Γ.klrQ ν) =
            ∑ l, KLR.KLRAlgebra.ψ n * KLR.KLRAlgebra.e l := by
          rw [← Finset.mul_sum, KLR.KLRAlgebra.sum_e, mul_one]
        change KLR.KLRAlgebra.ψ n ∈ S
        rw [hsum]
        apply S.sum_mem
        intro l _
        apply hh (H.ψ_mul_e_mem_grade' n l)
        rw [map_mul]
        change spacedHom k hS hD hne hl (KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k (.cross n))) *
          spacedHom k hS hD hne hl (KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k (.idem l))) ∈ _
        rw [spacedHom_gen, spacedHom_gen]
        exact G.genImg_cross_mul_idem_mem_familyGrade hD hne hl n l
    | mul u v hu hv =>
      rw [map_mul]
      exact Graded.componentPreimage_mul (H.grade ν) (G.familyGrade ν) φ
        (fun _ _ _ hx _ hy => G.mul_mem_familyGrade hx hy) hu hv
    | add u v hu hv =>
      rw [map_add]
      exact S.add_mem hu hv
  have h := hgood a d
  rw [DirectSum.decompose_of_mem_same _ ha] at h
  exact h i j

end GradingDatum

end Categorification.WeightedKLR
