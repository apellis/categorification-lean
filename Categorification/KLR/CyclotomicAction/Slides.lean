/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Square

/-!
# Dot slides and the nil-Hecke relations for cyclotomic induction

For cyclotomic induction functors (Kang–Kashiwara, arXiv:1102.4677v4, §4.2):

* `slide_left`, `slide_right`: for `i ≠ j`, dots slide through the crossing
  `F_j F_i ⟶ F_i F_j` (KL I, arXiv:0803.4121v2, §2.1; Brundan, arXiv:1501.00350v1, (1.2) for
  distinct labels), in the form of `TwoRep.RouqUpKLR.slide_left` and `slide_right`.
* `sameCross_slide_left`, `sameCross_slide_right`: the nil-Hecke dot slides for two strands of
  the same colour (Brundan (1.2) for equal labels), in the form of `TwoRep.RouqLoc.slide_left` and
  `slide_right`.
* `sameCross_sq`, `sameCross_braid`: the nil-Hecke quadratic and braid relations (Brundan (1.3),
  (1.4) for equal labels), in the form of `TwoRep.RouqFamily.square` and `braid`.

The same-colour crossing is `sameCross = -ψ`, as in Kang–Kashiwara §3 and `Square.lean`. The two
nil-Hecke slides fix this sign: with `+ψ` their right-hand sides would be `-𝟙`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory KLRAlgebra InductionAlong MvPolynomial

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

/-- Moving the unit of a two-strand block across the crossing and absorbing a dot on the first
added strand. -/
theorem double_mul_cross_last_dot (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    doubleIncl Q i j h₁ h₂ 1 * (ψ (Multiset.card γ) *
        lastIncl Q j h₄ (x ⟨Multiset.card γ, by rw [card_lastIncl i h₃]; omega⟩)) =
      doubleIncl Q i j h₁ h₂ 1 * (ψ (Multiset.card γ) *
        x ⟨Multiset.card γ, by rw [card_double h₁ h₂]; omega⟩) := by
  have hc := double_cross Q i j h₁ h₂ h₃ h₄ 1
  have hd := (isLeftBlock_lastIncl i h₃).one_mul_dot_last (Q := Q) j h₄
    ⟨Multiset.card γ, by rw [card_lastIncl i h₃]; omega⟩ le_rfl
  rw [← mul_assoc, hc, mul_assoc]
  change ψ _ * ((lastIncl Q j h₄).comp (lastIncl Q i h₃) 1 * _) = _
  rw [hd, ← mul_assoc]
  change ψ _ * doubleIncl Q j i h₃ h₄ 1 * _ = _
  rw [← hc, mul_assoc]

/-- The unit of a two-strand block absorbs a dot on the first added strand. -/
theorem double_mul_last_dot (i j : I) {γ β δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (t : KLRAlgebra k Q δ) :
    doubleIncl Q i j h₁ h₂ 1 *
        (lastIncl Q i h₂ (x ⟨Multiset.card γ, by rw [card_lastIncl j h₁]; omega⟩) * t) =
      doubleIncl Q i j h₁ h₂ 1 *
        (x ⟨Multiset.card γ, by rw [card_double h₁ h₂]; omega⟩ * t) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  exact (isLeftBlock_lastIncl j h₁).one_mul_dot_last (Q := Q) i h₂
    ⟨Multiset.card γ, by rw [card_lastIncl j h₁]; omega⟩ le_rfl

/-- The unit of a two-strand block is idempotent. -/
theorem double_one_mul_one (i j : I) {γ β δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) :
    doubleIncl Q i j h₁ h₂ 1 * doubleIncl Q i j h₁ h₂ 1 =
      doubleIncl Q i j h₁ h₂ 1 * 1 := by
  rw [← map_mul, mul_one, mul_one]


theorem one_eq_mk {γ : Multiset I} : (1 : CycKLR k Q a γ) = CycKLR.mk k Q a γ 1 :=
  (map_one _).symm

theorem rep_id.{u', w'} {A B D : Type u'} [Ring A] [Ring B] [Ring D] (φ : A →ₙ+* B)
    (φ' : B →ₙ+* D) :
    Rep2 (𝟙 (functor.{u', w'} φ ⋙ functor.{u', w'} φ'))
      (Intertwines.unit (φ'.comp φ)) := by
  rw [Rep2, natTrans_unit, Category.id_comp, Category.comp_id]

variable (Q a) in
/-- **Left dot slide for distinct colours** (KL I §2.1; Brundan, arXiv:1501.00350v1, (1.2), as in
`TwoRep.RouqUpKLR.slide_left`), for cyclotomic induction functors. -/
theorem slide_left (i j : I) (hij : i ≠ j) {γ β β' δ : Multiset I}
    (h₁ : {j} + γ = β) (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    Functor.whiskerLeft (ind.{u, v, w} Q a j h₁) (dot Q a i h₂) ≫ cross Q a i j h₁ h₂ h₃ h₄ =
      cross Q a i j h₁ h₂ h₃ h₄ ≫ Functor.whiskerRight (dot Q a i h₃) (ind Q a j h₄) := by
  refine ((Rep2.whiskerLeft (lastEmb Q a j h₁) (intertwines_dotElt Q a i h₂)).comp
    (rep_cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄)).eq
    ((rep_cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄).comp
      (Rep2.whiskerRight (lastEmb Q a j h₄) (intertwines_dotElt Q a i h₃))) ?_
  have hβ : Multiset.card β = Multiset.card γ + 1 := card_lastIncl j h₁
  have hδ := card_double h₁ h₂
  rw [one_eq_mk]
  simp only [dotElt, crossElt, lastEmb_mk, ← map_mul]
  congr 1
  change doubleIncl Q i j h₁ h₂ 1 * _ = doubleIncl Q i j h₁ h₂ 1 * _
  rw [double_mul_cross_last_dot (Q := Q) i j h₁ h₂ h₃ h₄]
  refine (isLeftBlock_double Q i j h₁ h₂).one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  have key := e_mul_dot_cross_right (Q := Q) (Multiset.card γ) (by omega) t
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false, hij.symm] at key
  rw [mul_sub, sub_eq_zero] at key
  simp only [hβ]
  exact key.symm

variable (Q a) in
/-- **Right dot slide for distinct colours** (KL I §2.1; Brundan, arXiv:1501.00350v1, (1.2), as
in `TwoRep.RouqUpKLR.slide_right`), for cyclotomic induction functors. -/
theorem slide_right (i j : I) (hij : i ≠ j) {γ β β' δ : Multiset I}
    (h₁ : {j} + γ = β) (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    Functor.whiskerRight (dot.{u, v, w} Q a j h₁) (ind Q a i h₂) ≫ cross Q a i j h₁ h₂ h₃ h₄ =
      cross Q a i j h₁ h₂ h₃ h₄ ≫ Functor.whiskerLeft (ind Q a i h₃) (dot Q a j h₄) := by
  refine ((Rep2.whiskerRight (lastEmb Q a i h₂) (intertwines_dotElt Q a j h₁)).comp
    (rep_cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄)).eq
    ((rep_cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄).comp
      (Rep2.whiskerLeft (lastEmb Q a i h₃) (intertwines_dotElt Q a j h₄))) ?_
  have hβ' : Multiset.card β' = Multiset.card γ + 1 := card_lastIncl i h₃
  have hδ := card_double h₁ h₂
  rw [one_eq_mk]
  simp only [dotElt, crossElt, lastEmb_mk, ← map_mul]
  congr 1
  change doubleIncl Q i j h₁ h₂ 1 * _ = doubleIncl Q i j h₁ h₂ 1 * _
  rw [double_mul_last_dot (Q := Q) i j h₁ h₂]
  refine (isLeftBlock_double Q i j h₁ h₂).one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  have key := e_mul_dot_cross_left (Q := Q) (Multiset.card γ) (by omega) t
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false, hij.symm] at key
  rw [mul_sub, sub_eq_zero] at key
  simp only [hβ']
  exact key

variable (Q a) in
/-- **Nil-Hecke left dot slide** (Brundan, arXiv:1501.00350v1, (1.2) for equal labels, as in
`TwoRep.RouqLoc.slide_left`), for cyclotomic induction functors with the same-colour crossing
`sameCross = -ψ`. -/
theorem sameCross_slide_left (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = δ) :
    Functor.whiskerLeft (ind.{u, v, w} Q a i h₁) (dot Q a i h₂) ≫ sameCross Q a i h₁ h₂ -
        sameCross Q a i h₁ h₂ ≫ Functor.whiskerRight (dot Q a i h₁) (ind Q a i h₂) = 𝟙 _ := by
  refine (((Rep2.whiskerLeft (lastEmb Q a i h₁) (intertwines_dotElt Q a i h₂)).comp
    (rep_sameCross.{u, v, w} Q a i h₁ h₂)).sub
    ((rep_sameCross.{u, v, w} Q a i h₁ h₂).comp
      (Rep2.whiskerRight (lastEmb Q a i h₂) (intertwines_dotElt Q a i h₁)))).eq
    (rep_id _ _) ?_
  have hβ : Multiset.card β = Multiset.card γ + 1 := card_lastIncl i h₁
  have hδ := card_double h₁ h₂
  rw [one_eq_mk]
  simp only [dotElt, crossElt, lastEmb_mk, NonUnitalRingHom.comp_apply, ← map_neg,
    ← map_mul, ← map_sub]
  congr 1
  simp only [mul_one, neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub]
  change doubleIncl Q i i h₁ h₂ 1 * _ = doubleIncl Q i i h₁ h₂ 1
  rw [mul_sub, double_mul_cross_last_dot (Q := Q) i i h₁ h₂ h₁ h₂, ← mul_sub]
  refine Eq.trans ?_ (mul_one _)
  refine (isLeftBlock_double Q i i h₁ h₂).one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  have key := e_mul_dot_cross_right (Q := Q) (Multiset.card γ) (by omega) t
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false] at key
  simp only [hβ]
  rw [mul_one]
  exact key

variable (Q a) in
/-- **Nil-Hecke right dot slide** (Brundan, arXiv:1501.00350v1, (1.2) for equal labels, as in
`TwoRep.RouqLoc.slide_right`), for cyclotomic induction functors with the same-colour crossing
`sameCross = -ψ`. -/
theorem sameCross_slide_right (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = δ) :
    sameCross.{u, v, w} Q a i h₁ h₂ ≫ Functor.whiskerLeft (ind Q a i h₁) (dot Q a i h₂) -
        Functor.whiskerRight (dot Q a i h₁) (ind Q a i h₂) ≫ sameCross Q a i h₁ h₂ = 𝟙 _ := by
  refine (((rep_sameCross.{u, v, w} Q a i h₁ h₂).comp
    (Rep2.whiskerLeft (lastEmb Q a i h₁) (intertwines_dotElt Q a i h₂))).sub
    ((Rep2.whiskerRight (lastEmb Q a i h₂) (intertwines_dotElt Q a i h₁)).comp
      (rep_sameCross.{u, v, w} Q a i h₁ h₂))).eq
    (rep_id _ _) ?_
  have hβ : Multiset.card β = Multiset.card γ + 1 := card_lastIncl i h₁
  have hδ := card_double h₁ h₂
  rw [one_eq_mk]
  simp only [dotElt, crossElt, lastEmb_mk, NonUnitalRingHom.comp_apply, ← map_neg,
    ← map_mul, ← map_sub]
  congr 1
  simp only [mul_one, neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub]
  change doubleIncl Q i i h₁ h₂ 1 * _ = doubleIncl Q i i h₁ h₂ 1
  rw [mul_sub, double_mul_last_dot (Q := Q) i i h₁ h₂, ← mul_sub]
  refine Eq.trans ?_ (mul_one _)
  refine (isLeftBlock_double Q i i h₁ h₂).one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  have key := e_mul_dot_cross_left (Q := Q) (Multiset.card γ) (by omega) t
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false] at key
  simp only [hβ]
  rw [mul_one]
  exact key

variable (Q a) in
/-- **Nil-Hecke quadratic relation** (Brundan, arXiv:1501.00350v1, (1.3) for equal labels, as in
`TwoRep.RouqFamily.square`), for cyclotomic induction functors. -/
theorem sameCross_sq (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    sameCross.{u, v, w} Q a i h₁ h₂ ≫ sameCross Q a i h₁ h₂ = 0 := by
  have h := ((rep_sameCross.{u, v, w} Q a i h₁ h₂).comp
    (rep_sameCross.{u, v, w} Q a i h₁ h₂)).eq_endHom (k := k)
  rw [h, ← (endHom (k := k) (compIso.{max u v, w} (lastEmb Q a i h₁) (lastEmb Q a i h₂))).map_zero]
  refine endHom_eq_of_unit_mul _ ?_
  have hδ := card_double h₁ h₂
  change _ * (-crossElt Q a (γ := γ) (δ := δ) * -crossElt Q a (γ := γ) (δ := δ)) = _ * 0
  rw [neg_mul_neg, one_eq_mk, NonUnitalRingHom.comp_apply, lastEmb_mk, lastEmb_mk, crossElt,
    ← map_mul, ← map_mul, mul_zero, ← map_zero (CycKLR.mk k Q a δ), ← mul_zero (_ : KLRAlgebra k Q δ)]
  congr 1
  refine (isLeftBlock_double Q i i h₁ h₂).one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  rw [e_mul_ψ_sq _ (by omega)]
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false, mul_zero]

/-- The KLR identity behind the nil-Hecke braid relation, with `p = card γ`. -/
theorem sameBraid_identity (i : I) {γ β β₁ δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = β₁) (h₃ : {i} + β₁ = δ) :
    tripleIncl Q i i i h₁ h₂ h₃ 1 *
        (-ψ (Multiset.card γ + 1) * (lastIncl Q i h₃ (-ψ (Multiset.card γ)) *
          -ψ (Multiset.card γ + 1))) =
      tripleIncl Q i i i h₁ h₂ h₃ 1 *
        (lastIncl Q i h₃ (-ψ (Multiset.card γ)) * (-ψ (Multiset.card γ + 1) *
          lastIncl Q i h₃ (-ψ (Multiset.card γ)))) := by
  set p := Multiset.card γ
  have hm : Multiset.card δ = p + 3 := card_triple h₁ h₂ h₃
  have hβ₁ : Multiset.card β₁ = p + 2 := by rw [card_lastIncl i h₂, card_lastIncl i h₁]
  have U := isLeftBlock_triple (Q := Q) i i i h₁ h₂ h₃
  have c0 : tripleIncl Q i i i h₁ h₂ h₃ 1 * ψ (p + 0) =
      ψ (p + 0) * tripleIncl Q i i i h₁ h₂ h₃ 1 :=
    triple_cross 0 U U (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have c1 : tripleIncl Q i i i h₁ h₂ h₃ 1 * ψ (p + 1) =
      ψ (p + 1) * tripleIncl Q i i i h₁ h₂ h₃ 1 :=
    triple_cross 1 U U (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  simp only [add_zero] at c0
  rw [map_neg, lastIncl_ψ i h₃ (by omega)]
  have ra : ∀ {a b c d : KLRAlgebra k Q δ}, a * b = c * d → ∀ x, a * (b * x) = c * (d * x) :=
    fun h x => by rw [← mul_assoc, h, mul_assoc]
  have ab : ∀ t : KLRAlgebra k Q δ,
      tripleIncl Q i i i h₁ h₂ h₃ 1 * (lastIncl Q i h₃ 1 * t) =
        tripleIncl Q i i i h₁ h₂ h₃ 1 * t :=
    fun t => by rw [← mul_assoc, triple_one_mul_last]
  have hL : tripleIncl Q i i i h₁ h₂ h₃ 1 * (ψ (p + 1) * (ψ p * (lastIncl Q i h₃ 1 *
      ψ (p + 1)))) = tripleIncl Q i i i h₁ h₂ h₃ 1 * (ψ (p + 1) * (ψ p * ψ (p + 1))) := by
    rw [ra c1, ra c0, ab, ← ra c0, ← ra c1]
  have hR : tripleIncl Q i i i h₁ h₂ h₃ 1 * (ψ p * (lastIncl Q i h₃ 1 * (ψ (p + 1) *
      (ψ p * lastIncl Q i h₃ 1)))) = tripleIncl Q i i i h₁ h₂ h₃ 1 * (ψ p * (ψ (p + 1) * ψ p)) := by
    rw [ra c0, ab, ra c1, ra c0, triple_one_mul_last, ← c0, ← ra c1, ← ra c0]
  simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  rw [hL, hR]
  congr 1
  refine U.one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  have l2 := hl.apply_add 2 (by omega)
  simp only [add_zero] at l0
  simp only [tripleWord, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_true,
    ite_false] at l0 l1 l2
  have key := e_mul_braid (Q := Q) p (by omega) t
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => hc.2 (by
    simp only [Seq.lbl]; rw [l0, l1]))] at key
  rw [mul_sub, sub_eq_zero] at key
  simp only [mul_assoc] at key
  exact key.symm

variable (Q a) in
/-- **Nil-Hecke braid relation** (Brundan, arXiv:1501.00350v1, (1.4) for equal labels, as in
`TwoRep.RouqFamily.braid`), for cyclotomic induction functors with the same-colour crossing
`sameCross = -ψ`. -/
theorem sameCross_braid (i : I) {γ β β₁ δ : Multiset I} (h₁ : {i} + γ = β)
    (h₂ : {i} + β = β₁) (h₃ : {i} + β₁ = δ) :
    Functor.whiskerLeft (ind.{u, v, w} Q a i h₁) (sameCross Q a i h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sameCross Q a i h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i h₁) (sameCross Q a i h₂ h₃) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sameCross Q a i h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i h₁) (sameCross Q a i h₂ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sameCross Q a i h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) := by
  have L := (Rep3.whiskerLeft (lastEmb Q a i h₁) (rep_sameCross.{u, v, w} Q a i h₂ h₃)).comp
    ((Rep3.whiskerRight (lastEmb Q a i h₃) (rep_sameCross.{u, v, w} Q a i h₁ h₂)).comp
      (Rep3.whiskerLeft (lastEmb Q a i h₁) (rep_sameCross.{u, v, w} Q a i h₂ h₃)))
  have R := (Rep3.whiskerRight (lastEmb Q a i h₃) (rep_sameCross.{u, v, w} Q a i h₁ h₂)).comp
    ((Rep3.whiskerLeft (lastEmb Q a i h₁) (rep_sameCross.{u, v, w} Q a i h₂ h₃)).comp
      (Rep3.whiskerRight (lastEmb Q a i h₃) (rep_sameCross.{u, v, w} Q a i h₁ h₂)))
  refine L.eq R ?_
  rw [one_eq_mk]
  simp only [crossElt, lastEmb_mk, ← map_neg, ← map_mul]
  congr 1
  rw [card_lastIncl i h₁]
  exact sameBraid_identity i h₁ h₂ h₃

end Categorification.KLR.CyclotomicAction
