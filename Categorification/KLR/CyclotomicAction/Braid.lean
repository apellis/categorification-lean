/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTriple
import Categorification.KLR.CyclotomicAction.Induction

/-!
# The braid relation for cyclotomic induction functors

For three cyclotomic induction functors (Kang–Kashiwara, arXiv:1102.4677v4, §4.2) adding
strands labelled `c`, `j`, `i` with `i ≠ c`, the two composites of whiskered crossings
`F_c F_j F_i ⟶ F_i F_j F_c` agree: this is the KLR braid relation of Khovanov–Lauda I
(arXiv:0803.4121v2, §2.1) with distinct outer labels, in the form of
`TwoRep.RouqUpKLR.braid` (Brundan, arXiv:1501.00350v1, Def. 1.1, (1.4)) with the 1-morphisms
read as functors, composition `≫` of 1-morphisms as `⋙`, and the associators of functor
composition.

Both sides are represented (`InductionAlong.Rep3`) by products of crossings in `R^Λ(δ)`.
Moving the units of the intermediate inductions across these crossings
(`KLRAlgebra.IsLeftBlock.intertwines_cross`) reduces the relation to the braid relation
(`KLRAlgebra.braid`) on the block with labels `i, j, c`, whose outer labels differ.
-/

namespace Categorification.KLR

open CategoryTheory

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### Three added strands -/

/-- The labels `a, b, c` of three added strands. -/
def tripleWord (a b c : I) : ℕ → I := fun n => if n = 0 then a else if n = 1 then b else c

section Triple

variable (Q) in
/-- The inclusion `R(γ) → R(δ)` adding strands labelled `a`, `b`, `c`. -/
noncomputable abbrev tripleIncl (a b c : I) {γ β β' δ : Multiset I} (h₁ : {a} + γ = β)
    (h₂ : {b} + β = β') (h₃ : {c} + β' = δ) : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ :=
  ((lastIncl Q c h₃).comp (lastIncl Q b h₂)).comp (lastIncl Q a h₁)

variable (a b c : I) {γ β β' δ : Multiset I} (h₁ : {a} + γ = β) (h₂ : {b} + β = β')
  (h₃ : {c} + β' = δ)

omit [DecidableEq I] in
theorem card_triple {a b c : I} {γ β β' δ : Multiset I} (h₁ : {a} + γ = β)
    (h₂ : {b} + β = β') (h₃ : {c} + β' = δ) : Multiset.card δ = Multiset.card γ + 3 := by
  rw [card_lastIncl c h₃, card_lastIncl b h₂, card_lastIncl a h₁]

theorem isLeftBlock_triple : IsLeftBlock (tripleIncl Q a b c h₁ h₂ h₃) (tripleWord a b c) := by
  have e1 : Multiset.card β - Multiset.card γ = 1 := by
    rw [card_lastIncl a h₁]; omega
  have e2 : Multiset.card β' - Multiset.card γ = 2 := by
    rw [card_lastIncl b h₂, card_lastIncl a h₁]; omega
  refine (((isLeftBlock_lastIncl a h₁).comp (isLeftBlock_lastIncl b h₂)).comp
    (isLeftBlock_lastIncl c h₃)).congr_word fun n hn => ?_
  have hδ := card_triple h₁ h₂ h₃
  rcases n with _ | _ | _ | n
  · simp [tripleWord, e1, e2]
  · simp [tripleWord, e1, e2]
  · simp [tripleWord, e2]
  · omega

/-- The unit of the added block absorbs the unit of its last inclusion. -/
theorem triple_one_mul_last :
    tripleIncl Q a b c h₁ h₂ h₃ 1 * lastIncl Q c h₃ 1 = tripleIncl Q a b c h₁ h₂ h₃ 1 := by
  rw [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.comp_apply, ← map_mul, mul_one]

/-- A crossing of the first two strands of a last inclusion. -/
theorem lastIncl_ψ (i : I) {β δ : Multiset I} (h : {i} + β = δ) {l : ℕ}
    (hl : l + 1 < Multiset.card β) : lastIncl Q i h (ψ l) = ψ l * lastIncl Q i h 1 :=
  (isLeftBlock_lastIncl i h).ψ_eq l hl

end Triple

/-- The braid relation on a left block whose first and third added labels differ, with the
idempotents on the right. -/
theorem IsLeftBlock.braid_mul_one {γ δ : Multiset I}
    {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w : ℕ → I} (hf : IsLeftBlock f w)
    (hδ : Multiset.card γ + 2 < Multiset.card δ) (hw : w 0 ≠ w 2) :
    ψ (Multiset.card γ) * ψ (Multiset.card γ + 1) * ψ (Multiset.card γ) * f 1 =
      ψ (Multiset.card γ + 1) * ψ (Multiset.card γ) * ψ (Multiset.card γ + 1) * f 1 := by
  rw [← sub_eq_zero, ← sub_mul, IsLeftBlock.map_one_eq, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  obtain ⟨t, ht, hl⟩ := hf.e_eq s
  rw [ht, braid _ hδ t, ite_eq_right]
  rintro ⟨h, -⟩
  apply hw
  have h0 := hl ⟨Multiset.card γ, by omega⟩
  have h2 := hl ⟨Multiset.card γ + 2, hδ⟩
  simp only [lt_self_iff_false, dite_false, Nat.sub_self] at h0
  simp only [show ¬ Multiset.card γ + 2 < Multiset.card γ by omega, dite_false,
    Nat.add_sub_cancel_left] at h2
  rw [← h0, ← h2]
  exact h

end KLRAlgebra

namespace CyclotomicAction

open KLRAlgebra InductionAlong

variable {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

variable (Q a) in
/-- The crossing is represented by the crossing element. -/
theorem rep_cross (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ)
    (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    Rep2 (cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄) (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄) := by
  simp only [Rep2, cross, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The KLR identity behind the braid relation, with `p = card l`. -/
theorem braid_identity (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : {c} + l = w₁) (e2 : {j} + w₁ = w₂)
    (e3 : {i} + w₂ = m) (e4 : {i} + w₁ = w₃) (e5 : {j} + w₃ = m)
    (e6 : {i} + l = w₄) (e7 : {c} + w₄ = w₃) (e8 : {j} + w₄ = w₅)
    (e9 : {c} + w₅ = m) (e10 : {j} + l = w₆) (e11 : {c} + w₆ = w₂)
    (e12 : {i} + w₆ = w₅) :
    tripleIncl Q c j i e1 e2 e3 1 *
        (ψ (Multiset.card l + 1) * (lastIncl Q j e5 (ψ (Multiset.card l)) *
          ψ (Multiset.card l + 1))) =
      tripleIncl Q c j i e1 e2 e3 1 *
        (lastIncl Q i e3 (ψ (Multiset.card l)) * (ψ (Multiset.card l + 1) *
          lastIncl Q c e9 (ψ (Multiset.card l)))) := by
  set p := Multiset.card l
  have hm : Multiset.card m = p + 3 := card_triple e1 e2 e3
  have hw₁ : Multiset.card w₁ = p + 1 := card_lastIncl c e1
  have hw₄ : Multiset.card w₄ = p + 1 := card_lastIncl i e6
  have hw₆ : Multiset.card w₆ = p + 1 := card_lastIncl j e10
  -- the blocks
  have B := isLeftBlock_triple (Q := Q) c j i e1 e2 e3
  have B₁ := isLeftBlock_triple (Q := Q) c i j e1 e4 e5
  have B₂ := isLeftBlock_triple (Q := Q) i c j e6 e7 e5
  have B₃ := isLeftBlock_triple (Q := Q) i j c e6 e8 e9
  have V₁ := isLeftBlock_triple (Q := Q) j c i e10 e11 e3
  have V₂ := isLeftBlock_triple (Q := Q) j i c e10 e12 e9
  have sw : ∀ (x y z : I) (q : ℕ) (w' : ℕ → I),
      (∀ n, n < 3 → w' n = IsLeftBlock.swapAt (tripleWord x y z) q n) →
      ∀ {f : KLRAlgebra k Q l →ₙₐ[k] KLRAlgebra k Q m}, IsLeftBlock f w' →
        IsLeftBlock f (IsLeftBlock.swapAt (tripleWord x y z) q) := fun x y z q w' hw f hf =>
    hf.congr_word fun n hn => hw n (by omega)
  have cr : ∀ {x y z x' y' z' : I} (q : ℕ) {f g : KLRAlgebra k Q l →ₙₐ[k] KLRAlgebra k Q m},
      IsLeftBlock f (tripleWord x y z) → IsLeftBlock g (tripleWord x' y' z') →
      (∀ n, n < 3 → tripleWord x' y' z' n = IsLeftBlock.swapAt (tripleWord x y z) q n) → q < 2 →
        f 1 * ψ (p + q) = ψ (p + q) * g 1 := fun q f g hf hg hw hq =>
    hf.intertwines_cross (sw _ _ _ q _ hw hg) (by omega) 1
  -- left side
  have l1 : tripleIncl Q c j i e1 e2 e3 1 * ψ (p + 1) =
      ψ (p + 1) * tripleIncl Q c i j e1 e4 e5 1 :=
    cr 1 B B₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  have l2 : tripleIncl Q c i j e1 e4 e5 1 * ψ (p + 0) =
      ψ (p + 0) * tripleIncl Q i c j e6 e7 e5 1 :=
    cr 0 B₁ B₂ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  have l3 : tripleIncl Q i c j e6 e7 e5 1 * ψ (p + 1) =
      ψ (p + 1) * tripleIncl Q i j c e6 e8 e9 1 :=
    cr 1 B₂ B₃ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  -- right side
  have r1 : tripleIncl Q c j i e1 e2 e3 1 * ψ (p + 0) =
      ψ (p + 0) * tripleIncl Q j c i e10 e11 e3 1 :=
    cr 0 B V₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  have r2 : tripleIncl Q j c i e10 e11 e3 1 * ψ (p + 1) =
      ψ (p + 1) * tripleIncl Q j i c e10 e12 e9 1 :=
    cr 1 V₁ V₂ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  have r3 : tripleIncl Q j i c e10 e12 e9 1 * ψ (p + 0) =
      ψ (p + 0) * tripleIncl Q i j c e6 e8 e9 1 :=
    cr 0 V₂ B₃ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt]) (by omega)
  simp only [add_zero] at l2 r1 r3
  have hw₂ : Multiset.card w₂ = p + 2 := by rw [card_lastIncl j e2]; omega
  have hw₃ : Multiset.card w₃ = p + 2 := by rw [card_lastIncl i e4]; omega
  have hw₅ : Multiset.card w₅ = p + 2 := by rw [card_lastIncl j e8]; omega
  rw [lastIncl_ψ j e5 (by omega), lastIncl_ψ i e3 (by omega), lastIncl_ψ c e9 (by omega)]
  have ra : ∀ {a b c d : KLRAlgebra k Q m}, a * b = c * d → ∀ x, a * (b * x) = c * (d * x) :=
    fun h x => by rw [← mul_assoc, h, mul_assoc]
  have ab : ∀ (x y z : I) {β β' : Multiset I} (h₁ : {x} + l = β) (h₂ : {y} + β = β')
      (h₃ : {z} + β' = m) (t : KLRAlgebra k Q m),
      tripleIncl Q x y z h₁ h₂ h₃ 1 * (lastIncl Q z h₃ 1 * t) = tripleIncl Q x y z h₁ h₂ h₃ 1 * t :=
    fun x y z _ _ h₁ h₂ h₃ t => by rw [← mul_assoc, triple_one_mul_last]
  have hb' := B₃.braid_mul_one (by omega) (by simpa [tripleWord] using hb)
  simp only [mul_assoc] at hb' ⊢
  rw [ra l1, ra l2, ab, l3, ra r1, ab, ra r2, ra r3, triple_one_mul_last]
  exact hb'.symm

variable (Q a) in
/-- **The braid relation with distinct outer labels** (KL I §2.1; Brundan, arXiv:1501.00350v1,
(1.4) for `i ≠ c`, as in `TwoRep.RouqUpKLR.braid`) for cyclotomic induction functors: the two
composites of whiskered crossings `F_c F_j F_i ⟶ F_i F_j F_c` agree when `i ≠ c`. -/
theorem braid (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ m : Multiset I} (e1 : {c} + l = w₁) (e2 : {j} + w₁ = w₂)
    (e3 : {i} + w₂ = m) (e4 : {i} + w₁ = w₃) (e5 : {j} + w₃ = m)
    (e6 : {i} + l = w₄) (e7 : {c} + w₄ = w₃) (e8 : {j} + w₄ = w₅)
    (e9 : {c} + w₅ = m) (e10 : {j} + l = w₆) (e11 : {c} + w₆ = w₂)
    (e12 : {i} + w₆ = w₅) :
    Functor.whiskerLeft (ind.{u, v, w} Q a c e1) (cross Q a i j e2 e3 e4 e5) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (cross Q a i c e1 e4 e6 e7) (ind Q a j e5) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i e6) (cross Q a j c e7 e5 e8 e9) =
      ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (cross Q a j c e1 e2 e10 e11) (ind Q a i e3) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a j e10) (cross Q a i c e11 e3 e12 e9) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (cross Q a i j e10 e12 e6 e8) (ind Q a c e9) ≫
          (Functor.associator _ _ _).hom) := by
  have L := (Rep3.whiskerLeft (lastEmb Q a c e1) (rep_cross.{u, v, w} Q a i j e2 e3 e4 e5)).comp
    ((Rep3.whiskerRight (lastEmb Q a j e5) (rep_cross.{u, v, w} Q a i c e1 e4 e6 e7)).comp
      (Rep3.whiskerLeft (lastEmb Q a i e6) (rep_cross.{u, v, w} Q a j c e7 e5 e8 e9)))
  have R := (Rep3.whiskerRight (lastEmb Q a i e3) (rep_cross.{u, v, w} Q a j c e1 e2 e10 e11)).comp
    ((Rep3.whiskerLeft (lastEmb Q a j e10) (rep_cross.{u, v, w} Q a i c e11 e3 e12 e9)).comp
      (Rep3.whiskerRight (lastEmb Q a c e9) (rep_cross.{u, v, w} Q a i j e10 e12 e6 e8)))
  refine L.eq R ?_
  have h1 : (1 : CycKLR k Q a l) = CycKLR.mk k Q a l 1 := (map_one _).symm
  rw [h1]
  simp only [crossElt, lastEmb_mk, ← map_mul]
  congr 1
  rw [card_lastIncl c e1, card_lastIncl i e6, card_lastIncl j e10]
  exact braid_identity i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12

end CyclotomicAction

end Categorification.KLR
