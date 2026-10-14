/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongEnd
import Categorification.KLR.CyclotomicAction.Braid
import Categorification.KLR.Symmetries

/-!
# The quadratic relation and the `i, j, i` braid relation for cyclotomic induction

For cyclotomic induction functors (Kang–Kashiwara, arXiv:1102.4677v4, §4.2), with
`k`-linear structure on module categories over a `k`-algebra (`ModuleCat.linearOverCommRing`):

* `square` : for `i ≠ j`, the composite of the two crossings `F_j F_i ⟶ F_i F_j ⟶ F_j F_i` is
  `Q_{ij}` evaluated in `End (F_j F_i)` at the dot on `F_i` and the dot on `F_j`. This is the
  quadratic KLR relation (KL I, arXiv:0803.4121v2, §2.1), in the form of Brundan's (1.3)
  (arXiv:1501.00350v1, Def. 1.1) recorded in `TwoRep.RouqUpKLR.square`.
* `braidQ` : for `i ≠ j`, the difference of the two composites of whiskered crossings
  `F_i F_j F_i ⟶ F_i F_j F_i` is `Q̄_{ij}` evaluated at the three dots, Brundan's (1.4) for
  equal outer labels, in the form of `TwoRep.RouqUpKLR.braidQ`.

Conventions, as in Kang–Kashiwara §3:
* `Q` is symmetric, `Q_{ij}(u, v) = Q_{ji}(v, u)` for `i ≠ j` (`KLRSymm Q`); this is an
  explicit hypothesis of `square`, since the left-hand side produces `Q_{ji}` at the dots
  `(x_p, x_{p+1})` while the right-hand side is `Q_{ij}` read on `(x_{p+1}, x_p)`.
* The crossing of two strands of the same colour enters the Rouquier relations as `-ψ`
  (`sameCross`): this is the sign that makes the nil-Hecke relations of `TwoRep.RouqLoc`
  (`x₂ τ - τ x₁ = 1`) hold, and with it `braidQ` holds with `Q̄_{ij}`. Distinct colours cross
  by `ψ` (`cross`).

Both sides of each relation are represented (`InductionAlong.Rep2`, `Rep3`) by elements of
`R^Λ(δ)`, and polynomials in represented endomorphisms are represented by the polynomials in
the elements (`InductionAlong.endHom_ncEval`). The relations then follow from
`KLRAlgebra.e_mul_ψ_sq` and `KLRAlgebra.e_mul_braid` on the blocks of the added strands.
-/

namespace Categorification.KLR

open CategoryTheory

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-- Two elements agree after the unit of a left block once they agree after each idempotent
of the block. -/
theorem IsLeftBlock.one_mul_eq {γ δ : Multiset I}
    {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w : ℕ → I} (hf : IsLeftBlock f w)
    {X Y : KLRAlgebra k Q δ} (h : ∀ (s : Seq γ) (t : Seq δ), Labels s w t → e t * X = e t * Y) :
    f 1 * X = f 1 * Y := by
  rw [IsLeftBlock.map_one_eq, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨t, ht, hl⟩ := hf.e_eq s
  rw [ht]
  exact h s t hl

omit [DecidableEq I] in
theorem Labels.apply_add {γ δ : Multiset I} {s : Seq γ} {w : ℕ → I} {t : Seq δ}
    (hl : Labels s w t) (q : ℕ) (hq : Multiset.card γ + q < Multiset.card δ) :
    t.1 ⟨Multiset.card γ + q, hq⟩ = w q := by
  rw [hl]
  simp

/-- A left block unit commutes with a dot on an added strand and absorbs the unit of its last
inclusion. -/
theorem IsLeftBlock.one_mul_dot_last {γ β δ : Multiset I} (i : I)
    {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q β} {w : ℕ → I} (hf : IsLeftBlock f w)
    (h : {i} + β = δ) (p : Fin (Multiset.card β)) (hp : Multiset.card γ ≤ p.val) :
    (lastIncl Q i h).comp f 1 * lastIncl Q i h (x p) =
      (lastIncl Q i h).comp f 1 * x ⟨p.val, by rw [card_lastIncl i h]; omega⟩ := by
  have hg := (hf.comp (isLeftBlock_lastIncl i h)).intertwines_dot
    ⟨p.val, by rw [card_lastIncl i h]; omega⟩ hp 1
  rw [(isLeftBlock_lastIncl i h).x_eq, ← mul_assoc, hg, mul_assoc,
    NonUnitalAlgHom.comp_apply, ← map_mul, mul_one, ← NonUnitalAlgHom.comp_apply, ← hg]

end KLRAlgebra

end Categorification.KLR

namespace Categorification.InductionAlong

open CategoryTheory

universe u' w' v'

variable {k : Type v'} [CommRing k] {A B D : Type u'} [Ring A] [Ring B] [Ring D] [Algebra k D]

theorem endHom_eq_of_unit_mul {G : ModuleCat.{max u' w'} A ⥤ ModuleCat.{max u' w'} D}
    {Φ : A →ₙ+* D} (e : G ≅ functor.{u', w'} Φ) {x y : selfInt k Φ}
    (h : Φ 1 * x.1 = Φ 1 * y.1) : endHom e x = endHom e y := by
  rw [endHom_apply, endHom_apply, natTrans_eq_of_unit_mul _ _ h]

theorem Rep2.neg {φ : A →ₙ+* B} {φ' : B →ₙ+* D} {ψ : A →ₙ+* B} {ψ' : B →ₙ+* D}
    {α : functor.{u', w'} φ ⋙ functor.{u', w'} φ' ⟶ functor.{u', w'} ψ ⋙ functor.{u', w'} ψ'}
    {x : D} {hx : Intertwines (φ'.comp φ) (ψ'.comp ψ) x} (hα : Rep2 α hx) :
    Rep2 (-α) hx.neg := by
  rw [Rep2, Preadditive.neg_comp, hα, natTrans_neg, Preadditive.comp_neg]

/-- A represented endomorphism of a double induction is `endHom` of its element. -/
theorem Rep2.eq_endHom {φ : A →ₙ+* B} {φ' : B →ₙ+* D}
    {α : functor.{u', w'} φ ⋙ functor.{u', w'} φ' ⟶ functor.{u', w'} φ ⋙ functor.{u', w'} φ'}
    {x : D} {hx : Intertwines (φ'.comp φ) (φ'.comp φ) x} (hα : Rep2 α hx) :
    α = endHom (k := k) (compIso.{u', w'} φ φ') ⟨x, hx⟩ := by
  rw [endHom_apply, ← Category.assoc, ← hα, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A represented endomorphism of a triple induction is `endHom` of its element. -/
theorem Rep3.eq_endHom {C : Type u'} [Ring C] {φ : A →ₙ+* B} {φ' : B →ₙ+* C}
    {φ'' : C →ₙ+* D}
    {α : functor.{u', w'} φ ⋙ (functor.{u', w'} φ' ⋙ functor.{u', w'} φ'') ⟶
      functor.{u', w'} φ ⋙ (functor.{u', w'} φ' ⋙ functor.{u', w'} φ'')}
    {x : D} {hx : Intertwines ((φ''.comp φ').comp φ) ((φ''.comp φ').comp φ) x}
    (hα : Rep3 α hx) :
    α = endHom (k := k) (tripleIso.{u', w'} φ φ' φ'') ⟨x, hx⟩ := by
  rw [endHom_apply, ← Category.assoc, ← hα, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Coercion of `ncEval` out of the subalgebra of self-intertwiners. -/
theorem selfInt_ncEval {Φ : A →ₙ+* D} {n : ℕ} (y : Fin n → selfInt k Φ)
    (p : MvPolynomial (Fin n) k) :
    ((KLR.ncEval y p : selfInt k Φ) : D) = KLR.ncEval (fun a => (y a : D)) p :=
  KLR.ncEval_map (selfInt k Φ).val y p

end Categorification.InductionAlong

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory KLRAlgebra InductionAlong MvPolynomial

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

/-- The dot on an added strand of a block, in the cyclotomic quotient, as a self-intertwiner
of the composite inclusion. -/
theorem mk_x_mem {γ δ : Multiset I} {F : CycKLR k Q a γ →ₙ+* CycKLR k Q a δ}
    {f : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q δ} {w : ℕ → I} (hf : IsLeftBlock f w)
    (hF : ∀ r, F (CycKLR.mk k Q a γ r) = CycKLR.mk k Q a δ (f r))
    (p : Fin (Multiset.card δ)) (hp : Multiset.card γ ≤ p.val) :
    CycKLR.mk k Q a δ (x p) ∈ selfInt k F :=
  intertwines_mk hF hF (hf.intertwines_dot p hp)

theorem rename_rev_two (P : MvPolynomial (Fin 2) k) :
    rename Fin.rev (rename ![1, 0] P) = P := by
  rw [rename_rename]
  have : (Fin.rev ∘ ![(1 : Fin 2), 0]) = id := by
    funext c
    fin_cases c <;> rfl
  rw [this, rename_id_apply]

variable (Q a) in
/-- **The quadratic KLR relation for distinct colours** (KL I §2.1; Brundan,
arXiv:1501.00350v1, (1.3), as in `TwoRep.RouqUpKLR.square`), for cyclotomic induction
functors. Hypothesis: `Q` is symmetric (`KLRSymm Q`), as in Kang–Kashiwara §3. -/
theorem square (hQ : KLRSymm Q) (i j : I) (hij : i ≠ j) {γ β β' δ : Multiset I}
    (h₁ : {j} + γ = β) (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ) :
    cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄ ≫ cross Q a j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (ind.{u, v, w} Q a j h₁ ⋙ ind Q a i h₂))
        ![Functor.whiskerLeft (ind Q a j h₁) (dot Q a i h₂),
          Functor.whiskerRight (dot Q a j h₁) (ind Q a i h₂)] (Q i j) := by
  set p := Multiset.card γ
  have hβ : Multiset.card β = p + 1 := card_lastIncl j h₁
  have hδ : Multiset.card δ = p + 2 := card_double h₁ h₂
  have B := isLeftBlock_double Q i j h₁ h₂
  have hF := lastEmb_comp_mk (Q := Q) (a := a) i j h₁ h₂
  set e := compIso.{max u v, w} (lastEmb Q a j h₁) (lastEmb Q a i h₂)
  have hL := ((rep_cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄).comp
    (rep_cross.{u, v, w} Q a j i h₃ h₄ h₁ h₂)).eq_endHom (k := k)
  have h1 := (Rep2.whiskerLeft (lastEmb Q a j h₁) (intertwines_dotElt Q a i h₂)).eq_endHom
    (k := k)
  have h2 := (Rep2.whiskerRight (lastEmb Q a i h₂) (intertwines_dotElt Q a j h₁)).eq_endHom
    (k := k)
  let X0 : selfInt k ((lastEmb Q a i h₂).comp (lastEmb Q a j h₁)) :=
    ⟨_, mk_x_mem B hF ⟨p, by omega⟩ le_rfl⟩
  let X1 : selfInt k ((lastEmb Q a i h₂).comp (lastEmb Q a j h₁)) :=
    ⟨_, mk_x_mem B hF ⟨p + 1, by omega⟩ (Nat.le_succ _)⟩
  have hunit : ((lastEmb Q a i h₂).comp (lastEmb Q a j h₁)) 1 =
      CycKLR.mk k Q a δ (doubleIncl (Q := Q) i j h₁ h₂ 1) := by
    rw [← map_one (CycKLR.mk k Q a γ), hF]
  have h1' : Functor.whiskerLeft (ind.{u, v, w} Q a j h₁) (dot Q a i h₂) = endHom e X1 := by
    refine h1.trans (endHom_eq_of_unit_mul e ?_)
    change _ * dotElt Q a i h₂ = _ * CycKLR.mk k Q a δ (x ⟨p + 1, _⟩)
    simp only [dotElt, hβ]
  have h2' : Functor.whiskerRight (dot.{u, v, w} Q a j h₁) (ind Q a i h₂) = endHom e X0 := by
    refine h2.trans (endHom_eq_of_unit_mul e ?_)
    change _ * lastEmb Q a i h₂ (dotElt Q a j h₁) = _ * CycKLR.mk k Q a δ (x ⟨p, _⟩)
    rw [hunit, dotElt, lastEmb_mk, ← map_mul, ← map_mul]
    exact congrArg _ ((isLeftBlock_lastIncl j h₁).one_mul_dot_last i h₂ _ le_rfl)
  have hR : KLR.ncEval (A := End (ind.{u, v, w} Q a j h₁ ⋙ ind Q a i h₂))
      ![Functor.whiskerLeft (ind Q a j h₁) (dot Q a i h₂),
        Functor.whiskerRight (dot Q a j h₁) (ind Q a i h₂)] (Q i j) =
      endHom e (KLR.ncEval ![X0, X1] (Q j i)) := by
    rw [endHom_ncEval, hQ i j hij, rename_rev_two, h1', h2']
    congr 1
    funext c
    fin_cases c <;> rfl
  rw [hR]
  refine hL.trans (endHom_eq_of_unit_mul e ?_)
  rw [selfInt_ncEval]
  change _ * (crossElt Q a (γ := γ) (δ := δ) * crossElt Q a (γ := γ) (δ := δ)) =
    _ * KLR.ncEval ![CycKLR.mk k Q a δ (x ⟨p, _⟩), CycKLR.mk k Q a δ (x ⟨p + 1, _⟩)] (Q j i)
  have hev : KLR.ncEval ![CycKLR.mk k Q a δ (x ⟨p, by omega⟩),
      CycKLR.mk k Q a δ (x ⟨p + 1, by omega⟩)] (Q j i) =
      CycKLR.mk k Q a δ (KLR.ncEval ![(x ⟨p, by omega⟩ : KLRAlgebra k Q δ), x ⟨p + 1, by omega⟩]
        (Q j i)) := by
    rw [KLR.ncEval_map]
    congr 1
    funext c
    fin_cases c <;> rfl
  rw [hev, hunit, crossElt, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  refine B.one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  simp only [add_zero] at l0
  rw [e_mul_ψ_sq _ (by omega), ncEval_x2]
  simp only [Seq.lbl, l0, l1, ite_true, Nat.one_ne_zero, ite_false, hij.symm]
  rfl

end Categorification.KLR.CyclotomicAction

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial

universe u v

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

/-- A crossing of two of three added strands moves a block unit to the unit of the block
with exchanged labels. -/
theorem triple_cross {x y z x' y' z' : I} (q : ℕ) {l m : Multiset I}
    {f g : KLRAlgebra k Q l →ₙₐ[k] KLRAlgebra k Q m} (hf : IsLeftBlock f (tripleWord x y z))
    (hg : IsLeftBlock g (tripleWord x' y' z'))
    (hw : ∀ n, n < 3 → tripleWord x' y' z' n = IsLeftBlock.swapAt (tripleWord x y z) q n)
    (hq : q < 2) (hm : Multiset.card m = Multiset.card l + 3) :
    f 1 * ψ (Multiset.card l + q) = ψ (Multiset.card l + q) * g 1 :=
  hf.intertwines_cross (hg.congr_word fun n hn => hw n (by omega)) (by omega) 1

/-- The KLR identity behind the `i, j, i` braid relation, with `p = card a`. -/
theorem braidQ_identity (i j : I) (hij : i ≠ j) {a b c d e f : Multiset I}
    (h₁ : {i} + a = b) (h₂ : {j} + b = c) (h₃ : {i} + c = f) (h₄ : {i} + b = d)
    (h₅ : {j} + d = f) (h₆ : {j} + a = e) (h₇ : {i} + e = c) :
    tripleIncl Q i j i h₁ h₂ h₃ 1 *
        (ψ (Multiset.card a + 1) * (lastIncl Q j h₅ (-ψ (Multiset.card a)) *
          ψ (Multiset.card a + 1)) -
        lastIncl Q i h₃ (ψ (Multiset.card a)) * (-ψ (Multiset.card a + 1) *
          lastIncl Q i h₃ (ψ (Multiset.card a)))) =
      tripleIncl Q i j i h₁ h₂ h₃ 1 *
        pol (rename ![⟨Multiset.card a, by rw [card_triple h₁ h₂ h₃]; omega⟩,
          ⟨Multiset.card a + 1, by rw [card_triple h₁ h₂ h₃]; omega⟩,
          ⟨Multiset.card a + 2, by rw [card_triple h₁ h₂ h₃]; omega⟩] (qbar (Q i j))) := by
  set p := Multiset.card a
  have hm : Multiset.card f = p + 3 := card_triple h₁ h₂ h₃
  have hb : Multiset.card b = p + 1 := card_lastIncl i h₁
  have hc : Multiset.card c = p + 2 := by rw [card_lastIncl j h₂]; omega
  have hd : Multiset.card d = p + 2 := by rw [card_lastIncl i h₄]; omega
  have U := isLeftBlock_triple (Q := Q) i j i h₁ h₂ h₃
  have U₁ := isLeftBlock_triple (Q := Q) i i j h₁ h₄ h₅
  have V₁ := isLeftBlock_triple (Q := Q) j i i h₆ h₇ h₃
  have c1 : tripleIncl Q i j i h₁ h₂ h₃ 1 * ψ (p + 1) = ψ (p + 1) * tripleIncl Q i i j h₁ h₄ h₅ 1 :=
    triple_cross 1 U U₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have c2 : tripleIncl Q i i j h₁ h₄ h₅ 1 * ψ (p + 0) = ψ (p + 0) * tripleIncl Q i i j h₁ h₄ h₅ 1 :=
    triple_cross 0 U₁ U₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have c3 : tripleIncl Q i i j h₁ h₄ h₅ 1 * ψ (p + 1) = ψ (p + 1) * tripleIncl Q i j i h₁ h₂ h₃ 1 :=
    triple_cross 1 U₁ U (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have d1 : tripleIncl Q i j i h₁ h₂ h₃ 1 * ψ (p + 0) = ψ (p + 0) * tripleIncl Q j i i h₆ h₇ h₃ 1 :=
    triple_cross 0 U V₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have d2 : tripleIncl Q j i i h₆ h₇ h₃ 1 * ψ (p + 1) = ψ (p + 1) * tripleIncl Q j i i h₆ h₇ h₃ 1 :=
    triple_cross 1 V₁ V₁ (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  have d3 : tripleIncl Q j i i h₆ h₇ h₃ 1 * ψ (p + 0) = ψ (p + 0) * tripleIncl Q i j i h₁ h₂ h₃ 1 :=
    triple_cross 0 V₁ U (by intro n hn; interval_cases n <;> simp [tripleWord, IsLeftBlock.swapAt])
      (by omega) hm
  simp only [add_zero] at c2 d1 d3
  rw [map_neg, lastIncl_ψ j h₅ (by omega), lastIncl_ψ i h₃ (by omega)]
  have ra : ∀ {a b c d : KLRAlgebra k Q f}, a * b = c * d → ∀ x, a * (b * x) = c * (d * x) :=
    fun h x => by rw [← mul_assoc, h, mul_assoc]
  have ab : ∀ (x y z : I) {β β' : Multiset I} (g₁ : {x} + a = β) (g₂ : {y} + β = β')
      (g₃ : {z} + β' = f) (t : KLRAlgebra k Q f),
      tripleIncl Q x y z g₁ g₂ g₃ 1 * (lastIncl Q z g₃ 1 * t) = tripleIncl Q x y z g₁ g₂ g₃ 1 * t :=
    fun x y z _ _ g₁ g₂ g₃ t => by rw [← mul_assoc, triple_one_mul_last]
  have hA : tripleIncl Q i j i h₁ h₂ h₃ 1 * (ψ (p + 1) * (ψ p * ψ (p + 1))) =
      ψ (p + 1) * (ψ p * (ψ (p + 1) * tripleIncl Q i j i h₁ h₂ h₃ 1)) := by
    rw [ra c1, ra c2, c3]
  have hB : tripleIncl Q i j i h₁ h₂ h₃ 1 * (ψ p * (ψ (p + 1) * ψ p)) =
      ψ p * (ψ (p + 1) * (ψ p * tripleIncl Q i j i h₁ h₂ h₃ 1)) := by
    rw [ra d1, ra d2, d3]
  have hA' : tripleIncl Q i j i h₁ h₂ h₃ 1 *
      (ψ (p + 1) * (-(ψ p * lastIncl Q j h₅ 1) * ψ (p + 1))) =
      -(tripleIncl Q i j i h₁ h₂ h₃ 1 * (ψ (p + 1) * (ψ p * ψ (p + 1)))) := by
    rw [hA]
    simp only [neg_mul, mul_neg, mul_assoc]
    rw [ra c1, ra c2, ab, c3]
  have hB' : tripleIncl Q i j i h₁ h₂ h₃ 1 *
      (ψ p * lastIncl Q i h₃ 1 * (-ψ (p + 1) * (ψ p * lastIncl Q i h₃ 1))) =
      -(tripleIncl Q i j i h₁ h₂ h₃ 1 * (ψ p * (ψ (p + 1) * ψ p))) := by
    rw [hB]
    simp only [neg_mul, mul_neg, mul_assoc]
    rw [ra d1, ab, ra d2, ra d3, triple_one_mul_last]
  rw [mul_sub, hA', hB', neg_sub_neg, ← mul_sub]
  refine U.one_mul_eq fun s t hl => ?_
  have l0 := hl.apply_add 0 (by omega)
  have l1 := hl.apply_add 1 (by omega)
  have l2 := hl.apply_add 2 (by omega)
  simp only [add_zero] at l0
  simp only [tripleWord, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_true,
    ite_false] at l0 l1 l2
  have key := e_mul_braid (Q := Q) p (by omega) t
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simp only [Seq.lbl]; rw [l0, l2],
    by simp only [Seq.lbl]; rw [l0, l1]; exact hij⟩)] at key
  have hQ : Q (t.lbl ⟨p, by omega⟩) (t.lbl ⟨p + 1, by omega⟩) = Q i j := by
    simp only [Seq.lbl]; rw [l0, l1]
  rw [hQ] at key
  rw [← key]
  simp only [mul_assoc]

end Categorification.KLR.KLRAlgebra

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory KLRAlgebra InductionAlong MvPolynomial

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

variable (Q a) in
/-- The crossing of two strands of the same colour as it enters the Rouquier relations: the
negative of the crossing element `ψ`. With this sign the nil-Hecke relations of
`TwoRep.RouqLoc` and the `i, j, i` braid relation `braidQ` hold. -/
noncomputable def sameCross (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    ind.{u, v, w} Q a i h₁ ⋙ ind Q a i h₂ ⟶ ind Q a i h₁ ⋙ ind Q a i h₂ :=
  -cross Q a i i h₁ h₂ h₁ h₂

variable (Q a) in
theorem rep_sameCross (i : I) {γ β δ : Multiset I} (h₁ : {i} + γ = β) (h₂ : {i} + β = δ) :
    Rep2 (sameCross.{u, v, w} Q a i h₁ h₂) (intertwines_crossElt Q a i i h₁ h₂ h₁ h₂).neg :=
  (rep_cross Q a i i h₁ h₂ h₁ h₂).neg

theorem rename_rev_three (P : MvPolynomial (Fin 3) k) : rename Fin.rev P = rename ![2, 1, 0] P := by
  have : (Fin.rev : Fin 3 → Fin 3) = ![2, 1, 0] := by
    funext c
    fin_cases c <;> rfl
  rw [this]

variable (Q a) in
/-- **The braid relation with equal outer labels** (KL I §2.1; Brundan, arXiv:1501.00350v1,
(1.4) for outer labels `i, i` and middle label `j ≠ i`, as in `TwoRep.RouqUpKLR.braidQ`) for
cyclotomic induction functors: the difference of the two composites of whiskered crossings
`F_i F_j F_i ⟶ F_i F_j F_i` is `Q̄_{ij}` evaluated at the three dots. The middle crossings
have equal colours and enter as `sameCross`, i.e. as `-ψ`. -/
theorem braidQ (i j : I) (hij : i ≠ j) {γ β β₁ β₂ β₃ δ : Multiset I}
    (h₁ : {i} + γ = β) (h₂ : {j} + β = β₁) (h₃ : {i} + β₁ = δ) (h₄ : {i} + β = β₂)
    (h₅ : {j} + β₂ = δ) (h₆ : {j} + γ = β₃) (h₇ : {i} + β₃ = β₁) :
    (Functor.whiskerLeft (ind.{u, v, w} Q a i h₁) (cross Q a i j h₂ h₃ h₄ h₅) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sameCross Q a i h₁ h₄) (ind Q a j h₅) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a i h₁) (cross Q a j i h₄ h₅ h₂ h₃)) -
      (((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (cross Q a j i h₁ h₂ h₆ h₇) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom) ≫
        Functor.whiskerLeft (ind Q a j h₆) (sameCross Q a i h₇ h₃) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (cross Q a i j h₆ h₇ h₁ h₂) (ind Q a i h₃) ≫
          (Functor.associator _ _ _).hom)) =
      KLR.ncEval (A := End (ind.{u, v, w} Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃))
        ![Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerLeft (ind Q a j h₂) (dot Q a i h₃)),
          Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerRight (dot Q a j h₂) (ind Q a i h₃)),
          Functor.whiskerRight (dot Q a i h₁) (ind Q a j h₂ ⋙ ind Q a i h₃)]
        (KLR.qbar (Q i j)) := by
  set p := Multiset.card γ
  have hβ : Multiset.card β = p + 1 := card_lastIncl i h₁
  have hβ₁ : Multiset.card β₁ = p + 2 := by rw [card_lastIncl j h₂]; omega
  have hβ₃ : Multiset.card β₃ = p + 1 := card_lastIncl j h₆
  have hδ : Multiset.card δ = p + 3 := card_triple h₁ h₂ h₃
  have U := isLeftBlock_triple (Q := Q) i j i h₁ h₂ h₃
  set Φ := ((lastEmb Q a i h₃).comp (lastEmb Q a j h₂)).comp (lastEmb Q a i h₁)
  have hF : ∀ r, Φ (CycKLR.mk k Q a γ r) = CycKLR.mk k Q a δ (tripleIncl Q i j i h₁ h₂ h₃ r) :=
    fun r => by
      simp only [Φ, NonUnitalRingHom.comp_apply, lastEmb_mk]
      rfl
  have hunit : Φ 1 = CycKLR.mk k Q a δ (tripleIncl Q i j i h₁ h₂ h₃ 1) := by
    rw [← map_one (CycKLR.mk k Q a γ), hF]
  set e := tripleIso.{max u v, w} (lastEmb Q a i h₁) (lastEmb Q a j h₂) (lastEmb Q a i h₃)
  let X : ∀ q : ℕ, q < 3 → selfInt k Φ := fun q hq =>
    ⟨_, mk_x_mem U hF ⟨p + q, by omega⟩ (Nat.le_add_right _ _)⟩
  -- the three dots
  have d2 : Functor.whiskerLeft (ind.{u, v, w} Q a i h₁)
      (Functor.whiskerLeft (ind Q a j h₂) (dot Q a i h₃)) = endHom e (X 2 (by omega)) := by
    refine ((Rep3.whiskerLeft (lastEmb Q a i h₁)
      (Rep2.whiskerLeft (lastEmb Q a j h₂) (intertwines_dotElt Q a i h₃))).eq_endHom
        (k := k)).trans (endHom_eq_of_unit_mul e ?_)
    change _ * dotElt Q a i h₃ = _ * CycKLR.mk k Q a δ (x ⟨p + 2, _⟩)
    simp only [dotElt, hβ₁]
  have d1 : Functor.whiskerLeft (ind.{u, v, w} Q a i h₁)
      (Functor.whiskerRight (dot Q a j h₂) (ind Q a i h₃)) = endHom e (X 1 (by omega)) := by
    refine ((Rep3.whiskerLeft (lastEmb Q a i h₁)
      (Rep2.whiskerRight (lastEmb Q a i h₃) (intertwines_dotElt Q a j h₂))).eq_endHom
        (k := k)).trans (endHom_eq_of_unit_mul e ?_)
    change _ * lastEmb Q a i h₃ (dotElt Q a j h₂) = _ * CycKLR.mk k Q a δ (x ⟨p + 1, _⟩)
    rw [hunit, dotElt, lastEmb_mk, ← map_mul, ← map_mul]
    refine congrArg _ (((isLeftBlock_double Q j i h₁ h₂).one_mul_dot_last i h₃ _
      (by change p ≤ Multiset.card β; omega)).trans ?_)
    simp only [hβ]
    rfl
  have d0 : Functor.whiskerRight (dot.{u, v, w} Q a i h₁) (ind Q a j h₂ ⋙ ind Q a i h₃) =
      endHom e (X 0 (by omega)) := by
    refine ((Rep3.whiskerRight₂ (lastEmb Q a j h₂) (lastEmb Q a i h₃)
      (intertwines_dotElt Q a i h₁)).eq_endHom (k := k)).trans (endHom_eq_of_unit_mul e ?_)
    change _ * lastEmb Q a i h₃ (lastEmb Q a j h₂ (dotElt Q a i h₁)) =
      _ * CycKLR.mk k Q a δ (x ⟨p + 0, _⟩)
    rw [hunit, dotElt, lastEmb_mk, lastEmb_mk, ← map_mul, ← map_mul]
    refine congrArg _ ?_
    have s1 := (isLeftBlock_lastIncl i h₁).one_mul_dot_last (Q := Q) j h₂ ⟨p, by omega⟩ le_rfl
    have s2 := (isLeftBlock_double Q j i h₁ h₂).one_mul_dot_last i h₃ ⟨p, by omega⟩ le_rfl
    change lastIncl Q i h₃ (doubleIncl Q j i h₁ h₂ 1) * lastIncl Q i h₃ (lastIncl Q j h₂ _) = _
    rw [← map_mul]
    change lastIncl Q i h₃ ((lastIncl Q j h₂).comp (lastIncl Q i h₁) 1 * _) = _
    rw [s1, map_mul]
    exact s2
  have L := (Rep3.whiskerLeft (lastEmb Q a i h₁) (rep_cross.{u, v, w} Q a i j h₂ h₃ h₄ h₅)).comp
    ((Rep3.whiskerRight (lastEmb Q a j h₅) (rep_sameCross.{u, v, w} Q a i h₁ h₄)).comp
      (Rep3.whiskerLeft (lastEmb Q a i h₁) (rep_cross.{u, v, w} Q a j i h₄ h₅ h₂ h₃)))
  have R := (Rep3.whiskerRight (lastEmb Q a i h₃) (rep_cross.{u, v, w} Q a j i h₁ h₂ h₆ h₇)).comp
    ((Rep3.whiskerLeft (lastEmb Q a j h₆) (rep_sameCross.{u, v, w} Q a i h₇ h₃)).comp
      (Rep3.whiskerRight (lastEmb Q a i h₃) (rep_cross.{u, v, w} Q a i j h₆ h₇ h₁ h₂)))
  have hR : KLR.ncEval (A := End (ind.{u, v, w} Q a i h₁ ⋙ ind Q a j h₂ ⋙ ind Q a i h₃))
      ![Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerLeft (ind Q a j h₂) (dot Q a i h₃)),
        Functor.whiskerLeft (ind Q a i h₁) (Functor.whiskerRight (dot Q a j h₂) (ind Q a i h₃)),
        Functor.whiskerRight (dot Q a i h₁) (ind Q a j h₂ ⋙ ind Q a i h₃)]
      (KLR.qbar (Q i j)) =
      endHom e (KLR.ncEval ![X 0 (by omega), X 1 (by omega), X 2 (by omega)]
        (KLR.qbar (Q i j))) := by
    rw [endHom_ncEval, rename_rev_three, qbar_rename_rev, d0, d1, d2]
    congr 1
    funext c
    fin_cases c <;> rfl
  rw [hR]
  refine ((L.sub R).eq_endHom (k := k)).trans (endHom_eq_of_unit_mul e ?_)
  rw [selfInt_ncEval]
  have hev : KLR.ncEval (fun c => ((![X 0 (by omega), X 1 (by omega), X 2 (by omega)] c :
      selfInt k Φ) : CycKLR k Q a δ)) (KLR.qbar (Q i j)) =
      CycKLR.mk k Q a δ (KLR.ncEval ![(x ⟨p + 0, by omega⟩ : KLRAlgebra k Q δ),
        x ⟨p + 1, by omega⟩, x ⟨p + 2, by omega⟩] (KLR.qbar (Q i j))) := by
    rw [KLR.ncEval_map]
    congr 1
    funext c
    fin_cases c <;> rfl
  rw [hev, ncEval_x3, hunit]
  change _ * (crossElt Q a (γ := β) (δ := δ) * (lastEmb Q a j h₅ (-crossElt Q a (γ := γ)
      (δ := β₂)) * crossElt Q a (γ := β) (δ := δ)) -
    lastEmb Q a i h₃ (crossElt Q a (γ := γ) (δ := β₁)) * (-crossElt Q a (γ := β₃) (δ := δ) *
      lastEmb Q a i h₃ (crossElt Q a (γ := γ) (δ := β₁)))) = _
  simp only [crossElt, ← map_neg, lastEmb_mk, ← map_mul, ← map_sub]
  congr 1
  rw [hβ, hβ₃]
  exact braidQ_identity (Q := Q) i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇
