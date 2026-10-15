/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqTwist
import Categorification.TwoRep.RouqFullCL
import Categorification.TwoRep.RouqMixedPitchfork
import Categorification.TwoRep.RouqKLRAction
import Categorification.Diagrams.KL3.SymmetrySigma
import Categorification.KLR.Symmetries

/-!
# The reverse of a Rouquier family

For a Rouquier family `S` in a bicategory `B` (J. Brundan, *On the definition of Kac–Moody
2-category*, arXiv:1501.00350v1, Definition 1.1), the **reverse** `S.reverse` is a Rouquier family
in the horizontal opposite `HOp B`, at the negated weights, with the same upward 1-morphisms read
backwards:

* the object at `x` is `S.obj (-x)`;
* `E'_i = op E_i`, `F'_i = op F_i`, with the adjunction `op E_i ⊣ op F_i` reflected from the
  left adjunction `F_i ⊣ E_i` of Brundan's Theorem 4.3 (`RouqFamily.adjL`);
* the dots are the dots of `S`, and the crossing of colours `i, j` is minus the crossing of `S`
  of colours `j, i`.

Rouquier's local data of the reverse are those of the twist (`RouqFamily.twist`; KL III
arXiv:0807.3250v1, §3.3.2, `ω̃`) reflected through right mates (`RouqLoc.mirror`): the double
right mates of the dots and crossings are the original ones by Brundan's cyclicity (5.6), (5.7)
(`RouqFamily.dotDn`, `RouqFamily.cyclic_cross`).

In `HOp B` the horizontal composition is reversed, so a representable 2-functor
`Hom_{HOp B}(w, -)` is precomposition `Hom_B(-, w)`. Applied to a lowest-weight family (for
instance cyclotomic induction), the reverse gives a highest-weight family on the categories of
functors out of it. This is the highest-weight factor of Webster's test representations
(B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of
Theorem `nondegenerate`).

## Main declarations

* `RouqFamily.reverse`;
* `RouqFamily.reverse_upKLR`: the mixed upward KLR relations (Brundan (1.2)–(1.4)) for `Q`
  satisfying `Q_ji(u, v) = Q_ij(v, u)`;
* `RouqFamily.reverse_mixedInversion`: Brundan's mixed inversion (1.7) for the reverse, from
  that of `S` and Brundan's scalars (`RouqFamily.mixed_mate`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

/-! ## Linear structure of the horizontal opposite -/

namespace HOp

variable {k : Type w'} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

instance (a b : HOp B) : Linear k (a ⟶ b) := inferInstanceAs (Linear k (obj b ⟶ obj a))

instance [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] (a : HOp B) {b c : HOp B}
    (f : b ⟶ c) : (postcomp a f).Linear k where
  map_smul η r := Functor.map_smul (precomp (obj a) (show obj c ⟶ obj b from f)) r η

instance [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] {a b : HOp B} (c : HOp B)
    (f : a ⟶ b) : (precomp c f).Linear k where
  map_smul η r := Functor.map_smul (postcomp (obj c) (show obj b ⟶ obj a from f)) r η

end HOp

/-! ## Equal data -/

namespace RouqLoc

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂}

/-- Rouquier's data with the dots and the crossing replaced by equal ones. -/
def ofEq {x₁ x₁' : E₁ ⟶ E₁} {x₂ x₂' : E₂ ⟶ E₂} {τ τ' : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}
    (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (hx₁ : x₁ = x₁') (hx₂ : x₂ = x₂') (hτ : τ = τ') :
    RouqLoc adj₁ adj₂ x₁' x₂' τ' h := by
  subst hx₁ hx₂ hτ
  exact L

end RouqLoc

/-! ## The reverse family -/

namespace RouqFamily

open QuantumGroup UDot

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} (S : RouqFamily (B := B) RD)

/-- The double right mate of the downward dot is the dot. -/
theorem conj_dotDn (i : I) {x y : X} (h : x + RD.iX i = y) :
    conjugateEquiv (S.adjL i h) (S.adjL i h) (S.dotDn i h) = S.dot i h := by
  rw [dotDn, Equiv.apply_symm_apply]

/-- **The reverse of a Rouquier family**, in the horizontal opposite: objects `x ↦ S.obj (-x)`,
`E' = op E`, `F' = op F`, the adjunction reflected from the left adjunction `F ⊣ E` (Brundan
Theorem 4.3), the same dots, and minus the crossings with the colours exchanged. -/
def reverse : RouqFamily (B := HOp B) RD where
  obj x := HOp.mk (S.obj (-x))
  E i _ _ h := HOp.op1 (S.E i (neg_reg i h))
  F i _ _ h := HOp.op1 (S.F i (neg_reg i h))
  adj i _ _ h := HOp.adjunction (S.adjL i (neg_reg i h))
  dot i _ _ h := S.dot i (neg_reg i h)
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ :=
    -S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)
  square i _ _ _ h₁ h₂ := by
    change (-S.cross i i _ _ _ _) ≫ (-S.cross i i _ _ _ _) = 0
    rw [Preadditive.neg_comp_neg]
    exact S.square i (neg_reg i h₂) (neg_reg i h₁)
  braid i _ _ _ _ h₁ h₂ h₃ := by
    have hb := congrArg (fun t => (α_ (S.E i (neg_reg i h₃)) (S.E i (neg_reg i h₂))
      (S.E i (neg_reg i h₁))).hom ≫ t ≫ (α_ (S.E i (neg_reg i h₃)) (S.E i (neg_reg i h₂))
      (S.E i (neg_reg i h₁))).inv) (S.braid i (neg_reg i h₃) (neg_reg i h₂) (neg_reg i h₁)).symm
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at hb
    change (-S.cross i i _ _ _ _) ▷ S.E i (neg_reg i h₁) ≫
        ((α_ _ _ _).hom ≫ S.E i (neg_reg i h₃) ◁ (-S.cross i i _ _ _ _) ≫ (α_ _ _ _).inv) ≫
        (-S.cross i i _ _ _ _) ▷ S.E i (neg_reg i h₁) =
      ((α_ _ _ _).hom ≫ S.E i (neg_reg i h₃) ◁ (-S.cross i i _ _ _ _) ≫ (α_ _ _ _).inv) ≫
        (-S.cross i i _ _ _ _) ▷ S.E i (neg_reg i h₁) ≫
        ((α_ _ _ _).hom ≫ S.E i (neg_reg i h₃) ◁ (-S.cross i i _ _ _ _) ≫ (α_ _ _ _).inv)
    simp only [AdditiveWhiskering.neg_whiskerRight, AdditiveWhiskering.whiskerLeft_neg,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, neg_inj, Category.assoc]
    exact hb
  loc i _ _ _ h₁ h₂ :=
    ((S.twist.loc i h₁ h₂).mirror).ofEq
      (by
        change conjugateEquiv (S.adjL i (neg_reg i h₁)) (S.adjL i (neg_reg i h₁))
          (S.twist.dot i h₁) = S.dot i (neg_reg i h₁)
        rw [twist_dot, conj_dotDn])
      (by
        change conjugateEquiv (S.adjL i (neg_reg i h₂)) (S.adjL i (neg_reg i h₂))
          (S.twist.dot i h₂) = S.dot i (neg_reg i h₂)
        rw [twist_dot, conj_dotDn])
      (by
        change conjugateEquiv ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂)))
          ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂)))
          (-conjugateEquiv ((S.adj i (neg_reg i h₂)).comp (S.adj i (neg_reg i h₁)))
            ((S.adj i (neg_reg i h₂)).comp (S.adj i (neg_reg i h₁)))
            (S.cross i i (neg_reg i h₂) (neg_reg i h₁) (neg_reg i h₂) (neg_reg i h₁))) = _
        rw [show ∀ φ, conjugateEquiv ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂)))
            ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂))) (-φ) =
            -conjugateEquiv ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂)))
              ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂))) φ from fun φ =>
            map_neg (RouqSl2Generic.rightMateAddEquiv
              ((S.adjL i (neg_reg i h₁)).comp (S.adjL i (neg_reg i h₂)))) φ,
          S.cyclic_cross i (neg_reg i h₂) (neg_reg i h₁)])

@[simp] theorem reverse_obj (x : X) : S.reverse.obj x = HOp.mk (S.obj (-x)) := rfl

theorem reverse_E (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.reverse.E i h = HOp.op1 (S.E i (neg_reg i h)) := rfl

theorem reverse_F (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.reverse.F i h = HOp.op1 (S.F i (neg_reg i h)) := rfl

theorem reverse_dot (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.reverse.dot i h = S.dot i (neg_reg i h) := rfl

theorem reverse_cross (i j : I) {a b c d : X} (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    S.reverse.cross i j h₁ h₂ h₃ h₄ =
      -S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃) := rfl

/-! ## The mixed upward relations of the reverse -/

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
/-- Dots on the two right strands of a composite of three 1-morphisms commute. -/
theorem commute_whiskerLeft_exchange {a b c d : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (η : g ⟶ g) (θ : h ⟶ h) : @Commute (End (f ≫ g ≫ h)) _ (f ◁ g ◁ θ) (f ◁ η ▷ h) := by
  show f ◁ η ▷ h ≫ f ◁ g ◁ θ = f ◁ g ◁ θ ≫ f ◁ η ▷ h
  rw [← whiskerLeft_comp, ← whiskerLeft_comp, whisker_exchange]

section UpKLR

variable {k : Type w'} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]

/-- **The mixed upward KLR relations of the reverse** (Brundan (1.2)–(1.4)), for parameters with
`Q_ji(u, v) = Q_ij(v, u)`. -/
theorem reverse_upKLR (Q : I → I → MvPolynomial (Fin 2) k) (hQ : KLR.KLRSymm Q)
    (H : RouqUpKLR S Q) : RouqUpKLR S.reverse Q where
  square := by
    intro i j hij a b c d h₁ h₂ h₃ h₄
    change (-S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)) ≫
        (-S.cross i j (neg_reg j h₄) (neg_reg i h₃) (neg_reg i h₂) (neg_reg j h₁)) =
      KLR.ncEval (A := End (S.E i (neg_reg i h₂) ≫ S.E j (neg_reg j h₁)))
        ![S.dot i (neg_reg i h₂) ▷ S.E j (neg_reg j h₁),
          S.E i (neg_reg i h₂) ◁ S.dot j (neg_reg j h₁)] (Q i j)
    rw [Preadditive.neg_comp_neg, H.square j i hij.symm, hQ i j hij,
      ← KL3.Diagram.ncEval_rename_of_commute _ (by
        intro x y
        fin_cases x <;> fin_cases y
        · exact Commute.refl _
        · exact (whisker_exchange _ _).symm
        · exact whisker_exchange _ _
        · exact Commute.refl _)]
    congr 1
    funext l
    fin_cases l <;> rfl
  slide_left := by
    intro i j hij a b c d h₁ h₂ h₃ h₄
    change S.dot i (neg_reg i h₂) ▷ S.E j (neg_reg j h₁) ≫
        (-S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)) =
      (-S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)) ≫
        S.E j (neg_reg j h₄) ◁ S.dot i (neg_reg i h₃)
    rw [Preadditive.comp_neg, Preadditive.neg_comp,
      H.slide_right j i hij.symm (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)]
  slide_right := by
    intro i j hij a b c d h₁ h₂ h₃ h₄
    change S.E i (neg_reg i h₂) ◁ S.dot j (neg_reg j h₁) ≫
        (-S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)) =
      (-S.cross j i (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)) ≫
        S.dot j (neg_reg j h₄) ▷ S.E i (neg_reg i h₃)
    rw [Preadditive.comp_neg, Preadditive.neg_comp,
      H.slide_left j i hij.symm (neg_reg i h₂) (neg_reg j h₁) (neg_reg j h₄) (neg_reg i h₃)]
  braid := by
    intro i j c hb l w₁ w₂ w₃ w₄ w₅ w₆ m e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    have h := congrArg (fun t => (α_ (S.E i (neg_reg i e3)) (S.E j (neg_reg j e2))
        (S.E c (neg_reg c e1))).hom ≫ t ≫ (α_ (S.E c (neg_reg c e9)) (S.E j (neg_reg j e8))
        (S.E i (neg_reg i e6))).inv)
      (H.braid c j i (Ne.symm hb) (neg_reg i e3) (neg_reg j e2) (neg_reg c e1) (neg_reg c e11)
        (neg_reg j e10) (neg_reg c e9) (neg_reg i e12) (neg_reg j e8) (neg_reg i e6)
        (neg_reg j e5) (neg_reg i e4) (neg_reg c e7))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
    change (-S.cross j i _ _ _ _) ▷ S.E c (neg_reg c e1) ≫
        ((α_ (S.E j (neg_reg j e5)) (S.E i (neg_reg i e4)) (S.E c (neg_reg c e1))).hom ≫
          S.E j (neg_reg j e5) ◁ (-S.cross c i _ _ _ _) ≫
          (α_ (S.E j (neg_reg j e5)) (S.E c (neg_reg c e7)) (S.E i (neg_reg i e6))).inv) ≫
        (-S.cross c j _ _ _ _) ▷ S.E i (neg_reg i e6) =
      ((α_ (S.E i (neg_reg i e3)) (S.E j (neg_reg j e2)) (S.E c (neg_reg c e1))).hom ≫
          S.E i (neg_reg i e3) ◁ (-S.cross c j _ _ _ _) ≫
          (α_ (S.E i (neg_reg i e3)) (S.E c (neg_reg c e11)) (S.E j (neg_reg j e10))).inv) ≫
        (-S.cross c i _ _ _ _) ▷ S.E j (neg_reg j e10) ≫
        ((α_ (S.E c (neg_reg c e9)) (S.E i (neg_reg i e12)) (S.E j (neg_reg j e10))).hom ≫
          S.E c (neg_reg c e9) ◁ (-S.cross j i _ _ _ _) ≫
          (α_ (S.E c (neg_reg c e9)) (S.E j (neg_reg j e8)) (S.E i (neg_reg i e6))).inv)
    simp only [AdditiveWhiskering.neg_whiskerRight, AdditiveWhiskering.whiskerLeft_neg,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, neg_inj, Category.assoc]
    exact h.symm
  braidQ := by
    intro i j hij a b c d e f h₁ h₂ h₃ h₄ h₅ h₆ h₇
    have hq := congrArg (endConj k (α_ (S.E i (neg_reg i h₃)) (S.E j (neg_reg j h₂))
        (S.E i (neg_reg i h₁))).symm)
      (H.braidQ i j hij (neg_reg i h₃) (neg_reg j h₂) (neg_reg i h₁) (neg_reg i h₇)
        (neg_reg j h₆) (neg_reg j h₅) (neg_reg i h₄))
    rw [← KLR.qbar_rename_rev, ← KL3.Diagram.ncEval_rename_of_commute _ (by
        intro x y
        fin_cases x <;> fin_cases y <;>
          first
          | exact Commute.refl _
          | exact whisker_exchange _ _
          | exact (whisker_exchange _ _).symm
          | exact commute_whiskerLeft_exchange _ _
          | exact (commute_whiskerLeft_exchange _ _).symm),
      KLR.ncEval_map] at hq
    change ((-S.cross j i _ _ _ _) ▷ S.E i (neg_reg i h₁) ≫
        ((α_ (S.E j (neg_reg j h₅)) (S.E i (neg_reg i h₄)) (S.E i (neg_reg i h₁))).hom ≫
          S.E j (neg_reg j h₅) ◁ (-S.cross i i _ _ _ _) ≫
          (α_ (S.E j (neg_reg j h₅)) (S.E i (neg_reg i h₄)) (S.E i (neg_reg i h₁))).inv) ≫
        (-S.cross i j _ _ _ _) ▷ S.E i (neg_reg i h₁)) -
      (((α_ (S.E i (neg_reg i h₃)) (S.E j (neg_reg j h₂)) (S.E i (neg_reg i h₁))).hom ≫
          S.E i (neg_reg i h₃) ◁ (-S.cross i j _ _ _ _) ≫
          (α_ (S.E i (neg_reg i h₃)) (S.E i (neg_reg i h₇)) (S.E j (neg_reg j h₆))).inv) ≫
        (-S.cross i i _ _ _ _) ▷ S.E j (neg_reg j h₆) ≫
        ((α_ (S.E i (neg_reg i h₃)) (S.E i (neg_reg i h₇)) (S.E j (neg_reg j h₆))).hom ≫
          S.E i (neg_reg i h₃) ◁ (-S.cross j i _ _ _ _) ≫
          (α_ (S.E i (neg_reg i h₃)) (S.E j (neg_reg j h₂)) (S.E i (neg_reg i h₁))).inv)) =
      KLR.ncEval (A := End ((S.E i (neg_reg i h₃) ≫ S.E j (neg_reg j h₂)) ≫
          S.E i (neg_reg i h₁)))
        ![(S.dot i (neg_reg i h₃) ▷ S.E j (neg_reg j h₂)) ▷ S.E i (neg_reg i h₁),
          (S.E i (neg_reg i h₃) ◁ S.dot j (neg_reg j h₂)) ▷ S.E i (neg_reg i h₁),
          (S.E i (neg_reg i h₃) ≫ S.E j (neg_reg j h₂)) ◁ S.dot i (neg_reg i h₁)]
        (KLR.qbar (Q i j))
    convert hq using 2
    · rw [map_sub, endConj_apply, endConj_apply]
      simp only [AdditiveWhiskering.neg_whiskerRight, AdditiveWhiskering.whiskerLeft_neg,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc,
        Iso.symm_hom, Iso.symm_inv, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      exact neg_sub_neg _ _
    · funext x
      fin_cases x <;> simp [endConj_apply]

end UpKLR

/-! ## Brundan's mixed inversion for the reverse -/

section Mixed

variable {k : Type w'} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

/-- **Brundan's mixed inversion (1.7) for the reverse.** The mixed mate of the reverse is minus
the inverse of a mixed mate of `S`, scaled by Brundan's unit `t_ij` (`RouqFamily.mixed_mate`). -/
theorem reverse_mixedInversion (Sc : KL3.Diagram.CL.CLScalars C k) (H : BrundanUpKLR S Sc)
    (M : BrundanMixedInversion S) : BrundanMixedInversion S.reverse := by
  intro i j hij a b c d hj hi' hi hj'
  have := M i j hij (neg_reg j hj') (neg_reg i hi) (neg_reg i hi') (neg_reg j hj)
  have hm := S.mixed_mate Sc H i j hij (neg_reg i hi') (neg_reg j hj) (neg_reg j hj')
    (neg_reg i hi)
  have hσ : S.reverse.mixedSigma i j hj hi' hi hj' =
      -((Sc.t i j : k) • inv (S.mixedSigma i j (neg_reg j hj') (neg_reg i hi) (neg_reg i hi')
        (neg_reg j hj))) := by
    change mateEquiv (HOp.adjunction (S.adjL i (neg_reg i hi)))
      (HOp.adjunction (S.adjL i (neg_reg i hi')))
      (-S.cross j i (neg_reg i hi') (neg_reg j hj) (neg_reg j hj') (neg_reg i hi)) = _
    rw [HOp.mateEquiv_reflect, Equiv.symm_apply_eq, ← hm]
    simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
      Adjunction.homEquiv₂_apply, AdditiveWhiskering.whiskerLeft_neg,
      AdditiveWhiskering.neg_whiskerRight, Preadditive.neg_comp, Preadditive.comp_neg]
  have hinv : IsIso (-((Sc.t i j : k) • inv (S.mixedSigma i j (neg_reg j hj') (neg_reg i hi)
      (neg_reg i hi') (neg_reg j hj)))) :=
    ⟨⟨-(((Sc.t i j)⁻¹ : kˣ) : k) • S.mixedSigma i j (neg_reg j hj') (neg_reg i hi)
      (neg_reg i hi') (neg_reg j hj), by simp [smul_smul], by simp [smul_smul]⟩⟩
  rw [hσ]
  exact hinv

end Mixed

end RouqFamily

end Categorification.TwoRep
