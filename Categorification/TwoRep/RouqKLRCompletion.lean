/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqKLRAction
import Categorification.KLR.Unfurling.Truncation

/-!
# The completed KLR algebra acting on words with nilpotent dots

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §3.2: if the
dots act nilpotently in a categorical action, the graded completion `R̂(ν)` acts. For a
Rouquier family `S` with the mixed upward KLR equations (`klrAct`) whose dots are nilpotent,
this file extends the action of `R(ν)` on the words of weight `ν` at `μ` to the completion
(`klrComplAt`, by `GradingDatum.completionLift`), and computes it on the elements
`F(x) e_t` of the completion: a polynomial `p` acts on the word of `t` as `p` evaluated at the
dots of the word, and the inverse series `F⁻¹` of a polynomial `F` with invertible constant
term acts as the inverse (`Ring.inverse`) of `F` evaluated at the dots.

The words are taken with an arbitrary target weight `x'` equal to `μ + Σ ν` (`wordCellAt`),
so that the action can be compared with words whose weights are given in another form.

## Main definitions and results

* `MatEnd.congrAlg`: the algebra isomorphism of matrix algebras along an equality of families.
* `RouqFamily.klrActAt`: the action of `R(ν)` on the words with target weight `x'`;
  `klrActAt_e`, `klrActAt_pol_mul_e`, `klrActAt_cross`.
* `RouqFamily.klrComplAt`: its extension to the completion `R̂(ν)`, for nilpotent dots;
  `klrComplAt_toCompletion`, `klrComplAt_seriesAt_coe`, `klrComplAt_seriesAt_invOfUnit`.
-/

noncomputable section

namespace Categorification.KLR.Diagram.MatEnd

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Linear

variable (k : Type*) [CommRing k] [Linear k C]

/-- The isomorphism of matrix algebras along an equality of families. -/
def congrAlg {X X' : ι → C} (h : X = X') : MatEnd X ≃ₐ[k] MatEnd X' := by
  subst h; exact AlgEquiv.refl

variable {k}

theorem congrAlg_apply {X X' : ι → C} (h : X = X') (f : MatEnd X) (i j : ι) :
    congrAlg k h f i j =
      eqToHom (congrFun h i).symm ≫ f i j ≫ eqToHom (congrFun h j) := by
  subst h; simp [congrAlg]

theorem congrAlg_single {X X' : ι → C} (h : X = X') (i j : ι) (f : X i ⟶ X j) :
    congrAlg k h (single i j f) =
      single i j (eqToHom (congrFun h i).symm ≫ f ≫ eqToHom (congrFun h j)) := by
  subst h; simp [congrAlg]

end Linear

omit [Fintype ι] in
theorem single_injective {X : ι → C} (i j : ι) {f g : X i ⟶ X j}
    (h : single i j f = single i j g) : f = g := by
  simpa using congrFun (congrFun h i) j

/-- The corner of a matrix at `(i, i)`. -/
theorem single_one_mul_mul_single_one {X : ι → C} (i : ι) (f : MatEnd X) :
    single i i (𝟙 (X i)) * f * single i i (𝟙 (X i)) = single i i (f i i) := by
  conv_lhs => rw [eq_sum_single f]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single i]
  · rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [single_mul_single, single_mul_single, Category.id_comp, Category.comp_id]
    · intro b _ hb; rw [single_mul_single_of_ne _ _ hb, zero_mul]
    · simp
  · intro a _ ha
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = i
    · subst hb; rw [single_mul_single, single_mul_single_of_ne _ _ (Ne.symm ha)]
    · rw [single_mul_single_of_ne _ _ hb, zero_mul]
  · simp

/-- Matrix units on the diagonal multiply as the endomorphisms (in reversed order). -/
theorem single_mul_single_self {X : ι → C} (i : ι) (f g : X i ⟶ X i) :
    single i i f * single i i g = single i i (g ≫ f) :=
  single_mul_single _ _ _ _ _

end Categorification.KLR.Diagram.MatEnd

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KLR TypeA

universe w v u u₁

/-- A two-sided inverse is the ring inverse. -/
theorem Ring.inverse_eq_of_mul {M₀ : Type*} [MonoidWithZero M₀] {x y : M₀} (h₁ : x * y = 1)
    (h₂ : y * x = 1) : Ring.inverse x = y :=
  Ring.inverse_unit ⟨x, y, h₁, h₂⟩

/-- Monoid-with-zero homomorphisms preserve the ring inverse of a unit. -/
theorem Ring.map_inverse {M₀ N₀ : Type*} [MonoidWithZero M₀] [MonoidWithZero N₀]
    {F : Type*} [FunLike F M₀ N₀] [MonoidHomClass F M₀ N₀] (f : F) {x : M₀}
    (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  refine (Ring.inverse_eq_of_mul ?_ ?_).symm
  · rw [← map_mul, Ring.mul_inverse_cancel x hx, map_one]
  · rw [← map_mul, Ring.inverse_mul_cancel x hx, map_one]

section Completion

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y}

namespace RouqFamily

open Diagram MatEnd

variable {S : RouqFamily (B := B) RD} {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
  (μ : X) {ν : Multiset I} (x' : X) (e : wtop RD μ ν = x')

local notation "m" => Multiset.card ν

variable (S) in
/-- The word of `t` with target weight `x' = μ + Σ ν`. -/
abbrev wordCellAt (t : Seq ν) : S.obj μ ⟶ S.obj x' :=
  S.wcell μ (wordL RD μ t) x' (wValid_of_eq (wValid_wordL μ t) e)

variable (S) in
/-- The dot on the `a`-th strand of the word of `t`, with target weight `x'`. -/
def wordDotAt (t : Seq ν) (a : Fin m) : End (S.wordCellAt μ x' e t) :=
  S.wdot μ a (wordL RD μ t) x' (wValid_of_eq (wValid_wordL μ t) e)

variable (S) in
/-- The crossing of the strands `j`, `j + 1` of the word of `t`, with target weight `x'`. -/
def wordCrossAt (t : Seq ν) (j : ℕ) :
    S.wordCellAt μ x' e t ⟶ S.wordCellAt μ x' e (sadj m j • t) :=
  if hj : j + 1 < m then
    S.wcrossTo μ j _ _ _ (wswap_wordL μ t hj) (wValid_of_eq (wValid_wordL μ t) e)
      (wValid_of_eq (wValid_wordL μ _) e)
  else 0

/-- The action of `R(ν)` on the words of weight `ν` at `μ`, with target weight `x'`. -/
def klrActAt : KLRAlgebra k Q ν →ₐ[k] MatEnd (fun t : Seq ν => S.wordCellAt μ x' e t) := by
  subst e; exact klrAct H μ

theorem klrActAt_e (t : Seq ν) :
    klrActAt H μ x' e (KLRAlgebra.e t) = single t t (𝟙 _) := by
  subst e; exact klrAct_e H t

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B] [DecidableEq I] in
theorem wordDotAt_rfl (t : Seq ν) (a : Fin m) :
    S.wordDotAt μ (wtop RD μ ν) rfl t a = S.wordDot μ t a := rfl

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B] [DecidableEq I] in
theorem wordCrossAt_rfl (t : Seq ν) (j : ℕ) :
    S.wordCrossAt μ (wtop RD μ ν) rfl t j = S.wordCross μ t j := rfl

theorem klrActAt_pol_mul_e (p : MvPolynomial (Fin m) k) (t : Seq ν) :
    klrActAt H μ x' e (KLRAlgebra.pol p * KLRAlgebra.e t) =
      single t t (ncEval (A := End (S.wordCellAt μ x' e t))
        (fun a => S.wordDotAt μ x' e t a) p) := by
  subst e
  change klrAct H μ _ = _
  have hp : (KLRAlgebra.pol p : KLRAlgebra k Q ν) = ncEval (fun a => KLRAlgebra.x (id a)) p := by
    rw [KLRAlgebra.ncEval_eq_pol id, MvPolynomial.rename_id_apply]
  rw [map_mul, klrAct_e, hp, AlgHom.map_ncEval]
  simp only [klrAct_dot]
  exact (single_ncEval (S := S) (μ := μ) t id p).symm

theorem klrActAt_cross (j : ℕ) :
    klrActAt H μ x' e (KLRAlgebra.ψ j : KLRAlgebra k Q ν) =
      ∑ t, single t (sadj m j • t) (S.wordCrossAt μ x' e t j) := by
  subst e; exact klrAct_cross H j

omit [DecidableEq I] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- A dot on a weighted word is nilpotent if the dots of `S` are. -/
theorem wdot_nilpotent
    (hnil : ∀ (c : I) {x y : X} (h : x + RD.iX c = y), IsNilpotent (End.of (S.dot c h))) :
    ∀ (a : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
      IsNilpotent (End.of (S.wdot μ a L μ' h))
  | 0, (c, ν) :: L, _, h => by
    obtain ⟨N, hN⟩ := hnil c h.2
    refine ⟨N, ?_⟩
    change End.of (S.wcell μ L ν h.1 ◁ S.dot c h.2) ^ N = 0
    rw [whiskerLeft_pow]
    erw [hN]
    exact AdditiveWhiskering.whiskerLeft_zero _ _ _
  | a + 1, (c, ν) :: L, _, h => by
    obtain ⟨N, hN⟩ := wdot_nilpotent hnil a L ν h.1
    refine ⟨N, ?_⟩
    change End.of (S.wdot μ a L ν h.1 ▷ S.E c h.2) ^ N = 0
    rw [whiskerRight_pow]
    erw [hN]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _
  | 0, [], _, _ => ⟨1, by simp; rfl⟩
  | _ + 1, [], _, _ => ⟨1, by simp; rfl⟩

variable (hnil : ∀ (c : I) {x y : X} (h : x + RD.iX c = y), IsNilpotent (End.of (S.dot c h)))
include hnil

theorem exists_klrActAt_pol_X_pow :
    ∃ M : ℕ, ∀ a : Fin m, klrActAt H μ x' e (KLRAlgebra.pol (MvPolynomial.X a ^ M)) = 0 := by
  classical
  subst e
  choose N hN using fun (p : Seq ν × Fin m) =>
    wdot_nilpotent (S := S) μ hnil p.2 (wordL RD μ p.1) (wtop RD μ ν) (wValid_wordL μ p.1)
  refine ⟨Finset.univ.sup N, fun a => ?_⟩
  change klrAct H μ _ = 0
  have hsum : (KLRAlgebra.pol (MvPolynomial.X a ^ Finset.univ.sup N) : KLRAlgebra k Q ν) =
      ∑ t, KLRAlgebra.pol (MvPolynomial.X a ^ Finset.univ.sup N) * KLRAlgebra.e t := by
    rw [← Finset.mul_sum, KLRAlgebra.sum_e, mul_one]
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [map_mul, map_pow, KLRAlgebra.pol_X, map_pow, klrAct_dot, klrAct_e, wordX_pow_mul_wordE]
  have hle : N (t, a) ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ (t, a))
  have hz : S.wordDot μ t a ^ Finset.univ.sup N = 0 := pow_eq_zero_of_le hle (hN (t, a))
  rw [hz, single_zero]

variable (G : GradingDatum Q)

/-- **The completed KLR algebra acting on words**: the extension of `klrActAt` to the
completion `R̂(ν)` (Webster, arXiv:1603.06311v3, §3.2), for nilpotent dots. -/
def klrComplAt : G.completion ν →ₐ[k] MatEnd (fun t : Seq ν => S.wordCellAt μ x' e t) :=
  G.completionLift (klrActAt H μ x' e)
    (Classical.choose_spec (exists_klrActAt_pol_X_pow H μ x' e hnil))

theorem klrComplAt_toCompletion (a : KLRAlgebra k Q ν) :
    klrComplAt H μ x' e hnil G (G.toCompletion a) = klrActAt H μ x' e a :=
  G.completionLift_toCompletion _ _ a

variable {G} (hX : ∀ a, 0 < G.degX a)

/-- A polynomial `p` in the dots acts on the word of `t` by `p` evaluated at its dots. -/
theorem klrComplAt_seriesAt_coe (t : Seq ν) (p : MvPolynomial (Fin m) k) :
    klrComplAt H μ x' e hnil G (G.seriesAt hX t (↑p : MvPowerSeries (Fin m) k)) =
      single t t (ncEval (A := End (S.wordCellAt μ x' e t))
        (fun a => S.wordDotAt μ x' e t a) p) := by
  rw [G.seriesAt_coe hX, klrComplAt_toCompletion, klrActAt_pol_mul_e]

/-- The image of an element of the corner `e_t R̂(ν) e_t` is supported at `(t, t)`. -/
theorem klrComplAt_seriesAt (t : Seq ν) (F : MvPowerSeries (Fin m) k) :
    klrComplAt H μ x' e hnil G (G.seriesAt hX t F) =
      single t t (klrComplAt H μ x' e hnil G (G.seriesAt hX t F) t t) := by
  have h : G.seriesAt hX t F =
      G.toCompletion (KLRAlgebra.e t) * G.seriesAt hX t F * G.toCompletion (KLRAlgebra.e t) := by
    rw [G.toCompletion_e_mul_seriesAt hX, ite_eq_left rfl, G.seriesAt_mul_toCompletion_e hX,
      ite_eq_left rfl]
  conv_lhs => rw [h, map_mul, map_mul, klrComplAt_toCompletion, klrActAt_e]
  rw [single_one_mul_mul_single_one]

/-- If the constant term of the polynomial `p` is a unit `u`, then `p` evaluated at the dots of
the word of `t` is invertible, and the inverse series `p⁻¹(x) e_t` acts by its inverse. -/
theorem klrComplAt_seriesAt_invOfUnit (t : Seq ν) (p : MvPolynomial (Fin m) k) (u : kˣ)
    (hu : MvPowerSeries.constantCoeff (↑p : MvPowerSeries (Fin m) k) = u) :
    IsUnit (ncEval (A := End (S.wordCellAt μ x' e t)) (fun a => S.wordDotAt μ x' e t a) p) ∧
      klrComplAt H μ x' e hnil G
          (G.seriesAt hX t ((↑p : MvPowerSeries (Fin m) k).invOfUnit u)) =
        single t t (Ring.inverse (M₀ := End (S.wordCellAt μ x' e t))
          (ncEval (A := End (S.wordCellAt μ x' e t)) (fun a => S.wordDotAt μ x' e t a) p)) := by
  set P := ncEval (A := End (S.wordCellAt μ x' e t)) (fun a => S.wordDotAt μ x' e t a) p
  set y := klrComplAt H μ x' e hnil G
    (G.seriesAt hX t ((↑p : MvPowerSeries (Fin m) k).invOfUnit u))
  have h₁ := congrArg (klrComplAt H μ x' e hnil G)
    (G.seriesAt_mul_seriesAt_invOfUnit hX t _ u hu)
  have h₂ := congrArg (klrComplAt H μ x' e hnil G)
    (G.seriesAt_invOfUnit_mul_seriesAt hX t _ u hu)
  rw [map_mul, klrComplAt_toCompletion, klrActAt_e, klrComplAt_seriesAt_coe] at h₁ h₂
  have hy : y = single t t (y t t) := klrComplAt_seriesAt H μ x' e hnil hX t _
  change single t t P * y = _ at h₁
  change y * single t t P = _ at h₂
  rw [hy, single_mul_single_self] at h₁ h₂
  set Y : End (S.wordCellAt μ x' e t) := y t t
  have e₁ : P * Y = 1 := single_injective t t h₁
  have e₂ : Y * P = 1 := single_injective t t h₂
  exact ⟨⟨⟨P, y t t, e₁, e₂⟩, rfl⟩, by rw [hy, Ring.inverse_eq_of_mul e₁ e₂]⟩

end RouqFamily

end Completion

end Categorification.TwoRep
