/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KrullSchmidtCat

/-!
# Summands of an idempotent which is local modulo an ideal

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4
(TeX `\subsubsection{Idempotents in $\UcatD$}`), (3.102)–(3.106):

> We can decompose `e_{r,r'} = ∑_{r''} e_{r,r',r''}` into a sum of minimal mutually-orthogonal
> degree zero idempotents […] for each `(r, r')` at most one of `β(e_{r,r',r''}) ≠ 0` […]
> If `β(e_{r,r',r''}) = 0` then `e_{r,r',r''} ∈ I_{ν,-ν',λ}` […] and the 1-morphism
> `(E_{ν,-ν'} 1_λ, e_{r,r',r''})` of `U̇` is isomorphic to a direct summand of
> `⨁_s E_{i(s)} 1_λ {t_s}`.

This file proves the category-theoretic core of this step, in a Hom-finite, idempotent complete
`k`-linear category `𝒞` with binary biproducts. Fix an object `W`, a two-sided ideal `T` of
`End W` (in the application: the endomorphisms factoring through shorter sequences) and a class
`Low` of objects containing every indecomposable retract `Q` of `W` whose idempotent `g ≫ f`
lies in `T`. Let `ε` be an idempotent of `W` which is **local modulo `T`** (`LocalModT`): every
`y ∈ ε (End W) ε` is nilpotent modulo `T` or invertible in `ε (End W) ε` modulo `T`. If an
indecomposable `Z ∉ Low` is a direct summand of the image `E` of `ε`, then the complement of `Z`
in `E` has only `Low` indecomposable summands:

* `of_sub_mem_closure_low`: `[E] - [Z]` is a sum of classes of indecomposables in `Low`.

Auxiliary: `of_mem_closure_indec_retract` refines the existence of Krull–Schmidt decompositions
(`of_mem_closure_indec`) by recording that the indecomposables are retracts of the object.
-/

noncomputable section

namespace Categorification.KrullSchmidtCat

open CategoryTheory CategoryTheory.Limits Module

universe v u

variable {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞]

/-! ## Decompositions into indecomposable retracts -/

section Retracts

variable (k : Type*) [Field k] [Linear k 𝒞] [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]
  [IsIdempotentComplete 𝒞]

/-- `Q` is a retract (direct summand) of `X`. -/
def IsRetract (Q X : 𝒞) : Prop := ∃ (f : Q ⟶ X) (g : X ⟶ Q), f ≫ g = 𝟙 Q

omit [Preadditive 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem IsRetract.trans {Q X Y : 𝒞} (h₁ : IsRetract Q X) (h₂ : IsRetract X Y) : IsRetract Q Y := by
  obtain ⟨f, g, hfg⟩ := h₁
  obtain ⟨f', g', hfg'⟩ := h₂
  exact ⟨f ≫ f', g' ≫ g, by rw [Category.assoc, ← Category.assoc f' g', hfg', Category.id_comp, hfg]⟩

omit [Preadditive 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem IsRetract.refl (Q : 𝒞) : IsRetract Q Q := ⟨𝟙 Q, 𝟙 Q, Category.id_comp _⟩

include k in
/-- **Krull–Schmidt decompositions into retracts**: the class of `X` is a sum of classes of
indecomposable retracts of `X`. -/
theorem of_mem_closure_indec_retract (X : 𝒞) :
    SplitK0.of X ∈ AddSubmonoid.closure
      {x | ∃ Z : 𝒞, IsIndec Z ∧ IsRetract Z X ∧ x = SplitK0.of Z} := by
  induction h : finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases h0 : IsZero X
    · rw [SplitK0.of_isZero h0]; exact AddSubmonoid.zero_mem _
    by_cases hi : IsIndec X
    · exact AddSubmonoid.subset_closure ⟨X, hi, IsRetract.refl X, rfl⟩
    obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
      by_contra hne
      push_neg at hne
      exact hi ⟨h0, fun e he => by
        by_cases h' : e = 0
        · exact Or.inl h'
        · exact Or.inr (hne e he h')⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
    have hY : ¬ IsZero Y := fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
    have hZ : ¬ IsZero Z := fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)
    rw [SplitK0.of_eq_add_of_iso (isoOfData i p i' p' h₁ h₂ h₃ h₄
      (by rw [h₅, h₆, add_sub_cancel]))]
    have hmono : ∀ (V : 𝒞), IsRetract V X →
        AddSubmonoid.closure {x | ∃ Z : 𝒞, IsIndec Z ∧ IsRetract Z V ∧ x = SplitK0.of Z} ≤
          AddSubmonoid.closure {x | ∃ Z : 𝒞, IsIndec Z ∧ IsRetract Z X ∧ x = SplitK0.of Z} :=
      fun V hV => AddSubmonoid.closure_mono fun _ ⟨Q, hQ, hQV, hx⟩ => ⟨Q, hQ, hQV.trans hV, hx⟩
    refine AddSubmonoid.add_mem _ (hmono Y ⟨i, p, h₁⟩ (ih _ ?_ Y rfl))
      (hmono Z ⟨i', p', h₂⟩ (ih _ ?_ Z rfl))
    · rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ
    · rw [← h]; exact finrank_end_lt k i' p' i p h₂ h₁ h₄ h₃ hY

end Retracts

/-! ## Idempotents local modulo an ideal -/

section LocalModT

variable {k : Type*} [Field k] [Linear k 𝒞]

/-- A submodule `T` of `End W` is a **two-sided ideal** (for composition). -/
structure IsIdealEnd {W : 𝒞} (T : Submodule k (W ⟶ W)) : Prop where
  comp_left : ∀ (x t : W ⟶ W), t ∈ T → x ≫ t ∈ T
  comp_right : ∀ (t x : W ⟶ W), t ∈ T → t ≫ x ∈ T

/-- The `n`-th power `y ≫ ⋯ ≫ y` of an endomorphism. -/
def compPow {W : 𝒞} (y : W ⟶ W) : ℕ → (W ⟶ W)
  | 0 => 𝟙 W
  | n + 1 => compPow y n ≫ y

/-- An idempotent `ε` of `W` is **local modulo `T`**: every `y ∈ ε (End W) ε` is nilpotent
modulo `T`, or invertible in `ε (End W) ε` modulo `T`. -/
def LocalModT {W : 𝒞} (T : Submodule k (W ⟶ W)) (ε : W ⟶ W) : Prop :=
  ∀ y : W ⟶ W, ε ≫ y ≫ ε = y →
    (∃ N : ℕ, compPow y (N + 1) ∈ T) ∨
      ∃ z : W ⟶ W, ε ≫ z ≫ ε = z ∧ y ≫ z - ε ∈ T ∧ z ≫ y - ε ∈ T

theorem IsIdealEnd.idem_pow_mem {W : 𝒞} {T : Submodule k (W ⟶ W)} (_ : IsIdealEnd T) {P : W ⟶ W} (hP : P ≫ P = P)
    (N : ℕ) (h : compPow P (N + 1) ∈ T) : P ∈ T := by
  have : ∀ n : ℕ, compPow P (n + 1) = P := by
    intro n
    induction n with
    | zero => simp [compPow]
    | succ n ih => rw [compPow, ih, hP]
  rwa [this] at h

variable [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞]

/-- **The complement of a non-low indecomposable summand of a local-mod-`T` idempotent is low**
(KL III §3.8.4, (3.102)–(3.106)). Let `T` be a two-sided ideal of `End W`, `Low` a class of objects
containing every indecomposable `Q` with a retraction `f : Q ⟶ W`, `g : W ⟶ Q` such that
`g ≫ f ∈ T`, `ε` an idempotent of `W` which is local modulo `T`, with image `E` (`i ≫ p = 𝟙 E`,
`p ≫ i = ε`). If an indecomposable `Z ∉ Low` is a retract of `E`, then `[E] - [Z]` is a sum of
classes of indecomposables in `Low`. -/
theorem of_sub_mem_closure_low [HomFinite k 𝒞] {W : 𝒞} {T : Submodule k (W ⟶ W)}
    (hT : IsIdealEnd T) (Low : 𝒞 → Prop)
    (hLow : ∀ (Q : 𝒞) (f : Q ⟶ W) (g : W ⟶ Q), f ≫ g = 𝟙 Q → g ≫ f ∈ T → IsIndec Q → Low Q)
    {ε : W ⟶ W} (hloc : LocalModT T ε) {E : 𝒞} (i : E ⟶ W) (p : W ⟶ E) (hip : i ≫ p = 𝟙 E)
    (hpi : p ≫ i = ε) {Z : 𝒞} (hZ : IsIndec Z) (f : Z ⟶ E) (g : E ⟶ Z) (hfg : f ≫ g = 𝟙 Z)
    (hZlow : ¬ Low Z) :
    SplitK0.of E - SplitK0.of Z ∈ AddSubmonoid.closure
      {x | ∃ Q : 𝒞, IsIndec Q ∧ Low Q ∧ x = SplitK0.of Q} := by
  -- the idempotent of `Z` on `W`, and its complement in `ε`
  set P : W ⟶ W := p ≫ g ≫ f ≫ i with hPdef
  have hεε : ε ≫ ε = ε := by rw [← hpi, Category.assoc, ← Category.assoc i, hip, Category.id_comp]
  have hPP : P ≫ P = P := by
    simp only [hPdef, Category.assoc]
    rw [← Category.assoc i p, hip, Category.id_comp, ← Category.assoc f g, hfg, Category.id_comp]
  have hεP : ε ≫ P = P := by
    rw [← hpi, hPdef, Category.assoc, ← Category.assoc i p, hip, Category.id_comp]
  have hPε : P ≫ ε = P := by
    rw [← hpi, hPdef]; simp only [Category.assoc]; rw [← Category.assoc i p, hip, Category.id_comp]
  -- `P ∉ T`, since `Z` is not low
  have hPT : P ∉ T := by
    intro hP
    refine hZlow (hLow Z (f ≫ i) (p ≫ g) ?_ (by simpa [hPdef, Category.assoc] using hP) hZ)
    rw [Category.assoc, ← Category.assoc i p, hip, Category.id_comp, hfg]
  -- hence `P` is invertible in `ε (End W) ε` modulo `T`
  obtain ⟨z, hz, hPz, -⟩ : ∃ z : W ⟶ W, ε ≫ z ≫ ε = z ∧ P ≫ z - ε ∈ T ∧ z ≫ P - ε ∈ T := by
    rcases hloc P (by rw [← Category.assoc, hεP, hPε]) with ⟨N, hN⟩ | h
    · exact absurd (hT.idem_pow_mem hPP N hN) hPT
    · exact h
  -- the complement `Q = ε - P` lies in `T`
  set Q : W ⟶ W := ε - P with hQdef
  have hQP : Q ≫ P = 0 := by rw [hQdef, Preadditive.sub_comp, hεP, hPP, sub_self]
  have hQT : Q ∈ T := by
    have hQε : Q ≫ ε = Q := by rw [hQdef, Preadditive.sub_comp, hεε, hPε]
    have e : Q = -(Q ≫ (P ≫ z - ε)) := by
      rw [Preadditive.comp_sub, ← Category.assoc, hQP, Limits.zero_comp, zero_sub, neg_neg, hQε]
    rw [e]
    exact T.neg_mem (hT.comp_left _ _ hPz)
  -- split `E = Z ⊕ Y`
  have hgf : (g ≫ f) ≫ (g ≫ f) = g ≫ f := by
    rw [Category.assoc, ← Category.assoc f g, hfg, Category.id_comp]
  obtain ⟨Z', Y, j, q, j', q', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split (g ≫ f) hgf
  have hZ' : Nonempty (Z' ≅ Z) := ⟨{
    hom := j ≫ g
    inv := f ≫ q
    hom_inv_id := by
      have : j ≫ g ≫ f ≫ q = (j ≫ q) ≫ (j ≫ q) := by
        rw [Category.assoc, ← Category.assoc q j, h₅]; simp only [Category.assoc]
      rw [Category.assoc, this, h₁, Category.id_comp]
    inv_hom_id := by
      have : f ≫ q ≫ j ≫ g = (f ≫ g) ≫ (f ≫ g) := by
        rw [← Category.assoc q j, h₅]; simp only [Category.assoc]
      rw [Category.assoc, this, hfg, Category.id_comp] }⟩
  rw [SplitK0.of_eq_add_of_iso (isoOfData j q j' q' h₁ h₂ h₃ h₄ (by rw [h₅, h₆, add_sub_cancel])),
    SplitK0.of_iso hZ'.some, add_sub_cancel_left]
  -- every indecomposable retract of `Y` is low
  have hq' : (g ≫ f) ≫ q' = 0 := by
    have e1 : q' = (𝟙 E - g ≫ f) ≫ q' := by
      rw [← h₆, Category.assoc, h₂, Category.comp_id]
    rw [e1, ← Category.assoc, Preadditive.comp_sub, Category.comp_id, hgf, sub_self,
      Limits.zero_comp]
  have hpq : p ≫ q' = Q ≫ p ≫ q' := by
    rw [hQdef, Preadditive.sub_comp, ← hpi, Category.assoc, ← Category.assoc i p, hip,
      Category.id_comp, hPdef]
    simp only [Category.assoc]
    rw [← Category.assoc i p, hip, Category.id_comp, ← Category.assoc g f, hq',
      Limits.comp_zero, sub_zero]
  refine AddSubmonoid.closure_mono ?_ (of_mem_closure_indec_retract k Y)
  rintro _ ⟨Q', hQ', ⟨fQ, gQ, hQ⟩, rfl⟩
  refine ⟨Q', hQ', hLow Q' (fQ ≫ j' ≫ i) (p ≫ q' ≫ gQ) ?_ ?_ hQ', rfl⟩
  · simp only [Category.assoc]
    rw [← Category.assoc i p, hip, Category.id_comp, ← Category.assoc j' q', h₂,
      Category.id_comp, hQ]
  · have e2 : (p ≫ q' ≫ gQ) ≫ fQ ≫ j' ≫ i = Q ≫ (p ≫ q' ≫ gQ ≫ fQ ≫ j' ≫ i) := by
      rw [← Category.assoc p q', hpq]; simp only [Category.assoc]
    rw [e2]
    exact hT.comp_right _ _ hQT

end LocalModT

end Categorification.KrullSchmidtCat
