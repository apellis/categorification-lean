/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownContext
import Categorification.Diagrams.KL3.SlideCalculus
import Categorification.KLR.BaseChange

/-!
# Downward KLR relations between two red strands

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward translation kills red
dots and crossings of two red strands. Hence the KLR relations in which two red strands of
different colours cross translate to zero, provided the polynomial of the two red colours has
no constant term (`downLinear_relation_sqNe_red`, `downLinear_relation_slideLNe_red`,
`downLinear_relation_slideRNe_red`, `downLinear_relation_braid_red₁₂`,
`downLinear_relation_braid_red₁₃`, `downLinear_relation_braid_red₂₃`).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR.Diagram

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (k : Type w) [CommRing k] (μ : X) (u v : List (DoubleStrand I ℓ))

/-- A layer whose generator has no downward translation translates to zero. -/
theorem downLinear_dl_of_none (l : List (I ⊕ Fin ℓ)) (g : KLR.Diagram.Gen (I ⊕ Fin ℓ))
    (r : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (ha : l ++ g.dom ++ r = a.word) (hb : l ++ g.cod ++ r = b.word) (hg : downMove g = none) :
    downLinear RD Λ k μ u v (LinDiagram.of (dl l g r ha hb)) = 0 := by
  rw [dl, downLinear_layer, downLinearLayer_of_none RD Λ k μ u v _ hg, LinDiagram.cast_eq_comp]
  simp

theorem downLinear_dl_red_dot (l : List (I ⊕ Fin ℓ)) (s : Fin ℓ)
    (r : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (ha : l ++ (Gen.dot (.inr s)).dom ++ r = a.word)
    (hb : l ++ (Gen.dot (.inr s)).cod ++ r = b.word) :
    downLinear RD Λ k μ u v (LinDiagram.of (dl l (.dot (.inr s)) r ha hb)) = 0 :=
  downLinear_dl_of_none RD Λ k μ u v _ _ _ ha hb rfl

theorem downLinear_dl_red_cross (l : List (I ⊕ Fin ℓ)) (s t : Fin ℓ)
    (r : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (ha : l ++ (Gen.cross (.inr s) (.inr t)).dom ++ r = a.word)
    (hb : l ++ (Gen.cross (.inr s) (.inr t)).cod ++ r = b.word) :
    downLinear RD Λ k μ u v (LinDiagram.of (dl l (.cross (.inr s) (.inr t)) r ha hb)) = 0 :=
  downLinear_dl_of_none RD Λ k μ u v _ _ _ ha hb rfl

omit [AddCommGroup X] in
/-- Evaluating a polynomial at zero gives its constant term. -/
theorem ncEval_zero_fun {A : Type*} [Ring A] [Algebra k A] {n : ℕ}
    (p : MvPolynomial (Fin n) k) :
    KLR.ncEval (fun _ => (0 : A)) p = algebraMap k A (MvPolynomial.constantCoeff p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [KLR.ncEval_monomial, MvPolynomial.constantCoeff_monomial]
    by_cases hs : s = 0
    · subst hs; simp
    · obtain ⟨a, ha⟩ : ∃ a, s a ≠ 0 := by
        by_contra h; exact hs (Finsupp.ext fun a => by_contra fun h' => h ⟨a, h'⟩)
      rw [ite_eq_right_iff.2 (fun h => absurd h hs), map_zero,
        List.prod_eq_zero (List.mem_ofFn.2 ⟨a, zero_pow ha⟩), mul_zero]
  | add p q hp hq => rw [KLR.ncEval_add, hp, hq, map_add, map_add]

/-- The downward translation as an algebra map on endomorphisms. -/
def downEnd (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    End (Free.of k a) →ₐ[k] End (Free.of k (downContextObj RD Λ μ u v a)) :=
  KL3.Diagram.functorEndAlg k (downLinearFunctor RD Λ k μ u v) (Free.of k a)

/-- A polynomial in red dots translates to its constant term. -/
theorem downLinear_lpoly_red {a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} {n : ℕ}
    (y : Fin n → (a ⟶ a)) (hy : ∀ i, downLinear RD Λ k μ u v (LinDiagram.of (y i)) = 0)
    (p : MvPolynomial (Fin n) k) :
    downLinear RD Λ k μ u v (lpoly k y p) =
      MvPolynomial.constantCoeff p • 𝟙 (Free.of k (downContextObj RD Λ μ u v a)) := by
  have e := AlgHom.map_ncEval (downEnd RD Λ k μ u v a)
    (fun i => (LinDiagram.of (y i) : End (Free.of k a))) p
  change downEnd RD Λ k μ u v a (lpoly k y p) = _
  rw [lpoly, e]
  simp only [downEnd, KL3.Diagram.functorEndAlg]
  erw [show (fun i => (downLinearFunctor RD Λ k μ u v).map (LinDiagram.of (y i))) =
    fun _ => (0 : End (Free.of k (downContextObj RD Λ μ u v a))) from funext hy]
  rw [ncEval_zero_fun, Algebra.algebraMap_eq_smul_one]
  rfl

section RelationEquations

variable {J : Type*} (Q : J → J → MvPolynomial (Fin 2) k)

theorem relation_sqNe (c d : J) (h : c ≠ d) :
    relation k Q (.sqNe c d h) = (LinDiagram.of (X2 c d ≫ X2 d c) -
      lpoly k ![D0 c d, D1 c d] (Q c d) : LinDiagram k (ob [c, d]) (ob [c, d])) := rfl

theorem relation_slideLNe (c d : J) (h : c ≠ d) :
    relation k Q (.slideLNe c d h) = (LinDiagram.of (X2 c d ≫ D0 d c) -
      LinDiagram.of (D1 c d ≫ X2 c d) : LinDiagram k (ob [c, d]) (ob [d, c])) := rfl

theorem relation_slideRNe (c d : J) (h : c ≠ d) :
    relation k Q (.slideRNe c d h) = (LinDiagram.of (D0 c d ≫ X2 c d) -
      LinDiagram.of (X2 c d ≫ D1 d c) : LinDiagram k (ob [c, d]) (ob [d, c])) := rfl

theorem relation_braid (c d e : J) (h : ¬ (c = e ∧ c ≠ d)) :
    relation k Q (.braid c d e h) = (LinDiagram.of (braidL c d e) -
      LinDiagram.of (braidR c d e) : LinDiagram k (ob [c, d, e]) (ob [e, d, c])) := rfl

end RelationEquations

variable (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

theorem downLinear_relation_sqNe_red (s t : Fin ℓ) (h : (Sum.inr s : I ⊕ Fin ℓ) ≠ .inr t)
    (hQ : MvPolynomial.constantCoeff (Q (.inr s) (.inr t)) = 0) :
    downLinear RD Λ k μ u v (relation k Q (.sqNe _ _ h)) = 0 := by
  have key : downLinear RD Λ k μ u v (LinDiagram.of (X2 (Sum.inr s) (Sum.inr t) ≫
      X2 (Sum.inr t) (Sum.inr s)) - lpoly k ![D0 (Sum.inr s) (Sum.inr t),
        D1 (Sum.inr s) (Sum.inr t)] (Q (.inr s) (.inr t)) :
        LinDiagram k (ob [Sum.inr s, Sum.inr t]) (ob [Sum.inr s, Sum.inr t])) = 0 := by
    rw [map_sub, LinDiagram.of_comp, downLinear_comp,
      downLinear_lpoly_red RD Λ k μ u v _ (fun i => by
        fin_cases i
        · exact downLinear_dl_red_dot RD Λ k μ u v [] s [.inr t] rfl rfl
        · exact downLinear_dl_red_dot RD Λ k μ u v [.inr s] t [] rfl rfl), hQ, zero_smul]
    erw [downLinear_dl_red_cross RD Λ k μ u v [] s t [] rfl rfl]
    simp
  exact key

theorem downLinear_relation_slideLNe_red (s t : Fin ℓ)
    (h : (Sum.inr s : I ⊕ Fin ℓ) ≠ .inr t) :
    downLinear RD Λ k μ u v (relation k Q (.slideLNe _ _ h)) = 0 := by
  have key : downLinear RD Λ k μ u v (LinDiagram.of (X2 (Sum.inr s) (Sum.inr t) ≫
      D0 (Sum.inr t) (Sum.inr s)) - LinDiagram.of (D1 (Sum.inr s) (Sum.inr t) ≫
        X2 (Sum.inr s) (Sum.inr t)) :
        LinDiagram k (ob [Sum.inr s, Sum.inr t]) (ob [Sum.inr t, Sum.inr s])) = 0 := by
    rw [map_sub, LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp, downLinear_comp]
    erw [downLinear_dl_red_cross RD Λ k μ u v [] s t [] rfl rfl]
    simp
  exact key

theorem downLinear_relation_slideRNe_red (s t : Fin ℓ)
    (h : (Sum.inr s : I ⊕ Fin ℓ) ≠ .inr t) :
    downLinear RD Λ k μ u v (relation k Q (.slideRNe _ _ h)) = 0 := by
  have key : downLinear RD Λ k μ u v (LinDiagram.of (D0 (Sum.inr s) (Sum.inr t) ≫
      X2 (Sum.inr s) (Sum.inr t)) - LinDiagram.of (X2 (Sum.inr s) (Sum.inr t) ≫
        D1 (Sum.inr t) (Sum.inr s)) :
        LinDiagram k (ob [Sum.inr s, Sum.inr t]) (ob [Sum.inr t, Sum.inr s])) = 0 := by
    rw [map_sub, LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp, downLinear_comp]
    have hD : downLinear RD Λ k μ u v (LinDiagram.of (D0 (Sum.inr s) (Sum.inr t))) = 0 :=
      downLinear_dl_red_dot RD Λ k μ u v [] s [.inr t] rfl rfl
    have hD' : downLinear RD Λ k μ u v (LinDiagram.of (D1 (Sum.inr t) (Sum.inr s))) = 0 :=
      downLinear_dl_red_dot RD Λ k μ u v [.inr t] s [] rfl rfl
    rw [hD, hD']
    simp
  exact key

/-- A composite of three diagrams one of whose factors translates to zero translates to
zero. -/
theorem downLinear_comp3_eq_zero {a b c d : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d)
    (H : downLinear RD Λ k μ u v (LinDiagram.of f) = 0 ∨
      downLinear RD Λ k μ u v (LinDiagram.of g) = 0 ∨
      downLinear RD Λ k μ u v (LinDiagram.of h) = 0) :
    downLinear RD Λ k μ u v (LinDiagram.of (f ≫ g ≫ h)) = 0 := by
  rw [LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp, downLinear_comp]
  rcases H with H | H | H <;> simp [H]

/-- The braid relation in which the first two strands are red translates to zero. -/
theorem downLinear_relation_braid_red₁₂ (s t : Fin ℓ) (e : I ⊕ Fin ℓ)
    (h : ¬ ((Sum.inr s : I ⊕ Fin ℓ) = e ∧ (Sum.inr s : I ⊕ Fin ℓ) ≠ .inr t)) :
    downLinear RD Λ k μ u v (relation k Q (.braid _ _ _ h)) = 0 := by
  have h₁ : downLinear RD Λ k μ u v (LinDiagram.of (XL (Sum.inr s) (Sum.inr t) e)) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [] s t [e] rfl rfl
  have h₂ : downLinear RD Λ k μ u v (LinDiagram.of (XR e (Sum.inr s) (Sum.inr t))) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [e] s t [] rfl rfl
  have key : downLinear RD Λ k μ u v (LinDiagram.of (braidL (Sum.inr s) (Sum.inr t) e) -
      LinDiagram.of (braidR (Sum.inr s) (Sum.inr t) e) :
        LinDiagram k (ob [Sum.inr s, Sum.inr t, e]) (ob [e, Sum.inr t, Sum.inr s])) = 0 := by
    rw [map_sub, downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inl h₁),
      downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inr (Or.inr h₂)), sub_zero]
  exact key

/-- The braid relation in which the outer two strands are red translates to zero. -/
theorem downLinear_relation_braid_red₁₃ (s t : Fin ℓ) (d : I ⊕ Fin ℓ)
    (h : ¬ ((Sum.inr s : I ⊕ Fin ℓ) = .inr t ∧ (Sum.inr s : I ⊕ Fin ℓ) ≠ d)) :
    downLinear RD Λ k μ u v (relation k Q (.braid _ _ _ h)) = 0 := by
  have h₁ : downLinear RD Λ k μ u v (LinDiagram.of (XR d (Sum.inr s) (Sum.inr t))) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [d] s t [] rfl rfl
  have h₂ : downLinear RD Λ k μ u v (LinDiagram.of (XL (Sum.inr s) (Sum.inr t) d)) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [] s t [d] rfl rfl
  have key : downLinear RD Λ k μ u v (LinDiagram.of (braidL (Sum.inr s) d (Sum.inr t)) -
      LinDiagram.of (braidR (Sum.inr s) d (Sum.inr t)) :
        LinDiagram k (ob [Sum.inr s, d, Sum.inr t]) (ob [Sum.inr t, d, Sum.inr s])) = 0 := by
    rw [map_sub, downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inr (Or.inl h₁)),
      downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inr (Or.inl h₂)), sub_zero]
  exact key

/-- The braid relation in which the last two strands are red translates to zero. -/
theorem downLinear_relation_braid_red₂₃ (c : I ⊕ Fin ℓ) (s t : Fin ℓ)
    (h : ¬ (c = .inr t ∧ c ≠ .inr s)) :
    downLinear RD Λ k μ u v (relation k Q (.braid _ _ _ h)) = 0 := by
  have h₁ : downLinear RD Λ k μ u v (LinDiagram.of (XL (Sum.inr s) (Sum.inr t) c)) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [] s t [c] rfl rfl
  have h₂ : downLinear RD Λ k μ u v (LinDiagram.of (XR c (Sum.inr s) (Sum.inr t))) = 0 :=
    downLinear_dl_red_cross RD Λ k μ u v [c] s t [] rfl rfl
  have key : downLinear RD Λ k μ u v (LinDiagram.of (braidL c (Sum.inr s) (Sum.inr t)) -
      LinDiagram.of (braidR c (Sum.inr s) (Sum.inr t)) :
        LinDiagram k (ob [c, Sum.inr s, Sum.inr t]) (ob [Sum.inr t, Sum.inr s, c])) = 0 := by
    rw [map_sub, downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inr (Or.inr h₁)),
      downLinear_comp3_eq_zero RD Λ k μ u v _ _ _ (Or.inl h₂), sub_zero]
  exact key

end Categorification.Stendhal.DoubleDiagram
