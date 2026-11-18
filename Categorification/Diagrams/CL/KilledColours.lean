/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.KL1
import Categorification.Diagrams.CL.NoMix

/-!
# KLR relations when the dots of some colours vanish

Let `P` be a presentation on the Cautis–Lauda signature in which the dots on upward strands of the
colours marked by `R` vanish, and in which upward words `[c, d, c]` with `c` marked are zero. Then
the KLR relations on upward strands for polynomials `Q` and `Q'` are equivalent as soon as `Q c d`
and `Q' c d` agree after setting the variables of the marked colours to zero
(`klrHolds_of_killed`).

This is used for the cover of Webster's tensor product algebras (B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v2, §4.5, Lemma 4.28): red strands of the
double calculus become strands of extra colours of an enlarged Cartan datum, on which dots vanish
and no colour repeats. Webster's mixed polynomials `Q_{ir} = u^{λ_r^i}` (`stendhalQ`) then agree
with the Cautis–Lauda polynomials of the enlarged datum after the red dots are set to zero.

## Main results

* `KLR.killVars`, `KLR.ncEval_aeval_killVars`: setting variables to zero before an ordered
  evaluation in which they evaluate to zero;
* `KLR.aeval_killVars_qbar`: setting the middle variable to zero commutes with `qbar`;
* `KL3.Diagram.CL.klrHolds_of_killed`.
-/

set_option backward.isDefEq.respectTransparency false

open MvPolynomial

noncomputable section

namespace Categorification.KLR

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

/-- Setting the variables marked by `K` to zero. -/
def killVars (k : Type*) [CommRing k] {n : ℕ} (K : Fin n → Bool) (a : Fin n) :
    MvPolynomial (Fin n) k :=
  if K a then 0 else X a

theorem aeval_killVars_of_forall {n : ℕ} {K : Fin n → Bool} (hK : ∀ a, K a = false)
    (p : MvPolynomial (Fin n) k) : aeval (killVars k K) p = p := by
  have : (killVars k K : Fin n → MvPolynomial (Fin n) k) = X := funext fun a => by
    simp [killVars, hK a]
  rw [this, aeval_X_left_apply]

/-- If the variables marked by `K` evaluate to zero, a polynomial and its specialization with
those variables set to zero have the same ordered evaluation. -/
theorem ncEval_aeval_killVars {n : ℕ} (K : Fin n → Bool) (z : Fin n → A)
    (hz : ∀ a, K a = true → z a = 0) (p : MvPolynomial (Fin n) k) :
    ncEval z (aeval (killVars k K) p) = ncEval z p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    by_cases h : ∃ a, K a = true ∧ s a ≠ 0
    · obtain ⟨a, ha, hs⟩ := h
      have h0 : aeval (killVars k K) (monomial s c) = 0 := by
        rw [aeval_monomial, Finsupp.prod, Finset.prod_eq_zero (i := a)
          (Finsupp.mem_support_iff.2 hs) (by simp [killVars, ha, zero_pow hs]), mul_zero]
      have h1 : (List.ofFn fun b => z b ^ s b).prod = 0 :=
        List.prod_eq_zero (List.mem_ofFn.2 ⟨a, by simp [hz a ha, zero_pow hs]⟩)
      rw [h0, Diagram.ncEval_zero', Diagram.ncEval_monomial', h1, mul_zero]
    · push Not at h
      have h0 : aeval (killVars k K) (monomial s c) = monomial s c := by
        rw [aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, algebraMap_eq]
        congr 1
        refine Finset.prod_congr rfl fun a ha => ?_
        cases hK : K a
        · simp [killVars, hK]
        · exact absurd (h a hK) (Finsupp.mem_support_iff.1 ha)
      rw [h0]
  | add p q hp hq => rw [map_add, Diagram.ncEval_add', Diagram.ncEval_add', hp, hq]

/-- Killing the middle variable commutes with `qbar`. -/
theorem aeval_killVars_qbar (b : Bool) (Q : MvPolynomial (Fin 2) k) :
    aeval (killVars k ![false, b, false]) (qbar Q) = qbar (aeval (killVars k ![false, b]) Q) := by
  cases b
  · rw [aeval_killVars_of_forall (by decide), aeval_killVars_of_forall (by decide)]
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [qbar_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Fin.prod_univ_two]
    by_cases hs : s 1 = 0
    · have : (algebraMap k (MvPolynomial (Fin 2) k) c *
          ((killVars k ![false, true] 0 : MvPolynomial (Fin 2) k) ^ s 0 *
            killVars k ![false, true] 1 ^ s 1)) = monomial s c := by
        rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
        simp [killVars, hs, algebraMap_eq]
      rw [this, qbar_monomial]
      simp [killVars, hs, map_sum]
    · have : (killVars k ![false, true] 1 : MvPolynomial (Fin 2) k) ^ s 1 = 0 := by
        simp [killVars, zero_pow hs]
      have hz : qbar (0 : MvPolynomial (Fin 2) k) = 0 := by
        have := qbar_add (0 : MvPolynomial (Fin 2) k) 0
        simpa using this
      rw [this, mul_zero, mul_zero, hz]
      simp [killVars, zero_pow hs]
  | add p q hp hq => rw [map_add, qbar_add, map_add, hp, hq, qbar_add]

end Categorification.KLR

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (psig RD) k) (Q Q' : I → I → MvPolynomial (Fin 2) k)
  (R : I → Bool)

/-- The KLR relations on upward strands for `Q` imply those for `Q'`, if the upward dots of the
colours marked by `R` vanish, upward words `[c, d, c]` with `c` marked vanish, and for `c ≠ d` the
polynomials `Q c d`, `Q' c d` agree after setting the variables of marked colours to zero. -/
theorem klrHolds_of_killed
    (hdot : ∀ (μ : X) (u v : List I) (c : I) {a b : Obj (KLR.Diagram.sig I)}
      (ha : u ++ (KLR.Diagram.Gen.dot c).dom ++ v = a.word)
      (hb : u ++ (KLR.Diagram.Gen.dot c).cod ++ v = b.word), R c = true →
      P.diag (upDiag RD μ (KLR.Diagram.dl u (.dot c) v ha hb)) = 0)
    (hrep : ∀ (μ : X) (c d : I), R c = true → 𝟙 (P.obj (ob RD μ (ups [c, d, c]))) = 0)
    (hQ : ∀ c d, c ≠ d → aeval (KLR.killVars k ![R c, R d]) (Q c d) =
      aeval (KLR.killVars k ![R c, R d]) (Q' c d))
    (h : KLRHolds P Q) : KLRHolds P Q' := by
  intro μ r
  have key := h μ r
  cases r with
  | sqNe c d hcd =>
    simp only [KLR.Diagram.relation] at key ⊢
    rw [← freeLift_upFreeC] at key ⊢
    rw [Functor.map_sub, sub_eq_zero] at key ⊢
    rw [key]
    change functorEndAlg k (freeLift k (upFreeC P μ)) (Free.of k (KLR.Diagram.ob [c, d]))
        (KLR.Diagram.lpoly k _ (Q c d)) =
      functorEndAlg k (freeLift k (upFreeC P μ)) (Free.of k (KLR.Diagram.ob [c, d]))
        (KLR.Diagram.lpoly k _ (Q' c d))
    have hz : ∀ a, (![R c, R d] : Fin 2 → Bool) a = true →
        (fun a => functorEndAlg k (freeLift k (upFreeC P μ)) _
          (LinDiagram.of ((![KLR.Diagram.D0 c d, KLR.Diagram.D1 c d] : Fin 2 → _) a))) a = 0 := by
      intro a ha
      fin_cases a
      · show (freeLift k (upFreeC P μ)).map (LinDiagram.of _) = 0
        rw [freeLift_map_of]
        exact hdot μ [] [d] c (a := KLR.Diagram.ob [c, d]) (b := KLR.Diagram.ob [c, d]) rfl rfl ha
      · show (freeLift k (upFreeC P μ)).map (LinDiagram.of _) = 0
        rw [freeLift_map_of]
        exact hdot μ [c] [] d (a := KLR.Diagram.ob [c, d]) (b := KLR.Diagram.ob [c, d]) rfl rfl ha
    rw [KLR.Diagram.lpoly, KLR.Diagram.lpoly, AlgHom.map_ncEval, AlgHom.map_ncEval,
      ← KLR.ncEval_aeval_killVars _ _ hz, hQ c d hcd, KLR.ncEval_aeval_killVars _ _ hz]
  | braidQ c d hcd =>
    cases hc : R c
    · simp only [KLR.Diagram.relation] at key ⊢
      rw [← freeLift_upFreeC] at key ⊢
      rw [Functor.map_sub, sub_eq_zero] at key ⊢
      rw [key]
      have hz : ∀ a, (![false, R d, false] : Fin 3 → Bool) a = true →
          (fun a => functorEndAlg k (freeLift k (upFreeC P μ)) _
            (LinDiagram.of ((![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c,
              KLR.Diagram.E2 c d c] : Fin 3 → _) a))) a = 0 := by
        intro a ha
        fin_cases a
        · exact absurd ha (by simp)
        · show (freeLift k (upFreeC P μ)).map (LinDiagram.of _) = 0
          rw [freeLift_map_of]
          exact hdot μ [c] [c] d (a := KLR.Diagram.ob [c, d, c]) (b := KLR.Diagram.ob [c, d, c])
            rfl rfl ha
        · exact absurd ha (by simp)
      change functorEndAlg k (freeLift k (upFreeC P μ)) (Free.of k (KLR.Diagram.ob [c, d, c]))
          (KLR.Diagram.lpoly k _ (KLR.qbar (Q c d))) =
        functorEndAlg k (freeLift k (upFreeC P μ)) (Free.of k (KLR.Diagram.ob [c, d, c]))
          (KLR.Diagram.lpoly k _ (KLR.qbar (Q' c d)))
      have hQ' := hQ c d hcd
      rw [hc] at hQ'
      rw [KLR.Diagram.lpoly, KLR.Diagram.lpoly, AlgHom.map_ncEval, AlgHom.map_ncEval,
        ← KLR.ncEval_aeval_killVars _ _ hz, KLR.aeval_killVars_qbar, hQ',
        ← KLR.aeval_killVars_qbar, KLR.ncEval_aeval_killVars _ _ hz]
    · have hz := hrep μ c d hc
      rw [← Category.id_comp (P.lin _)]
      exact (congrArg (· ≫ _) hz).trans Limits.zero_comp
  | _ => exact key

end Categorification.KL3.Diagram.CL

end
