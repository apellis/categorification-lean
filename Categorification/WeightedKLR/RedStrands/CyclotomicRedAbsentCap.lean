/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentCap
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCapTrace

/-!
# Red projections and the opposite cap for an absent colour

Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25. In the absent-colour
commutator the source is the two-sided dot-unit corner. The comparison of its
caps follows by evaluation of polynomials, including on the vacuum edge.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra AbsentColour Polynomial
variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (β : Multiset I)
  {a b : I → Polynomial k} (hab : ∀ j, a j ∣ b j)

local notation "π" => cyclotomicRedProjection Q hab β
local notation "B" => ((Singleton.singleton i : Multiset I) + β)
local notation "y" => (x (Q := Q) (ν := B) (Fin.mk (Multiset.card β) (lastPos_lt i β)))

private theorem project_modulus (d : ℕ) (hi : b i = X ^ d * a i) :
    (cornerModulus Q i β b).map (π).toRingHom = X ^ d * cornerModulus Q i β a := by
  unfold cornerModulus
  split_ifs with hz
  · rw [hi, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_map]
    congr 2
    ext r
    exact (π).commutes r
  · exact cyclotomicRedProjection_aMonicL Q hab i β d hi

private theorem dotPow_cornerEval (d : ℕ) (p : Polynomial (CycKLR k Q b β)) :
    cornerDotPow Q i β b d (cornerEval Q i β b p) = cornerEval Q i β b (X ^ d * p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, map_add, hp, hq]
  | monomial n r =>
    rw [cornerEval_monomial, X_pow_mul_monomial, cornerEval_monomial]
    apply Subtype.ext
    let z := CycKLR.mk k Q b B y
    let c := AbsentColour.cyclotomicLast Q i b β r
    let e := AbsentColour.cyclotomicLast Q i b β 1
    have hc : Commute (z ^ d) e := by
      rw [show e = CycKLR.mk k Q b B (cL Q i β 1) from AbsentColour.cyclotomicLast_one Q i b β]
      exact ((commute_x_last_cL (Q := Q) i β 1).map (CycKLR.mk k Q b B)).pow_left d
    change (c * z ^ n * e) * z ^ d = c * z ^ (n+d) * e
    rw [mul_assoc _ e, ← hc.eq, pow_add]
    simp only [mul_assoc]

private theorem project_cornerEval (p : Polynomial (CycKLR k Q b β)) :
    cornerRedProjection Q i hab β (cornerEval Q i β b p) =
      cornerEval Q i β a (p.map (π).toRingHom) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, map_add, hp, hq]
  | monomial n r =>
    obtain ⟨v, rfl⟩ := CycKLR.mk_surjective r
    rw [cornerEval_monomial, Polynomial.map_monomial, cornerEval_monomial]
    apply Subtype.ext
    change cyclotomicRedProjection Q hab B
      (AbsentColour.cyclotomicLast Q i b β (CycKLR.mk k Q b β v) * CycKLR.mk k Q b B y ^ n *
        AbsentColour.cyclotomicLast Q i b β 1) =
      AbsentColour.cyclotomicLast Q i a β (π (CycKLR.mk k Q b β v)) * CycKLR.mk k Q a B y ^ n *
        AbsentColour.cyclotomicLast Q i a β 1
    simp only [AbsentColour.cyclotomicLast_mk, AbsentColour.cyclotomicLast_one, map_mul, map_pow, cyclotomicRedProjection_mk]

variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)
  {C₀ : QuantumGroup.CartanDatum I} {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
  (RD : QuantumGroup.UDot.WeightDatum C₀ W Z) (lower upper : W)
  (hl : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) lower)
  (hu : ((b i).natDegree : ℤ) = RD.pair (RD.iY i) upper)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- The red crossing commutes with the opposite cap on the whole absent-colour
corner after inserting its dot power (Webster v2, §4.5, Theorem 4.25).
At weight zero the empty inverse coordinate gives the zero cap. -/
theorem redProjection_absent_oppositeCap (d : ℕ) (hi : b i = X ^ d * a i)
    (habs : i ∉ β) (z : Corner Q i b β) :
    π (oppositeCap Q i β b hsym hQ hb RD upper hu hdeg habs (cornerDotPow Q i β b d z)) =
      oppositeCap Q i β a hsym hQ ha RD lower hl hdeg habs (cornerRedProjection Q i hab β z) := by
  obtain ⟨p,rfl⟩ := cornerEval_surjective Q i β b hsym hQ hb RD upper hu hdeg habs z
  rw [dotPow_cornerEval, project_cornerEval, oppositeCap_eval, oppositeCap_eval]
  change (π).toRingHom _ = _
  rw [redTrace_map _ _ _ (cornerModulus_monic Q i β b hsym hQ hb), project_modulus Q i β hab d hi,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    redTrace_mul_X_pow _ (cornerModulus_monic Q i β a hsym hQ ha)]

section AllContents

variable (c : I → Polynomial k) (hc : ∀ j, (c j).Monic) (highest : W)
  (hhighest : ((c i).natDegree : ℤ) = RD.pair (RD.iY i) highest)

/-- The opposite cap on the ordinary two-sided induction corner, in arbitrary black
content. At a present colour Brundan's signed inverse gives the bimodule trace.
At an absent colour its inverse components are the finite dot-unit coordinates. -/
def cyclotomicOppositeCap : Corner Q i c β →ₗ[k] CycKLR k Q c β :=
  if hi : i ∈ β then
    let he := (Multiset.singleton_add i (β.erase i)).trans (Multiset.cons_erase hi)
    he ▸ (CornerTrace.trace Q i (β.erase i) c hsym hQ hc RD highest hhighest hdeg).restrictScalars k
  else oppositeCap Q i β c hsym hQ hc RD highest hhighest hdeg hi

private theorem cyclotomicOppositeCap_present (γ : Multiset I) :
    cyclotomicOppositeCap Q i ({i} + γ) hsym hQ RD hdeg c hc highest hhighest =
      (CornerTrace.trace Q i γ c hsym hQ hc RD highest hhighest hdeg).restrictScalars k := by
  unfold cyclotomicOppositeCap
  rw [dite_eq_left (by simp)]
  have transport (u : Multiset I) (hu : u = γ) (he : {i} + u = {i} + γ) :
      Eq.rec (motive := fun v _ => Corner Q i c v →ₗ[k] CycKLR k Q c v)
        ((CornerTrace.trace Q i u c hsym hQ hc RD highest hhighest hdeg).restrictScalars k) he =
        (CornerTrace.trace Q i γ c hsym hQ hc RD highest hhighest hdeg).restrictScalars k := by
    subst u
    rfl
  exact transport ((({i} : Multiset I) + γ).erase i) (by simp) _

/-- Webster v2, §4.5, Theorem 4.25, opposite-cap comparison on an arbitrary
induction corner. No assumption on the presence of the final colour or the signs
of the two coroot weights is required. -/
theorem redProjection_cyclotomicOppositeCap (d : ℕ) (hi : b i = X ^ d * a i)
    (z : Corner Q i b β) :
    π (cyclotomicOppositeCap Q i β hsym hQ RD hdeg b hb upper hu (cornerDotPow Q i β b d z)) =
      cyclotomicOppositeCap Q i β hsym hQ RD hdeg a ha lower hl (cornerRedProjection Q i hab β z) := by
  by_cases hm : i ∈ β
  · obtain ⟨γ,hγ⟩ := Multiset.exists_cons_of_mem hm
    rw [← Multiset.singleton_add] at hγ
    subst β
    rw [cyclotomicOppositeCap_present, cyclotomicOppositeCap_present]
    exact redProjection_oppositeCap Q i γ hab hsym hQ ha hb RD lower upper hl hu hdeg d hi z
  · simp only [cyclotomicOppositeCap, dite_eq_right hm]
    exact redProjection_absent_oppositeCap Q i β hab hsym hQ ha hb RD lower upper hl hu hdeg d hi hm z

end AllContents
end Categorification.Stendhal
