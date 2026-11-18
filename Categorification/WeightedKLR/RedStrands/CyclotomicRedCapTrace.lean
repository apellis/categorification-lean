/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDottedTrace
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCapCoordinates
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPairing

/-!
# Red crossings and the opposite cap on present-colour corners

Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25. Transferring the last-dot
power across the cap compares the canonical cyclotomic projections. A common
shift in the remainder formula includes the case where the two weights have
different signs.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Polynomial

variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
/-- Right multiplication by the induction dot on the two-sided cyclotomic corner. -/
def cornerDotPow (β : Multiset I) (a : I → Polynomial k) (d : ℕ) :
    AbsentColour.Corner Q i a β →ₗ[k] AbsentColour.Corner Q i a β where
  toFun z := ⟨z.val * CyclotomicAction.dotElt Q a i (show {i} + β = {i} + β from rfl) ^ d, by
    have hc := ((commute_x_last_cL (Q := Q) i β 1).map (CycKLR.mk k Q a ({i} + β))).pow_left d
    constructor
    · rw [← mul_assoc, z.2.1]
    · change z.val * CycKLR.mk k Q a ({i} + β) (x ⟨β.card, lastPos_lt i β⟩) ^ d * _ = _
      rw [mul_assoc, hc.eq, ← mul_assoc, z.2.2]
      rfl⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

variable {a b : I → Polynomial k} (hab : ∀ j, a j ∣ b j)

/-- The cyclotomic red projection applied to the elements of the two-sided corner. -/
def cornerRedProjection (β : Multiset I) : AbsentColour.Corner Q i b β →ₗ[k] AbsentColour.Corner Q i a β where
  toFun z := ⟨cyclotomicRedProjection Q hab ({i} + β) z.val, by
    constructor
    · simpa only [map_mul, cyclotomicRedProjection_mk] using congrArg (cyclotomicRedProjection Q hab ({i} + β)) z.2.1
    · simpa only [map_mul, cyclotomicRedProjection_mk] using congrArg (cyclotomicRedProjection Q hab ({i} + β)) z.2.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "B" => ((Singleton.singleton i : Multiset I) + β)
local notation "y" => (x (Q := Q) (ν := B) (Fin.mk (Multiset.card β) (lastPos_lt i β)))
local notation "aff" => KLRAlgebra k Q B

/-- The last-dot power on a present-colour commutator corner. -/
abbrev middleDotPow (a : I → Polynomial k) (d : ℕ) :=
  cornerDotPow Q i β a d

/-- The cyclotomic projection on a present-colour commutator corner. -/
abbrev middleRedProjection := cornerRedProjection Q i hab β

local notation:max "lift(" c "," r ")" => middleTensorLift Q i γ c (Submodule.Quotient.mk r)
local notation:max "proj(" c ")" => middleCyclotomicProj Q i γ c

private theorem middleDotPow_rep (a : I → Polynomial k) (d : ℕ) (r : aff) :
    middleDotPow Q i γ a d (proj(a) lift(a,r)) = proj(a) lift(a,r * y ^ d) := by
  apply Subtype.ext
  change (proj(a) lift(a,r) : CycKLR k Q a B) * _ = _
  rw [middleCyclotomicProj_representative, middleCyclotomicProj_representative]
  change CycKLR.mk k Q a B _ * CycKLR.mk k Q a B y ^ d = _
  rw [← map_pow, ← map_mul]
  apply congrArg (CycKLR.mk k Q a B)
  rw [mul_assoc _ (cL Q i β 1) (y ^ d), ← ((commute_x_last_cL (Q := Q) i β 1).pow_left d).eq]
  simp only [mul_assoc]

private theorem middleRedProjection_rep (r : aff) :
    middleRedProjection Q i γ hab (proj(b) lift(b,r)) = proj(a) lift(a,r) := by
  apply Subtype.ext
  change cyclotomicRedProjection Q hab B (proj(b) lift(b,r) : CycKLR k Q b B) = _
  rw [middleCyclotomicProj_representative, cyclotomicRedProjection_mk, middleCyclotomicProj_representative]

variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)
  {C₀ : QuantumGroup.CartanDatum I} {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
  (RD : QuantumGroup.UDot.WeightDatum C₀ W Z) (lower upper : W)
  (hl : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) lower)
  (hu : ((b i).natDegree : ℤ) = RD.pair (RD.iY i) upper)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

local notation "π" => cyclotomicRedProjection Q hab β
local notation:max "wt(" w ")" => RD.pair (RD.iY i) (w - Multiset.sum (Multiset.map RD.iX β))

/-- Moving the red crossing past the opposite cap on any present-colour corner
(Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25). Multiplying by the new last-dot
power before tracing upstairs agrees with projecting the corner and tracing
downstairs, for every sign of each coroot pairing. -/
theorem redProjection_oppositeCap (d : ℕ) (hi : b i = X ^ d * a i)
    (z : MiddleCyclotomic Q i γ b) :
    π (CornerTrace.trace Q i γ b hsym hQ hb RD upper hu hdeg (middleDotPow Q i γ b d z)) =
      CornerTrace.trace Q i γ a hsym hQ ha RD lower hl hdeg (middleRedProjection Q i γ hab z) := by
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (z : CycKLR k Q b B)
  have hz : proj(b) lift(b,r) = z := by
    apply Subtype.ext
    rw [middleCyclotomicProj_representative, map_mul, map_mul, hr, z.2.1, z.2.2]
  let N := (-wt(upper)).toNat + (-wt(lower)).toNat + 1
  have hupper : 0 < wt(upper) + N := by dsimp only [N]; omega
  have hlower : 0 < wt(lower) + (N+d : ℕ) := by dsimp only [N]; omega
  rw [← hz, middleDotPow_rep, middleRedProjection_rep,
    CornerTrace.trace_eq_dotted Q i γ b hsym hQ hb RD upper hu hdeg N hupper,
    CornerTrace.trace_eq_dotted Q i γ a hsym hQ ha RD lower hl hdeg (N+d) hlower]
  change (π).toRingHom _ = _
  rw [redTrace_map _ _ _ ((monic_X_pow N).mul (monic_aMonicL i β b hsym hQ (hb i))),
    Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    cyclotomicRedProjection_aMonicL Q hab i β d hi, cyclotomicRedProjection_sPoly,
    redProjection_dottedCapPolynomial Q hab i γ hsym N d r, ← mul_assoc, ← pow_add]

end Categorification.Stendhal
