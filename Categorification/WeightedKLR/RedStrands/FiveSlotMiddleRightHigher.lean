/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.TypeA.Matsumoto
import Categorification.TypeA.Inversions

/-!
# Two generators for the middle-right five-slot higher kernel

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
An adapted reduced-word choice factors each higher coefficient through the
central crossing or the three-crossing word from the nearby loading.
The nearby higher kernel maps into the image of the central crossing.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "rightMiddle" => sadj N 2 • fixedTopFourExitCut 2
local notation "leftExtreme" => fixedTopFourExitCut 0
local notation "central" => fixedTopFourExitCut 1
local notation "nearby" => sadj N 2 • fixedTopFourExitCut 0

private def middleRightCandidate (w : Perm (Fin N)) (suffix : List ℕ) : List ℕ :=
  canWord N (w * (wordProd N suffix)⁻¹) ++ suffix

private def middleRightFits (w : Perm (Fin N)) (suffix : List ℕ) : Prop :=
  invCount N (w * (wordProd N suffix)⁻¹) + suffix.length = invCount N w

private instance (w : Perm (Fin N)) (suffix : List ℕ) :
    Decidable (middleRightFits w suffix) := by
  unfold middleRightFits
  infer_instance

private theorem middleRightCandidate_prod (w : Perm (Fin N)) (suffix : List ℕ) :
    wordProd N (middleRightCandidate w suffix) = w := by
  rw [middleRightCandidate, wordProd_append, wordProd_canWord]
  exact inv_mul_cancel_right w _

private theorem middleRightCandidate_reduced (w : Perm (Fin N)) (suffix : List ℕ)
    (hvalid : ValidWord N suffix) (hfit : middleRightFits w suffix) :
    IsReduced N (middleRightCandidate w suffix) := by
  constructor
  · exact validWord_append.mpr ⟨validWord_canWord _ _, hvalid⟩
  · rw [middleRightCandidate_prod, middleRightCandidate, List.length_append,
      length_canWord, length_eq_invCount, length_eq_invCount]
    exact hfit

private def middleRightWord (w : Perm (Fin N)) : List ℕ :=
  if middleRightFits w [1] then middleRightCandidate w [1]
  else if middleRightFits w [1, 2, 3] then middleRightCandidate w [1, 2, 3]
  else canWord N w

private theorem middleRightWord_spec (w : Perm (Fin N)) :
    IsReduced N (middleRightWord w) ∧ wordProd N (middleRightWord w) = w := by
  unfold middleRightWord
  split_ifs with h₁ h₂
  · exact ⟨middleRightCandidate_reduced w [1] (by simp [ValidWord, stendhalWeight]) h₁, middleRightCandidate_prod w [1]⟩
  · exact ⟨middleRightCandidate_reduced w [1, 2, 3] (by simp [ValidWord, stendhalWeight]) h₂, middleRightCandidate_prod w [1, 2, 3]⟩
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private theorem middleRight_higher_fits (w : Perm (Fin N))
    (hw : w • rightMiddle = leftExtreme ∨ w • rightMiddle = central ∨ w • rightMiddle = nearby) :
    middleRightFits w [1] ∨ middleRightFits w [1, 2, 3] := by
  have h : ∀ w : Perm (Fin N),
      w • rightMiddle = leftExtreme ∨ w • rightMiddle = central ∨ w • rightMiddle = nearby →
      middleRightFits w [1] ∨ middleRightFits w [1, 2, 3] := by decide +kernel
  exact h w hw

private theorem middleRightWord_hasSuffix (w : Perm (Fin N))
    (hw : w • rightMiddle = leftExtreme ∨ w • rightMiddle = central ∨ w • rightMiddle = nearby) :
    (∃ pref, middleRightWord w = pref ++ [1]) ∨
      ∃ pref, middleRightWord w = pref ++ [1, 2, 3] := by
  have h := middleRight_higher_fits w hw
  by_cases h₁ : middleRightFits w [1]
  · left
    refine ⟨canWord N (w * (wordProd N [1])⁻¹), ?_⟩
    simp only [middleRightWord, ite_eq_left h₁, middleRightCandidate]
  · right
    refine ⟨canWord N (w * (wordProd N [1, 2, 3])⁻¹), ?_⟩
    simp only [middleRightWord, ite_eq_right h₁,
      ite_eq_left (h.resolve_left h₁), middleRightCandidate]


variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "c₁" => (ψ 1 * e rightMiddle : R)
local notation "c₂" => (ψw [1, 2, 3] * e rightMiddle : R)

/-- The affine corner at the middle-right loading has two possible final
red-black paths to each nonviolated higher cut. -/
private theorem middleRight_affine_factor (hQ : KLRSymm Q) (u : Seq μ₀)
    (hu : u = leftExtreme ∨ u = central ∨ u = nearby) (z : R) :
    ∃ y₁ y₂ : R, e u * z * e rightMiddle = y₁ * c₁ + y₂ * c₂ := by
  classical
  let B := lbasis («μ» := μ₀) (stendhalQ_symm Q Λ hQ) middleRightWord middleRightWord_spec
  let f₁ := LinearMap.mulRight k c₁
  let f₂ := LinearMap.mulRight k c₂
  have hm : e u * z * e rightMiddle ∈ LinearMap.range f₁ ⊔ LinearMap.range f₂ := by
    induction B.mem_span z using Submodule.span_induction with
    | zero =>
      simp only [mul_zero, zero_mul]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ hx
    | mem x hx =>
      obtain ⟨⟨v, w, p⟩, rfl⟩ := hx
      have value : B (v, w, p) = (pol (monomial p 1) * ψw (middleRightWord w) * e v : R) :=
        lbasis_apply (stendhalQ_symm Q Λ hQ) middleRightWord middleRightWord_spec (v, w, p)
      rw [value, mul_assoc, mul_assoc _ (e v), e_mul_e]
      by_cases hv : v = rightMiddle
      · subst v
        rw [ite_eq_left (rfl : rightMiddle = rightMiddle)]
        by_cases hw : w • rightMiddle = u
        · have higher : w • rightMiddle = leftExtreme ∨ w • rightMiddle = central ∨
              w • rightMiddle = nearby := by
            rwa [hw]
          rcases middleRightWord_hasSuffix w higher with ⟨l, hl⟩ | ⟨l, hl⟩
          · apply Submodule.mem_sup_left
            refine ⟨e u * pol (monomial p 1) * ψw l, ?_⟩
            simp only [f₁, LinearMap.mulRight_apply, hl, ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc]
          · apply Submodule.mem_sup_right
            refine ⟨e u * pol (monomial p 1) * ψw l, ?_⟩
            simp only [f₂, LinearMap.mulRight_apply, hl, ψw_append, mul_assoc]
        · have cut := e_mul_pol_ψw_e (Q := stendhalQ Q Λ) (monomial p (1 : k))
            (middleRightWord w) rightMiddle
          rw [(middleRightWord_spec w).2] at cut
          rw [← cut, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hw), zero_mul]
          exact zero_mem _
      · rw [ite_eq_right hv, mul_zero, mul_zero]
        exact zero_mem _
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨y₁, rfl⟩ := ha
  obtain ⟨y₂, rfl⟩ := hb
  exact ⟨y₁, y₂, he.symm⟩


local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "pof" => fun v : Seq μ₀ => F (e v)

private theorem hflip_middleRightFirst :
    hflip c₁ = (ψ 1 * e central : R) := by
  have step : sadj N 1 • rightMiddle = central := by decide +kernel
  rw [hflip_mul, hflip_ψ, hflip_e, e_mul_ψ, step]

private theorem hflip_middleRightSecond :
    hflip c₂ = (ψw [3, 2, 1] * e nearby : R) := by
  rw [hflip_mul, hflip_e, hflip_ψw]
  change (e rightMiddle : R) * ψw [3, 2, 1] = _
  rw [e_mul_ψw]
  have step : (wordProd N [3, 2, 1])⁻¹ • rightMiddle = nearby := by decide +kernel
  rw [step]

/-- Every middle-right coefficient supported at a nonviolated higher loading
factors through the two explicit central and nearby crossing words. -/
theorem fiveSlotMiddleRight_viol_corner_two_factors (hQ : KLRSymm Q) (u : Seq μ₀)
    (hu : u = leftExtreme ∨ u = central ∨ u = nearby) (x : V)
    (hx : pof rightMiddle * x * pof u = x) :
    ∃ a b : V,
      x = F (ψ 1 * e central) * a + F (ψw [3, 2, 1] * e nearby) * b := by
  obtain ⟨y, hy⟩ := violMk_surjective (Q := Q) (Λ := Λ) x
  obtain ⟨z, rfl⟩ := ofKLR_surjective y
  have hπz : F z = x := hy
  have hk : F (e rightMiddle * z * e u) = x := by rw [map_mul, map_mul, hπz, hx]
  obtain ⟨a, b, hcoef⟩ := middleRight_affine_factor Q Λ hQ u hu (hflip z)
  have hnative : (e rightMiddle * z * e u : R) =
      (ψ 1 * e central) * hflip a + (ψw [3, 2, 1] * e nearby) * hflip b := by
    simpa only [hflip_mul, hflip_e, hflip_hflip, hflip_add, hflip_middleRightFirst Q Λ,
      hflip_middleRightSecond Q Λ, mul_assoc] using congrArg hflip hcoef
  refine ⟨F (hflip a), F (hflip b), ?_⟩
  calc
    x = F (e rightMiddle * z * e u) := hk.symm
    _ = _ := by simpa only [map_add, map_mul] using congrArg F hnative


local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2
  (adjacentBlockRoot 1 2 rightMiddle) (redWord rightMiddle)
local notation "C₁" => F (ψ 1 * e central)
local notation "C₂" => F (ψw [3, 2, 1] * e nearby)

private theorem middleRight_higher_classification (u : Seq μ₀)
    (order : redWord u = redWord rightMiddle)
    (higher : adjacentBlockRoot 1 2 rightMiddle < adjacentBlockRoot 1 2 u)
    (nonviolated : ¬ IsViolated u) : u = leftExtreme ∨ u = central ∨ u = nearby := by
  have hw : redWord u = redWord leftExtreme := order.trans (by decide)
  rcases fiveSlot_nonviolated_tops u hw nonviolated with ht | ht
  · have hs : FiveSlotRightTop rightMiddle := Or.inr (Or.inl rfl)
    have eq : adjacentBlockRoot 1 2 u = adjacentBlockRoot 1 2 rightMiddle :=
      (fiveSlotRightTop_blockRoot u ht).trans (fiveSlotRightTop_blockRoot rightMiddle hs).symm
    rw [eq] at higher
    exact (lt_irrefl _ higher).elim
  · exact ht

/-- The actual higher ideal cut at the middle right loading is generated on
the right by its central crossing and the three-crossing word from nearby. -/
theorem fiveSlotMiddleRight_higher_two_factors (hQ : KLRSymm Q) (x : V)
    (hx : x ∈ J) (hl : pof rightMiddle * x = x) :
    ∃ y₁ y₂ : V, x = C₁ * y₁ + C₂ * y₂ := by
  have cut (z : V) (hz : z ∈ J) : ∀ a b : V,
      ∃ y₁ y₂ : V, pof rightMiddle * a * z * b = C₁ * y₁ + C₂ * y₂ := by
    rw [blockUpperIdeal] at hz
    refine TwoSidedIdeal.span_induction (p := fun z _ => ∀ a b : V,
      ∃ y₁ y₂ : V, pof rightMiddle * a * z * b = C₁ * y₁ + C₂ * y₂) ?_ ?_ ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨u, hu, hlt, rfl⟩ a b
      change ∃ y₁ y₂ : V, pof rightMiddle * a * pof u * b = C₁ * y₁ + C₂ * y₂
      by_cases hv : IsViolated u
      · have hp : pof u = 0 := violMk_e hv
        exact ⟨0, 0, by simp only [hp, mul_zero, zero_mul, add_zero]⟩
      have hclass := middleRight_higher_classification u hu hlt hv
      have idem (s : Seq μ₀) : pof s * pof s = pof s := by
        rw [← map_mul, e_mul_self]
      have support : pof rightMiddle * (pof rightMiddle * a * pof u) * pof u =
          pof rightMiddle * a * pof u := by
        calc
          _ = (pof rightMiddle * pof rightMiddle) * a * (pof u * pof u) := by simp only [mul_assoc]
          _ = _ := by rw [idem, idem]
      obtain ⟨l, r, hf⟩ :=
        fiveSlotMiddleRight_viol_corner_two_factors Q Λ hQ u hclass _ support
      exact ⟨l * b, r * b, by rw [hf, add_mul, mul_assoc, mul_assoc]⟩
    · intro a b
      exact ⟨0, 0, by simp only [mul_zero, zero_mul, add_zero]⟩
    · intro u v _ _ hu hv a b
      obtain ⟨l, r, he⟩ := hu a b
      obtain ⟨l', r', he'⟩ := hv a b
      exact ⟨l + l', r + r', by rw [mul_add, add_mul, he, he', mul_add, mul_add]; ac_rfl⟩
    · intro u _ hu a b
      obtain ⟨l, r, he⟩ := hu a b
      exact ⟨-l, -r, by rw [mul_neg, neg_mul, he, neg_add, mul_neg, mul_neg]⟩
    · intro a u _ hu b d
      simpa only [mul_assoc] using hu (b * a) d
    · intro b u _ hu a d
      simpa only [mul_assoc] using hu a (b * d)
  obtain ⟨l, r, h⟩ := cut x hx 1 1
  exact ⟨l, r, by simpa only [mul_one, hl] using h⟩


private theorem middleRight_second_word_on_higher :
    ((ψw [3, 2, 1] * e nearby) * (ψ 2 * e leftExtreme) : R) =
      (ψ 1 * e central) * (ψw [3, 2, 1] * e leftExtreme) := by
  have nearCut : (e nearby : R) * (ψ 2 * e leftExtreme) = ψ 2 * e leftExtreme := by
    rw [ψ_mul_e, ← mul_assoc, e_mul_self]
  have wordStep : wordProd N [3, 2, 1] • leftExtreme = central := by decide +kernel
  have centralCut : (e central : R) * (ψw [3, 2, 1] * e leftExtreme) =
      ψw [3, 2, 1] * e leftExtreme := by
    rw [← wordStep, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  have braidEq : ((ψ 2 * ψ 1 * ψ 2) * e leftExtreme : R) =
      (ψ 1 * ψ 2 * ψ 1) * e leftExtreme := by
    have neq : (leftExtreme).lbl ⟨1, by decide⟩ ≠ (leftExtreme).lbl ⟨3, by decide⟩ := by decide
    have rel := braid (Q := stendhalQ Q Λ) 1 (by decide) leftExtreme
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [Nat.reduceAdd, neq, false_and, ↓reduceIte, sub_mul] using rel
  have commute : (ψ 3 : R) * ψ 1 = ψ 1 * ψ 3 :=
    (ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide)).symm
  rw [mul_assoc, nearCut, mul_assoc, centralCut]
  calc
    _ = ψ 3 * ((ψ 2 * ψ 1 * ψ 2) * e leftExtreme) := by
      simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
    _ = ψ 3 * ((ψ 1 * ψ 2 * ψ 1) * e leftExtreme) := congrArg (ψ 3 * ·) braidEq
    _ = (ψ 3 * ψ 1) * (ψ 2 * ψ 1 * e leftExtreme) := by simp only [mul_assoc]
    _ = _ := by rw [commute]; simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]

/-- The second higher generator sends the nearby loading's higher kernel
into the image of the central crossing. -/
theorem fiveSlotMiddleRight_second_factors_higher_nearby (hQ : KLRSymm Q) (x : V)
    (hx : x ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 nearby) (redWord nearby))
    (hl : pof nearby * x = x) : ∃ y : V, C₂ * x = C₁ * y := by
  obtain ⟨r, _, he⟩ := fiveSlot_jA_higher_exists_leftFactor Q Λ hQ x hx hl
  have he' : F (ψ 2 * e leftExtreme) * r = x := he
  have rep : C₂ * F (ψ 2 * e leftExtreme) = C₁ * F (ψw [3, 2, 1] * e leftExtreme) := by
    simpa only [map_mul] using congrArg F (middleRight_second_word_on_higher Q Λ)
  exact ⟨F (ψw [3, 2, 1] * e leftExtreme) * r, by rw [← he', ← mul_assoc, rep, mul_assoc]⟩


attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord rightMiddle))
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord rightMiddle))
local notation "K" => blockLoadingKernel Q Λ rightMiddle 1 2

/-- Every element of the actual middle-right higher kernel has a two-term
expression with coefficients in the source ordered algebra, cut at the
central and nearby loadings respectively. -/
theorem fiveSlotMiddleRight_blockLoadingKernel_two_factors (hQ : KLRSymm Q) (x : K) :
    ∃ a b : T, pof central * a.1 = a.1 ∧ pof nearby * b.1 = b.1 ∧
      x.1.1.1 = C₁ * a.1 + C₂ * b.1 := by
  let ord := isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord rightMiddle)
  have project (u : Seq μ₀) (hu : redWord u = redWord rightMiddle) (y : V) :
      ∃ r : T, r.1 = pof u * y * E ∧ pof u * r.1 = r.1 := by
    have left : E * pof u = pof u := by
      change E * violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (e u)) = _
      rw [← map_mul, redProj_mul_e, ite_eq_left hu]
      rfl
    have hs : pof u * pof u = pof u := by rw [← map_mul, e_mul_self]
    let r : T := ⟨pof u * y * E, (Subsemigroup.mem_corner_iff ord).2
      ⟨by rw [← mul_assoc, ← mul_assoc, left], by rw [mul_assoc, ord.eq]⟩⟩
    exact ⟨r, rfl, by change pof u * (pof u * y * E) = _; rw [← mul_assoc, ← mul_assoc, hs]⟩
  have left : pof rightMiddle * x.1.1.1 = x.1.1.1 :=
    congrArg (fun z : T => z.1) x.1.2
  have right : x.1.1.1 * E = x.1.1.1 :=
    CornerEndomorphism.corner_mul_right ord x.1.1
  obtain ⟨y, z, hx⟩ := fiveSlotMiddleRight_higher_two_factors Q Λ hQ x.1.1.1 x.2 left
  obtain ⟨a, ha, hpa⟩ := project central (by decide) y
  obtain ⟨b, hb, hpb⟩ := project nearby (by decide) z
  have h₁ : C₁ * pof central = C₁ := by rw [← map_mul, mul_assoc, e_mul_self]
  have h₂ : C₂ * pof nearby = C₂ := by rw [← map_mul, mul_assoc, e_mul_self]
  refine ⟨a, b, hpa, hpb, ?_⟩
  calc
    x.1.1.1 = x.1.1.1 * E := right.symm
    _ = (C₁ * y + C₂ * z) * E := congrArg (· * E) hx
    _ = C₁ * a.1 + C₂ * b.1 := by rw [ha, hb, add_mul, ← mul_assoc C₁, ← mul_assoc C₁, h₁,
      ← mul_assoc C₂, ← mul_assoc C₂, h₂]

end Categorification.Stendhal.BraidedStendhalAlgebra
