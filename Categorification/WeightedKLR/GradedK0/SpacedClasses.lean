/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.DividedPowers
import Categorification.WeightedKLR.GradedK0.Idempotents
import Categorification.WeightedKLR.GradedK0.Algebra
import Categorification.WeightedKLR.GradedK0.ScalarExtension
import Categorification.KLR.KL2.Gamma2

/-!
# Spaced loading classes in the weighted Grothendieck algebra

Webster, arXiv:1209.2463v4, §2.4, Definition 2.17 and Theorem 2.19. Induction
concatenates the classes of ordinary words at their evenly spaced loadings.
The divided-power classes use the normalization of Khovanov–Lauda I,
arXiv:0803.4121v2, §2.5, and Khovanov–Lauda II, arXiv:0804.2080v1, §3.
The factorial identity identifies their products after extension of scalars,
and freeness of projective Grothendieck groups over the Laurent polynomial
ring gives equality in the integral Grothendieck algebra over a field.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR Categorification.KLR.KL2
  LaurentPolynomial QuantumGroup GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

variable (G : GradingDatum Γ)

/-- The class of an ordinary word at its spaced loading, in the Grothendieck algebra. -/
def spacedClsSeq (l : List I) : G.K0W :=
  DirectSum.of G.K0fam (l : Multiset I).toFinsupp
    (K0.of (G.spacedProjSeq (KLRAlgebra.Seq.ofList l rfl)))

theorem spacedClsSeq_eq {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    G.spacedClsSeq l = DirectSum.of G.K0fam ν.toFinsupp
      (K0.of (G.spacedProjSeq (KLRAlgebra.Seq.ofList l h))) := by
  subst h
  rfl

variable (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

local notation "Gs" => hS.gradingDatum

/-- The normalized divided-power class of a word, in the Grothendieck algebra. -/
def spacedClsDiv (d : List (I × ℕ)) : (Gs).K0W :=
  DirectSum.of (Gs).K0fam (KLRAlgebra.expandDiv d : Multiset I).toFinsupp
    (K0.of (spacedProjDiv hS hD hne hl d rfl))

theorem spacedClsDiv_eq {ν : Multiset I} (d : List (I × ℕ))
    (h : (KLRAlgebra.expandDiv d : Multiset I) = ν) :
    spacedClsDiv hS hD hne hl d =
      DirectSum.of (Gs).K0fam ν.toFinsupp (K0.of (spacedProjDiv hS hD hne hl d h)) := by
  subst h
  rfl

/-- The factorial identity in the direct sum of the weighted Grothendieck groups,
from KL I, arXiv:0803.4121v2, §2.5, and Webster, arXiv:1209.2463v4, Proposition 2.14. -/
theorem spacedClsSeq_expandDiv (d : List (I × ℕ)) :
    (Gs).spacedClsSeq (KLRAlgebra.expandDiv d) =
      divQFact2 hS.cartanDatum d • spacedClsDiv hS hD hne hl d := by
  rw [spacedClsSeq, spacedClsDiv, K0_spacedProjSeq_expandDiv hS hD hne hl d rfl,
    K0W_of_smul]

private theorem of_ofIdempotent_cast {ν μ : I →₀ ℕ} (h : ν = μ)
    {e : WeightedKLRAlgebra k Γ ν} {f : WeightedKLRAlgebra k Γ μ}
    (heq : castW k Γ h e = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (he0 : e ∈ G.klrGrade ν 0) (hf0 : f ∈ G.klrGrade μ 0) :
    DirectSum.of G.K0fam ν (K0.of (GProj.ofIdempotent e he he0)) =
      DirectSum.of G.K0fam μ (K0.of (GProj.ofIdempotent f hf hf0)) := by
  subst h
  change e = f at heq
  exact congrArg (DirectSum.of G.K0fam ν) (K0.of_ofIdempotent_congr heq he hf he0 hf0)

private theorem of_indK0_spacedProjSeq {ν μ : Multiset I} (t : Seq ν) (u : Seq μ) :
    DirectSum.of G.K0fam (ν.toFinsupp + μ.toFinsupp)
        (G.indK0 ν.toFinsupp μ.toFinsupp (K0.of (G.spacedProjSeq t)) (K0.of (G.spacedProjSeq u))) =
      DirectSum.of G.K0fam (ν + μ).toFinsupp (K0.of (G.spacedProjSeq (t.finAppend u))) := by
  have ht : spacedW k Γ t ∈ G.klrGrade ν.toFinsupp 0 := G.e_mem_grade (spacedFull Γ t)
  have hu : spacedW k Γ u ∈ G.klrGrade μ.toFinsupp 0 := G.e_mem_grade (spacedFull Γ u)
  have hit := isIdempotentElem_spacedW (k := k) (Γ := Γ) t
  have hiu := isIdempotentElem_spacedW (k := k) (Γ := Γ) u
  calc
    _ = _ := congrArg (DirectSum.of G.K0fam _) (G.indK0_ofIdempotent hit hiu ht hu)
    _ = _ := G.of_ofIdempotent_cast (Seq.toFinsupp_add ν μ) (inductionMap_spacedW t u)
      (inductionMap_idem hit hiu) (isIdempotentElem_spacedW (t.finAppend u))
      (G.inductionMap_mem_grade_zero ht hu) (G.e_mem_grade (spacedFull Γ (t.finAppend u)))

omit [DecidableEq I] in
private theorem seq_ofList_finAppend (l l' : List I)
    (h : ((l ++ l' : List I) : Multiset I) = (l : Multiset I) + (l' : Multiset I)) :
    KLRAlgebra.Seq.ofList (l ++ l') h =
      (KLRAlgebra.Seq.ofList l rfl).finAppend (KLRAlgebra.Seq.ofList l' rfl) := by
  rw [KLGamma.seq_ofList_append]
  let t : Seq (l : Multiset I) := KLRAlgebra.Seq.ofList l rfl
  let u : Seq (l' : Multiset I) := KLRAlgebra.Seq.ofList l' rfl
  change t.append u = t.finAppend u
  apply Subtype.ext
  funext a
  obtain ⟨b, rfl⟩ :=
    (TypeA.blockEquiv (Seq.card_add' (l : Multiset I) (l' : Multiset I))).surjective a
  rcases b with x | y
  · change (t.append u).1 (Seq.posL _ x) = (t.finAppend u).1 (Seq.posL _ x)
    rw [Seq.append_posL, show Seq.posL (l' : Multiset I) x = Seq.inlPos x from Fin.ext rfl,
      Seq.finAppend_inlPos]
  · change (t.append u).1 (Seq.posR _ y) = (t.finAppend u).1 (Seq.posR _ y)
    rw [Seq.append_posR, show Seq.posR (l : Multiset I) y = Seq.inrPos y from Fin.ext rfl,
      Seq.finAppend_inrPos]

/-- Juxtaposition of evenly spaced loadings gives the concatenation product
of their classes, by the induction of Webster, arXiv:1209.2463v4, Definition 2.17
and Theorem 2.19. -/
theorem spacedClsSeq_append (l l' : List I) :
    G.spacedClsSeq (l ++ l') = G.spacedClsSeq l * G.spacedClsSeq l' := by
  rw [G.spacedClsSeq_eq (l ++ l') (Multiset.coe_add l l').symm, seq_ofList_finAppend]
  rw [spacedClsSeq, spacedClsSeq, G.K0W_of_mul_of, G.of_indK0_spacedProjSeq]

/-- The empty spaced loading represents the unit of the Grothendieck algebra. -/
theorem spacedClsSeq_nil : G.spacedClsSeq [] = 1 := by
  rw [G.K0W_one, spacedClsSeq]
  apply congrArg (DirectSum.of G.K0fam 0)
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso]
  exact K0.of_ofIdempotent_congr (one_eq_spacedW_nil (k := k) (Γ := Γ)).symm _ _ _ _

theorem spacedClsSeq_replicate (i : I) (n : ℕ) :
    G.spacedClsSeq (List.replicate n i) = G.spacedClsSeq [i] ^ n := by
  induction n with
  | zero => simpa only [List.replicate_zero, pow_zero] using G.spacedClsSeq_nil
  | succ n ih =>
    rw [List.replicate_succ, show i :: List.replicate n i = [i] ++ List.replicate n i from rfl,
      G.spacedClsSeq_append, ih, pow_succ']

/-- The single-letter class is the regular module of the one-strand algebra. -/
theorem spacedClsSeq_single (i : I) :
    G.spacedClsSeq [i] = DirectSum.of G.K0fam (Finsupp.single i 1)
      (K0.of (GProj.regular (G.klrGrade (Finsupp.single i 1)))) := by
  rw [← Multiset.toFinsupp_singleton i, spacedClsSeq]
  apply congrArg (DirectSum.of G.K0fam (↑[i] : Multiset I).toFinsupp)
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso]
  exact K0.of_ofIdempotent_congr (one_eq_spacedW_single (k := k) (Γ := Γ) i).symm _ _ _ _

/-- The first divided power is the corresponding single-letter class. -/
theorem spacedClsDiv_single_one (i : I) :
    spacedClsDiv hS hD hne hl [(i, 1)] = (Gs).spacedClsSeq [i] := by
  have h := spacedClsSeq_expandDiv hS hD hne hl [(i, 1)]
  simpa [KLRAlgebra.expandDiv, divQFact2] using h.symm

/-- The empty divided-power word represents the unit. -/
theorem spacedClsDiv_nil : spacedClsDiv hS hD hne hl [] = 1 := by
  have h := spacedClsSeq_expandDiv hS hD hne hl []
  simpa [KLRAlgebra.expandDiv, divQFact2, spacedClsSeq_nil] using h.symm

end Categorification.WeightedKLR.GradingDatum

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR Categorification.KLR.KL2 QuantumGroup

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

local notation "Gs" => hS.gradingDatum

/-- The factorial identity for a single divided power after extension of scalars,
in the form used in the integral map of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem toK0Q_spacedClsDiv_factorial (i : I) (n : ℕ) :
    (Gs).toK0Q (spacedClsDiv hS hD hne hl [(i, 1)]) ^ n =
      qfact (PreF.vi hS.cartanDatum.dot vQ i) n •
        (Gs).toK0Q (spacedClsDiv hS hD hne hl [(i, n)]) := by
  have h := spacedClsSeq_expandDiv hS hD hne hl [(i, n)]
  simp only [KLRAlgebra.expandDiv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    divQFact2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [spacedClsSeq_replicate, ← spacedClsDiv_single_one hS hD hne hl] at h
  have h' := congrArg (Gs).toK0Q h
  rw [map_pow, toK0Q_smul, KL2Gamma.qToV_qfact_tUnit] at h'
  exact h'

/-- The class of a concatenation of divided-power words is their induction product.
This is the multiplication used for the map of Webster, arXiv:1209.2463v4,
Theorem 2.19, with the divided-power normalization of KL I §2.5 and KL II §3. -/
theorem spacedClsDiv_append (d d' : List (I × ℕ)) :
    spacedClsDiv hS hD hne hl (d ++ d') =
      spacedClsDiv hS hD hne hl d * spacedClsDiv hS hD hne hl d' := by
  have h := spacedClsSeq_expandDiv hS hD hne hl (d ++ d')
  rw [expandDiv_append, spacedClsSeq_append, spacedClsSeq_expandDiv,
    spacedClsSeq_expandDiv, divQFact2_append] at h
  have h' := congrArg (Gs).toK0Q h
  rw [map_mul, toK0Q_smul, toK0Q_smul, toK0Q_smul, map_mul, smul_mul_smul_comm] at h'
  have hn := mul_ne_zero (KL2Gamma.qToV_divQFact2_ne_zero hS.cartanDatum d)
    (KL2Gamma.qToV_divQFact2_ne_zero hS.cartanDatum d')
  have hZ : Γ.NoZeroLoops := fun e he => (hne e he).elim
  have : ∀ ν : I →₀ ℕ, HasGdim ((Gs).klrGrade ν) :=
    fun ν => GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD hZ hS
  apply (Gs).toK0Q_injective
  rw [map_mul]
  exact (smul_right_injective _ hn h').symm

end Categorification.WeightedKLR.GradingDatum
