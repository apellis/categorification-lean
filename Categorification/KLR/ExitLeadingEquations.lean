/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree

/-!
# The highest crossing degree of a family of local exits

For the local affine relations in Webster, arXiv:1309.3796v2, §6.1, proof after
(6.21), concatenate the upper crossing word and the exit leg. At the highest
crossing degree, reduced concatenations with the same output permutation
contribute their top polynomials to the same equation. Nonreduced concatenations
drop in the crossing filtration. No restriction on colours is needed.
-/

namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial
noncomputable section

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {ν : Multiset I} (hQ : KLRSymm Q)
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "S" => Perm (Fin m)
local notation "P" => MvPolynomial (Fin m) k
local notation "B" => basisOfSymm (ν := ν) hQ (TypeA.canWord m)
  (fun w => And.intro (isReduced_canWord _ w) (wordProd_canWord _ w))

private def wordCoefficient (t : S) : R →ₗ[k] P :=
  (B).constr k fun a => if a.2.1 = t then monomial a.2.2 1 else 0

private theorem wordCoefficient_monomial (t w : S) (s : Seq ν) (d : Fin m →₀ ℕ) :
    wordCoefficient hQ t (ψw (TypeA.canWord m w) * pol (monomial d 1) * e s) =
      if w = t then monomial d 1 else 0 := by
  calc
    _ = wordCoefficient hQ t ((B) (s,w,d)) :=
      congrArg (wordCoefficient hQ t) (basisOfSymm_apply _ _ _ (s,w,d)).symm
    _ = _ := (B).constr_basis k _ (s,w,d)

private theorem wordCoefficient_polynomial (t w : S) (s : Seq ν) (f : P) :
    wordCoefficient hQ t (ψw (TypeA.canWord m w) * pol f * e s) = if w = t then f else 0 := by
  let atWord := (LinearMap.mulRight k (e s : R)).comp
    ((LinearMap.mulLeft k (ψw (TypeA.canWord m w) : R)).comp pol.toLinearMap)
  by_cases ht : w = t
  · rw [ite_eq_left ht]
    have eq : (wordCoefficient hQ t).comp atWord = LinearMap.id := by
      apply (basisMonomials (Fin m) k).ext
      intro d
      exact (wordCoefficient_monomial hQ t w s d).trans (ite_eq_left ht)
    exact LinearMap.congr_fun eq f
  · rw [ite_eq_right ht]
    have eq : (wordCoefficient hQ t).comp atWord = 0 := by
      apply (basisMonomials (Fin m) k).ext
      intro d
      exact (wordCoefficient_monomial hQ t w s d).trans (ite_eq_right ht)
    exact LinearMap.congr_fun eq f

private theorem wordCoefficient_lower (t : S) {d : ℕ} (ht : d < length m t) {x : R}
    (hx : x ∈ filt k Q ν d) : wordCoefficient hQ t x = 0 := by
  rw [filt_eq_span (fun _ _ h h' e => braidEquiv_of_isReduced h h' e)
    (fun _ hv hr => exists_braidEquiv_hasRepeat_of_not_isReduced hv hr) (TypeA.canWord m)
    (fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩) d] at hx
  change x ∈ LinearMap.ker (wordCoefficient hQ t)
  apply (Submodule.span_le.2 ?_) hx
  rintro _ ⟨w,a,s,hw,rfl⟩
  exact (wordCoefficient_polynomial hQ t w s _).trans (ite_eq_right (fun he => (he ▸ hw).not_gt ht))

private theorem wordCoefficient_high (t : S) {d : ℕ} (ht : d < length m t)
    (l : List ℕ) (hl : ValidWord m l) (hlen : l.length ≤ d+1) (s : Seq ν) (f : P) :
    wordCoefficient hQ t (ψw l * pol f * e s) = if wordProd m l = t then f else 0 := by
  by_cases small : l.length ≤ d
  · have zl := wordCoefficient_lower hQ t ht (mem_filt hl small f s)
    rw [zl,ite_eq_right (fun he => ht.not_ge ((length_le_of_wordProd_eq hl he).trans small))]
  have eq : l.length = d+1 := by omega
  by_cases red : IsReduced m l
  · have bra := braidEquiv_of_isReduced red (isReduced_canWord _ (wordProd m l)) (wordProd_canWord _ _).symm
    have diff := sub_mul_mem_of_braidEquiv (k := k) (Q := Q) (ν := ν) bra f s
    rw [eq,Nat.add_sub_cancel,sub_mul,sub_mul] at diff
    have z := wordCoefficient_lower hQ t ht diff
    rw [map_sub,sub_eq_zero] at z
    exact z.trans (wordCoefficient_polynomial hQ t _ s f)
  · obtain ⟨b,he,hr⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hl red
    have low := gen_mem_of_hasRepeat (k := k) (Q := Q) (ν := ν) hr f s
    have diff := sub_mul_mem_of_braidEquiv (k := k) (Q := Q) (ν := ν) he f s
    rw [← length_eq_of_braidEquiv he,eq,Nat.add_sub_cancel] at low
    rw [eq,Nat.add_sub_cancel,sub_mul,sub_mul] at diff
    have sum := add_mem diff low
    rw [sub_add_cancel] at sum
    rw [wordCoefficient_lower hQ t ht sum,ite_eq_right]
    intro hw
    apply red
    refine ⟨hl,?_⟩
    have le := length_le_of_wordProd_eq hl hw
    rw [hw]
    omega

private theorem hflip_mem_crossingFilt {d : ℕ} {x : R} (hx : x ∈ filt k Q ν d) :
    hflip x ∈ filt k Q ν d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l,f,s,hl,hlen,rfl⟩ := hx
    simp only [hflip_mul,hflip_e,hflip_pol,hflip_ψw]
    apply e_mul_mem
    apply pol_mul_mem
    have hy := ψw_mul_mem l.reverse (one_mem_filt (k := k) (Q := Q) (ν := ν) 0)
    rw [List.length_reverse,Nat.add_zero,mul_one] at hy
    exact filt_mono hlen hy
  | zero => simp only [hflip_zero,zero_mem]
  | add _ _ _ _ h₁ h₂ => rw [hflip_add]; exact add_mem h₁ h₂
  | smul _ _ _ hh => rw [hflip_smul]; exact Submodule.smul_mem _ _ hh

/-- At an output permutation above degree `d`, a word of length at most `d+1`
contributes precisely its top polynomial if it gives that permutation. -/
private theorem read_high (t : S) {d : ℕ} (ht : d < length m t) (l : List ℕ) (hl : ValidWord m l)
    (hlen : l.length ≤ d+1) (f : P) (s : Seq ν) :
    wordCoefficient hQ t⁻¹ (hflip (pol f * ψw l * e s)) = if wordProd m l = t then f else 0 := by
  rw [hflip_mul,hflip_mul,hflip_pol,hflip_e,hflip_ψw,← mul_assoc,e_mul_ψw,wordProd_reverse,inv_inv,
    mul_assoc,(e_commute_pol _ f).eq,← mul_assoc]
  have high : d < length m t⁻¹ := by rwa [length_inv]
  rw [wordCoefficient_high hQ _ high _ (validWord_reverse.2 hl) (by simpa using hlen),
    wordProd_reverse]
  simp only [inv_inj]

include hQ in
/-- In a relation of local exits, all highest-degree contributions at the same
output permutation must sum to zero, including when black colours coincide. -/
private theorem exit_leading_polynomial_sum_eq_zero {η : Type*} (A : Finset η) {d : ℕ} (s : Seq ν)
    (words : η → List ℕ) (f : η → P) (valid : ∀ a ∈ A, ValidWord m (words a))
    (bound : ∀ a ∈ A, (words a).length ≤ d+1)
    (lower : (∑ a ∈ A, pol (f a) * ψw (words a) * e s : R) ∈ filt k Q ν d)
    (t : S) (ht : d < length m t) : ∑ a ∈ A, (if wordProd m (words a) = t then f a else 0) = 0 := by
  have hh := hflip_mem_crossingFilt lower
  rw [hflip_sum] at hh
  have hz := wordCoefficient_lower hQ t⁻¹ (by rwa [length_inv]) hh
  rw [map_sum] at hz
  rwa [Finset.sum_congr rfl fun a ha => read_high hQ t ht _ (valid a ha) (bound a ha) (f a) s] at hz

private theorem word_model_error {d : ℕ} (l : List ℕ) (hl : ValidWord m l) (hbound : l.length ≤ d+1)
    (f : P) (s : Seq ν) :
    let w := wordProd m l
    (pol f * ψw l * e s : R) - (if d < length m w then pol f * ψw (TypeA.canWord m w) * e s else 0)
      ∈ filt k Q ν d := by
  intro w
  have hs : (e s : R) ∈ filt k Q ν 0 := by simpa only [map_one,one_mul] using pol_mul_e_mem (Q := Q) (1 : P) s 0
  have bound : l.length - 1 ≤ d := by omega
  by_cases hh : d < length m w
  · rw [ite_eq_left hh]
    have hlen : length m w ≤ l.length := length_le_of_wordProd_eq hl rfl
    have red : IsReduced m l := ⟨hl,by change l.length = length m w; omega⟩
    have bra := braidEquiv_of_isReduced red (isReduced_canWord m w) (wordProd_canWord m w).symm
    have diff := sub_mem_of_braidEquiv bra hs
    rw [Nat.add_zero] at diff
    exact filt_mono bound (by simpa only [mul_sub,mul_assoc] using pol_mul_mem f diff)
  · rw [ite_eq_right hh,sub_zero,mul_assoc]
    apply pol_mul_mem
    by_cases small : l.length ≤ d
    · simpa only [map_one,mul_one] using mem_filt (Q := Q) hl small (1 : P) s
    · have nred : ¬ IsReduced m l := fun hr => hh (by rw [← show l.length = length m w from hr.2]; omega)
      obtain ⟨b,bra,rep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hl nred
      have low := mul_mem_of_hasRepeat rep hs
      rw [← length_eq_of_braidEquiv bra] at low
      have sum := add_mem (sub_mem_of_braidEquiv bra hs) low
      rw [sub_add_cancel,Nat.add_zero] at sum
      exact filt_mono bound sum

include hQ in
/-- The highest crossing-degree equations present the affine exit kernel modulo
lower crossing degree. For each output permutation, add the upper polynomials
of all length-additive cuts giving that permutation. -/
private theorem exit_leading_polynomial_iff {η : Type*} (A : Finset η) {d : ℕ} (s : Seq ν)
    (words : η → List ℕ) (f : η → P) (valid : ∀ a ∈ A, ValidWord m (words a))
    (bound : ∀ a ∈ A, (words a).length ≤ d+1) :
    (∑ a ∈ A, pol (f a) * ψw (words a) * e s : R) ∈ filt k Q ν d ↔
      ∀ t : S, d < length m t → (∑ a ∈ A, if wordProd m (words a) = t then f a else 0) = 0 := by
  classical
  constructor
  · exact exit_leading_polynomial_sum_eq_zero hQ A s words f valid bound
  intro eqs
  let v (a : η) := wordProd m (words a)
  let row (t : S) : P →ₗ[k] R := (LinearMap.mulRight k (e s : R)).comp
    ((LinearMap.mulRight k (ψw (TypeA.canWord m t) : R)).comp pol.toLinearMap)
  let normal (a : η) := if d < length m (v a) then row (v a) (f a) else 0
  have ga (a : η) : normal a = ∑ t : S, if d < length m t ∧ v a = t then row t (f a) else 0 := by
    rw [Finset.sum_eq_single (v a)]
    · simp only [normal,and_true]
    · intro t _ ht; exact ite_eq_right (fun h => ht h.2.symm)
    · simp
  have zr : (∑ a ∈ A, normal a) = 0 := by
    rw [Finset.sum_congr rfl (fun a _ => ga a),Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases high : d < length m t
    · calc _ = ∑ a ∈ A, row t (if v a = t then f a else 0) := by
                apply Finset.sum_congr rfl
                intro a _
                by_cases he : v a = t <;> simp [high,he]
           _ = row t (∑ a ∈ A, if v a = t then f a else 0) := (map_sum _ _ _).symm
           _ = 0 := (congrArg (row t) (eqs t high)).trans (map_zero _)
    · simp [high]
  have err := (filt k Q ν d).sum_mem fun a ha => word_model_error (Q := Q) (words a) (valid a ha) (bound a ha) (f a) s
  change (∑ a ∈ A, (pol (f a) * ψw (words a) * e s - normal a : R)) ∈ _ at err
  rwa [Finset.sum_sub_distrib,zr,sub_zero] at err

include hQ in
/-- For the affine exit relations in Webster, arXiv:1309.3796v2, §6.1, proof of
Lemma 6.8 after (6.21), take one crossing degree above the lower filtration.
For upper PBW rows multiplied by their supported exit legs, the equation in
crossing degree `d+1` is the polynomial sum at each output permutation.
Lower-degree corrections from braids, equal colours and bigons are retained in
the filtration step `d`. -/
theorem exit_products_leading_iff {η : Type*} (A : Finset η) {d : ℕ} (s : Seq ν)
    (upper leg : η → List ℕ) (f : η → P)
    (hu : ∀ a ∈ A, ValidWord m (upper a)) (hv : ∀ a ∈ A, ValidWord m (leg a))
    (bound : ∀ a ∈ A, (upper a).length + (leg a).length ≤ d+1) :
    (∑ a ∈ A, (pol (f a) * ψw (upper a) * e (wordProd m (leg a) • s)) * (ψw (leg a) * e s) : R)
        ∈ filt k Q ν d ↔
      ∀ t : S, d < length m t →
        (∑ a ∈ A, if wordProd m (upper a) * wordProd m (leg a) = t then f a else 0) = 0 := by
  have cut (a : η) : e (wordProd m (leg a) • s) * (ψw (leg a) * e s : R) = ψw (leg a) * e s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have row (a : η) : (pol (f a) * ψw (upper a) * e (wordProd m (leg a) • s)) * (ψw (leg a) * e s : R) =
      pol (f a) * ψw (upper a ++ leg a) * e s := by
    rw [mul_assoc _ (e _),cut,ψw_append]
    simp only [mul_assoc]
  rw [Finset.sum_congr rfl (fun a _ => row a)]
  simpa only [wordProd_append] using exit_leading_polynomial_iff hQ A s (fun a => upper a ++ leg a) f
    (fun a ha => validWord_append.2 ⟨hu a ha,hv a ha⟩) (fun a ha => by simpa using bound a ha)

end
end Categorification.KLR.KLRAlgebra
