/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardInjective
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip

/-!
# A crossing at two consecutive boundary positions

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and the cut after (6.21) in Lemma 6.8.
If the two exchanging red strands are consecutive *positions* at the bottom, every
permutation into the source order has the same available bottom red crossing. Use
reduced words through that crossing on the unviolated and the violated loadings alike.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv MvPolynomial
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "p" => fun j : KLR.Seq μ => raw (e j)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "mk" => violMk k Q Λ ν
local notation "ρ" => canWord m

private theorem pairedWords {n : ℕ} : IsReducedChoice (canWord n) :=
  fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩

/-- With a common reduced top factor for *all* the words from order `κ`, the affine
factorization has no violated-bottom error term. -/
private theorem through_all {g : Perm (Fin m)} {s u : KLR.Seq μ} (hgu : g • u = s)
    {κ : List (Fin ℓ)} (hg : ∀ (j : KLR.Seq μ) (τ : Perm (Fin m)), τ • j = s → redWord j = κ →
      invSet m (g⁻¹ * τ) ⊆ invSet m τ) (w : A) :
    ∃ x : A, p s * w * redProj k Q Λ ν κ = raw (ψw (ρ g) * e u) * x := by
  obtain ⟨v,rfl⟩ := ofKLR_surjective w
  let words := fun τ => ρ (τ * (throughFrame g τ)⁻¹) ++ ρ (throughFrame g τ)
  have hw : IsReducedChoice words := isReducedChoice_through pairedWords g
  let c : R := ψw (ρ g) * e u
  have gen (j : KLR.Seq μ) (hj : redWord j = κ) : e s * v * e j ∈ LinearMap.range (LinearMap.mulLeft k c) := by
    apply (Submodule.span_le.2 ?_) (mem_span_corner' words hw j s (r := e s * v * e j) (by
      simp only [← mul_assoc, e_mul_self]; rw [mul_assoc _ (e j), e_mul_self]))
    rintro _ ⟨τ,d,hτ,rfl⟩
    have hf : throughFrame g τ = g⁻¹ * τ := by simp [throughFrame, hg j τ hτ hj]
    have he : (g⁻¹*τ) • j = u := by rw [mul_smul, hτ, ← hgu, inv_smul_smul]
    have hz := e_mul_std (Q := Q) (Λ := Λ) (ρ (g⁻¹*τ)) (monomial d 1) j
    rw [wordProd_canWord, he] at hz
    refine ⟨ψw (ρ (g⁻¹*τ)) * pol (monomial d 1) * e j, ?_⟩
    change c * _ = ψw (words τ) * pol (monomial d 1) * e j
    rw [show words τ = ρ g ++ ρ (g⁻¹*τ) by simp [words,hf], ψw_append]
    change ψw (ρ g) * e u * _ = _
    rw [mul_assoc, hz]; simp only [mul_assoc]
  have H : e s * v * redIdem k Q Λ κ ∈ LinearMap.range (LinearMap.mulLeft k c) := by
    rw [redIdem, Finset.mul_sum]
    exact Submodule.sum_mem _ fun j hj => gen j (Finset.mem_filter.1 hj).2
  obtain ⟨x,hx⟩ := H
  exact ⟨raw x, by simpa only [c,map_mul,redProj,LinearMap.mulLeft_apply] using (congrArg raw hx).symm⟩

variable {u : KLR.Seq (stendhalWeight ℓ ν)} {n : ℕ} {a b : Fin ℓ} {L M : List (Fin ℓ)}
local notation "g" => sadj m n
local notation "s" => g • u
local notation "E" => redProj k Q Λ ν (L ++ a :: b :: M)
local notation "c" => raw (ψw (ρ g) * e u)

omit [DecidableEq I] in
private theorem ascent_at_pair (hn : n+1 < m) (ha : u.lbl ⟨n,by omega⟩ = .inr a)
    (hb : u.lbl ⟨n+1,hn⟩ = .inr b) (j : KLR.Seq μ) (w : Perm (Fin m))
    (hj : redWord j = L ++ a :: b :: M) (hw : w • j = u) :
    invSet m w ⊆ invSet m (g*w) := by
  apply invSet_subset_sadj_mul hn
  apply lt_of_redWord_eq_append hj
  · simpa only [← hw,lbl_smul] using ha
  · simpa only [← hw,lbl_smul] using hb

/-- PBW division at a bottom loading with the two reds in consecutive positions.
The coefficient is in the ordered affine column. Right multiplication by this same
crossing detects its coefficient modulo global violations when the affine product is zero. -/
theorem exists_pairedRedColumn (hQ : KLRSymm Q) (hn : n+1 < m)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,hn⟩ = .inr b)
    (hu : redWord u = L ++ a :: b :: M) :
    ∃ C : A, E * C = C ∧ C * p s = C ∧
      (∀ w : A, ∃ d : A, E*d = d ∧ d*E = d ∧ d*p u = d ∧ E*w*p s = d*C) ∧
      ∀ d : A, E*d = d → d*p u = d → d*C = 0 → mk d = 0 := by
  have cu : c * p u = c := by rw [← map_mul, mul_assoc, e_mul_self]
  have sc : p s * c = c := e_mul_psi_e pairedWords rfl
  have ue : p u * E = p u := (e_mul_redProj _ _).trans (ite_eq_left hu)
  have ce : c * E = c := by rw [← cu, mul_assoc, ue]
  refine ⟨flip c, by simpa only [flip_mul,flip_redProj] using congrArg flip ce,
    by simpa only [flip_mul,flip_e] using congrArg flip sc, ?_, ?_⟩
  · intro w
    have hg (j : KLR.Seq μ) (τ : Perm (Fin m)) (hτ : τ • j = s) (hj : redWord j = L ++ a :: b :: M) :
        invSet m (g⁻¹*τ) ⊆ invSet m τ := by
      have H := ascent_at_pair hn ha hb j (g⁻¹*τ) hj (by rw [mul_smul,hτ,inv_smul_smul])
      rwa [mul_inv_cancel_left] at H
    obtain ⟨z,hz⟩ := through_all (Q := Q) (Λ := Λ) (u := u) («g» := g) rfl hg (flip w)
    have h := congrArg flip hz
    simp only [flip_mul,flip_e,flip_redProj,flip_flip] at h
    let d := E * flip z * p u
    have hl : E*d = d := by simp only [d, ← mul_assoc, (isIdempotentElem_redProj _).eq]
    have hr : d*p u = d := by simp only [d,mul_assoc,← map_mul,e_mul_self]
    refine ⟨d,hl,by simp only [d,mul_assoc,ue],hr,?_⟩
    have uc : p u * flip c = flip c := by simpa only [flip_mul,flip_e] using congrArg flip cu
    have eh : E * (flip z * flip c) = flip z * flip c := by
      rw [← h]; simp only [← mul_assoc,(isIdempotentElem_redProj _).eq]
    simpa only [d, mul_assoc, uc, eh] using (show E*w*p s = flip z * flip c from by simpa only [mul_assoc] using h)
  · intro d hd hu' hz
    have h₁ : flip d * E = flip d := by simpa only [flip_mul,flip_redProj] using congrArg flip hd
    have h₂ : p u * flip d = flip d := by simpa only [flip_mul,flip_e] using congrArg flip hu'
    have h₃ : c * flip d = 0 := by simpa only [flip_mul,flip_flip,flip_zero] using congrArg flip hz
    have hdif := throughMap_braid_sub_mem (Q := Q) (Λ := Λ) («s» := s) (t := u) (κ := L ++ a :: b :: M) pairedWords hQ g rfl
      (fun j σ hσ hj _ => ascent_at_pair hn ha hb j σ hj hσ) (flip d)
    rw [h₃, zero_mul, map_zero, h₂, h₁, zero_sub] at hdif
    apply (violMk_eq_zero_iff _).2
    have := flip_mem_violIdeal (mem_violIdeal_of_mem_violBottom (neg_mem hdif))
    simpa only [neg_neg, flip_flip] using this

end Categorification.Stendhal.BraidedStendhalAlgebra
