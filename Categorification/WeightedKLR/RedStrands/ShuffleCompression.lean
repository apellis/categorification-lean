/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalParameters
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.KLR.Symmetries

/-!
# Cancellation at affine Stendhal boundaries

Webster, arXiv:1309.3796v2, Lemma 4.17 and its application in Lemma 4.26.
Right multiplication by a black dot increments one exponent in the affine
basis of Proposition 4.16. Relation (4.2) then cancels mixed crossings.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial StendhalAlgebraAllOrders
open Categorification.WeightedKLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
    {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
local notation "B" => {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}

private def increment (s : Seq μ) (a : Fin m) (ha : (s.lbl a).isLeft) (b : B) : B := by
  classical
  by_cases h : b.val.1 = s
  · refine ⟨(b.val.1, b.val.2.1, b.val.2.2 + Finsupp.single a 1),
      b.property.1, b.property.2.1, ?_, b.property.2.2.2⟩
    intro p hp
    by_cases he : p = a
    · subst p; simpa [h] using ha
    · apply b.property.2.2.1
      simpa [Finsupp.mem_support_iff, Finsupp.single_apply, Ne.symm he] using hp
  · exact b

private theorem increment_injective (s : Seq μ) (a : Fin m) (ha : (s.lbl a).isLeft) :
    Function.Injective (increment (ρ := ρ) s a ha) := by
  classical
  rintro ⟨⟨i, w, u⟩, h⟩ ⟨⟨j, v, t⟩, h'⟩ he
  apply Subtype.ext
  replace he := congrArg Subtype.val he
  by_cases hi : i = s <;> by_cases hj : j = s <;>
    simp_all [increment]

private theorem mul_dot_term (s : Seq μ) (hs : IsRedOrdered s) (a : Fin m)
    (ha : (s.lbl a).isLeft) (hρ : ∀ w, wordProd m (ρ w) = w) (b : B) :
    (stendhalTerm Q Λ hρ b).val * (e s * x a + (1 - e s)) =
      (stendhalTerm Q Λ hρ (increment s a ha b)).val := by
  classical
  have cut := congrArg Subtype.val (stendhalTerm_mul_e (Q := Q) (Λ := Λ) hρ b s hs)
  change (stendhalTerm Q Λ hρ b).val * e s = _ at cut
  rw [mul_add, ← mul_assoc, mul_sub, mul_one, cut]
  by_cases hb : b.val.1 = s
  · simp only [hb, ite_true, sub_self, add_zero]
    change π (KLRAlgebra.stdElt ρ b.val) * π (KLRAlgebra.x a) = _
    rw [← map_mul]
    apply congrArg π
    change KLRAlgebra.stdElt ρ b.val * KLRAlgebra.x a =
      KLRAlgebra.stdElt ρ (increment s a ha b).val
    simp only [increment, hb, ↓reduceDIte, KLRAlgebra.stdElt]
    rw [mul_assoc _ (KLRAlgebra.e _), KLRAlgebra.e_mul_x, ← mul_assoc, mul_assoc _ _ (KLRAlgebra.x _),
      ← KLRAlgebra.pol_X, ← map_mul, X, monomial_mul_monomial, mul_one]
  · simp [hb, increment]

private theorem cancel_black_dot
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hind : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (s : Seq μ) (hs : IsRedOrdered s) (a : Fin m) (ha : (s.lbl a).isLeft)
    (z : T) (hz : z.val * e s = z.val) (hzero : z.val * x a = 0) : z = 0 := by
  let F : T →ₗ[k] A := (LinearMap.mulRight k (e s * x a + (1 - e s))).comp stendhalValₗ
  let terms := stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)
  have hi : LinearIndependent k (stendhalValₗ ∘ terms) :=
    hind.map' _ (LinearMap.ker_eq_bot.mpr stendhalValₗ_injective)
  have h : F ∘ terms = (stendhalValₗ ∘ terms) ∘ increment s a ha := by
    funext b; exact mul_dot_term s hs a ha (fun w => (hρ w).2) b
  have hF : Function.Injective F := LinearMap.injective_of_linearIndependent
    (top_unique (span_stendhalTerm hρ)) (h.symm ▸ hi.comp _ (increment_injective s a ha))
  apply hF
  rw [map_zero]
  change z.val * (e s * x a + (1 - e s)) = 0
  rw [mul_add, ← mul_assoc, mul_sub, mul_one, hz, hzero, sub_self, add_zero]

private theorem projection_val_of_support {s : Seq μ} (hs : IsRedOrdered s) (z : A)
    (hz : z * e s = z) : (orderProjection Q Λ ν z).val = z := by
  change z * redOrderedIdem k Q Λ ν = z
  conv_lhs => lhs; rw [← hz]
  rw [mul_assoc, e_mul_redOrderedIdem, ite_eq_left hs, hz]

private theorem cancel_black_dot_all
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hind : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (s : Seq μ) (hs : IsRedOrdered s) (a : Fin m) (ha : (s.lbl a).isLeft)
    (z : A) (hz : z * e s = z) (hzero : z * x a = 0) : z = 0 := by
  let t := orderProjection Q Λ ν z
  have ht : t.val = z := projection_val_of_support hs z hz
  have h := cancel_black_dot hρ hind s hs a ha t (by simpa only [ht] using hz)
    (by simpa only [ht] using hzero)
  exact ht.symm.trans (congrArg Subtype.val h)

private theorem cancel_mixed_right
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hind : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (s : Seq μ) (hs : IsRedOrdered s) (j : ℕ) (hj : j + 1 < m)
    {i : I} {r : Fin ℓ} (hi : s.lbl ⟨j, by omega⟩ = .inl i)
    (hr : s.lbl ⟨j+1, hj⟩ = .inr r) (z : A) (hz : z * e s = z)
    (hzero : z * ψ j = 0) : z = 0 := by
  let a : Fin m := ⟨j, by omega⟩
  have hc : Commute (e s : A) (x a) :=
    (Commute.map (show Commute (KLRAlgebra.x a) (KLRAlgebra.e s) from
      KLRAlgebra.x_mul_e a s) π).symm
  have hcanc (n : ℕ) (hn : z * x a ^ n = 0) : z = 0 := by
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      apply cancel_black_dot_all hρ hind s hs a (by change (s.lbl ⟨j,_⟩).isLeft; simp [hi])
      · rw [mul_assoc, ← (hc.pow_right n).eq, ← mul_assoc, hz]
      · simpa only [pow_succ, mul_assoc] using hn
  apply hcanc (Λ r i)
  have hbig := ψ_sq_black_red (k := k) (Q := Q) (Λ := Λ) j hj s i r hi hr
  change ψ j * ψ j * e s = x a ^ Λ r i * e s at hbig
  rw [← (hc.pow_right _).eq] at hbig
  calc z * x a ^ Λ r i = z * (e s * x a ^ Λ r i) := by rw [← mul_assoc, hz]
       _ = z * (ψ j * ψ j * e s) := by rw [hbig]
       _ = 0 := by rw [← mul_assoc, ← mul_assoc, hzero, zero_mul, zero_mul]

section Reflection

open MulOpposite
local notation "S" => stendhalQ Q Λ
local notation "K" => KLRAlgebra k S μ

private def flipKLR : K →ₐ[k] Aᵐᵒᵖ :=
  (π).op.comp (KLRAlgebra.flipH k S μ).toAlgHom

private def flipAll : A →ₐ[k] Aᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨flipKLR.comp (KLRAlgebra.mk k S μ), fun _ _ h => by
    cases h with
    | klr h => exact congrArg flipKLR (RingQuot.mkAlgHom_rel k h)
    | red_dot a s ha =>
      simp only [AlgHom.comp_apply, map_mul (KLRAlgebra.mk k S μ), map_zero]
      change op (π (KLRAlgebra.hflip (KLRAlgebra.x a * KLRAlgebra.e s))) = 0
      rw [KLRAlgebra.hflip_mul, KLRAlgebra.hflip_x, KLRAlgebra.hflip_e,
        KLRAlgebra.e_mul_x, map_mul]
      exact congrArg op (x_mul_e_of_red a s ha)
    | red_cross j hj s ha hb =>
      simp only [AlgHom.comp_apply, map_mul (KLRAlgebra.mk k S μ), map_zero]
      change op (π (KLRAlgebra.hflip (KLRAlgebra.ψ j * KLRAlgebra.e s))) = 0
      rw [KLRAlgebra.hflip_mul, KLRAlgebra.hflip_ψ, KLRAlgebra.hflip_e,
        KLRAlgebra.e_mul_ψ, map_mul]
      apply congrArg op
      exact ψ_mul_e_of_red j hj _ (by rwa [KLRAlgebra.lbl_sadj_left hj])
        (by rwa [KLRAlgebra.lbl_sadj_right hj])⟩

private abbrev reflect (z : A) := (flipAll z).unop

private theorem reflect_ofKLR (z : K) : reflect (π z) = π (KLRAlgebra.hflip z) := by
  obtain ⟨f,rfl⟩ := KLRAlgebra.mk_surjective z
  rw [ofKLR_mk]
  exact congrArg unop (show flipAll (RingQuot.mkAlgHom k (Rel k Q Λ ν) f) =
    flipKLR (KLRAlgebra.mk k S μ f) from RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _)

private theorem reflect_involutive : Function.Involutive (reflect (Q := Q) (Λ := Λ) (ν := ν)) := by
  intro z
  obtain ⟨a,rfl⟩ := ofKLR_surjective z
  rw [reflect_ofKLR, reflect_ofKLR, KLRAlgebra.hflip_hflip]

private theorem reflect_mul (y z : A) : reflect (y * z) = reflect z * reflect y := by
  change (flipAll (y * z)).unop = _
  rw [map_mul, unop_mul]

private theorem reflect_e (s : Seq μ) : reflect (e s : A) = e s := by
  rw [e, reflect_ofKLR, KLRAlgebra.hflip_e]

private theorem reflect_zero : reflect (0 : A) = 0 := by
  change (flipAll (0 : A)).unop = 0
  rw [map_zero, unop_zero]

end Reflection

/-- All red strands precede all black strands. The indicator of a black
strand is weakly increasing from left to right. -/
def RedsFirst (s : Seq μ) : Prop := Monotone fun a => (s.lbl a).isLeft

omit [DecidableEq I] in
private theorem adjacent_mixed {n : ℕ} (f : Fin n → I ⊕ Fin ℓ)
    (h : ¬ Monotone fun a => (f a).isLeft) :
    ∃ (j : ℕ) (hj : j + 1 < n) (i : I) (r : Fin ℓ),
      f ⟨j, by omega⟩ = .inl i ∧ f ⟨j+1, hj⟩ = .inr r := by
  cases n with
  | zero => exact False.elim (h fun a => Fin.elim0 a)
  | succ n =>
    rw [Fin.monotone_iff_le_succ] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    cases h₁ : f j.castSucc with
    | inr r =>
      cases h₂ : f j.succ <;> simp [h₁, h₂] at hj
      exact ((by decide : ¬ true < false) hj).elim
    | inl i =>
      cases h₂ : f j.succ with
      | inl c => simp [h₁, h₂] at hj
      | inr r => exact ⟨j.val, by omega, i, r, h₁, h₂⟩

private def redPositionSum (s : Seq μ) : ℕ := ∑ r : Fin ℓ, posVal s (redStrand ν r)

private theorem redPositionSum_sadj (s : Seq μ) (j : ℕ) (hj : j+1 < m)
    {i : I} {r : Fin ℓ} (hi : s.lbl ⟨j, by omega⟩ = .inl i)
    (hr : s.lbl ⟨j+1, hj⟩ = .inr r) :
    redPositionSum (sadj m j • s) < redPositionSum s := by
  let a : Fin m := ⟨j, by omega⟩
  let b : Fin m := ⟨j+1, hj⟩
  have hn : s.val a ≠ s.val b := by change s.lbl _ ≠ s.lbl _; rw [hi,hr]; simp
  have he : s.strandAt b = redStrand ν r := eq_redStrand hr
  unfold redPositionSum
  rw [posVal_sadj s hj hn]
  apply Finset.sum_lt_sum
  · intro q _
    by_cases h : redStrand ν q = s.strandAt b
    · rw [h, Function.comp_apply, swap_apply_right, posVal_strandAt, posVal_strandAt]
      exact (Nat.le_succ j)
    · have h' : redStrand ν q ≠ s.strandAt a := by
        intro e
        have hh : Sum.inr q = s.lbl a := congrArg (fun x => x.1.val) e
        rw [hi] at hh; contradiction
      rw [Function.comp_apply, swap_apply_of_ne_of_ne h' h]
  · refine ⟨r, Finset.mem_univ _, ?_⟩
    rw [← he, Function.comp_apply, swap_apply_right, posVal_strandAt, posVal_strandAt]
    exact Nat.lt_succ_self j

private theorem exists_right_shuffle
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hind : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (s : Seq μ) (hs : IsRedOrdered s) :
    ∃ (t : Seq μ) (u : A), IsRedOrdered t ∧ RedsFirst t ∧ e s * u = u ∧ u * e t = u ∧
      ∀ z : A, z * e s = z → z * u = 0 → z = 0 := by
  classical
  by_cases h : RedsFirst s
  · refine ⟨s, e s, hs, h, ?_, ?_, fun _ hz hzero => hz.symm.trans hzero⟩ <;>
      simp [e_mul_e]
  obtain ⟨j, hj, i, r, hi, hr⟩ := adjacent_mixed s.lbl h
  let t := sadj m j • s
  have ht : IsRedOrdered t := isRedOrdered_sadj hs hj (Or.inl (by
    change (s.lbl ⟨j,_⟩).isLeft; simp [hi]))
  have hlt : redPositionSum t < redPositionSum s := redPositionSum_sadj s j hj hi hr
  obtain ⟨t', u, hto, hfirst, hleft, hright, hreg⟩ := exists_right_shuffle hρ hind t ht
  have hcut : (e s : A) * ψ j = ψ j * e t :=
    (map_mul π _ _).symm.trans ((congrArg π (KLRAlgebra.e_mul_ψ j s)).trans (map_mul π _ _))
  refine ⟨t', ψ j * u, hto, hfirst, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hcut, mul_assoc, hleft]
  · rw [mul_assoc, hright]
  · intro z hz hzero
    apply cancel_mixed_right hρ hind s hs j hj hi hr z hz
    apply hreg
    · rw [mul_assoc, ← hcut, ← mul_assoc, hz]
    · rwa [mul_assoc]
termination_by redPositionSum s

private theorem compression_of_basis
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hind : LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)))
    (s t : Seq μ) (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    ∃ (p q : Seq μ) (hp : IsRedOrdered p) (hq : IsRedOrdered q) (c d : T),
      RedsFirst p ∧ RedsFirst q ∧ StendhalAlgebra.e p hp * c = c ∧
      c * StendhalAlgebra.e s hs = c ∧ StendhalAlgebra.e t ht * d = d ∧
      d * StendhalAlgebra.e q hq = d ∧
      Function.Injective (fun z : {z : T // StendhalAlgebra.e s hs * z = z ∧
        z * StendhalAlgebra.e t ht = z} => c * z.val * d) := by
  obtain ⟨p,u,hp,hpf,hus,hup,hu⟩ := exists_right_shuffle hρ hind s hs
  obtain ⟨q,v,hq,hqf,hvt,hvq,hv⟩ := exists_right_shuffle hρ hind t ht
  have hpu : e p * reflect u = reflect u := by
    simpa only [reflect_mul, reflect_e] using congrArg reflect hup
  have hsu : reflect u * e s = reflect u := by
    simpa only [reflect_mul, reflect_e] using congrArg reflect hus
  let c := orderProjection Q Λ ν (reflect u)
  let d := orderProjection Q Λ ν v
  have hc : c.val = reflect u := projection_val_of_support hs _ hsu
  have hd : d.val = v := projection_val_of_support hq _ hvq
  refine ⟨p,q,hp,hq,c,d,hpf,hqf,Subtype.ext ?_,Subtype.ext ?_,Subtype.ext ?_,Subtype.ext ?_,?_⟩
  · change e p * c.val = c.val; rwa [hc]
  · change c.val * e s = c.val; rwa [hc]
  · change e t * d.val = d.val; rwa [hd]
  · change d.val * e q = d.val; rwa [hd]
  intro z z' he
  let y : A := z.val.val - z'.val.val
  have hys : e s * y = y := by
    rw [show y = z.val.val - z'.val.val from rfl, mul_sub,
      show e s * z.val.val = z.val.val from congrArg Subtype.val z.property.1,
      show e s * z'.val.val = z'.val.val from congrArg Subtype.val z'.property.1]
  have hyt : y * e t = y := by
    rw [show y = z.val.val - z'.val.val from rfl, sub_mul,
      show z.val.val * e t = z.val.val from congrArg Subtype.val z.property.2,
      show z'.val.val * e t = z'.val.val from congrArg Subtype.val z'.property.2]
  have hy : reflect u * y * v = 0 := by
    have he' := congrArg Subtype.val he
    change c.val * z.val.val * d.val = c.val * z'.val.val * d.val at he'
    rw [hc,hd] at he'
    simpa only [y, mul_sub, sub_mul, sub_eq_zero] using he'
  have hleft : reflect u * y = 0 :=
    hv _ (by rw [mul_assoc, hyt]) hy
  have href : reflect y = 0 := hu _ (by
    simpa only [reflect_mul, reflect_e] using congrArg reflect hys) (by
    simpa only [reflect_mul, reflect_involutive u, reflect_zero] using congrArg reflect hleft)
  exact Subtype.ext (Subtype.ext (sub_eq_zero.mp
    (reflect_involutive.injective (href.trans reflect_zero.symm))))

variable (Λ) in
/-- **Faithful compression to the all-reds-first boundaries** used in the proof
of Webster, arXiv:1309.3796v2, Lemma 4.26, following Lemma 4.17. Two
independent shuffles move the red strands at the top and bottom to the left.
Multiplying by the corresponding diagrams is injective on the entire
specified affine corner for Webster's parameters from §2.2. -/
theorem exists_redsFirst_compression {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q)
    (s t : Seq μ) (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    ∃ (p q : Seq μ) (hp : IsRedOrdered p) (hq : IsRedOrdered q) (c d : T),
      RedsFirst p ∧ RedsFirst q ∧ StendhalAlgebra.e p hp * c = c ∧
      c * StendhalAlgebra.e s hs = c ∧ StendhalAlgebra.e t ht * d = d ∧
      d * StendhalAlgebra.e q hq = d ∧
      Function.Injective (fun z : {z : T //
        StendhalAlgebra.e s hs * z = z ∧ z * StendhalAlgebra.e t ht = z} => c * z.val * d) := by
  choose ρ hρ using exists_reduced m
  exact compression_of_basis hρ (linearIndependent_stendhalTerm_of_rouquier Q ν Λ hQ hρ) s t hs ht

end Categorification.Stendhal
