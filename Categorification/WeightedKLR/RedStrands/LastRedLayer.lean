/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedTruncation
import Categorification.WeightedKLR.RedStrands.StendhalBasis
import Categorification.TypeA.DoubleCoset
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Categorification.KLR.InductionFree
import Categorification.KLR.ConcatAssoc

/-!
# Diagrams through a smaller last black block

Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.37 and Theorem 4.38.
For a fixed position of the last red strand choose PBW words so that a
permutation exchanging strands across that position has a cut with the red
strand one place farther to the right.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

private theorem reduced_append_descent {m j : ℕ} {w : Perm (Fin m)} (hj : j+1 < m)
    (hd : w ⟨j+1,hj⟩ < w ⟨j,by omega⟩) {ρ : List ℕ}
    (hρ : IsReduced m ρ) (hw : wordProd m ρ = w * sadj m j) :
    IsReduced m (ρ ++ [j]) ∧ wordProd m (ρ ++ [j]) = w := by
  have hp : wordProd m (ρ ++ [j]) = w := by
    rw [wordProd_append, wordProd_singleton, hw, mul_assoc, sadj_mul_self, mul_one]
  refine ⟨⟨validWord_append.2 ⟨hρ.1, by simp [hj]⟩, ?_⟩, hp⟩
  rw [List.length_append, hρ.2, hp, hw]
  exact length_mul_sadj_of_gt hj hd

/-- A permutation fixing the marked strand and taking a suffix strand to
its left has a reduced expression whose right subword moves the marked
strand one place right. -/
private theorem exists_cut_word {m : ℕ} (p : Fin m) (b : ℕ) (hb : b < m)
    (w : Perm (Fin m)) (hw : w p = p) (hpb : p.val < b) (hbw : w ⟨b,hb⟩ < p) :
    ∃ L R : List ℕ, IsReduced m (L ++ R) ∧ wordProd m (L ++ R) = w ∧
      (wordProd m R p).val = p.val + 1 := by
  induction b generalizing w with
  | zero => omega
  | succ b ih =>
    have hbm : b < m := by omega
    by_cases h : w ⟨b,hbm⟩ < p
    · have hne : p.val ≠ b := by
        intro he
        rw [show (⟨b,hbm⟩ : Fin m) = p from Fin.ext he.symm, hw] at h
        exact lt_irrefl _ h
      exact ih hbm w hw (by omega) h
    · let v := w * sadj m b
      have hd : w ⟨b+1,hb⟩ < w ⟨b,hbm⟩ := hbw.trans_le (le_of_not_gt h)
      obtain he | he := lt_or_eq_of_le (show p.val ≤ b by omega)
      · have hf : sadj m b p = p := sadj_apply_of_ne p (by omega) (by omega)
        have hvp : v p = p := by simp only [v, Perm.mul_apply, hf, hw]
        obtain ⟨L,R,hLR,hvR,hcut⟩ := ih hbm v hvp he (by
          change w (sadj m b _) < p
          rwa [sadj_apply_left hb])
        obtain ⟨hr,hprod⟩ := reduced_append_descent hb hd hLR hvR
        refine ⟨L,R ++ [b], by simpa only [List.append_assoc] using hr,
          by simpa only [List.append_assoc] using hprod, ?_⟩
        rw [wordProd_append, wordProd_singleton, Perm.mul_apply, hf, hcut]
      · obtain ⟨hr,hprod⟩ := reduced_append_descent hb hd (isReduced_canWord m v) (wordProd_canWord m v)
        refine ⟨canWord m v,[b],hr,hprod,?_⟩
        rw [wordProd_singleton, show p = ⟨b,hbm⟩ from Fin.ext he, sadj_apply_left hb]

private def crossesCut {m : ℕ} (p : Fin m) (w : Perm (Fin m)) : Prop :=
  w p = p ∧ ∃ b : Fin m, p < b ∧ w b < p

private theorem cut_split {m : ℕ} (p : Fin m) (w : Perm (Fin m)) (hc : crossesCut p w) :
    ∃ z : List ℕ × List ℕ, IsReduced m (z.1 ++ z.2) ∧ wordProd m (z.1 ++ z.2) = w ∧
      (wordProd m z.2 p).val = p.val + 1 := by
  obtain ⟨hw,b,hpb,hbw⟩ := hc
  obtain ⟨L,R,h⟩ := exists_cut_word p b b.isLt w hw hpb hbw
  exact ⟨(L,R), h⟩

private theorem cutCard {m : ℕ} (p : Fin m) : (p.val+1) + (m-(p.val+1)) = m := by omega

private theorem block_of_not_crosses {m : ℕ} (p : Fin m) (w : Perm (Fin m))
    (hw : w p = p) (hn : ¬ crossesCut p w) :
    ∃ u v, blockPerm (cutCard p) u v = w := by
  let S := blockEquiv (cutCard p)
  let σ := S.symm.permCongr w
  have hm : Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro _ ⟨a,rfl⟩
    cases ha : σ (Sum.inr a) with
    | inr d => exact ⟨d,rfl⟩
    | inl d =>
      have hpos : w (S (.inr a)) = S (.inl d) := by
        simpa [σ, Equiv.permCongr_apply] using congrArg S ha
      have hi : p < S (.inr a) := by change p.val < p.val + 1 + a.val; omega
      have hd : S (.inl d) ≤ p := by change d.val ≤ p.val; omega
      have hne : w (S (.inr a)) ≠ p := fun h => hi.ne ((w.injective (h.trans hw.symm)).symm)
      exact (hn ⟨hw,_,hi,lt_of_le_of_ne (hpos ▸ hd) hne⟩).elim
  obtain ⟨⟨u,v⟩,huv⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr σ).mpr hm)
  refine ⟨u,v,?_⟩
  change S.permCongr (Equiv.Perm.sumCongr u v) = w
  change Equiv.Perm.sumCongr u v = S.symm.permCongr w at huv
  rw [huv]
  exact S.permCongr.apply_symm_apply w

private def sideWord {m : ℕ} (p : Fin m) (w : Perm (Fin m)) : List ℕ :=
  open Classical in
  if h : ∃ u v, blockPerm (cutCard p) u v = w then
    canWord _ h.choose ++ shiftWord (p.val+1) (canWord _ h.choose_spec.choose)
  else canWord m w

private theorem sideWord_spec {m : ℕ} (p : Fin m) (w : Perm (Fin m)) :
    IsReduced m (sideWord p w) ∧ wordProd m (sideWord p w) = w := by
  classical
  unfold sideWord
  split
  next h =>
    exact ⟨(isReduced_canWord _ _).append_shiftWord (cutCard p) (isReduced_canWord _ _), by
      rw [wordProd_append_shiftWord (cutCard p) (validWord_canWord _ _) (validWord_canWord _ _),
        wordProd_canWord, wordProd_canWord]
      exact h.choose_spec.choose_spec⟩
  next => exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private def cutWord {m : ℕ} (p : Fin m) (w : Perm (Fin m)) : List ℕ :=
  open Classical in
  if hc : crossesCut p w then
    let z := (cut_split p w hc).choose
    z.1 ++ z.2
  else sideWord p w

private theorem cutWord_spec {m : ℕ} (p : Fin m) (w : Perm (Fin m)) :
    IsReduced m (cutWord p w) ∧ wordProd m (cutWord p w) = w := by
  classical
  unfold cutWord
  split
  next hc => exact ⟨(cut_split p w hc).choose_spec.1, (cut_split p w hc).choose_spec.2.1⟩
  next => exact sideWord_spec p w

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "M" => stendhalWeight (ℓ+1) ν
local notation "n" => Multiset.card M

private theorem ordered_word {s : Seq M} (hs : IsRedOrdered s) {γ : List ℕ}
    (hv : ValidWord n γ) (hr : NoRedCross γ s) : IsRedOrdered (wordProd n γ • s) := by
  induction γ with
  | nil => simpa using hs
  | cons j γ ih =>
    obtain ⟨hj,hv⟩ := validWord_cons.mp hv
    rw [wordProd_cons, mul_smul]
    exact isRedOrdered_sadj (ih hv hr.1) hj (hr.2 hj)

private theorem noRedCross_tail {s : Seq M} (L R : List ℕ) (h : NoRedCross (L ++ R) s) :
    NoRedCross R s := by
  induction L with
  | nil => exact h
  | cons j L ih => exact ih h.1

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)

/-- The ideal generated by boundaries where the last red strand is strictly
to the right of position `p` (Webster §4.7, proof of Lemma 4.37). -/
def smallerSuffixIdeal (p : Fin n) : TwoSidedIdeal (TensorProductAlgebra k Q Λ ν) :=
  TwoSidedIdeal.span {x | ∃ (s : Seq M) (hs : IsRedOrdered s) (a : Fin n),
    p < a ∧ s.lbl a = .inr (Fin.last ℓ) ∧ x = TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)}

local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "τ" => TensorProductAlgebra.mk Q Λ ν

private theorem cut_term_mem (p : Fin n)
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ+1) (cutWord p) b})
    (hred : b.1.1.lbl p = .inr (Fin.last ℓ)) (hc : crossesCut p b.1.2.1) :
    τ (stendhalTerm Q Λ (fun w => (cutWord_spec p w).2) b) ∈ smallerSuffixIdeal Q Λ p := by
  classical
  let w := b.1.2.1
  let z := (cut_split p w hc).choose
  have hγ : cutWord p w = z.1 ++ z.2 := dite_eq_left hc
  have hs := (cut_split p w hc).choose_spec
  let t := wordProd n z.2 • b.1.1
  obtain ⟨-,hv⟩ := validWord_append.mp hs.1.1
  have hn := b.2.2.2.2
  change NoRedCross (cutWord p w) b.1.1 at hn
  rw [hγ] at hn
  have ht : IsRedOrdered t := ordered_word b.2.1 hv (noRedCross_tail _ _ hn)
  let et := StendhalAlgebra.e (Q := Q) (Λ := Λ) t ht
  have hgen : τ et ∈ smallerSuffixIdeal Q Λ p := TwoSidedIdeal.subset_span
    ⟨t,ht,wordProd n z.2 p, by change p.val < _; rw [hs.2.2]; omega,
      by change b.1.1.lbl ((wordProd n z.2).symm _) = _; rwa [Equiv.symm_apply_apply], rfl⟩
  let d := MvPolynomial.monomial b.1.2.2 (1 : k)
  let v := KLRAlgebra.ψw (k := k) (Q := stendhalQ Q Λ) (ν := M) z.2 *
    KLRAlgebra.pol d * KLRAlgebra.e b.1.1
  have hfix : KLRAlgebra.e t * v = v := by
    rw [show v = _ from rfl, KLRAlgebra.e_mul_gen]
    simp [t, v]
  let u := stendhalTerm Q Λ (fun g => (cutWord_spec p g).2) b
  have he : u.val = π (KLRAlgebra.ψw z.1) * et.val * π v := by
    change π (KLRAlgebra.ψw (cutWord p w) * KLRAlgebra.pol d * KLRAlgebra.e b.1.1) =
      π _ * π (KLRAlgebra.e t) * π _
    rw [hγ, KLRAlgebra.ψw_append, mul_assoc (π _), ← map_mul π (KLRAlgebra.e t), hfix]
    simp only [v, map_mul, mul_assoc]
  have hu : u ∈ TwoSidedIdeal.span ({et} : Set _) := by
    apply corner_mem_span_singleton_of_val _ et u
    rw [he]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _
      (TwoSidedIdeal.subset_span (Set.mem_singleton _)))
  exact (TwoSidedIdeal.mem_comap ..).1 ((TwoSidedIdeal.span_le.2
    (show ({et} : Set _) ⊆ ((smallerSuffixIdeal Q Λ p).comap τ : TwoSidedIdeal _) by
      rintro _ rfl
      exact (TwoSidedIdeal.mem_comap ..).2 hgen)) hu)

/-- At a given last-red position one can choose Proposition 4.16 PBW words so
that every term exchanging black strands across the last red belongs to the
ideal of smaller suffixes (Webster, arXiv:1309.3796v2, Lemma 4.37, proof). -/
theorem exists_reducedWords_smallerSuffix (p : Fin n) :
    ∃ (ρ : Perm (Fin n) → List ℕ) (hρ : ∀ w, IsReduced n (ρ w) ∧ wordProd n (ρ w) = w),
      ∀ (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ+1) ρ b}), b.1.1.lbl p = .inr (Fin.last ℓ) →
        b.1.2.1 p = p → (∃ a : Fin n, p < a ∧ b.1.2.1 a < p) →
        τ (stendhalTerm Q Λ (fun w => (hρ w).2) b) ∈ smallerSuffixIdeal Q Λ p :=
  ⟨cutWord p, cutWord_spec p, fun b hr hw ha => cut_term_mem Q Λ p b hr ⟨hw,ha⟩⟩


open KLRAlgebra MvPolynomial
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem exists_concat_split_word {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {α β γ : Multiset J} (h : α + β = γ)
    (a : Seq α) (b : Seq β) {L R : List ℕ} (hL : ValidWord α.card L) (hR : ValidWord β.card R)
    (d : Fin γ.card →₀ ℕ) :
    ∃ z, castKLR P h (concat P α β z) =
      ψw (L ++ shiftWord α.card R) * pol (monomial d 1) * KLRAlgebra.e (Seq.cast h (a.append b)) := by
  subst γ
  obtain ⟨⟨u,v⟩,rfl⟩ := (expEquiv α β).surjective d
  refine ⟨((ψw L ⊗ₜ ψw R) * (pol (monomial u 1) ⊗ₜ pol (monomial v 1))) *
    (KLRAlgebra.e a ⊗ₜ KLRAlgebra.e b), ?_⟩
  change concat P α β _ = ψw _ * pol _ * KLRAlgebra.e (a.append b)
  rw [concat_mul, concat_mul, concat_e_tmul_e, concat_ψw_tmul_ψw hL hR, concat_pol_tmul_pol,
    ← monomial_expEquiv, oneConcat, mul_E_mul_mul_E (eSum_idem _) _ (pol_mul_eSum _ _).symm,
    mul_assoc _ (eSum P _), eSum_mul_e, ite_eq_left (append_mem_concatSet a b)]

local notation "S" => stendhalQ Q Λ
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "proj" => orderProjection Q Λ ν

/-- Juxtapose diagrams in the two augmented KLR blocks and pass to the
quotient by diagrams through smaller suffixes. -/
def suffixConcat (p : Fin n) {α β : Multiset (I ⊕ Fin (ℓ+1))} (h : α+β=M) :
    KLRAlgebra k S α ⊗[k] KLRAlgebra k S β →ₗ[k] (smallerSuffixIdeal Q Λ p).ringCon.Quotient :=
  ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k).toLinearMap ∘ₗ (τ).toLinearMap ∘ₗ
    (proj).toLinearMap ∘ₗ (π).toLinearMap ∘ₗ (castKLR S h).toLinearMap ∘ₗ concat S α β

private theorem side_cut_mem_range (p : Fin n) {α β : Multiset (I ⊕ Fin (ℓ+1))}
    (h : α+β=M) (ha : α.card = p.val+1) (a : Seq α) (b : Seq β)
    (c : {c // IsStendhalTerm (ν := ν) (ℓ := ℓ+1) (cutWord p) c})
    (hc : c.1.1 = Seq.cast h (a.append b)) (hw : c.1.2.1 p = p) (hn : ¬ crossesCut p c.1.2.1) :
    (smallerSuffixIdeal Q Λ p).ringCon.mk' (τ (stendhalTerm Q Λ (fun w => (cutWord_spec p w).2) c)) ∈
      LinearMap.range (suffixConcat Q Λ p h) := by
  classical
  let w := c.1.2.1
  have hside := block_of_not_crosses p w hw hn
  let u := hside.choose
  let v := hside.choose_spec.choose
  have hb : β.card = n - (p.val+1) := by
    have H := congrArg Multiset.card h
    rw [Multiset.card_add,ha] at H
    omega
  have hγ : cutWord p w = canWord _ u ++ shiftWord α.card (canWord _ v) := by
    change ¬ crossesCut p w at hn
    rw [cutWord, dite_eq_right hn, sideWord, dite_eq_left hside, ha]
  obtain ⟨z,hz⟩ := exists_concat_split_word S h a b
    (L := canWord _ u) (R := canWord _ v) (by rw [ha]; exact validWord_canWord _ u) (by rw [hb]; exact validWord_canWord _ v) c.1.2.2
  refine ⟨z,?_⟩
  let y := stendhalTerm Q Λ (fun g => (cutWord_spec p g).2) c
  suffices hy : proj (π (castKLR S h (concat S α β z))) = y by
    exact congrArg (smallerSuffixIdeal Q Λ p).ringCon.mk' (congrArg τ hy)
  apply Subtype.ext
  have hf := KLR.Corner.val_mul_E y
  change π (castKLR S h (concat S α β z)) * _ = y.val
  rw [← hf]
  congr 1
  rw [hz, ← hc, stendhalTerm_val, stdElt, hγ]

/-- Every diagram with the last red strand at `p` on both boundaries comes
from juxtaposition of its two blocks modulo the smaller-suffix ideal.
The bottom boundary specifies the two block weights. This is the spanning
step in Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.37. -/
theorem sandwich_mem_range_suffixConcat (p : Fin n) {α β : Multiset (I ⊕ Fin (ℓ+1))}
    (h : α+β=M) (ha : α.card = p.val+1) (a : Seq α) (b : Seq β)
    (s t : Seq M) (hs : IsRedOrdered s) (ht : IsRedOrdered t)
    (hsplit : s = Seq.cast h (a.append b))
    (hr : s.lbl p = .inr (Fin.last ℓ)) (hr' : t.lbl p = .inr (Fin.last ℓ)) (x : A) :
    (smallerSuffixIdeal Q Λ p).ringCon.mk' (τ (StendhalAlgebra.e t ht) * x * τ (StendhalAlgebra.e s hs)) ∈
      LinearMap.range (suffixConcat Q Λ p h) := by
  classical
  obtain ⟨y,rfl⟩ := (show Function.Surjective τ from RingCon.mkₐ_surjective _) x
  let f := ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k).comp τ
  change f (StendhalAlgebra.e t ht * y * StendhalAlgebra.e s hs) ∈ _
  have hv := span_stendhalTerm (Q := Q) (Λ := Λ) (ν := ν) (cutWord_spec p) (Submodule.mem_top (x := y))
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c,rfl⟩ := hy
    rw [e_mul_stendhalTerm]
    split_ifs with hout
    · rw [stendhalTerm_mul_e]
      split_ifs with hin
      · let w := c.1.2.1
        have hsrc : c.1.1.lbl p = .inr (Fin.last ℓ) := hin ▸ hr
        have hout' : (w • c.1.1).lbl p = .inr (Fin.last ℓ) := hout ▸ hr'
        have hpos : (w • c.1.1).lbl (w p) = .inr (Fin.last ℓ) := by
          change c.1.1.lbl (w.symm (w p)) = _
          rwa [Equiv.symm_apply_apply]
        have hw : w p = p := eq_of_lbl_eq_inr hpos hout'
        by_cases hn : crossesCut p w
        · have hJ := cut_term_mem Q Λ p c hsrc hn
          have hz := (TwoSidedIdeal.mem_ker _).mp
            ((TwoSidedIdeal.ker_ringCon_mk' (smallerSuffixIdeal Q Λ p)).symm ▸ hJ)
          exact hz ▸ Submodule.zero_mem _
        · exact side_cut_mem_range Q Λ p h ha a b c (hin.trans hsplit) hw hn
      · rw [map_zero]
        exact Submodule.zero_mem _
    · rw [zero_mul, map_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add y z _ _ hy hz =>
    simpa only [mul_add, add_mul, map_add] using (LinearMap.range (suffixConcat Q Λ p h)).add_mem hy hz
  | smul c y _ hy =>
    simpa only [mul_smul_comm, smul_mul_assoc, map_smul] using (LinearMap.range (suffixConcat Q Λ p h)).smul_mem c hy

end Categorification.Stendhal
