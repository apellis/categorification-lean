/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayerTensor
import Categorification.KLR.Prop32Mult

/-!
# Loading support in the final-red layers

Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38. Every ordered
loading with a specified position of the last red strand belongs to a
corner for a division of the black weight into prefix and suffix.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR
variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "M" => stendhalWeight (ℓ+1) ν
local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))

private theorem exists_black_word {J : Type*} (w : List (I ⊕ J)) (h : ∀ c ∈ w, c.isLeft) :
    ∃ v : List I, v.map Sum.inl = w := by
  induction w with
  | nil => exact ⟨[],rfl⟩
  | cons c w ih =>
    obtain ⟨v,hv⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    cases c with
    | inl i => exact ⟨i::v, by simp [hv]⟩
    | inr j => simpa using h (.inr j) (List.mem_cons_self ..)

private theorem split_colours {J : Type*} (w : List (I ⊕ J)) :
    ∃ (u : Multiset I) (v : Multiset J), u.map Sum.inl + v.map Sum.inr = (w : Multiset (I ⊕ J)) := by
  induction w with
  | nil => exact ⟨0,0,rfl⟩
  | cons c w ih =>
    obtain ⟨u,v,h⟩ := ih
    cases c with
    | inl i => exact ⟨i::ₘu,v,by simp [h]⟩
    | inr j => exact ⟨u,j::ₘv,by simp [h]⟩

private theorem disjSum_injective {J : Type*} {u u' : Multiset I} {v v' : Multiset J}
    (h : u.map Sum.inl + v.map Sum.inr = u'.map Sum.inl + v'.map Sum.inr) :
    u=u' ∧ v=v' := by
  classical
  constructor
  · apply Multiset.ext.mpr
    intro i
    have H := congrArg (Multiset.count (.inl i)) h
    simpa [Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective] using H
  · apply Multiset.ext.mpr
    intro j
    have H := congrArg (Multiset.count (.inr j)) h
    simpa [Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective] using H

/-- Cut an ordered loading directly after its last red strand. The left
weight contains all the red labels and the right weight contains only
black labels. The two black weights sum to the original one. -/
theorem exists_lastRedLayer_split (s : Seq M) (hs : IsRedOrdered s) (p : Fin (Multiset.card M))
    (hr : s.lbl p = .inr (Fin.last ℓ)) :
    ∃ (θ β : Multiset I) (h : stendhalWeight (ℓ+1) θ + β.map ι = M),
      θ+β=ν ∧ (stendhalWeight (ℓ+1) θ).card = p.val+1 ∧
      ∃ (a : Seq (stendhalWeight (ℓ+1) θ)) (b : Seq (β.map ι)),
        HasLastRed a ∧ s = Seq.cast h (a.append b) := by
  classical
  let w := List.ofFn s.1
  let u := w.take (p.val+1)
  let v := w.drop (p.val+1)
  have hu : u.length = p.val+1 := by simp [u,w]
  have huv : u++v=w := List.take_append_drop ..
  have hblack (c) (hc : c ∈ v) : c.isLeft := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hc
    change ((List.ofFn s.1).drop (p.val+1))[j].isLeft = true
    rw [List.getElem_drop, List.getElem_ofFn]
    cases hh : s.1 ⟨p.val+1+j,by simpa [v,w] using (show p.val+1+j < w.length by
      have : j < w.length - (p.val+1) := by simpa [v] using hj
      omega)⟩ with
    | inl i => rfl
    | inr r =>
      exact False.elim ((not_lt_of_ge (Fin.le_last r)) (hs p _ _ _ (by change p.val < p.val+1+j; omega) hr hh))
  obtain ⟨bl,hbl⟩ := exists_black_word v hblack
  let β : Multiset I := bl
  have hv : β.map ι = (v : Multiset (I ⊕ Fin (ℓ+1))) := congrArg (fun t : List (I ⊕ Fin (ℓ+1)) => (t : Multiset (I ⊕ Fin (ℓ+1)))) hbl
  obtain ⟨θ,δ,hθ⟩ := split_colours u
  have H : (θ+β).map ι + δ.map Sum.inr = ν.map ι + Finset.univ.val.map Sum.inr := by
    rw [Multiset.map_add, add_right_comm, hθ, hv]
    calc _ = ((u++v : List _) : Multiset _) := rfl
         _ = M := (congrArg (fun t : List (I ⊕ Fin (ℓ+1)) => (t : Multiset (I ⊕ Fin (ℓ+1)))) huv).trans (KLRAlgebra.Seq.coe_ofFn s)
  obtain ⟨hν,hδ⟩ := disjSum_injective H
  subst δ
  have hα : stendhalWeight (ℓ+1) θ = (u : Multiset _) := hθ
  have h : stendhalWeight (ℓ+1) θ + β.map ι = M := by
    rw [← hν]
    simp only [stendhalWeight, Multiset.map_add]
    ac_rfl
  have hcard : (stendhalWeight (ℓ+1) θ).card = p.val+1 := by rw [hα]; exact hu
  let a := KLRAlgebra.Seq.ofList u hα.symm
  let b := KLRAlgebra.Seq.ofList v hv.symm
  have hab : s = Seq.cast h (a.append b) := by
    apply Subtype.ext
    funext j
    change s.1 j = (Seq.cast h (a.append b)).1 j
    rw [Seq.cast_apply]
    by_cases hj : j.val < (stendhalWeight (ℓ+1) θ).card
    · rw [Seq.append_apply_lt _ _ _ hj]
      change s.1 j = (KLRAlgebra.Seq.ofList u _).lbl _
      rw [KLRAlgebra.Seq.ofList_lbl, List.getElem_take, List.getElem_ofFn]
      rfl
    · rw [Seq.append_apply_ge _ _ _ (le_of_not_gt hj)]
      change s.1 j = (KLRAlgebra.Seq.ofList v _).lbl _
      rw [KLRAlgebra.Seq.ofList_lbl, List.getElem_drop, List.getElem_ofFn]
      apply congrArg s.1
      apply Fin.ext
      change j.val = p.val+1+(j.val-(stendhalWeight (ℓ+1) θ).card)
      omega
  have hp : (lastRedPosition ℓ θ).val = p.val := by
    change θ.card + ℓ = p.val
    simp [stendhalWeight] at hcard
    omega
  have hred : HasLastRed a := by
    change (KLRAlgebra.Seq.ofList u _).lbl (lastRedPosition ℓ θ) = _
    rw [KLRAlgebra.Seq.ofList_lbl, List.getElem_take, List.getElem_ofFn]
    exact (congrArg s.1 (Fin.ext hp)).trans hr
  exact ⟨θ,β,h,hν,hcard,a,b,hred,hab⟩

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)

/-- The image of each loading with last red at `p` is supported by a
fixed-weight layer idempotent, Webster, arXiv:1309.3796v2, Theorem 4.38. -/
theorem exists_lastRedLayerIdem_mul_boundary (s : Seq M) (hs : IsRedOrdered s)
    (p : Fin (Multiset.card M)) (hr : s.lbl p = .inr (Fin.last ℓ)) :
    ∃ (θ β : Multiset I) (h : stendhalWeight (ℓ+1) θ + β.map ι = M),
      θ+β=ν ∧ (stendhalWeight (ℓ+1) θ).card = p.val+1 ∧
      let e := (smallerSuffixIdeal Q Λ p).ringCon.mk' (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs))
      lastRedLayerIdem Q Λ p h * e = e := by
  obtain ⟨θ,β,h,hν,ha,a,b,hend,rfl⟩ := exists_lastRedLayer_split s hs p hr
  exact ⟨θ,β,h,hν,ha,lastRedLayerIdem_mul_boundary Q Λ p h a b hend hs⟩

end Categorification.Stendhal
