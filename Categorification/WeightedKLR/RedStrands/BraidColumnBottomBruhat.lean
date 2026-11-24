/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Extension.Linear
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomGeneration
import Categorification.WeightedKLR.RedStrands.LeftStandardSupport

/-!
# Bruhat refinement of the bottom-label filtration

Webster, arXiv:1309.3796v3, proof of Lemma 6.12, p. 66, orders the
selected diagrams by the bottom-label preorder. The Bruhat convention in
v2, Proposition 5.20 and Lemma 6.11, suggests refining a class with equal
black counts by the rank inequalities and strict Coxeter length. This
choice allows every shorter black cut, including cuts between different
literal loadings in the same count class. A linear extension preserves
all these comparisons, and changing the reduced word of a selected
diagram contributes only to the earlier span.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- Strict dominance places the higher bottom first. Equal black counts
are refined by the Bruhat rank inequalities and strict Coxeter length. -/
def braidColumnIndexEarlier (s : Seq μ) (u w : Perm (Fin m)) : Prop :=
  StendhalLT (w⁻¹ • s) (u⁻¹ • s) ∨
    (blackCount (u⁻¹ • s) = blackCount (w⁻¹ • s) ∧
      (∀ i j : ℕ, rk u i j ≤ rk w i j) ∧ length m u < length m w)

theorem braidColumnIndexEarlier_irrefl (s : Seq μ) (w : Perm (Fin m)) :
    ¬ braidColumnIndexEarlier s w w := by
  rintro (h | ⟨_,_,h⟩)
  · exact h.2 (fun _ _ => le_rfl)
  · exact (lt_irrefl _) h

theorem braidColumnIndexEarlier_trans (s : Seq μ) {u v w : Perm (Fin m)}
    (huv : braidColumnIndexEarlier s u v) (hvw : braidColumnIndexEarlier s v w) :
    braidColumnIndexEarlier s u w := by
  rcases huv with h₁ | ⟨h₁,hr₁,hl₁⟩ <;> rcases hvw with h₂ | ⟨h₂,hr₂,hl₂⟩
  · left
    exact ⟨fun r i => (h₂.1 r i).trans (h₁.1 r i),
      fun h => h₁.2 (fun r i => (h r i).trans (h₂.1 r i))⟩
  · left
    simpa only [StendhalLT, StendhalLE, h₂] using h₁
  · left
    simpa only [StendhalLT, StendhalLE, h₁] using h₂
  · exact Or.inr ⟨h₁.trans h₂,fun i j => (hr₁ i j).trans (hr₂ i j),hl₁.trans hl₂⟩

/-- A linear extension preserves both parts of the strict refinement. -/
theorem exists_braidColumnIndexLinearRefinement (s : Seq μ) :
    ∃ R : Perm (Fin m) → Perm (Fin m) → Prop,
      IsLinearOrder (Perm (Fin m)) R ∧
      ∀ u w, braidColumnIndexEarlier s u w → R u w ∧ ¬ R w u := by
  let R₀ := fun u w : Perm (Fin m) => u = w ∨ braidColumnIndexEarlier s u w
  let h₀ : IsPartialOrder (Perm (Fin m)) R₀ := by
    refine { refl := fun _ => Or.inl rfl, trans := ?_, antisymm := ?_ }
    · intro u v w huv hvw
      rcases huv with rfl | hu
      · exact hvw
      · rcases hvw with rfl | hw
        · exact Or.inr hu
        · exact Or.inr (braidColumnIndexEarlier_trans s hu hw)
    · intro u v huv hvu
      rcases huv with h | h
      · exact h
      · rcases hvu with h' | h'
        · exact h'.symm
        · exact (braidColumnIndexEarlier_irrefl s u (braidColumnIndexEarlier_trans s h h')).elim
  obtain ⟨R,hR,hExt⟩ := @extend_partialOrder (Perm (Fin m)) R₀ h₀
  refine ⟨R,hR,fun u w h => ⟨hExt u w (Or.inr h),?_⟩⟩
  intro hw
  have he := hR.antisymm u w (hExt u w (Or.inr h)) hw
  subst w
  exact braidColumnIndexEarlier_irrefl s _ h

private theorem braidColumnIndexEarlier_of_subword
    (s : Seq μ) (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    {u w : Perm (Fin m)} (hs : u ∈ subProds m (ρ w))
    (hl : length m u < length m w) (hb : u⁻¹ • s = w⁻¹ • s) :
    braidColumnIndexEarlier s u w :=
  Or.inr ⟨congrArg blackCount hb,
    fun i j => by simpa only [(hρ w).2] using rk_le_of_mem_subProds (hρ w).1 hs i j,hl⟩

private theorem braidColumnIndexEarlier_of_descent
    (s : Seq μ) (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (w : Perm (Fin m)) (j : ℕ) (hj : j + 1 < m)
    (hd : w ⟨j+1,hj⟩ < w ⟨j,by omega⟩)
    (hblack : ((w⁻¹ • s).lbl ⟨j+1,hj⟩).isLeft) :
    braidColumnIndexEarlier s (w * sadj m j) w := by
  let b := w⁻¹ • s
  let v := w * sadj m j
  have hc : v⁻¹ • s = sadj m j • b := by
    dsimp [v,b]
    rw [mul_inv_rev,sadj_inv,mul_smul]
  obtain ⟨i,hi⟩ : ∃ i, b.lbl ⟨j+1,hj⟩ = .inl i := by
    cases h : b.lbl ⟨j+1,hj⟩ with
    | inl i => exact ⟨i,rfl⟩
    | inr r => change (b.lbl ⟨j+1,hj⟩).isLeft at hblack; simp [h] at hblack
  cases hleft : b.lbl ⟨j,by omega⟩ with
  | inr r =>
    left
    rw [hc]
    exact stendhalLT_sadj hj hleft hi (fun d h => lbl_eq_inr_unique h hleft)
  | inl i' =>
    have hlen : length m v + 1 = length m w := length_mul_sadj_of_gt hj hd
    have hprod : wordProd m (ρ v ++ [j]) = w := by
      rw [wordProd_append,wordProd_singleton,(hρ v).2]
      change (w * sadj m j) * sadj m j = w
      rw [mul_assoc,TypeA.sadj_mul_self,mul_one]
    have hred : IsReduced m (ρ v ++ [j]) := by
      refine ⟨validWord_append.2 ⟨(hρ v).1.1,validWord_cons.2 ⟨hj,validWord_nil m⟩⟩,?_⟩
      rw [List.length_append,List.length_singleton,(hρ v).1.2,(hρ v).2,hprod,hlen]
    have hb := braidEquiv_of_isReduced hred (hρ w).1 (hprod.trans (hρ w).2.symm)
    have hsub : v ∈ subProds m (ρ w) := by
      rw [← hb.subProds_eq hred.1, mem_subProds]
      exact ⟨ρ v,List.sublist_append_left _ _,(hρ v).2⟩
    right
    refine ⟨?_, fun i j => by
      simpa only [(hρ w).2] using rk_le_of_mem_subProds (hρ w).1 hsub i j,Nat.lt_of_succ_le hlen.le⟩
    funext r q
    rw [hc]
    exact blackCount_sadj_black_black b hj hleft hi r q

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MvPolynomial
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)

/-- Changing the reduced word gives a combination of eligible products
strictly earlier in the dominance–Bruhat refinement. Thus any linear
extension preserving this refinement gives the same layer map. -/
theorem braidColumnBottomBlock_wordChange_mem_earlier_span
    (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (w : Perm (Fin m)) (hword : redWord (w⁻¹ • s) = (List.finRange ℓ).map σ)
    {u v : List ℕ} (hu : IsReduced m u) (hv : IsReduced m v)
    (huw : wordProd m u = w) (hvw : wordProd m v = w) (p : MvPolynomial (Fin m) k) :
    F (ψw u * pol p * e (w⁻¹ • s)) - F (ψw v * pol p * e (w⁻¹ • s)) ∈
      Submodule.span k (braidColumnBottomProductsAt (Q := Q) (Λ := Λ) s σ ρ
        (fun x => braidColumnIndexEarlier s x w)) := by
  let b := w⁻¹ • s
  let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) s b
  have hp (r : List ℕ) (hr : wordProd m r = w) :
      f (ψw r * pol p * e b) = F (ψw r * pol p * e b) := by
    change F (e s * ((ψw r * pol p * e b) * e b)) = _
    rw [gen_mul_e,ite_eq_left rfl,e_mul_gen,hr,ite_eq_left rfl]
  have hraw := braidEquiv_sub_mem_lowSpan
    (Q := stendhalQ Q Λ) (braidEquiv_of_isReduced hu hv (huw.trans hvw.symm)) hu.1 p b
  have hm := Submodule.mem_map_of_mem (f := f) hraw
  rw [map_sub,hp _ huw,hp _ hvw] at hm
  have hterms := braidColumnLoadingProjection_map_lowSpan_le_same_bottom
    (Q := Q) (Λ := Λ) s b ρ hρ (subProds m u) (u.length - 2) hm
  refine (Submodule.span_le.mpr ?_) hterms
  rintro _ ⟨x,a,hsub,hshort,he,rfl⟩
  have hlen : length m x < length m w := by
    rw [hu.2,huw] at hshort
    omega
  have hP : braidColumnIndexEarlier s x w :=
    Or.inr ⟨congrArg blackCount he,
      fun i j => by simpa only [huw] using rk_le_of_mem_subProds hu hsub i j,hlen⟩
  have H := braidColumnBottomBlock_pbw_mem_span_at (Q := Q) (Λ := Λ)
    s hs σ ρ hρ (fun x => braidColumnIndexEarlier s x w)
    (fun v j hj hd hb h => braidColumnIndexEarlier_trans s
      (braidColumnIndexEarlier_of_descent s ρ hρ v j hj hd hb) h)
    (fun v u hsu hlu hbu h => braidColumnIndexEarlier_trans s
      (braidColumnIndexEarlier_of_subword s ρ hρ hsu hlu hbu) h)
    x (he ▸ hword) hP (monomial a 1)
  rwa [he] at H

end Categorification.Stendhal
