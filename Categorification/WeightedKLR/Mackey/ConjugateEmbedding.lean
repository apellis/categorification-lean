/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Parabolic

/-!
# Chamber embeddings that differ by a relabelling of strands

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4). The balancedness of the shuffle
element compares a diagram of the middle parabolic, drawn in the order `a b c d` of its four
blocks, with the same diagram drawn in the order `a c b d`. The two drawings are images of chamber
embeddings `J, J'` of the same arrangement whose strand maps differ by a relabelling `ρ` of the
strands of `ν`: `J' s = ρ (J s)`. This file shows that in the polynomial representation the block
operators of `J' x` are those of `J x` conjugated by the renaming of variables along `ρ`, block by
block of image chambers (`ChamberEmbedding.isConjOn_toHom`). The comparison is local: it does not
need `J'` to send chambers to the `ρ`-translates of the chambers of `J`.

## Main definitions

* `GalleryAlgebra.IsConjOn χ χ' ρ z' z`: `z` and `z'` vanish outside the blocks of the chamber
  families `χ` and `χ'`, and `z'_{χ' q, χ' q'} = ρ ∘ z_{χ q, χ q'} ∘ ρ⁻¹`.

## Main results

* `StrandEmbedding.comap_hyp`, `StrandEmbedding.reverses_hyp`: `ρ` carries the hyperplanes of `J`
  to those of `J'`, without reversing them.
* `ChamberEmbedding.perm_eq_conj`: `J' g = ρ (J g) ρ⁻¹` on relabellings.
* `GalleryAlgebra.IsConjOn.add`, `.sum`, `.smul`, `.mul`: the relation is compatible with the
  algebra operations.
* `ChamberEmbedding.isConjOn_toHom`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv GalleryAlgebra FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace StrandEmbedding

variable {ν₀ : I →₀ ℕ} {j j' : StrandEmbedding ν₀ ν} {ρ : ColPerm ν}

omit [DecidableEq I] in
theorem inv_apply_of_eq (hρ : ∀ s, j' s = ρ.1 (j s)) (s : Strand ν₀) : ρ.1⁻¹ (j' s) = j s := by
  rw [hρ]
  exact ρ.1.symm_apply_apply _

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The relabelling `ρ` reads the hyperplanes of `j'` as those of `j`. -/
theorem comap_hyp (hρ : ∀ s, j' s = ρ.1 (j s)) (h : Hyp Γ ν₀) :
    (j'.hyp h).comap ρ = j.hyp h := by
  rcases h with w | d
  · refine congrArg Sum.inl (Subtype.ext (Prod.ext rfl (Prod.ext ?_ ?_)))
    · exact inv_apply_of_eq hρ w.src
    · exact inv_apply_of_eq hρ w.tgt
  · refine congrArg Sum.inr (Diag.eq_of_pair ?_)
    rcases Diag.comap_spec ρ (j'.diag d) with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩
    · left
      exact ⟨h₁.trans (inv_apply_of_eq hρ _), h₂.trans (inv_apply_of_eq hρ _)⟩
    · right
      exact ⟨h₁.trans (inv_apply_of_eq hρ _), h₂.trans (inv_apply_of_eq hρ _)⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The relabelling `ρ` does not reverse the hyperplanes of `j'`. -/
theorem reverses_hyp (hρ : ∀ s, j' s = ρ.1 (j s)) (h : Hyp Γ ν₀) :
    (j'.hyp h).reverses ρ = false := by
  rcases h with w | d
  · rfl
  · show (Diag.comap ρ (j'.diag d)).2 = false
    rcases Diag.comap_spec ρ (j'.diag d) with ⟨h₀, -, -⟩ | ⟨-, h₁, h₂⟩
    · exact h₀
    · exfalso
      have hlt := (Diag.comap ρ (j'.diag d)).1.2.2
      have e₁ : (Diag.comap ρ (j'.diag d)).1.fst = j d.snd := h₁.trans (inv_apply_of_eq hρ _)
      have e₂ : (Diag.comap ρ (j'.diag d)).1.snd = j d.fst := h₂.trans (inv_apply_of_eq hρ _)
      have hlt' : (j d.snd).2.val < (j d.fst).2.val := by
        have : ((Diag.comap ρ (j'.diag d)).1.fst).2.val <
            ((Diag.comap ρ (j'.diag d)).1.snd).2.val := hlt
        rwa [e₁, e₂] at this
      exact lt_asymm hlt' (j.rank_lt _ _ d.2.1 d.2.2)

end StrandEmbedding

namespace ChamberEmbedding

variable {ν₀ : I →₀ ℕ} {J J' : ChamberEmbedding Γ ν₀ ν} {ρ : ColPerm ν}

omit [DecidableEq I] in
/-- The extensions of relabellings of `J` and `J'` are conjugate by `ρ`. -/
theorem perm_eq_conj (hρ : ∀ s, J'.toFun s = ρ.1 (J.toFun s)) (g : ColPerm ν₀) :
    J'.perm g = ρ * J.perm g * ρ⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro t
  show (J'.perm g).1 t = ρ.1 ((J.perm g).1 (ρ.1⁻¹ t))
  by_cases ht : t ∈ Set.range J'.toFun
  · obtain ⟨s, rfl⟩ := ht
    rw [J'.perm_apply, hρ, hρ, show ρ.1⁻¹ (ρ.1 (J.toFun s)) = J.toFun s from
      ρ.1.symm_apply_apply _, J.perm_apply]
  · have ht' : ρ.1⁻¹ t ∉ Set.range J.toFun := by
      rintro ⟨s, hs⟩
      refine ht ⟨s, ?_⟩
      rw [hρ, hs]
      exact ρ.1.apply_symm_apply t
    rw [J'.perm_apply_of_not_mem _ _ ht, J.perm_apply_of_not_mem _ _ ht']
    exact (ρ.1.apply_symm_apply t).symm

end ChamberEmbedding

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ren_comp_ren_inv (ρ : ColPerm ν) :
    ren (k := k) ρ ∘ₗ ren ρ⁻¹ = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, ← ren_mul_apply, mul_inv_cancel, ren_one]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ren_inv_comp_ren (ρ : ColPerm ν) :
    ren (k := k) ρ⁻¹ ∘ₗ ren ρ = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, ← ren_mul_apply, inv_mul_cancel, ren_one]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem ren_inv_apply_ren (ρ : ColPerm ν) (f : PolyRing ν k) :
    ren (k := k) ρ⁻¹ (ren ρ f) = f := by
  rw [← ren_mul_apply, inv_mul_cancel, ren_one, LinearMap.id_apply]

namespace GalleryAlgebra

variable (hΓ : Γ.PSymm)

theorem blockOp_of_galleryRep_eq_blk_eq_ite {A B : FullChamber Γ ν} {z : GalleryAlgebra k Γ ν}
    {a : PolyRing ν k →ₗ[k] PolyRing ν k} (h : galleryRep k hΓ z = blk k A B a)
    (D C : FullChamber Γ ν) : blockOp k hΓ D C z = if C = A ∧ D = B then a else 0 := by
  refine _root_.LinearMap.ext fun f => ?_
  rw [blockOp_apply, h, blk_apply]
  by_cases hC : C = A
  · subst hC
    by_cases hD : D = B
    · subst hD
      simp
    · simp [hD]
  · simp [Pi.single_apply, Ne.symm hC, hC]

variable {Q : Type*}

variable (k) in
/-- `z` and `z'` vanish outside the blocks of the chamber families `χ` and `χ'`, and the block
operators of `z'` at `χ'` are those of `z` at `χ` conjugated by the renaming along `ρ`. -/
def IsConjOn (χ χ' : Q → FullChamber Γ ν) (ρ : ColPerm ν) (z' z : GalleryAlgebra k Γ ν) :
    Prop :=
  (∀ D C, ((∀ q, χ q ≠ D) ∨ ∀ q, χ q ≠ C) → blockOp k hΓ D C z = 0) ∧
  (∀ D C, ((∀ q, χ' q ≠ D) ∨ ∀ q, χ' q ≠ C) → blockOp k hΓ D C z' = 0) ∧
  ∀ q q', blockOp k hΓ (χ' q) (χ' q') z' = ren ρ ∘ₗ blockOp k hΓ (χ q) (χ q') z ∘ₗ ren ρ⁻¹

namespace IsConjOn

variable {hΓ} {χ χ' : Q → FullChamber Γ ν} {ρ : ColPerm ν}

theorem zero : IsConjOn k hΓ χ χ' ρ 0 0 :=
  ⟨fun _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ => by simp⟩

theorem add {z z' w w' : GalleryAlgebra k Γ ν} (h : IsConjOn k hΓ χ χ' ρ z' z)
    (h' : IsConjOn k hΓ χ χ' ρ w' w) : IsConjOn k hΓ χ χ' ρ (z' + w') (z + w) := by
  refine ⟨fun D C hDC => ?_, fun D C hDC => ?_, fun q q' => ?_⟩
  · rw [blockOp_add, h.1 D C hDC, h'.1 D C hDC, add_zero]
  · rw [blockOp_add, h.2.1 D C hDC, h'.2.1 D C hDC, add_zero]
  · rw [blockOp_add, blockOp_add, h.2.2, h'.2.2, LinearMap.add_comp, LinearMap.comp_add]

theorem smul {z z' : GalleryAlgebra k Γ ν} (h : IsConjOn k hΓ χ χ' ρ z' z) (c : k) :
    IsConjOn k hΓ χ χ' ρ (c • z') (c • z) := by
  refine ⟨fun D C hDC => ?_, fun D C hDC => ?_, fun q q' => ?_⟩
  · rw [blockOp_smul, h.1 D C hDC, smul_zero]
  · rw [blockOp_smul, h.2.1 D C hDC, smul_zero]
  · rw [blockOp_smul, blockOp_smul, h.2.2, LinearMap.smul_comp, LinearMap.comp_smul]

theorem sum {ι : Type*} (s : Finset ι) {z z' : ι → GalleryAlgebra k Γ ν}
    (h : ∀ i ∈ s, IsConjOn k hΓ χ χ' ρ (z' i) (z i)) :
    IsConjOn k hΓ χ χ' ρ (∑ i ∈ s, z' i) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsConjOn k hΓ χ χ' ρ 0 0)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sum_blockOp_comp [Fintype Q] (hχ : Function.Injective χ) {a z : GalleryAlgebra k Γ ν}
    (ha : ∀ D C, ((∀ q, χ q ≠ D) ∨ ∀ q, χ q ≠ C) → blockOp k hΓ D C a = 0) (D C) :
    ∑ E, blockOp k hΓ D E a ∘ₗ blockOp k hΓ E C z =
      ∑ p, blockOp k hΓ D (χ p) a ∘ₗ blockOp k hΓ (χ p) C z := by
  classical
  refine (Fintype.sum_of_injective χ hχ _ _ (fun E hE => ?_) fun p => rfl).symm
  rw [ha D E (Or.inr fun q hq => hE ⟨q, hq⟩), LinearMap.zero_comp]

theorem mul [Fintype Q] (hχ : Function.Injective χ) (hχ' : Function.Injective χ')
    {a a' z z' : GalleryAlgebra k Γ ν} (ha : IsConjOn k hΓ χ χ' ρ a' a)
    (hz : IsConjOn k hΓ χ χ' ρ z' z) : IsConjOn k hΓ χ χ' ρ (a' * z') (a * z) := by
  refine ⟨fun D C hDC => ?_, fun D C hDC => ?_, fun q q' => ?_⟩
  · rw [blockOp_mul_eq_sum]
    refine Finset.sum_eq_zero fun E _ => ?_
    rcases hDC with hD | hC
    · rw [ha.1 D E (Or.inl hD), LinearMap.zero_comp]
    · rw [hz.1 E C (Or.inr hC), LinearMap.comp_zero]
  · rw [blockOp_mul_eq_sum]
    refine Finset.sum_eq_zero fun E _ => ?_
    rcases hDC with hD | hC
    · rw [ha.2.1 D E (Or.inl hD), LinearMap.zero_comp]
    · rw [hz.2.1 E C (Or.inr hC), LinearMap.comp_zero]
  · rw [blockOp_mul_eq_sum, blockOp_mul_eq_sum, sum_blockOp_comp hχ ha.1,
      sum_blockOp_comp hχ' ha.2.1]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ha.2.2, hz.2.2]
    simp only [LinearMap.comp_apply, ren_inv_apply_ren]

theorem of_blk (hχ : Function.Injective χ) (hχ' : Function.Injective χ') {q₁ q₂ : Q}
    {z z' : GalleryAlgebra k Γ ν} {a : PolyRing ν k →ₗ[k] PolyRing ν k}
    (h : galleryRep k hΓ z = blk k (χ q₁) (χ q₂) a)
    (h' : galleryRep k hΓ z' = blk k (χ' q₁) (χ' q₂) (ren ρ ∘ₗ a ∘ₗ ren ρ⁻¹)) :
    IsConjOn k hΓ χ χ' ρ z' z := by
  refine ⟨fun D C hDC => ?_, fun D C hDC => ?_, fun q q' => ?_⟩
  · rw [blockOp_of_galleryRep_eq_blk_eq_ite hΓ h, ite_eq_right]
    rintro ⟨rfl, rfl⟩
    rcases hDC with hD | hC
    · exact hD q₂ rfl
    · exact hC q₁ rfl
  · rw [blockOp_of_galleryRep_eq_blk_eq_ite hΓ h', ite_eq_right]
    rintro ⟨rfl, rfl⟩
    rcases hDC with hD | hC
    · exact hD q₂ rfl
    · exact hC q₁ rfl
  · rw [blockOp_of_galleryRep_eq_blk_eq_ite hΓ h, blockOp_of_galleryRep_eq_blk_eq_ite hΓ h']
    by_cases hq : q' = q₁ ∧ q = q₂
    · obtain ⟨rfl, rfl⟩ := hq
      simp
    · rw [ite_eq_right (fun e => hq ⟨hχ' e.1, hχ' e.2⟩),
        ite_eq_right (fun e => hq ⟨hχ e.1, hχ e.2⟩)]
      simp

theorem of_blk' (hχ : Function.Injective χ) (hχ' : Function.Injective χ') {q₁ q₂ : Q}
    {z z' : GalleryAlgebra k Γ ν} {a a' : PolyRing ν k →ₗ[k] PolyRing ν k}
    (h : galleryRep k hΓ z = blk k (χ q₁) (χ q₂) a)
    (h' : galleryRep k hΓ z' = blk k (χ' q₁) (χ' q₂) a') (ha : a' = ren ρ ∘ₗ a ∘ₗ ren ρ⁻¹) :
    IsConjOn k hΓ χ χ' ρ z' z :=
  of_blk hχ hχ' h (ha ▸ h')

end IsConjOn

theorem galleryRep_poly_mul_e (f : PolyRing ν k) (A : FullChamber Γ ν) :
    galleryRep k hΓ (poly f * e A) = blk k A A (LinearMap.mulLeft k f) := by
  rw [map_mul, galleryRep_poly, galleryRep_e, Module.End.mul_eq_comp, diagOp_comp_blk,
    LinearMap.comp_id]

end GalleryAlgebra

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ren_comp_mulLeft_comp_ren_inv (ρ : ColPerm ν) (f : PolyRing ν k) :
    ren ρ ∘ₗ LinearMap.mulLeft k f ∘ₗ ren ρ⁻¹ = LinearMap.mulLeft k (ren ρ f) := by
  refine LinearMap.ext fun g => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [show ren ρ (f * ren ρ⁻¹ g) = ren ρ f * ren ρ (ren ρ⁻¹ g) from map_mul (rename _) _ _,
    ← ren_mul_apply, mul_inv_cancel, ren_one, LinearMap.id_apply]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ren_comp_id_comp_ren_inv (ρ : ColPerm ν) :
    ren (k := k) ρ ∘ₗ LinearMap.id ∘ₗ ren ρ⁻¹ = LinearMap.id := by
  rw [LinearMap.id_comp, ren_comp_ren_inv]

namespace ChamberEmbedding

variable {ν₀ : I →₀ ℕ} {J J' : ChamberEmbedding Γ ν₀ ν} {ρ : ColPerm ν}

omit [DecidableEq I] in
theorem ren_rename (hρ : ∀ s, J'.toFun s = ρ.1 (J.toFun s)) (f : PolyRing ν₀ k) :
    ren ρ (rename J.toFun f) = rename J'.toFun f := by
  simp only [ren, AlgHom.toLinearMap_apply, rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => (hρ s).symm)

theorem stepOp_conj (hρ : ∀ s, J'.toFun s = ρ.1 (J.toFun s)) (C D : FullChamber Γ ν₀) :
    stepOp (k := k) Γ (J'.chamber C) (J'.chamber D) =
      ren ρ ∘ₗ stepOp Γ (J.chamber C) (J.chamber D) ∘ₗ ren ρ⁻¹ := by
  by_cases hCD : ∃ h, C.Adjacent D h
  · obtain ⟨h, hh⟩ := hCD
    rw [stepOp_eq (J'.adjacent_chamber hh), stepOp_eq (J.adjacent_chamber hh), J'.chamber_hyp,
      J.chamber_hyp]
    have := ren_comp_hypOp (k := k) ρ (J'.hyp h) (C.1 h)
    rw [StrandEmbedding.comap_hyp (j := J.toStrandEmbedding) (j' := J'.toStrandEmbedding) hρ,
      StrandEmbedding.reverses_hyp (j := J.toStrandEmbedding) (j' := J'.toStrandEmbedding) hρ]
      at this
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [← LinearMap.comp_assoc, this, LinearMap.comp_assoc, ren_comp_ren_inv, LinearMap.comp_id]
  · push Not at hCD
    rw [stepOp_of_not (J'.not_adjacent_chamber hCD), stepOp_of_not (J.not_adjacent_chamber hCD),
      LinearMap.zero_comp, LinearMap.comp_zero]

omit [DecidableEq I] in
theorem ren_perm (hρ : ∀ s, J'.toFun s = ρ.1 (J.toFun s)) (g : ColPerm ν₀) :
    ren (k := k) (J'.perm g) = ren ρ ∘ₗ ren (J.perm g) ∘ₗ ren ρ⁻¹ := by
  refine LinearMap.ext fun f => ?_
  rw [perm_eq_conj hρ, ren_mul_apply, ren_mul_apply]
  rfl

variable (hΓ : Γ.PSymm)

/-- **Conjugate chamber embeddings.** If the strand maps of two chamber embeddings differ by a
relabelling, `J' s = ρ (J s)`, then the block operators of `J' x` at the chambers of `J'` are
those of `J x` at the chambers of `J`, conjugated by the renaming of variables along `ρ`. -/
theorem isConjOn_galleryHom (hρ : ∀ s, J'.toFun s = ρ.1 (J.toFun s))
    (x : GalleryAlgebra k Γ ν₀) :
    IsConjOn k hΓ J.chamber J'.chamber ρ (J'.galleryHom x).1 (J.galleryHom x).1 := by
  have hχ := J.chamber_injective
  have hχ' := J'.chamber_injective
  have hidem : IsConjOn k hΓ J.chamber J'.chamber ρ J'.idem J.idem :=
    IsConjOn.sum _ fun C _ => IsConjOn.of_blk' hχ hχ' (galleryRep_e hΓ _) (galleryRep_e hΓ _)
      (ren_comp_id_comp_ren_inv ρ).symm
  obtain ⟨a, rfl⟩ := mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, IsIdempotentElem.corner_val_algebraMap,
      IsIdempotentElem.corner_val_algebraMap]
    exact hidem.smul c
  | grade1 g =>
    cases g with
    | idem C =>
      show IsConjOn k hΓ _ _ ρ (J'.galleryHom (e C)).1 (J.galleryHom (e C)).1
      rw [galleryHom_e, galleryHom_e]
      exact IsConjOn.of_blk' hχ hχ' (galleryRep_e hΓ _) (galleryRep_e hΓ _)
        (ren_comp_id_comp_ren_inv ρ).symm
    | poly f =>
      show IsConjOn k hΓ _ _ ρ (J'.galleryHom (poly f)).1 (J.galleryHom (poly f)).1
      rw [galleryHom_poly, galleryHom_poly, idem, idem, Finset.mul_sum, Finset.mul_sum]
      refine IsConjOn.sum _ fun C _ => IsConjOn.of_blk' hχ hχ'
        (galleryRep_poly_mul_e hΓ _ _) (galleryRep_poly_mul_e hΓ _ _) ?_
      rw [ren_comp_mulLeft_comp_ren_inv, ren_rename hρ]
    | step C D =>
      show IsConjOn k hΓ _ _ ρ (J'.galleryHom (t C D)).1 (J.galleryHom (t C D)).1
      rw [galleryHom_t, galleryHom_t]
      exact IsConjOn.of_blk' hχ hχ' (galleryRep_t hΓ _ _) (galleryRep_t hΓ _ _)
        (stepOp_conj hρ C D)
    | relabel g C =>
      show IsConjOn k hΓ _ _ ρ (J'.galleryHom (r g C)).1 (J.galleryHom (r g C)).1
      rw [galleryHom_r, galleryHom_r]
      refine IsConjOn.of_blk' (q₁ := C) (q₂ := g • C) hχ hχ' ?_ ?_ (ren_perm hρ g)
      · rw [galleryRep_r, J.smul_chamber]
      · rw [galleryRep_r, J'.smul_chamber]
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul]
    exact ha.mul hχ hχ' hb
  | add a b ha hb =>
    rw [map_add, map_add, map_add]
    exact ha.add hb

end ChamberEmbedding

end Categorification.WeightedKLR
