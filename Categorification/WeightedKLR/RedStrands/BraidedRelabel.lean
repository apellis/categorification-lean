/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity
import Categorification.KLR.Reindex

set_option backward.isDefEq.respectTransparency false

/-!
# Relabelling the red strands of braided Stendhal diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1. The
algebra of braided Stendhal diagrams depends on the sequence `λ_1, …, λ_ℓ` only up to
relabelling the red strands: for a permutation `σ` of the red labels and `Λ' = Λ ∘ σ`, the
relabelling `λ'_r ↦ λ_{σ r}` is an isomorphism `B̃(Λ') ≃ B̃(Λ)`, sending the idempotent of red
order `κ` to that of red order `σ ∘ κ` and violated idempotents to violated idempotents. This
identifies the corner of any red order with the corner of the order `λ'_1, …, λ'_ℓ`, so the
results proved for the identity order (`violCornerEquiv`, `B_e ≃ T^λ`) hold at every red order
with `λ` replaced by the reordered sequence; Webster uses this implicitly when he writes
`T^{wλ}` for the corner at `wλ`.

## Main definitions and results

* `SeqRelabel.ofRedPerm σ h` : the relabelling of sequences of Stendhal weight along `σ`.
* `BraidedStendhalAlgebra.relabelEquiv σ h` : `B̃(Λ') ≃ B̃(Λ)`.
* `BraidedStendhalAlgebra.relabelEquiv_redProj` : `e_κ ↦ e_{σ ∘ κ}`.
* `BraidedStendhalAlgebra.relabelEquiv_mem_violIdeal_iff` : the violated ideals correspond.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ Λ' : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν

/-! ### Corners along ring isomorphisms -/

/-- A ring isomorphism sending the idempotent `e` to `e'` restricts to an isomorphism of the
corners `eRe ≃ e'Se'`. -/
def _root_.IsIdempotentElem.cornerRingEquiv {R S : Type*} [Ring R] [Ring S] {e : R} {e' : S}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (f : R ≃+* S) (hf : f e = e') :
    he.Corner ≃+* he'.Corner where
  toFun x := ⟨f x.1, by
    obtain ⟨r, hr⟩ := x.2
    exact ⟨f r, by rw [← hr, ← hf]; simp only [map_mul]⟩⟩
  invFun y := ⟨f.symm y.1, by
    obtain ⟨r, hr⟩ := y.2
    exact ⟨f.symm r, by rw [← hr, ← hf]; simp only [map_mul, RingEquiv.symm_apply_apply]⟩⟩
  left_inv x := Subtype.ext (f.symm_apply_apply _)
  right_inv y := Subtype.ext (f.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

@[simp] theorem _root_.IsIdempotentElem.cornerRingEquiv_val {R S : Type*} [Ring R] [Ring S]
    {e : R} {e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (f : R ≃+* S)
    (hf : f e = e') (x : he.Corner) : (he.cornerRingEquiv he' f hf x).1 = f x.1 := rfl

/-! ### Relabelling sequences -/

omit [DecidableEq I] in
theorem map_stendhalWeight (σ : Perm (Fin ℓ)) :
    (stendhalWeight ℓ ν).map (Sum.map id σ) = stendhalWeight ℓ ν := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, Function.comp_def,
    Sum.map_inl, id, Sum.map_inr]
  congr 1
  rw [← Function.comp_def Sum.inr σ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

namespace Seq

omit [DecidableEq I] in
/-- The sequence `(id ⊕ σ) ∘ 𝐢` of Stendhal weight. -/
def redPerm (σ : Perm (Fin ℓ)) (i : Seq μ) : Seq μ :=
  ⟨Sum.map id σ ∘ i.1, by rw [← Multiset.map_map, i.2, map_stendhalWeight]⟩

omit [DecidableEq I] in
@[simp] theorem redPerm_lbl (σ : Perm (Fin ℓ)) (i : Seq μ) (a : Fin (Multiset.card μ)) :
    (redPerm σ i).lbl a = Sum.map id σ (i.lbl a) := rfl

omit [DecidableEq I] in
theorem redPerm_redPerm (σ τ : Perm (Fin ℓ)) (i : Seq μ) :
    redPerm σ (redPerm τ i) = redPerm (σ * τ) i := by
  apply Subtype.ext; funext a
  change Sum.map id σ (Sum.map id τ (i.1 a)) = Sum.map id (σ * τ) (i.1 a)
  rcases i.1 a with _ | r <;> rfl

omit [DecidableEq I] in
theorem redPerm_one (i : Seq μ) : redPerm 1 i = i := by
  apply Subtype.ext; funext a
  change Sum.map id (1 : Perm (Fin ℓ)) (i.1 a) = i.1 a
  rcases i.1 a with _ | r <;> rfl

omit [DecidableEq I] in
/-- Relabelling the red strands along `σ` as an equivalence of sequences. -/
def redPermEquiv (σ : Perm (Fin ℓ)) : Seq μ ≃ Seq μ where
  toFun := redPerm σ
  invFun := redPerm σ⁻¹
  left_inv i := by rw [redPerm_redPerm, inv_mul_cancel, redPerm_one]
  right_inv i := by rw [redPerm_redPerm, mul_inv_cancel, redPerm_one]

end Seq

omit [DecidableEq I] in
theorem stendhalQ_redPerm (σ : Perm (Fin ℓ)) (h : ∀ r, Λ' r = Λ (σ r)) (a b : I ⊕ Fin ℓ) :
    stendhalQ Q Λ (Sum.map id σ a) (Sum.map id σ b) = stendhalQ Q Λ' a b := by
  rcases a with i | r <;> rcases b with j | t <;> simp [stendhalQ, h]

/-- **Relabelling the red strands** along `σ`, for `Λ' = Λ ∘ σ`: a relabelling of the sequences
of Stendhal weight from the data `stendhalQ Q Λ'` to `stendhalQ Q Λ`. -/
def SeqRelabel.ofRedPerm (σ : Perm (Fin ℓ)) (h : ∀ r, Λ' r = Λ (σ r)) :
    SeqRelabel k (stendhalQ Q Λ') (stendhalQ Q Λ) μ μ where
  card_eq := rfl
  equiv := Seq.redPermEquiv σ
  equiv_smul j i := rfl
  lbl_eq_iff i a b := by
    change Sum.map id σ (i.lbl a) = Sum.map id σ (i.lbl b) ↔ _
    exact (Sum.map_injective.2 ⟨Function.injective_id, σ.injective⟩).eq_iff
  Q_eq i a b _ := stendhalQ_redPerm σ h _ _

/-! ### The braided algebras -/

namespace BraidedStendhalAlgebra

variable (R : SeqRelabel k (stendhalQ Q Λ') (stendhalQ Q Λ) (stendhalWeight ℓ ν)
    (stendhalWeight ℓ ν))
  (hR : ∀ (i : Seq (stendhalWeight ℓ ν)) (a : Fin (Multiset.card (stendhalWeight ℓ ν))),
    ((R.equiv i).lbl (Fin.cast R.card_eq a)).isRight = (i.lbl a).isRight)

/-- The free algebra on the generators maps to `B̃(Λ)` through a relabelling. -/
noncomputable def relabelFree : FreeAlgebra k (Gen μ) →ₐ[k] BraidedStendhalAlgebra k Q Λ ν :=
  (ofKLR k Q Λ ν).comp ((KLRAlgebra.relabelHom R).comp (KLRAlgebra.mk k _ _))

include hR in
theorem relabelFree_rel ⦃u v : FreeAlgebra k (Gen μ)⦄ (h : BraidedRel k Q Λ' ν u v) :
    relabelFree R u = relabelFree R v := by
  cases h with
  | klr h =>
    have : KLRAlgebra.mk k (stendhalQ Q Λ') (stendhalWeight ℓ ν) u =
        KLRAlgebra.mk k (stendhalQ Q Λ') (stendhalWeight ℓ ν) v := RingQuot.mkAlgHom_rel k h
    simp only [relabelFree, AlgHom.comp_apply, this]
  | red_dot a i h =>
    simp only [relabelFree, AlgHom.comp_apply, map_mul, map_zero]
    change ofKLR k Q Λ ν (KLRAlgebra.relabelHom R (KLRAlgebra.x a)) *
      ofKLR k Q Λ ν (KLRAlgebra.relabelHom R (KLRAlgebra.e i)) = 0
    rw [KLRAlgebra.relabelHom_x, KLRAlgebra.relabelHom_e, ← map_mul]
    exact ofKLR_x_mul_e_of_red _ _ (by rw [hR]; exact h)

/-- **Relabelling** `B̃(Λ') → B̃(Λ)` along a relabelling of sequences that preserves the colour
(black or red) of every strand. -/
noncomputable def relabelHom :
    BraidedStendhalAlgebra k Q Λ' ν →ₐ[k] BraidedStendhalAlgebra k Q Λ ν :=
  RingQuot.liftAlgHom k ⟨relabelFree R, relabelFree_rel R hR⟩

theorem relabelHom_ofKLR (u : KLR.KLRAlgebra k (stendhalQ Q Λ') μ) :
    relabelHom R hR (ofKLR k Q Λ' ν u) = ofKLR k Q Λ ν (KLRAlgebra.relabelHom R u) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective u
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

omit [DecidableEq I] in
include hR in
theorem symm_isRight (i : Seq μ) (a : Fin (Multiset.card μ)) :
    ((R.symm.equiv i).lbl (Fin.cast R.symm.card_eq a)).isRight = (i.lbl a).isRight := by
  have := hR (R.equiv.symm i) (Fin.cast R.symm.card_eq a)
  simp only [Equiv.apply_symm_apply, Fin.cast_eq_self] at this
  exact this.symm

/-- **Relabelling** `B̃(Λ') ≃ B̃(Λ)` along a relabelling of sequences that preserves the colour
of every strand. -/
noncomputable def relabelAlgEquiv :
    BraidedStendhalAlgebra k Q Λ' ν ≃ₐ[k] BraidedStendhalAlgebra k Q Λ ν :=
  AlgEquiv.ofAlgHom (relabelHom R hR) (relabelHom R.symm (fun i a => symm_isRight R hR i a))
    (by
      ext y
      obtain ⟨u, rfl⟩ := ofKLR_surjective y
      simp only [AlgHom.comp_apply, relabelHom_ofKLR, AlgHom.id_apply]
      rw [← AlgHom.comp_apply (KLRAlgebra.relabelHom R),
        show (KLRAlgebra.relabelHom R).comp (KLRAlgebra.relabelHom R.symm) = AlgHom.id _ _ by
          simpa using KLRAlgebra.relabelHom_symm_comp R.symm]
      rfl)
    (by
      ext y
      obtain ⟨u, rfl⟩ := ofKLR_surjective y
      simp only [AlgHom.comp_apply, relabelHom_ofKLR, AlgHom.id_apply]
      rw [← AlgHom.comp_apply (KLRAlgebra.relabelHom R.symm), KLRAlgebra.relabelHom_symm_comp]
      rfl)

@[simp] theorem relabelAlgEquiv_ofKLR (u : KLR.KLRAlgebra k (stendhalQ Q Λ') μ) :
    relabelAlgEquiv R hR (ofKLR k Q Λ' ν u) = ofKLR k Q Λ ν (KLRAlgebra.relabelHom R u) :=
  relabelHom_ofKLR R hR u

/-! ### Relabelling along a permutation of the red labels -/

section RedPerm

variable (σ : Perm (Fin ℓ)) (h : ∀ r, Λ' r = Λ (σ r))

omit [DecidableEq I] in
theorem ofRedPerm_isRight (i : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (((SeqRelabel.ofRedPerm (k := k) (Q := Q) σ h).equiv i).lbl
      (Fin.cast (SeqRelabel.ofRedPerm (k := k) (Q := Q) σ h).card_eq a)).isRight =
        (i.lbl a).isRight := by
  change (Sum.map id σ (i.lbl a)).isRight = _
  rcases i.lbl a with _ | _ <;> rfl

/-- **Relabelling the red strands** (arXiv:1309.3796v2, §6.1): for `Λ' = Λ ∘ σ`, the relabelling
`λ'_r ↦ λ_{σ r}` is an isomorphism `B̃(Λ') ≃ B̃(Λ)`. -/
noncomputable def redPermAlgEquiv :
    BraidedStendhalAlgebra k Q Λ' ν ≃ₐ[k] BraidedStendhalAlgebra k Q Λ ν :=
  relabelAlgEquiv (SeqRelabel.ofRedPerm σ h) (ofRedPerm_isRight σ h)

theorem redPermAlgEquiv_e (i : Seq μ) :
    redPermAlgEquiv σ h (ofKLR k Q Λ' ν (KLRAlgebra.e i)) =
      ofKLR k Q Λ ν (KLRAlgebra.e (Seq.redPerm σ i)) := by
  rw [redPermAlgEquiv, relabelAlgEquiv_ofKLR, KLRAlgebra.relabelHom_e]
  rfl

omit [DecidableEq I] in
theorem redWord_redPerm (i : Seq μ) : redWord (Seq.redPerm σ i) = (redWord i).map σ := by
  simp only [redWord, Seq.redPerm_lbl, List.map_filterMap]
  congr 1
  funext a
  rcases i.lbl a with _ | _ <;> rfl

/-- The relabelling sends the idempotent of red order `κ` to that of red order `σ ∘ κ`. -/
theorem redPermAlgEquiv_redProj (κ : List (Fin ℓ)) :
    redPermAlgEquiv σ h (redProj k Q Λ' ν κ) = redProj k Q Λ ν (κ.map σ) := by
  rw [redProj, redIdem, map_sum, map_sum, redProj, redIdem, map_sum]
  refine Finset.sum_equiv (Seq.redPermEquiv σ) (fun i => ?_) (fun i _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ redWord (Seq.redPerm σ i) = _
    rw [redWord_redPerm, (List.map_injective_iff.2 σ.injective).eq_iff]
  · exact redPermAlgEquiv_e σ h i

omit [DecidableEq I] in
theorem isViolated_redPerm (i : Seq μ) : IsViolated (Seq.redPerm σ i) ↔ IsViolated i := by
  simp only [IsViolated, Seq.redPerm_lbl]
  refine exists_congr fun _ => ?_
  rcases i.lbl _ with _ | _ <;> rfl

theorem redPermAlgEquiv_mem_violIdeal_iff (x : BraidedStendhalAlgebra k Q Λ' ν) :
    redPermAlgEquiv σ h x ∈ violIdeal k Q Λ ν ↔ x ∈ violIdeal k Q Λ' ν := by
  set f := redPermAlgEquiv (k := k) (Q := Q) (ν := ν) σ h
  constructor
  · intro hx
    have hle : violIdeal k Q Λ ν ≤ TwoSidedIdeal.comap f.symm (violIdeal k Q Λ' ν) := by
      rw [violIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
      have : f.symm (ofKLR k Q Λ ν (KLRAlgebra.e j)) =
          ofKLR k Q Λ' ν (KLRAlgebra.e (Seq.redPerm σ⁻¹ j)) := by
        rw [AlgEquiv.symm_apply_eq, redPermAlgEquiv_e, Seq.redPerm_redPerm, mul_inv_cancel,
          Seq.redPerm_one]
      rw [this]
      exact TwoSidedIdeal.subset_span ⟨_, (isViolated_redPerm σ⁻¹ j).2 hj, rfl⟩
    have := hle hx
    rwa [TwoSidedIdeal.mem_comap, AlgEquiv.symm_apply_apply] at this
  · intro hx
    have hle : violIdeal k Q Λ' ν ≤ TwoSidedIdeal.comap f (violIdeal k Q Λ ν) := by
      rw [violIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, redPermAlgEquiv_e]
      exact TwoSidedIdeal.subset_span ⟨_, (isViolated_redPerm σ i).2 hi, rfl⟩
    have := hle hx
    rwa [TwoSidedIdeal.mem_comap] at this

/-- The relabelling descends to the quotients by violated idempotents. -/
noncomputable def violRedPermEquiv : ViolQuotient k Q Λ' ν ≃ₐ[k] ViolQuotient k Q Λ ν :=
  RingCon.congrₐ k (redPermAlgEquiv σ h) (by
    ext x y
    rw [RingCon.comap_rel, TwoSidedIdeal.rel_iff, TwoSidedIdeal.rel_iff]
    change _ ↔ redPermAlgEquiv σ h x - redPermAlgEquiv σ h y ∈ _
    rw [← map_sub, redPermAlgEquiv_mem_violIdeal_iff])

theorem violRedPermEquiv_violMk (x : BraidedStendhalAlgebra k Q Λ' ν) :
    violRedPermEquiv σ h (violMk k Q Λ' ν x) = violMk k Q Λ ν (redPermAlgEquiv σ h x) :=
  rfl

/-- The relabelling identifies the corner of the violated quotient at red order `κ` with the one
at red order `σ ∘ κ`. -/
noncomputable def violCornerRedPermEquiv (κ : List (Fin ℓ)) :
    ((isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ') (ν := ν) κ).map
      (violMk k Q Λ' ν)).Corner ≃+*
    ((isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) (κ.map σ)).map
      (violMk k Q Λ ν)).Corner :=
  IsIdempotentElem.cornerRingEquiv _ _ (violRedPermEquiv σ h).toRingEquiv (by
    change violRedPermEquiv σ h (violMk k Q Λ' ν _) = _
    rw [violRedPermEquiv_violMk, redPermAlgEquiv_redProj])

end RedPerm

omit [DecidableEq I] in
/-- Every ordering of the red labels is `σ ∘ (1, …, ℓ)` for a permutation `σ`. -/
theorem exists_perm_eq_map_finRange {κ : List (Fin ℓ)} (hκ : κ.Perm (List.finRange ℓ)) :
    ∃ σ : Perm (Fin ℓ), κ = (List.finRange ℓ).map σ := by
  have hlen : κ.length = ℓ := by simpa using hκ.length_eq
  have hnd : κ.Nodup := hκ.nodup_iff.2 (List.nodup_finRange ℓ)
  refine ⟨(finCongr hlen.symm).trans
    (hnd.getEquivOfForallMemList κ fun r => hκ.mem_iff.2 (List.mem_finRange r)), ?_⟩
  apply List.ext_get (by simp [hlen])
  intro n h₁ h₂
  simp [List.Nodup.getEquivOfForallMemList]

/-! ### The corner at an arbitrary red order -/

section AnyOrder

variable {I₀ : Type} [DecidableEq I₀] {Q₀ : I₀ → I₀ → MvPolynomial (Fin 2) k}
  {Λ₀ : Fin ℓ → I₀ →₀ ℕ} {ν₀ : Multiset I₀}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν₀))) → List ℕ}

/-- **The corner of `B` at the red order `σ ∘ (1, …, ℓ)` is `T^{λ ∘ σ}`** (arXiv:1309.3796v2,
§6.1, where this corner is written `T^{wλ}`), for symmetric `Q`: relabel the red strands to the
identity order and apply `violCornerEquiv`. -/
noncomputable def violCornerRedPermTensorEquiv (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q₀)
    (σ : Perm (Fin ℓ)) :
    ((isIdempotentElem_redProj (k := k) (Q := Q₀) (Λ := Λ₀) (ν := ν₀)
      ((List.finRange ℓ).map σ)).map (violMk k Q₀ Λ₀ ν₀)).Corner ≃+*
      TensorProductAlgebra k Q₀ (Λ₀ ∘ σ) ν₀ :=
  (violCornerRedPermEquiv (Λ' := Λ₀ ∘ σ) σ (fun _ => rfl) (List.finRange ℓ)).symm.trans
    (violCornerEquiv (Λ := Λ₀ ∘ σ) hρ hQ)

end AnyOrder

end BraidedStendhalAlgebra

end Categorification.Stendhal
