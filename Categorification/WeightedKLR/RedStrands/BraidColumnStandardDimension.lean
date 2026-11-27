/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnChoice
import Categorification.WeightedKLR.RedStrands.BraidSequenceStandardFiltration
import Categorification.WeightedKLR.RedStrands.ViolCornerRelabelFiltration

/-!
# The standards of a braid column are row standards

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 6.11. At an eligible index of the braid column of `e(t) V e_σ`, the bottom loading is made
of the bottom blocks of the wiring, reordered by `σ`. Relabelling its red strands along `σ`
gives the row loading of the block words reordered by `σ` (`ofFn_relabel_bottom`), so the
loading standard at that index has the dimension of the row standard of those words
(`finrank_loadingStandard_bottom`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Equiv FirstWeight BraidedStendhalAlgebra
open scoped BigOperators

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ}

/-! ### Words of loadings made of blocks -/

theorem map_inl_filterMap_getLeft {I J : Type*} :
    ∀ (L : List (I ⊕ J)), (∀ x ∈ L, x.isLeft) → (L.filterMap Sum.getLeft?).map Sum.inl = L
  | [], _ => rfl
  | .inl i :: L, h => by
    rw [List.filterMap_cons, Sum.getLeft?_inl, List.map_cons,
      map_inl_filterMap_getLeft L fun x hx => h x (List.mem_cons_of_mem _ hx)]
  | .inr _ :: _, h => absurd (h _ List.mem_cons_self) (by simp)

/-- **A loading made of red-led blocks is a row loading.** -/
theorem ofFn_eq_rowWord {I : Type} (n : Fin ℓ → ℕ) {d : ℕ} (hn : (∑ r, (n r + 1)) = d)
    (f : Fin d → I ⊕ Fin ℓ) (h0 : ∀ r, f (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (h1 : ∀ r a, a ≠ 0 → (f (braidBlockPositions n hn ⟨r, a⟩)).isLeft) :
    List.ofFn f = rowWord ℓ fun r =>
      (List.ofFn fun a : Fin (n r + 1) => f (braidBlockPositions n hn ⟨r, a⟩)).filterMap
        Sum.getLeft? := by
  rw [List.ofFn_eq_map, ← flatMap_braidBlockPositions n hn, List.map_flatMap, rowWord]
  refine List.flatMap_congr fun r _ => ?_
  rw [List.ofFn_succ, List.ofFn_succ, List.map_cons, List.filterMap_cons, h0, Sum.getLeft?_inr]
  congr 1
  rw [List.map_ofFn, map_inl_filterMap_getLeft]
  · rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
    exact h1 r a.succ (Fin.succ_ne_zero a)

variable {I : Type} [DecidableEq I] {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- **The relabelled bottom of an eligible index is the row loading of its block words.** -/
theorem ofFn_relabel_bottom {t : Seq μ} {n : Fin ℓ → ℕ} {hn : (∑ r, (n r + 1)) = m}
    {φ : Perm (Fin m)}
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (σ : Perm (Fin ℓ)) :
    List.ofFn (Seq.redPerm σ⁻¹ ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • t)).lbl =
      rowWord ℓ (blockRow t n hn φ ∘ σ) := by
  have hl (r : Fin ℓ) (a : Fin (n (σ r) + 1)) :
      (Seq.redPerm σ⁻¹ ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • t)).lbl
        (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩) =
      Sum.map id ⇑(σ⁻¹) ((φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨σ r, a⟩)) := by
    rw [Seq.redPerm_lbl, braidColumnBottomBlockIndex_bottom, lbl_braidBlockPermutation_smul]
  rw [ofFn_eq_rowWord (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn)]
  · congr 1
    funext r
    simp only [Function.comp_apply, hl, blockRow]
    have hm : (List.ofFn fun a : Fin (n (σ r) + 1) =>
        Sum.map id ⇑(σ⁻¹) ((φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨σ r, a⟩))) =
        (List.ofFn fun a : Fin (n (σ r) + 1) =>
          (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨σ r, a⟩)).map (Sum.map id ⇑(σ⁻¹)) :=
      List.map_ofFn.symm
    rw [hm, List.filterMap_map]
    congr 1
    funext x
    cases x <;> rfl
  · intro r
    rw [hl, hred]
    simp
  · intro r a ha
    rw [hl]
    obtain ⟨i, hi⟩ := exists_lbl_inl hred (r := σ r) ha
    rw [hi]
    rfl

omit [DecidableEq I] in
theorem eq_rowSeq_of_ofFn (s : Seq μ) (u : Fin ℓ → List I) (hν : blockContent u = ν)
    (h : List.ofFn s.lbl = rowWord ℓ u) : s = (rowSeq u hν).1 := by
  subst hν
  apply Subtype.ext
  funext a
  have := List.ofFn_injective (h.trans (ofFn_rowLoading ℓ u).symm)
  exact congrFun this a

variable {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

theorem loadingStandardRelabel_smul_scalar (σ : Perm (Fin ℓ)) {s : Seq μ} {κ : List (Fin ℓ)}
    (hκ : redWord s = κ) (c : k)
    (z : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ) :
    loadingStandardRelabel σ hκ (c • z) = c • loadingStandardRelabel σ hκ z := by
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, loadingStandardRelabel_mk, loadingStandardRelabel_mk,
      ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    rw [violCornerRelabel_val, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
      violCornerRelabel_val, map_smul]

theorem finrank_loadingStandard_redPerm (σ : Perm (Fin ℓ)) {s : Seq μ} {κ : List (Fin ℓ)}
    (hκ : redWord s = κ) :
    Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s)
      (κ.map σ)) =
      Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ) := by
  let e : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ ≃ₗ[k]
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) (κ.map σ) :=
    { loadingStandardRelabel σ hκ with
      map_smul' := loadingStandardRelabel_smul_scalar σ hκ }
  exact e.finrank_eq.symm

end Categorification.Stendhal

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Equiv BraidedStendhalAlgebra QuantumGroup QuantumGroup.UDot

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}

/-- **The standard at an eligible index of a braid column is a row standard** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11): its dimension is that of the row standard of
`λ ∘ σ` at the block words reordered by `σ`. -/
theorem finrank_loadingStandard_bottom {t : Seq (stendhalWeight ℓ ν)} {n : Fin ℓ → ℕ}
    {hn : (∑ r, (n r + 1)) = Multiset.card (stendhalWeight ℓ ν)}
    {φ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν)))}
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r)
    (σ : Perm (Fin ℓ)) (hν : blockContent (blockRow t n hn φ ∘ σ) = ν) :
    Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ)
      ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • t) ((List.finRange ℓ).map σ)) =
      Module.finrank k (rightRowStandard C hQ (Λ ∘ σ) (blockRow t n hn φ ∘ σ)).carrier := by
  set b := (braidColumnBottomBlockIndex n hn σ φ)⁻¹ • t
  have hb : b = Seq.redPerm σ (Seq.redPerm σ⁻¹ b) := by
    rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one]
  have hκ : redWord (Seq.redPerm σ⁻¹ b) = List.finRange ℓ := by
    rw [redWord_redPerm, redWord_braidColumnBottomBlockIndex_bottom _ _ _ _ _ hred,
      List.map_map]
    simp
  rw [hb, finrank_loadingStandard_redPerm σ hκ,
    eq_rowSeq_of_ofFn _ _ hν (ofFn_relabel_bottom hred σ)]
  exact finrank_rowSeq C hQ (Λ ∘ σ) _ hν

end Categorification.Stendhal.FirstWeight
