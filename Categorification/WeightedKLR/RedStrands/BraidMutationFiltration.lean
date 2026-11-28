/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnCutFiltration
import Categorification.WeightedKLR.RedStrands.BraidBlockTransport
import Categorification.WeightedKLR.RedStrands.BraidColumnStayIndex

set_option backward.isDefEq.respectTransparency false

/-!
# The labelled standard filtration of a braided projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 6.20 (mutation of the standard stratification). For a red-ordered loading `t`, the
cut `e(t) V e_{wλ}` (the braid `𝔅_w(e(t) T^λ)`) has a filtration by the loading standards of red
order `w`, labelled by the bottoms `W⁻¹ t` of the eligible indices of the braid column
(`exists_hasFiltration_violCorner_braidColumn`, under the class-map hypotheses of Lemma 6.11).

Each label is the block transport `blockTransport w b` of a constituent `b = φ⁻¹ t ≥ t` of the
projective `e(t) T^λ`, and exactly one index, the transport of `t` itself, has a label whose
constituent is not strictly above `t` (`exists_braidColumnIndex_labels`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv BraidColumn

section Labels

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

omit [DecidableEq I] in
/-- A loading that is the row of its red-led blocks is not violated. -/
theorem not_isViolated_of_braidBlockPositions {s : Seq μ} (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m)
    (h : ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) : ¬ IsViolated s := by
  rintro ⟨h0, hl⟩
  by_cases hℓ : 0 < ℓ
  · have hp : braidBlockPositions n hn ⟨⟨0, hℓ⟩, 0⟩ = ⟨0, h0⟩ := by
      apply Fin.ext
      simp only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finSigmaFinEquiv_apply, Fin.val_zero, add_zero]
      exact Finset.sum_eq_zero fun j _ => j.elim0
    have := h ⟨0, hℓ⟩
    rw [hp] at this
    rw [this] at hl
    exact Bool.false_ne_true hl
  · have hℓ0 : ℓ = 0 := Nat.eq_zero_of_not_pos hℓ
    subst hℓ0
    simp at hn
    omega

/-- **The labels of a braided projective** (Webster, arXiv:1309.3796v3, proof of
Proposition 6.20): for a nonviolated red-ordered loading `t`, every eligible index `W` of the
braid column has bottom `W⁻¹ t = blockTransport w b` for a nonviolated red-ordered `b ≥ t`; the
index `W₀` of the identity wiring has bottom `blockTransport w t`, and every other index has
`b` strictly above `t`. -/
theorem exists_braidColumnIndex_labels (w : Perm (Fin ℓ)) {t : Seq μ} (ht : IsRedOrdered t)
    (hv : ¬ IsViolated t) :
    ∃ W₀ ∈ braidColumnIndexList t w, W₀⁻¹ • t = blockTransport w t ∧
      ∀ W ∈ braidColumnIndexList t w, ∃ b : Seq μ, IsRedOrdered b ∧ ¬ IsViolated b ∧
        StendhalLE t b ∧ W⁻¹ • t = blockTransport w b ∧ (W ≠ W₀ → ¬ StendhalLE b t) := by
  obtain ⟨n₀, hn₀, h₀⟩ := exists_braidBlockPositions t ht hv
  have h₀' : ∀ r : Fin ℓ, ((1 : Perm (Fin m))⁻¹ • t).lbl (braidBlockPositions n₀ hn₀ ⟨r, 0⟩) =
      .inr r := by
    simpa only [inv_one, one_smul] using h₀
  refine ⟨braidColumnBottomBlockIndex n₀ hn₀ w 1,
    mem_braidColumnIndexList.2 ⟨n₀, hn₀, 1, projectiveBlockIndex_one ht, h₀', rfl⟩, ?_, ?_⟩
  · rw [braidColumnBottomBlockIndex_bottom, inv_one, one_smul, blockTransport_eq w n₀ hn₀ h₀]
  · intro W hW
    obtain ⟨n, hn, φ, hφ, hred, rfl⟩ := mem_braidColumnIndexList.1 hW
    refine ⟨φ⁻¹ • t, hφ.bottom_ordered, not_isViolated_of_braidBlockPositions n hn hred,
      stendhalLE_inv_smul hφ, ?_, fun hne hle => hne ?_⟩
    · rw [braidColumnBottomBlockIndex_bottom, blockTransport_eq w n hn hred]
    · obtain rfl := eq_one_of_stendhalLE_inv_smul ht hφ hle
      have hred' : ∀ r : Fin ℓ, t.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r := by
        simpa only [inv_one, one_smul] using hred
      obtain rfl := eq_of_braidBlockPositions hred' h₀
      rfl

end Labels

namespace BraidedStendhalAlgebra

open MulOpposite ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (σ : Perm (Fin ℓ))

local notation "μ" => stendhalWeight ℓ ν
local notation "C'" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- **Relabelling a labelled standard filtration** along a relabelling equivalence: the labels
`s` become `σ s`. -/
theorem exists_hasFiltration_of_cornerRelabel_labels {κ : List (Fin ℓ)}
    {X : ModuleCat.{0} (C' κ)ᵐᵒᵖ} {Y : ModuleCat.{0} (C (κ.map σ))ᵐᵒᵖ}
    (e : (ModuleCat.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
        (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).obj X ≃ₗ[(C (κ.map σ))ᵐᵒᵖ] Y)
    (l : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s})
    (hl : HasFiltration (fun s => ModuleCat.of (C' κ)ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s.1 κ)) l X) :
    ∃ l' : List {s : Seq μ // redWord s = κ.map σ ∧ ¬ IsViolated s},
      l'.map Subtype.val = l.map (fun s => Seq.redPerm σ s.1) ∧
      HasFiltration (fun s => ModuleCat.of (C (κ.map σ))ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.1 (κ.map σ))) l' Y := by
  let g : {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s} →
      {s : Seq μ // redWord s = κ.map σ ∧ ¬ IsViolated s} := fun s =>
    ⟨Seq.redPerm σ s.1, by rw [redWord_redPerm, s.2.1], by
      rw [isViolated_redPerm]; exact s.2.2⟩
  have h1 := (hl.restrictScalars (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ :
    (C (κ.map σ))ᵐᵒᵖ →+* (C' κ)ᵐᵒᵖ)).of_equiv e
  have hlab : ∀ l : List {s : Seq μ // redWord s = κ ∧ ¬ IsViolated s},
      (l.flatMap fun s => [g s]).map Subtype.val = l.map (fun s => Seq.redPerm σ s.1) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.flatMap_cons, List.map_append, ih]; rfl
  refine ⟨l.flatMap fun s => [g s], hlab l, h1.bind fun s => HasFiltration.single ?_⟩
  exact loadingStandardRelabelEquiv σ s.2.1

end BraidedStendhalAlgebra

namespace FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF ModuleFiltration
open BraidedStendhalAlgebra BraidColumn Equiv
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "𝕂" => RatFunc ℚ

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **The labelled standard filtration of a braided projective** (Webster, arXiv:1309.3796v3,
proof of Proposition 6.20, from Lemma 6.11): under the class-map hypotheses of Lemma 6.11, the
cut `e(t) V e_{wλ}` has a filtration by the loading standards of red order `w`, with labels the
bottoms `W⁻¹ t` of the eligible indices of the braid column, in reverse order. -/
theorem exists_hasFiltration_violCorner_braidColumn (w : Equiv.Perm (Fin ℓ))
    (f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ w))
    (hf : VOneCongr f (tensorPermute wt w).toLinearMap)
    (hcls : braidClass C hQ hR Λ wt hwt w = (formDual hR (wt ∘ w)).comp f)
    {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    ∃ l : List {s : Seq (stendhalWeight ℓ ν) //
        redWord s = (List.finRange ℓ).map w ∧ ¬ IsViolated s},
      l.map Subtype.val = (braidColumnIndexList t w).reverse.map (fun W => W⁻¹ • t) ∧
      HasFiltration (fun s => ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ)
          (ν := ν) ((List.finRange ℓ).map w))ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q)
            (Λ := Λ) s.1 ((List.finRange ℓ).map w))) l
        (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
          ((List.finRange ℓ).map w))ᵐᵒᵖ (violCorner k Q Λ ν t ((List.finRange ℓ).map w))) := by
  obtain ⟨l, hl1, hl2⟩ := exists_hasFiltration_braidRightSequenceCut C hQ hR Λ wt hwt w f hf hcls
    t ht
  obtain ⟨l', h1, h2⟩ := exists_hasFiltration_of_cornerRelabel_labels w
    (braidRightSequenceCutEquiv (isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht) l hl2
  refine ⟨l', ?_, h2⟩
  rw [h1, show (fun s : {s : Seq (stendhalWeight ℓ ν) // redWord s = List.finRange ℓ ∧
      ¬ IsViolated s} => Seq.redPerm w s.1) = Seq.redPerm w ∘ Subtype.val from rfl,
    ← List.map_map, hl1, List.map_map]
  refine List.map_congr_left fun W _ => ?_
  simp only [Function.comp_apply]
  rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one]

end FirstWeight

end Categorification.Stendhal
