/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistDuality
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

set_option backward.isDefEq.respectTransparency false

/-!
# Red-first loadings as loadings `e⁰_{κ,b}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. A red-first, red-ordered loading of black weight `ν` is, up to the identification
`ν = b₁ + ⋯ + b_n`, the loading `e⁰_{κ,b}` of its red strands followed by its black strands `b`
(`exists_redFirstSeq_eq`). Consequently the self-duality of `𝔅_τ P^κ` holds for every black
weight `ν` (`exists_halfTwistSelfDual`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv

section Loadings

variable {I : Type} {ℓ : ℕ}

/-- The last strand of a red-first loading with a black strand is black. -/
theorem exists_terminal_black {ν : Multiset I} (hν : ν ≠ 0) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedFirst s) :
    ∃ i ∈ ν, s.lbl (FirstWeight.terminalPos (ν := ν) (ℓ := ℓ)
      (by have := Multiset.card_pos.2 hν; omega)) = .inl i := by
  have hpos : 0 < ℓ + ν.card := by have := Multiset.card_pos.2 hν; omega
  have hmem : ∀ x, (x ∈ stendhalWeight ℓ ν) ↔ ∃ a, s.lbl a = x := fun x =>
    ⟨fun hx => by
      have h : x ∈ Finset.univ.val.map s.1 := s.2.symm ▸ hx
      obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h
      exact ⟨a, ha⟩,
    fun ⟨a, ha⟩ => ha ▸ s.mem a⟩
  obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hν
  obtain ⟨a, ha⟩ := (hmem (.inl i)).1 (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, hi, rfl⟩)))
  set p := FirstWeight.terminalPos (ν := ν) (ℓ := ℓ) hpos
  cases hp : s.lbl p with
  | inl j =>
    refine ⟨j, ?_, rfl⟩
    have : (Sum.inl j : I ⊕ Fin ℓ) ∈ stendhalWeight ℓ ν := (hmem _).2 ⟨p, hp⟩
    simp only [stendhalWeight, Multiset.mem_add, Multiset.mem_map] at this
    rcases this with ⟨j', hj', h⟩ | ⟨r, _, h⟩
    · cases h; exact hj'
    · cases h
  | inr r =>
    exfalso
    have hlt := hs a p (by rw [ha]; rfl) (by rw [hp]; rfl)
    have : a.val ≤ p.val := by
      change a.val ≤ Multiset.card (stendhalWeight ℓ ν) - 1
      have := a.isLt; omega
    exact absurd hlt (not_lt.2 this)

/-- **Every red-first, red-ordered loading is `e⁰_{κ,b}`**, up to `ν = b₁ + ⋯ + b_n`. -/
theorem exists_redFirstSeq_eq : ∀ (n : ℕ) {ν : Multiset I}, Multiset.card ν = n →
    ∀ (s : Seq (stendhalWeight ℓ ν)), IsRedFirst s → IsRedOrdered s →
    ∃ (b : List I) (h : blackWeight b = ν) (s₁ : Seq (stendhalWeight ℓ (0 : Multiset I))),
      redWord s₁ = redWord s ∧ Seq.cast (congrArg (stendhalWeight ℓ) h) (redFirstSeq s₁ b) = s
  | 0, ν, hn, s, _, _ => by
    obtain rfl := Multiset.card_eq_zero.1 hn
    exact ⟨[], rfl, s, rfl, rfl⟩
  | n + 1, ν, hn, s, hf, ho => by
    have hν : ν ≠ 0 := fun h => by simp [h] at hn
    obtain ⟨i, hi, hlast⟩ := exists_terminal_black hν s hf
    obtain ⟨β, rfl⟩ : ∃ β, ν = {i} + β := by
      obtain ⟨β, hβ⟩ := Multiset.exists_cons_of_mem hi
      exact ⟨β, hβ.trans (Multiset.singleton_add i β).symm⟩
    obtain ⟨u, hu, rfl⟩ := FirstWeight.exists_appendBlack_terminal s hlast ho
    have hfu : IsRedFirst u := (isRedFirst_appendBlackLoading_iff i β u).1 hf
    have hcard : Multiset.card β = n := by simp at hn; omega
    obtain ⟨b, hb, s₁, hs₁, hcast⟩ := exists_redFirstSeq_eq n hcard u hfu hu
    subst hb
    refine ⟨i :: b, rfl, s₁, ?_, ?_⟩
    · rw [hs₁, redWord_appendBlackLoading]
    · change appendBlackLoading i (blackWeight b) (redFirstSeq s₁ b) = _
      rw [show redFirstSeq s₁ b = u from hcast]

end Loadings

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (w : Perm (Fin (ℓ + 1)))
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (hbase : BaseCrossing (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ),
    AllFiniteDeltaInjective (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ' hQ.klrSymm)
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

include hQ hR hbase hall H hwt hw in
/-- **`𝔅_τ P^κ ≅ (𝔅_τ P^κ)⋆` for every black weight** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14), at the Khovanov–Lauda scalars: for a red-ordered loading `t` of black weight `ν`
and a red order `κ = w(1, …, ℓ)` reversing every pair of red strands, `e(t) V e_κ` carries a
nondegenerate form that is contravariant for the right action of `e_κ V e_κ` through the flip.
Route hypotheses: those of `FirstWeight.halfTwistInclusionEquiv` (Corollary 6.10 and
`BaseCrossing`). -/
theorem exists_halfTwistSelfDual
    (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) ν),
      redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
    (t : Seq (stendhalWeight (ℓ + 1) ν)) (ht : IsRedOrdered t) :
    ∃ Φ : violCorner k QL Λ ν t (List.map w (List.finRange (ℓ + 1))) ≃ₗ[k]
        Module.Dual k (violCorner k QL Λ ν t (List.map w (List.finRange (ℓ + 1)))),
      CornerSelfDual.IsContravariant
        (fun c : ViolQuotient k QL Λ ν =>
          violMk k QL Λ ν (redProj k QL Λ ν (List.map w (List.finRange (ℓ + 1)))) * c *
            violMk k QL Λ ν (redProj k QL Λ ν (List.map w (List.finRange (ℓ + 1)))) = c)
        violFlip Φ.toLinearMap := by
  obtain ⟨b, hb, s₁, hs₁, hcast⟩ := exists_redFirstSeq_eq (Multiset.card ν) rfl
    (redShufflePerm t • t) (isRedFirst_redShuffle t) (isRedOrdered_redShuffle ht)
  subst hb
  rw [Seq.cast_rfl] at hcast
  have hs₁' : redWord s₁ = List.finRange (ℓ + 1) := by
    rw [hs₁]; exact (redWord_eq_finRange_iff _).2 (isRedOrdered_redShuffle ht)
  exact ⟨halfTwistSelfDualEquiv C hQ Λ b w hs₁' hcast.symm hR hbase hall H wt hwt hw hκ ht,
    isContravariant_halfTwistSelfDualEquiv C hQ Λ b w hs₁' hcast.symm hR hbase hall H wt hwt hw hκ ht⟩

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
