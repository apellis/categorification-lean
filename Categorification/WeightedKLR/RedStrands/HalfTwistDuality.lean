/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistSelfDual
import Categorification.WeightedKLR.RedStrands.HalfTwistInjective
import Categorification.WeightedKLR.RedStrands.HalfTwistDots
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossing

set_option backward.isDefEq.respectTransparency false

/-!
# The self-duality of `𝔅_τ P^κ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. Let `t` be a red-ordered loading whose black strands, read from the left, are
`b`, so that its red-first loading `t⁰ = τ_t • t` is `e⁰_{(1, …, ℓ),b}`, and let `κ = w(1, …, ℓ)`
reverse every pair of red strands. The chain

* `ι : e(t) V e_κ ≅ y · e(t⁰) V e_κ` (`FirstWeight.halfTwistInclusionEquiv`),
* `y = g(x) e⁰_{(1, …, ℓ),b}` (`exists_halfTwistY_eq_pol`), so that
  `y · e(t⁰) V e_κ = g(x) e⁰_{(1, …, ℓ),b} · P⁰_{(1, …, ℓ),b}` (`map_halfTwistY_eq_dotCut`),
* the red braid of Corollary 6.8, `g(x) e⁰_{κ,b} · P⁰_{κ,b} ≅ g(x) e⁰_{(1, …, ℓ),b} · P⁰_{(1, …, ℓ),b}`
  (`dotTransport`),
* the self-duality of `g(x) e⁰_{κ,b} · P⁰_{κ,b}` at the Khovanov–Lauda scalars
  (`dotCutSelfDualEquiv`),

identifies `𝔅_τ P^κ = e(t) V e_κ` with its dual (`halfTwistSelfDualEquiv`). Every map in the
chain is a left multiplication, so the form is contravariant for the right action of
`e_κ V e_κ` through the flip (`isContravariant_halfTwistSelfDualEquiv`): `𝔅_τ P^κ ≅ (𝔅_τ P^κ)⋆`.

## Main results

* `violCorner_redFirstSeq`: `e(t⁰) V e_κ = P⁰_{κ',b}` for `t⁰ = e⁰_{κ',b}`.
* `map_halfTwistY_eq_dotCut`: `y · e(t⁰) V e_κ = g(x) e⁰_{κ',b} · P⁰_{κ',b}`.
* `halfTwistSelfDualEquiv`, `isContravariant_halfTwistSelfDualEquiv`: `𝔅_τ P^κ ≅ (𝔅_τ P^κ)⋆`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv KLRAlgebra

section General

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

/-- The cut of `V` at the loading of `e⁰_{κ',b}` is `P⁰_{κ',b}`. -/
theorem violCorner_redFirstSeq {κ' : List (Fin ℓ)} {s₁ : Seq (stendhalWeight ℓ (0 : Multiset I))}
    (hs₁ : redWord s₁ = κ') (b : List I) (κ : List (Fin ℓ)) :
    violCorner k Q Λ (blackWeight b) (redFirstSeq s₁ b) κ = redFirstCut Q Λ κ' κ b := by
  have he : redFirstViol Q Λ κ' b * redFirstViol Q Λ κ' b = redFirstViol Q Λ κ' b := by
    rw [redFirstViol_eq_violMk_e hs₁, ← map_mul, ← map_mul, KLRAlgebra.e_mul_e,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have hP : violMk k Q Λ (blackWeight b) (redProj k Q Λ (blackWeight b) κ) *
      violMk k Q Λ (blackWeight b) (redProj k Q Λ (blackWeight b) κ) =
        violMk k Q Λ (blackWeight b) (redProj k Q Λ (blackWeight b) κ) := by
    rw [← map_mul, (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) κ :
      IsIdempotentElem (redProj k Q Λ (blackWeight b) κ)).eq]
  ext x
  rw [mem_violCorner_iff, ← redFirstViol_eq_violMk_e hs₁]
  change _ ↔ redFirstViol Q Λ κ' b * x * _ = x
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h, ← mul_assoc, ← mul_assoc, he]
    · rw [← h, mul_assoc, hP]

/-- **`y · e(t⁰) V e_κ = g(x) e⁰_{κ',b} · P⁰_{κ',b}`** when `t⁰ = e⁰_{κ',b}` and
`y = g(x) e(t⁰)`. -/
theorem map_halfTwistY_eq_dotCut {κ' : List (Fin ℓ)}
    {s₁ : Seq (stendhalWeight ℓ (0 : Multiset I))} (hs₁ : redWord s₁ = κ') {b : List I}
    {t : Seq (stendhalWeight ℓ (blackWeight b))} (ht₀ : redShufflePerm t • t = redFirstSeq s₁ b)
    (κ : List (Fin ℓ)) {f : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k}
    (hf : halfTwistY (k := k) (Q := Q) (Λ := Λ) t = violMk k Q Λ (blackWeight b)
      (ofKLR k Q Λ (blackWeight b) (pol f * KLRAlgebra.e (redShufflePerm t • t)))) :
    (violCorner k Q Λ (blackWeight b) (redShufflePerm t • t) κ).map
        (LinearMap.mulLeft k (halfTwistY (k := k) (Q := Q) (Λ := Λ) t)) =
      dotCut Q Λ κ' κ b f := by
  have hy : halfTwistY (k := k) (Q := Q) (Λ := Λ) t = dotIdem Q Λ κ' b f := by
    rw [hf, ht₀, dotIdem, redFirstViol_eq_violMk_e hs₁, map_mul, map_mul]
  rw [hy, ht₀, violCorner_redFirstSeq hs₁]
  rfl

end General

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : List I) (w : Perm (Fin (ℓ + 1)))
  {t : Seq (stendhalWeight (ℓ + 1) (blackWeight b))}
  {s₁ : Seq (stendhalWeight (ℓ + 1) (0 : Multiset I))}
  (hs₁ : redWord s₁ = List.finRange (ℓ + 1)) (ht₀ : redShufflePerm t • t = redFirstSeq s₁ b)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "κ" => List.map w (List.finRange (ℓ + 1))
local notation "M" => violCorner k QL Λ (blackWeight b) t (List.map w (List.finRange (ℓ + 1)))

/-- The polynomial `g` with `y = g(x) e(t⁰)`. -/
def halfTwistPol : MvPolynomial (Fin (Multiset.card (stendhalWeight (ℓ + 1) (blackWeight b)))) k :=
  (exists_halfTwistY_eq_pol (k := k) (Q := QL) (Λ := Λ) t).choose

theorem halfTwistY_eq_halfTwistPol :
    halfTwistY (k := k) (Q := QL) (Λ := Λ) t = violMk k QL Λ (blackWeight b)
      (ofKLR k QL Λ (blackWeight b) (pol (halfTwistPol C Λ b (t := t)) *
        KLRAlgebra.e (redShufflePerm t • t))) :=
  (exists_halfTwistY_eq_pol (k := k) (Q := QL) (Λ := Λ) t).choose_spec

include hs₁ in
theorem redWord_redPerm_redFirst : redWord (Seq.redPerm w s₁) = κ := by
  rw [redWord_redPerm, hs₁]

/-- A nonzero red braid `r₀ ∈ e_{(1, …, ℓ)} V(0) e_κ`. -/
def halfTwistRedBraid : ViolQuotient k QL Λ 0 :=
  (exists_ne_zero_of_nil (k := k) (Q := QL) (Λ := Λ) hQ.klrSymm s₁ (Seq.redPerm w s₁)).choose

theorem halfTwistRedBraid_ne_zero : halfTwistRedBraid C hQ Λ w (s₁ := s₁) ≠ 0 :=
  (exists_ne_zero_of_nil (k := k) (Q := QL) (Λ := Λ) hQ.klrSymm s₁ (Seq.redPerm w s₁)).choose_spec.1

include hs₁ in
theorem halfTwistRedBraid_mem :
    violMk k QL Λ 0 (redProj k QL Λ 0 (List.finRange (ℓ + 1))) *
        halfTwistRedBraid C hQ Λ w (s₁ := s₁) * violMk k QL Λ 0 (redProj k QL Λ 0 κ) =
      halfTwistRedBraid C hQ Λ w (s₁ := s₁) := by
  have h : violMk k QL Λ 0 (redProj k QL Λ 0 (redWord s₁)) *
      halfTwistRedBraid C hQ Λ w (s₁ := s₁) *
        violMk k QL Λ 0 (redProj k QL Λ 0 (redWord (Seq.redPerm w s₁))) =
      halfTwistRedBraid C hQ Λ w (s₁ := s₁) :=
    (exists_ne_zero_of_nil (k := k) (Q := QL) (Λ := Λ) hQ.klrSymm s₁
      (Seq.redPerm w s₁)).choose_spec.2
  rwa [hs₁, redWord_redPerm_redFirst w hs₁] at h

variable {Y : Type*} [AddCommGroup Y] [Finite I]
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
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)
  (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w ≠ 1)
  (hκ : ∀ t' : Seq (stendhalWeight (ℓ + 1) (blackWeight b)),
    redWord t' = (List.finRange (ℓ + 1)).map w → IsRedReversed t')
  (ht : IsRedOrdered t)

/-- The chain `𝔅_τ P^κ = e(t) V e_κ ≅ y · e(t⁰) V e_κ = g(x) e⁰_{(1,…,ℓ),b} · P⁰_{(1,…,ℓ),b}
≅ g(x) e⁰_{κ,b} · P⁰_{κ,b}` of left multiplications. -/
def halfTwistCutEquiv : M ≃ₗ[k] dotCut QL Λ κ κ b (halfTwistPol C Λ b (t := t)) :=
  (FirstWeight.halfTwistInclusionEquiv C hQ hR (baseCrossing_of_rouquier hQ hQ.klrSymm)
      H Λ wt hwt (blackWeight b) w hw hκ
      t ht).trans
    ((LinearEquiv.ofEq _ _ (map_halfTwistY_eq_dotCut hs₁ ht₀ κ
      (halfTwistY_eq_halfTwistPol C Λ b))).trans
      (dotTransport hQ.klrSymm (FirstWeight.canChoice (ℓ + 1)) (fun ν => FirstWeight.isReducedChoice_canChoice ν)
        (halfTwistRedBraid_mem C hQ Λ w hs₁) (halfTwistRedBraid_ne_zero C hQ Λ w) b _).symm)

local notation "S" => fun c : ViolQuotient k QL Λ (blackWeight b) =>
  violMk k QL Λ (blackWeight b) (redProj k QL Λ (blackWeight b) κ) * c *
    violMk k QL Λ (blackWeight b) (redProj k QL Λ (blackWeight b) κ) = c

include hs₁ in
theorem commutesRight_halfTwistCutEquiv :
    CornerSelfDual.CommutesRight S
      (halfTwistCutEquiv C hQ Λ b w hs₁ ht₀ hR H wt hwt hw hκ ht) := by
  refine CornerSelfDual.CommutesRight.trans (fun m c _ h => ?_)
    (CornerSelfDual.CommutesRight.trans (CornerSelfDual.commutesRight_ofEq _)
      (CornerSelfDual.CommutesRight.symm (fun z c _ h => ?_) ?_))
  · change violShuffleDual (k := k) (Q := QL) (Λ := Λ) t * (m.1 * c) =
      violShuffleDual (k := k) (Q := QL) (Λ := Λ) t * m.1 * c
    rw [mul_assoc]
  · change redBraid (halfTwistRedBraid C hQ Λ w (s₁ := s₁)) b * (z.1 * c) =
      redBraid (halfTwistRedBraid C hQ Λ w (s₁ := s₁)) b * z.1 * c
    rw [mul_assoc]
  · intro x hx c hc
    exact mul_mem_dotCut hQ.klrSymm Λ w b (FirstWeight.isReducedChoice_canChoice (blackWeight b))
      (redWord_redPerm_redFirst w hs₁) _ hx hc

/-- **`𝔅_τ P^κ ≅ (𝔅_τ P^κ)⋆`** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14), at the
Khovanov–Lauda scalars: for a red-ordered loading `t` with black strands `b` and a red order
`κ = w(1, …, ℓ)` reversing every pair of red strands, the form pulled back along
`e(t) V e_κ ≅ g(x) e⁰_{κ,b} · P⁰_{κ,b}` identifies `e(t) V e_κ` with its dual. Route
hypothesis: the injectivity of Lemma 6.8 (`RowFigureFiveHypotheses`);
`AllFiniteDeltaInjective` and `BaseCrossing` are proved at these scalars. -/
def halfTwistSelfDualEquiv : M ≃ₗ[k] Module.Dual k M :=
  (halfTwistCutEquiv C hQ Λ b w hs₁ ht₀ hR H wt hwt hw hκ ht).trans
    ((dotCutSelfDualEquiv hQ hQ.klrSymm Λ w b
      (FirstWeight.isReducedChoice_canChoice (blackWeight b))
      (redWord_redPerm_redFirst w hs₁) _).trans
      (halfTwistCutEquiv C hQ Λ b w hs₁ ht₀ hR H wt hwt hw hκ ht).dualMap)

/-- The form of `halfTwistSelfDualEquiv` is contravariant for the right action of
`e_κ V e_κ` through the flip: `⟨m c, m'⟩ = ⟨m, m' ċ⟩`. -/
theorem isContravariant_halfTwistSelfDualEquiv :
    CornerSelfDual.IsContravariant S violFlip
      (halfTwistSelfDualEquiv C hQ Λ b w hs₁ ht₀ hR H wt hwt hw hκ ht).toLinearMap :=
  (isContravariant_dotCutSelfDualEquiv hQ hQ.klrSymm Λ w b
      (FirstWeight.isReducedChoice_canChoice (blackWeight b))
      (redWord_redPerm_redFirst w hs₁) _).transport
    (commutesRight_halfTwistCutEquiv C hQ Λ b w hs₁ ht₀ hR H wt hwt hw hκ ht)
    (fun _ hc => redProj_violFlip_redProj Λ w b hc)

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
