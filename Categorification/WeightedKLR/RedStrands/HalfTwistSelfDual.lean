/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistCorner
import Categorification.WeightedKLR.RedStrands.HalfTwistTransport
import Categorification.WeightedKLR.RedStrands.RedFirstSymmetricTrace
import Categorification.WeightedKLR.RedStrands.RedFirstReach
import Categorification.WeightedKLR.RedStrands.RedShuffleFactor

set_option backward.isDefEq.respectTransparency false

/-!
# Self-duality of `g(x) e⁰_{κ,b} · P⁰_{κ,b}`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. Let `κ = σ(1, …, ℓ)` and `b` a list of black labels. Under the corner isomorphism
`ψ : T^{λ∘σ} ≅ e_κ V e_κ` (`cornerEmbed`), the red-first idempotent `e⁰_{κ,b}` of `V` is the
idempotent `e(s)` of a red-first loading of `T^{λ∘σ}`, which lies under the red-first idempotent
`e⁰` of `T^{λ∘σ}` (`cornerEmbed_redFirstLoading`). At the Khovanov–Lauda scalars, the symmetric
trace of `e⁰ T^{λ∘σ} e⁰` (`redFirstIdem_symmetricPairing`) therefore restricts to `e(s)`, and the
flip of `V` is an anti-involution fixing `y' = g(x) e⁰_{κ,b}`. Hence the pairing
`⟨y' a, y' b⟩ = τ(e⁰ a ḃ y')` identifies `y' · P⁰_{κ,b} = y' e⁰_{κ,b} V e_κ` with its dual,
contravariantly for the right action of `e_κ V e_κ` through the flip (`dotCutSelfDualEquiv`,
`dotCutSelfDualEquiv_mul`).

## Main results

* `isRedFirst_redFirstSeq`, `redWord_redFirstSeq`: `e⁰_{κ,b}` is a red-first loading of order `κ`.
* `cornerEmbed_redFirstLoading`: `ψ (e(s)) = e⁰_{κ,b}` for `s = σ⁻¹ • (κ, b)`.
* `dotCutSelfDualEquiv`, `dotCutSelfDualEquiv_mul`: the self-duality of `y' · P⁰_{κ,b}`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv KL3.Diagram

section Loadings

variable {I : Type} {ℓ : ℕ}

/-- The loading of `e⁰_{κ,b}` is red-first. -/
theorem isRedFirst_redFirstSeq (s₀ : Seq (stendhalWeight ℓ (0 : Multiset I))) :
    ∀ b : List I, IsRedFirst (redFirstSeq s₀ b)
  | [] => isRedFirst_of_card_eq_zero Multiset.card_zero s₀
  | i :: b => (isRedFirst_appendBlackLoading_iff i (blackWeight b) _).2
      (isRedFirst_redFirstSeq s₀ b)

/-- The loading of `e⁰_{κ,b}` has red order `κ`. -/
theorem redWord_redFirstSeq (s₀ : Seq (stendhalWeight ℓ (0 : Multiset I))) :
    ∀ b : List I, redWord (redFirstSeq s₀ b) = redWord s₀
  | [] => rfl
  | i :: b => (redWord_appendBlackLoading i (blackWeight b) _).trans (redWord_redFirstSeq s₀ b)

theorem isRedFirst_redPerm {ν : Multiset I} (σ : Perm (Fin ℓ)) {s : Seq (stendhalWeight ℓ ν)}
    (hs : IsRedFirst s) : IsRedFirst (Seq.redPerm σ s) := by
  intro a b ha hb
  refine hs a b ?_ ?_
  · rw [Seq.redPerm_lbl] at ha
    cases h : s.lbl a <;> simp_all
  · rw [Seq.redPerm_lbl] at hb
    cases h : s.lbl b <;> simp_all

end Loadings

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (σ : Perm (Fin (ℓ + 1))) (b : List I)
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) (blackWeight b)))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  {s₀ : Seq (stendhalWeight (ℓ + 1) (0 : Multiset I))}
  (hs₀ : redWord s₀ = List.map σ (List.finRange (ℓ + 1)))

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "κ" => List.map σ (List.finRange (ℓ + 1))
local notation "ν" => blackWeight b
local notation "T" => TensorProductAlgebra k QL (Λ ∘ σ) (blackWeight b)
local notation "V" => ViolQuotient k QL Λ (blackWeight b)
local notation "P" => violMk k QL Λ (blackWeight b)
  (redProj k QL Λ (blackWeight b) (List.map σ (List.finRange (ℓ + 1))))
local notation "ψ" => cornerEmbed (Λ := Λ) hρ hQs σ
local notation "e⁰" => redFirstViol QL Λ (List.map σ (List.finRange (ℓ + 1))) b

/-- The red-ordered loading `s = σ⁻¹ • (κ, b)` of `T^{λ∘σ}`. -/
abbrev redFirstLoading : Seq (stendhalWeight (ℓ + 1) (blackWeight b)) :=
  Seq.redPerm σ⁻¹ (redFirstSeq s₀ b)

include hs₀ in
theorem isRedOrdered_redFirstLoading : IsRedOrdered (redFirstLoading σ b (s₀ := s₀)) := by
  rw [← redWord_eq_finRange_iff, redWord_redPerm, redWord_redFirstSeq, hs₀, List.map_map]
  simp

theorem isRedFirst_redFirstLoading : IsRedFirst (redFirstLoading σ b (s₀ := s₀)) :=
  isRedFirst_redPerm _ (isRedFirst_redFirstSeq s₀ b)

/-- The idempotent `e(s)` of `T^{λ∘σ}`. -/
abbrev redFirstLoadingIdem : T :=
  seqIdem QL (Λ ∘ σ) (redFirstLoading σ b (s₀ := s₀)) (isRedOrdered_redFirstLoading σ b hs₀)

/-- **`ψ (e(s)) = e⁰_{κ,b}`.** -/
theorem cornerEmbed_redFirstLoading :
    ψ (redFirstLoadingIdem Λ σ b hs₀) = e⁰ := by
  rw [cornerEmbed_seqIdem, Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one,
    redFirstViol_eq_violMk_e hs₀]

include hs₀ in
theorem redFirstViol_mul_self : e⁰ * e⁰ = e⁰ := by
  rw [redFirstViol_eq_violMk_e hs₀, ← map_mul, ← map_mul, KLRAlgebra.e_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

include hs₀ in
theorem redFirstViol_mul_redProj : e⁰ * P = e⁰ := by
  rw [redFirstViol_eq_violMk_e hs₀, ← map_mul, e_mul_redProj,
    ite_eq_left_of_eq_true _ _ (eq_true ((redWord_redFirstSeq s₀ b).trans hs₀))]

include hs₀ in
theorem redProj_mul_redFirstViol : P * e⁰ = e⁰ := by
  rw [redFirstViol_eq_violMk_e hs₀, ← map_mul, redProj_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_true ((redWord_redFirstSeq s₀ b).trans hs₀))]

variable (g : MvPolynomial (Fin (Multiset.card (stendhalWeight (ℓ + 1) (blackWeight b)))) k)

include hs₀ in
theorem dotIdem_eq_sandwich : e⁰ * dotIdem QL Λ κ b g * e⁰ = dotIdem QL Λ κ b g := by
  rw [redFirstViol_mul_dotIdem (redFirstViol_mul_self Λ σ b hs₀),
    dotIdem_mul_redFirstViol (redFirstViol_mul_self Λ σ b hs₀)]

include hs₀ in
theorem redProj_dotIdem_redProj : P * dotIdem QL Λ κ b g * P = dotIdem QL Λ κ b g := by
  rw [← dotIdem_eq_sandwich Λ σ b hs₀ g, ← mul_assoc, ← mul_assoc,
    redProj_mul_redFirstViol Λ σ b hs₀, mul_assoc, redFirstViol_mul_redProj Λ σ b hs₀]

/-- The element `y = ψ⁻¹ (g(x) e⁰_{κ,b})` of `T^{λ∘σ}`. -/
def dotIdemCorner : T :=
  (exists_cornerEmbed_eq hρ hQs σ (redProj_dotIdem_redProj Λ σ b hs₀ g)).choose

theorem cornerEmbed_dotIdemCorner :
    ψ (dotIdemCorner hQs Λ σ b hρ hs₀ g) = dotIdem QL Λ κ b g :=
  (exists_cornerEmbed_eq hρ hQs σ (redProj_dotIdem_redProj Λ σ b hs₀ g)).choose_spec

local notation "eT" => redFirstIdem QL (Λ ∘ σ) (blackWeight b)
local notation "fT" => redFirstLoadingIdem (k := k) (C := C) Λ σ b hs₀
local notation "yT" => dotIdemCorner hQs Λ σ b hρ hs₀ g
local notation "τ" => redFirstTrace hR hQs (Λ ∘ σ) (blackWeight b)

omit g in
theorem redFirstIdem_mul_redFirstLoadingIdem : eT * fT = fT := by
  rw [show fT = redLoadingIdem QL (Λ ∘ σ) _ _ (isRedOrdered_redFirstLoading σ b hs₀) from rfl,
    redFirstIdem_mul_redLoadingIdem_eq, ite_eq_left_of_eq_true _ _ (eq_true (isRedFirst_redFirstLoading σ b))]

omit g in
theorem redFirstLoadingIdem_mul_redFirstIdem : fT * eT = fT := by
  rw [show fT = redLoadingIdem QL (Λ ∘ σ) _ _ (isRedOrdered_redFirstLoading σ b hs₀) from rfl,
    redLoadingIdem_mul_redFirstIdem_eq, ite_eq_left_of_eq_true _ _ (eq_true (isRedFirst_redFirstLoading σ b))]

omit g in
theorem isIdempotentElem_redFirstLoadingIdem : IsIdempotentElem fT :=
  seqIdem_mul_self _ _ _ _

theorem dotIdemCorner_sandwich : fT * yT * fT = yT := by
  apply cornerEmbed_injective hρ hQs σ
  rw [cornerEmbed_mul, cornerEmbed_mul, cornerEmbed_redFirstLoading, cornerEmbed_dotIdemCorner,
    dotIdem_eq_sandwich Λ σ b hs₀ g]

theorem tensorCornerFlip_dotIdemCorner : tensorCornerFlip (Λ := Λ) hρ hQs σ yT = yT := by
  apply cornerEmbed_injective hρ hQs σ
  rw [cornerEmbed_tensorCornerFlip, cornerEmbed_dotIdemCorner, violFlip_dotIdem]

/-- The self-duality of `ψ (y T^{λ∘σ})` for `y = ψ⁻¹ (g(x) e⁰_{κ,b})`. -/
def dotCornerSelfDualEquiv :
    (CornerSelfDual.Left k yT).map ψ ≃ₗ[k] Module.Dual k ((CornerSelfDual.Left k yT).map ψ) :=
  haveI : Module.Finite k T := tensorProductAlgebra_finite (Λ ∘ σ) (blackWeight b) hR
  have hsp := (redFirstIdem_symmetricPairing hR hQs (Λ ∘ σ) (blackWeight b)).choose_spec
  CornerSelfDual.embedSelfDualEquiv fT yT τ
    (isIdempotentElem_redFirstLoadingIdem Λ σ b hs₀) (dotIdemCorner_sandwich hQs Λ σ b hρ hs₀ g)
    (CornerSelfDual.symm_of_le τ hsp.1 fT (redFirstIdem_mul_redFirstLoadingIdem Λ σ b hs₀)
      (redFirstLoadingIdem_mul_redFirstIdem Λ σ b hs₀))
    (CornerSelfDual.left_of_le τ hsp.1 hsp.2.1 fT (isIdempotentElem_redFirstLoadingIdem Λ σ b hs₀)
      (redFirstIdem_mul_redFirstLoadingIdem Λ σ b hs₀)
      (redFirstLoadingIdem_mul_redFirstIdem Λ σ b hs₀))
    (CornerSelfDual.right_of_le τ hsp.1 hsp.2.2 fT
      (isIdempotentElem_redFirstLoadingIdem Λ σ b hs₀)
      (redFirstIdem_mul_redFirstLoadingIdem Λ σ b hs₀)
      (redFirstLoadingIdem_mul_redFirstIdem Λ σ b hs₀))
    (tensorCornerFlip (Λ := Λ) hρ hQs σ) (tensorCornerFlip_mul hρ hQs σ) (tensorCornerFlip_tensorCornerFlip hρ hQs σ)
    (tensorCornerFlip_dotIdemCorner hQs Λ σ b hρ hs₀ g) ψ (cornerEmbed_injective hρ hQs σ)

theorem dotCornerSelfDualEquiv_mul (x x' : (CornerSelfDual.Left k yT).map ψ) (t : T) :
    dotCornerSelfDualEquiv hR hQs Λ σ b hρ hs₀ g
        ⟨x.1 * ψ t, CornerSelfDual.mul_mem_map_left _ _ (cornerEmbed_mul hρ hQs σ) x.2 t⟩ x' =
      dotCornerSelfDualEquiv hR hQs Λ σ b hρ hs₀ g x
        ⟨x'.1 * ψ (tensorCornerFlip (Λ := Λ) hρ hQs σ t),
          CornerSelfDual.mul_mem_map_left _ _ (cornerEmbed_mul hρ hQs σ) x'.2 _⟩ :=
  haveI : Module.Finite k T := tensorProductAlgebra_finite (Λ ∘ σ) (blackWeight b) hR
  CornerSelfDual.embedSelfDualEquiv_mul _ _ _ _ _ _ _ _ _ _ _ _ _ (cornerEmbed_mul hρ hQs σ) _
    x x' t

local notation "D" => dotCut QL Λ (List.map σ (List.finRange (ℓ + 1)))
  (List.map σ (List.finRange (ℓ + 1))) b g

omit hQs g in
theorem violRedProj_mul_self : P * P = P := by
  rw [← map_mul, (isIdempotentElem_redProj (k := k) (Q := QL) (Λ := Λ) κ :
    IsIdempotentElem (redProj k QL Λ (blackWeight b) κ)).eq]

/-- `ψ (y T^{λ∘σ}) = g(x) e⁰_{κ,b} · P⁰_{κ,b}`. -/
theorem map_left_dotIdemCorner : (CornerSelfDual.Left k yT).map ψ = D := by
  have hP := violRedProj_mul_self (k := k) (C := C) Λ σ b
  have he := redFirstViol_mul_self (k := k) (C := C) Λ σ b hs₀
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    have ha : ψ a * P = ψ a := by
      conv_lhs => rw [← cornerEmbed_mem hρ hQs σ a]
      rw [mul_assoc, hP, cornerEmbed_mem]
    refine ⟨e⁰ * ψ a * P, ?_, ?_⟩
    · change e⁰ * (e⁰ * ψ a * P) * P = e⁰ * ψ a * P
      simp only [mul_assoc, hP]
      rw [← mul_assoc e⁰ e⁰, he]
    · change dotIdem QL Λ κ b g * (e⁰ * ψ a * P) = ψ (yT * a)
      rw [cornerEmbed_mul, cornerEmbed_dotIdemCorner, mul_assoc, ha, ← mul_assoc,
        dotIdem_mul_redFirstViol he]
  · rintro ⟨c, hc, rfl⟩
    have hc : e⁰ * c * P = c := hc
    have hPc : P * c * P = c := by
      rw [← hc, ← mul_assoc, ← mul_assoc, redProj_mul_redFirstViol Λ σ b hs₀, mul_assoc, hP]
    obtain ⟨t, rfl⟩ := exists_cornerEmbed_eq hρ hQs σ hPc
    exact ⟨yT * t, ⟨t, rfl⟩, by
      change ψ (yT * t) = dotIdem QL Λ κ b g * ψ t
      rw [cornerEmbed_mul, cornerEmbed_dotIdemCorner]⟩

include hQs hρ hs₀ in
theorem mul_mem_dotCut {x c : V} (hx : x ∈ D) (hc : P * c * P = c) : x * c ∈ D := by
  rw [← map_left_dotIdemCorner hQs Λ σ b hρ hs₀ g] at hx ⊢
  obtain ⟨t, rfl⟩ := exists_cornerEmbed_eq hρ hQs σ hc
  exact CornerSelfDual.mul_mem_map_left _ _ (cornerEmbed_mul hρ hQs σ) hx t

omit hQs g in
theorem redProj_violFlip_redProj {c : V} (hc : P * c * P = c) :
    P * violFlip c * P = violFlip c := by
  have hP : violFlip P = P := by rw [violFlip_violMk, flip_redProj]
  conv_rhs => rw [← hc]
  rw [violFlip_mul_eq, violFlip_mul_eq, hP, mul_assoc]

/-- **The self-duality of `g(x) e⁰_{κ,b} · P⁰_{κ,b}`** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.14), at the Khovanov–Lauda scalars: with `y' = g(x) e⁰_{κ,b}` and `ψ` the corner
isomorphism, `⟨y' ψ(a), y' ψ(b)⟩ = τ(e⁰ a ḃ y)` identifies `y' · P⁰_{κ,b}` with its dual. -/
def dotCutSelfDualEquiv : D ≃ₗ[k] Module.Dual k D :=
  (LinearEquiv.ofEq _ _ (map_left_dotIdemCorner hQs Λ σ b hρ hs₀ g).symm).trans
    ((dotCornerSelfDualEquiv hR hQs Λ σ b hρ hs₀ g).trans
      (LinearEquiv.ofEq _ _ (map_left_dotIdemCorner hQs Λ σ b hρ hs₀ g).symm).dualMap)

/-- The form of `dotCutSelfDualEquiv` is contravariant for the right action of `e_κ V e_κ`,
through the flip: `⟨x c, x'⟩ = ⟨x, x' ċ⟩`. -/
theorem dotCutSelfDualEquiv_mul (x x' : D) {c : V} (hc : P * c * P = c) :
    dotCutSelfDualEquiv hR hQs Λ σ b hρ hs₀ g
        ⟨x.1 * c, mul_mem_dotCut hQs Λ σ b hρ hs₀ g x.2 hc⟩ x' =
      dotCutSelfDualEquiv hR hQs Λ σ b hρ hs₀ g x
        ⟨x'.1 * violFlip c, mul_mem_dotCut hQs Λ σ b hρ hs₀ g x'.2
          (redProj_violFlip_redProj Λ σ b hc)⟩ := by
  obtain ⟨t, rfl⟩ := exists_cornerEmbed_eq hρ hQs σ hc
  have h := map_left_dotIdemCorner hQs Λ σ b hρ hs₀ g
  have key := dotCornerSelfDualEquiv_mul hR hQs Λ σ b hρ hs₀ g
    (LinearEquiv.ofEq _ _ h.symm x) (LinearEquiv.ofEq _ _ h.symm x') t
  simp only [dotCutSelfDualEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  have e1 : ∀ hm, LinearEquiv.ofEq _ _ h.symm ⟨x.1 * ψ t, hm⟩ =
      ⟨(LinearEquiv.ofEq _ _ h.symm x).1 * ψ t, CornerSelfDual.mul_mem_map_left _ _
        (cornerEmbed_mul hρ hQs σ) (LinearEquiv.ofEq _ _ h.symm x).2 t⟩ := fun _ => rfl
  have e2 : ∀ hm, LinearEquiv.ofEq _ _ h.symm ⟨x'.1 * violFlip (ψ t), hm⟩ =
      ⟨(LinearEquiv.ofEq _ _ h.symm x').1 * ψ (tensorCornerFlip (Λ := Λ) hρ hQs σ t),
        CornerSelfDual.mul_mem_map_left _ _ (cornerEmbed_mul hρ hQs σ)
          (LinearEquiv.ofEq _ _ h.symm x').2 _⟩ := fun _ =>
    Subtype.ext (show x'.1 * violFlip (ψ t) = x'.1 * ψ (tensorCornerFlip (Λ := Λ) hρ hQs σ t) by
      rw [cornerEmbed_tensorCornerFlip])
  rw [e1, e2]
  exact key

theorem isContravariant_dotCutSelfDualEquiv :
    CornerSelfDual.IsContravariant (fun c : V => P * c * P = c) violFlip
      (dotCutSelfDualEquiv hR hQs Λ σ b hρ hs₀ g).toLinearMap :=
  fun x x' _ hc _ _ => dotCutSelfDualEquiv_mul hR hQs Λ σ b hρ hs₀ g x x' hc

end Categorification.Stendhal.BraidedStendhalAlgebra
