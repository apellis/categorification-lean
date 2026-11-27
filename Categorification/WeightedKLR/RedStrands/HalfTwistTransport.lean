/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedBraidDots

set_option backward.isDefEq.respectTransparency false

/-!
# Transporting the element `y` of the half twist along Corollary 6.8

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. The element `y = θ̇_t θ_t` is a polynomial `g(x)` in the dots times the red-first
idempotent `e⁰_{κ',b}` (`exists_halfTwistY_eq_pol`). Dots commute with the red braid `r_b` of
Corollary 6.8 (`commute_redBraid_pol`), so `y r_b = r_b y'` for `y' = g(x) e⁰_{κ,b}`, and
left multiplication by `r_b` identifies `y' · e⁰_{κ,b} V e_κ` with `y · e⁰_{κ',b} V e_κ`
(`dotTransport`). The element `y'` is fixed by the flip of `V` (`violFlip_dotIdem`).

## Main results

* `redFirstSeq`, `redFirstViol_eq_violMk_e`: `e⁰_{κ,b}` is the idempotent of one loading.
* `dotIdem`, `violFlip_dotIdem`, `dotIdem_mul_redBraid`.
* `redFirstCut`, `dotCut`: `P⁰_{κ,b} = e⁰_{κ,b} V e_κ` and `y' · P⁰_{κ,b}`.
* `dotTransport`: `y' · P⁰_{κ,b} ≅ y · P⁰_{κ',b}`, `z ↦ r_b z`.
-/

noncomputable section

namespace Categorification.Stendhal

open Equiv KLR KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

namespace BraidedStendhalAlgebra

/-- The red-first loading with the red strands of `s₀` followed by the black strands of `b`. -/
def redFirstSeq (s₀ : Seq (stendhalWeight ℓ (0 : Multiset I))) :
    ∀ b : List I, Seq (stendhalWeight ℓ (blackWeight b))
  | [] => s₀
  | i :: b => appendBlackLoading i (blackWeight b) (redFirstSeq s₀ b)

theorem redProj_nil {κ : List (Fin ℓ)} {s₀ : Seq (stendhalWeight ℓ (0 : Multiset I))}
    (hs₀ : redWord s₀ = κ) :
    redProj k Q Λ 0 κ = ofKLR k Q Λ 0 (KLRAlgebra.e s₀) := by
  rw [redProj, redIdem, Finset.sum_eq_single s₀]
  · intro s hs hne
    exact absurd (eq_of_redWord_eq_nil ((Finset.mem_filter.1 hs).2.trans hs₀.symm)) hne
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ s₀, hs₀⟩) h

/-- `e⁰_{κ,b}` is the idempotent of the loading `redFirstSeq s₀ b`. -/
theorem redFirstViol_eq_violMk_e {κ : List (Fin ℓ)} {s₀ : Seq (stendhalWeight ℓ (0 : Multiset I))}
    (hs₀ : redWord s₀ = κ) :
    ∀ b : List I, redFirstViol Q Λ κ b =
      violMk k Q Λ (blackWeight b) (ofKLR k Q Λ _ (KLRAlgebra.e (redFirstSeq s₀ b)))
  | [] => by
    change violMk k Q Λ 0 (redProj k Q Λ 0 κ) = _
    rw [redProj_nil hs₀]
    rfl
  | i :: b => by
    change appendViol Q Λ i (blackWeight b) (redFirstViol Q Λ κ b) = _
    rw [redFirstViol_eq_violMk_e hs₀ b, appendViol_violMk, appendBlackAlg_apply,
      appendBlackValue_apply, appendBlack_ofKLR_e]
    rfl

theorem redFirstViol_eq_redBraid (κ : List (Fin ℓ)) :
    ∀ b : List I, redFirstViol Q Λ κ b = redBraid (violMk k Q Λ 0 (redProj k Q Λ 0 κ)) b
  | [] => rfl
  | i :: b => by
    change appendViol Q Λ i (blackWeight b) (redFirstViol Q Λ κ b) =
      appendViol Q Λ i (blackWeight b) _
    rw [redFirstViol_eq_redBraid κ b]

theorem commute_redFirstViol_pol (κ : List (Fin ℓ)) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    Commute (violMk k Q Λ (blackWeight b) (ofKLR k Q Λ _ (pol g))) (redFirstViol Q Λ κ b) := by
  rw [redFirstViol_eq_redBraid]
  exact commute_redBraid_pol _ b g

theorem violFlip_redFirstViol (κ : List (Fin ℓ)) :
    ∀ b : List I, violFlip (redFirstViol Q Λ κ b) = redFirstViol Q Λ κ b
  | [] => by
    change violFlip (violMk k Q Λ 0 (redProj k Q Λ 0 κ)) = _
    rw [violFlip_violMk, flip_redProj]
    rfl
  | i :: b => by
    change violFlip (appendViol Q Λ i (blackWeight b) (redFirstViol Q Λ κ b)) =
      appendViol Q Λ i (blackWeight b) (redFirstViol Q Λ κ b)
    rw [violFlip_appendViol, violFlip_redFirstViol κ b]

theorem violFlip_violMk_pol {ν : Multiset I} (g : MvPolynomial (Fin (Multiset.card
    (stendhalWeight ℓ ν))) k) :
    violFlip (violMk k Q Λ ν (ofKLR k Q Λ ν (pol g))) = violMk k Q Λ ν (ofKLR k Q Λ ν (pol g)) := by
  rw [violFlip_violMk, flip_ofKLR, hflip_pol]

theorem violFlip_mul_eq {ν : Multiset I} (a b : ViolQuotient k Q Λ ν) :
    violFlip (a * b) = violFlip b * violFlip a :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ ν) a b)

variable (Q Λ) in
/-- The element `g(x) e⁰_{κ,b}` of `V`. -/
def dotIdem (κ : List (Fin ℓ)) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    ViolQuotient k Q Λ (blackWeight b) :=
  violMk k Q Λ (blackWeight b) (ofKLR k Q Λ _ (pol g)) * redFirstViol Q Λ κ b

/-- The flip of `V` fixes `g(x) e⁰_{κ,b}`. -/
theorem violFlip_dotIdem (κ : List (Fin ℓ)) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    violFlip (dotIdem Q Λ κ b g) = dotIdem Q Λ κ b g := by
  rw [dotIdem, violFlip_mul_eq, violFlip_violMk_pol, violFlip_redFirstViol,
    (commute_redFirstViol_pol κ b g).eq]

theorem redFirstViol_mul_dotIdem {κ : List (Fin ℓ)} {b : List I}
    (hidem : redFirstViol Q Λ κ b * redFirstViol Q Λ κ b = redFirstViol Q Λ κ b)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    redFirstViol Q Λ κ b * dotIdem Q Λ κ b g = dotIdem Q Λ κ b g := by
  rw [dotIdem, ← mul_assoc, ← (commute_redFirstViol_pol κ b g).eq, mul_assoc, hidem]

theorem dotIdem_mul_redFirstViol {κ : List (Fin ℓ)} {b : List I}
    (hidem : redFirstViol Q Λ κ b * redFirstViol Q Λ κ b = redFirstViol Q Λ κ b)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    dotIdem Q Λ κ b g * redFirstViol Q Λ κ b = dotIdem Q Λ κ b g := by
  rw [dotIdem, mul_assoc, hidem]

/-- **`y r_b = r_b y'`**: dots pass through the red braid. -/
theorem dotIdem_mul_redBraid {κ' κ : List (Fin ℓ)} {b : List I} {r₀ : ViolQuotient k Q Λ 0}
    (h : RedFirstData (blackWeight b) κ' κ (redFirstViol Q Λ κ b) (redFirstViol Q Λ κ' b)
      (redBraid r₀ b))
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    dotIdem Q Λ κ' b g * redBraid r₀ b = redBraid r₀ b * dotIdem Q Λ κ b g := by
  rw [dotIdem, dotIdem, mul_assoc, h.braid_left, (commute_redBraid_pol r₀ b g).eq,
    (commute_redFirstViol_pol κ b g).eq, ← mul_assoc, h.braid_right]

set_option quotPrecheck false in
local notation "eB" b:max κ:max =>
  violMk k Q Λ (blackWeight b) (redProj k Q Λ (blackWeight b) κ)

variable (Q Λ) in
/-- The cut `P⁰_{κ'',b} = e⁰_{κ'',b} V e_κ`. -/
def redFirstCut (κ'' κ : List (Fin ℓ)) (b : List I) : Submodule k (ViolQuotient k Q Λ (blackWeight b)) where
  carrier := {c | redFirstViol Q Λ κ'' b * c * eB b κ = c}
  add_mem' {c c'} hc hc' := by
    change _ = _ at hc hc' ⊢
    rw [mul_add, add_mul, hc, hc']
  zero_mem' := by change _ = _; rw [mul_zero, zero_mul]
  smul_mem' a c hc := by
    change _ = _ at hc ⊢
    rw [mul_smul_comm, smul_mul_assoc, hc]

variable (Q Λ) in
/-- The submodule `g(x) e⁰_{κ'',b} · P⁰_{κ'',b}`. -/
def dotCut (κ'' κ : List (Fin ℓ)) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    Submodule k (ViolQuotient k Q Λ (blackWeight b)) :=
  (redFirstCut Q Λ κ'' κ b).map (LinearMap.mulLeft k (dotIdem Q Λ κ'' b g))

variable (hQ : KLRSymm Q)
  (ρ : ∀ ν : Multiset I, Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ ν, TypeA.IsReducedChoice (ρ ν))

include hQ hρ in
theorem redBraid_mul_mem_dotCut {κ' κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀)
    (hne : r₀ ≠ 0) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k)
    (z : dotCut Q Λ κ κ b g) : redBraid r₀ b * z.1 ∈ dotCut Q Λ κ' κ b g := by
  obtain ⟨h, -, -⟩ := redFirstData_redBraid hQ ρ hρ hr₀ hne b
  obtain ⟨c, hc, hz⟩ := z.2
  refine ⟨redBraid r₀ b * c, redBraid_mul_mem h hc, ?_⟩
  change dotIdem Q Λ κ' b g * (redBraid r₀ b * c) = redBraid r₀ b * z.1
  rw [← hz, ← mul_assoc, dotIdem_mul_redBraid h, mul_assoc]
  rfl

/-- **Transport along Corollary 6.8** (Webster, arXiv:1309.3796v3, proof of Theorem 6.14):
left multiplication by the red braid `r_b` identifies `g(x) e⁰_{κ,b} · P⁰_{κ,b}` with
`g(x) e⁰_{κ',b} · P⁰_{κ',b}`; it commutes with the right action of `V`. -/
def dotTransport {κ' κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀)
    (hne : r₀ ≠ 0) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k) :
    dotCut Q Λ κ κ b g ≃ₗ[k] dotCut Q Λ κ' κ b g :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (dotCut Q Λ κ' κ b g)
      (LinearMap.mulLeft k (redBraid r₀ b) ∘ₗ (dotCut Q Λ κ κ b g).subtype)
      (redBraid_mul_mem_dotCut hQ ρ hρ hr₀ hne b g)) (by
    obtain ⟨h, hS, hI⟩ := redFirstData_redBraid hQ ρ hρ hr₀ hne b
    have hF : eB b κ * eB b κ = eB b κ := idemS_mul_self κ
    have hmem : ∀ z : dotCut Q Λ κ κ b g,
        redFirstViol Q Λ κ b * z.1 * eB b κ = z.1 := by
      rintro ⟨_, c, hc, rfl⟩
      change redFirstViol Q Λ κ b * (dotIdem Q Λ κ b g * c) * eB b κ = dotIdem Q Λ κ b g * c
      have hc' : c * eB b κ = c := by
        conv_lhs => rw [← (show _ = c from hc)]
        rw [mul_assoc, hF]
        exact hc
      rw [← mul_assoc, redFirstViol_mul_dotIdem h.idem, mul_assoc, hc']
    refine ⟨fun z z' hzz => Subtype.ext ?_, fun w => ?_⟩
    · have e := congrArg Subtype.val hzz
      change redBraid r₀ b * z.1 = redBraid r₀ b * z'.1 at e
      refine sub_eq_zero.1 (hI _ ?_ (by rw [mul_sub, e, sub_self]))
      rw [mul_sub, sub_mul, hmem z, hmem z']
    · obtain ⟨_, d, hd, rfl⟩ := w
      obtain ⟨c, hc, rfl⟩ := hS d hd
      refine ⟨⟨dotIdem Q Λ κ b g * c, c, hc, rfl⟩, Subtype.ext ?_⟩
      change redBraid r₀ b * (dotIdem Q Λ κ b g * c) = dotIdem Q Λ κ' b g * (redBraid r₀ b * c)
      rw [← mul_assoc, ← mul_assoc, dotIdem_mul_redBraid h])

theorem dotTransport_apply {κ' κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀)
    (hne : r₀ ≠ 0) (b : List I)
    (g : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ (blackWeight b)))) k)
    (z : dotCut Q Λ κ κ b g) :
    (dotTransport hQ ρ hρ hr₀ hne b g z).1 = redBraid r₀ b * z.1 := rfl

end BraidedStendhalAlgebra

end Categorification.Stendhal
