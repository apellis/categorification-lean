/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams
import Categorification.WeightedKLR.RedStrands.Standardization

/-!
# Standard modules with no black strand left of the red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
remark after Definition 5.1: if the first strand of `s` is red (`κ(1) = 0`), the action of
`T̃^λ` on the standard module `S_s = e(s) T̃^λ / U_s` factors through `T̃^λ → T^λ`.

The proof: for a violated sequence `t` (first strand black), every element of `e(s) T̃^λ e(t)`
factors through a sequence strictly above `s`, hence lies in `U_s`. For a diagram with top `s`,
bottom `t` and permutation `τ`, send each black strand of `t` to the smaller of its block in `t`
and its block in `s` (`diagAssign`). The resulting `φ` lies below `τ` in the weak order, so
`ψ_τ e(t) = ψ_{τ φ⁻¹} e(φ • t) ψ_φ e(t)` for suitable reduced words; the middle sequence `φ • t`
is at least `s` (`stendhalLE_phiBottom_diagAssign`), and strictly above it, since the first
strand of `t` stays left of every red strand (`not_stendhalLE_phiBottom_of_violated`).

## Main results

* `StendhalAlgebra.e_mul_mul_e_mem_upperSubmodule`: `e(s) T̃^λ e(t) ⊆ U_s` for `s` not violated
  and `t` violated.
* `StendhalAlgebra.e_mul_mem_upperSubmodule_of_mem_violatedIdeal`: `e(s) K ⊆ U_s`, so the
  violating ideal `K` acts by zero on `S_s`.
* `StendhalAlgebra.rootIdem_mul_mem_rootUpper_of_mem_violatedIdeal`: `e_α K ⊆ U_α` when no
  sequence of root function `α` is violated, in particular when `α(0) = 0`
  (`not_isViolated_of_blackCount_zero`): then `K` acts by zero on `S_α`, as used after
  Definition 5.4 to view standardization as a functor to `T^λ`-modules.
* `StendhalAlgebra.op_smul_rootStandard_eq_zero`, `StendhalAlgebra.op_smul_standardization_eq_zero`:
  `K` acts by zero on `S_α` and on the standardization `S(M) = M ⊗_B S_α` when `α(0) = 0`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial MulOpposite

section Combinatorics

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

theorem redsBefore_zero {m' : ℕ} (lbl : Fin m' → I ⊕ Fin ℓ) (h : 0 < m') :
    redsBefore lbl ⟨0, h⟩ = 0 :=
  Nat.le_zero.1 (redsBefore_le lbl _)

/-- **A violated bottom stays strictly above a non-violated top**: if the first strand of `t`
is black and the first strand of `τ • t` is red, the middle sequence `φ • t` of the diagram is
not below `τ • t`. -/
theorem not_stendhalLE_phiBottom_of_violated [DecidableEq I] {t : Seq μ} (ht : IsRedOrdered t)
    {τ : Perm (Fin m)} (hs : IsRedOrdered (τ • t)) (htv : IsViolated t)
    (hsv : ¬ IsViolated (τ • t)) :
    ¬ StendhalLE (phiBottom t (diagAssign t τ)) (τ • t) := by
  classical
  obtain ⟨h0, hb⟩ := htv
  obtain ⟨i, hi⟩ : ∃ i, t.lbl ⟨0, h0⟩ = .inl i := by
    rcases h : t.lbl ⟨0, h0⟩ with i | r
    · exact ⟨i, rfl⟩
    · simp [h] at hb
  -- the first strand of `τ • t` is the red strand `λ_0`
  obtain ⟨r, hr⟩ : ∃ r, (τ • t).lbl ⟨0, h0⟩ = .inr r := by
    rcases h : (τ • t).lbl ⟨0, h0⟩ with j | r
    · exact absurd ⟨h0, by simp [h]⟩ hsv
    · exact ⟨r, rfl⟩
  have hr0 : r.val = 0 := by
    have := redIndexed_of_isRedOrdered hs ⟨0, h0⟩ r hr
    rw [redsBefore_zero] at this
    exact this
  intro hle
  have h := hle r i
  -- no black strand of `τ • t` is left of its first strand
  have hz : blackCount (τ • t) r i = 0 := by
    rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨-, ha⟩
    exact absurd (Fin.lt_def.1 (ha _ hr)) (Nat.not_lt_zero _)
  -- the first strand of `t` is left of `λ_0` in `φ • t`
  have hpos : 0 < blackCount (phiBottom t (diagAssign t τ)) r i := by
    rw [blackCount_smul]
    refine Finset.card_pos.2 ⟨⟨0, h0⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hi, fun q hq => (keyPerm_lt_iff _).2 (.inl ?_)⟩
    have hq' := redIndexed_of_isRedOrdered ht q r hq
    rw [assignKey_black _ (by simp [hi]), assignKey_red (diagAssign_mem t τ) (by simp [hq])]
    have : diagAssign t τ ⟨0, h0⟩ = 0 := by
      unfold diagAssign
      simp only [hi, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
      rw [redsBefore_zero]
      exact Nat.zero_min _
    omega
  omega

/-- A violated sequence has a black strand left of the red strand `λ_0`. -/
theorem not_isViolated_of_blackCount_zero [DecidableEq I] {s : Seq μ} (hℓ : 0 < ℓ)
    (h0 : ∀ i, blackCount s ⟨0, hℓ⟩ i = 0) : ¬ IsViolated s := by
  classical
  rintro ⟨hm, hb⟩
  obtain ⟨i, hi⟩ : ∃ i, s.lbl ⟨0, hm⟩ = .inl i := by
    rcases h : s.lbl ⟨0, hm⟩ with i | r
    · exact ⟨i, rfl⟩
    · simp [h] at hb
  have := h0 i
  rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
  refine this (Finset.mem_univ ⟨0, hm⟩) ⟨hi, fun q hq => Fin.lt_def.2 (Nat.pos_of_ne_zero ?_)⟩
  intro hq0
  have : q = ⟨0, hm⟩ := Fin.ext hq0
  rw [this, hi] at hq
  exact Sum.inl_ne_inr hq

end Combinatorics

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebra k Q Λ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "E" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- `e(s) y e(t)` as an element of `T̃^λ`, for red-ordered `s`, `t`. -/
def idemCut (s t : Seq μ) (hs : IsRedOrdered s) (ht : IsRedOrdered t)
    (y : StendhalAlgebraAllOrders k Q Λ ν) : A :=
  ⟨E s * y * E t, by
    classical
    rw [Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem]
    constructor
    · rw [← mul_assoc, ← mul_assoc, StendhalAlgebraAllOrders.redOrderedIdem_mul_e,
        ite_eq_left_of_eq_true _ _ (eq_true hs)]
    · rw [mul_assoc, StendhalAlgebraAllOrders.e_mul_redOrderedIdem,
        ite_eq_left_of_eq_true _ _ (eq_true ht)]⟩

theorem E_mul_E_self (s : Seq μ) : E s * E s = E s := by
  simp [StendhalAlgebraAllOrders.e_mul_e]

theorem idemCut_mul_idemCut {s b t : Seq μ} (hs : IsRedOrdered s) (hb : IsRedOrdered b)
    (ht : IsRedOrdered t) (y y' : StendhalAlgebraAllOrders k Q Λ ν) :
    idemCut s b hs hb y * idemCut b t hb ht y' = idemCut s t hs ht (y * E b * y') :=
  Subtype.ext (by
    change E s * y * E b * (E b * y' * E t) = E s * (y * E b * y') * E t
    calc E s * y * E b * (E b * y' * E t) = E s * y * (E b * E b) * y' * E t := by
          simp only [mul_assoc]
      _ = _ := by rw [E_mul_E_self]; simp only [mul_assoc])

theorem e_mul_idemCut {s b : Seq μ} (hs : IsRedOrdered s) (hb : IsRedOrdered b)
    (y : StendhalAlgebraAllOrders k Q Λ ν) :
    e s hs * idemCut s b hs hb y * e b hb = idemCut s b hs hb y :=
  Subtype.ext (by
    change E s * (E s * y * E b) * E b = E s * y * E b
    calc E s * (E s * y * E b) * E b = (E s * E s) * y * (E b * E b) := by
          simp only [mul_assoc]
      _ = _ := by rw [E_mul_E_self, E_mul_E_self])

theorem e_mul_mul_e_eq_idemCut {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (a : A) :
    e s hs * a * e t ht = idemCut s t hs ht a.1 :=
  rfl

theorem idemCut_add {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t)
    (y y' : StendhalAlgebraAllOrders k Q Λ ν) :
    idemCut s t hs ht (y + y') = idemCut s t hs ht y + idemCut s t hs ht y' :=
  Subtype.ext (by
    change E s * (y + y') * E t = E s * y * E t + E s * y' * E t
    rw [mul_add, add_mul])

theorem idemCut_zero {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    idemCut s t hs ht (0 : StendhalAlgebraAllOrders k Q Λ ν) = 0 :=
  Subtype.ext (by
    change E s * 0 * E t = 0
    rw [mul_zero, zero_mul])

theorem idemCut_smul {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t) (c : k)
    (y : StendhalAlgebraAllOrders k Q Λ ν) :
    idemCut s t hs ht (c • y) = idemCut s t hs ht y * idemCut t t ht ht (algebraMap k _ c) := by
  rw [idemCut_mul_idemCut]
  apply Subtype.ext
  change E s * _ * E t = E s * _ * E t
  rw [Algebra.smul_def, Algebra.commutes c y, mul_assoc y (E t), ← Algebra.commutes c (E t)]
  simp only [mul_assoc, E_mul_E_self]

/-- **Violated sequences factor through higher ones** (Webster, arXiv:1309.3796v3, remark after
Definition 5.1): if the first strand of `s` is red and the first strand of `t` is black, then
`e(s) T̃^λ e(t) ⊆ U_s`. -/
theorem e_mul_mul_e_mem_upperSubmodule {s t : Seq μ} (hs : IsRedOrdered s) (ht : IsRedOrdered t)
    (hsv : ¬ IsViolated s) (htv : IsViolated t) (a : A) :
    e s hs * a * e t ht ∈ upperSubmodule Q Λ s hs := by
  classical
  obtain ⟨z, hz⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) a.1
  rw [e_mul_mul_e_eq_idemCut, ← hz]
  set r : R := KLRAlgebra.e s * z * KLRAlgebra.e t with hr_def
  have hcut : idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z) =
      idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν r) := by
    apply Subtype.ext
    change E s * _ * E t = E s * _ * E t
    rw [hr_def, map_mul, map_mul]
    change _ = E s * (E s * _ * E t) * E t
    calc E s * StendhalAlgebraAllOrders.ofKLR k Q Λ ν z * E t
        = (E s * E s) * StendhalAlgebraAllOrders.ofKLR k Q Λ ν z * (E t * E t) := by
          rw [E_mul_E_self, E_mul_E_self]
      _ = _ := by simp only [mul_assoc]
  rw [hcut]
  have hr : KLRAlgebra.e s * r * KLRAlgebra.e t = r := by
    rw [hr_def, ← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_self, mul_assoc,
      KLRAlgebra.e_mul_self]
  -- reduced words through `φ`
  let ρ : Perm (Fin m) → List ℕ := fun w => (exists_reduced m w).choose
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := fun w =>
    (exists_reduced m w).choose_spec
  let v : Perm (Fin m) → Perm (Fin m) := fun τ =>
    if τ • t = s then phiPerm t (diagAssign t τ) else 1
  have hv : ∀ τ, invSet m (v τ) ⊆ invSet m τ := fun τ => by
    dsimp only [v]
    split_ifs with h
    · exact invSet_phiPerm_diagAssign ht (h ▸ hs)
    · intro x hx
      simp [invSet] at hx
      exact absurd hx.2 (lt_asymm hx.1)
  let ρ' : Perm (Fin m) → List ℕ := fun τ => ρ (τ * (v τ)⁻¹) ++ ρ (v τ)
  have hρ' : ∀ τ, IsReduced m (ρ' τ) ∧ wordProd m (ρ' τ) = τ := fun τ => by
    have hl := length_add_of_invSet_subset (hv τ)
    refine ⟨⟨validWord_append.2 ⟨(hρ _).1.1, (hρ _).1.1⟩, ?_⟩, ?_⟩
    · rw [List.length_append, wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right,
        (hρ _).1.2, (hρ _).1.2, (hρ _).2, (hρ _).2, hl]
    · rw [wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right]
  have hmem := KLRAlgebra.mem_span_corner_dotsTop ρ' hρ' t s hr
  let F : R → A := fun x => idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν x)
  change F r ∈ _
  suffices key : ∀ x ∈ Submodule.span k {b : R | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ),
      w • t = s ∧ KLRAlgebra.pol (monomial u 1) * KLRAlgebra.ψw (ρ' w) * KLRAlgebra.e t = b},
      F x ∈ upperSubmodule Q Λ s hs from key r hmem
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨τ, u, hτ, rfl⟩ := hx
    set φ := phiPerm t (diagAssign t τ)
    have hvτ : v τ = φ := by simp [v, hτ, φ]
    have hg := diagAssign_mem t τ
    have hb := isRedOrdered_phiBottom ht hg
    have hlt : StendhalLT s (phiBottom t (diagAssign t τ)) :=
      ⟨hτ ▸ stendhalLE_phiBottom_diagAssign ht (hτ ▸ hs),
        hτ ▸ not_stendhalLE_phiBottom_of_violated ht (hτ ▸ hs) htv (hτ ▸ hsv)⟩
    have hfac : F (KLRAlgebra.pol (monomial u 1) * KLRAlgebra.ψw (ρ' τ) * KLRAlgebra.e t) =
        idemCut s (phiBottom t (diagAssign t τ)) hs hb
          (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
            (KLRAlgebra.pol (monomial u 1) * KLRAlgebra.ψw (ρ (τ * φ⁻¹)))) *
        idemCut (phiBottom t (diagAssign t τ)) t hb ht
          (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ φ))) := by
      have hb' : E (phiBottom t (diagAssign t τ)) *
          StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ φ)) =
          StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ φ) * KLRAlgebra.e t) := by
        change StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.e (φ • t)) * _ = _
        rw [← map_mul, KLRAlgebra.e_mul_ψw, (hρ _).2, inv_smul_smul]
      rw [idemCut_mul_idemCut]
      simp only [F]
      congr 1
      rw [mul_assoc (StendhalAlgebraAllOrders.ofKLR k Q Λ ν _), hb', ← map_mul]
      congr 1
      rw [show ρ' τ = ρ (τ * φ⁻¹) ++ ρ φ by simp only [ρ', hvτ], KLRAlgebra.ψw_append]
      simp only [mul_assoc]
    rw [hfac, ← e_mul_idemCut hs hb]
    exact Submodule.smul_mem _ (op _) (Submodule.subset_span ⟨_, hb, _, hlt, rfl⟩)
  | zero =>
    change idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν 0) ∈ _
    rw [map_zero, idemCut_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    change idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (x + y)) ∈ _
    rw [map_add, idemCut_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    change idemCut s t hs ht (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (c • x)) ∈ _
    rw [map_smul, idemCut_smul]
    exact Submodule.smul_mem _ (op _) hx

/-- **The violating ideal acts by zero on `S_s`** when the first strand of `s` is red (Webster,
arXiv:1309.3796v3, remark after Definition 5.1): `e(s) K ⊆ U_s`. -/
theorem e_mul_mem_upperSubmodule_of_mem_violatedIdeal {s : Seq μ} (hs : IsRedOrdered s)
    (hsv : ¬ IsViolated s) {x : A} (hx : x ∈ violatedIdeal k Q Λ ν) :
    e s hs * x ∈ upperSubmodule Q Λ s hs := by
  suffices h : ∀ c : A, e s hs * c * x ∈ upperSubmodule Q Λ s hs by
    simpa using h 1
  induction hx using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, htv, rfl⟩ := hy
    exact fun c => e_mul_mul_e_mem_upperSubmodule hs ht hsv htv c
  | zero => intro c; rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro c; rw [mul_add]; exact add_mem (hx c) (hy c)
  | neg x _ hx =>
    intro c
    rw [show e s hs * c * -x = -(e s hs * c * x) from Subtype.ext (mul_neg _ _)]
    exact neg_mem (hx c)
  | left_absorb a x _ hx =>
    intro c
    rw [← mul_assoc, mul_assoc (e s hs)]
    exact hx (c * a)
  | right_absorb a x _ hx =>
    intro c
    rw [← mul_assoc]
    exact Submodule.smul_mem _ (op a) (hx c)

/-- `e_α` as the sum of the idempotents of its sequences. -/
theorem rootIdem_eq_sum (α : Fin ℓ → I → ℕ) :
    rootIdem Q Λ α = ∑ s ∈ (rootSet ν α).attach, e s.1 (mem_rootSet.1 s.2).1 := by
  let v : A →+ StendhalAlgebraAllOrders k Q Λ ν := ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩
  apply Subtype.ext
  change _ = v _
  rw [map_sum, coe_rootIdem, ← Finset.sum_attach]
  rfl

/-- **The violating ideal acts by zero on `S_α`** (Webster, arXiv:1309.3796v3, remark after
Definition 5.4) when no sequence of root function `α` is violated: `e_α K ⊆ U_α`. -/
theorem rootIdem_mul_mem_rootUpper_of_mem_violatedIdeal (α : Fin ℓ → I → ℕ)
    (hα : ∀ s ∈ rootSet ν α, ¬ IsViolated s) {x : A} (hx : x ∈ violatedIdeal k Q Λ ν) :
    rootIdem Q Λ α * x ∈ rootUpper Q Λ α := by
  rw [rootIdem_eq_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun s _ => ?_
  have h := (mem_rootSet.1 s.2).2
  have := upperSubmodule_le_rootUpper (Q := Q) (Λ := Λ) s.1 (mem_rootSet.1 s.2).1
    (e_mul_mem_upperSubmodule_of_mem_violatedIdeal _ (hα s.1 s.2) hx)
  convert this using 2
  exact h.symm

/-- **The violating ideal acts by zero on `S_α`** when no sequence of root function `α` is
violated. -/
theorem op_smul_rootStandard_eq_zero (α : Fin ℓ → I → ℕ)
    (hα : ∀ s ∈ rootSet ν α, ¬ IsViolated s) {x : A} (hx : x ∈ violatedIdeal k Q Λ ν)
    (v : rootStandard (ν := ν) Q Λ α) : op x • v = 0 := by
  obtain ⟨y, hy, hv⟩ := Submodule.mem_map.1 v.2
  apply Subtype.ext
  change op x • (v : A ⧸ rootUpper (ν := ν) Q Λ α) = 0
  rw [← hv, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, op_smul_eq_mul]
  have hy' := (mem_span_singleton_iff_mul (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ)
    (ν := ν) α) y).1 hy
  rw [← hy', mul_assoc]
  exact rootIdem_mul_mem_rootUpper_of_mem_violatedIdeal α hα
    ((violatedIdeal k Q Λ ν).mul_mem_left y x hx)

/-- With no black strand left of `λ_0` (`b_0 = 0`), no sequence of the root function of the
blocks is violated. -/
theorem not_isViolated_of_mem_rootSet_blockRoot {b : Fin (ℓ + 1) → Multiset I} (hℓ : 0 < ℓ)
    (hb : b 0 = 0) {s : Seq (stendhalWeight ℓ (blockPrefix b (ℓ + 1)))}
    (hs : s ∈ rootSet (blockPrefix b (ℓ + 1)) (blockRoot b)) : ¬ IsViolated s := by
  refine not_isViolated_of_blackCount_zero hℓ fun i => ?_
  rw [(mem_rootSet.1 hs).2, blockRoot, blockPrefix]
  have : (Finset.univ.filter fun j : Fin (ℓ + 1) => j.val < (⟨0, hℓ⟩ : Fin ℓ).val + 1) = {0} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun h => Fin.ext ?_, fun h => ⟨Finset.mem_univ _, by rw [h]; exact Nat.zero_lt_one⟩⟩
    have := h.2
    change j.val < 0 + 1 at this
    change j.val = 0
    omega
  rw [this, Finset.sum_singleton, hb, Multiset.count_zero]

section Standardization

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- **Standardization lands in `T^λ`-modules** when `b_0 = 0` (Webster, arXiv:1309.3796v3,
remark after Definition 5.4): the violating ideal acts by zero on `S(M) = M ⊗_B S_α`. -/
theorem op_smul_standardization_eq_zero {b : Fin (ℓ + 1) → Multiset I}
    (hb : ∀ s ∈ rootSet (blockPrefix b (ℓ + 1)) (blockRoot b), ¬ IsViolated s)
    (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    {x : StendhalAlgebra k Q Λ (blockPrefix b (ℓ + 1))}
    (hx : x ∈ violatedIdeal k Q Λ (blockPrefix b (ℓ + 1))) (v : Standardization Q Λ b M) :
    op x • v = 0 := by
  refine BalancedTensor.induction_on v (smul_zero _) (fun y z => ?_)
    (fun v w hv hw => by rw [smul_add, hv, hw, add_zero])
  rw [BalancedTensor.smul_tmul', op_smul_rootStandard_eq_zero _ hb hx, BalancedTensor.zero_tmul]

end Standardization

end StendhalAlgebra

end Categorification.Stendhal
