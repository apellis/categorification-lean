/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardModule

/-!
# Standard modules along idempotent splittings of `T^λ e(s)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.18: the indecomposable summands of `T^λ e(s)` whose root function is that of `s`
surject onto the standard module `S_s`, which is the direct sum of standard quotients of
these projectives; the summands with a higher root function lie in the image of projectives
`T^λ e(t)` with `t` above `s`, so in `U_s`.

We state this for an arbitrary orthogonal idempotent decomposition `e(s) = ∑ⱼ fⱼ`
(`IsSeqDecomp`), in the left-module form of `LeftStandardModule`. The standard quotient of the
summand `T^λ fⱼ` is `T^λ fⱼ / Uⱼ`, where `Uⱼ` is spanned by the elements `e(t) a fⱼ` with `t`
above `s` (`upperAt`); it is `T^λ fⱼ ∩ U_s` (`leftUpper_inf_lIdeal`). The root function of a
summand is read off from the loadings `q` with `fⱼ ∈ T^λ e(q) T^λ`: a summand whose idempotent
factors through a loading above `s` has zero standard quotient
(`IsSeqDecomp.subsingleton_standardPiece`).

## Main definitions

* `upperAt s g`: the left ideal spanned by the `e(t) a g`, `t` above `s`.
* `IsSeqDecomp`: an orthogonal decomposition of `e(s)` into idempotents.
* `standardPiece s g`: the standard quotient `T^λ g / upperAt s g`.

## Main results

* `leftUpper_inf_lIdeal`: `U_s ∩ T^λ g = upperAt s g` for an idempotent `g ≤ e(s)`.
* `IsSeqDecomp.leftStandardEquiv`: `S_s ≅ ∏ⱼ T^λ fⱼ / Uⱼ`.
* `IsSeqDecomp.subsingleton_standardPiece`: summands factoring through a higher loading have
  zero standard quotient.
* `IsSeqDecomp.lIdeal_le_sup`: the remaining summands, together with `U_s`, span
  `T^λ e(s)`, so they surject onto `S_s`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν

/-- The kernel of the standard quotient of `T^λ g`: the left ideal spanned by the elements
`e(t) a g` with `t` strictly above `s`. -/
def upperAt (s : Seq μ) (g : A) : Submodule A A :=
  Submodule.span A
    {z | ∃ (t : Seq μ) (ht : IsRedOrdered t) (a : A),
      StendhalLT s t ∧ z = seqIdem Q Λ t ht * a * g}

variable {Q Λ}

theorem mul_mem_upperAt {s : Seq μ} {hs : IsRedOrdered s} {g z : A}
    (hg : seqIdem Q Λ s hs * g = g) (hz : z ∈ leftUpper Q Λ s hs) :
    z * g ∈ upperAt Q Λ s g := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, a, hst, rfl⟩ := hx
    refine Submodule.subset_span ⟨t, ht, a * seqIdem Q Λ s hs, hst, ?_⟩
    simp only [mul_assoc, hg]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact Submodule.smul_mem _ a hx

theorem upperAt_le_leftUpper {s : Seq μ} {hs : IsRedOrdered s} {g : A}
    (hg : g * seqIdem Q Λ s hs = g) : upperAt Q Λ s g ≤ leftUpper Q Λ s hs := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t, ht, a, hst, rfl⟩
  refine Submodule.subset_span ⟨t, ht, a * g, hst, ?_⟩
  simp only [mul_assoc, hg]

theorem leftUpper_inf_lIdeal {s : Seq μ} {hs : IsRedOrdered s} {g : A}
    (hg : IsIdempotentElem g) (hgl : seqIdem Q Λ s hs * g = g)
    (hgr : g * seqIdem Q Λ s hs = g) :
    leftUpper Q Λ s hs ⊓ lIdeal g = upperAt Q Λ s g := by
  refine le_antisymm (fun z hz => ?_) (le_inf (upperAt_le_leftUpper hgr) ?_)
  · have h := mul_mem_upperAt hgl hz.1
    rwa [(mem_lIdeal.1 hz.2)] at h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨t, ht, a, -, rfl⟩
    change _ * _ = _
    rw [mul_assoc, hg.eq]

theorem mem_leftUpper_of_mem_span {s : Seq μ} {hs : IsRedOrdered s} {q : Seq μ}
    {hq : IsRedOrdered q} (hsq : StendhalLT s q) {g : A}
    (hg : g ∈ Submodule.span A (Set.range fun b : A => seqIdem Q Λ q hq * b)) :
    g * seqIdem Q Λ s hs ∈ leftUpper Q Λ s hs := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact Submodule.subset_span ⟨q, hq, b, hsq, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact Submodule.smul_mem _ a hx

section Decomposition

variable {s : Seq (stendhalWeight ℓ ν)} {hs : IsRedOrdered s} {J : Type*} [Fintype J]
  {f : J → TensorProductAlgebra k Q Λ ν}

/-- An orthogonal decomposition `e(s) = ∑ j, f j` into idempotents. -/
structure IsSeqDecomp (s : Seq μ) (hs : IsRedOrdered s) (f : J → A) : Prop where
  idem : ∀ j, IsIdempotentElem (f j)
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ j, f j = seqIdem Q Λ s hs

theorem IsSeqDecomp.seqIdem_mul (h : IsSeqDecomp s hs f) (j : J) :
    seqIdem Q Λ s hs * f j = f j := by
  rw [← h.sum, Finset.sum_mul, Finset.sum_eq_single j (fun i _ hij => h.orth i j hij)
    (by simp), (h.idem j).eq]

theorem IsSeqDecomp.mul_seqIdem (h : IsSeqDecomp s hs f) (j : J) :
    f j * seqIdem Q Λ s hs = f j := by
  rw [← h.sum, Finset.mul_sum, Finset.sum_eq_single j
    (fun i _ hij => h.orth j i (Ne.symm hij)) (by simp), (h.idem j).eq]

theorem IsSeqDecomp.mul_eq_zero (h : IsSeqDecomp s hs f) {y : A} {i j : J}
    (hy : y ∈ lIdeal (f i)) (hij : i ≠ j) : y * f j = 0 := by
  rw [← mem_lIdeal.1 hy, mul_assoc, h.orth i j hij, mul_zero]

/-- Membership in `U_s` splits along an orthogonal decomposition of `e(s)`. -/
theorem IsSeqDecomp.mem_leftUpper_iff (h : IsSeqDecomp s hs f) {y : A}
    (hy : y ∈ lIdeal (seqIdem Q Λ s hs)) :
    y ∈ leftUpper Q Λ s hs ↔ ∀ j, y * f j ∈ upperAt Q Λ s (f j) := by
  refine ⟨fun hu j => mul_mem_upperAt (h.seqIdem_mul j) hu, fun hu => ?_⟩
  rw [← mem_lIdeal.1 hy, ← h.sum, Finset.mul_sum]
  exact Submodule.sum_mem _ fun j _ => upperAt_le_leftUpper (h.mul_seqIdem j) (hu j)

/-- Right multiplication by an idempotent `g`, as a map `T^λ → T^λ g` of left modules. -/
def lIdealMulRight (g : A) (hg : IsIdempotentElem g) : A →ₗ[A] lIdeal g where
  toFun y := ⟨y * g, by rw [mem_lIdeal, mul_assoc, hg.eq]⟩
  map_add' x y := Subtype.ext (add_mul x y g)
  map_smul' a y := Subtype.ext (by simp [smul_eq_mul, mul_assoc])

variable (Q Λ) in
/-- The standard quotient `T^λ g / (T^λ g ∩ U_s)` of a summand `T^λ g` of `T^λ e(s)`. -/
abbrev standardPiece (s : Seq μ) (g : A) : Type :=
  lIdeal g ⧸ (upperAt Q Λ s g).comap (lIdeal g).subtype

/-- The map `T^λ e(s) → ∏ⱼ T^λ fⱼ / Uⱼ`, `y ↦ (y fⱼ)ⱼ`. -/
def IsSeqDecomp.toPieces (h : IsSeqDecomp s hs f) :
    lIdeal (seqIdem Q Λ s hs) →ₗ[A] Π j, standardPiece Q Λ s (f j) :=
  LinearMap.pi fun j => (Submodule.mkQ _).comp
    ((lIdealMulRight (f j) (h.idem j)).comp (lIdeal (seqIdem Q Λ s hs)).subtype)

theorem IsSeqDecomp.ker_toPieces (h : IsSeqDecomp s hs f) :
    LinearMap.ker h.toPieces =
      (leftUpper Q Λ s hs).comap (lIdeal (seqIdem Q Λ s hs)).subtype := by
  ext y
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  rw [h.mem_leftUpper_iff y.2, funext_iff]
  refine forall_congr' fun j => ?_
  simp [IsSeqDecomp.toPieces, lIdealMulRight, Submodule.Quotient.mk_eq_zero]

theorem IsSeqDecomp.toPieces_surjective (h : IsSeqDecomp s hs f) :
    Function.Surjective h.toPieces := by
  intro x
  choose y hy using fun j => Submodule.Quotient.mk_surjective _ (x j)
  have hy' : ∀ j, (y j : A) * f j = y j := fun j => mem_lIdeal.1 (y j).2
  refine ⟨⟨∑ j, (y j : A), ?_⟩, funext fun j => ?_⟩
  · rw [mem_lIdeal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy' j, mul_assoc, h.mul_seqIdem]
  · rw [← hy j]
    simp only [IsSeqDecomp.toPieces, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
    congr 1
    refine Subtype.ext ?_
    change (∑ i, (y i : A)) * f j = y j
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i _ hij => h.mul_eq_zero (y i).2 hij)
      (by simp), hy']

/-- **Webster, Proposition 5.18, splitting of `S_s`.** Along an orthogonal idempotent
decomposition `e(s) = ∑ⱼ fⱼ`, the standard module splits as the product of the standard
quotients `T^λ fⱼ / (T^λ fⱼ ∩ U_s)` of the summands. -/
def IsSeqDecomp.leftStandardEquiv (h : IsSeqDecomp s hs f) :
    leftStandard Q Λ s hs ≃ₗ[A] Π j, standardPiece Q Λ s (f j) :=
  (Submodule.quotEquivOfEq _ _ h.ker_toPieces.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ h.toPieces_surjective)

/-- A summand `T^λ g` whose idempotent factors through some `e(q)` with `q` above `s` lies in
`U_s`. -/
theorem lIdeal_le_leftUpper {s : Seq μ} {hs : IsRedOrdered s} {q : Seq μ}
    {hq : IsRedOrdered q} (hsq : StendhalLT s q) {g : A} (hgr : g * seqIdem Q Λ s hs = g)
    (hg : g ∈ Submodule.span A (Set.range fun b : A => seqIdem Q Λ q hq * b)) :
    lIdeal g ≤ leftUpper Q Λ s hs := by
  intro y hy
  have h1 := mem_leftUpper_of_mem_span (hs := hs) hsq hg
  rw [hgr] at h1
  rw [← mem_lIdeal.1 hy]
  exact Submodule.smul_mem _ y h1

/-- **Webster, Proposition 5.18, higher summands.** The standard quotient of a summand whose
idempotent factors through a loading above `s` vanishes. -/
theorem IsSeqDecomp.subsingleton_standardPiece (h : IsSeqDecomp s hs f) {j : J}
    {q : Seq μ} {hq : IsRedOrdered q} (hsq : StendhalLT s q)
    (hg : f j ∈ Submodule.span A (Set.range fun b : A => seqIdem Q Λ q hq * b)) :
    Subsingleton (standardPiece Q Λ s (f j)) := by
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun y _ => ?_)
  have hle := lIdeal_le_leftUpper hsq (h.mul_seqIdem j) hg y.2
  rw [Submodule.mem_comap, Submodule.subtype_apply,
    ← leftUpper_inf_lIdeal (h.idem j) (h.seqIdem_mul j) (h.mul_seqIdem j)]
  exact ⟨hle, y.2⟩

/-- **Webster, Proposition 5.18, surjectivity.** If every summand outside `L` factors through
a loading above `s`, the summands `T^λ fⱼ`, `j ∈ L`, map onto `S_s`: together with `U_s` they
span `T^λ e(s)`. -/
theorem IsSeqDecomp.lIdeal_le_sup (h : IsSeqDecomp s hs f) (L : Finset J)
    (hL : ∀ j ∉ L, ∃ (q : Seq μ) (hq : IsRedOrdered q), StendhalLT s q ∧
      f j ∈ Submodule.span A (Set.range fun b : A => seqIdem Q Λ q hq * b)) :
    lIdeal (seqIdem Q Λ s hs) ≤ leftUpper Q Λ s hs ⊔ ⨆ j ∈ L, lIdeal (f j) := by
  intro y hy
  rw [← mem_lIdeal.1 hy, ← h.sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hyj : y * f j ∈ lIdeal (f j) := by rw [mem_lIdeal, mul_assoc, (h.idem j).eq]
  by_cases hj : j ∈ L
  · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj hyj))
  · obtain ⟨q, hq, hsq, hg⟩ := hL j hj
    exact Submodule.mem_sup_left (lIdeal_le_leftUpper hsq (h.mul_seqIdem j) hg hyj)

end Decomposition

end Categorification.Stendhal
