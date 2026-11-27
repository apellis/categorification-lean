/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtErase
import Categorification.WeightedKLR.Rigidity.RigidityExtTrace

/-!
# The unique simple quotient of a wrap projective

Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3, in the form that only uses the cyclotomic quotient
at the first red strand. For two red strands and an idempotent `z₀` of `R^{λ₁}(ν)`, the *wrap
idempotent* `wrapIdem z₀` puts the first red strand on the left and the second on the right of
`z₀`. Let the *cuts* be the idempotents of red-ordered loadings whose last strand is not the
second red strand, i.e. the loadings `κ` with `κ(2) < |ν|`.

Under the cyclotomic relation `hR` of the second red strand on the last black strand, if every
nonzero element of `z₀ R^{λ₁}(ν)` generates `z₀` on the right, then the sum of the images of all
maps from cut projectives is the unique submodule of the right projective `wrapIdem z₀ · T` with
simple quotient (`coevaluationTrace_eq_iff_isSimpleModule_wrapIdem`).
-/

noncomputable section

namespace Categorification.Stendhal.TwoRedErase

open KLR KLRAlgebra TypeA MulOpposite

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ) (ν : Multiset I)

local notation "μ" => stendhalWeight 2 ν
local notation "n" => Multiset.card ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "π" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "Λ₀" => (Λ ∘ Fin.castSucc : Fin 1 → I →₀ ℕ)
local notation "Ordered" => { s : Seq μ // IsRedOrdered s }

/-- The red-ordered loadings whose last strand is not the second red strand: the loadings `κ`
with `κ(2) < |ν|` of Webster, arXiv:1309.3796v3, Lemma 7.3. -/
def CutLoading : Type _ := { s : Ordered // ¬HasLastRed (ℓ := 1) s.1 }

instance : Finite (CutLoading ν) := Subtype.finite

/-- The idempotent of a cut loading. -/
def cutIdem (s : CutLoading ν) : T :=
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s.1.1 s.1.2)

theorem isIdempotentElem_cutIdem (s : CutLoading ν) : IsIdempotentElem (cutIdem Q Λ ν s) := by
  rw [IsIdempotentElem, cutIdem, ← map_mul]
  congr 1
  apply Subtype.ext
  change (StendhalAlgebraAllOrders.e (Λ := Λ) s.1.1 : StendhalAlgebraAllOrders k Q Λ ν) *
    StendhalAlgebraAllOrders.e s.1.1 = StendhalAlgebraAllOrders.e s.1.1
  simpa using (StendhalAlgebraAllOrders.e_mul_e (k := k) (Q := Q) (Λ := Λ) s.1.1 s.1.1)

/-- The wrap idempotent of an idempotent `z₀` of the cyclotomic quotient: the second red strand
appended to the cyclotomic projection of `z₀`. -/
def wrapIdem (z : C) : T :=
  (appendRed (ℓ := 1) Q Λ ν (SingleRed.cyclotomicProjection Q Λ₀ ν z)).val

local notation "l" => TensorProductAlgebra.lastRedIdem (ℓ := 1) Q Λ ν

theorem wrapIdem_mul (z z' : C) : wrapIdem Q Λ ν z * wrapIdem Q Λ ν z' = wrapIdem Q Λ ν (z * z') := by
  rw [wrapIdem, wrapIdem, wrapIdem, map_mul, map_mul]
  rfl

theorem lastRedIdem_mul_val (y : TensorProductAlgebra.lastRedCorner (ℓ := 1) Q Λ ν) :
    l * y.val = y.val :=
  ((Subsemigroup.mem_corner_iff (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν)).1
    y.2).1

theorem val_mul_lastRedIdem (y : TensorProductAlgebra.lastRedCorner (ℓ := 1) Q Λ ν) :
    y.val * l = y.val :=
  ((Subsemigroup.mem_corner_iff (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν)).1
    y.2).2

private theorem one_sub_lastRedIdem [Fintype Ordered] [Fintype (CutLoading ν)] :
    (1 : T) - l = ∑ s : CutLoading ν, cutIdem Q Λ ν s := by
  classical
  let f : Ordered → T := fun s => TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s.1 s.2)
  have h1 : (∑ s : Ordered, StendhalAlgebra.e s.1 s.2 : StendhalAlgebra k Q Λ ν) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : Ordered, StendhalAlgebraAllOrders.e s.1) =
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    rw [StendhalAlgebraAllOrders.redOrderedIdem]
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  have hone : (1 : T) = ∑ s : Ordered, f s := by
    simpa only [map_sum, map_one] using (congrArg (TensorProductAlgebra.mk Q Λ ν) h1).symm
  have hl : l = ∑ s ∈ Finset.univ.filter (fun s : Ordered => HasLastRed (ℓ := 1) s.1), f s := by
    rw [TensorProductAlgebra.lastRedIdem, StendhalAlgebra.lastRedIdem, map_sum]
    exact Finset.sum_congr (by ext; simp) fun _ _ => rfl
  rw [hone, hl, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun s : Ordered => HasLastRed (ℓ := 1) s.1), add_sub_cancel_left]
  rw [Finset.sum_subtype (Finset.univ.filter fun s : Ordered => ¬HasLastRed (ℓ := 1) s.1)
    (p := fun s : Ordered => ¬HasLastRed (ℓ := 1) s.1) (fun s => by simp) f]
  exact Fintype.sum_equiv (κ := CutLoading ν) (Equiv.refl _)
    (fun s => f s.1) (cutIdem Q Λ ν) (fun _ => rfl)

/-- A wrap loading's idempotent is not a cut. -/
private theorem eraseWrap_cutIdem (hR : LastDotRelation Q Λ ν) (s : CutLoading ν) :
    eraseWrap Q Λ ν hR (cutIdem Q Λ ν s) = 0 := by
  apply eraseWrap_e_of_not_wrap
  rintro ⟨t, ht⟩
  apply s.2
  rw [← ht]
  exact hasLastRed_appendRedLoading (ℓ := 1) (SingleRed.insertWord ν t)

/-- **The unique simple quotient of a wrap projective** (Webster, arXiv:1309.3796v3, §7.1,
Lemma 7.3, reduced to the cyclotomic quotient at the first red strand). If the second red strand's
cyclotomic relation holds on the last black strand of `R^{λ₁}(ν)`, and every nonzero element of
`z₀ R^{λ₁}(ν)` generates `z₀` on the right, then the sum of the images of maps from the
projectives of the loadings with `κ(2) < |ν|` is the unique submodule of the wrap projective with
simple quotient. -/
theorem coevaluationTrace_eq_iff_isSimpleModule_wrapIdem
    (hR : LastDotRelation Q Λ ν) (z₀ : C) (hz₀ : IsIdempotentElem z₀) (hne : z₀ ≠ 0)
    (hgen : ∀ y : C, z₀ * y = y → y ≠ 0 → ∃ c : C, y * c = z₀)
    (N : Submodule Tᵐᵒᵖ (rIdeal (wrapIdem Q Λ ν z₀))) :
    N = coevaluationTrace (cutIdem Q Λ ν) ↔
      IsSimpleModule Tᵐᵒᵖ (rIdeal (wrapIdem Q Λ ν z₀) ⧸ N) := by
  classical
  let := Fintype.ofFinite Ordered
  let := Fintype.ofFinite (CutLoading ν)
  let Φ := eraseWrap Q Λ ν hR
  have hΦ (z : C) : Φ (wrapIdem Q Λ ν z) = z := eraseWrap_appendRed_cyclotomicProjection Q Λ ν hR z
  have he : IsIdempotentElem (wrapIdem Q Λ ν z₀) := by
    rw [IsIdempotentElem, wrapIdem_mul, hz₀.eq]
  refine coevaluationTrace_eq_iff_isSimpleModule_of_corner he
    (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν) (val_mul_lastRedIdem Q Λ ν _)
    (lastRedIdem_mul_val Q Λ ν _) (cutIdem Q Λ ν) (isIdempotentElem_cutIdem Q Λ ν)
    Finset.univ (one_sub_lastRedIdem Q Λ ν) Φ (eraseWrap_cutIdem Q Λ ν hR) ?_ ?_ ?_ ?_ N
  · intro y hy h0
    let yc : TensorProductAlgebra.lastRedCorner (ℓ := 1) Q Λ ν :=
      ⟨y, (Subsemigroup.mem_corner_iff
        (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν)).2
        ⟨by rw [← hy, ← mul_assoc, ← mul_assoc,
              (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).eq],
         by rw [← hy, mul_assoc, (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).eq]⟩⟩
    obtain ⟨u, hu⟩ := appendRed_surjective (ℓ := 1) Q Λ ν yc
    obtain ⟨z, rfl⟩ := SingleRed.cyclotomicProjection_surjective Q Λ₀ ν u
    have hy' : y = wrapIdem Q Λ ν z := (congrArg Subtype.val hu).symm
    rw [hy', hΦ] at h0
    rw [hy', h0, wrapIdem, map_zero, map_zero]
    rfl
  · intro z
    exact ⟨wrapIdem Q Λ ν z, hΦ z⟩
  · intro y hy hy0
    rw [hΦ] at hy ⊢
    exact hgen y hy hy0
  · rw [hΦ]
    exact hne

end Categorification.Stendhal.TwoRedErase
