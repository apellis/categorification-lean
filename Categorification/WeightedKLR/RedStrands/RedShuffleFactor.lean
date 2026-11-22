/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstReach
import Categorification.WeightedKLR.RedStrands.QuotientBasis
import Categorification.TypeA.GapSort

set_option backward.isDefEq.respectTransparency false

/-!
# Factoring through the red-first idempotent by a red/black shuffle

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.30. For a red-ordered loading `s`, let `θ_s` be the diagram from the red-first
loading `t_s` (the red strands of `s` moved to the left, keeping the order of the black strands)
to `s` with no black/black crossings. By Proposition 4.16 every diagram from a red-first
loading to `s` can be drawn with all red/black crossings above all black/black crossings, so
every element `x` of `e(s) T^λ e⁰` factors as `θ_s m` with `m ∈ e⁰ T^λ e⁰`.

## Main results

* `redShufflePerm`: the permutation `τ_s` sorting the red strands of `s` to the left.
* `redShuffle`: the element `θ_s ∈ e(s) T^λ e(t_s)`.
* `exists_eq_redShuffle_mul`: every `x ∈ e(s) T^λ e⁰` is `θ_s m` with `m ∈ e⁰ T^λ e⁰`.
-/

noncomputable section

namespace Categorification.Stendhal

open Equiv KLR TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

section Shuffle

/-- The sorting key putting red strands before black strands and keeping the order inside
each colour class. -/
def redShuffleKey (s : Seq μ) (a : Fin m) : ℕ :=
  if (s.lbl a).isRight then a.val else a.val + m

theorem redShuffleKey_injective (s : Seq μ) : Function.Injective (redShuffleKey s) := by
  intro a b h
  unfold redShuffleKey at h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  split_ifs at h <;> omega

/-- The permutation `τ_s` moving the red strands of `s` to the left, keeping the relative order
of the red strands and of the black strands. -/
def redShufflePerm (s : Seq μ) : Perm (Fin m) :=
  (exists_perm_lt_iff _ (redShuffleKey_injective s)).choose

theorem redShufflePerm_lt_iff (s : Seq μ) (x y : Fin m) :
    redShufflePerm s x < redShufflePerm s y ↔ redShuffleKey s x < redShuffleKey s y :=
  (exists_perm_lt_iff _ (redShuffleKey_injective s)).choose_spec x y

theorem redShuffleKey_red {s : Seq μ} {a : Fin m} (h : (s.lbl a).isRight) :
    redShuffleKey s a = a.val := by
  simp [redShuffleKey, h]

theorem redShuffleKey_black {s : Seq μ} {a : Fin m} (h : (s.lbl a).isLeft) :
    redShuffleKey s a = a.val + m := by
  cases hs : s.lbl a with
  | inl _ => simp [redShuffleKey, hs]
  | inr _ => rw [hs] at h; simp at h

/-- The red-first loading `t_s = τ_s • s`. -/
theorem isRedFirst_redShuffle (s : Seq μ) : IsRedFirst (redShufflePerm s • s) := by
  intro a b ha hb
  obtain ⟨A, rfl⟩ := (redShufflePerm s).surjective a
  obtain ⟨B, rfl⟩ := (redShufflePerm s).surjective b
  change (s.lbl ((redShufflePerm s).symm (redShufflePerm s A))).isLeft at ha
  change (s.lbl ((redShufflePerm s).symm (redShufflePerm s B))).isRight at hb
  rw [Equiv.symm_apply_apply] at ha hb
  rw [redShufflePerm_lt_iff, redShuffleKey_red hb, redShuffleKey_black ha]
  have := B.isLt
  omega

theorem isRedOrdered_redShuffle {s : Seq μ} (hs : IsRedOrdered s) :
    IsRedOrdered (redShufflePerm s • s) := by
  intro a b r r' hab ha hb
  obtain ⟨A, rfl⟩ := (redShufflePerm s).surjective a
  obtain ⟨B, rfl⟩ := (redShufflePerm s).surjective b
  change s.lbl ((redShufflePerm s).symm (redShufflePerm s A)) = _ at ha
  change s.lbl ((redShufflePerm s).symm (redShufflePerm s B)) = _ at hb
  rw [Equiv.symm_apply_apply] at ha hb
  rw [redShufflePerm_lt_iff, redShuffleKey_red (by rw [ha]; rfl),
    redShuffleKey_red (by rw [hb]; rfl)] at hab
  exact hs A B r r' (Fin.lt_def.2 hab) ha hb

/-- The crossing condition of `length_eq_add_of_cross` for `τ_s` and a permutation `w` with
`w • t = s` and `t` red-first: `τ_s` only uncrosses a red strand from a black strand on its
left, and such a pair is already in this order in `t`. -/
theorem redShuffle_cross (s t : Seq μ) (ht : IsRedFirst t) (w : Perm (Fin m))
    (hw : w • t = s) :
    ∀ X Y, Y < X → redShufflePerm s X < redShufflePerm s Y → w⁻¹ X < w⁻¹ Y := by
  intro X Y hYX hτ
  rw [redShufflePerm_lt_iff] at hτ
  have hl : ∀ Z, s.lbl Z = t.lbl (w⁻¹ Z) := fun Z => by rw [← hw]; rfl
  cases hX : s.lbl X with
  | inl i =>
    rw [redShuffleKey_black (by rw [hX]; rfl)] at hτ
    cases hY : s.lbl Y with
    | inl j =>
      rw [redShuffleKey_black (by rw [hY]; rfl)] at hτ
      exact absurd (Fin.lt_def.2 (by omega)) (lt_asymm hYX)
    | inr r =>
      rw [redShuffleKey_red (by rw [hY]; rfl)] at hτ
      have := Y.isLt
      omega
  | inr r =>
    cases hY : s.lbl Y with
    | inl j =>
      exact ht _ _ (by rw [← hl, hY]; rfl) (by rw [← hl, hX]; rfl)
    | inr r' =>
      rw [redShuffleKey_red (by rw [hX]; rfl), redShuffleKey_red (by rw [hY]; rfl)] at hτ
      exact absurd (Fin.lt_def.2 hτ) (lt_asymm hYX)

open Classical in
/-- Reduced words adapted to `s`: when `w` satisfies the crossing condition for `τ_s`, the word of
`w` is a reduced word of `τ_s⁻¹` followed by one of `τ_s w`. -/
def redShuffleWord (s : Seq μ) (w : Perm (Fin m)) : List ℕ :=
  if ∀ X Y, Y < X → redShufflePerm s X < redShufflePerm s Y → w⁻¹ X < w⁻¹ Y then
    canWord m (redShufflePerm s)⁻¹ ++ canWord m (redShufflePerm s * w)
  else canWord m w

theorem redShuffleWord_spec (s : Seq μ) (w : Perm (Fin m)) :
    IsReduced m (redShuffleWord s w) ∧ wordProd m (redShuffleWord s w) = w := by
  unfold redShuffleWord
  split_ifs with h
  · have hw : wordProd m (canWord m (redShufflePerm s)⁻¹ ++ canWord m (redShufflePerm s * w)) =
        w := by
      rw [wordProd_append, wordProd_canWord, wordProd_canWord, ← mul_assoc, inv_mul_cancel,
        one_mul]
    refine ⟨IsReduced.append_of_length_eq (isReduced_canWord _ _) (isReduced_canWord _ _) ?_,
      hw⟩
    rw [hw, wordProd_canWord, wordProd_canWord, length_inv]
    exact length_eq_add_of_cross w _ h
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

end Shuffle

section Factor

open KLRAlgebra

variable [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin ℓ → I →₀ ℕ)

/-- Composing two diagrams through a middle idempotent in the KLR algebra. -/
theorem KLRAlgebra.e_ψw_e_mul_e_gen (α β : List ℕ) (p : MvPolynomial (Fin m) k)
    (s t' t : Seq μ) (h₁ : (wordProd m α)⁻¹ • s = t')
    (h₂ : (wordProd m β)⁻¹ • t' = t) :
    (KLRAlgebra.e s * ψw α * KLRAlgebra.e t' *
        (KLRAlgebra.e t' * (ψw β * pol p) * KLRAlgebra.e t) :
        KLRAlgebra k (stendhalQ Q Λ) μ) = ψw (α ++ β) * pol p * KLRAlgebra.e t := by
  have hg : (KLRAlgebra.e t' * (ψw β * pol p * KLRAlgebra.e t) :
      KLRAlgebra k (stendhalQ Q Λ) μ) = ψw β * pol p * KLRAlgebra.e t := by
    rw [e_mul_gen, ite_eq_left_of_eq_true _ _ (eq_true h₂)]
  rw [mul_assoc (KLRAlgebra.e t') (ψw β * pol p), hg, e_mul_ψw, h₁, mul_assoc (ψw α),
    KLRAlgebra.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl), mul_assoc (ψw α), hg,
    ψw_append]
  simp only [mul_assoc]

/-- The element `e(i) y e(j)` of `T̃^λ`, for red-ordered `i` and `j`. -/
def StendhalAlgebra.cut (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (y : StendhalAlgebraAllOrders k Q Λ ν) : StendhalAlgebra k Q Λ ν :=
  ⟨StendhalAlgebraAllOrders.e i * y * StendhalAlgebraAllOrders.e j, by
    classical
    rw [Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem]
    constructor
    · rw [← mul_assoc, ← mul_assoc, StendhalAlgebraAllOrders.redOrderedIdem_mul_e,
        ite_eq_left_of_eq_true _ _ (eq_true hi)]
    · rw [mul_assoc, StendhalAlgebraAllOrders.e_mul_redOrderedIdem,
        ite_eq_left_of_eq_true _ _ (eq_true hj)]⟩

theorem StendhalAlgebra.e_mul_cut (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (y : StendhalAlgebraAllOrders k Q Λ ν) :
    StendhalAlgebra.e i hi * StendhalAlgebra.cut Q Λ i j hi hj y =
      StendhalAlgebra.cut Q Λ i j hi hj y := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e i * (StendhalAlgebraAllOrders.e i * y *
    StendhalAlgebraAllOrders.e j) = _
  rw [← mul_assoc, ← mul_assoc, StendhalAlgebraAllOrders.e_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

theorem StendhalAlgebra.cut_mul_e (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (y : StendhalAlgebraAllOrders k Q Λ ν) :
    StendhalAlgebra.cut Q Λ i j hi hj y * StendhalAlgebra.e j hj =
      StendhalAlgebra.cut Q Λ i j hi hj y := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e i * y * StendhalAlgebraAllOrders.e j *
    StendhalAlgebraAllOrders.e j = _
  rw [mul_assoc _ (StendhalAlgebraAllOrders.e j), StendhalAlgebraAllOrders.e_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  rfl

open Classical in
/-- `e(t) e⁰` is `e(t)` for red-first `t` and zero otherwise. -/
theorem redLoadingIdem_mul_redFirstIdem_eq (t : Seq μ) (ht : IsRedOrdered t) :
    redLoadingIdem Q Λ ν t ht * redFirstIdem Q Λ ν =
      if IsRedFirst t then redLoadingIdem Q Λ ν t ht else 0 := by
  split_ifs with htf
  · exact redLoadingIdem_mul_redFirstIdem Q Λ ν t ht htf
  unfold redLoadingIdem redFirstIdem redFirstStendhalIdem
  rw [← map_mul, Finset.mul_sum, Finset.sum_eq_zero, map_zero]
  intro u _
  rw [StendhalAlgebra.e_mul_e, ite_eq_right_of_eq_false _ _ 
    (eq_false (fun (h : t = ↑u) => htf (h ▸ u.2.2)))]

open Classical in
/-- `e⁰ e(t)` is `e(t)` for red-first `t` and zero otherwise. -/
theorem redFirstIdem_mul_redLoadingIdem_eq (t : Seq μ) (ht : IsRedOrdered t) :
    redFirstIdem Q Λ ν * redLoadingIdem Q Λ ν t ht =
      if IsRedFirst t then redLoadingIdem Q Λ ν t ht else 0 := by
  unfold redLoadingIdem redFirstIdem redFirstStendhalIdem
  rw [← map_mul, Finset.sum_mul]
  split_ifs with htf
  · rw [Finset.sum_eq_single_of_mem (⟨t, ht, htf⟩ : RedFirstLoading (ℓ := ℓ) ν)
      (Finset.mem_univ _), StendhalAlgebra.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    intro u _ hne
    rw [StendhalAlgebra.e_mul_e,
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => hne (Subtype.ext h)))]
  · rw [Finset.sum_eq_zero, map_zero]
    intro u _
    rw [StendhalAlgebra.e_mul_e, ite_eq_right_of_eq_false _ _ 
    (eq_false (fun (h : ↑u = t) => htf (h ▸ u.2.2)))]

/-- The red/black shuffle `θ_s` of `T̃^λ`: the diagram from `t_s = τ_s • s` to `s` with no
black/black crossings. -/
def redShuffleStendhal (s : Seq μ) (hs : IsRedOrdered s) : StendhalAlgebra k Q Λ ν :=
  StendhalAlgebra.cut Q Λ s (redShufflePerm s • s) hs (isRedOrdered_redShuffle hs)
    (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (canWord m (redShufflePerm s)⁻¹)))

/-- **The red/black shuffle** `θ_s ∈ e(s) T^λ e(t_s)` (Webster, arXiv:1309.3796v2, proof of
Proposition 5.30). -/
def redShuffle (s : Seq μ) (hs : IsRedOrdered s) : TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (redShuffleStendhal Q Λ s hs)

/-- A Stendhal term from a red-first loading to `s`, for the words adapted to `s`, is `θ_s`
followed by a diagram between red-first loadings. -/
theorem stendhalTerm_eq_redShuffle_mul (s : Seq μ) (hs : IsRedOrdered s)
    (b : {b // IsStendhalTerm (redShuffleWord s) b}) (htop : b.1.2.1 • b.1.1 = s)
    (htf : IsRedFirst b.1.1) :
    stendhalTerm Q Λ (fun w => (redShuffleWord_spec s w).2) b =
      redShuffleStendhal Q Λ s hs * StendhalAlgebra.cut Q Λ (redShufflePerm s • s) b.1.1
        (isRedOrdered_redShuffle hs) b.2.1
        (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (canWord m (redShufflePerm s * b.1.2.1)) *
          pol (MvPolynomial.monomial b.1.2.2 1))) := by
  have hcross := redShuffle_cross s b.1.1 htf b.1.2.1 htop
  apply Subtype.ext
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.stdElt (redShuffleWord s) b.1) =
    StendhalAlgebraAllOrders.e s *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (canWord m (redShufflePerm s)⁻¹)) *
      StendhalAlgebraAllOrders.e (redShufflePerm s • s) *
      (StendhalAlgebraAllOrders.e (redShufflePerm s • s) *
        StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (canWord m (redShufflePerm s * b.1.2.1)) *
          pol (MvPolynomial.monomial b.1.2.2 1)) * StendhalAlgebraAllOrders.e b.1.1)
  simp only [StendhalAlgebraAllOrders.e, ← map_mul]
  rw [KLRAlgebra.e_ψw_e_mul_e_gen Q Λ _ _ _ s _ b.1.1 (by rw [wordProd_canWord, inv_inv])
    (by rw [wordProd_canWord, mul_inv_rev, mul_smul, inv_smul_smul,
      inv_smul_eq_iff.mpr htop.symm])]
  unfold KLRAlgebra.stdElt redShuffleWord
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcross)]

/-- `e(i) y e(j)` lies in the red-first corner when `i` and `j` are red-first. -/
theorem redFirstIdem_mul_cut_mul (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (hif : IsRedFirst i) (hjf : IsRedFirst j) (y : StendhalAlgebraAllOrders k Q Λ ν) :
    redFirstIdem Q Λ ν * TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.cut Q Λ i j hi hj y) *
        redFirstIdem Q Λ ν =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.cut Q Λ i j hi hj y) := by
  classical
  have hl : redFirstIdem Q Λ ν * redLoadingIdem Q Λ ν i hi = redLoadingIdem Q Λ ν i hi := by
    rw [redFirstIdem_mul_redLoadingIdem_eq, ite_eq_left_of_eq_true _ _ (eq_true hif)]
  have hr : redLoadingIdem Q Λ ν j hj * redFirstIdem Q Λ ν = redLoadingIdem Q Λ ν j hj := by
    rw [redLoadingIdem_mul_redFirstIdem_eq, ite_eq_left_of_eq_true _ _ (eq_true hjf)]
  rw [← StendhalAlgebra.e_mul_cut, ← StendhalAlgebra.cut_mul_e, map_mul, map_mul]
  change redFirstIdem Q Λ ν * (redLoadingIdem Q Λ ν i hi * (_ * redLoadingIdem Q Λ ν j hj)) *
    redFirstIdem Q Λ ν = redLoadingIdem Q Λ ν i hi * (_ * redLoadingIdem Q Λ ν j hj)
  rw [← mul_assoc (redFirstIdem Q Λ ν), hl, mul_assoc, mul_assoc, hr]

/-- **Factorization through the red-first idempotent** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.30). Every `x ∈ e(s) T^λ e⁰` is `θ_s m` with `m ∈ e⁰ T^λ e⁰`. -/
theorem exists_eq_redShuffle_mul (s : Seq μ) (hs : IsRedOrdered s)
    (x : TensorProductAlgebra k Q Λ ν) (h₁ : redLoadingIdem Q Λ ν s hs * x = x)
    (h₂ : x * redFirstIdem Q Λ ν = x) :
    ∃ y, x = redShuffle Q Λ s hs * (redFirstIdem Q Λ ν * y * redFirstIdem Q Λ ν) := by
  classical
  let e₀ := redFirstIdem Q Λ ν
  let es := redLoadingIdem Q Λ ν s hs
  let P : TensorProductAlgebra k Q Λ ν →ₗ[k] TensorProductAlgebra k Q Λ ν :=
    (LinearMap.mulLeft k es).comp (LinearMap.mulRight k e₀)
  let L : TensorProductAlgebra k Q Λ ν →ₗ[k] TensorProductAlgebra k Q Λ ν :=
    (LinearMap.mulLeft k (redShuffle Q Λ s hs)).comp
      ((LinearMap.mulLeft k e₀).comp (LinearMap.mulRight k e₀))
  suffices hP : ∀ z, P z ∈ LinearMap.range L by
    obtain ⟨y, hy⟩ := hP x
    refine ⟨y, ?_⟩
    have hx : P x = x := by
      change es * (x * e₀) = x
      rw [h₂, h₁]
    rw [← hx, ← hy]
    simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, e₀, mul_assoc]
  intro z
  have hz : z ∈ Submodule.span k (Set.range (tensorProductTerm (fun w => redShuffleWord_spec s w)
      Q Λ)) := by
    rw [span_tensorProductTerm]
    trivial
  induction hz using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  | mem a ha =>
    obtain ⟨b, rfl⟩ := ha
    change es * (TensorProductAlgebra.mk Q Λ ν
      (stendhalTerm Q Λ (fun w => (redShuffleWord_spec s w).2) b) * e₀) ∈ _
    set T := stendhalTerm Q Λ (fun w => (redShuffleWord_spec s w).2) b
    have hT : T = T * StendhalAlgebra.e b.1.1 b.2.1 := by
      rw [stendhalTerm_mul_e, ite_eq_left_of_eq_true _ _ (eq_self _)]
    have hTe : es * TensorProductAlgebra.mk Q Λ ν T =
        if b.1.2.1 • b.1.1 = s then TensorProductAlgebra.mk Q Λ ν T else 0 := by
      change TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) *
        TensorProductAlgebra.mk Q Λ ν T = _
      rw [← map_mul, e_mul_stendhalTerm]
      split_ifs
      · rfl
      · exact map_zero _
    rw [← mul_assoc, hTe]
    by_cases htop : b.1.2.1 • b.1.1 = s
    swap
    · rw [ite_eq_right_of_eq_false _ _ (eq_false htop), zero_mul]
      exact zero_mem _
    rw [ite_eq_left_of_eq_true _ _ (eq_true htop), hT, map_mul]
    change TensorProductAlgebra.mk Q Λ ν T * redLoadingIdem Q Λ ν b.1.1 b.2.1 * e₀ ∈ _
    rw [mul_assoc, redLoadingIdem_mul_redFirstIdem_eq]
    by_cases htf : IsRedFirst b.1.1
    swap
    · rw [ite_eq_right_of_eq_false _ _ (eq_false htf), mul_zero]
      exact zero_mem _
    rw [ite_eq_left_of_eq_true _ _ (eq_true htf), ← map_mul, ← hT,
      show T = _ from stendhalTerm_eq_redShuffle_mul Q Λ s hs b htop htf, map_mul]
    set y := TensorProductAlgebra.mk Q Λ ν
      (StendhalAlgebra.cut Q Λ (redShufflePerm s • s) b.1.1
      (isRedOrdered_redShuffle hs) b.2.1 (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (ψw (canWord m (redShufflePerm s * b.1.2.1)) * pol (MvPolynomial.monomial b.1.2.2 1))))
    refine ⟨y, ?_⟩
    simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, e₀, y]
    rw [← mul_assoc (redFirstIdem Q Λ ν),
      redFirstIdem_mul_cut_mul Q Λ _ _ _ _ (isRedFirst_redShuffle s) htf]
    rfl

end Factor

end Categorification.Stendhal
