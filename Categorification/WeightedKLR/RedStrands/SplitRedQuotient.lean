/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.GapSort
import Categorification.WeightedKLR.RedStrands.SplitRedInjective

/-!
# Splitting a red strand: violated diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. A loading of `λ'` in which the red strands `c` and `c + 1` are adjacent is the
split loading of a loading of `λ`. A diagram between split loadings that passes through a
violated loading factors through a violated split loading: the strands between the two red
strands are slid out of the gap, which is the effect of the bigon and triangle relations
(Webster, Lemma 4.10) in the proof of Proposition 4.21.

## Main results

* `exists_splitLoading_eq` : a loading with adjacent red strands `c`, `c + 1` is split.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ} (c : Fin ℓ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-! ### Merging adjacent red strands -/

/-- A left inverse of `splitColor c`. -/
def mergeColor : I ⊕ Fin (ℓ + 1) → I ⊕ Fin ℓ :=
  haveI : Nonempty (I ⊕ Fin ℓ) := ⟨.inr c⟩
  Function.invFun (splitColor c)

@[simp] theorem mergeColor_splitColor (x : I ⊕ Fin ℓ) : mergeColor c (splitColor c x) = x :=
  haveI : Nonempty (I ⊕ Fin ℓ) := ⟨.inr c⟩
  Function.leftInverse_invFun (splitColor_injective c) x

theorem splitColor_mergeColor {y : I ⊕ Fin (ℓ + 1)} (hy : y ≠ .inr c.succ) :
    splitColor c (mergeColor c y) = y := by
  rcases y with i | r
  · exact congrArg (splitColor c) (mergeColor_splitColor c (.inl i))
  · obtain ⟨r', hr'⟩ := Fin.exists_succAbove_eq (x := r) (y := c.succ)
      (fun e => hy (by rw [e]))
    rw [← hr']
    exact congrArg (splitColor c) (mergeColor_splitColor c (.inr r'))

variable [DecidableEq I]

/-- The label of the new red strand of a loading of `λ'` occurs at one position only. -/
theorem ne_new_of_ne {t : Seq μ'} {a b : Fin (Multiset.card μ')} (hab : a ≠ b)
    (hb : t.lbl b = .inr c.succ) : t.lbl a ≠ .inr c.succ := fun ha =>
  hab (eq_of_lbl_eq_inr (ν := ν) ha hb)

/-- The positions of the old strands, given the position `b` of the red strand `c`. -/
private def oldPos (b : Fin m) (a : Fin m) : Fin (Multiset.card μ') :=
  (posEquiv ℓ ν).symm (b.succ.succAbove a)

omit [DecidableEq I] in
private theorem oldPos_val (b a : Fin m) :
    (oldPos (ν := ν) b a : ℕ) = if (a : ℕ) ≤ b then (a : ℕ) else (a : ℕ) + 1 := by
  simp only [oldPos, finCongr_symm, finCongr_apply, Fin.val_cast, Fin.succAbove]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.castSucc_lt_succ_iff.1 h1) h2
  · exact absurd (Fin.castSucc_lt_succ_iff.2 h2) h1
  · simp

omit [DecidableEq I] in
private theorem map_univ_oldPos {α : Type*} (b : Fin m) (g : Fin (Multiset.card μ') → α) :
    Finset.univ.val.map g = Finset.univ.val.map (fun a => g (oldPos (ν := ν) b a)) +
      {g ⟨b + 1, by have := card_split ℓ ν; omega⟩} := by
  have hu := congrArg Finset.val (Finset.map_univ_equiv (posEquiv ℓ ν).symm)
  rw [show (Finset.univ : Finset (Fin (Multiset.card μ'))).val =
    Finset.univ.val.map (posEquiv ℓ ν).symm from hu.symm, Multiset.map_map,
    Fin.univ_succAbove m b.succ]
  change ((b.succ ::ₘ (Finset.univ.map (Fin.succAboveEmb _)).val).map _) = _
  rw [Multiset.map_cons, ← Multiset.singleton_add, add_comm]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Fin.coe_succAboveEmb]
  rfl

/-- A loading of `λ'` with the red strand `c + 1` just right of the red strand `c` is the
split loading of a loading of `λ`. -/
theorem exists_splitLoading_eq (t : Seq μ') (b : Fin m)
    (hb : t.lbl ⟨b, by have := card_split ℓ ν; omega⟩ = .inr c.castSucc)
    (hb' : t.lbl ⟨b + 1, by have := card_split ℓ ν; omega⟩ = .inr c.succ) :
    ∃ t₀ : Seq μ, splitLoading c t₀ = t ∧ redPos c t₀ = b := by
  have hcard := card_split ℓ ν
  set B' : Fin (Multiset.card μ') := ⟨b + 1, by omega⟩
  have hne : ∀ a : Fin m, t.lbl (oldPos b a) ≠ .inr c.succ := fun a =>
    ne_new_of_ne c (b := B') (fun e => by
      have := congrArg Fin.val e; rw [oldPos_val] at this; simp only [B'] at this
      split_ifs at this <;> omega) hb'
  let f : Fin m → I ⊕ Fin ℓ := fun a => mergeColor c (t.lbl (oldPos b a))
  have hf : Finset.univ.val.map f = μ := by
    apply Multiset.map_injective (splitColor_injective c)
    have h1 : (Finset.univ.val.map f).map (splitColor c) =
        Finset.univ.val.map fun a => t.lbl (oldPos b a) := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun a _ => splitColor_mergeColor c (hne a)
    rw [h1]
    apply (add_left_inj ({.inr c.succ} : Multiset (I ⊕ Fin (ℓ + 1)))).1
    rw [stendhalWeight_split]
    -- the positions of `μ'` are the old positions and `b + 1`
    refine Eq.trans ?_ t.2
    rw [map_univ_oldPos b t.1]
    exact congrArg₂ (· + ·) rfl (congrArg _ hb'.symm)
  let t₀ : Seq μ := ⟨f, hf⟩
  have hred : redPos c t₀ = b := by
    refine (eq_redPos c ?_).symm
    change mergeColor c (t.lbl (oldPos b b)) = _
    have : oldPos (ν := ν) b b = ⟨b, by omega⟩ := Fin.ext (by rw [oldPos_val]; simp)
    rw [this, hb, ← succAbove_self, ← splitColor_inr, mergeColor_splitColor]
  refine ⟨t₀, ?_, hred⟩
  apply Subtype.ext
  funext x
  change (splitLoading c t₀).lbl x = t.lbl x
  have hr : (redPos c t₀ : ℕ) = b := congrArg Fin.val hred
  rw [splitLoading_lbl]
  split_ifs with h1 h2
  · change splitColor c (mergeColor c (t.lbl (oldPos b ⟨x, _⟩))) = _
    rw [splitColor_mergeColor c (hne _)]
    congr 1; apply Fin.ext; rw [oldPos_val]; simp only; split_ifs <;> omega
  · rw [show x = B' from Fin.ext (by simp only [B']; omega), hb']
  · change splitColor c (mergeColor c (t.lbl (oldPos b ⟨x - 1, _⟩))) = _
    rw [splitColor_mergeColor c (hne _)]
    congr 1; apply Fin.ext; rw [oldPos_val]; simp only; split_ifs <;> omega

/-! ### Cutting a diagram from a split loading at a split loading -/

local notation "m'" => Multiset.card μ'

/-- The position of the red strand `c` in a split loading. -/
private def oldRedPos (s : Seq μ) : Fin m' := splitPos c s (redPos c s)

private theorem oldRedPos_val (s : Seq μ) : (oldRedPos c s : ℕ) = redPos c s := by
  rw [oldRedPos, splitPos_val]; simp

private theorem splitLoading_lbl_oldRedPos (s : Seq μ) :
    (splitLoading c s).lbl (oldRedPos c s) = .inr c.castSucc := by
  rw [oldRedPos, splitLoading_lbl_splitPos, lbl_redPos, splitColor_inr, succAbove_self]

private theorem newPos_val_eq (s : Seq μ) : (newPos c s : ℕ) = oldRedPos c s + 1 := by
  rw [newPos_val, oldRedPos_val]

open Classical in
/-- The permutation sorting the strands of a diagram out of the gap between the red strands
`c` and `c + 1` at its top, when that gap is in the right order. -/
def cutPerm (s : Seq μ) (w : Perm (Fin m')) : Perm (Fin m') :=
  if h : w (oldRedPos c s) < w (newPos c s) then
    (exists_gapSort w _ _ (newPos_val_eq c s) h).choose
  else 1

theorem length_cutPerm (s : Seq μ) (w : Perm (Fin m')) :
    length m' w = length m' (cutPerm c s w) + length m' (cutPerm c s w * w) := by
  unfold cutPerm
  split_ifs with h
  · exact (exists_gapSort w _ _ (newPos_val_eq c s) h).choose_spec.2.1
  · simp [length_one]

/-- The reduced word of a diagram from a split loading that first sorts the gap. -/
def cutWord (s : Seq μ) (w : Perm (Fin m')) : List ℕ :=
  canWord m' (cutPerm c s w)⁻¹ ++ canWord m' (cutPerm c s w * w)

theorem cutWord_spec (s : Seq μ) (w : Perm (Fin m')) :
    IsReduced m' (cutWord c s w) ∧ wordProd m' (cutWord c s w) = w := by
  have hp : wordProd m' (cutWord c s w) = w := by
    rw [cutWord, wordProd_append, wordProd_canWord, wordProd_canWord, ← mul_assoc,
      inv_mul_cancel, one_mul]
  refine ⟨IsReduced.append_of_length_eq (isReduced_canWord _ _) (isReduced_canWord _ _) ?_, hp⟩
  rw [← cutWord, hp, wordProd_canWord, wordProd_canWord, length_inv]
  exact length_cutPerm c s w

/-- After sorting the gap, a red-ordered violated top of a diagram from a split loading becomes
a red-ordered violated split loading. -/
theorem exists_cut_splitLoading (s : Seq μ) (w : Perm (Fin m'))
    (ho : IsRedOrdered (w • splitLoading c s)) (hV : IsViolated (w • splitLoading c s)) :
    ∃ t : Seq μ, IsRedOrdered t ∧ IsViolated t ∧
      splitLoading c t = (cutPerm c s w * w) • splitLoading c s := by
  set v := w • splitLoading c s with hvdef
  have hP : v.lbl (w (oldRedPos c s)) = .inr c.castSucc := by
    change (splitLoading c s).lbl (w.symm (w (oldRedPos c s))) = _
    rw [Equiv.symm_apply_apply]; exact splitLoading_lbl_oldRedPos c s
  have hP' : v.lbl (w (newPos c s)) = .inr c.succ := by
    change (splitLoading c s).lbl (w.symm (w (newPos c s))) = _
    rw [Equiv.symm_apply_apply]; exact splitLoading_lbl_newPos c s
  have hlt : w (oldRedPos c s) < w (newPos c s) := by
    rcases lt_trichotomy (w (oldRedPos c s)) (w (newPos c s)) with h | h | h
    · exact h
    · exact absurd (w.injective h) (fun e => by
        have := congrArg Fin.val e; rw [newPos_val_eq] at this; omega)
    · exact absurd (ho _ _ _ _ h hP' hP) (fun h' => by
        rw [Fin.lt_def] at h'; simp at h')
  obtain ⟨hadj, -, hord, h0⟩ := (exists_gapSort w _ _ (newPos_val_eq c s) hlt).choose_spec
  have hτ : cutPerm c s w = (exists_gapSort w _ _ (newPos_val_eq c s) hlt).choose := by
    unfold cutPerm; simp only [hlt, ↓reduceDIte]
  set τ := cutPerm c s w
  rw [← hτ] at hadj hord h0
  have htv : ∀ X, ((τ * w) • splitLoading c s).lbl (τ X) = v.lbl X := by
    intro X
    change (splitLoading c s).lbl ((τ * w).symm (τ X)) = (splitLoading c s).lbl (w.symm X)
    congr 1
    simp [Equiv.Perm.mul_def]
  -- no red strand lies strictly inside the gap
  have hout : ∀ X (r : Fin (ℓ + 1)), v.lbl X = .inr r → X ≤ w (oldRedPos c s) ∨ w (newPos c s) ≤ X := by
    intro X r hX
    by_contra hc
    push Not at hc
    have h1 := ho _ _ _ _ hc.1 hP hX
    have h2 := ho _ _ _ _ hc.2 hX hP'
    rw [Fin.lt_def] at h1 h2
    simp at h1 h2
    omega
  have hcard := card_split ℓ ν
  have hbm : (τ (w (oldRedPos c s)) : ℕ) < m := by have := (τ (w (newPos c s))).isLt; omega
  obtain ⟨t, ht, -⟩ := exists_splitLoading_eq c ((τ * w) • splitLoading c s) ⟨_, hbm⟩
    (by rw [show (⟨(τ (w (oldRedPos c s)) : ℕ), _⟩ : Fin m') = τ (w (oldRedPos c s)) from rfl, htv, hP])
    (by rw [show (⟨(τ (w (oldRedPos c s)) : ℕ) + 1, _⟩ : Fin m') = τ (w (newPos c s)) from Fin.ext hadj, htv, hP'])
  refine ⟨t, ?_, ?_, ht⟩
  · rw [← isRedOrdered_splitLoading_iff c, ht]
    intro X Y r r' hXY hX hY
    obtain ⟨X, rfl⟩ := τ.surjective X
    obtain ⟨Y, rfl⟩ := τ.surjective Y
    rw [htv] at hX hY
    exact ho _ _ _ _ ((hord X Y (hout X r hX) (hout Y r' hY)).1 hXY) hX hY
  · rw [← isViolated_splitLoading_iff c, ht]
    obtain ⟨hm, hl⟩ := hV
    have hpos : (0 : ℕ) < w (oldRedPos c s) := by
      rcases Nat.eq_zero_or_pos (w (oldRedPos c s) : ℕ) with h | h
      · have : w (oldRedPos c s) = ⟨0, hm⟩ := Fin.ext h
        rw [this] at hP; rw [hP] at hl; cases hl
      · exact h
    refine ⟨hm, ?_⟩
    rw [← h0 hm hpos, htv]
    exact hl

/-! ### The violating ideal in the split corner -/

section Violated

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ' : Fin (ℓ + 1) → I →₀ ℕ)

local notation "π'" => StendhalAlgebraAllOrders.ofKLR k Q Λ' ν
local notation "P'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν

/-- The element `P' z P'` of `T̃^{λ'}`, for `P'` the unit of `T̃^{λ'}`. -/
private def cornerOf (z : StendhalAlgebraAllOrders k Q Λ' ν) : StendhalAlgebra k Q Λ' ν :=
  KLR.Corner.mk (P' * z * P') (by
    have hP := (StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem
      (k := k) (Q := Q) (Λ := Λ') (ν := ν)).eq
    have hP' : ∀ x, P' * (P' * x) = P' * x := fun x => by rw [← mul_assoc, hP]
    simp only [mul_assoc, hP', hP])

private theorem e_mul_redOrderedIdem_mul {j : Seq μ'} (hj : IsRedOrdered j)
    (y : StendhalAlgebraAllOrders k Q Λ' ν) :
    StendhalAlgebraAllOrders.e j * (P' * y) = StendhalAlgebraAllOrders.e j * y := by
  classical
  rw [← mul_assoc, StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  simp [hj]

private theorem redOrderedIdem_mul_e_mul {j : Seq μ'} (hj : IsRedOrdered j)
    (y : StendhalAlgebraAllOrders k Q Λ' ν) :
    P' * (StendhalAlgebraAllOrders.e j * y) = StendhalAlgebraAllOrders.e j * y := by
  classical
  rw [← mul_assoc, StendhalAlgebraAllOrders.redOrderedIdem_mul_e]
  simp [hj]

private theorem e_mul_e_mul (j : Seq μ') (y : StendhalAlgebraAllOrders k Q Λ' ν) :
    StendhalAlgebraAllOrders.e j * (StendhalAlgebraAllOrders.e j * y) =
      StendhalAlgebraAllOrders.e j * y := by
  rw [← mul_assoc, StendhalAlgebraAllOrders.e_mul_e]
  simp

/-- A generator `T b T b'` of the violating ideal of `T̃^{λ'}` (`mem_violatedIdeal_iff`), cut
between split loadings, is the split of an element of the violating ideal of `T̃^λ`: the word of
`b'` first sorts the strands out of the gap between the red strands `c` and `c + 1`
(`cutWord`), and the loading reached is a violated split loading (`exists_cut_splitLoading`). -/
private theorem exists_violated_split_generator (s₀ t₀ : Seq μ) (hs : IsRedOrdered s₀)
    (ht : IsRedOrdered t₀)
    (b b' : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) (cutWord c s₀) b})
    (hv : IsViolated b.1.1) (hb : b.1.1 = b'.1.2.1 • b'.1.1) :
    ∃ g ∈ StendhalAlgebra.violatedIdeal k Q (mergeWeights c Λ') ν,
      splitStendhalValue c Q Λ' ν g =
        StendhalAlgebra.e (splitLoading c t₀) ((isRedOrdered_splitLoading_iff c t₀).2 ht) *
          (stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b *
            stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b') *
          StendhalAlgebra.e (splitLoading c s₀) ((isRedOrdered_splitLoading_iff c s₀).2 hs) := by
  classical
  by_cases h1 : b'.1.1 = splitLoading c s₀
  swap
  · refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, mul_assoc, mul_assoc, stendhalTerm_mul_e]
    simp [h1]
  have ho : IsRedOrdered (b'.1.2.1 • splitLoading c s₀) := h1 ▸ b'.2.2.1
  have hV : IsViolated (b'.1.2.1 • splitLoading c s₀) := by rw [← h1, ← hb]; exact hv
  obtain ⟨t₁, ht₁, hv₁, hsplit⟩ := exists_cut_splitLoading c s₀ b'.1.2.1 ho hV
  have ht₁' := (isRedOrdered_splitLoading_iff c t₁).2 ht₁
  have hs₀' := (isRedOrdered_splitLoading_iff c s₀).2 hs
  have ht₀' := (isRedOrdered_splitLoading_iff c t₀).2 ht
  let X₀ : StendhalAlgebraAllOrders k Q Λ' ν :=
    π' (KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1)⁻¹))
  let Z₀ : StendhalAlgebraAllOrders k Q Λ' ν :=
    π' (KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1 * b'.1.2.1)) *
      KLRAlgebra.pol (MvPolynomial.monomial b'.1.2.2 1) * KLRAlgebra.e (splitLoading c s₀))
  have hcut : (stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b').val =
      X₀ * StendhalAlgebraAllOrders.e (splitLoading c t₁) * Z₀ := by
    have he : (KLRAlgebra.e (splitLoading c t₁) : KLRAlgebra k (stendhalQ Q Λ') μ') *
        (KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1 * b'.1.2.1)) *
          KLRAlgebra.pol (MvPolynomial.monomial b'.1.2.2 1) * KLRAlgebra.e (splitLoading c s₀)) =
        KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1 * b'.1.2.1)) *
          KLRAlgebra.pol (MvPolynomial.monomial b'.1.2.2 1) *
            KLRAlgebra.e (splitLoading c s₀) := by
      rw [KLRAlgebra.e_mul_gen, wordProd_canWord, hsplit, inv_smul_smul]
      simp
    rw [stendhalTerm_val, KLRAlgebra.stdElt, h1]
    change π' (KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1)⁻¹ ++
      canWord m' (cutPerm c s₀ b'.1.2.1 * b'.1.2.1)) * _ * _) = _
    change _ = π' (KLRAlgebra.ψw (canWord m' (cutPerm c s₀ b'.1.2.1)⁻¹)) *
      π' (KLRAlgebra.e (splitLoading c t₁)) * π' (KLRAlgebra.ψw
        (canWord m' (cutPerm c s₀ b'.1.2.1 * b'.1.2.1)) *
          KLRAlgebra.pol (MvPolynomial.monomial b'.1.2.2 1) * KLRAlgebra.e (splitLoading c s₀))
    rw [mul_assoc (π' _) (π' (KLRAlgebra.e _)), ← map_mul π' (KLRAlgebra.e _), he, ← map_mul,
      KLRAlgebra.ψw_append]
    simp only [mul_assoc]
  let y₁ := stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b * cornerOf Λ' X₀
  obtain ⟨g₁, hg₁⟩ := e_mul_mul_e_mem_range_splitStendhalValue c Λ' t₁ t₀ ht₁ ht y₁
  obtain ⟨g₂, hg₂⟩ := e_mul_mul_e_mem_range_splitStendhalValue c Λ' s₀ t₁ hs ht₁
    (cornerOf Λ' Z₀)
  refine ⟨g₁ * StendhalAlgebra.e t₁ ht₁ * g₂, TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨t₁, ht₁, hv₁, rfl⟩)), ?_⟩
  rw [map_mul, map_mul, hg₁, hg₂, splitStendhalValue_e]
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e (splitLoading c t₀) *
      ((stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b).val * (P' * X₀ * P')) *
      StendhalAlgebraAllOrders.e (splitLoading c t₁) * StendhalAlgebraAllOrders.e
        (splitLoading c t₁) * (StendhalAlgebraAllOrders.e (splitLoading c t₁) * (P' * Z₀ * P') *
      StendhalAlgebraAllOrders.e (splitLoading c s₀)) =
    StendhalAlgebraAllOrders.e (splitLoading c t₀) *
      ((stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b).val *
        (stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b').val) *
      StendhalAlgebraAllOrders.e (splitLoading c s₀)
  have hTb : ∀ y, (stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b).val * (P' * y) =
      (stendhalTerm Q Λ' (fun w => (cutWord_spec c s₀ w).2) b).val * y := fun y => by
    rw [← mul_assoc, KLR.Corner.val_mul_E]
  rw [hcut]
  simp only [mul_assoc, hTb, e_mul_redOrderedIdem_mul Λ' ht₁', redOrderedIdem_mul_e_mul Λ' ht₁',
    e_mul_e_mul]
  simp [StendhalAlgebraAllOrders.redOrderedIdem_mul_e, hs₀']

/-- **The violating ideal of `T̃^{λ'}`, cut between split loadings, is the split of the violating
ideal of `T̃^λ`** (Webster, arXiv:1309.3796v3, Proposition 4.21, proof). -/
theorem exists_violated_splitStendhalValue (s₀ t₀ : Seq μ) (hs : IsRedOrdered s₀)
    (ht : IsRedOrdered t₀) (x : StendhalAlgebra k Q Λ' ν)
    (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ' ν) :
    ∃ g ∈ StendhalAlgebra.violatedIdeal k Q (mergeWeights c Λ') ν,
      splitStendhalValue c Q Λ' ν g =
        StendhalAlgebra.e (splitLoading c t₀) ((isRedOrdered_splitLoading_iff c t₀).2 ht) * x *
          StendhalAlgebra.e (splitLoading c s₀) ((isRedOrdered_splitLoading_iff c s₀).2 hs) := by
  classical
  have h := (mem_violatedIdeal_iff (Q := Q) (Λ := Λ') (cutWord_spec c s₀) x).1 hx
  clear hx
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, b', hv, hb, rfl⟩ := hx
    exact exists_violated_split_generator c Λ' s₀ t₀ hs ht b b' hv hb
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, mul_zero, zero_mul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, heu⟩ := hx
    obtain ⟨v, hv, hev⟩ := hy
    exact ⟨u + v, add_mem hu hv, by rw [map_add, heu, hev, mul_add, add_mul]⟩
  | smul a x _ hx =>
    obtain ⟨g, hg, he⟩ := hx
    refine ⟨a • g, ?_, ?_⟩
    · rw [Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hg
    · rw [splitStendhalValue_smul, he, mul_smul_comm, smul_mul_assoc]

open Classical in
/-- The unit of `T̃^λ` is the sum of the idempotents `e(s)`, `s` red-ordered. -/
theorem stendhal_one_eq_sum :
    (1 : StendhalAlgebra k Q (mergeWeights c Λ') ν) =
      ∑ s : {s : Seq μ // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 := by
  apply KLR.Corner.ext
  rw [KLR.Corner.val_sum]
  change StendhalAlgebraAllOrders.redOrderedIdem k Q (mergeWeights c Λ') ν =
    ∑ s : {s : Seq μ // IsRedOrdered s}, StendhalAlgebraAllOrders.e s.1
  rw [StendhalAlgebraAllOrders.redOrderedIdem]
  exact Finset.sum_subtype _ (p := fun s : Seq μ => IsRedOrdered s) (fun x => by simp) _

open Classical in
/-- The split idempotent: the image of the unit of `T̃^λ`, the sum of the idempotents of the split
loadings of red-ordered loadings. -/
theorem splitStendhalValue_one :
    splitStendhalValue c Q Λ' ν 1 = ∑ s : {s : Seq μ // IsRedOrdered s},
      StendhalAlgebra.e (splitLoading c s.1) ((isRedOrdered_splitLoading_iff c s.1).2 s.2) := by
  rw [stendhal_one_eq_sum c Λ', map_sum]
  exact Finset.sum_congr rfl fun s _ => splitStendhalValue_e c Λ' s.1 s.2

/-- The violating ideal of `T̃^{λ'}` in the corner of the split idempotent is the split of the
violating ideal of `T̃^λ` (Webster, arXiv:1309.3796v3, Proposition 4.21, proof). -/
theorem exists_violated_split (x : StendhalAlgebra k Q Λ' ν)
    (hx : x ∈ StendhalAlgebra.violatedIdeal k Q Λ' ν) :
    ∃ g ∈ StendhalAlgebra.violatedIdeal k Q (mergeWeights c Λ') ν,
      splitStendhalValue c Q Λ' ν g =
        splitStendhalValue c Q Λ' ν 1 * x * splitStendhalValue c Q Λ' ν 1 := by
  classical
  choose g hg he using fun (t s : {s : Seq μ // IsRedOrdered s}) =>
    exists_violated_splitStendhalValue c Λ' s.1 t.1 s.2 t.2 x hx
  refine ⟨∑ t, ∑ s, g t s, sum_mem fun t _ => sum_mem fun s _ => hg t s, ?_⟩
  rw [splitStendhalValue_one, Finset.sum_mul, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => he t s

end Violated

end Categorification.Stendhal.SplitRed
