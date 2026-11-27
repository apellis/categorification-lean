/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PhiLayerStd
import Categorification.WeightedKLR.RedStrands.RedShuffleFactor
import Categorification.WeightedKLR.RedStrands.CoarseAssignment
import Categorification.WeightedKLR.RedStrands.RedFirstEndomorphism
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossing
import Categorification.Algebra.FinrankCountingFiltration

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.25: the cokernel of the red/black shuffle

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 5.25
and its proof. For a red-ordered loading `s`, let `τ = τ_s` be the red/black shuffle permutation
(`redShufflePerm`), so that `t⁰ = τ • s` is red-first and `θ_s ∈ e(s) T^λ e(t⁰)` is the diagram of
`τ⁻¹`. A block assignment `g` of `s` is also one of `t⁰` after relabelling the positions by `τ`
(`shuffleAssign`); the two diagrams have the same bottom (`phiBottom_shuffleAssign`), and the
permutation of the second is that of the first followed by `τ⁻¹`, with lengths adding
(`phiPerm_shuffleAssign`, `length_phiPerm_mul_inv`). For the choice of reduced words
`shuffleWords ρ` that writes such a permutation as `ρ φ` followed by the canonical word of `τ⁻¹`,
`x_φ θ_s` is the diagram `x_{φ'}` of the matching block assignment of `t⁰`
(`phiElt_shuffleAssign`). So right multiplication by `θ_s`, `T^λ e(s) → T^λ e(t⁰)`, is a filtered
map which is the identity on the layers it meets, as in Webster's proof. Together with the
dimension identity of Lemma 5.19 for both loadings and the injectivity of `θ_s`, this shows that
the cokernel has a filtration by the standard modules of the block assignments of `t⁰` that do
not come from `s` (`exists_hasFiltration_shuffleCokernel`). This is the form of Lemma 5.25 used in
the proof of Theorem 6.14, where the cokernel is tensored with a standardly filtered module.

## Main definitions

* `shuffleAssign`, `shuffleWords`, `shuffleMul`, `shuffleCokernel`.

## Main results

* `shuffleAssign_mem`, `phiBottom_shuffleAssign`, `phiPerm_shuffleAssign`.
* `phiElt_shuffleAssign`: `x_φ θ_s = x_{φ'}`.
* `exists_hasFiltration_shuffleCokernel`, `exists_hasFiltration_shuffleCokernel_std`: the
  cokernel of `θ_s` is filtered by standard modules.
-/

noncomputable section

namespace Submodule

variable {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)
  (N : ι → Submodule R M)

omit [Fintype ι] [DecidableEq ι] in
/-- The image of `P_{>φ}` under a linear map is `P_{>φ}` of the image family. -/
theorem above_map (f : M →ₗ[R] M') (φ : ι) :
    above rel (fun φ => (N φ).map f) φ = (above rel N φ).map f := by
  simp only [above, Submodule.map_iSup]

theorem finiteDimensional_quotient {k : Type*} [Field k] [Algebra k R] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M] (S : Submodule R M) :
    FiniteDimensional k (M ⧸ S) :=
  Module.Finite.of_surjective (S.mkQ.restrictScalars k) (Submodule.mkQ_surjective S)

theorem finiteDimensional_submodule {k : Type*} [Field k] [Algebra k R] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M] (S : Submodule R M) :
    FiniteDimensional k S :=
  Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective

end Submodule

namespace Categorification.Stendhal

/- The `k`-algebra structure on corners used by the dimension count of Lemma 5.19. -/
attribute [local instance 2000] KLR.cornerAlgebra

open KLR TypeA Equiv

section Combinatorics

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- The block assignment of the red-first loading `τ_s • s` obtained from one of `s` by
relabelling positions along `τ_s`. -/
def shuffleAssign (s : Seq μ) (g : Fin m → ℕ) : Fin m → ℕ :=
  g ∘ (redShufflePerm s).symm

theorem lbl_redShuffle (s : Seq μ) (x : Fin m) :
    (redShufflePerm s • s).lbl x = s.lbl ((redShufflePerm s).symm x) := rfl

theorem assignKey_shuffleAssign (s : Seq μ) (g : Fin m → ℕ) (x : Fin m) :
    assignKey (redShufflePerm s • s).lbl (shuffleAssign s g) x =
      assignKey s.lbl g ((redShufflePerm s).symm x) := rfl

/-- `τ_s` keeps the relative order of the black strands. -/
theorem redShufflePerm_lt_iff_of_black {s : Seq μ} {X Y : Fin m} (hX : (s.lbl X).isLeft)
    (hY : (s.lbl Y).isLeft) : redShufflePerm s X < redShufflePerm s Y ↔ X < Y := by
  rw [redShufflePerm_lt_iff, redShuffleKey_black hX, redShuffleKey_black hY, Fin.lt_def]
  omega

/-- `τ_s` keeps the relative order of the red strands. -/
theorem redShufflePerm_lt_iff_of_red {s : Seq μ} {X Y : Fin m} (hX : (s.lbl X).isRight)
    (hY : (s.lbl Y).isRight) : redShufflePerm s X < redShufflePerm s Y ↔ X < Y := by
  rw [redShufflePerm_lt_iff, redShuffleKey_red hX, redShuffleKey_red hY, Fin.lt_def]

/-- In a red-first loading, a black strand has all `ℓ` red strands before it. -/
theorem le_redsBefore_of_isRedFirst {t : Seq μ} (ht : IsRedOrdered t) (htf : IsRedFirst t)
    {x : Fin m} (hx : (t.lbl x).isLeft) : ℓ ≤ redsBefore t.lbl x := by
  rcases ℓ with _ | ℓ
  · exact Nat.zero_le _
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr t (Fin.last ℓ)
  have hqx : q < x := htf x q hx (by simp [hq])
  have h := redsBefore_add_le t.lbl hqx
  rw [redsBefore_of_lbl_eq_inr ht hq, hq] at h
  simp only [Sum.isRight_inr, ite_true, Fin.val_last] at h
  exact h

/-- **The relabelled block assignment is a block assignment of `τ_s • s`.** -/
theorem shuffleAssign_mem {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) :
    shuffleAssign s g ∈ assignments (redShufflePerm s • s).lbl := by
  have ht := isRedOrdered_redShuffle hs
  refine mem_assignList.2 fun x => ?_
  have hgx := mem_assignList.1 hg ((redShufflePerm s).symm x)
  unfold assignChoices at hgx ⊢
  rw [lbl_redShuffle] at ⊢
  rcases hl : s.lbl ((redShufflePerm s).symm x) with i | r
  · simp only [hl, Sum.isRight_inl, Bool.false_eq_true, ite_false, List.mem_range] at hgx ⊢
    have hb : ((redShufflePerm s • s).lbl x).isLeft := by rw [lbl_redShuffle, hl]; rfl
    have h₁ := le_redsBefore_of_isRedFirst ht (isRedFirst_redShuffle s) hb
    have h₂ := redsBefore_le_card hs ((redShufflePerm s).symm x)
    change g ((redShufflePerm s).symm x) < redsBefore (redShufflePerm s • s).lbl x + 1
    omega
  · simp only [hl, Sum.isRight_inr, ite_true, List.mem_singleton] at hgx ⊢
    have hx : (redShufflePerm s • s).lbl x = .inr r := by rw [lbl_redShuffle, hl]
    change g ((redShufflePerm s).symm x) = redsBefore (redShufflePerm s • s).lbl x
    rw [hgx, redsBefore_of_lbl_eq_inr hs hl, redsBefore_of_lbl_eq_inr ht hx]

private theorem eq_of_lbl_inr [DecidableEq I] {i : Seq μ} {a b : Fin m} {r : Fin ℓ}
    (ha : i.lbl a = .inr r) (hb : i.lbl b = .inr r) : a = b := by
  have e1 := eq_redStrand (ν := ν) (s := i.strandAt a) ha
  have e2 := eq_redStrand (ν := ν) (s := i.strandAt b) hb
  exact i.strandAt_injective (e1.trans e2.symm)

/-- Equal keys of a block assignment occur only at black strands or at a single position. -/
theorem assignKey_eq_cases [DecidableEq I] {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) {X Y : Fin m} (h : assignKey s.lbl g X = assignKey s.lbl g Y) :
    X = Y ∨ ((s.lbl X).isLeft ∧ (s.lbl Y).isLeft) := by
  rcases hX : s.lbl X with i | r <;> rcases hY : s.lbl Y with j | r'
  · exact .inr ⟨rfl, rfl⟩
  · exfalso
    rw [assignKey_black g (by simp [hX]), assignKey_red hg (by simp [hY])] at h
    omega
  · exfalso
    rw [assignKey_red hg (by simp [hX]), assignKey_black g (by simp [hY])] at h
    omega
  · left
    rw [assignKey_red hg (by simp [hX]), assignKey_red hg (by simp [hY]),
      redsBefore_of_lbl_eq_inr hs hX, redsBefore_of_lbl_eq_inr hs hY] at h
    have hr : r = r' := Fin.ext (by omega)
    subst hr
    exact eq_of_lbl_inr hX hY

/-- **The permutation of the relabelled assignment is that of `g` followed by `τ_s⁻¹`.** -/
theorem phiPerm_shuffleAssign [DecidableEq I] {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) :
    phiPerm (redShufflePerm s • s) (shuffleAssign s g) = phiPerm s g * (redShufflePerm s)⁻¹ := by
  refine perm_eq_of_lt_iff fun p q => ?_
  rw [keyPerm_lt_iff, Perm.mul_apply, Perm.mul_apply, keyPerm_lt_iff,
    assignKey_shuffleAssign, assignKey_shuffleAssign, Perm.inv_def]
  set X := (redShufflePerm s).symm p
  set Y := (redShufflePerm s).symm q
  refine or_congr_right (and_congr_right fun he => ?_)
  rcases assignKey_eq_cases hs hg he with hXY | ⟨hX, hY⟩
  · have : p = q := (redShufflePerm s).symm.injective hXY
    subst this
    exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
  · have := redShufflePerm_lt_iff_of_black hX hY
    simp only [X, Y, Equiv.apply_symm_apply] at this
    exact this

/-- The inversions of `τ_s⁻¹` are inversions of `φ τ_s⁻¹`: a black strand left of a red one in
`s` stays left of it at the bottom of `x_φ`. -/
theorem invSet_inv_redShufflePerm_subset {s : Seq μ} {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) :
    invSet m (redShufflePerm s)⁻¹ ⊆ invSet m (phiPerm s g * (redShufflePerm s)⁻¹) := by
  rintro ⟨p, q⟩ hpq
  rw [mem_invSet] at hpq ⊢
  dsimp only at hpq ⊢
  refine ⟨hpq.1, ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply]
  set X := (redShufflePerm s)⁻¹ p
  set Y := (redShufflePerm s)⁻¹ q
  have hYX : Y < X := hpq.2
  have hpq' : redShufflePerm s X < redShufflePerm s Y := by
    simpa [X, Y, Perm.inv_def] using hpq.1
  rw [redShufflePerm_lt_iff] at hpq'
  -- `X` is red and `Y` is black
  have hXr : (s.lbl X).isRight := by
    by_contra hX
    have hX' : (s.lbl X).isLeft := by
      rcases h : s.lbl X with _ | _ <;> simp_all
    rw [redShuffleKey_black hX'] at hpq'
    unfold redShuffleKey at hpq'
    split_ifs at hpq' <;> simp only [Fin.lt_def] at hYX <;> omega
  have hYb : (s.lbl Y).isLeft := by
    by_contra hY
    have hY' : (s.lbl Y).isRight := by
      rcases h : s.lbl Y with _ | _ <;> simp_all
    rw [redShuffleKey_red hXr, redShuffleKey_red hY'] at hpq'
    simp only [Fin.lt_def] at hYX
    omega
  refine (keyPerm_lt_iff _).2 (.inl ?_)
  have hYk := assignKey_black (lbl := s.lbl) g (p := Y) (by
    rcases h : s.lbl Y with _ | _ <;> simp_all)
  have hXk := assignKey_red hg (p := X) hXr
  have hgY := mem_assignList.1 hg Y
  unfold assignChoices at hgY
  have hYl : (s.lbl Y).isRight = false := by rcases h : s.lbl Y with _ | _ <;> simp_all
  simp only [hYl, Bool.false_eq_true, ite_false, List.mem_range] at hgY
  have hmono := redsBefore_add_le s.lbl hYX
  rw [hYk, hXk]
  split_ifs at hmono <;> omega

/-- **Lengths add**: `ℓ(φ τ_s⁻¹) = ℓ(φ) + ℓ(τ_s⁻¹)`. -/
theorem length_phiPerm_mul_inv {s : Seq μ} {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) :
    length m (phiPerm s g * (redShufflePerm s)⁻¹) =
      length m (phiPerm s g) + length m (redShufflePerm s)⁻¹ := by
  have h := length_add_of_invSet_subset (invSet_inv_redShufflePerm_subset hg)
  rw [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at h
  exact h.symm

/-- The bottom of the relabelled diagram is the bottom of `x_φ`. -/
theorem phiBottom_shuffleAssign [DecidableEq I] {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) :
    phiBottom (redShufflePerm s • s) (shuffleAssign s g) = phiBottom s g := by
  rw [phiBottom, phiPerm_shuffleAssign hs hg, mul_smul, inv_smul_smul]

end Combinatorics

section Words

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

open Classical in
/-- Reduced words adapted to the shuffle `θ_s`: when the lengths of `w τ_s` and `τ_s⁻¹` add up
to that of `w`, the word of `w` is `ρ (w τ_s)` followed by the canonical word of `τ_s⁻¹`. -/
def shuffleWords (s : Seq μ) (ρ : Perm (Fin m) → List ℕ) (w : Perm (Fin m)) : List ℕ :=
  if length m w = length m (w * redShufflePerm s) + length m (redShufflePerm s)⁻¹ then
    ρ (w * redShufflePerm s) ++ canWord m (redShufflePerm s)⁻¹
  else ρ w

theorem shuffleWords_spec (s : Seq μ) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (w : Perm (Fin m)) :
    IsReduced m (shuffleWords s ρ w) ∧ wordProd m (shuffleWords s ρ w) = w := by
  unfold shuffleWords
  split_ifs with h
  · have hw : wordProd m (ρ (w * redShufflePerm s) ++ canWord m (redShufflePerm s)⁻¹) = w := by
      rw [wordProd_append, (hρ _).2, wordProd_canWord, mul_inv_cancel_right]
    refine ⟨IsReduced.append_of_length_eq (hρ _).1 (isReduced_canWord _ _) ?_, hw⟩
    rw [hw, (hρ _).2, wordProd_canWord]
    exact h
  · exact hρ w

theorem shuffleWords_phiPerm [DecidableEq I] {s : Seq μ}
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) (ρ : Perm (Fin m) → List ℕ) :
    shuffleWords s ρ (phiPerm s g * (redShufflePerm s)⁻¹) =
      ρ (phiPerm s g) ++ canWord m (redShufflePerm s)⁻¹ := by
  unfold shuffleWords
  rw [inv_mul_cancel_right, ite_eq_left_of_eq_true _ _ (eq_true (length_phiPerm_mul_inv hg))]

end Words

section Algebra

open KLRAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- **`x_φ θ_s = x_{φ'}`** (Webster, arXiv:1309.3796v3, proof of Lemma 5.25): for the reduced
words `shuffleWords s ρ`, the diagram of the relabelled block assignment of `τ_s • s` is the
diagram `x_φ` of `s` followed by the shuffle `θ_s`. -/
theorem phiElt_shuffleAssign {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    phiElt Q Λ (shuffleWords s ρ) (isRedOrdered_redShuffle hs) (shuffleAssign_mem hs hg) =
      phiElt Q Λ ρ hs hg * redShuffle Q Λ s hs := by
  unfold phiElt redShuffle redShuffleStendhal
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e (phiBottom (redShufflePerm s • s) (shuffleAssign s g)) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (ψw (shuffleWords s ρ (phiPerm (redShufflePerm s • s) (shuffleAssign s g)))) *
      StendhalAlgebraAllOrders.e (redShufflePerm s • s) =
    StendhalAlgebraAllOrders.e (phiBottom s g) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (ρ (phiPerm s g))) *
      StendhalAlgebraAllOrders.e s *
      (StendhalAlgebraAllOrders.e s *
        StendhalAlgebraAllOrders.ofKLR k Q Λ ν (ψw (canWord m (redShufflePerm s)⁻¹)) *
        StendhalAlgebraAllOrders.e (redShufflePerm s • s))
  rw [phiBottom_shuffleAssign hs hg, phiPerm_shuffleAssign hs hg, shuffleWords_phiPerm hg]
  simp only [StendhalAlgebraAllOrders.e, ← map_mul]
  congr 1
  have h₁ : (wordProd m (ρ (phiPerm s g)))⁻¹ • phiBottom s g = s := by
    rw [(hρ _).2, phiBottom, inv_smul_smul]
  have h₂ : (wordProd m (canWord m (redShufflePerm s)⁻¹))⁻¹ • s = redShufflePerm s • s := by
    rw [wordProd_canWord, inv_inv]
  have hgen := KLRAlgebra.e_ψw_e_mul_e_gen Q Λ (ρ (phiPerm s g))
    (canWord m (redShufflePerm s)⁻¹) 1 _ _ _ h₁ h₂
  simp only [map_one, mul_one] at hgen
  have h₃ : (wordProd m (ρ (phiPerm s g) ++ canWord m (redShufflePerm s)⁻¹))⁻¹ •
      phiBottom s g = redShufflePerm s • s := by
    rw [wordProd_append, mul_inv_rev, mul_smul, h₁, h₂]
  rw [hgen, e_mul_ψw, mul_assoc, KLRAlgebra.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true h₃), h₃]

end Algebra

section Cokernel

open KLRAlgebra ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => TensorProductAlgebra k Q Λ ν

variable (Q Λ) in
theorem redShuffle_mul_seqIdem (s : Seq μ) (hs : IsRedOrdered s) :
    redShuffle Q Λ s hs * seqIdem Q Λ (redShufflePerm s • s) (isRedOrdered_redShuffle hs) =
      redShuffle Q Λ s hs := by
  unfold redShuffle redShuffleStendhal
  rw [← map_mul, StendhalAlgebra.cut_mul_e]

variable (Q Λ) in
/-- Right multiplication by `θ_s`, from `T^λ e(s)` to `T^λ e(τ_s • s)`. -/
def shuffleMul (s : Seq μ) (hs : IsRedOrdered s) :
    lIdeal (seqIdem Q Λ s hs) →ₗ[A]
      lIdeal (seqIdem Q Λ (redShufflePerm s • s) (isRedOrdered_redShuffle hs)) where
  toFun x := ⟨x * redShuffle Q Λ s hs, by
    change _ * _ * _ = _
    rw [mul_assoc, redShuffle_mul_seqIdem]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' a x := Subtype.ext (mul_assoc _ _ _)

/-- The block assignment `shuffleAssign s g` of `τ_s • s`, as an index. -/
def PhiIndex.shuffle {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    PhiIndex (redShufflePerm s • s) :=
  ⟨shuffleAssign s g.1, List.mem_toFinset.2 (shuffleAssign_mem hs g.mem)⟩

omit [DecidableEq I] in
theorem PhiIndex.shuffle_injective {s : Seq μ} (hs : IsRedOrdered s) :
    Function.Injective (PhiIndex.shuffle hs) := by
  intro g g' h
  apply Subtype.ext
  funext x
  have := congrFun (congrArg Subtype.val h) (redShufflePerm s x)
  simpa [PhiIndex.shuffle, shuffleAssign] using this

theorem phiBottom_shuffle {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    phiBottom (redShufflePerm s • s) (PhiIndex.shuffle hs g).1 = phiBottom s g.1 :=
  phiBottom_shuffleAssign hs g.mem

theorem shuffleMul_phiVec {s : Seq μ} (hs : IsRedOrdered s) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    shuffleMul Q Λ s hs (phiVec Q Λ ρ hs g) =
      phiVec Q Λ (shuffleWords s ρ) (isRedOrdered_redShuffle hs) (PhiIndex.shuffle hs g) :=
  Subtype.ext (phiElt_shuffleAssign Q Λ hs g.mem hρ).symm

theorem map_shuffleMul_phiSub {s : Seq μ} (hs : IsRedOrdered s) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    (phiSub Q Λ ρ hs g).map (shuffleMul Q Λ s hs) =
      phiSub Q Λ (shuffleWords s ρ) (isRedOrdered_redShuffle hs) (PhiIndex.shuffle hs g) := by
  rw [phiSub, Submodule.map_span, Set.image_singleton, shuffleMul_phiVec hs hρ]
  rfl

variable (Q Λ) in
/-- The image `T^λ e(s) θ_s` of right multiplication by `θ_s`. -/
def shuffleRange (s : Seq μ) (hs : IsRedOrdered s) :
    Submodule A (lIdeal (seqIdem Q Λ (redShufflePerm s • s) (isRedOrdered_redShuffle hs))) :=
  LinearMap.range (shuffleMul Q Λ s hs)

variable (Q Λ) in
/-- A quotient of the projective `T^λ e(t)`. -/
def lIdealQuot (t : Seq μ) (ht : IsRedOrdered t) (p : Submodule A (lIdeal (seqIdem Q Λ t ht))) :
    Type :=
  lIdeal (seqIdem Q Λ t ht) ⧸ p

instance (t : Seq μ) (ht : IsRedOrdered t) (p : Submodule A (lIdeal (seqIdem Q Λ t ht))) :
    AddCommGroup (lIdealQuot Q Λ t ht p) :=
  inferInstanceAs (AddCommGroup (lIdeal (seqIdem Q Λ t ht) ⧸ p))

instance (t : Seq μ) (ht : IsRedOrdered t) (p : Submodule A (lIdeal (seqIdem Q Λ t ht))) :
    Module A (lIdealQuot Q Λ t ht p) :=
  inferInstanceAs (Module A (lIdeal (seqIdem Q Λ t ht) ⧸ p))

instance (t : Seq μ) (ht : IsRedOrdered t) (p : Submodule A (lIdeal (seqIdem Q Λ t ht))) :
    Module k (lIdealQuot Q Λ t ht p) :=
  inferInstanceAs (Module k (lIdeal (seqIdem Q Λ t ht) ⧸ p))

instance (t : Seq μ) (ht : IsRedOrdered t) (p : Submodule A (lIdeal (seqIdem Q Λ t ht))) :
    IsScalarTower k A (lIdealQuot Q Λ t ht p) :=
  inferInstanceAs (IsScalarTower k A (lIdeal (seqIdem Q Λ t ht) ⧸ p))


variable (Q Λ) in
/-- The cokernel `T^λ e(τ_s • s) / T^λ e(s) θ_s` of right multiplication by `θ_s`. -/
abbrev shuffleCokernel (s : Seq μ) (hs : IsRedOrdered s) : Type :=
  lIdealQuot Q Λ (redShufflePerm s • s) (isRedOrdered_redShuffle hs) (shuffleRange Q Λ s hs)

variable (Q Λ) in
/-- The projection onto the cokernel. -/
def shuffleCokernel.mk (s : Seq μ) (hs : IsRedOrdered s) :
    lIdeal (seqIdem Q Λ (redShufflePerm s • s) (isRedOrdered_redShuffle hs)) →ₗ[A]
      shuffleCokernel Q Λ s hs :=
  (shuffleRange Q Λ s hs).mkQ

theorem shuffleCokernel.mk_surjective (s : Seq μ) (hs : IsRedOrdered s) :
    Function.Surjective (shuffleCokernel.mk Q Λ s hs) :=
  Submodule.mkQ_surjective _

theorem shuffleCokernel.mk_shuffleMul (s : Seq μ) (hs : IsRedOrdered s)
    (x : lIdeal (seqIdem Q Λ s hs)) :
    shuffleCokernel.mk Q Λ s hs (shuffleMul Q Λ s hs x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ x)

theorem shuffleCokernel.range_mk (s : Seq μ) (hs : IsRedOrdered s) :
    LinearMap.range (shuffleCokernel.mk Q Λ s hs) = ⊤ :=
  Submodule.range_mkQ _

variable (Q Λ) in
/-- The image of `T^λ x_{φ'}` in the cokernel. -/
def cokerSub (ρ : Perm (Fin m) → List ℕ) (s : Seq μ) (hs : IsRedOrdered s)
    (j : PhiIndex (redShufflePerm s • s)) : Submodule A (shuffleCokernel Q Λ s hs) :=
  (phiSub Q Λ (shuffleWords s ρ) (isRedOrdered_redShuffle hs) j).map
    (shuffleCokernel.mk Q Λ s hs)

theorem cokerSub_shuffle {s : Seq μ} (hs : IsRedOrdered s) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    cokerSub Q Λ ρ s hs (PhiIndex.shuffle hs g) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_shuffleMul_phiSub hs hρ] at hy
  obtain ⟨x, _, rfl⟩ := hy
  exact shuffleCokernel.mk_shuffleMul s hs x

theorem iSup_cokerSub {s : Seq μ} (hs : IsRedOrdered s) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    (⨆ j, cokerSub Q Λ ρ s hs j) = ⊤ := by
  simp only [cokerSub]
  rw [← Submodule.map_iSup, iSup_phiSub_eq_top _ _ (shuffleWords_spec s hρ), Submodule.map_top,
    shuffleCokernel.range_mk]

variable (Q Λ) in
/-- The class of `x_{φ'}` in the layer of the cokernel at `φ'`. -/
def cokerLayerGen (ρ : Perm (Fin m) → List ℕ) (s : Seq μ) (hs : IsRedOrdered s)
    (j : PhiIndex (redShufflePerm s • s)) :
    Submodule.layer PhiLT (cokerSub Q Λ ρ s hs) j :=
  Submodule.Quotient.mk ⟨shuffleCokernel.mk Q Λ s hs
    (phiVec Q Λ (shuffleWords s ρ) (isRedOrdered_redShuffle hs) j),
    Submodule.mem_sup_left (Submodule.mem_map_of_mem (Submodule.subset_span rfl))⟩

theorem cokerLayerGen_annihilated {s : Seq μ} (hs : IsRedOrdered s)
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (j : PhiIndex (redShufflePerm s • s)) (t : Seq μ) (ht : IsRedOrdered t) (a : A)
    (hlt : StendhalLT (phiBottom (redShufflePerm s • s) j.1) t) :
    (seqIdem Q Λ t ht * a) • cokerLayerGen Q Λ ρ s hs j = 0 := by
  have h := phiLayerGen_annihilated (Q := Q) (Λ := Λ) _ (isRedOrdered_redShuffle hs)
    (shuffleWords_spec s hρ) j t ht a hlt
  rw [phiLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at h
  rw [cokerLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  change _ ∈ Submodule.above PhiLT (fun j => cokerSub Q Λ ρ s hs j) j
  simp only [cokerSub]
  rw [Submodule.above_map]
  exact ⟨_, h, by simp⟩

variable (Q Λ) in
/-- The map `S_{φ'} → ` (layer of the cokernel at `φ'`), `[e(φ' • t⁰)] ↦ [x_{φ'}]`. -/
def cokerLayerMap {s : Seq μ} (hs : IsRedOrdered s) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (j : PhiIndex (redShufflePerm s • s)) :
    leftStandard Q Λ (phiBottom _ j.1) (j.isRedOrdered (isRedOrdered_redShuffle hs)) →ₗ[A]
      Submodule.layer PhiLT (cokerSub Q Λ ρ s hs) j :=
  leftStandardLift _ _ (cokerLayerGen Q Λ ρ s hs j) fun t ht a hlt =>
    cokerLayerGen_annihilated hs hρ j t ht a hlt

theorem cokerLayerMap_surjective {s : Seq μ} (hs : IsRedOrdered s) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (j : PhiIndex (redShufflePerm s • s)) :
    Function.Surjective (cokerLayerMap Q Λ hs ρ hρ j) := by
  have hunit : cokerLayerMap Q Λ hs ρ hρ j
      (leftStandardUnit Q Λ _ (j.isRedOrdered (isRedOrdered_redShuffle hs))) =
      cokerLayerGen Q Λ ρ s hs j := by
    refine leftStandardLift_unit (k := k) (Q := Q) (Λ := Λ) (ν := ν) _ _ _ ?_ _
    rw [cokerLayerGen, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    exact seqIdem_mul_phiElt (Q := Q) (Λ := Λ) _ (isRedOrdered_redShuffle hs) j.mem
  intro v
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨n, hn, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨n', hn', rfl⟩ := hn
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn'
  refine ⟨c • leftStandardUnit Q Λ _ (j.isRedOrdered (isRedOrdered_redShuffle hs)), ?_⟩
  rw [map_smul, hunit, cokerLayerGen, ← Submodule.Quotient.mk_smul, eq_comm,
    Submodule.Quotient.eq, Submodule.mem_comap]
  convert hb using 1
  change shuffleCokernel.mk Q Λ s hs (c • _) + b - c • shuffleCokernel.mk Q Λ s hs _ = b
  rw [map_smul]
  abel

theorem subsingleton_layer_cokerSub {s : Seq μ} (hs : IsRedOrdered s)
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (g : PhiIndex s) :
    Subsingleton (Submodule.layer PhiLT (cokerSub Q Λ ρ s hs) (PhiIndex.shuffle hs g)) := by
  refine subsingleton_of_forall_eq 0 fun q => ?_
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [cokerSub_shuffle hs hρ, bot_sup_eq] at hw
  exact hw

end Cokernel


section Filtration

open ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {C : QuantumGroup.CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

open Classical in
/-- **Lemma 5.25, filtered form** (Webster, arXiv:1309.3796v3, proof of Lemma 5.25): right
multiplication by the red/black shuffle `θ_s` embeds `T^λ e(s)` in `T^λ e(τ_s • s)`, and its
cokernel has a filtration by the standard modules `S_{φ' • (τ_s • s)}` of the block assignments
`φ'` of `τ_s • s` that do not come from block assignments of `s`. The map is filtered, with
`Φ_s ⊂ Φ_{τ_s • s}` by `shuffleAssign`, and the identity on the layers it meets; the dimension
identity of Lemma 5.19 for both loadings shows that the remaining layers of the cokernel are the
standard modules. Route hypotheses: those of Lemma 5.19 (`AllFiniteDeltaInjective`) and of the
injectivity of `θ_s` (`BaseCrossing`), both proved at the standard Khovanov–Lauda parameters
(`exists_hasFiltration_shuffleCokernel_std`). -/
theorem exists_hasFiltration_shuffleCokernel (hR : IsRouquierQ C Q) (hQs : KLRSymm Q)
    (hbase : BaseCrossing Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQs)
    (Λ : Fin ℓ → I →₀ ℕ) (s : Seq μ) (hs : IsRedOrdered s) :
    ∃ l : List (PhiIndex (redShufflePerm s • s)),
      (∀ j ∈ l, j ∉ Set.range (PhiIndex.shuffle hs)) ∧
      HasFiltration (fun j : PhiIndex (redShufflePerm s • s) =>
          ModuleCat.of (TensorProductAlgebra k Q Λ ν)
            (leftStandard Q Λ (phiBottom _ j.1) (j.isRedOrdered (isRedOrdered_redShuffle hs)))) l
        (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (shuffleCokernel Q Λ s hs)) := by
  have hs' := isRedOrdered_redShuffle hs
  let ρ : Perm (Fin m) → List ℕ := fun w => (TypeA.exists_reduced m w).choose
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := fun w =>
    (TypeA.exists_reduced m w).choose_spec
  have : Module.Finite k (TensorProductAlgebra k Q Λ ν) := by
    convert tensorProductAlgebra_finite (Q := Q) Λ ν hR using 4
    exact cornerAlgebra_eq_instAlgebraCorner _
  have hP : ∀ (t : Seq μ) (ht : IsRedOrdered t),
      FiniteDimensional k (lIdeal (seqIdem Q Λ t ht)) := fun t ht =>
    Submodule.finiteDimensional_submodule _
  have hS : ∀ (t : Seq μ) (ht : IsRedOrdered t), FiniteDimensional k (leftStandard Q Λ t ht) :=
    fun t ht => Submodule.finiteDimensional_quotient _
  have : FiniteDimensional k (shuffleCokernel Q Λ s hs) :=
    Submodule.finiteDimensional_quotient (shuffleRange Q Λ s hs)
  set N := cokerSub Q Λ ρ s hs with hN
  -- the dimension of the cokernel
  have hinj : Function.Injective (shuffleMul Q Λ s hs) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (mul_redShuffle_injective hR hQs hbase Λ s hs x x.2
      (congrArg Subtype.val hx))
  have hdimN : Module.finrank k (shuffleCokernel Q Λ s hs) +
      Module.finrank k (lIdeal (seqIdem Q Λ s hs)) =
      Module.finrank k (lIdeal (seqIdem Q Λ _ hs')) := by
    have h1 := Submodule.finrank_quotient_add_finrank ((shuffleRange Q Λ s hs).restrictScalars k)
    have h2 := LinearMap.finrank_range_of_inj (f := (shuffleMul Q Λ s hs).restrictScalars k) hinj
    rw [LinearMap.range_restrictScalars] at h2
    rw [(Submodule.Quotient.restrictScalarsEquiv k (shuffleRange Q Λ s hs)).finrank_eq] at h1
    have h2' : Module.finrank k ((shuffleRange Q Λ s hs).restrictScalars k) =
        Module.finrank k (lIdeal (seqIdem Q Λ s hs)) := h2
    change Module.finrank k (shuffleCokernel Q Λ s hs) + _ = _ at h1
    omega
  -- the dimension count
  have hstd : ∀ {t : Seq μ} (ht : IsRedOrdered t) (j : PhiIndex t),
      stdDim Q Λ (phiBottom t j.1) =
        Module.finrank k (leftStandard Q Λ _ (j.isRedOrdered ht)) := fun ht j => by
    unfold stdDim
    rw [dite_eq_left (j.isRedOrdered ht)]
  let d : PhiIndex (redShufflePerm s • s) → ℕ := fun j =>
    if j ∈ Set.range (PhiIndex.shuffle hs) then 0 else stdDim Q Λ (phiBottom (redShufflePerm s • s) j.1)
  have hsum : ∑ j, d j = Module.finrank k (shuffleCokernel Q Λ s hs) := by
    have h₀ := finrank_lIdeal_eq_sum_phiBottom Q hQs hR hall Λ hs
    have h₁ := finrank_lIdeal_eq_sum_phiBottom Q hQs hR hall Λ hs'
    simp only [← hstd hs, ← hstd hs'] at h₀ h₁
    have hsplit : ∑ j : PhiIndex (redShufflePerm s • s), stdDim Q Λ (phiBottom (redShufflePerm s • s) j.1) =
        ∑ j, d j + ∑ j : PhiIndex (redShufflePerm s • s),
          if j ∈ Set.range (PhiIndex.shuffle hs) then stdDim Q Λ (phiBottom (redShufflePerm s • s) j.1) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [d]
      split_ifs <;> simp
    have himg : (∑ j : PhiIndex (redShufflePerm s • s),
        if j ∈ Set.range (PhiIndex.shuffle hs) then stdDim Q Λ (phiBottom (redShufflePerm s • s) j.1) else 0) =
        ∑ g : PhiIndex s, stdDim Q Λ (phiBottom s g.1) := by
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun j => j ∈ Set.range (PhiIndex.shuffle hs)) =
          Finset.univ.map ⟨PhiIndex.shuffle hs, PhiIndex.shuffle_injective hs⟩ := by
        ext j
        simp
      rw [hf, Finset.sum_map]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Function.Embedding.coeFn_mk]
      rw [phiBottom_shuffle hs g]
    omega
  have hsub : ∀ S : Submodule (TensorProductAlgebra k Q Λ ν) (shuffleCokernel Q Λ s hs),
      FiniteDimensional k S := fun S => Submodule.finiteDimensional_submodule S
  have hlay : ∀ j, FiniteDimensional k (Submodule.layer PhiLT N j) := fun j =>
    Submodule.finiteDimensional_quotient _
  have hfl : ∀ j, Module.finrank k (Submodule.layer PhiLT N j) =
      Submodule.layerRank (k := k) PhiLT N j := fun j =>
    Submodule.finrank_quotient_comap_subtype le_sup_right
  have hle : ∀ j, Submodule.layerRank (k := k) PhiLT N j ≤ d j := by
    intro j
    by_cases h : j ∈ Set.range (PhiIndex.shuffle hs)
    · obtain ⟨g, rfl⟩ := h
      have := subsingleton_layer_cokerSub (Q := Q) (Λ := Λ) hs hρ g
      rw [← hfl, Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _
    · simp only [d, h, ↓reduceIte]
      rw [← hfl, hstd hs' j]
      exact LinearMap.finrank_le_finrank_of_surjective
        (f := (cokerLayerMap Q Λ hs ρ hρ j).restrictScalars k)
        (cokerLayerMap_surjective hs hρ j)
  have htop : Submodule.finrankK k (⊤ : Submodule (TensorProductAlgebra k Q Λ ν)
      (shuffleCokernel Q Λ s hs)) = Module.finrank k (shuffleCokernel Q Λ s hs) := by
    unfold Submodule.finrankK
    rw [Submodule.restrictScalars_top, finrank_top]
  have heq := Submodule.layerRank_eq_of_sum_eq (k := k) PhiLT N phiLT_irrefl phiLT_trans
    (iSup_cokerSub hs hρ) d hle (by rw [hsum, htop])
  have htight : ∑ j, Submodule.layerRank (k := k) PhiLT N j = Submodule.finrankK k (⨆ j, N j) := by
    rw [Finset.sum_congr rfl fun j _ => heq j, hsum, iSup_cokerSub hs hρ, htop]
  obtain ⟨l, -, hl⟩ := Submodule.hasFiltration_iSup (k := k) (rel := PhiLT) (N := N) phiLT_irrefl phiLT_trans
    htight Finset.univ (by simp)
  have hl' := hl.of_equiv (Y' := ModuleCat.of (TensorProductAlgebra k Q Λ ν)
    (shuffleCokernel Q Λ s hs)) ((LinearEquiv.ofEq _ ⊤ (by
    simp only [Finset.mem_univ, iSup_pos]
    exact iSup_cokerSub hs hρ)).trans Submodule.topEquiv)
  let M : PhiIndex (redShufflePerm s • s) → List (PhiIndex (redShufflePerm s • s)) := fun j =>
    if j ∈ Set.range (PhiIndex.shuffle hs) then [] else [j]
  have hL : ∀ j, HasFiltration (fun j : PhiIndex (redShufflePerm s • s) =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν)
          (leftStandard Q Λ (phiBottom _ j.1) (j.isRedOrdered hs'))) (M j)
        (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (Submodule.layer PhiLT N j)) := by
    intro j
    by_cases h : j ∈ Set.range (PhiIndex.shuffle hs)
    · simp only [M, h, ↓reduceIte]
      obtain ⟨g, rfl⟩ := h
      exact .zero (subsingleton_layer_cokerSub (Q := Q) (Λ := Λ) hs hρ g)
    · simp only [M, h, ↓reduceIte]
      have hd := heq j
      simp only [d, h, ↓reduceIte] at hd
      rw [← hfl, hstd hs' j] at hd
      have hsurj := cokerLayerMap_surjective (Q := Q) (Λ := Λ) hs hρ j
      have hinj' := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd.symm
        (f := (cokerLayerMap Q Λ hs ρ hρ j).restrictScalars k)).2 hsurj
      exact HasFiltration.single
        (LinearEquiv.ofBijective (cokerLayerMap Q Λ hs ρ hρ j) ⟨hinj', hsurj⟩).symm
  refine ⟨l.flatMap M, fun j hj => ?_, hl'.bind hL⟩
  obtain ⟨c, -, hc⟩ := List.mem_flatMap.1 hj
  simp only [M] at hc
  split_ifs at hc with h
  · simp at hc
  · rw [List.mem_singleton] at hc
    exact hc ▸ h

end Filtration

section Standard

open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration
open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}

/-- **Lemma 5.25, filtered form, at the standard Khovanov–Lauda parameters** (Webster,
arXiv:1309.3796v3, proof of Lemma 5.25): `T^λ e(s) θ_s ⊂ T^λ e(τ_s • s)`, with cokernel
filtered by the standard modules of the block assignments of `τ_s • s` that do not come from
`s`. -/
theorem exists_hasFiltration_shuffleCokernel_std
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) :
    ∃ l : List (PhiIndex (redShufflePerm s • s)),
      (∀ j ∈ l, j ∉ Set.range (PhiIndex.shuffle hs)) ∧
      HasFiltration (fun j : PhiIndex (redShufflePerm s • s) =>
          ModuleCat.of (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν)
            (leftStandard (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ (phiBottom _ j.1)
              (j.isRedOrdered (isRedOrdered_redShuffle hs)))) l
        (ModuleCat.of (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν)
          (shuffleCokernel (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs)) :=
  exists_hasFiltration_shuffleCokernel hR hQs (baseCrossing_std hR hQs)
    (fun _ _ => allFiniteDeltaInjective_std hR hQs) Λ s hs

end Standard

end Categorification.Stendhal
