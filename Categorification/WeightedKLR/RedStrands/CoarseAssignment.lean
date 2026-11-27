/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRoot

/-!
# Coarse block assignments

Part of the proof of Webster, arXiv:1309.3796v3, §6.1, Lemma 6.8: the kernel of a loading
projective onto its partial standard is filtered by partial standards at higher loadings. The
partial standardization keeps every red cut except the cut at one red strand `λ_j`, so the two
blocks `j` (between `λ_{j-1}` and `λ_j`) and `j + 1` (right of `λ_j`) merge.

For a red-ordered loading `s`, a block assignment `f` of `s` (`assignments`, Webster's set `Φ̃`
of §5.4) is *coarse* when no black strand is newly assigned to block `j`. Every assignment `f`
factors as a coarse assignment `g = coarsen j s f` followed by a *local* assignment `f'` of the
bottom `u = φ_g • s`, which moves black strands only from block `j + 1` to block `j`:
`φ_f = φ_{f'} φ_g` (`phiPerm_eq_mul`), the inversions of `φ_g` are inversions of `φ_f`
(`invSet_phiPerm_coarsen_subset`), and the bottoms agree. This gives a bijection between the
block assignments of `s` and the pairs of a coarse assignment `g` and a local assignment of
`φ_g • s`, in the form of a sum (`sum_assignments_eq_sum_coarse_local`).

The black counts of the bottom of an assignment are read off the assignment
(`blackCount_phiBottom`): a black strand ends left of `λ_r` exactly when its new block is at most
`r`. Coarsening changes only the count at `λ_j` (`blackCount_phiBottom_coarsen`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

section Counts

omit [DecidableEq I] in
/-- In a red-ordered loading the red strand `λ_r` has `r` red strands before it. -/
theorem redsBefore_of_lbl_eq_inr {s : Seq μ} (hs : IsRedOrdered s) {p : Fin m} {r : Fin ℓ}
    (hp : s.lbl p = .inr r) : redsBefore s.lbl p = r :=
  (redIndexed_of_isRedOrdered hs p r hp).symm

omit [DecidableEq I] in
/-- In a red-ordered loading a black strand lies left of `λ_r` exactly when its block is at
most `r`. -/
theorem lt_iff_redsBefore_le {s : Seq μ} (hs : IsRedOrdered s) {p q : Fin m} {r : Fin ℓ}
    (hp : (s.lbl p).isRight = false) (hq : s.lbl q = .inr r) :
    p < q ↔ redsBefore s.lbl p ≤ r := by
  have hrq := redsBefore_of_lbl_eq_inr hs hq
  constructor
  · intro h
    have := redsBefore_add_le s.lbl h
    omega
  · intro h
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with h' | rfl
    · have := redsBefore_add_le s.lbl h'
      simp only [hq, Sum.isRight_inr, ite_true] at this
      omega
    · simp [hq] at hp

/-- The black counts of a red-ordered loading, by blocks. -/
theorem blackCount_eq_card_redsBefore {s : Seq μ} (hs : IsRedOrdered s) (r : Fin ℓ) (i : I) :
    blackCount s r i = (Finset.univ.filter fun p =>
      s.lbl p = .inl i ∧ redsBefore s.lbl p ≤ r).card := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr s r
  unfold blackCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, (lt_iff_redsBefore_le hs (by simp [hp]) hq).1 (h q hq)⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun b hb => ?_⟩
    have hbq : b = q := by
      by_contra hne
      have h1 := redsBefore_of_lbl_eq_inr hs hb
      have h2 := redsBefore_of_lbl_eq_inr hs hq
      rcases lt_or_gt_of_ne hne with h' | h'
      · have := redsBefore_add_le s.lbl h'
        simp only [hb, Sum.isRight_inr, ite_true] at this
        omega
      · have := redsBefore_add_le s.lbl h'
        simp only [hq, Sum.isRight_inr, ite_true] at this
        omega
    subst hbq
    exact (lt_iff_redsBefore_le hs (by simp [hp]) hq).2 h

/-- **Black counts of the bottom of a block assignment**: a black strand ends left of `λ_r`
exactly when its new block is at most `r`. -/
theorem blackCount_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) (r : Fin ℓ) (i : I) :
    blackCount (phiBottom s f) r i = (Finset.univ.filter fun p =>
      s.lbl p = .inl i ∧ f p ≤ r).card := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr s r
  have hkq : assignKey s.lbl f q = 2 * r + 1 := by
    rw [assignKey_red hf (by simp [hq]), redsBefore_of_lbl_eq_inr hs hq]
  rw [blackCount_smul]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    have hkp : assignKey s.lbl f p = 2 * f p := assignKey_black f (by simp [hp])
    rcases (keyPerm_lt_iff _).1 (h q hq) with h' | ⟨h', -⟩ <;> omega
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun b hb => ?_⟩
    have hkb : assignKey s.lbl f b = 2 * r + 1 := by
      rw [assignKey_red hf (by simp [hb]), redsBefore_of_lbl_eq_inr hs hb]
    have hkp : assignKey s.lbl f p = 2 * f p := assignKey_black f (by simp [hp])
    exact (keyPerm_lt_iff _).2 (.inl (by omega))

end Counts

section Coarse

variable (j : ℕ)

/-- An assignment is *coarse* (for the merged blocks `j`, `j + 1`) when no black strand is
newly assigned to block `j`. -/
def IsCoarse (s : Seq μ) (f : Fin m → ℕ) : Prop :=
  ∀ p, (s.lbl p).isRight = false → f p = j → redsBefore s.lbl p = j

/-- An assignment is *local* when it moves black strands only from block `j + 1` to block
`j`. -/
def IsLocal (s : Seq μ) (f : Fin m → ℕ) : Prop :=
  ∀ p, (s.lbl p).isRight = false →
    f p = redsBefore s.lbl p ∨ (redsBefore s.lbl p = j + 1 ∧ f p = j)

/-- The coarse part of an assignment: black strands newly assigned to block `j` are sent to
block `j + 1` instead. -/
def coarsen (s : Seq μ) (f : Fin m → ℕ) (p : Fin m) : ℕ :=
  if (s.lbl p).isRight = false ∧ f p = j ∧ j + 1 ≤ redsBefore s.lbl p then j + 1 else f p

variable {j}

omit [DecidableEq I] in
theorem coarsen_mem {s : Seq μ} {f : Fin m → ℕ} (hf : f ∈ assignments s.lbl) :
    coarsen j s f ∈ assignments s.lbl := by
  refine mem_assignList.2 fun p => ?_
  have h := mem_assignList.1 hf p
  unfold coarsen
  split_ifs with hc
  · obtain ⟨hb, -, hle⟩ := hc
    simp only [assignChoices, hb, Bool.false_eq_true, ite_false, List.mem_range]
    omega
  · exact h

omit [DecidableEq I] in
theorem isCoarse_coarsen (s : Seq μ) (f : Fin m → ℕ) (hf : f ∈ assignments s.lbl) :
    IsCoarse j s (coarsen j s f) := by
  intro p hp hfp
  have h := mem_assignList.1 hf p
  simp only [assignChoices, hp, Bool.false_eq_true, ite_false, List.mem_range] at h
  unfold coarsen at hfp
  split_ifs at hfp with hc
  · omega
  · simp only [hp, true_and, not_and, not_le] at hc
    have := hc hfp
    omega

omit [DecidableEq I] in
theorem coarsen_le (s : Seq μ) (f : Fin m → ℕ) (p : Fin m) : f p ≤ coarsen j s f p := by
  unfold coarsen
  split_ifs with hc
  · omega
  · exact le_rfl

omit [DecidableEq I] in
theorem coarsen_eq_of_isCoarse {s : Seq μ} {f : Fin m → ℕ} (hf : IsCoarse j s f) :
    coarsen j s f = f := by
  funext p
  unfold coarsen
  split_ifs with hc
  · obtain ⟨hb, hfp, hle⟩ := hc
    have := hf p hb hfp
    omega
  · rfl

/-- Coarsening changes only the black counts at `λ_j`. -/
theorem blackCount_phiBottom_coarsen {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) {r : Fin ℓ} (hr : (r : ℕ) ≠ j) (i : I) :
    blackCount (phiBottom s (coarsen j s f)) r i = blackCount (phiBottom s f) r i := by
  rw [blackCount_phiBottom hs (coarsen_mem hf), blackCount_phiBottom hs hf]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro _
  unfold coarsen
  split_ifs with hc
  · obtain ⟨-, hfp, -⟩ := hc
    omega
  · exact Iff.rfl

end Coarse

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

section Factor

omit [DecidableEq I] in
/-- In a red-ordered loading every block is at most `ℓ`. -/
theorem redsBefore_le_card {s : Seq μ} (hs : IsRedOrdered s) (p : Fin m) :
    redsBefore s.lbl p ≤ ℓ := by
  by_contra h
  have hlt : ℓ < redCount (List.ofFn s.lbl) :=
    lt_of_lt_of_le (not_le.1 h) (redsBefore_le_redCount s.lbl p)
  obtain ⟨q, hq, hq'⟩ := exists_redsBefore_eq s.lbl hlt
  rcases hl : s.lbl q with i | r
  · simp [hl] at hq
  · have := redsBefore_of_lbl_eq_inr hs hl
    have := r.2
    omega

omit [DecidableEq I] in
/-- **The block of a black strand at the bottom of `x_φ` is its assigned block.** -/
theorem redsBefore_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) {p : Fin m} (hp : (s.lbl p).isRight = false) :
    redsBefore (phiBottom s g).lbl (phiPerm s g p) = g p := by
  have hu := isRedOrdered_phiBottom hs hg
  have hgp : g p ≤ redsBefore s.lbl p := by
    have h := mem_assignList.1 hg p
    simp only [assignChoices, hp, Bool.false_eq_true, ite_false, List.mem_range] at h
    omega
  have hpu : ((phiBottom s g).lbl (phiPerm s g p)).isRight = false := by
    rw [lbl_smul_apply]; exact hp
  have key : ∀ r : Fin ℓ, redsBefore (phiBottom s g).lbl (phiPerm s g p) ≤ r ↔ g p ≤ r := by
    intro r
    obtain ⟨q, hq⟩ := exists_lbl_eq_inr s r
    have hqu : (phiBottom s g).lbl (phiPerm s g q) = .inr r := by rw [lbl_smul_apply]; exact hq
    rw [← lt_iff_redsBefore_le hu hpu hqu]
    have hkq : assignKey s.lbl g q = 2 * r + 1 := by
      rw [assignKey_red hg (by simp [hq]), redsBefore_of_lbl_eq_inr hs hq]
    have hkp : assignKey s.lbl g p = 2 * g p := assignKey_black g hp
    rw [keyPerm_lt_iff]
    omega
  have h1 := redsBefore_le_card hu (phiPerm s g p)
  have h2 := redsBefore_le_card hs p
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := (key ⟨redsBefore (phiBottom s g).lbl (phiPerm s g p), by omega⟩).1 le_rfl
    change g p ≤ redsBefore (phiBottom s g).lbl (phiPerm s g p) at this
    omega
  · have := (key ⟨g p, by omega⟩).2 le_rfl
    change redsBefore (phiBottom s g).lbl (phiPerm s g p) ≤ g p at this
    omega

/-- Two permutations of `Fin m` inducing the same order are equal. -/
theorem perm_eq_of_lt_iff {n : ℕ} {σ τ : Perm (Fin n)} (h : ∀ p q, σ p < σ q ↔ τ p < τ q) :
    σ = τ := by
  have hmono : StrictMono (σ * τ⁻¹ : Perm (Fin n)) := fun x y hxy => by
    simpa using (h (τ⁻¹ x) (τ⁻¹ y)).2 (by simpa using hxy)
  let e := hmono.orderIsoOfSurjective _ (σ * τ⁻¹).surjective
  have he : ∀ x, (σ * τ⁻¹) x = x := fun x => Fin.ext (Fin.coe_orderIso_apply e x)
  ext x
  have := he (τ x)
  rw [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply] at this
  exact congrArg Fin.val this

variable (j : ℕ)

omit [DecidableEq I] in
theorem assignKey_coarsen (s : Seq μ) (f : Fin m → ℕ) (x : Fin m) :
    assignKey s.lbl (coarsen j s f) x =
      if (s.lbl x).isRight = false ∧ f x = j ∧ j + 1 ≤ redsBefore s.lbl x then
        assignKey s.lbl f x + 2 else assignKey s.lbl f x := by
  unfold assignKey coarsen
  split_ifs <;> omega

/-- The local part of an assignment, on the bottom of its coarse part. -/
abbrev localPart (s : Seq μ) (f : Fin m → ℕ) : Fin m → ℕ :=
  f ∘ (phiPerm s (coarsen j s f)).symm

variable {j}

omit [DecidableEq I] in
private theorem redsBefore_mono (lbl : Fin m → I ⊕ Fin ℓ) {p q : Fin m} (h : p ≤ q) :
    redsBefore lbl p ≤ redsBefore lbl q := by
  rcases h.lt_or_eq with h | rfl
  · have := redsBefore_add_le lbl h
    omega
  · exact le_rfl

omit [DecidableEq I] in
/-- **The coarse part comes first**: `φ_f = φ_{f'} φ_g` for the coarse part `g` and the local
part `f'` of `f`. -/
theorem phiPerm_eq_mul {s : Seq μ} {f : Fin m → ℕ} (hf : f ∈ assignments s.lbl) :
    phiPerm s f = phiPerm (phiBottom s (coarsen j s f)) (localPart j s f) *
      phiPerm s (coarsen j s f) := by
  set g := coarsen j s f with hgdef
  have hk : ∀ x, assignKey (phiBottom s g).lbl (localPart j s f) (phiPerm s g x) =
      assignKey s.lbl f x := fun x => by
    unfold assignKey
    rw [lbl_smul_apply]
    simp only [localPart, Function.comp_apply, ← hgdef, Equiv.symm_apply_apply]
  have H : ∀ p q, assignKey s.lbl f p = assignKey s.lbl f q →
      (phiPerm s g p < phiPerm s g q ↔ p < q) := by
    intro p q hpq
    rw [keyPerm_lt_iff, hgdef, assignKey_coarsen, assignKey_coarsen]
    rcases Bool.eq_false_or_eq_true (s.lbl p).isRight with hbp | hbp
    · have hKp := assignKey_red hf hbp
      rcases Bool.eq_false_or_eq_true (s.lbl q).isRight with hbq | hbq
      · have hKq := assignKey_red hf hbq
        have hpq' : p = q := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := redsBefore_add_le s.lbl h
            simp only [hbp, ite_true] at this
            omega
          · have := redsBefore_add_le s.lbl h
            simp only [hbq, ite_true] at this
            omega
        subst hpq'
        simp
      · have := assignKey_black f hbq
        omega
    · rcases Bool.eq_false_or_eq_true (s.lbl q).isRight with hbq | hbq
      · have := assignKey_red hf hbq
        have := assignKey_black f hbp
        omega
      · have hKp := assignKey_black f hbp
        have hKq := assignKey_black f hbq
        simp only [hbp, hbq, true_and]
        rcases lt_trichotomy p q with h | rfl | h
        · have := redsBefore_mono s.lbl h.le
          simp only [h, iff_true, and_true]
          split_ifs <;> omega
        · simp
        · have := redsBefore_mono s.lbl h.le
          have hn : ¬ p < q := lt_asymm h
          simp only [hn, iff_false, and_false, or_false, not_lt]
          split_ifs <;> omega
  symm
  refine perm_eq_of_lt_iff fun p q => ?_
  rw [Perm.mul_apply, Perm.mul_apply, keyPerm_lt_iff, hk, hk,
    keyPerm_lt_iff (key := assignKey s.lbl f)]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (H p q h).1 h'⟩
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, (H p q h).2 h'⟩

omit [DecidableEq I] in
/-- The inversions of the coarse part are inversions of the assignment. -/
theorem invSet_phiPerm_coarsen_subset {s : Seq μ} {f : Fin m → ℕ} (hf : f ∈ assignments s.lbl) :
    invSet m (phiPerm s (coarsen j s f)) ⊆ invSet m (phiPerm s f) := by
  rintro ⟨p, q⟩ hpq
  rw [mem_invSet] at hpq ⊢
  dsimp only at hpq ⊢
  obtain ⟨hlt, hφ⟩ := hpq
  refine ⟨hlt, ?_⟩
  have hk : assignKey s.lbl (coarsen j s f) q < assignKey s.lbl (coarsen j s f) p := by
    rcases (keyPerm_lt_iff _).1 hφ with h | ⟨-, h⟩
    · exact h
    · exact absurd (h.trans hlt) (lt_irrefl _)
  refine (keyPerm_lt_iff _).2 (Or.inl ?_)
  rw [assignKey_coarsen, assignKey_coarsen] at hk
  have hm := redsBefore_mono s.lbl hlt.le
  rcases Bool.eq_false_or_eq_true (s.lbl p).isRight with hbp | hbp
  · have hKp := assignKey_red hf hbp
    simp only [hbp, Bool.true_eq_false, false_and, ite_false] at hk
    split_ifs at hk <;> omega
  · rcases Bool.eq_false_or_eq_true (s.lbl q).isRight with hbq | hbq
    · have hKq := assignKey_red hf hbq
      have hKp := assignKey_black f hbp
      simp only [hbq, Bool.true_eq_false, false_and, ite_false] at hk
      split_ifs at hk <;> omega
    · have hKp := assignKey_black f hbp
      have hKq := assignKey_black f hbq
      simp only [hbp, hbq, true_and] at hk
      split_ifs at hk <;> omega

omit [DecidableEq I] in
/-- Membership in the block assignments of a loading. -/
theorem mem_assignments_iff {lbl : Fin m → I ⊕ Fin ℓ} {f : Fin m → ℕ} :
    f ∈ assignments lbl ↔ ∀ p, ((lbl p).isRight → f p = redsBefore lbl p) ∧
      ((lbl p).isRight = false → f p ≤ redsBefore lbl p) := by
  rw [mem_assignList]
  refine forall_congr' fun p => ?_
  rcases Bool.eq_false_or_eq_true (lbl p).isRight with h | h
  · simp [assignChoices, h]
  · simp only [assignChoices, h, Bool.false_eq_true, ite_false, List.mem_range]
    constructor
    · intro h'; exact ⟨fun h'' => absurd h'' (by simp), fun _ => by omega⟩
    · intro h'; have := h'.2 trivial; omega

omit [DecidableEq I] in
/-- **An assignment is read off its `φ`**: the block of a black strand is its block at the
bottom. -/
theorem diagAssign_phiPerm {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) : diagAssign s (phiPerm s f) = f := by
  funext p
  have h := (mem_assignments_iff.1 hf p)
  unfold diagAssign
  split_ifs with hp
  · exact (h.1 hp).symm
  · have hp' : (s.lbl p).isRight = false := by simpa using hp
    have e := redsBefore_phiBottom hs hf hp'
    change redsBefore (phiBottom s f).lbl (phiPerm s f p) = f p at e
    change min (redsBefore s.lbl p) (redsBefore (phiBottom s f).lbl (phiPerm s f p)) = f p
    rw [e]
    exact min_eq_right (h.2 hp')

omit [DecidableEq I] in
/-- Red strands keep their block at the bottom of an assignment. -/
theorem redsBefore_phiBottom_red {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) {p : Fin m} (hp : (s.lbl p).isRight) :
    redsBefore (phiBottom s g).lbl (phiPerm s g p) = redsBefore s.lbl p := by
  obtain ⟨r, hr⟩ : ∃ r, s.lbl p = .inr r := by
    rcases h : s.lbl p with i | r
    · simp [h] at hp
    · exact ⟨r, rfl⟩
  rw [redsBefore_of_lbl_eq_inr (isRedOrdered_phiBottom hs hg) ((lbl_smul_apply s _ p).trans hr),
    redsBefore_of_lbl_eq_inr hs hr]

omit [DecidableEq I] in
/-- The local part is a block assignment of the bottom of the coarse part. -/
theorem localPart_mem {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) :
    localPart j s f ∈ assignments (phiBottom s (coarsen j s f)).lbl := by
  have hg := coarsen_mem (j := j) hf
  refine mem_assignments_iff.2 fun x => ?_
  obtain ⟨y, rfl⟩ := (phiPerm s (coarsen j s f)).surjective x
  have hl := lbl_smul_apply s (phiPerm s (coarsen j s f)) y
  simp only [localPart, Function.comp_apply, Equiv.symm_apply_apply]
  rw [show (phiBottom s (coarsen j s f)).lbl (phiPerm s (coarsen j s f) y) = s.lbl y from hl]
  have h := mem_assignments_iff.1 hf y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [redsBefore_phiBottom_red hs hg hy]; exact h.1 hy
  · rw [redsBefore_phiBottom hs hg hy]; exact coarsen_le s f y

omit [DecidableEq I] in
/-- The local part is local. -/
theorem isLocal_localPart {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) :
    IsLocal j (phiBottom s (coarsen j s f)) (localPart j s f) := by
  have hg := coarsen_mem (j := j) hf
  intro x hx
  obtain ⟨y, rfl⟩ := (phiPerm s (coarsen j s f)).surjective x
  have hl : (phiBottom s (coarsen j s f)).lbl (phiPerm s (coarsen j s f) y) = s.lbl y :=
    lbl_smul_apply s _ y
  rw [hl] at hx
  simp only [localPart, Function.comp_apply, Equiv.symm_apply_apply]
  rw [redsBefore_phiBottom hs hg hx]
  unfold coarsen
  split_ifs with hc
  · exact Or.inr ⟨rfl, hc.2.1⟩
  · exact Or.inl rfl

omit [DecidableEq I] in
/-- **The bottom of an assignment is the bottom of its local part.** -/
theorem phiBottom_eq_phiBottom_localPart {s : Seq μ} {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) :
    phiBottom s f = phiBottom (phiBottom s (coarsen j s f)) (localPart j s f) := by
  change phiPerm s f • s = _ • (_ • s)
  rw [phiPerm_eq_mul (j := j) hf, mul_smul]

omit [DecidableEq I] in
/-- A local assignment after a coarse one is an assignment. -/
theorem comp_phiPerm_mem {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) {f' : Fin m → ℕ}
    (hf' : f' ∈ assignments (phiBottom s g).lbl) :
    f' ∘ phiPerm s g ∈ assignments s.lbl := by
  refine mem_assignments_iff.2 fun y => ?_
  have hl : (phiBottom s g).lbl (phiPerm s g y) = s.lbl y := lbl_smul_apply s _ y
  have h := mem_assignments_iff.1 hf' (phiPerm s g y)
  rw [hl] at h
  have h' := mem_assignments_iff.1 hg y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Function.comp_apply, h.1 hy, redsBefore_phiBottom_red hs hg hy]
  · have := h.2 hy
    rw [redsBefore_phiBottom hs hg hy] at this
    exact this.trans (h'.2 hy)

omit [DecidableEq I] in
/-- The coarse part of a local assignment after a coarse one is the coarse one. -/
theorem coarsen_comp_phiPerm {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) (hc : IsCoarse j s g) {f' : Fin m → ℕ}
    (hf' : f' ∈ assignments (phiBottom s g).lbl) (hl : IsLocal j (phiBottom s g) f') :
    coarsen j s (f' ∘ phiPerm s g) = g := by
  funext y
  have hlb : (phiBottom s g).lbl (phiPerm s g y) = s.lbl y := lbl_smul_apply s _ y
  have h' := mem_assignments_iff.1 hg y
  unfold coarsen
  rcases Bool.eq_false_or_eq_true (s.lbl y).isRight with hy | hy
  · simp only [hy, Bool.true_eq_false, false_and, ite_false, Function.comp_apply]
    have h := (mem_assignments_iff.1 hf' (phiPerm s g y)).1 (by rw [hlb]; exact hy)
    rw [h, redsBefore_phiBottom_red hs hg hy, h'.1 hy]
  · have hloc := hl (phiPerm s g y) (by rw [hlb]; exact hy)
    rw [redsBefore_phiBottom hs hg hy] at hloc
    have hcy := hc y hy
    simp only [hy, true_and, Function.comp_apply]
    rcases hloc with h | ⟨h1, h2⟩
    · rw [h]
      split_ifs with hc'
      · exact absurd (hcy hc'.1) (by omega)
      · rfl
    · rw [h2]
      split_ifs with hc'
      · exact h1.symm
      · exact absurd ⟨rfl, by have := h'.2 hy; omega⟩ hc'


omit [DecidableEq I] in
/-- The local part of a local assignment after a coarse one is the local assignment. -/
theorem localPart_comp_phiPerm {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) (hc : IsCoarse j s g) {f' : Fin m → ℕ}
    (hf' : f' ∈ assignments (phiBottom s g).lbl) (hl : IsLocal j (phiBottom s g) f') :
    localPart j s (f' ∘ phiPerm s g) = f' := by
  funext x
  simp only [localPart, coarsen_comp_phiPerm hs hg hc hf' hl, Function.comp_apply,
    Equiv.apply_symm_apply]

omit [DecidableEq I] in
/-- An assignment is its local part after its coarse part. -/
theorem localPart_comp_phiPerm_coarsen (s : Seq μ) (f : Fin m → ℕ) :
    localPart j s f ∘ phiPerm s (coarsen j s f) = f := by
  funext x
  simp only [localPart, Function.comp_apply, Equiv.symm_apply_apply]

omit [DecidableEq I] in
open scoped Classical in
/-- **Block assignments as pairs of a coarse and a local assignment**: a sum over the block
assignments of `s`, of a function of the bottom, is a sum over the coarse assignments `g` and
the local assignments of `φ_g • s`. -/
theorem sum_assignments_eq_sum_coarse_local {β : Type*} [AddCommMonoid β] {s : Seq μ}
    (hs : IsRedOrdered s) (D : Seq μ → β) :
    ∑ f ∈ (assignments s.lbl).toFinset, D (phiBottom s f) =
      ∑ g ∈ (assignments s.lbl).toFinset.filter (IsCoarse j s),
        ∑ f' ∈ (assignments (phiBottom s g).lbl).toFinset.filter (IsLocal j (phiBottom s g)),
          D (phiBottom (phiBottom s g) f') := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun f => ⟨coarsen j s f, localPart j s f⟩)
    (fun x => x.2 ∘ phiPerm s x.1) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    have hf' := List.mem_toFinset.1 hf
    simp only [Finset.mem_sigma, Finset.mem_filter, List.mem_toFinset]
    exact ⟨⟨coarsen_mem hf', isCoarse_coarsen s f hf'⟩, localPart_mem hs hf',
      isLocal_localPart hs hf'⟩
  · rintro ⟨g, f'⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, List.mem_toFinset] at h
    exact List.mem_toFinset.2 (comp_phiPerm_mem hs h.1.1 h.2.1)
  · intro f _
    exact localPart_comp_phiPerm_coarsen s f
  · rintro ⟨g, f'⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, List.mem_toFinset] at h
    simp only [Sigma.mk.injEq]
    exact ⟨coarsen_comp_phiPerm hs h.1.1 h.1.2 h.2.1 h.2.2,
      heq_of_eq (localPart_comp_phiPerm hs h.1.1 h.1.2 h.2.1 h.2.2)⟩
  · intro f hf
    rw [phiBottom_eq_phiBottom_localPart (j := j) (List.mem_toFinset.1 hf)]

/-- A loading lies below the bottom of each of its block assignments. -/
theorem stendhalLE_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) : StendhalLE s (phiBottom s f) := by
  intro r i
  rw [blackCount_phiBottom hs hf, blackCount_eq_card_redsBefore hs]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  refine ⟨hp.1, le_trans ?_ hp.2⟩
  exact (mem_assignments_iff.1 hf p).2 (by simp [hp.1])

private theorem blackCount_lt_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) {p : Fin m} {i : I} (hp : s.lbl p = .inl i) {r : Fin ℓ}
    (h1 : f p ≤ r) (h2 : (r : ℕ) < redsBefore s.lbl p) :
    blackCount s r ≠ blackCount (phiBottom s f) r := by
  intro h
  have h' := congrFun h i
  rw [blackCount_phiBottom hs hf, blackCount_eq_card_redsBefore hs] at h'
  refine absurd h' (Nat.ne_of_lt (Finset.card_lt_card ⟨fun q hq => ?_, fun hsub => ?_⟩))
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨hq.1, le_trans ((mem_assignments_iff.1 hf q).2 (by simp [hq.1])) hq.2⟩
  · have := hsub (show p ∈ Finset.univ.filter fun q => s.lbl q = .inl i ∧ f q ≤ r by simp [hp, h1])
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    omega

/-- A local assignment keeps the black counts at every red strand except `λ_j`. -/
theorem blackCount_phiBottom_of_isLocal {u : Seq μ} (hu : IsRedOrdered u) {f' : Fin m → ℕ}
    (hf' : f' ∈ assignments u.lbl) (hl : IsLocal j u f') {r : Fin ℓ} (hr : (r : ℕ) ≠ j) :
    blackCount (phiBottom u f') r = blackCount u r := by
  funext i
  rw [blackCount_phiBottom hu hf', blackCount_eq_card_redsBefore hu]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro hp
  rcases hl p (by simp [hp]) with h | ⟨h1, h2⟩ <;> omega

/-- An assignment that is not local moves a black strand across a red strand other than
`λ_j`. -/
theorem exists_blackCount_ne_of_not_isLocal {u : Seq μ} (hu : IsRedOrdered u) {f' : Fin m → ℕ}
    (hf' : f' ∈ assignments u.lbl) (hl : ¬ IsLocal j u f') :
    ∃ r : Fin ℓ, (r : ℕ) ≠ j ∧ blackCount u r ≠ blackCount (phiBottom u f') r := by
  simp only [IsLocal, not_forall, not_or, not_and] at hl
  obtain ⟨p, hb, hne, hj⟩ := hl
  obtain ⟨i, hi⟩ : ∃ i, u.lbl p = .inl i := by
    rcases h : u.lbl p with i | r
    · exact ⟨i, rfl⟩
    · simp [h] at hb
  have hle := (mem_assignments_iff.1 hf' p).2 hb
  have hcard := redsBefore_le_card hu p
  by_cases hfj : f' p = j
  · have hrb : j + 2 ≤ redsBefore u.lbl p := by
      have := fun h => hj h hfj
      omega
    exact ⟨⟨j + 1, by omega⟩, by simp, blackCount_lt_phiBottom hu hf' hi (by simp; omega)
      (by simp; omega)⟩
  · exact ⟨⟨f' p, by omega⟩, hfj, blackCount_lt_phiBottom hu hf' hi le_rfl (by simp; omega)⟩

end Factor

section Root

variable {j : ℕ} {a b : Fin ℓ}

/-- The root of a red-ordered loading, at the merged pair `b < a`, reads the black counts at
`λ_b` for both labels of the pair. -/
theorem adjacentBlockRoot_eq_of_isRedOrdered (hba : b < a) {t : Seq μ} (ht : IsRedOrdered t)
    (r : Fin ℓ) : adjacentBlockRoot a b t r = blackCount t (if r = a ∨ r = b then b else r) := by
  unfold adjacentBlockRoot
  split_ifs with hr
  · funext i
    unfold blockBlackCount blackCount
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine and_congr_right fun _ => ⟨fun h y hy => h y b (Or.inr rfl) hy, ?_⟩
    rintro h y r' (rfl | rfl) hy
    · obtain ⟨z, hz⟩ := exists_lbl_eq_inr t b
      refine (h z hz).trans ?_
      rcases lt_trichotomy z y with h' | rfl | h'
      · exact h'
      · rw [hz] at hy; cases hy; exact absurd hba (lt_irrefl _)
      · exact absurd (ht y z _ _ h' hy hz) (not_lt.2 hba.le)
    · exact h y hy
  · funext i
    simp [blockBlackCount_singleton]

/-- Red-ordered loadings with the same black counts away from `λ_j` have the same root at a
merged pair `b < a = j`. -/
theorem adjacentBlockRoot_eq_of_blackCount (hba : b < a) (ha : (a : ℕ) = j) {t t' : Seq μ}
    (ht : IsRedOrdered t) (ht' : IsRedOrdered t')
    (h : ∀ r : Fin ℓ, (r : ℕ) ≠ j → blackCount t r = blackCount t' r) :
    adjacentBlockRoot a b t = adjacentBlockRoot a b t' := by
  funext r
  rw [adjacentBlockRoot_eq_of_isRedOrdered hba ht, adjacentBlockRoot_eq_of_isRedOrdered hba ht']
  refine h _ ?_
  split_ifs with hr
  · have := Fin.lt_def.1 hba; omega
  · intro hj; exact hr (Or.inl (Fin.ext (hj.trans ha.symm)))

/-- A red-ordered loading above another, with a different black count away from `λ_j`, has a
strictly larger root at a merged pair `b < a = j`. -/
theorem adjacentBlockRoot_lt_of_blackCount (hba : b < a) (ha : (a : ℕ) = j) {t t' : Seq μ}
    (ht : IsRedOrdered t) (ht' : IsRedOrdered t') (hle : StendhalLE t t')
    (h : ∃ r : Fin ℓ, (r : ℕ) ≠ j ∧ blackCount t r ≠ blackCount t' r) :
    adjacentBlockRoot a b t < adjacentBlockRoot a b t' := by
  refine lt_of_le_of_ne (fun r i => ?_) fun he => ?_
  · rw [adjacentBlockRoot_eq_of_isRedOrdered hba ht, adjacentBlockRoot_eq_of_isRedOrdered hba ht']
    exact hle _ i
  · obtain ⟨r, hr, hne⟩ := h
    have e := congrFun he r
    rw [adjacentBlockRoot_eq_of_isRedOrdered hba ht,
      adjacentBlockRoot_eq_of_isRedOrdered hba ht'] at e
    have hra : r ≠ a := fun h' => hr (by rw [h', ha])
    by_cases hrb : r = b
    · subst hrb; simp only [or_true, ite_true] at e; exact hne e
    · simp only [hra, hrb, or_self, ite_false] at e; exact hne e

end Root

end Categorification.Stendhal
