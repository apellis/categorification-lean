/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams

/-!
# Coarse block assignments

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8: the kernel of a loading
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
`φ_g • s` (`coarseLocalEquiv`).

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

end Factor

end Categorification.Stendhal
