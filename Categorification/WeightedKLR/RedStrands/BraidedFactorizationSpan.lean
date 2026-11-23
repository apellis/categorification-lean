/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationExits

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: spanning by frame classes

Part of the proof of Webster, arXiv:1309.3796v2, Lemma 6.5, for one red-red crossing: the red
strands of `κ₀ = L ++ a :: b :: M` and `κ₁ = L ++ b :: a :: M` differ by exchanging `a` and `b`,
and `b` comes before `a` in `κ₂`. Every class `ψ_α ⊗ ψ_β x^p e(i)` is, modulo lower degree, a
combination of frame classes `frameClass τ f i` with `ℓ(τ) ≤ |α| + |β|` (`low_le_frameSpan`):
non-reduced words lower the degree, reduced words can be replaced by the chosen ones, pairs whose
lengths do not add lie in lower degree (`pgen_mem_low_of_lt`) and additive pairs agree with the
frame class of their product (`pgen_sub_frameClass_mem_low`). Hence the frame classes span the
tensor product (`frameSpan_eq_top`).
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)} {L M : List (Fin ℓ)} {a b : Fin ℓ}

/-- The span of the frame classes of permutations of length at most `n`. -/
noncomputable def frameSpan (ρ : Perm (Fin m) → List ℕ) (n : ℕ) :
    Submodule k (CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂)
      (redProj k Q Λ ν κ₁) (redProj k Q Λ ν κ₀)) :=
  Submodule.span k {t | ∃ τ f i, length m τ ≤ n ∧ t = frameClass ρ τ f i}

theorem frameSpan_mono (ρ : Perm (Fin m) → List ℕ) {n n' : ℕ} (h : n ≤ n') :
    frameSpan (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ n ≤ frameSpan ρ n' :=
  Submodule.span_mono fun _ ⟨τ, f, i, hτ, ht⟩ => ⟨τ, f, i, hτ.trans h, ht⟩

theorem frameClass_mem_frameSpan (ρ : Perm (Fin m) → List ℕ) (τ : Perm (Fin m))
    (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ τ f i ∈
      frameSpan ρ (length m τ) :=
  Submodule.subset_span ⟨τ, f, i, le_rfl, rfl⟩

omit [DecidableEq I] in
/-- If `b` comes before `a` in the red strands of `w • i`, then `w` inverts the red strands
`q < p` of `i` labelled `a` and `b`. -/
theorem mem_invSet_of_sublist_redWord {i : Seq μ} {w : Perm (Fin m)}
    (h : [b, a].Sublist (redWord (w • i))) {q p : Fin m} (hqp : q < p)
    (hq : i.lbl q = .inr a) (hp : i.lbl p = .inr b) : (q, p) ∈ invSet m w := by
  rw [mem_invSet_pair]
  refine ⟨hqp, ?_⟩
  have hP := (redWord_pairwise_one (w • i)).sublist h
  rw [List.pairwise_pair] at hP
  exact hP (w p) (w q) (by rw [lbl_smul]; simpa using hp) (by rw [lbl_smul]; simpa using hq)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ)
include hρ

/-- **Reduction of `pgen` to frame classes.** The class `pgen u v` vanishes, or `v` has a
crossing and `pgen u v` is a frame class of length at most `ℓ(u) + ℓ(v)` modulo lower degree. -/
theorem pgen_eq_zero_or_mem_frameSpan (h0 : κ₀ = L ++ a :: b :: M)
    (h1 : κ₁ = L ++ b :: a :: M) (h2 : [b, a].Sublist κ₂) (u v : Perm (Fin m))
    (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v f i = 0 ∨
      (1 ≤ length m v ∧ pgen (Q := Q) (Λ := Λ) ρ u v f i ∈ frameSpan ρ (length m u + length m v) ⊔
        low κ₂ κ₁ κ₀ (length m u + length m v - 1)) := by
  by_cases hi : redWord i = κ₀
  swap
  · exact Or.inl (pgen_eq_zero_right u v f i hi)
  by_cases hr : redWord (v • i) = κ₁
  swap
  · exact Or.inl (pgen_eq_zero hρ u v f i hr)
  by_cases hl2 : redWord ((u * v) • i) = κ₂
  swap
  · exact Or.inl (pgen_eq_zero_left hρ u v f i hl2)
  right
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr i a
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr i b
  have hi' : redWord i = L ++ a :: b :: M := hi.trans h0
  have hqp := lt_of_redWord_eq_append hi' hq hp
  have hqR : q ∈ redSet i := by simp [redSet, hq]
  have hpR : p ∈ redSet i := by simp [redSet, hp]
  have hsw := (redWord_smul_eq_swap_iff' hi' hq hp v).1 (hr.trans h1)
  have hvq : (q, p) ∈ invSet m v := (hsw q p hqR hpR).2 ⟨rfl, rfl⟩
  have hv1 : 1 ≤ length m v := by
    rw [length_eq_invCount, invCount]
    exact Finset.card_pos.2 ⟨_, hvq⟩
  refine ⟨hv1, ?_⟩
  have huv : (q, p) ∈ invSet m (u * v) :=
    mem_invSet_of_sublist_redWord (hl2 ▸ h2) hqp hq hp
  rcases lt_or_eq_of_le (length_mul_le u v) with hlt | heq
  · refine Submodule.mem_sup_right (pgen_mem_low_of_lt hρ f i ?_ hlt)
    intro s t hs ht hst
    obtain ⟨rfl, rfl⟩ := (hsw s t (by simpa [redSet] using hs) (by simpa [redSet] using ht)).1 hst
    exact huv
  · have hd := pgen_sub_frameClass_mem_low (Q := Q) (Λ := Λ) (κ₂ := κ₂) hρ h0 h1 heq.symm f i
      hi hr
    have hF : frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ (u * v) f i ∈
        frameSpan ρ (length m u + length m v) :=
      frameSpan_mono ρ heq.le (frameClass_mem_frameSpan ρ (u * v) f i)
    rw [← sub_add_cancel (pgen ρ u v f i) (frameClass ρ (u * v) f i)]
    exact add_mem (Submodule.mem_sup_right hd) (Submodule.mem_sup_left hF)

/-- Every generator of `low` is a combination of frame classes modulo lower degree. -/
theorem gen_mem_frameSpan_sup (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) {α β : List ℕ} (hα : ValidWord m α) (hβ : ValidWord m β)
    (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw α) (KLRAlgebra.ψw β * KLRAlgebra.pol f * KLRAlgebra.e i) ∈
      frameSpan (Q := Q) (Λ := Λ) ρ (α.length + β.length) ⊔
        low κ₂ κ₁ κ₀ (α.length + β.length - 1) := by
  by_cases ha : IsReduced m α
  swap
  · obtain ⟨σ, hσ, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hα ha
    refine Submodule.mem_sup_right ?_
    have h₁ := gen_sub_mem_low_of_braidEquiv_left (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ) hσ hα hβ f i
    have h₂ := gen_mem_low_of_hasRepeat_left (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ) hrep hβ f i
    rw [← hσ.length_eq] at h₂
    simpa using add_mem h₁ h₂
  by_cases hb : IsReduced m β
  swap
  · obtain ⟨σ, hσ, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hβ hb
    refine Submodule.mem_sup_right ?_
    have h₁ := gen_sub_mem_low_of_braidEquiv_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ) hσ hα f i
    have h₂ := gen_mem_low_of_hasRepeat_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
      (Q := Q) (Λ := Λ) hrep hα f i
    rw [← hσ.length_eq] at h₂
    simpa using add_mem h₁ h₂
  have hu : BraidEquiv α (ρ (wordProd m α)) :=
    braidEquiv_of_isReduced ha (hρ _).1 (hρ _).2.symm
  have hv : BraidEquiv β (ρ (wordProd m β)) :=
    braidEquiv_of_isReduced hb (hρ _).1 (hρ _).2.symm
  have h₁ := gen_sub_mem_low_of_braidEquiv_left (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
    (Q := Q) (Λ := Λ) hu hα hβ f i
  have h₂ := gen_sub_mem_low_of_braidEquiv_right (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀)
    (Q := Q) (Λ := Λ) hv (hρ (wordProd m α)).1.1 f i
  rw [← hu.length_eq] at h₂
  have key := add_mem h₁ h₂
  rw [sub_add_sub_cancel] at key
  have hlen : α.length + β.length = length m (wordProd m α) + length m (wordProd m β) := by
    rw [ha.2, hb.2]
  rw [← sub_add_cancel (gen κ₂ κ₁ κ₀ _ _) (pgen ρ (wordProd m α) (wordProd m β) f i)]
  refine add_mem (Submodule.mem_sup_right key) ?_
  rcases pgen_eq_zero_or_mem_frameSpan hρ h0 h1 h2 (wordProd m α) (wordProd m β) f i with
    h | ⟨_, h⟩
  · rw [h]; exact zero_mem _
  · rwa [hlen]

/-- **The frame classes span modulo the filtration.** Every class of degree at most `n` is a
combination of frame classes of permutations of length at most `n`. -/
theorem low_le_frameSpan (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) (n : ℕ) :
    low (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ n ≤ frameSpan ρ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  refine Submodule.span_le.2 ?_
  rintro t ⟨α, β, f, i, hα, hβ, hn, rfl⟩
  by_cases hN : α.length + β.length = 0
  · have hα0 : α = [] := List.length_eq_zero_iff.1 (by omega)
    have hβ0 : β = [] := List.length_eq_zero_iff.1 (by omega)
    subst hα0 hβ0
    have hρ1 : ρ 1 = [] :=
      List.length_eq_zero_iff.1 (by rw [(hρ 1).1.2, (hρ 1).2, length_one])
    have he : gen κ₂ κ₁ κ₀ (KLRAlgebra.ψw []) (KLRAlgebra.ψw [] * KLRAlgebra.pol f *
        KLRAlgebra.e i) = pgen (Q := Q) (Λ := Λ) ρ 1 1 f i := by
      rw [pgen, hρ1]
    rw [SetLike.mem_coe, he]
    rcases pgen_eq_zero_or_mem_frameSpan hρ h0 h1 h2 1 1 f i with h | ⟨h, _⟩
    · rw [h]; exact zero_mem _
    · simp at h
  have hg := gen_mem_frameSpan_sup (Q := Q) (Λ := Λ) hρ h0 h1 h2 hα hβ f i
  exact sup_le (frameSpan_mono ρ hn) ((ih _ (by omega)).trans (frameSpan_mono ρ (by omega))) hg

/-- **The frame classes span the tensor product.** -/
theorem frameSpan_eq_top (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) :
    ⨆ n, frameSpan (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ n = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  obtain ⟨n, hn⟩ := exists_mem_low (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) t
  exact Submodule.mem_iSup_of_mem n (low_le_frameSpan hρ h0 h1 h2 n hn)

end BraidedStendhalAlgebra

end Categorification.Stendhal
