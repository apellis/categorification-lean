/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationSpan
import Categorification.KLR.Spanning
import Categorification.WeightedKLR.Mackey.ParabolicBasis

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: one red crossing

Webster, arXiv:1309.3796v2, Lemma 6.5, for one red-red crossing: the red strands of
`κ₀ = L ++ a :: b :: M` and `κ₁ = L ++ b :: a :: M` differ by exchanging `a` and `b`, and `b`
comes before `a` in `κ₂`. Then multiplication `B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` over the
middle corner is an isomorphism (`tensorMultEquiv`).

The proof compares the frame classes with the basis of Proposition 6.4 (`cornerBasis`). Every
corner basis vector `ψ_{ρ(τ)} x^u e(i)` has a frame `v` (a permutation below `τ` in the weak
order performing the red crossing, `exists_frame`), and multiplication sends its frame class
`ψ_{ρ(τ v⁻¹)} ⊗ ψ_{ρ(v)} x^u e(i)` to the basis vector plus shorter basis vectors
(`tensorMult_frameClass_sub_mem`). So the images of the frame classes form a basis
(`frameBasis`); since the frame classes span the tensor product (`frameSpan_eq_top`),
multiplication is bijective.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)} {L M : List (Fin ℓ)} {a b : Fin ℓ}

/-- The index set of the basis of `B̃(κ', κ)` of Proposition 6.4. -/
abbrev RedCornerIdx (ν : Multiset I) (κ' κ : List (Fin ℓ)) : Type _ :=
  {b : BlackIdx (ℓ := ℓ) ν // redWord (b.1.2.1 • b.1.1) = κ' ∧ redWord b.1.1 = κ}

omit [DecidableEq I] in
/-- **Existence of frames.** If the red strands of `i` and `τ • i` read `κ₀` and `κ₂`, then `τ`
has a frame: a permutation `v` below `τ` in the weak order with red strands of `v • i`
reading `κ₁`. -/
theorem exists_frame (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) {τ : Perm (Fin m)} {i : Seq μ} (hi : redWord i = κ₀)
    (hτ : redWord (τ • i) = κ₂) :
    ∃ v, invSet m v ⊆ invSet m τ ∧ redWord (v • i) = κ₁ := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr i a
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr i b
  have hi' : redWord i = L ++ a :: b :: M := hi.trans h0
  have hqp := lt_of_redWord_eq_append hi' hq hp
  have hT : (q, p) ∈ invSet m τ :=
    mem_invSet_of_sublist_redWord (by rw [hτ]; exact h2) hqp hq hp
  obtain ⟨e, he⟩ : ∃ e, IsExit τ (redSet i) q p e := exists_isExit hqp hT fun t ht hqt htp =>
    not_lt_of_redWord_eq_append hi' hq hp (by simpa [redSet] using ht) hqt htp
  have hx : (e q : ℕ) + 1 < m := by have := he.adj; have := (e p).2; omega
  have hS := he.isSwapBelow hqp hT hx
  exact ⟨_, hS.le, h1 ▸ (redWord_smul_eq_swap_iff' hi' hq hp _).2 hS.red⟩

variable (k Q Λ ν κ₂ κ₁ κ₀) in
/-- Multiplication `B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` over the middle corner. -/
noncomputable def tensorMult :
    CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁)
      (redProj k Q Λ ν κ₀) →ₗ[k] cornerSpace k Q Λ ν κ₂ κ₀ :=
  LinearMap.codRestrict _ (CornerTensor.mult (isIdempotentElem_redProj κ₂)
    (isIdempotentElem_redProj κ₁) (isIdempotentElem_redProj κ₀)) fun t => by
    induction t using CornerTensor.induction_on with
    | tmul x y =>
      rw [CornerTensor.mult_tmul]
      exact ⟨x * redProj k Q Λ ν κ₁ * y, by simp [redProj, mul_assoc]⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht

theorem coe_tensorMult_tmul (x y : BraidedStendhalAlgebra k Q Λ ν) :
    (tensorMult k Q Λ ν κ₂ κ₁ κ₀ (CornerTensor.tmul x y) : BraidedStendhalAlgebra k Q Λ ν) =
      redProj k Q Λ ν κ₂ * x * redProj k Q Λ ν κ₁ * y * redProj k Q Λ ν κ₀ := by
  simp [tensorMult, CornerTensor.mult_tmul]

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ)

include hρ in
/-- The product of a pair `ψ_{ρ(u)} ⊗ ψ_{ρ(v)} x^p e(i)`. -/
theorem coe_tensorMult_pgen (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (hv : redWord (v • i) = κ₁) :
    (tensorMult k Q Λ ν κ₂ κ₁ κ₀ (pgen ρ u v p i) : BraidedStendhalAlgebra k Q Λ ν) =
      ofKLR k Q Λ ν (redIdem k Q Λ κ₂ *
        (KLRAlgebra.ψw (ρ u ++ ρ v) * KLRAlgebra.pol p * KLRAlgebra.e i) *
          redIdem k Q Λ κ₀) := by
  have hy := e_mul_std (Q := Q) (Λ := Λ) (ρ v) p i
  rw [(hρ v).2] at hy
  have h₁ : (redIdem k Q Λ κ₁ * (KLRAlgebra.ψw (ρ v) * KLRAlgebra.pol p * KLRAlgebra.e i) :
      R) = KLRAlgebra.ψw (ρ v) * KLRAlgebra.pol p * KLRAlgebra.e i := by
    rw [← hy, ← mul_assoc, redIdem_mul_e, ite_eq_left hv]
  rw [pgen, gen, coe_tensorMult_tmul]
  simp only [redProj, ← map_mul]
  congr 1
  have h₁' := congrArg (· * redIdem k Q Λ κ₀) h₁
  simp only [mul_assoc] at h₁'
  rw [KLRAlgebra.ψw_append]
  simp only [mul_assoc]
  rw [h₁']

variable (hQ : KLRSymm Q)

include hρ in
/-- `ofKLR (redIdem κ₂ * z * redIdem κ₀)`, for `z` of crossing degree at most `n`, is a
combination of corner basis vectors of length at most `n`. -/
theorem ofKLR_corner_mem_span {n : ℕ} {z : R} (hz : z ∈ KLRAlgebra.filt k (stendhalQ Q Λ) μ n) :
    ofKLR k Q Λ ν (redIdem k Q Λ κ₂ * z * redIdem k Q Λ κ₀) ∈
      Submodule.span k (Set.range fun c : {c : RedCornerIdx ν κ₂ κ₀ //
        length m c.1.1.2.1 ≤ n} =>
          (cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀ c.1 : BraidedStendhalAlgebra k Q Λ ν)) := by
  rw [KLRAlgebra.filt_eq_span (fun _ _ h h' e => braidEquiv_of_isReduced h h' e)
    (fun _ hv hr => exists_braidEquiv_hasRepeat_of_not_isReduced hv hr) ρ hρ n] at hz
  set F : R →ₗ[k] BraidedStendhalAlgebra k Q Λ ν :=
    (ofKLR k Q Λ ν).toLinearMap ∘ₗ LinearMap.mulLeft k (redIdem k Q Λ κ₂) ∘ₗ
      LinearMap.mulRight k (redIdem k Q Λ κ₀) with hF
  have hFz : ∀ z : R, F z = ofKLR k Q Λ ν (redIdem k Q Λ κ₂ * z * redIdem k Q Λ κ₀) := by
    intro z; simp [hF, mul_assoc]
  rw [← hFz, ← Submodule.mem_comap]
  refine Submodule.span_le.2 ?_ hz
  rintro _ ⟨w, u, j, hw, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hFz, redIdem_mul_std, (hρ w).2]
  split_ifs with hc
  swap
  · rw [map_zero]; exact zero_mem _
  by_cases hu : ∀ a, (j.lbl a).isRight → u a = 0
  · refine Submodule.subset_span ⟨⟨⟨⟨(j, w, u), hu⟩, hc⟩, hw⟩, ?_⟩
    exact cornerBasis_apply hQ ρ hρ κ₂ κ₀ _
  · push Not at hu
    obtain ⟨a', ha, hu'⟩ := hu
    rw [ofKLR_std_eq_zero _ _ _ a' ha hu']
    exact zero_mem _

include hρ in
/-- **Unitriangularity.** The product of the frame class of a corner basis vector is that basis
vector plus a combination of shorter ones. -/
theorem tensorMult_frameClass_sub_mem (h0 : κ₀ = L ++ a :: b :: M)
    (h1 : κ₁ = L ++ b :: a :: M) (h2 : [b, a].Sublist κ₂) (c : RedCornerIdx ν κ₂ κ₀) :
    tensorMult k Q Λ ν κ₂ κ₁ κ₀ (frameClass ρ c.1.1.2.1 (monomial c.1.1.2.2 1) c.1.1.1) -
        cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀ c ∈
      Submodule.span k (cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀ ''
        {c' | length m c'.1.1.2.1 < length m c.1.1.2.1}) := by
  obtain ⟨⟨⟨i, τ, u⟩, hu⟩, hτ, hi⟩ := c
  dsimp only at hτ hi ⊢
  have hex := exists_frame h0 h1 h2 hi hτ
  obtain ⟨hv1, hv2⟩ := hex.choose_spec
  rw [frameClass, dite_eq_left hex]
  set v := hex.choose
  have hl : length m (τ * v⁻¹) + length m v = length m τ := length_add_of_invSet_subset hv1
  -- `τ` is not the identity: it inverts the red strands labelled `a` and `b`.
  have hpos : 0 < length m τ := by
    obtain ⟨q, hq⟩ := exists_lbl_eq_inr i a
    obtain ⟨p, hp⟩ := exists_lbl_eq_inr i b
    have hi' : redWord i = L ++ a :: b :: M := hi.trans h0
    have hT : (q, p) ∈ invSet m τ := mem_invSet_of_sublist_redWord (by rw [hτ]; exact h2)
      (lt_of_redWord_eq_append hi' hq hp) hq hp
    rw [length_eq_invCount, invCount]
    exact Finset.card_pos.2 ⟨_, hT⟩
  have hA : IsReduced m (ρ (τ * v⁻¹) ++ ρ v) := by
    refine ⟨validWord_append.2 ⟨(hρ _).1.1, (hρ _).1.1⟩, ?_⟩
    rw [List.length_append, wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right,
      (hρ _).1.2, (hρ _).1.2, (hρ _).2, (hρ _).2, hl]
  have hE : BraidEquiv (ρ (τ * v⁻¹) ++ ρ v) (ρ τ) := braidEquiv_of_isReduced hA (hρ τ).1
    (by rw [wordProd_append, (hρ _).2, (hρ _).2, (hρ _).2, inv_mul_cancel_right])
  have hD := KLRAlgebra.sub_mem_of_braidEquiv hE
    (KLRAlgebra.pol_mul_e_mem (Q := stendhalQ Q Λ) (monomial u 1) i 0)
  rw [List.length_append, (hρ _).1.2, (hρ _).1.2, (hρ _).2, (hρ _).2, hl, Nat.add_zero] at hD
  have hS := ofKLR_corner_mem_span (κ₂ := κ₂) (κ₀ := κ₀) hρ hQ hD
  refine Module.Basis.mem_span_image_of_coe_mem _ _ ?_
  refine Submodule.span_mono (s := Set.range (fun c : {c : RedCornerIdx ν κ₂ κ₀ //
      length m c.1.1.2.1 ≤ length m τ - 1} =>
        (cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀ c.1 : BraidedStendhalAlgebra k Q Λ ν))) ?_ ?_
  · rintro _ ⟨c', rfl⟩
    exact ⟨⟨c'.1, by have := c'.2; omega⟩, rfl⟩
  have hb : (ofKLR k Q Λ ν (redIdem k Q Λ κ₂ *
      (KLRAlgebra.ψw (ρ τ) * (KLRAlgebra.pol (monomial u 1) * KLRAlgebra.e i)) *
        redIdem k Q Λ κ₀)) =
      (cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀ ⟨⟨(i, τ, u), hu⟩, hτ, hi⟩ :
        BraidedStendhalAlgebra k Q Λ ν) := by
    rw [cornerBasis_apply, ← mul_assoc (KLRAlgebra.ψw _), redIdem_mul_std, (hρ τ).2,
      ite_eq_left ⟨hτ, hi⟩]
  rw [Submodule.coe_sub, coe_tensorMult_pgen hρ _ _ _ _ hv2, ← hb, ← map_sub, ← sub_mul,
    ← mul_sub, mul_assoc (KLRAlgebra.ψw _)]
  exact hS

theorem frameClass_add (ρ : Perm (Fin m) → List ℕ) (τ : Perm (Fin m))
    (f g : MvPolynomial (Fin m) k) (i : Seq μ) :
    frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ τ (f + g) i =
      frameClass ρ τ f i + frameClass ρ τ g i := by
  unfold frameClass
  split_ifs
  · simp only [pgen, map_add, mul_add, add_mul, gen_add_right]
  · simp

theorem frameClass_smul (ρ : Perm (Fin m) → List ℕ) (τ : Perm (Fin m)) (r : k)
    (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ τ (r • f) i =
      r • frameClass ρ τ f i := by
  unfold frameClass
  split_ifs
  · simp only [pgen, map_smul, smul_mul_assoc, mul_smul_comm, gen_smul_right]
  · simp

include hρ in
/-- Every frame class is a combination of the frame classes indexed by the corner basis. -/
theorem frameClass_mem_span (τ : Perm (Fin m)) (f : MvPolynomial (Fin m) k) (i : Seq μ) :
    frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ τ f i ∈
      Submodule.span k (Set.range fun c : RedCornerIdx ν κ₂ κ₀ =>
        frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ c.1.1.2.1
          (monomial c.1.1.2.2 1) c.1.1.1) := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [frameClass_add]; exact add_mem hf hg
  | monomial u r =>
    rw [show (monomial u r : MvPolynomial (Fin m) k) = r • monomial u 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], frameClass_smul]
    refine Submodule.smul_mem _ r ?_
    by_cases hex : ∃ v, invSet m v ⊆ invSet m τ ∧ redWord (v • i) = κ₁
    swap
    · rw [frameClass, dite_eq_right hex]; exact zero_mem _
    by_cases hi : redWord i = κ₀
    swap
    · rw [frameClass, dite_eq_left hex, pgen_eq_zero_right _ _ _ _ hi]; exact zero_mem _
    by_cases hτ : redWord (τ • i) = κ₂
    swap
    · rw [frameClass, dite_eq_left hex,
        pgen_eq_zero_left hρ _ _ _ _ (by rwa [inv_mul_cancel_right])]
      exact zero_mem _
    by_cases hu : ∀ a, (i.lbl a).isRight → u a = 0
    · exact Submodule.subset_span ⟨⟨⟨(i, τ, u), hu⟩, hτ, hi⟩, rfl⟩
    · push Not at hu
      obtain ⟨a', ha, hu'⟩ := hu
      rw [frameClass, dite_eq_left hex, pgen, gen, ofKLR_std_eq_zero _ _ _ a' ha hu']
      simp

include hρ in
/-- The frame classes indexed by the corner basis span the tensor product. -/
theorem span_frameClass_eq_top (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) :
    Submodule.span k (Set.range fun c : RedCornerIdx ν κ₂ κ₀ =>
        frameClass (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ c.1.1.2.1
          (monomial c.1.1.2.2 1) c.1.1.1) = ⊤ := by
  rw [eq_top_iff, ← frameSpan_eq_top hρ h0 h1 h2, iSup_le_iff]
  intro n
  refine Submodule.span_le.2 ?_
  rintro _ ⟨τ, f, i, -, rfl⟩
  exact frameClass_mem_span hρ τ f i

/-- The images of the frame classes under multiplication: a basis of `B̃(κ₂, κ₀)`,
unitriangular with respect to the corner basis of Proposition 6.4. -/
noncomputable def frameBasis (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) : Module.Basis (RedCornerIdx ν κ₂ κ₀) k (cornerSpace k Q Λ ν κ₂ κ₀) :=
  Module.Basis.ofTriangular (cornerBasis (Λ := Λ) hQ ρ hρ κ₂ κ₀) (fun c => length m c.1.1.2.1)
    (Equiv.refl _) (fun c => tensorMult k Q Λ ν κ₂ κ₁ κ₀
      (frameClass ρ c.1.1.2.1 (monomial c.1.1.2.2 1) c.1.1.1))
    (tensorMult_frameClass_sub_mem hρ hQ h0 h1 h2)

theorem frameBasis_apply (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) (c : RedCornerIdx ν κ₂ κ₀) :
    frameBasis hρ hQ h0 h1 h2 c = tensorMult k Q Λ ν κ₂ κ₁ κ₀
      (frameClass ρ c.1.1.2.1 (monomial c.1.1.2.2 1) c.1.1.1) :=
  Module.Basis.ofTriangular_apply _ _ _ _ _ c

include hρ hQ in
/-- **Webster, Lemma 6.5, one red crossing.** Multiplication
`B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` is bijective when `κ₁` is obtained from `κ₀` by
exchanging adjacent red strands `a, b` that `κ₂` reads in the order `b, a`. -/
theorem tensorMult_bijective (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) : Function.Bijective (tensorMult k Q Λ ν κ₂ κ₁ κ₀) := by
  set S : RedCornerIdx ν κ₂ κ₀ → CornerTensor k (BraidedStendhalAlgebra k Q Λ ν)
      (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁) (redProj k Q Λ ν κ₀) :=
    fun c => frameClass ρ c.1.1.2.1 (monomial c.1.1.2.2 1) c.1.1.1 with hS
  have hB : ∀ c, frameBasis hρ hQ h0 h1 h2 c = tensorMult k Q Λ ν κ₂ κ₁ κ₀ (S c) :=
    frameBasis_apply hρ hQ h0 h1 h2
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    have htop : t ∈ LinearMap.range (Finsupp.linearCombination k S) := by
      rw [Finsupp.range_linearCombination, span_frameClass_eq_top hρ h0 h1 h2]
      exact Submodule.mem_top
    obtain ⟨c, rfl⟩ := htop
    rw [LinearMap.mem_ker, Finsupp.apply_linearCombination] at ht
    have hfun : (frameBasis hρ hQ h0 h1 h2 : _ → _) = tensorMult k Q Λ ν κ₂ κ₁ κ₀ ∘ S :=
      funext hB
    rw [← hfun] at ht
    have hc : c = 0 := linearIndependent_iff.1 (frameBasis hρ hQ h0 h1 h2).linearIndependent c ht
    simp [hc]
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← (frameBasis hρ hQ h0 h1 h2).span_eq,
      Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨S c, (hB c).symm⟩

/-- **Webster, Lemma 6.5, one red crossing**, as a linear isomorphism. -/
noncomputable def tensorMultEquiv (h0 : κ₀ = L ++ a :: b :: M) (h1 : κ₁ = L ++ b :: a :: M)
    (h2 : [b, a].Sublist κ₂) :
    CornerTensor k (BraidedStendhalAlgebra k Q Λ ν) (redProj k Q Λ ν κ₂) (redProj k Q Λ ν κ₁)
      (redProj k Q Λ ν κ₀) ≃ₗ[k] cornerSpace k Q Λ ν κ₂ κ₀ :=
  LinearEquiv.ofBijective _ (tensorMult_bijective hρ hQ h0 h1 h2)

end BraidedStendhalAlgebra

end Categorification.Stendhal
