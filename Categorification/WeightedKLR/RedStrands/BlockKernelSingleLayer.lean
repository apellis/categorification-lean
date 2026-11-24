/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelFiltration
import Mathlib.LinearAlgebra.Quotient.Basic
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity
import Categorification.WeightedKLR.RedStrands.BoundaryCharacters

/-!
# The higher partial standard across a zero-weight spectator

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21).
For one black strand following a pair of reds and a zero-weight spectator, moving
the black before the spectator gives the sole layer in a partial standard filtration of the
kernel. Its projective presentation has no surviving higher cut.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t s : Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
local notation "p" => fun s => violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s))

/-- A loading with no surviving strictly higher loading is its own partial standard. -/
theorem blockLoadingKernel_eq_bot_of_maximal
    (h : ∀ w : Seq (stendhalWeight ℓ ν), redWord w = redWord t →
      adjacentBlockRoot a b t < adjacentBlockRoot a b w → IsViolated w) :
    K = ⊥ := by
  rw [blockLoadingKernel_eq_span]
  refine le_antisymm (Submodule.span_le.2 ?_) bot_le
  rintro _ ⟨w, hw, hlt, z, rfl⟩
  change blockLoadingRep Q Λ t (z * p w) ∈ (⊥ : Submodule Tᵐᵒᵖ P)
  have hp : p w = 0 := violMk_e (h w hw hlt)
  rw [hp, mul_zero, Submodule.mem_bot]
  apply Subtype.ext; apply Subtype.ext
  rw [blockLoadingRep_val, mul_zero, zero_mul]
  rfl

/-- An equivalent higher idempotent generates the entire source loading projective. -/
theorem blockLoadingKernel_eq_top_of_equiv (ho : redWord s = redWord t)
    (hlt : adjacentBlockRoot a b t < adjacentBlockRoot a b s)
    (he : IdemEquiv (orderedLoadingIdem Q Λ t)
      (orderedLoadingIdemAt Q Λ (redWord t) s ho)) :
    K = ⊤ := by
  obtain ⟨c, d, hc, hd, _, _⟩ := he
  have hs : p s ∈ J := TwoSidedIdeal.subset_span ⟨s, ho, hlt, rfl⟩
  have heq : c.1 * d.1 = p t := congrArg Subtype.val hc
  have heq' : d.1 * c.1 = p s := congrArg Subtype.val hd
  have ht : p t ∈ J := by
    have hi : p t * p t = p t := congrArg Subtype.val (orderedLoadingIdem_idem Q Λ t).eq
    have ht' : c.1 * p s * d.1 = p t := by
      rw [← heq', ← mul_assoc, heq, mul_assoc, heq, hi]
    rw [← ht']
    exact TwoSidedIdeal.mul_mem_right J _ _ (TwoSidedIdeal.mul_mem_left J _ _ hs)
  apply top_unique
  intro x _
  change x.1.1 ∈ J
  rw [← show p t * x.1.1 = x.1.1 from congrArg Subtype.val x.2]
  exact TwoSidedIdeal.mul_mem_right J _ _ ht

/-- Invertible red-black bigons give equivalent loading idempotents in their common order. -/
theorem loadingIdemEquiv_of_unit_bigon (ho : redWord s = redWord t)
    (j : ℕ) (hs : TypeA.sadj (Multiset.card (stendhalWeight ℓ ν)) j • t = s)
    (htb : (KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e t :
      KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) = KLRAlgebra.e t)
    (hsb : (KLRAlgebra.ψ j * KLRAlgebra.ψ j * KLRAlgebra.e s :
      KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) = KLRAlgebra.e s) :
    IdemEquiv (orderedLoadingIdem Q Λ t) (orderedLoadingIdemAt Q Λ (redWord t) s ho) := by
  let E := violMk k Q Λ ν (redProj k Q Λ ν (redWord t))
  let π := (violMk k Q Λ ν).comp (ofKLR k Q Λ ν)
  let ψ := π (KLRAlgebra.ψ j)
  have ht : p t * ψ = ψ * p s := by
    change π (KLRAlgebra.e t) * π (KLRAlgebra.ψ j) =
      π (KLRAlgebra.ψ j) * π (KLRAlgebra.e s)
    rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_ψ, hs]
  have hst : TypeA.sadj (Multiset.card (stendhalWeight ℓ ν)) j • s = t := by
    rw [← hs, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  have hs' : p s * ψ = ψ * p t := by
    change π (KLRAlgebra.e s) * π (KLRAlgebra.ψ j) =
      π (KLRAlgebra.ψ j) * π (KLRAlgebra.e t)
    rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_ψ, hst]
  have et : E * p t = p t ∧ p t * E = p t :=
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).1
      (orderedLoadingIdem Q Λ t).2
  have es : E * p s = p s ∧ p s * E = p s :=
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).1
      (orderedLoadingIdemAt Q Λ (redWord t) s ho).2
  let c : T := ⟨p t * ψ, (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
    ⟨by rw [← mul_assoc, et.1], by rw [ht, mul_assoc, es.2]⟩⟩
  let d : T := ⟨p s * ψ, (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
    ⟨by rw [← mul_assoc, es.1], by rw [hs', mul_assoc, et.2]⟩⟩
  have pt : p t * p t = p t := congrArg Subtype.val (orderedLoadingIdem_idem Q Λ t).eq
  have ps : p s * p s = p s := congrArg Subtype.val (orderedLoadingIdem_idem Q Λ s).eq
  have hbt : ψ * ψ * p t = p t := by
    change π _ * π _ * π _ = π _
    rw [← map_mul, ← map_mul, htb]
  have hbs : ψ * ψ * p s = p s := by
    change π _ * π _ * π _ = π _
    rw [← map_mul, ← map_mul, hsb]
  have hc : (p t * ψ) * (p s * ψ) = p t := by
    rw [← mul_assoc, show (p t * ψ) * p s = p t * ψ by rw [ht, mul_assoc, ps],
      ht, mul_assoc, hs', ← mul_assoc, hbt]
  have hd : (p s * ψ) * (p t * ψ) = p s := by
    rw [← mul_assoc, show (p s * ψ) * p t = p s * ψ by rw [hs', mul_assoc, pt],
      hs', mul_assoc, ht, ← mul_assoc, hbs]
  refine ⟨c, d, Subtype.ext hc, Subtype.ext hd, ?_, ?_⟩ <;> apply Subtype.ext
  · change (p t * ψ) * (p s * ψ) * (p t * ψ) = p t * ψ
    rw [hc, ← mul_assoc, pt]
  · change (p s * ψ) * (p t * ψ) * (p s * ψ) = p s * ψ
    rw [hd, ← mul_assoc, ps]

/-- The higher-cut kernel in the corner of any chosen equal red word. -/
def blockLoadingKernelAt (κ : List (Fin ℓ)) (hs : redWord s = κ) :
    Submodule (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ))ᵐᵒᵖ
      (rIdeal (orderedLoadingIdemAt Q Λ κ s hs)) := by
  subst κ
  exact blockLoadingKernel Q Λ s a b

local notation "Tκ" => fun κ =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)

/-- The loading projective modulo its strictly higher retained cuts, in the fixed order. -/
def blockPartialStandardAt (κ : List (Fin ℓ)) (hs : redWord s = κ) : ModuleCat (Tκ κ)ᵐᵒᵖ := by
  let projective := rIdeal (orderedLoadingIdemAt Q Λ κ s hs)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : Module (Tκ κ)ᵐᵒᵖ projective := Submodule.module projective
  let ker : Submodule (Tκ κ)ᵐᵒᵖ projective := blockLoadingKernelAt Q Λ s a b κ hs
  exact ModuleCat.of (Tκ κ)ᵐᵒᵖ (projective ⧸ ker)

private theorem blockLoadingKernelAt_eq_bot (κ : List (Fin ℓ)) (hs : redWord s = κ)
    (hmax : ∀ w : Seq (stendhalWeight ℓ ν), redWord w = redWord s →
      adjacentBlockRoot a b s < adjacentBlockRoot a b w → IsViolated w) :
    blockLoadingKernelAt Q Λ s a b κ hs = ⊥ := by
  subst κ
  exact blockLoadingKernel_eq_bot_of_maximal Q Λ s a b hmax

/-- A maximal surviving loading has no higher cut, so its partial standard is projective. -/
def blockPartialStandardAt_equiv_projective (κ : List (Fin ℓ)) (hs : redWord s = κ)
    (hmax : ∀ w : Seq (stendhalWeight ℓ ν), redWord w = redWord s →
      adjacentBlockRoot a b s < adjacentBlockRoot a b w → IsViolated w) :
    blockPartialStandardAt Q Λ s a b κ hs ≃ₗ[(Tκ κ)ᵐᵒᵖ] rIdeal (orderedLoadingIdemAt Q Λ κ s hs) := by
  let projective := rIdeal (orderedLoadingIdemAt Q Λ κ s hs)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : Module (Tκ κ)ᵐᵒᵖ projective := Submodule.module projective
  exact (blockLoadingKernelAt Q Λ s a b κ hs).quotEquivOfEqBot
    (blockLoadingKernelAt_eq_bot Q Λ s a b κ hs hmax)

/-- An equivalent higher maximal loading gives a single partial-standard layer of the kernel. -/
theorem blockLoadingKernel_hasHigherSingle (ho : redWord s = redWord t)
    (hlt : adjacentBlockRoot a b t < adjacentBlockRoot a b s)
    (he : IdemEquiv (orderedLoadingIdem Q Λ t) (orderedLoadingIdemAt Q Λ (redWord t) s ho))
    (hmax : ∀ w : Seq (stendhalWeight ℓ ν), redWord w = redWord s →
      adjacentBlockRoot a b s < adjacentBlockRoot a b w → IsViolated w) :
    ModuleFiltration.HasFiltration (fun _ : Unit => blockPartialStandardAt Q Λ s a b (redWord t) ho)
      [()] (ModuleCat.of Tᵐᵒᵖ K) := by
  have ht := blockLoadingKernel_eq_top_of_equiv Q Λ t s a b ho hlt he
  obtain ⟨c, d, hcd⟩ := he
  exact ModuleFiltration.HasFiltration.single
    ((LinearEquiv.ofEq K ⊤ ht).trans (Submodule.topEquiv.trans
      (hcd.rIdealEquiv.trans (blockPartialStandardAt_equiv_projective Q Λ s a b _ ho hmax).symm)))

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra
namespace ThreeRedOneBlack

open KLR

private abbrev ν : Multiset Unit := {()}
private abbrev μ := stendhalWeight 3 ν
/-- The black strand lies to the right of the zero-weight spectator. -/
def source : Seq (stendhalWeight 3 ({()} : Multiset Unit)) := KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inl ()] (by decide)
/-- The black strand lies just to the left of the zero-weight spectator. -/
def higher : Seq (stendhalWeight 3 ({()} : Multiset Unit)) := KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2] (by decide)

/-- The two loadings give the same order of red strands. -/
theorem sameOrder : redWord higher = redWord source := by decide

/-- Moving the black across the spectator increases the retained-boundary root. -/
theorem source_lt_higher : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 higher := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad : (0 : ℕ) = 1 := congrFun (congrFun h (2 : Fin 3)) ()
    contradiction

/-- Any loading of this order strictly above the higher loading is violated. -/
theorem higher_maximal : ∀ w : Seq μ, redWord w = redWord higher →
    adjacentBlockRoot 0 1 higher < adjacentBlockRoot 0 1 w → IsViolated w := by
  suffices test : ∀ w : Seq μ, redWord w = redWord higher →
      (∀ r : Fin 3, adjacentBlockRoot 0 1 higher r () ≤ adjacentBlockRoot 0 1 w r ()) →
      (∃ r : Fin 3, adjacentBlockRoot 0 1 higher r () < adjacentBlockRoot 0 1 w r ()) →
      (w.lbl ⟨0, by decide⟩).isLeft by
    intro w ho hh
    refine ⟨by decide, test w ho (fun r => hh.le r ()) ?_⟩
    by_contra! h
    exact hh.not_ge fun r i => by cases i; exact h r
  let : Fintype (Seq μ) := inferInstanceAs (Fintype { f : Fin 4 → Unit ⊕ Fin 3 //
    Finset.univ.val.map f = μ })
  decide

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
private abbrev R := KLRAlgebra k (stendhalQ Q Λ) μ

private theorem swap : TypeA.sadj (Multiset.card μ) 2 • source = higher := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide

private theorem lowBigon (h : Λ 2 () = 0) :
    (KLRAlgebra.ψ 2 * KLRAlgebra.ψ 2 * KLRAlgebra.e source : R Q Λ) = KLRAlgebra.e source := by
  rw [KLRAlgebra.ψ_sq 2 (by decide)]
  have hr : source.lbl ⟨2, by decide⟩ = .inr 2 := rfl
  have hb : source.lbl ⟨3, by decide⟩ = .inl () := rfl
  rw [hr, hb]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, h, pow_zero]
  unfold ncEval
  rw [show (1 : MvPolynomial (Fin 2) k).coeff = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

private theorem highBigon (h : Λ 2 () = 0) :
    (KLRAlgebra.ψ 2 * KLRAlgebra.ψ 2 * KLRAlgebra.e higher : R Q Λ) = KLRAlgebra.e higher := by
  rw [KLRAlgebra.ψ_sq 2 (by decide)]
  have hb : higher.lbl ⟨2, by decide⟩ = .inl () := rfl
  have hr : higher.lbl ⟨3, by decide⟩ = .inr 2 := rfl
  rw [hb, hr]
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, h, pow_zero]
  unfold ncEval
  rw [show (1 : MvPolynomial (Fin 2) k).coeff = Finsupp.single 0 1 from rfl,
    Finsupp.sum_single_index (by simp)]
  simp

/-- In the one-black loading after a zero-weight spectator, the higher retained
partial standard comes from moving the black just before the spectator. -/
theorem kernel_hasHigherFiltration (h : Λ 2 () = 0) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of _ (blockLoadingKernel Q Λ source 0 1)) :=
  blockLoadingKernel_hasHigherSingle Q Λ source higher 0 1 sameOrder source_lt_higher
    (loadingIdemEquiv_of_unit_bigon Q Λ source higher sameOrder 2 swap (lowBigon Q Λ h) (highBigon Q Λ h)) higher_maximal

/-- With positive red weights, the higher retained partial standard is nonzero.
The first-weight boundary character reads its projective idempotent as one. -/
theorem higherPartialStandard_nontrivial [Nontrivial k] (hQ : KLRSymm Q)
    (hΛ : ∀ r, 0 < Λ r ()) :
    Nontrivial (blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder) := by
  have hw : redWord higher = List.finRange 3 := by decide
  have hv : ¬ IsViolated higher := by rintro ⟨_, h⟩; contradiction
  have hs := (redWord_eq_finRange_iff higher).1 hw
  let ρ := TypeA.canWord (Multiset.card μ)
  have hρ : TypeA.IsReducedChoice ρ :=
    fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩
  let q := violCornerEquiv (ν := ν) (Λ := Λ) hρ hQ
  let e := cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e higher))
  have he : (violCornerHom k Q Λ ν e).1 ≠ 0 := by
    intro h
    have hz : violCornerHom k Q Λ ν e = 0 := Subtype.ext h
    have hc := congrArg (FirstWeight.boundaryCharacter Q Λ hΛ higher hs hv ∘ q) hz
    change FirstWeight.boundaryCharacter Q Λ hΛ higher hs hv (q (violCornerHom k Q Λ ν e)) =
      FirstWeight.boundaryCharacter Q Λ hΛ higher hs hv (q 0) at hc
    rw [map_zero, map_zero, violCornerEquiv_violCornerHom hρ hQ,
      identityCornerHom_e hw, FirstWeight.boundaryCharacter_e, ite_eq_left rfl] at hc
    exact one_ne_zero hc
  let d := orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder
  let η := blockPartialStandardAt_equiv_projective Q Λ higher 0 1 (redWord source) sameOrder higher_maximal
  have hd : d.1 ≠ 0 := by
    rw [show d.1 = (violCornerHom k Q Λ ν e).1 by
      symm
      rw [violCornerHom_val, cornerMk_e_val hw]
      rfl]
    exact he
  have hidem : IsIdempotentElem d := by
    apply Subtype.ext
    exact congrArg Subtype.val (orderedLoadingIdem_idem Q Λ higher).eq
  have hd' : (⟨d, hidem.eq⟩ : rIdeal d) ≠ 0 := fun h =>
    hd (congrArg (fun x : rIdeal d => x.1.1) h)
  exact ⟨η.symm ⟨d, hidem.eq⟩, η.symm 0, fun h => hd' (η.symm.injective h)⟩

end ThreeRedOneBlack
end Categorification.Stendhal.BraidedStendhalAlgebra
