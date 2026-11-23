/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendViolated
import Categorification.KLR.Symmetries

set_option backward.isDefEq.respectTransparency false

/-!
# The flip of braided Stendhal diagrams and the functors `𝔉_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7. Flipping diagrams top to bottom is an anti-automorphism of the braided
Stendhal algebra fixing the idempotents, the dots and the crossings. It preserves the ideal of
violated idempotents and commutes with the map `φ` adding a black strand at the right, so it
turns the statement of Proposition 6.7 for `𝔈_i` (`violMk_mult_injective_append`) into the
statement for `𝔉_i`, which is the same statement over the opposite algebras.

Webster deduces the statement for `𝔉_i` from the one for `𝔈_i` "by biadjunction"; here it is
deduced from the flip instead, which gives the module-level isomorphism directly.

## Main definitions

* `BraidedStendhalAlgebra.flip`: the top–bottom flip, an anti-automorphism (`flip_mul`,
  `flip_flip`) fixing `e(i)`, `x_a`, `ψ_j` (`flip_ofKLR`).
* `BraidedStendhalAlgebra.violFlip`: the flip on the quotient by violated idempotents.
* `BraidedStendhalAlgebra.appendViolOp`: the append map on the opposite algebras.

## Main results

* `flip_appendBlackAlg`, `violFlip_appendViol`: the flip commutes with appending a black strand.
* `violMk_mult_injective_append_op`, `violMk_mult_surjective_append_op`: **Proposition 6.7 for
  `𝔉_i`**: multiplication `e_{κ'} B(ν) e_κ ⊗_{e_κ B(ν) e_κ} φ(e_κ) B(ν + i) e_κ →
  φ(e_{κ'}) B(ν + i) e_κ`, `y ⊗ x ↦ φ(y) x`, is bijective (stated over the opposite algebras,
  where it is a tensor product along `φ` in the sense of `TensorAlong`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial Equiv MulOpposite

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

namespace BraidedStendhalAlgebra

/-! ### The flip -/

section Flip

variable {Q Λ} {ν : Multiset I}

variable (k Q Λ ν) in
/-- The flip on the free algebra on the KLR generators. -/
def flipFreeB : FreeAlgebra k (KLR.Gen (stendhalWeight ℓ ν)) →ₐ[k]
    (BraidedStendhalAlgebra k Q Λ ν)ᵐᵒᵖ :=
  (AlgHom.op (ofKLR k Q Λ ν)).comp (KLRAlgebra.flipFree k (stendhalQ Q Λ) (stendhalWeight ℓ ν))

variable (k Q Λ ν) in
/-- The top–bottom flip of braided Stendhal diagrams, as a homomorphism to the opposite
algebra. -/
def flipHom : BraidedStendhalAlgebra k Q Λ ν →ₐ[k] (BraidedStendhalAlgebra k Q Λ ν)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨flipFreeB k Q Λ ν, fun a b h => by
    cases h with
    | klr h =>
      exact congrArg (AlgHom.op (ofKLR k Q Λ ν)) (KLRAlgebra.flipFree_rel h)
    | red_dot a s h =>
      simp only [flipFreeB, AlgHom.comp_apply, map_mul, KLRAlgebra.flipFree_fx,
        KLRAlgebra.flipFree_fe, map_zero]
      apply unop_injective
      change ofKLR k Q Λ ν (KLRAlgebra.e s) * ofKLR k Q Λ ν (KLRAlgebra.x a) = 0
      rw [← map_mul, KLRAlgebra.e_mul_x, ofKLR_x_mul_e_of_red a s h]⟩

/-- The top–bottom flip of braided Stendhal diagrams. -/
def flip (z : BraidedStendhalAlgebra k Q Λ ν) : BraidedStendhalAlgebra k Q Λ ν :=
  (flipHom k Q Λ ν z).unop

theorem flip_ofKLR (z : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    flip (ofKLR k Q Λ ν z) = ofKLR k Q Λ ν (KLRAlgebra.hflip z) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [ofKLR_mk, KLRAlgebra.hflip, KLRAlgebra.flipAlgHom_mk]
  exact (congrArg unop (RingQuot.liftAlgHom_mkAlgHom_apply k (flipFreeB k Q Λ ν) _ a)).trans rfl

@[simp] theorem flip_mul (y z : BraidedStendhalAlgebra k Q Λ ν) :
    flip (y * z) = flip z * flip y := by
  simp [flip]

@[simp] theorem flip_add (y z : BraidedStendhalAlgebra k Q Λ ν) :
    flip (y + z) = flip y + flip z := by
  simp [flip]

@[simp] theorem flip_sub (y z : BraidedStendhalAlgebra k Q Λ ν) :
    flip (y - z) = flip y - flip z := by
  simp [flip]

@[simp] theorem flip_neg (z : BraidedStendhalAlgebra k Q Λ ν) : flip (-z) = -flip z := by
  simp [flip]

@[simp] theorem flip_zero : flip (0 : BraidedStendhalAlgebra k Q Λ ν) = 0 := by
  simp [flip]

@[simp] theorem flip_one : flip (1 : BraidedStendhalAlgebra k Q Λ ν) = 1 := by
  simp [flip]

@[simp] theorem flip_smul (c : k) (z : BraidedStendhalAlgebra k Q Λ ν) :
    flip (c • z) = c • flip z := by
  simp [flip]

@[simp] theorem flip_algebraMap (c : k) :
    flip (algebraMap k (BraidedStendhalAlgebra k Q Λ ν) c) =
      algebraMap k (BraidedStendhalAlgebra k Q Λ ν) c := by
  simp [flip]

@[simp] theorem flip_flip (z : BraidedStendhalAlgebra k Q Λ ν) : flip (flip z) = z := by
  obtain ⟨z, rfl⟩ := ofKLR_surjective z
  rw [flip_ofKLR, flip_ofKLR, KLRAlgebra.hflip_hflip]

theorem flip_sum {ι : Type*} (s : Finset ι) (f : ι → BraidedStendhalAlgebra k Q Λ ν) :
    flip (∑ x ∈ s, f x) = ∑ x ∈ s, flip (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, flip_add, ih]

theorem flip_bijective :
    Function.Bijective (flip : BraidedStendhalAlgebra k Q Λ ν → BraidedStendhalAlgebra k Q Λ ν) :=
  Function.Involutive.bijective flip_flip

theorem flip_e (s : Seq (stendhalWeight ℓ ν)) :
    flip (ofKLR k Q Λ ν (KLRAlgebra.e s)) = ofKLR k Q Λ ν (KLRAlgebra.e s) := by
  rw [flip_ofKLR, KLRAlgebra.hflip_e]

theorem flip_redProj (κ : List (Fin ℓ)) : flip (redProj k Q Λ ν κ) = redProj k Q Λ ν κ := by
  rw [redProj, flip_ofKLR, redIdem, KLRAlgebra.hflip_sum]
  simp only [KLRAlgebra.hflip_e]

theorem flip_mem_violIdeal {z : BraidedStendhalAlgebra k Q Λ ν} (hz : z ∈ violIdeal k Q Λ ν) :
    flip z ∈ violIdeal k Q Λ ν := by
  rw [violIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨a, -, g, ⟨s, hs, rfl⟩, rfl⟩, b, -, rfl⟩ := hz
    rw [flip_mul, flip_mul, flip_e]
    refine TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_right _ _ _ ?_)
    exact TwoSidedIdeal.subset_span ⟨s, hs, rfl⟩
  | zero => rw [flip_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [flip_add]; exact add_mem hz hw
  | neg z _ hz => rw [flip_neg]; exact neg_mem hz

variable (k Q Λ ν) in
/-- The flip on the quotient by violated idempotents, as a homomorphism to the opposite
algebra. -/
def violFlipHom : ViolQuotient k Q Λ ν →ₐ[k] (ViolQuotient k Q Λ ν)ᵐᵒᵖ :=
  (violIdeal k Q Λ ν).ringCon.liftₐ ((AlgHom.op (violMk k Q Λ ν)).comp (flipHom k Q Λ ν))
    fun x y h => by
      rw [RingCon.ker_apply]
      have h' : x - y ∈ violIdeal k Q Λ ν := (TwoSidedIdeal.rel_iff _ x y).1 h
      apply unop_injective
      change violMk k Q Λ ν (flip x) = violMk k Q Λ ν (flip y)
      rw [← sub_eq_zero, ← map_sub, ← flip_sub, violMk_eq_zero_iff]
      exact flip_mem_violIdeal h'

/-- The flip on the quotient by violated idempotents. -/
def violFlip (z : ViolQuotient k Q Λ ν) : ViolQuotient k Q Λ ν := (violFlipHom k Q Λ ν z).unop

theorem violFlip_violMk (z : BraidedStendhalAlgebra k Q Λ ν) :
    violFlip (violMk k Q Λ ν z) = violMk k Q Λ ν (flip z) := rfl

theorem violFlip_violFlip (z : ViolQuotient k Q Λ ν) : violFlip (violFlip z) = z := by
  obtain ⟨z, rfl⟩ := violMk_surjective z
  rw [violFlip_violMk, violFlip_violMk, flip_flip]

theorem violFlipHom_bijective : Function.Bijective (violFlipHom k Q Λ ν) :=
  show Function.Bijective (fun z => op (violFlip z)) from
    MulOpposite.opEquiv.bijective.comp (Function.Involutive.bijective violFlip_violFlip)

end Flip

/-! ### The flip and the appended black strand -/

theorem flip_appendIdem : flip (appendIdem Q Λ i ν) = appendIdem Q Λ i ν := by
  rw [appendIdem_eq_sum, flip_sum]
  exact Finset.sum_congr rfl fun s _ => flip_e _

/-- An element `g' φ(1)` of the corner, with `g'` fixed by the flip, commutes with `φ(1)`. -/
private theorem appendIdem_mul_of_flip {g : BraidedStendhalAlgebra k Q Λ νᵢ}
    (hg : flip g = g)
    (hc : appendIdem Q Λ i ν * (g * appendIdem Q Λ i ν) * appendIdem Q Λ i ν =
      g * appendIdem Q Λ i ν) :
    appendIdem Q Λ i ν * g = g * appendIdem Q Λ i ν := by
  have hE := isIdempotentElem_appendIdem Q Λ i ν
  have := congrArg flip hc
  simp only [flip_mul, flip_appendIdem, hg] at this
  have h1 : appendIdem Q Λ i ν * (g * appendIdem Q Λ i ν) * appendIdem Q Λ i ν =
      appendIdem Q Λ i ν * g * appendIdem Q Λ i ν := by
    rw [mul_assoc, mul_assoc, hE.eq, ← mul_assoc]
  calc appendIdem Q Λ i ν * g
      = appendIdem Q Λ i ν * (appendIdem Q Λ i ν * g * appendIdem Q Λ i ν) := this.symm
    _ = appendIdem Q Λ i ν * g * appendIdem Q Λ i ν := by
      rw [← mul_assoc, ← mul_assoc, hE.eq]
    _ = g * appendIdem Q Λ i ν := h1.symm.trans hc

/-- **The flip commutes with appending a black strand.** -/
theorem flip_appendBlackAlg (z : BraidedStendhalAlgebra k Q Λ ν) :
    flip (appendBlackAlg Q Λ i ν z) = appendBlackAlg Q Λ i ν (flip z) := by
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (BraidedRel k Q Λ ν) z
  have hcorner : ∀ y : BraidedStendhalAlgebra k Q Λ ν,
      appendIdem Q Λ i ν * appendBlackAlg Q Λ i ν y * appendIdem Q Λ i ν =
        appendBlackAlg Q Λ i ν y := fun y =>
    (congrArg (· * appendIdem Q Λ i ν) (KLR.Corner.E_mul_val (appendBlack Q Λ i ν y))).trans
      (KLR.Corner.val_mul_E _)
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes]
    change flip (appendBlackAlg Q Λ i ν (algebraMap k (BraidedStendhalAlgebra k Q Λ ν) c)) =
      appendBlackAlg Q Λ i ν (flip (algebraMap k (BraidedStendhalAlgebra k Q Λ ν) c))
    rw [flip_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul, flip_smul]
    congr 1
    have h1 : appendBlackAlg Q Λ i ν 1 = appendIdem Q Λ i ν := by
      rw [appendBlackAlg_apply, appendBlackValue_apply, map_one]
      rfl
    rw [h1]
    exact flip_appendIdem Q Λ i ν
  | grade1 g =>
    have hmk : RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) (FreeAlgebra.ι k g) =
        ofKLR k Q Λ ν (KLRAlgebra.mk k _ _ (FreeAlgebra.ι k g)) := (ofKLR_mk _).symm
    rw [hmk]
    cases g with
    | idem s =>
      change flip (appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.e s))) =
        appendBlackAlg Q Λ i ν (flip (ofKLR k Q Λ ν (KLRAlgebra.e s)))
      rw [flip_e, appendBlackAlg_e, flip_e]
    | dot b =>
      change flip (appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.x b))) =
        appendBlackAlg Q Λ i ν (flip (ofKLR k Q Λ ν (KLRAlgebra.x b)))
      have hx : flip (ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν b))) =
          ofKLR k Q Λ νᵢ (KLRAlgebra.x (appendPos i ν b)) := by
        rw [flip_ofKLR, KLRAlgebra.hflip_x]
      have hv := appendBlack_ofKLR_x Q Λ i ν b
      have hc := hcorner (ofKLR k Q Λ ν (KLRAlgebra.x b))
      rw [flip_ofKLR, KLRAlgebra.hflip_x, appendBlackAlg_apply, appendBlackValue_apply, hv]
      rw [appendBlackAlg_apply, appendBlackValue_apply, hv] at hc
      rw [flip_mul, flip_appendIdem, hx, appendIdem_mul_of_flip Q Λ i ν hx hc]
    | cross j =>
      change flip (appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.ψ j))) =
        appendBlackAlg Q Λ i ν (flip (ofKLR k Q Λ ν (KLRAlgebra.ψ j)))
      rw [flip_ofKLR, KLRAlgebra.hflip_ψ]
      by_cases hj : j + 1 < Multiset.card μ
      · have hψ : flip (ofKLR k Q Λ νᵢ (KLRAlgebra.ψ j)) = ofKLR k Q Λ νᵢ (KLRAlgebra.ψ j) := by
          rw [flip_ofKLR, KLRAlgebra.hflip_ψ]
        have hv := appendBlack_ofKLR_ψ Q Λ i ν hj
        have hc := hcorner (ofKLR k Q Λ ν (KLRAlgebra.ψ j))
        rw [appendBlackAlg_apply, appendBlackValue_apply, hv]
        rw [appendBlackAlg_apply, appendBlackValue_apply, hv] at hc
        rw [flip_mul, flip_appendIdem, hψ, appendIdem_mul_of_flip Q Λ i ν hψ hc]
      · rw [KLRAlgebra.ψ_eq_zero j (by omega), map_zero, map_zero, flip_zero]
  | mul a b ha hb =>
    simp only [map_mul, flip_mul, ha, hb]
    rw [← map_mul]
    exact congrArg _ (flip_mul (Q := Q) (Λ := Λ) (RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) a)
      (RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) b)).symm
  | add a b ha hb =>
    simp only [map_add, flip_add, ha, hb]
    rw [← map_add]
    exact congrArg _ (flip_add (Q := Q) (Λ := Λ) (RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) a)
      (RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) b)).symm

/-- The flip commutes with appending a black strand on the quotients. -/
theorem violFlip_appendViol (z : ViolQuotient k Q Λ ν) :
    violFlip (appendViol Q Λ i ν z) = appendViol Q Λ i ν (violFlip z) := by
  obtain ⟨z, rfl⟩ := violMk_surjective z
  rw [appendViol_violMk, violFlip_violMk, violFlip_violMk, appendViol_violMk,
    flip_appendBlackAlg]

/-! ### Proposition 6.7 for `𝔉_i` -/

/-- The append map on the opposite algebras. -/
def appendViolOp : (ViolQuotient k Q Λ ν)ᵐᵒᵖ →ₙₐ[k] (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ where
  toFun c := op (appendViol Q Λ i ν c.unop)
  map_smul' c x := congrArg op (map_smul (appendViol Q Λ i ν) c x.unop)
  map_zero' := congrArg op (map_zero (appendViol Q Λ i ν))
  map_add' x y := congrArg op (map_add (appendViol Q Λ i ν) x.unop y.unop)
  map_mul' x y := congrArg op (map_mul (appendViol Q Λ i ν) y.unop x.unop)

theorem appendViolOp_apply (c : (ViolQuotient k Q Λ ν)ᵐᵒᵖ) :
    appendViolOp Q Λ i ν c = op (appendViol Q Λ i ν c.unop) := rfl

omit [DecidableEq I] in
private theorem isIdempotentElem_op {A : Type*} [Mul A] {e : A} (h : IsIdempotentElem e) :
    IsIdempotentElem (op e) := by
  change op e * op e = op e
  rw [← op_mul, h.eq]

private theorem idemOp (ν : Multiset I) (κ : List (Fin ℓ)) :
    IsIdempotentElem (op (violMk k Q Λ ν (redProj k Q Λ ν κ))) :=
  isIdempotentElem_op ((isIdempotentElem_redProj κ).map (violMk k Q Λ ν))

private theorem violFlipHom_redProj (ν : Multiset I) (κ : List (Fin ℓ)) :
    violFlipHom k Q Λ ν (violMk k Q Λ ν (redProj k Q Λ ν κ)) =
      op (violMk k Q Λ ν (redProj k Q Λ ν κ)) := by
  apply unop_injective
  change violFlip _ = _
  rw [violFlip_violMk, flip_redProj]
  rfl

private theorem violFlipHom_appendViol (c : ViolQuotient k Q Λ ν) :
    violFlipHom k Q Λ νᵢ (appendViol Q Λ i ν c) =
      appendViolOp Q Λ i ν (violFlipHom k Q Λ ν c) := by
  apply unop_injective
  exact violFlip_appendViol Q Λ i ν c

variable (hQ : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ) (hρ : IsReducedChoice ρ)

include hQ hρ in
/-- **Webster, Proposition 6.7** (arXiv:1309.3796v2), injectivity, for `𝔉_i`: multiplication
`e_{κ'} B(ν) e_κ ⊗_{e_κ B(ν) e_κ} φ(e_κ) B(ν + i) e_κ → B(ν + i)`, `y ⊗ x ↦ φ(y) x`, is
injective. Over the opposite algebras this is the tensor product along `φ` with idempotents
`e_κ`, `e_κ`, `e_{κ'}`. -/
theorem violMk_mult_injective_append_op (κ' κ : List (Fin ℓ)) :
    Function.Injective (TensorAlong.mult (idemOp Q Λ νᵢ κ) (idemOp Q Λ ν κ) (idemOp Q Λ ν κ') :
      TensorAlong k _ _ (appendViolOp Q Λ i ν) (op (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ)))
        (op (violMk k Q Λ ν (redProj k Q Λ ν κ)))
        (op (violMk k Q Λ ν (redProj k Q Λ ν κ'))) →ₗ[k] _) :=
  TensorAlong.mult_injective_of_bijective (violFlipHom k Q Λ νᵢ) (violFlipHom k Q Λ ν)
    (violFlipHom_appendViol Q Λ i ν) _ _ _ _ _ _ (violFlipHom_redProj Q Λ νᵢ κ)
    (violFlipHom_redProj Q Λ ν κ) (violFlipHom_redProj Q Λ ν κ') violFlipHom_bijective
    violFlipHom_bijective.2 (violMk_mult_injective_append Q Λ i ν hQ ρ hρ κ κ')

include hQ hρ in
/-- **Webster, Proposition 6.7** (arXiv:1309.3796v2), surjectivity, for `𝔉_i`: every element of
`φ(e_{κ'}) B(ν + i) e_κ` is a product `φ(y) x`. -/
theorem violMk_mult_surjective_append_op (κ' κ : List (Fin ℓ))
    (z : (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ) :
    ∃ t, TensorAlong.mult (idemOp Q Λ νᵢ κ) (idemOp Q Λ ν κ) (idemOp Q Λ ν κ')
      (t : TensorAlong k _ _ (appendViolOp Q Λ i ν) (op (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ)))
        (op (violMk k Q Λ ν (redProj k Q Λ ν κ)))
        (op (violMk k Q Λ ν (redProj k Q Λ ν κ')))) =
      op (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ)) * z *
        appendViolOp Q Λ i ν (op (violMk k Q Λ ν (redProj k Q Λ ν κ'))) :=
  TensorAlong.mult_surjective_of_surjective' (violFlipHom k Q Λ νᵢ) (violFlipHom k Q Λ ν)
    (violFlipHom_appendViol Q Λ i ν) _ _ _ _ _ _ (violFlipHom_redProj Q Λ νᵢ κ)
    (violFlipHom_redProj Q Λ ν κ) (violFlipHom_redProj Q Λ ν κ') violFlipHom_bijective.2
    (violMk_mult_surjective_append Q Λ i ν hQ ρ hρ κ κ') z

end BraidedStendhalAlgebra

end Categorification.Stendhal
