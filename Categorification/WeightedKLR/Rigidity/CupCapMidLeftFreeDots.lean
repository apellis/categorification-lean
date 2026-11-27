/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFree

/-!
# Dots on the strands of `λ` act on the generators of the model

Webster, arXiv:1309.3796v3, §7.3, for a cap after the red strand `λ_j`. A polynomial `p` in the
dots of `λ`, acting on the left of the model, slides under the maximum: on an element
`Z ⊗ v` with `Z` of top in the window of `s`, it multiplies `Z` by `p` placed on the strands of
`λ` outside the window (`midKLRAct_pol_tmul_midGen`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

theorem midGen_smul (c : k) (Z : Tp) :
    midGen j hj Q Λ Λc ν ν₀ (c • Z) = algebraMap k Tpᵐᵒᵖ c • midGen j hj Q Λ Λc ν ν₀ Z :=
  Subtype.ext (by
    change op (midStendhal j hj Q Λ Λc ν ν₀ 1 * (c • Z)) =
      algebraMap k Tpᵐᵒᵖ c * op (midStendhal j hj Q Λ Λc ν ν₀ 1 * Z)
    rw [mul_smul_comm, op_smul]
    exact Algebra.smul_def (A := Tpᵐᵒᵖ) c _)

omit [DecidableEq I] in
/-- The dot of `λ` on the strand `a`, in the window of `s`, is the dot at `outPos s a`. -/
theorem dotPos_midPos (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    dotPos (j := j) (hj := hj) (ν₀ := ν₀) ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a =
      outPos j ν₀ s a := by
  apply Fin.ext
  rw [outPos_val]
  simp only [dotPos, Fin.val_cast, insertPos_inl_val, Multiset.card_map]

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **Dots of `λ` slide under the maximum**: for `Z` with top in the window of `s`, a
polynomial `p` in the dots of `λ` acts on `Z ⊗ v` by placing `p` on the strands of `λ` outside
the window. -/
theorem midKLRAct_pol_tmul_midGen (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (s : Seq (stendhalWeight ℓ ν)) (p : MvPolynomial (Fin m) k) :
    ∀ (Z : Rp), E s * Z = Z → ∀ v : L,
      midKLRAct hR (pol p) (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v) =
        Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (pol (rename (outPos j ν₀ s) p) * Z))) v := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    intro Z _ v
    simp only [← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Module.algebraMap_end_apply]
    rw [← Algebra.smul_def, map_smul, midGen_smul, ← Ind.smul_tmul]
    rfl
  | add p q hp hq =>
    intro Z hZ v
    rw [map_add, map_add, LinearMap.add_apply, hp Z hZ v, hq Z hZ v, map_add, map_add, add_mul,
      map_add, midGen_add, Ind.add_tmul]
  | mul_X p a hp =>
    intro Z hZ v
    have h1 : midDot j hj Q Λ Λc ν ν₀ a * Z = KLRAlgebra.x (outPos j ν₀ s a) * Z := by
      conv_lhs => rw [← hZ]
      rw [← mul_assoc, midDot_mul_eSum, dotPos_midPos, mul_assoc, hZ]
    have h2 : E s * (KLRAlgebra.x (outPos j ν₀ s a) * Z) = KLRAlgebra.x (outPos j ν₀ s a) * Z := by
      rw [← mul_assoc, ← x_mul_eSum, mul_assoc, hZ]
    rw [map_mul, pol_X, map_mul, Module.End.mul_apply, midKLRAct_x, midEnd_tmul_midGen L hL,
      ← map_mul, h1, hp _ h2 v]
    simp only [map_mul, rename_X, pol_X, mul_assoc]

/-! ### Dotted generators and surjectivity of `Θ` -/

variable (j hj ν ν₀) in
/-- The generator `g` with its dots removed. -/
def MidGen.undot (g : MidGen j hj ν ν₀) : MidGen j hj ν ν₀ :=
  { g with d := 0, hd := fun a ha => absurd ha (by simp) }

omit [DecidableEq I] in
theorem MidGen.undot_d (g : MidGen j hj ν ν₀) : (MidGen.undot j hj ν ν₀ g).d = 0 := rfl

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-- The dots of a generator, placed on top of the generator without dots. -/
theorem pol_mul_midGenKLR_undot (g : MidGen j hj ν ν₀) :
    pol (rename (outPos j ν₀ g.s) (monomial g.d 1)) *
        midGenKLR Q Λ Λc ρ₃ (MidGen.undot j hj ν ν₀ g) = midGenKLR Q Λ Λc ρ₃ g := by
  simp only [midGenKLR, MidGen.undot, MidGen.bot, monomial_zero', map_one, mul_one]
  rw [← mul_assoc, ← mul_assoc, ← (e_commute_pol _ _).eq]

/-- The element of `T̃^λ` giving the dots of a generator, `x^d e(s)`. -/
def midDotElt (g : MidGen j hj ν ν₀) : StendhalAlgebra k Q Λ ν :=
  topMap k Q Λ ν (pol (monomial g.d 1)) * StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.s g.hs

theorem midDotElt_mem (g : MidGen j hj ν ν₀) :
    midDotElt (k := k) (Q := Q) (Λ := Λ) g ∈
      Submodule.span (StendhalAlgebra k Q Λ ν)
        {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.s g.hs} :=
  Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- **Step 2: the dotted generators are left multiples of the generators without dots**:
`x^d e(s) · (v γ_{g₀}) = v γ_g` for `g₀` the generator `g` without dots. -/
theorem midLeftAlg_midDotElt_tmul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (g : MidGen j hj ν ν₀) (v : L) :
    midLeftAlg L hL hR (midDotElt g)
        (Ind.tmul (midGenCorner Q Λ Λc ρ₃ (MidGen.undot j hj ν ν₀ g)) v) =
      Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) v := by
  rw [midDotElt, map_mul, Module.End.mul_apply]
  erw [midLeftAlg_e_tmul_midGenCorner (g := MidGen.undot j hj ν ν₀ g) hR]
  rw [midLeftAlg_topMap,
    midGenCorner_eq_midGen, midGenElt,
    midKLRAct_pol_tmul_midGen hR g.s _ _ (midIdem_mul_midGenKLR (MidGen.undot j hj ν ν₀ g)),
    pol_mul_midGenKLR_undot, ← midGenElt, ← midGenCorner_eq_midGen]

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- The generator without dots, as an index of `Θ`. -/
def MidGen.toShuffle (g : MidGen j hj ν ν₀) : MidShuffle j hj ν ν₀ :=
  ⟨MidGen.undot j hj ν ν₀ g, rfl⟩

/-- `Θ (x^d e(s) ⊗ v) = v γ_g`. -/
theorem midTheta_midDotElt [DecidableEq (MidShuffle j hj ν ν₀)]
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidGen j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midTheta L hL ρ₃ hR (DirectSum.lof (StendhalAlgebra k Q Λ ν) _ (MidLeftSummand Q Λ Λc L)
        (MidGen.toShuffle g) (⟨midDotElt g, midDotElt_mem g⟩ ⊗ₜ v)) =
      (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L) : MidModel j hj Q Λ Λc ν ν₀ L) := by
  rw [midTheta_of_tmul]
  exact midLeftAlg_midDotElt_tmul hR g (v : L)

local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

/-- **Step 3: `Θ` is surjective** (for symmetric `Q`, through the basis of the model). -/
theorem midTheta_surjective [DecidableEq (MidGen j hj ν ν₀)] [DecidableEq (MidShuffle j hj ν ν₀)]
    (hQ : KLRSymm Q) {ρ₂ : Perm (Fin N) → List ℕ}
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    Function.Surjective (midTheta L hL ρ₃ hR) := by
  intro y
  obtain ⟨f, hf⟩ := (midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃).symm.surjective y
  subst hf
  induction f using DFinsupp.induction with
  | h0 => exact ⟨0, by rw [map_zero, map_zero]⟩
  | ha g n f _ _ ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨DirectSum.lof (StendhalAlgebra k Q Λ ν) _ (MidLeftSummand Q Λ Λc L) (MidGen.toShuffle g)
      (⟨midDotElt g, midDotElt_mem g⟩ ⊗ₜ (⟨(n : L), n.2⟩ :
        BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g))) + x, ?_⟩
    rw [map_add, hx, midTheta_midDotElt, map_add, midModelEquiv_symm_single]

end Categorification.Stendhal.CupCap
