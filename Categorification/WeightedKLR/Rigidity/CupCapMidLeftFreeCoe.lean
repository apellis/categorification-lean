/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeViolated
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeProjective
import Categorification.WeightedKLR.Rigidity.CupCapMidKLRAll
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMapEquiv
import Categorification.WeightedKLR.Rigidity.CupCapLeftProjective

/-!
# `K^{λ⁺}_λ` is projective as a left `T^λ`-module, for a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j` (every `j ≤ ℓ`).

The comparison map `Θ : ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g) → K̃^{λ⁺}_λ` over the block shuffles is
bijective (`midThetaBlock_bijective`, in the model of `midCapModelEquiv`), so `K̃^{λ⁺}_λ` is a
projective left `T̃^λ`-module when each piece `L e(t)` is projective over `k`. The violated
diagrams of `K̃^{λ⁺}_λ` lie in `V_λ K̃` (`op_smul_mem_midViolatedSub` for those violated below
the cap), so `K^{λ⁺}_λ = K̃^{λ⁺}_λ / V_λ K̃ = T^λ ⊗_{T̃^λ} K̃^{λ⁺}_λ`, which is projective over
`T^λ` (`projective_of_surjective_of_ker_le`).

Route hypotheses (tracked): `Q` symmetric, invertible cup scalars and both pull-off identities
(as for `midCapModelEquiv`), and the pieces `L e(t)` finitely generated over `k` (for the
bijectivity of `Θ`). Webster's statement is for `L = L_μ` over a field; here the pieces are
assumed projective over `k`, which holds over a field.

## Main results

* `midCapModelEquiv_mem_of_mem_violated`: the violated diagrams lie in `V_λ K̃`, in the model.
* `projective_midCapBimodule`: `K^{λ⁺}_λ` is a projective left `T^λ`-module.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "V" => StendhalAlgebra.violatedIdeal k Q Λ ν
local notation "Ev" => Env k Q Λ Λc j hj ν ν₀

/-- The idempotent `e(s)` of `T̃^λ` is idempotent. -/
theorem isIdempotentElem_stendhalE (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    IsIdempotentElem (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) s hs) := by
  rw [← topMap_e_of_isRedOrdered s hs]
  exact (show IsIdempotentElem (KLRAlgebra.e (k := k) (Q := stendhalQ Q Λ) s) from
    KLRAlgebra.e_mul_self s).map (topMap k Q Λ ν)

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (L) in
/-- The class in `K^{λ⁺}_λ` of an element of `K̃^{λ⁺}_λ`. -/
def toMidCap (y : CapTilde k Q Λ Λc j hj ν ν₀ L) : CapBimodule k Q Λ Λc j hj ν ν₀ L :=
  Submodule.Quotient.mk y

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem toMidCap_add (y y' : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    toMidCap L (y + y') = toMidCap L y + toMidCap L y' :=
  Submodule.Quotient.mk_add _

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem toMidCap_envMk_smul (a : T) (y : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    toMidCap L ((Env.mk a 1 : Ev) • y) = TensorProductAlgebra.mk Q Λ ν a • toMidCap L y :=
  rfl

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

variable (L hL) in
/-- The model with its left action, as the bimodule. -/
def midLeftToBimod (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    MidLeftModel L hL hR ≃+ MidBimod L hL hR where
  toFun y := toMidBimod L hL hR y
  invFun y := ofMidBimod L hL hR y
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem midLeftToBimod_smul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : T)
    (y : MidLeftModel L hL hR) :
    midLeftToBimod L hL hR (a • y) = (Env.mk a 1 : Ev) • midLeftToBimod L hL hR y := by
  change toMidBimod L hL hR (midLeftAlg L hL hR a y) = _
  rw [midBimod_smul, midEnvAlg_mk, op_one, one_smul]
  rfl

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- `V_λ K̃` is stable under the action of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`. -/
theorem midEnvAlg_mem_midViolatedSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (r : Ev)
    {y : MidLeftModel L hL hR} (hy : y ∈ midViolatedSub L hL hR) :
    (midLeftToBimod L hL hR).symm (r • midLeftToBimod L hL hR y) ∈ midViolatedSub L hL hR := by
  change (midEnvAlg L hL hR r y : MidModel j hj Q Λ Λc ν ν₀ L) ∈ midViolatedSub L hL hR
  induction r using TensorProduct.inductionOn with
  | tmul a c =>
    have h := midEnvAlg_mk hR a (unop c) y
    change midEnvAlg L hL hR (Env.mk a (unop c)) y ∈ _
    rw [h]
    exact Submodule.smul_mem _ a (midRightLin_mem_midViolatedSub hR (op (unop c)) hy)
  | add r r' hr hr' =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem hr hr'

/-- **The violated diagrams lie in `V_λ K̃`** (arXiv:1309.3796v3, §7.3, after Lemma 7.19), in the
model: those violated above the cap by definition, those violated below it by
`op_smul_mem_midViolatedSub`. -/
theorem midCapModelEquiv_mem_of_mem_violated [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    {z : CapTilde k Q Λ Λc j hj ν ν₀ L} (hz : z ∈ violated k Q Λ Λc j hj ν ν₀ L) :
    (midLeftToBimod L hL hR).symm (midCapModelEquiv hP hPL hκ hR z) ∈
      midViolatedSub L hL hR := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, y, rfl⟩ | ⟨b, hb, y, rfl⟩
    · rw [map_smul]
      have h := midLeftToBimod_smul hR a
        ((midLeftToBimod L hL hR).symm (midCapModelEquiv hP hPL hκ hR y))
      rw [AddEquiv.apply_symm_apply] at h
      rw [← h, AddEquiv.symm_apply_apply]
      exact smul_mem_midViolatedSub hR ha _
    · rw [map_smul]
      change (midEnvAlg L hL hR (Env.mk 1 b) _ : MidModel j hj Q Λ Λc ν ν₀ L) ∈ _
      rw [midEnvAlg_mk, map_one, Module.End.one_apply]
      exact op_smul_mem_midViolatedSub hR hρ₃ hP hκ hb _
  | zero =>
    rw [map_zero, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [map_smul]
    have h := midEnvAlg_mem_midViolatedSub hR r hx
    rwa [AddEquiv.apply_symm_apply] at h

/-- **`K^{λ⁺}_λ` is a projective left `T^λ`-module, for a cap after `λ_j`**
(arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19), for `L` supported on the cap-good
loadings with pieces `L e(t)` finitely generated and projective over `k`.

Route hypotheses (tracked): `Q` symmetric, invertible cup scalars, the pull-off identities
`PullOff` and `PullOffLeft`, and the finite generation of the pieces `L e(t)`. -/
theorem projective_midCapBimodule
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hQ : KLRSymm Q) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L)
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    Module.Projective (TensorProductAlgebra k Q Λ ν) (CapBimodule k Q Λ Λc j hj ν ν₀ L) := by
  classical
  choose ρ₃ hρ₃ using fun w => exists_reduced M w
  have hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL := midKLRRel hκ hP hPL
  let Θ := LinearEquiv.ofBijective (midThetaBlock L hL ρ₃ hR)
    (midThetaBlock_bijective hR hQ hρ₃ hP hκ hfin)
  let E := midCapModelEquiv hP hPL hκ hR
  have h1 : ∀ b : MidBlockShuffle j hj ν ν₀, Module.Projective T
      (Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs}) :=
    fun b => projective_span_singleton_of_isIdempotentElem (isIdempotentElem_stendhalE _ _)
  have h2 : ∀ b : MidBlockShuffle j hj ν ν₀, Module.Projective k
      (BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc b.1.1)) :=
    fun b => hproj b.1.1.t b.1.1.ht
  have h3 : ∀ b : MidBlockShuffle j hj ν ν₀, Module.Projective T
      (MidLeftSummand Q Λ Λc L b.1) := fun b => by
    have := h1 b
    have := h2 b
    exact Module.Projective.tensorProduct
  have hSrc : Module.Projective T (MidBlockSrc j hj Q Λ Λc ν ν₀ L) :=
    Module.Projective.directSum
  let f : MidBlockSrc j hj Q Λ Λc ν ν₀ L →+ CapBimodule k Q Λ Λc j hj ν ν₀ L :=
    { toFun := fun p => toMidCap L (E.symm (midLeftToBimod L hL hR (Θ p)))
      map_zero' := by
        rw [map_zero, map_zero, map_zero]
        exact Submodule.Quotient.mk_zero _
      map_add' := fun p p' => by
        rw [map_add, map_add, map_add, toMidCap_add] }
  have hf : ∀ p, f p = toMidCap L (E.symm (midLeftToBimod L hL hR (Θ p))) := fun _ => rfl
  refine projective_of_surjective_of_ker_le (P := MidBlockSrc j hj Q Λ Λc ν ν₀ L)
    (TensorProductAlgebra.mk Q Λ ν).toRingHom
    (fun r => (V).ringCon.mkₐ_surjective (α := k) r) f (fun r p => ?_) (fun z => ?_)
      (fun p hp => ?_)
  · rw [hf, hf, map_smul, midLeftToBimod_smul, map_smul]
    exact toMidCap_envMk_smul r _
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨Θ.symm ((midLeftToBimod L hL hR).symm (E y)), ?_⟩
    rw [hf, LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    rfl
  · rw [hf] at hp
    have hv := midCapModelEquiv_mem_of_mem_violated hP hPL hκ hR hρ₃
      ((Submodule.Quotient.mk_eq_zero _).1 hp)
    rw [LinearEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] at hv
    have key : ∀ w ∈ midViolatedSub L hL hR, Θ.symm w ∈ Submodule.span T
        {x | ∃ r : T, (TensorProductAlgebra.mk Q Λ ν).toRingHom r = 0 ∧ ∃ q, x = r • q} := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, y, rfl⟩ := hx
        rw [map_smul]
        exact Submodule.subset_span ⟨a, tensorAlgebra_mk_eq_zero ha, _, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
    have := key _ hv
    rwa [LinearEquiv.symm_apply_apply] at this

end Categorification.Stendhal.CupCap
