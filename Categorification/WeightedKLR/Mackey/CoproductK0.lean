/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndTwist

/-!
# The coproduct on `K₀` of weighted KLR algebras

Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19, states
that `K₀` of the weighted KLR algebras is a twisted bialgebra, with product given by induction
and coproduct by restriction. This file passes from the Mackey formula on `K₀(W_{ν₁} ⊗ W_{ν₂})`
(`exists_resK0_indK0_eq_sum_twistK0`) to `K₀(W_{ν₁}) ⊗_ℤ K₀(W_{ν₂})`, the target of the
coproduct in Theorem 2.19.

## Main results

* `ProjK0.extTensorHom`: the comparison `K₀(A) ⊗_ℤ K₀(B) → K₀(A ⊗ B)`, `[P] ⊗ [Q] ↦ [P ⊠ Q]`,
  over any commutative ring. `ProjK0.ExtTensorBijective` says it is bijective; this is **not**
  proved here for weighted KLR algebras.
* `Juxtapose.extIndIndEquiv`: `Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)` is induction from the middle
  parabolic of `(P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)`, as `W_{a+c} ⊗ W_{b+d}`-modules, over any commutative
  ring; on classes `Juxtapose.middleIndK0_extTensor`.
* `coproductK0`: `Δ_{ν₁,ν₂} : K₀(W_{ν₁+ν₂}) → K₀(W_{ν₁}) ⊗_ℤ K₀(W_{ν₂})`, defined from the
  restriction `resK0` under the hypothesis `ProjK0.ExtTensorBijective` for `(ν₁, ν₂)`.
* `ShuffleLayout.twistedMulK0`: the twisted product `(x_a ⊗ x_b) ⊗ (y_c ⊗ y_d) ↦
  (x_a · y_c) ⊗ (x_b · y_d)` of a shuffle layout, and `ShuffleLayout.extTensorHom_twistedMulK0`
  (unconditional) comparing it with `ResIndPiece.twistK0`.
* `exists_coproductK0_indK0_eq_sum`: **the Mackey formula**
  `Δ_{ν₁,ν₂}(x · y) = ∑ T_L(Δ_{a,b} x ⊗ Δ_{c,d} y)`, summed over the shuffle types, under
  Webster's standing hypothesis and the bijectivity of every comparison map, over any
  commutative ring. The statement is ungraded.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

namespace ProjK0

universe u v

variable {k : Type v} [CommRing k] {A B A' B' : Type u} [Ring A] [Algebra k A] [Ring B]
  [Algebra k B] [Ring A'] [Algebra k A'] [Ring B'] [Algebra k B']

theorem map_congr_extTensor_of (σ : A ≃ₐ[k] A') (τ : B ≃ₐ[k] B') (P : FGProj k A)
    (Q : FGProj k B) :
    map (Algebra.TensorProduct.congr σ τ) (of (extTensorProj P Q)) =
      of (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)) := by
  refine map_of_semilinear _ _ _ (AddEquiv.refl _) fun t x => ?_
  change (t • x : (extTensorProj P Q).carrier) = (Algebra.TensorProduct.congr σ τ t •
    (@id (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier x) :
      (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier)
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [add_smul, map_add, add_smul, ht, ht']; rfl
  | tmul a b =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    refine ExtTensor.induction_on (motive := fun x : ExtTensor k P.carrier Q.carrier =>
      ((a ⊗ₜ[k] b) • x : (extTensorProj P Q).carrier) = ((σ a ⊗ₜ[k] τ b) •
        (@id (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier x) :
          (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier)) x ?_ ?_ ?_
    · show ((a ⊗ₜ[k] b) • (0 : (extTensorProj P Q).carrier) : (extTensorProj P Q).carrier) =
        ((σ a ⊗ₜ[k] τ b) • (0 : (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier) :
          (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier)
      rw [smul_zero, smul_zero]; rfl
    · intro p q
      show ExtTensor.tmul (a • p) (b • q) = ExtTensor.tmul (σ.symm (σ a) • p) (τ.symm (τ b) • q)
      rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    · intro x x' hx hx'
      show ((a ⊗ₜ[k] b) • (x + x' : (extTensorProj P Q).carrier) : (extTensorProj P Q).carrier) =
        ((σ a ⊗ₜ[k] τ b) •
          (@id (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier x +
            @id (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier x') :
          (extTensorProj (FGProj.restrict σ P) (FGProj.restrict τ Q)).carrier)
      rw [smul_add, smul_add, hx, hx']; rfl

/-- Transport of external products along isomorphisms of both factors. -/
theorem map_congr_extTensor (σ : A ≃ₐ[k] A') (τ : B ≃ₐ[k] B') (x : ProjK0 k A)
    (y : ProjK0 k B) :
    map (Algebra.TensorProduct.congr σ τ) (extTensor x y) = extTensor (map σ x) (map τ y) := by
  induction x using induction_on generalizing y with
  | of P =>
    induction y using induction_on with
    | of Q => rw [extTensor_of, map_congr_extTensor_of, map_of, map_of, extTensor_of]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

/-- The comparison map `K₀(A) ⊗_ℤ K₀(B) → K₀(A ⊗ B)`, `[P] ⊗ [Q] ↦ [P ⊠ Q]`. -/
def extTensorHom : ProjK0 k A ⊗[ℤ] ProjK0 k B →+ ProjK0 k (A ⊗[k] B) :=
  TensorProduct.liftAddHom extTensor fun r x y => by rw [map_zsmul, AddMonoidHom.smul_apply,
    map_zsmul]

@[simp] theorem extTensorHom_tmul (x : ProjK0 k A) (y : ProjK0 k B) :
    extTensorHom (x ⊗ₜ[ℤ] y) = extTensor x y :=
  TensorProduct.liftAddHom_tmul _ _ _ _

variable (k A B) in
/-- The comparison `K₀(A) ⊗_ℤ K₀(B) → K₀(A ⊗ B)` is bijective. -/
def ExtTensorBijective : Prop := Function.Bijective (extTensorHom : ProjK0 k A ⊗[ℤ] ProjK0 k B →+ _)

/-- The comparison isomorphism `K₀(A) ⊗_ℤ K₀(B) ≅ K₀(A ⊗ B)`, given that it is bijective. -/
def extTensorEquiv (h : ExtTensorBijective k A B) :
    ProjK0 k A ⊗[ℤ] ProjK0 k B ≃+ ProjK0 k (A ⊗[k] B) :=
  AddEquiv.ofBijective extTensorHom h

@[simp] theorem extTensorEquiv_apply (h : ExtTensorBijective k A B)
    (u : ProjK0 k A ⊗[ℤ] ProjK0 k B) : extTensorEquiv h u = extTensorHom u := rfl

end ProjK0


/-! ### Exchanging the middle factors of iterated external products -/

namespace ExtTensor

variable {k : Type*} [CommRing k] {A₁ A₂ A₃ A₄ : Type*} [Ring A₁] [Algebra k A₁] [Ring A₂]
  [Algebra k A₂] [Ring A₃] [Algebra k A₃] [Ring A₄] [Algebra k A₄]
  {M₁ M₂ M₃ M₄ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁] [IsScalarTower k A₁ M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂] [IsScalarTower k A₂ M₂]
  [AddCommGroup M₃] [Module k M₃] [Module A₃ M₃] [IsScalarTower k A₃ M₃]
  [AddCommGroup M₄] [Module k M₄] [Module A₄ M₄] [IsScalarTower k A₄ M₄]

/-- The exchange `(M₁ ⊠ M₂) ⊠ (M₃ ⊠ M₄) ≅ (M₁ ⊠ M₃) ⊠ (M₂ ⊠ M₄)` of the middle factors; it is
semilinear along the exchange of the middle tensor factors of the algebras
(`ExtTensor.middleComm_smul`). -/
def middleComm : ExtTensor k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄) ≃ₗ[k]
    ExtTensor k (ExtTensor k M₁ M₃) (ExtTensor k M₂ M₄) :=
  TensorProduct.tensorTensorTensorComm k M₁ M₂ M₃ M₄

theorem middleComm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) (m₄ : M₄) :
    middleComm (tmul (tmul m₁ m₂) (tmul m₃ m₄) :
        ExtTensor k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄)) =
      tmul (tmul m₁ m₃) (tmul m₂ m₄) := rfl

theorem middleComm_smul (t : (A₁ ⊗[k] A₂) ⊗[k] (A₃ ⊗[k] A₄))
    (x : ExtTensor k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄)) :
    middleComm (t • x) =
      Algebra.TensorProduct.tensorTensorTensorComm k k k k A₁ A₂ A₃ A₄ t • middleComm x := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [add_smul, map_add, hs, ht, map_add, add_smul]
  | tmul s t =>
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' =>
      rw [TensorProduct.add_tmul, add_smul, map_add, hs, hs', map_add, add_smul]
    | tmul a₁ a₂ =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' =>
        rw [TensorProduct.tmul_add, add_smul, map_add, ht, ht', map_add, add_smul]
      | tmul a₃ a₄ =>
        induction x using induction_on with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
        | tmul u v =>
          induction u using induction_on with
          | zero => rw [zero_tmul, smul_zero, map_zero, smul_zero]
          | add u u' hu hu' => rw [add_tmul, smul_add, map_add, hu, hu', map_add, smul_add]
          | tmul m₁ m₂ =>
            induction v using induction_on with
            | zero => rw [tmul_zero, smul_zero, map_zero, smul_zero]
            | add v v' hv hv' => rw [tmul_add, smul_add, map_add, hv, hv', map_add, smul_add]
            | tmul m₃ m₄ =>
              rw [smul_tmul, smul_tmul, smul_tmul, middleComm_tmul, middleComm_tmul,
                Algebra.TensorProduct.tensorTensorTensorComm_tmul, smul_tmul, smul_tmul,
                smul_tmul]

theorem middleComm_symm_smul (t : (A₁ ⊗[k] A₃) ⊗[k] (A₂ ⊗[k] A₄))
    (x : ExtTensor k (ExtTensor k M₁ M₃) (ExtTensor k M₂ M₄)) :
    middleComm.symm (t • x) =
      (Algebra.TensorProduct.tensorTensorTensorComm k k k k A₁ A₂ A₃ A₄).symm t •
        (middleComm.symm x : ExtTensor k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄)) := by
  apply (middleComm (k := k) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (M₄ := M₄)).injective
  rw [LinearEquiv.apply_symm_apply, middleComm_smul, AlgEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end ExtTensor

namespace WeightedKLR

open FullChamber GalleryAlgebra InductionAlong MulOpposite

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

/-! ### Induction from the middle parabolic of external products -/

section MiddleExt

variable {a b c d : I →₀ ℕ}

variable (k Γ a b c d) in
/-- `ι_{a,c} ⊗ ι_{b,d} : (W_a ⊗ W_c) ⊗ (W_b ⊗ W_d) → W_{a+c} ⊗ W_{b+d}`, as the composite
`(ι_{a,c} ⊗ id) ∘ (id ⊗ ι_{b,d})` of non-unital ring maps. -/
abbrev pairInd :=
  (tensorLeft k (WeightedKLRAlgebra k Γ (b + d)) (inductionRingHom k Γ a c) (inductionRingHom_smul k Γ a c)).comp
    (tensorRight k ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) (inductionRingHom k Γ b d) (inductionRingHom_smul k Γ b d))

theorem pairInd_apply (y : ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d))) :
    pairInd k Γ a b c d y = TensorProduct.map (inductionLin k Γ a c) (inductionLin k Γ b d) y := by
  induction y using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem pairInd_smul (r : k) (y : ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d))) :
    pairInd k Γ a b c d (r • y) = r • pairInd k Γ a b c d y := by
  rw [pairInd_apply, pairInd_apply, map_smul]

variable (k Γ a b c d) in
/-- The exchange `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d) ≅ (W_a ⊗ W_c) ⊗ (W_b ⊗ W_d)` of the middle factors. -/
abbrev middleAlgComm : MiddleAlg k Γ a b c d ≃ₐ[k] ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d)) :=
  Algebra.TensorProduct.tensorTensorTensorComm k k k k (WeightedKLRAlgebra k Γ a) (WeightedKLRAlgebra k Γ b) (WeightedKLRAlgebra k Γ c) (WeightedKLRAlgebra k Γ d)

theorem pairInd_middleAlgComm (m : MiddleAlg k Γ a b c d) :
    pairInd k Γ a b c d (middleAlgComm k Γ a b c d m) = middleTop k Γ a b c d m := by
  rw [pairInd_apply]
  rfl

theorem pairInd_one : pairInd k Γ a b c d 1 = middleTop k Γ a b c d 1 := by
  rw [← pairInd_middleAlgComm, map_one (middleAlgComm k Γ a b c d)]

variable (k Γ a b c d) in
/-- The generator `e' = (ι_{a,c} ⊗ ι_{b,d})(1)` of the corner `(W_{a+c} ⊗ W_{b+d}) e'`. -/
def middleTopGen : MiddleTop k Γ a b c d :=
  ⟨middleTop k Γ a b c d 1, by rw [mem_middleTopSub, ← middleTop_mul, one_mul]⟩

variable (Pa : FGProj k (WeightedKLRAlgebra k Γ a)) (Pb : FGProj k (WeightedKLRAlgebra k Γ b)) (Qc : FGProj k (WeightedKLRAlgebra k Γ c)) (Qd : FGProj k (WeightedKLRAlgebra k Γ d))

/-- The bilinear map `(t, (p_a ⊗ p_b) ⊗ (q_c ⊗ q_d)) ↦ t · (1 ⊗ ((p_a ⊗ q_c) ⊗ (p_b ⊗ q_d)))`. -/
def middleIndFun (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d) :=
  (t : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) • Ind.tmul (unitGen (pairInd k Γ a b c d)) (ExtTensor.middleComm n)

theorem middleIndFun_add_left (t t' : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd (t + t') n =
      middleIndFun Pa Pb Qc Qd t n + middleIndFun Pa Pb Qc Qd t' n := by
  rw [middleIndFun, middleIndFun, middleIndFun, Submodule.coe_add, add_smul]

theorem middleIndFun_add_right (t : MiddleTop k Γ a b c d) (n n' : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd t (n + n') =
      middleIndFun Pa Pb Qc Qd t n + middleIndFun Pa Pb Qc Qd t n' := by
  rw [middleIndFun, middleIndFun, middleIndFun, map_add, Ind.tmul_add, smul_add]

theorem middleIndFun_smul_left (r : k) (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd (r • t) n =
      algebraMap k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) r • middleIndFun Pa Pb Qc Qd t n := by
  rw [middleIndFun, middleIndFun, Submodule.coe_smul_of_tower, ← mul_smul, Algebra.smul_def]

theorem middleIndFun_smul_right (r : k) (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd t (r • n) =
      algebraMap k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) r • middleIndFun Pa Pb Qc Qd t n := by
  rw [middleIndFun, middleIndFun, map_smul,
    Ind.tmul_algebraMap_smul k (pairInd_smul (Γ := Γ) (a := a) (b := b) (c := c) (d := d)),
    ← mul_smul, ← mul_smul, Algebra.commutes]

theorem middleIndFun_op_smul (t : MiddleTop k Γ a b c d) (m : MiddleAlg k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd (op m • t) n = middleIndFun Pa Pb Qc Qd t (m • n) := by
  rw [middleIndFun, middleIndFun, coe_op_smul_middleTop, unop_op, mul_smul,
    ExtTensor.middleComm_smul, unitGen_tmul_smul, pairInd_middleAlgComm]

theorem middleIndFun_smul (z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFun Pa Pb Qc Qd (z • t) n = z • middleIndFun Pa Pb Qc Qd t n := by
  rw [middleIndFun, middleIndFun, Submodule.coe_smul, smul_eq_mul, mul_smul]

/-- `t ⊗ ((p_a ⊗ p_b) ⊗ (q_c ⊗ q_d)) ↦ t · (1 ⊗ ((p_a ⊗ q_c) ⊗ (p_b ⊗ q_d)))`. -/
def middleIndFwd :
    BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) →ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))]
      IndK k (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d) :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) =>
        (show IndK k (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d) from middleIndFun Pa Pb Qc Qd t n))
      (fun t t' n => middleIndFun_add_left Pa Pb Qc Qd t t' n)
      (fun r t n => middleIndFun_smul_left Pa Pb Qc Qd r t n)
      (fun t n n' => middleIndFun_add_right Pa Pb Qc Qd t n n')
      (fun r t n => middleIndFun_smul_right Pa Pb Qc Qd r t n))
    (fun t m n => middleIndFun_op_smul Pa Pb Qc Qd t m n)
    (fun z t n => middleIndFun_smul Pa Pb Qc Qd z t n)

theorem middleIndFwd_tmul (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndFwd Pa Pb Qc Qd (BalancedTensor.tmul t n) = middleIndFun Pa Pb Qc Qd t n := rfl

theorem pairInd_smul_middleTopGen (y : ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d))) :
    (pairInd k Γ a b c d y • middleTopGen k Γ a b c d : MiddleTop k Γ a b c d) =
      op ((middleAlgComm k Γ a b c d).symm y) • middleTopGen k Γ a b c d := by
  apply Subtype.ext
  rw [coe_op_smul_middleTop, unop_op, Submodule.coe_smul, smul_eq_mul]
  change pairInd k Γ a b c d y * middleTop k Γ a b c d 1 =
    middleTop k Γ a b c d 1 * middleTop k Γ a b c d ((middleAlgComm k Γ a b c d).symm y)
  rw [← AlgEquiv.apply_symm_apply (middleAlgComm k Γ a b c d) y, pairInd_middleAlgComm,
    AlgEquiv.symm_apply_apply, ← middleTop_mul, ← middleTop_mul, mul_one, one_mul]

/-- The inverse exchange `(P_a ⊠ Q_c) ⊠ (P_b ⊠ Q_d) → (P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)`. -/
def middleCommInv : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier) ≃ₗ[k] ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier) :=
  (ExtTensor.middleComm (k := k) (M₁ := Pa.carrier) (M₂ := Pb.carrier) (M₃ := Qc.carrier)
    (M₄ := Qd.carrier)).symm

theorem middleCommInv_smul (y : ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d)))
    (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleCommInv Pa Pb Qc Qd (y • w) =
      (middleAlgComm k Γ a b c d).symm y • middleCommInv Pa Pb Qc Qd w :=
  ExtTensor.middleComm_symm_smul y w

/-- The map `(z, (p_a ⊗ q_c) ⊗ (p_b ⊗ q_d)) ↦ z · (e' ⊗ ((p_a ⊗ p_b) ⊗ (q_c ⊗ q_d)))`. -/
def middleIndBwdFun (z : Corner (pairInd k Γ a b c d)) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) : BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :=
  (z.1 : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) • BalancedTensor.tmul (middleTopGen k Γ a b c d) (middleCommInv Pa Pb Qc Qd w)

theorem middleIndBwdFun_op_smul (z : Corner (pairInd k Γ a b c d)) (y : ((WeightedKLRAlgebra k Γ a) ⊗[k] (WeightedKLRAlgebra k Γ c)) ⊗[k] ((WeightedKLRAlgebra k Γ b) ⊗[k] (WeightedKLRAlgebra k Γ d))) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndBwdFun Pa Pb Qc Qd (op y • z) w = middleIndBwdFun Pa Pb Qc Qd z (y • w) := by
  unfold middleIndBwdFun
  have h : ((op y • z : Corner (pairInd k Γ a b c d)) : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) =
      (z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) * pairInd k Γ a b c d y := rfl
  rw [h, mul_smul, BalancedTensor.smul_tmul', pairInd_smul_middleTopGen,
    BalancedTensor.op_smul_tmul, middleCommInv_smul]

theorem middleIndBwdFun_smul (r : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (z : Corner (pairInd k Γ a b c d)) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndBwdFun Pa Pb Qc Qd (r • z) w = r • middleIndBwdFun Pa Pb Qc Qd z w := by
  unfold middleIndBwdFun
  have h : ((r • z : Corner (pairInd k Γ a b c d)) : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) = r * (z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) := rfl
  rw [h, mul_smul]

theorem middleIndBwdFun_add_left (z z' : Corner (pairInd k Γ a b c d)) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndBwdFun Pa Pb Qc Qd (z + z') w =
      middleIndBwdFun Pa Pb Qc Qd z w + middleIndBwdFun Pa Pb Qc Qd z' w := by
  unfold middleIndBwdFun
  have h : ((z + z' : Corner (pairInd k Γ a b c d)) : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) = (z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) + (z' : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) := rfl
  rw [h, add_smul]

theorem middleIndBwdFun_add_right (z : Corner (pairInd k Γ a b c d)) (w w' : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndBwdFun Pa Pb Qc Qd z (w + w') =
      middleIndBwdFun Pa Pb Qc Qd z w + middleIndBwdFun Pa Pb Qc Qd z w' := by
  unfold middleIndBwdFun
  rw [map_add, BalancedTensor.tmul_add, smul_add]

/-- `z ⊗ ((p_a ⊗ q_c) ⊗ (p_b ⊗ q_d)) ↦ z · (e' ⊗ ((p_a ⊗ p_b) ⊗ (q_c ⊗ q_d)))`. -/
def middleIndBwd : Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d) →ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))]
    BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :=
  Ind.lift (middleIndBwdFun Pa Pb Qc Qd) (middleIndBwdFun_add_left Pa Pb Qc Qd)
    (middleIndBwdFun_add_right Pa Pb Qc Qd) (middleIndBwdFun_op_smul Pa Pb Qc Qd)
    (middleIndBwdFun_smul Pa Pb Qc Qd)

theorem middleIndBwd_tmul (z : Corner (pairInd k Γ a b c d)) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndBwd Pa Pb Qc Qd (Ind.tmul z w) = middleIndBwdFun Pa Pb Qc Qd z w := rfl

theorem middleTop_one_mul_pairInd_one :
    middleTop k Γ a b c d 1 * pairInd k Γ a b c d 1 = pairInd k Γ a b c d 1 := by
  rw [pairInd_one, ← middleTop_mul, one_mul]

theorem pairInd_one_mul_middleTop_one :
    pairInd k Γ a b c d 1 * middleTop k Γ a b c d 1 = middleTop k Γ a b c d 1 := by
  rw [pairInd_one, ← middleTop_mul, one_mul]

theorem middleIndFwd_bwd_tmul (z : Corner (pairInd k Γ a b c d)) (w : ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) :
    middleIndFwd Pa Pb Qc Qd (middleIndBwd Pa Pb Qc Qd (Ind.tmul z w)) = Ind.tmul z w := by
  rw [middleIndBwd_tmul, middleIndBwdFun, map_smul, middleIndFwd_tmul]
  change ((z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) • middleIndFun Pa Pb Qc Qd (middleTopGen k Γ a b c d)
    (middleCommInv Pa Pb Qc Qd w) : Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d)) = Ind.tmul z w
  rw [middleIndFun, middleCommInv, LinearEquiv.apply_symm_apply, Ind.smul_tmul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change (z : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) * (middleTop k Γ a b c d 1 * pairInd k Γ a b c d 1) = z
  rw [middleTop_one_mul_pairInd_one]
  exact z.2

theorem middleIndFwd_bwd (y : Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d)) :
    middleIndFwd Pa Pb Qc Qd (middleIndBwd Pa Pb Qc Qd y) = y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero (middleIndBwd Pa Pb Qc Qd)]; exact map_zero _
  | tmul z w => exact middleIndFwd_bwd_tmul Pa Pb Qc Qd z w
  | add s t hs ht =>
    rw [map_add (middleIndBwd Pa Pb Qc Qd)]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hs ht)

theorem middleIndBwd_middleIndFun (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :
    middleIndBwd Pa Pb Qc Qd (middleIndFun Pa Pb Qc Qd t n) = BalancedTensor.tmul t n := by
  unfold middleIndFun
  rw [(middleIndBwd Pa Pb Qc Qd).map_smul, middleIndBwd_tmul]
  unfold middleIndBwdFun
  rw [middleCommInv, LinearEquiv.symm_apply_apply, BalancedTensor.smul_tmul',
    BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change (t : (WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) * (pairInd k Γ a b c d 1 * middleTop k Γ a b c d 1) = t
  rw [pairInd_one_mul_middleTop_one]
  exact t.2

theorem middleIndBwd_fwd (x : BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier))) :
    middleIndBwd Pa Pb Qc Qd (middleIndFwd Pa Pb Qc Qd x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero (middleIndFwd Pa Pb Qc Qd)]; exact map_zero _
  | tmul t n => exact middleIndBwd_middleIndFun Pa Pb Qc Qd t n
  | add s t hs ht =>
    rw [map_add (middleIndFwd Pa Pb Qc Qd)]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hs ht)

/-- `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d))` is induction along
`ι_{a,c} ⊗ ι_{b,d}` of `(P_a ⊠ Q_c) ⊠ (P_b ⊠ Q_d)`. -/
def middleIndCommEquiv :
    BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) ≃ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))] IndK k (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (pairInd k Γ a b c d) :=
  { middleIndFwd Pa Pb Qc Qd with
    invFun := middleIndBwd Pa Pb Qc Qd
    left_inv := middleIndBwd_fwd Pa Pb Qc Qd
    right_inv := middleIndFwd_bwd Pa Pb Qc Qd }

/-- First step of `extIndIndEquiv`: `Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d) ≅
Ind_{ι_{a,c} ⊗ id} ((P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d))`. -/
def extIndIndLeft :
    ExtTensor k (ind k Γ a c Pa.carrier Qc.carrier) (ind k Γ b d Pb.carrier Qd.carrier) ≃ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))]
      Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ind k Γ b d Pb.carrier Qd.carrier)) (tensorLeft k (WeightedKLRAlgebra k Γ (b + d)) (inductionRingHom k Γ a c) (inductionRingHom_smul k Γ a c)) :=
  extIndLeft k (WeightedKLRAlgebra k Γ (b + d)) (inductionRingHom k Γ a c)
    (inductionRingHom_smul k Γ a c) (ExtTensor k Pa.carrier Qc.carrier)
    (ind k Γ b d Pb.carrier Qd.carrier)

/-- `extIndRight` for the second factor, with target written as `Ind`. -/
def extIndIndRight :
    ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ind k Γ b d Pb.carrier Qd.carrier) ≃ₗ[(WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)]
      Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (tensorRight k (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ c) (inductionRingHom k Γ b d) (inductionRingHom_smul k Γ b d)) :=
  extIndRight k (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ c) (inductionRingHom k Γ b d)
    (inductionRingHom_smul k Γ b d) (ExtTensor k Pb.carrier Qd.carrier)
    (ExtTensor k Pa.carrier Qc.carrier)

/-- `middleIndCommEquiv` with target written as `Ind` along the composite. -/
def middleIndCommEquivInd :
    BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) ≃ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))]
      Ind (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) ((tensorLeft k (WeightedKLRAlgebra k Γ (b + d)) (inductionRingHom k Γ a c) (inductionRingHom_smul k Γ a c)).comp (tensorRight k (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ c) (inductionRingHom k Γ b d) (inductionRingHom_smul k Γ b d))) :=
  middleIndCommEquiv Pa Pb Qc Qd

/-- **The product of two inductions is induction from the middle parabolic**:
`Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d) ≅ (W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d))`
as `W_{a+c} ⊗ W_{b+d}`-modules, over any commutative ring `k`. This is the module-level step
behind the multiplicativity of the coproduct in Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, Theorem 2.19. -/
def extIndIndEquiv :
    ExtTensor k (ind k Γ a c Pa.carrier Qc.carrier) (ind k Γ b d Pb.carrier Qd.carrier) ≃ₗ[(WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))]
      BalancedTensor k ((WeightedKLRAlgebra k Γ (a + c)) ⊗[k] (WeightedKLRAlgebra k Γ (b + d))) (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) (ExtTensor k (ExtTensor k Pa.carrier Pb.carrier) (ExtTensor k Qc.carrier Qd.carrier)) :=
  (extIndIndLeft Pa Pb Qc Qd).trans ((Ind.mapEquiv (extIndIndRight Pa Pb Qc Qd)).trans
    ((compEquiv (ExtTensor k (ExtTensor k Pa.carrier Qc.carrier) (ExtTensor k Pb.carrier Qd.carrier)) (tensorRight k (WeightedKLRAlgebra k Γ a ⊗[k] WeightedKLRAlgebra k Γ c) (inductionRingHom k Γ b d) (inductionRingHom_smul k Γ b d)) (tensorLeft k (WeightedKLRAlgebra k Γ (b + d)) (inductionRingHom k Γ a c) (inductionRingHom_smul k Γ a c))).trans (middleIndCommEquivInd Pa Pb Qc Qd).symm))

/-- On classes: `[(W_{a+c} ⊗ W_{b+d}) e' ⊗ ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d))] =
[Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)]` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem middleIndK0_extTensor_of :
    middleIndK0 k Γ a b c d (ProjK0.of (ProjK0.extTensorProj (ProjK0.extTensorProj Pa Pb)
      (ProjK0.extTensorProj Qc Qd))) =
      ProjK0.of (ProjK0.extTensorProj (indProj Pa Qc) (indProj Pb Qd)) := by
  rw [middleIndK0_of]
  exact ProjK0.of_eq_of_iso (extIndIndEquiv Pa Pb Qc Qd).symm

end MiddleExt

/-- **Induction from the middle parabolic of an external product of external products**:
`middleInd ((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)` in
`K₀(W_{a+c} ⊗ W_{b+d})`, over any commutative ring `k` (Webster, arXiv:1209.2463v4,
Theorem 2.19). -/
theorem middleIndK0_extTensor (xa : ProjK0 k (WeightedKLRAlgebra k Γ a))
    (xb : ProjK0 k (WeightedKLRAlgebra k Γ b)) (yc : ProjK0 k (WeightedKLRAlgebra k Γ c))
    (yd : ProjK0 k (WeightedKLRAlgebra k Γ d)) :
    middleIndK0 k Γ a b c d (ProjK0.extTensor (ProjK0.extTensor xa xb) (ProjK0.extTensor yc yd)) =
      ProjK0.extTensor (indK0 a c xa yc) (indK0 b d xb yd) := by
  induction xa using ProjK0.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]
  | of Pa =>
    induction xb using ProjK0.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
    | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]
    | of Pb =>
      induction yc using ProjK0.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
      | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]
      | of Qc =>
        induction yd using ProjK0.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | neg x hx => simp only [map_neg, hx]
        | of Qd =>
          rw [ProjK0.extTensor_of, ProjK0.extTensor_of, ProjK0.extTensor_of, indK0_of, indK0_of,
            ProjK0.extTensor_of]
          exact middleIndK0_extTensor_of Pa Pb Qc Qd

end Juxtapose

open Juxtapose

/-! ### The coproduct on `K₀ ⊗ K₀` and the Mackey formula -/

section Coproduct

variable (k Γ) in
/-- Induction on `K₀(W_μ) ⊗_ℤ K₀(W_{μ'}) → K₀(W_ν)` for `μ + μ' = ν`:
`x ⊗ y ↦ x · y`, the weighted KLR algebras of `μ + μ'` and `ν` identified by `castW`
(Webster, arXiv:1209.2463v4, §2.4). -/
def indTensorK0 (μ μ' ν : I →₀ ℕ) (h : μ + μ' = ν) :
    ProjK0 k (WeightedKLRAlgebra k Γ μ) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ μ') →ₗ[ℤ]
      ProjK0 k (WeightedKLRAlgebra k Γ ν) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun x y => ProjK0.map (castW k Γ h) (indK0 μ μ' x y))
    (fun x x' y => by rw [map_add, AddMonoidHom.add_apply, map_add])
    (fun n x y => by rw [map_zsmul, AddMonoidHom.smul_apply, map_zsmul])
    (fun x y y' => by rw [map_add, map_add])
    (fun n x y => by rw [map_zsmul, map_zsmul]))

theorem indTensorK0_tmul {μ μ' ν : I →₀ ℕ} (h : μ + μ' = ν)
    (x : ProjK0 k (WeightedKLRAlgebra k Γ μ)) (y : ProjK0 k (WeightedKLRAlgebra k Γ μ')) :
    indTensorK0 k Γ μ μ' ν h (x ⊗ₜ[ℤ] y) = ProjK0.map (castW k Γ h) (indK0 μ μ' x y) :=
  TensorProduct.lift.tmul _ _

section Def

variable {ν₁ ν₂ : I →₀ ℕ} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

variable (ν₁ ν₂) in
/-- **The coproduct component of Webster's Theorem 2.19 on `K₀ ⊗ K₀`** (arXiv:1209.2463v4,
§2.4): `Δ_{ν₁,ν₂} : K₀(W_{ν₁+ν₂}) → K₀(W_{ν₁}) ⊗_ℤ K₀(W_{ν₂})`, `[L] ↦ [Res_{ν₁;ν₂} L]`
composed with the inverse of the comparison `K₀(W_{ν₁}) ⊗_ℤ K₀(W_{ν₂}) → K₀(W_{ν₁} ⊗ W_{ν₂})`.
It is defined under the hypothesis `h` that this comparison is bijective, which is not
proved here. -/
def coproductK0 (h : ProjK0.ExtTensorBijective k (WeightedKLRAlgebra k Γ ν₁)
      (WeightedKLRAlgebra k Γ ν₂)) :
    ProjK0 k (WeightedKLRAlgebra k Γ (ν₁ + ν₂)) →+
      ProjK0 k (WeightedKLRAlgebra k Γ ν₁) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ ν₂) :=
  (ProjK0.extTensorEquiv h).symm.toAddMonoidHom.comp (resK0 ν₁ ν₂ hD hZ hS)

theorem extTensorHom_coproductK0 (h : ProjK0.ExtTensorBijective k (WeightedKLRAlgebra k Γ ν₁) (WeightedKLRAlgebra k Γ ν₂))
    (x : ProjK0 k (WeightedKLRAlgebra k Γ (ν₁ + ν₂))) :
    ProjK0.extTensorHom (coproductK0 ν₁ ν₂ hD hZ hS h x) = resK0 ν₁ ν₂ hD hZ hS x := by
  rw [← ProjK0.extTensorEquiv_apply h]
  exact (ProjK0.extTensorEquiv h).apply_symm_apply _

end Def

namespace ShuffleLayout

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂)

variable (k Γ) in
/-- **The twisted product of a shuffle layout** on `K₀ ⊗ K₀`:
`(x_a ⊗ x_b) ⊗ (y_c ⊗ y_d) ↦ (x_a · y_c) ⊗ (x_b · y_d)`, from
`(K₀(W_a) ⊗ K₀(W_b)) ⊗ (K₀(W_c) ⊗ K₀(W_d))` to `K₀(W_{ν₁}) ⊗ K₀(W_{ν₂})` (Webster,
arXiv:1209.2463v4, Theorem 2.19; ungraded, so no twist by a power of `q` appears). -/
def twistedMulK0 :
    (ProjK0 k (WeightedKLRAlgebra k Γ L.a) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ L.b)) ⊗[ℤ]
        (ProjK0 k (WeightedKLRAlgebra k Γ L.c) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ L.d)) →ₗ[ℤ]
      ProjK0 k (WeightedKLRAlgebra k Γ ν₁) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ ν₂) :=
  TensorProduct.map (indTensorK0 k Γ L.a L.c ν₁ L.hac) (indTensorK0 k Γ L.b L.d ν₂ L.hbd) ∘ₗ
    (TensorProduct.tensorTensorTensorComm ℤ _ _ _ _).toLinearMap

theorem twistedMulK0_tmul (xa : ProjK0 k (WeightedKLRAlgebra k Γ L.a))
    (xb : ProjK0 k (WeightedKLRAlgebra k Γ L.b)) (yc : ProjK0 k (WeightedKLRAlgebra k Γ L.c))
    (yd : ProjK0 k (WeightedKLRAlgebra k Γ L.d)) :
    twistedMulK0 k Γ L ((xa ⊗ₜ[ℤ] xb) ⊗ₜ[ℤ] (yc ⊗ₜ[ℤ] yd)) =
      ProjK0.map (castW k Γ L.hac) (indK0 L.a L.c xa yc) ⊗ₜ[ℤ]
        ProjK0.map (castW k Γ L.hbd) (indK0 L.b L.d xb yd) := by
  rw [← indTensorK0_tmul, ← indTensorK0_tmul]
  rfl

/-- The twisted product of a shuffle layout under the comparison maps is the twisted
`Ind ∘ Res` of `ResIndPiece.twistK0`: `extTensorHom (T_L (u ⊗ w)) =
(Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (extTensorHom u ⊠ extTensorHom w)`, over any commutative
ring `k` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem extTensorHom_twistedMulK0
    (u : ProjK0 k (WeightedKLRAlgebra k Γ L.a) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ L.b))
    (w : ProjK0 k (WeightedKLRAlgebra k Γ L.c) ⊗[ℤ] ProjK0 k (WeightedKLRAlgebra k Γ L.d)) :
    ProjK0.extTensorHom (twistedMulK0 k Γ L (u ⊗ₜ[ℤ] w)) =
      ProjK0.map (L.leftEquiv k Γ) (middleIndK0 k Γ L.a L.b L.c L.d
        (ProjK0.extTensor (ProjK0.extTensorHom u) (ProjK0.extTensorHom w))) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [TensorProduct.add_tmul, map_add, AddMonoidHom.add_apply, hu, hu']
  | tmul xa xb =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul yc yd =>
      rw [twistedMulK0_tmul, ProjK0.extTensorHom_tmul, ProjK0.extTensorHom_tmul,
        ProjK0.extTensorHom_tmul, middleIndK0_extTensor, ShuffleLayout.leftEquiv,
        ProjK0.map_congr_extTensor]

end ShuffleLayout

/-- **The Mackey formula for the coproduct on `K₀ ⊗ K₀`** (Webster, arXiv:1209.2463v4,
Theorem 2.19, ungraded). For `ν₁ + ν₂ = ν' + ν''`, under Webster's standing hypothesis and
assuming that every comparison `K₀(W_μ) ⊗_ℤ K₀(W_{μ'}) → K₀(W_μ ⊗ W_{μ'})` is bijective
(`hT`, not proved here), there are shuffle layouts `L i`, one for each shuffle type of
`(ν', ν''; ν₁, ν₂)`, with
`Δ_{ν₁,ν₂}(x · y) = ∑ᵢ T_{L i}(Δ_{a,b} x ⊗ Δ_{c,d} y)` for all `x ∈ K₀(W_{ν'})`,
`y ∈ K₀(W_{ν''})`, where `T_L` is `ShuffleLayout.twistedMulK0` and algebras of equal
dimension vectors are identified by `castW`. The identity holds over any commutative ring
`k`; no grading shift appears. -/
theorem exists_coproductK0_indK0_eq_sum (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (hν : ν₁ + ν₂ = ν' + ν'')
    (hT : ∀ μ μ' : I →₀ ℕ, ProjK0.ExtTensorBijective k (WeightedKLRAlgebra k Γ μ)
      (WeightedKLRAlgebra k Γ μ')) :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (x : ProjK0 k (WeightedKLRAlgebra k Γ ν')) (y : ProjK0 k (WeightedKLRAlgebra k Γ ν'')),
        coproductK0 ν₁ ν₂ hD hZ hS (hT ν₁ ν₂)
            (ProjK0.map (castW k Γ hν.symm) (indK0 ν' ν'' x y)) =
          ∑ i, (L i).twistedMulK0 k Γ
            (coproductK0 (L i).a (L i).b hD hZ hS (hT _ _)
                (ProjK0.map (castW k Γ (L i).hab).symm x) ⊗ₜ[ℤ]
              coproductK0 (L i).c (L i).d hD hZ hS (hT _ _)
                (ProjK0.map (castW k Γ (L i).hcd).symm y)) := by
  obtain ⟨n, L, hinj, hrange, h⟩ := exists_resK0_indK0_eq_sum_twistK0 (k := k) hD hZ hS hν
  refine ⟨n, L, hinj, hrange, fun x y => (hT ν₁ ν₂).1 ?_⟩
  rw [extTensorHom_coproductK0, h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ShuffleLayout.extTensorHom_twistedMulK0, extTensorHom_coproductK0,
    extTensorHom_coproductK0, ResIndPiece.twistK0_apply]

end Coproduct

end WeightedKLR

end Categorification
