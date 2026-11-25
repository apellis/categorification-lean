/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedOrdinary
import Categorification.WeightedKLR.RedStrands.AdjacentBlockSlide
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived

set_option backward.isDefEq.respectTransparency false

/-!
# The ordinary braid of a partial standard

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition 6.10).
Let `t` be a loading of red order `κ₁ = L ++ b :: a :: M` and let `κ₀ = L ++ a :: b :: M` be the
order with `a` and `b` exchanged. The partial standard of Lemma 6.8 is the loading projective
`e(t) T` modulo the loadings of order `κ₁` whose retained root is strictly higher than that of
`t`. Its ordinary tensor with the braid bimodule `B(κ₁, κ₀)` is the cut `e(t) B(κ₁, κ₀)` modulo
the diagrams through loadings of order `κ₀` with strictly higher retained root.

The forward map multiplies. It is well defined because a diagram of the crossing bimodule
factors through a higher loading of the top order exactly when it factors through one of the
bottom order (`mem_blockUpperIdeal_iff`). The inverse inserts `e(t)` in the tensor.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR MulOpposite DG DG.DegreeZero CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "pt" => mk (ofKLR k Q Λ ν (KLRAlgebra.e t))
local notation:max "E" κ:arg => mk (redProj k Q Λ ν κ)
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "Braid" => OpBimodule T (braidingBimodule k Q Λ ν (redWord t) κ)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t)

/-- The diagrams of `e(t) V e_κ` that factor through a loading of order `κ` whose retained root
is strictly higher than that of `t`. -/
def braidCutUpper : Submodule Uᵐᵒᵖ (violCorner k Q Λ ν t κ) where
  carrier := {y | y.1 ∈ J κ}
  zero_mem' := (J κ).zero_mem
  add_mem' {x y} hx hy := (J κ).add_mem (x := x.1) (y := y.1) hx hy
  smul_mem' u y hy := by
    change y.1 * u.unop.1 ∈ J κ
    exact TwoSidedIdeal.mul_mem_right _ _ _ hy

/-- The cut `e(t) V e_κ` modulo the diagrams through higher loadings of order `κ`. -/
def BraidCutQuotient : Type _ := violCorner k Q Λ ν t κ ⧸ braidCutUpper Q Λ t a b κ

instance : AddCommGroup (BraidCutQuotient Q Λ t a b κ) :=
  Submodule.Quotient.addCommGroup (braidCutUpper Q Λ t a b κ)

instance : Module Uᵐᵒᵖ (BraidCutQuotient Q Λ t a b κ) :=
  Submodule.Quotient.module (braidCutUpper Q Λ t a b κ)

/-- The quotient map onto `BraidCutQuotient`. -/
def braidCutMk : violCorner k Q Λ ν t κ →ₗ[Uᵐᵒᵖ] BraidCutQuotient Q Λ t a b κ :=
  (braidCutUpper Q Λ t a b κ).mkQ

theorem braidCutMk_surjective : Function.Surjective (braidCutMk Q Λ t a b κ) :=
  Submodule.mkQ_surjective _

instance : AddCommGroup P := Submodule.addCommGroup P
instance : Module Tᵐᵒᵖ P := Submodule.module P

/-- The partial standard `e(t) T / K` of Lemma 6.8. -/
def PartialStandardQuotient : Type _ := P ⧸ K

instance : AddCommGroup (PartialStandardQuotient Q Λ t a b) := Submodule.Quotient.addCommGroup K

instance : Module Tᵐᵒᵖ (PartialStandardQuotient Q Λ t a b) := Submodule.Quotient.module K

/-- The quotient map onto the partial standard. -/
def partialStandardMk : P →ₗ[Tᵐᵒᵖ] PartialStandardQuotient Q Λ t a b := (K).mkQ

theorem partialStandardMk_surjective : Function.Surjective (partialStandardMk Q Λ t a b) :=
  Submodule.mkQ_surjective _

theorem partialStandardMk_eq_zero {x : P} (hx : x ∈ K) : partialStandardMk Q Λ t a b x = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 hx

variable {Q Λ t a b} in
/-- Additive maps out of the partial standard. -/
def partialStandardLift {G : Type*} [AddCommGroup G] (f : P →+ G) (hf : ∀ x ∈ K, f x = 0) :
    PartialStandardQuotient Q Λ t a b →+ G :=
  QuotientAddGroup.lift (K).toAddSubgroup f fun x hx => hf x hx

theorem partialStandardLift_mk {G : Type*} [AddCommGroup G] (f : P →+ G)
    (hf : ∀ x ∈ K, f x = 0) (x : P) :
    partialStandardLift f hf (partialStandardMk Q Λ t a b x) = f x :=
  rfl

variable {Q Λ t a b κ} in
/-- Additive maps out of `BraidCutQuotient`. -/
def braidCutLift {G : Type*} [AddCommGroup G] (f : violCorner k Q Λ ν t κ →+ G)
    (hf : ∀ y ∈ braidCutUpper Q Λ t a b κ, f y = 0) : BraidCutQuotient Q Λ t a b κ →+ G :=
  QuotientAddGroup.lift (braidCutUpper Q Λ t a b κ).toAddSubgroup f fun y hy => hf y hy

theorem braidCutLift_mk {G : Type*} [AddCommGroup G] (f : violCorner k Q Λ ν t κ →+ G)
    (hf : ∀ y ∈ braidCutUpper Q Λ t a b κ, f y = 0) (y : violCorner k Q Λ ν t κ) :
    braidCutLift f hf (braidCutMk Q Λ t a b κ y) = f y :=
  rfl

local notation "Y" => BraidCutQuotient Q Λ t a b κ
local notation "Xq" => PartialStandardQuotient Q Λ t a b
local notation "TP" => TensorProductOver Tᵐᵒᵖ (InDegreeZero Braid) (InDegreeZero Xq)

private theorem pt_mul_pt : pt * pt = pt :=
  congrArg Subtype.val (orderedLoadingIdem_idem Q Λ t).eq

variable {Q Λ t} in
private theorem rIdeal_val_left (x : P) : pt * x.1.1 = x.1.1 := congrArg Subtype.val x.2

/-- Multiplication `e(t) T × B(κ₁, κ) → e(t) V e_κ`. -/
private def cutMul : P →+ Braid →+ violCorner k Q Λ ν t κ where
  toFun x :=
    { toFun := fun β => ⟨x.1.1 * (β : braidingBimodule k Q Λ ν (redWord t) κ).1,
        mem_violCorner_iff.2 ⟨by rw [← mul_assoc, rIdeal_val_left],
          by rw [mul_assoc, (mem_cornerBimodule.1
            (β : braidingBimodule k Q Λ ν (redWord t) κ).2).2]⟩⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun β β' => Subtype.ext (mul_add x.1.1 _ _) }
  map_zero' := AddMonoidHom.ext fun β => Subtype.ext (zero_mul _)
  map_add' x x' := AddMonoidHom.ext fun β => Subtype.ext (add_mul x.1.1 x'.1.1 _)

variable {L M : List (Fin ℓ)}

variable {Q Λ t a b κ} in
/-- A diagram `e(t) x` of the crossing bimodule, with `x` through a higher loading of the top
order, factors through a higher loading of the bottom order. -/
private theorem cutMul_mem (ht : redWord t = L ++ b :: a :: M) (hκ : κ = L ++ a :: b :: M)
    (x : P) (hx : x ∈ K) (β : Braid) :
    (cutMul Q Λ t κ x β).1 ∈ J κ := by
  subst hκ
  let β' : braidingBimodule k Q Λ ν (redWord t) (L ++ a :: b :: M) := β
  have hβ := mem_cornerBimodule.1 β'.2
  have hz : x.1.1 * β'.1 ∈ J (redWord t) := TwoSidedIdeal.mul_mem_right _ _ _ hx
  refine (mem_blockUpperIdeal_iff ?_ ?_).2 (by rw [← ht]; exact hz)
  · change E (L ++ b :: a :: M) * (x.1.1 * β'.1) = x.1.1 * β'.1
    rw [← ht, ← mul_assoc,
      corner_mul_left (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)) x.1]
  · change x.1.1 * β'.1 * E (L ++ a :: b :: M) = x.1.1 * β'.1
    rw [mul_assoc, hβ.2]

/-- Multiplication into the cut, modulo higher loadings of the bottom order. -/
private def cutMulQ : P →+ Braid →+ Y where
  toFun x := (braidCutMk Q Λ t a b κ).toAddMonoidHom.comp (cutMul Q Λ t κ x)
  map_zero' := by ext β; simp
  map_add' x x' := by ext β; simp

variable {Q Λ t a b κ} in
private def cutMulX (ht : redWord t = L ++ b :: a :: M) (hκ : κ = L ++ a :: b :: M) :
    Xq →+ Braid →+ Y :=
  partialStandardLift (cutMulQ Q Λ t a b κ) fun x hx => by
    ext β
    exact (Submodule.Quotient.mk_eq_zero _).2 (cutMul_mem ht hκ x hx β)

variable {Q Λ t a b κ} in
/-- The multiplication map `B(κ₁, κ) ⊗ (e(t) T / K) → e(t) V e_κ / (higher)`. -/
def partialStandardTensorMul (ht : redWord t = L ++ b :: a :: M) (hκ : κ = L ++ a :: b :: M) :
    TP →+ Y :=
  TensorProductOver.lift (cutMulX ht hκ).flip fun c β n => by
    obtain ⟨x, rfl⟩ := partialStandardMk_surjective Q Λ t a b n
    change braidCutMk Q Λ t a b κ (cutMul Q Λ t κ x (c.unop • β)) =
      braidCutMk Q Λ t a b κ (cutMul Q Λ t κ (c • x) β)
    congr 1
    exact Subtype.ext (mul_assoc _ _ _).symm

/-- The cut `e_{κ₁} v e_κ` of an element of `V`, as an element of the braid bimodule. -/
private def braidCut : V →+ Braid where
  toFun v := (⟨E (redWord t) * v * E κ, mem_cornerBimodule.2
    ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq],
      by rw [mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq]⟩⟩ :
    braidingBimodule k Q Λ ν (redWord t) κ)
  map_zero' := Subtype.ext (by
    change E (redWord t) * 0 * E κ = 0
    rw [mul_zero, zero_mul])
  map_add' v v' := Subtype.ext (by
    change E (redWord t) * (v + v') * E κ = E (redWord t) * v * E κ + E (redWord t) * v' * E κ
    rw [mul_add, add_mul])

/-- The generator `e(t)` of the partial standard. -/
private def partialStandardGen : Xq :=
  partialStandardMk Q Λ t a b ⟨orderedLoadingIdem Q Λ t, (orderedLoadingIdem_idem Q Λ t).eq⟩

/-- `v ↦ e_{κ₁} v e_κ ⊗ e(t)`. -/
private def braidTmul : V →+ TP :=
  ((TensorProductOver.tmulAddHom Tᵐᵒᵖ (InDegreeZero Braid) (InDegreeZero Xq)).flip
    (partialStandardGen Q Λ t a b)).comp (braidCut Q Λ t κ)

/-- `e(t) y` as an element of `e(t) T`. -/
private def loadingMul (y : T) : P :=
  ⟨⟨pt * y.1, (Subsemigroup.mem_corner_iff
    (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
      ⟨by
        have h : E (redWord t) * pt = pt := corner_mul_left _ (orderedLoadingIdem Q Λ t)
        rw [← mul_assoc, h],
        by rw [mul_assoc, corner_mul_right _ y]⟩⟩,
    Subtype.ext (by
      change pt * (pt * y.1) = pt * y.1
      rw [← mul_assoc, pt_mul_pt])⟩

private theorem op_smul_partialStandardGen (y : T) :
    (op y • partialStandardGen Q Λ t a b : Xq) =
      partialStandardMk Q Λ t a b (loadingMul Q Λ t y) :=
  (map_smul (partialStandardMk Q Λ t a b) (op y) _).symm

/-- Diagrams through higher loadings of the top order vanish in the tensor. -/
private theorem braidTmul_eq_zero {v : V} (hv : v ∈ J (redWord t)) :
    braidTmul Q Λ t a b κ v = 0 := by
  rw [blockUpperIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, ⟨c, -, _, ⟨s, hs, hlt, rfl⟩, rfl⟩, d, -, rfl⟩ := hx
    have hsE : mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * E (redWord t) =
        mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) := by
      rw [← map_mul, e_mul_redProj, ite_eq_left hs]
    let y : T := ⟨E (redWord t) * c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)),
      (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
        ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq],
          by rw [mul_assoc, hsE]⟩⟩
    have hcut : braidCut Q Λ t κ (c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) =
        (op (op y) • braidCut Q Λ t κ d : Braid) := by
      apply Subtype.ext
      change E (redWord t) * (c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) * E κ =
        E (redWord t) * c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * (E (redWord t) * d * E κ)
      calc E (redWord t) * (c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) * E κ
          = E (redWord t) * c * (mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * E (redWord t)) * d *
              E κ := by rw [hsE]; simp only [mul_assoc]
        _ = _ := by simp only [mul_assoc]
    have hK : loadingMul Q Λ t y ∈ K := by
      change pt * (E (redWord t) * c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s))) ∈ J (redWord t)
      rw [← mul_assoc, ← mul_assoc]
      exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨s, hs, hlt, rfl⟩)
    change TensorProductOver.tmul Tᵐᵒᵖ
      (braidCut Q Λ t κ (c * mk (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) : InDegreeZero Braid)
        (partialStandardGen Q Λ t a b) = 0
    rw [hcut, TensorProductOver.op_smul_tmul, op_smul_partialStandardGen,
      partialStandardMk_eq_zero Q Λ t a b hK, TensorProductOver.tmul_zero]
  | zero => exact map_zero _
  | add _ _ _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | neg _ _ hu => rw [map_neg, hu, neg_zero]

variable {Q Λ t a b κ} in
/-- The inverse map `e(t) V e_κ / (higher) → B(κ₁, κ) ⊗ (e(t) T / K)`, `y ↦ y ⊗ e(t)`. -/
private def partialStandardTensorInv (ht : redWord t = L ++ b :: a :: M)
    (hκ : κ = L ++ a :: b :: M) : Y →+ TP :=
  braidCutLift ((braidTmul Q Λ t a b κ).comp (violCorner k Q Λ ν t κ).subtype.toAddMonoidHom)
    fun y hy => by
      subst hκ
      have hy' := mem_violCorner_iff.1 y.2
      apply braidTmul_eq_zero
      have h1 : E (L ++ b :: a :: M) * y.1 = y.1 := by
        rw [← ht, ← hy'.1, ← mul_assoc, ← map_mul, redProj_mul_e, ite_eq_left rfl]
      have := (mem_blockUpperIdeal_iff h1 hy'.2).1 hy
      rw [ht]
      exact this

variable {Q Λ t a b κ} in
/-- **The ordinary braid of a partial standard** (part of the proof of Webster,
arXiv:1309.3796v2, Proposition 6.9). For a loading `t` of red order `L ++ b :: a :: M`, the
tensor of the braid bimodule `B(κ₁, κ₀)` with the partial standard `e(t) T / K` is the cut
`e(t) V e_{κ₀}` modulo the diagrams through loadings of order `κ₀ = L ++ a :: b :: M` with
strictly higher retained root. -/
def partialStandardTensorEquiv (ht : redWord t = L ++ b :: a :: M)
    (hκ : κ = L ++ a :: b :: M) : TP ≃ₗ[Uᵐᵒᵖ] Y := by
  refine { partialStandardTensorMul ht hκ with
    invFun := partialStandardTensorInv ht hκ
    left_inv := ?_
    right_inv := ?_
    map_smul' := ?_ }
  · intro u z
    have h : (partialStandardTensorMul ht hκ).comp (DistribSMul.toAddMonoidHom TP u) =
        (DistribSMul.toAddMonoidHom Y u).comp (partialStandardTensorMul ht hκ) := by
      apply TensorProductOver.addHom_ext
      intro β n
      obtain ⟨x, rfl⟩ := partialStandardMk_surjective Q Λ t a b n
      change braidCutMk Q Λ t a b κ (cutMul Q Λ t κ x (u • β)) =
        u • braidCutMk Q Λ t a b κ (cutMul Q Λ t κ x β)
      rw [← map_smul]
      congr 1
      exact Subtype.ext (mul_assoc _ _ _).symm
    exact DFunLike.congr_fun h z
  · have h : (partialStandardTensorInv ht hκ).comp (partialStandardTensorMul ht hκ) =
        AddMonoidHom.id TP := by
      apply TensorProductOver.addHom_ext
      intro β n
      obtain ⟨x, rfl⟩ := partialStandardMk_surjective Q Λ t a b n
      have hβ := mem_cornerBimodule.1 (β : braidingBimodule k Q Λ ν (redWord t) κ).2
      have hcut : braidCut Q Λ t κ (x.1.1 * (β : braidingBimodule k Q Λ ν (redWord t) κ).1) =
          (op (op x.1) • β : Braid) := by
        apply Subtype.ext
        change E (redWord t) * (x.1.1 * _) * E κ = x.1.1 * _
        rw [← mul_assoc, corner_mul_left _ x.1, mul_assoc, hβ.2]
      have hx : loadingMul Q Λ t x.1 = x := Subtype.ext (Subtype.ext (rIdeal_val_left x))
      change TensorProductOver.tmul Tᵐᵒᵖ
          (braidCut Q Λ t κ (x.1.1 * (β : braidingBimodule k Q Λ ν (redWord t) κ).1) :
            InDegreeZero Braid) (partialStandardGen Q Λ t a b) =
        TensorProductOver.tmul Tᵐᵒᵖ β (partialStandardMk Q Λ t a b x)
      rw [hcut, TensorProductOver.op_smul_tmul, op_smul_partialStandardGen, hx]
    exact DFunLike.congr_fun h
  · intro z
    obtain ⟨y, rfl⟩ := braidCutMk_surjective Q Λ t a b κ z
    have hy := mem_violCorner_iff.1 y.2
    change braidCutMk Q Λ t a b κ (cutMul Q Λ t κ _ (braidCut Q Λ t κ y.1)) =
      braidCutMk Q Λ t a b κ y
    congr 1
    apply Subtype.ext
    change pt * (E (redWord t) * y.1 * E κ) = y.1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left rfl, hy.1, hy.2]

universe w

variable {Q Λ t a b κ} in
/-- **The braid of a partial standard** (Webster, arXiv:1309.3796v2, Lemma 6.8 with the
tensor computed, as used in the proof of Proposition 6.9). For a loading `t` of red order
`L ++ b :: a :: M`, the derived braid to `κ₀ = L ++ a :: b :: M` of the partial standard at
`t` is, in degree zero, the cut `e(t) V e_{κ₀}` modulo higher loadings of order `κ₀`.

The hypotheses `hfilt` and `hinj` are those of `blockPartialStandard_braidIsoOrdinary`. -/
def blockPartialStandard_braidIso
    [HasDerivedCategory.{w} Tᵐᵒᵖ] [HasDerivedCategory.{w} Uᵐᵒᵖ]
    (ht : redWord t = L ++ b :: a :: M) (hκ : κ = L ++ a :: b :: M)
    (hfilt : ∀ (s : Seq (stendhalWeight ℓ ν)) (hs : redWord s = redWord t),
      ∃ m : List {u : Seq (stendhalWeight ℓ ν) // redWord u = redWord t},
      (∀ u ∈ m, adjacentBlockRoot a b s < adjacentBlockRoot a b u.1) ∧
      ModuleFiltration.HasFiltration
        (fun u => blockPartialStandardAt Q Λ u.1 a b (redWord t) u.2) m
        (blockLoadingKernelObjAt Q Λ a b (redWord t) s hs))
    (hinj : ∀ s : Seq (stendhalWeight ℓ ν), redWord s = redWord t →
      Function.Injective (blockKernelTensorInclusion Q Λ s a b κ)) :
    (braidingFunctor.{w} k Q Λ ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t a b).X₃)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of Uᵐᵒᵖ (InDegreeZero Y)) :=
  blockPartialStandard_braidIsoOrdinary Q Λ t a b κ hfilt hinj ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv (DGModuleEquiv.ofDegreeZero
      (show TP ≃ₗ[Uᵐᵒᵖ] InDegreeZero Y from partialStandardTensorEquiv ht hκ)
      (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
      TensorProductOver.d_inDegreeZero InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _)))

end Categorification.Stendhal.BraidedStendhalAlgebra
