/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIntertwine
import Categorification.KLR.Induction
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.GradedFree

/-!
# The subquotients of the Mackey filtration as balanced tensor products

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18** (TeX lines 1784–1817). For
`ν + ν' = ν'' + ν'''` the `(R(ν) ⊗ R(ν'), R(ν'') ⊗ R(ν'''))`-bimodule `_{ν,ν'}R_{ν'',ν'''}` has a
filtration by bimodules isomorphic to

`(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'} (_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''})
  {-λ·(ν'+λ-ν''')}`,

`R' = R(ν-λ) ⊗ R(λ) ⊗ R(ν'+λ-ν''') ⊗ R(ν'''-λ)`, over all `λ` for which all these weights are
in `ℕ[I]`.

## The data `λ`

We encode `λ` by a `KLRAlgebra.MackeyQuad`: four weights `α = ν - λ`, `β = λ`,
`γ = ν' + λ - ν''' = ν'' + λ - ν` and `δ = ν''' - λ` with `α + β = ν`, `γ + δ = ν'`,
`α + γ = ν''` and `β + δ = ν'''` (for fixed `ν, …, ν'''` a quadruple is determined by `β = λ`,
`MackeyQuad.ext_of_β`).

## Main definitions

* `KLRAlgebra.QuadAlg Q q = (R(α) ⊗ R(β)) ⊗ (R(γ) ⊗ R(δ))`, the paper's `R'`;
  `KLRAlgebra.quadTop q : R' → R(ν) ⊗ R(ν')` (`ι_{α,β} ⊗ ι_{γ,δ}`) and
  `KLRAlgebra.quadBot q : R' → R(ν'') ⊗ R(ν''')` (`ι_{α,γ} ⊗ ι_{β,δ}` after exchanging the two
  middle factors), both multiplicative.
* `KLRAlgebra.MackeyTop Q q = (R(ν) ⊗ R(ν')) (1_{α,β} ⊗ 1_{γ,δ})`, the paper's
  `_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}` (a left ideal of `R(ν) ⊗ R(ν')`, which is the
  tensor product of the two left ideals `R(ν) 1_{α,β}`, `R(ν') 1_{γ,δ}`), a
  `(R(ν) ⊗ R(ν'), R')`-bimodule; `KLRAlgebra.MackeyBot Q q = (1_{α,γ} ⊗ 1_{β,δ}) (R(ν'') ⊗ R(ν'''))`,
  the paper's `_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''}`, an
  `(R', R(ν'') ⊗ R(ν'''))`-bimodule.
* `KLRAlgebra.MackeyX Q q = MackeyTop ⊗_{R'} MackeyBot` (a `Categorification.BalancedTensor`), a
  left `R(ν) ⊗ R(ν')`-module with the right `R(ν'') ⊗ R(ν''')`-action `MackeyX.rightAct`.

The subquotients `F_c / F_{c-1}` of the Mackey filtration (`KLRAlgebra.MackeySubquot`), the maps
`KLRAlgebra.mackeyMap : MackeyX Q q → F_c / F_{c-1}` and their properties are in
`Categorification.KLR.MackeyMap`, `Categorification.KLR.MackeyGraded` (grading shift),
`Categorification.KLR.MackeyIso` (surjectivity) and `Categorification.KLR.MackeyInj`
(injectivity; the direct sum decomposition `KLRAlgebra.mackeySubquot_isInternal`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

/-! ### Transport of sequences -/

omit [DecidableEq I] in
theorem seqCast_eq_cast {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂) (s : Seq μ₁) :
    KLRAlgebra.seqCast h s = Seq.cast h s := by
  subst h; rfl

omit [DecidableEq I] in
theorem seqCast_apply {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂) (s : Seq μ₁)
    (a : Fin (Multiset.card μ₂)) :
    (KLRAlgebra.seqCast h s).1 a = s.1 (Fin.cast (congrArg Multiset.card h).symm a) := by
  subst h; rfl

omit [DecidableEq I] in
theorem seqCast_append_apply_lt {μ₁ μ₂ μ : Multiset I} (hμ : μ₁ + μ₂ = μ) (i : Seq μ₁)
    (j : Seq μ₂) (t : Fin (Multiset.card μ)) (ht : t.val < Multiset.card μ₁) :
    (KLRAlgebra.seqCast hμ (i.append j)).1 t = i.1 ⟨t.val, ht⟩ := by
  rw [seqCast_apply, Seq.append_apply_lt _ _ _ (by simpa using ht)]
  rfl

omit [DecidableEq I] in
theorem seqCast_append_apply_ge {μ₁ μ₂ μ : Multiset I} (hμ : μ₁ + μ₂ = μ) (i : Seq μ₁)
    (j : Seq μ₂) (t : Fin (Multiset.card μ)) (ht : Multiset.card μ₁ ≤ t.val) :
    (KLRAlgebra.seqCast hμ (i.append j)).1 t = j.1 ⟨t.val - Multiset.card μ₁, by
      have := t.2
      have hc : Multiset.card μ = Multiset.card μ₁ + Multiset.card μ₂ := by
        rw [← hμ, Multiset.card_add]
      omega⟩ := by
  rw [seqCast_apply, Seq.append_apply_ge _ _ _ (by simpa using ht)]
  rfl

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

theorem castAlg_pol_eq {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂)
    (p : MvPolynomial (Fin (Multiset.card μ₁)) k) :
    castAlg Q h (pol p) = pol (rename (Fin.cast (congrArg Multiset.card h)) p) := by
  subst h
  have : (Fin.cast (congrArg Multiset.card (rfl : μ₁ = μ₁))) = id := funext fun _ => rfl
  rw [this, rename_id_apply]; rfl

theorem castAlg_rfl {μ : Multiset I} (a : KLRAlgebra k Q μ) : castAlg Q rfl a = a := rfl

/-! ### Multiplicative tensor maps -/

theorem tensorMap_mul {A B C D : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C]
    [Algebra k C] [Ring D] [Algebra k D] (f : A →ₗ[k] C) (g : B →ₗ[k] D)
    (hf : ∀ a a', f (a * a') = f a * f a') (hg : ∀ b b', g (b * b') = g b * g b')
    (x y : A ⊗[k] B) : TensorProduct.map f g (x * y) =
      TensorProduct.map f g x * TensorProduct.map f g y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, hf, hg]
    | add y y' h1 h2 => rw [mul_add, map_add, h1, h2, map_add, mul_add]
  | add x x' h1 h2 => rw [add_mul, map_add, h1, h2, map_add, add_mul]

/-! ### The data `λ` -/

/-- **The data `λ` of KL I, Proposition 2.18**, as four weights `α = ν - λ`, `β = λ`,
`γ = ν' + λ - ν''' = ν'' + λ - ν` and `δ = ν''' - λ`, all in `ℕ[I]`. -/
structure MackeyQuad (ν ν' ν'' ν''' : Multiset I) where
  /-- `ν - λ`: strands from the first bottom block to the first top block. -/
  α : Multiset I
  /-- `λ`: strands from the second bottom block to the first top block. -/
  β : Multiset I
  /-- `ν' + λ - ν'''`: strands from the first bottom block to the second top block. -/
  γ : Multiset I
  /-- `ν''' - λ`: strands from the second bottom block to the second top block. -/
  δ : Multiset I
  h₁ : α + β = ν
  h₂ : γ + δ = ν'
  h₃ : α + γ = ν''
  h₄ : β + δ = ν'''

namespace MackeyQuad

variable {ν ν' ν'' ν''' : Multiset I}

omit [DecidableEq I] in
/-- A quadruple is determined by `λ = β`. -/
theorem ext_of_β {q q' : MackeyQuad ν ν' ν'' ν'''} (h : q.β = q'.β) : q = q' := by
  obtain ⟨α, β, γ, δ, h₁, h₂, h₃, h₄⟩ := q
  obtain ⟨α', β', γ', δ', h₁', h₂', h₃', h₄'⟩ := q'
  simp only at h
  subst h
  have hα : α = α' := add_right_cancel (h₁.trans h₁'.symm)
  subst hα
  have hγ : γ = γ' := add_left_cancel (h₃.trans h₃'.symm)
  subst hγ
  have hδ : δ = δ' := add_left_cancel (h₄.trans h₄'.symm)
  subst hδ
  rfl

/-- **The admissible `λ`** of KL I, Proposition 2.18: `λ` gives a quadruple iff
`ν - λ`, `ν' + λ - ν'''`, `ν''' - λ` are in `ℕ[I]` (and then so is `ν'' + λ - ν`), i.e.
`λ ≤ ν`, `λ ≤ ν'''`, `ν - λ ≤ ν''`. -/
theorem exists_iff (h : ν'' + ν''' = ν + ν') (lam : Multiset I) :
    (∃ q : MackeyQuad ν ν' ν'' ν''', q.β = lam) ↔ lam ≤ ν ∧ lam ≤ ν''' ∧ ν - lam ≤ ν'' := by
  constructor
  · rintro ⟨⟨α, β, γ, δ, h₁, h₂, h₃, h₄⟩, rfl⟩
    subst h₁ h₃ h₄
    refine ⟨Multiset.le_add_left _ _, Multiset.le_add_right _ _, ?_⟩
    rw [add_tsub_cancel_right]; exact Multiset.le_add_right _ _
  · rintro ⟨h1, h2, h3⟩
    have hA : ν - lam + lam = ν := tsub_add_cancel_of_le h1
    have hG : ν - lam + (ν'' - (ν - lam)) = ν'' := add_tsub_cancel_of_le h3
    have hD : lam + (ν''' - lam) = ν''' := add_tsub_cancel_of_le h2
    refine ⟨⟨ν - lam, lam, ν'' - (ν - lam), ν''' - lam, hA, ?_, hG, hD⟩, rfl⟩
    have : (ν'' - (ν - lam) + (ν''' - lam)) + (ν - lam + lam) = ν' + (ν - lam + lam) := by
      calc (ν'' - (ν - lam) + (ν''' - lam)) + (ν - lam + lam)
          = (ν - lam + (ν'' - (ν - lam))) + (lam + (ν''' - lam)) := by
            rw [add_add_add_comm, add_comm (ν'' - (ν - lam)), add_comm (ν''' - lam),
              add_add_add_comm]
        _ = ν + ν' := by rw [hG, hD, h]
        _ = ν' + (ν - lam + lam) := by rw [hA, add_comm]
    exact add_right_cancel this

end MackeyQuad

variable {ν ν' ν'' ν''' : Multiset I}

section QuadMaps

variable (Q) in
/-- The algebra `R' = (R(α) ⊗ R(β)) ⊗ (R(γ) ⊗ R(δ))` of KL I, Proposition 2.18. -/
abbrev QuadAlg (q : MackeyQuad ν ν' ν'' ν''') : Type _ :=
  TensorKLR Q q.α q.β ⊗[k] TensorKLR Q q.γ q.δ

variable (q : MackeyQuad ν ν' ν'' ν''')

set_option synthInstance.maxHeartbeats 200000 in
instance instRingQuadAlg : Ring (QuadAlg Q q) := Algebra.TensorProduct.instRing

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraQuadAlg : Algebra k (QuadAlg Q q) := Algebra.TensorProduct.instAlgebra

/-- The embedding `ι_{α,β} ⊗ ι_{γ,δ} : R' → R(ν) ⊗ R(ν')` (non-unital, multiplicative). -/
noncomputable def quadTop : QuadAlg Q q →ₗ[k] TensorKLR Q ν ν' :=
  TensorProduct.map ((castAlg Q q.h₁).toLinearMap ∘ₗ concat Q q.α q.β)
    ((castAlg Q q.h₂).toLinearMap ∘ₗ concat Q q.γ q.δ)

/-- The embedding `R' → R(ν'') ⊗ R(ν''')`: exchange the two middle factors and apply
`ι_{α,γ} ⊗ ι_{β,δ}`. -/
noncomputable def quadBot : QuadAlg Q q →ₗ[k] TensorKLR Q ν'' ν''' :=
  TensorProduct.map ((castAlg Q q.h₃).toLinearMap ∘ₗ concat Q q.α q.γ)
      ((castAlg Q q.h₄).toLinearMap ∘ₗ concat Q q.β q.δ) ∘ₗ
    (Algebra.TensorProduct.tensorTensorTensorComm k k (KLRAlgebra k Q q.α) (KLRAlgebra k Q q.β)
      (KLRAlgebra k Q q.γ) (KLRAlgebra k Q q.δ)).toLinearMap

theorem quadTop_tmul (a : KLRAlgebra k Q q.α) (b : KLRAlgebra k Q q.β)
    (c : KLRAlgebra k Q q.γ) (d : KLRAlgebra k Q q.δ) :
    quadTop q ((a ⊗ₜ b) ⊗ₜ (c ⊗ₜ d)) =
      castAlg Q q.h₁ (concat Q q.α q.β (a ⊗ₜ b)) ⊗ₜ castAlg Q q.h₂ (concat Q q.γ q.δ (c ⊗ₜ d)) :=
  rfl

theorem quadBot_tmul (a : KLRAlgebra k Q q.α) (b : KLRAlgebra k Q q.β)
    (c : KLRAlgebra k Q q.γ) (d : KLRAlgebra k Q q.δ) :
    quadBot q ((a ⊗ₜ b) ⊗ₜ (c ⊗ₜ d)) =
      castAlg Q q.h₃ (concat Q q.α q.γ (a ⊗ₜ c)) ⊗ₜ castAlg Q q.h₄ (concat Q q.β q.δ (b ⊗ₜ d)) :=
  rfl

theorem quadTop_mul (r s : QuadAlg Q q) : quadTop q (r * s) = quadTop q r * quadTop q s :=
  tensorMap_mul _ _ (fun a a' => by simp [concat_mul]) (fun a a' => by simp [concat_mul]) r s

theorem quadBot_mul (r s : QuadAlg Q q) : quadBot q (r * s) = quadBot q r * quadBot q s := by
  simp only [quadBot, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul]
  exact tensorMap_mul _ _ (fun a a' => by simp [concat_mul]) (fun a a' => by simp [concat_mul]) _ _

theorem quadTop_mul_one (r : QuadAlg Q q) : quadTop q r * quadTop q 1 = quadTop q r := by
  rw [← quadTop_mul, mul_one]

theorem quadTop_one_mul (r : QuadAlg Q q) : quadTop q 1 * quadTop q r = quadTop q r := by
  rw [← quadTop_mul, one_mul]

theorem quadBot_mul_one (r : QuadAlg Q q) : quadBot q r * quadBot q 1 = quadBot q r := by
  rw [← quadBot_mul, mul_one]

theorem quadBot_one_mul (r : QuadAlg Q q) : quadBot q 1 * quadBot q r = quadBot q r := by
  rw [← quadBot_mul, one_mul]

end QuadMaps

/-! ### The bimodules `MackeyTop` and `MackeyBot` -/

section Bimodules

variable (Q) (q : MackeyQuad ν ν' ν'' ν''')

/-- The `(R(ν) ⊗ R(ν'), R')`-bimodule `(R(ν) ⊗ R(ν')) (1_{α,β} ⊗ 1_{γ,δ})`, i.e.
`_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}` in KL I, Proposition 2.18. -/
abbrev MackeyTop : Type _ := Graded.leftIdeal (quadTop (Q := Q) q 1)

variable {Q q}

theorem mul_quadTop_mem (t : MackeyTop Q q) (r : QuadAlg Q q) :
    (t : TensorKLR Q ν ν') * quadTop q r ∈ Graded.leftIdeal (quadTop (Q := Q) q 1) := by
  rw [Graded.mem_leftIdeal, mul_assoc, quadTop_mul_one]

instance : SMul (QuadAlg Q q)ᵐᵒᵖ (MackeyTop Q q) :=
  ⟨fun r t => ⟨t * quadTop q r.unop, mul_quadTop_mem t _⟩⟩

theorem coe_op_smul_top (r : (QuadAlg Q q)ᵐᵒᵖ) (t : MackeyTop Q q) :
    ((r • t : MackeyTop Q q) : TensorKLR Q ν ν') = t * quadTop q r.unop := rfl

instance : Module (QuadAlg Q q)ᵐᵒᵖ (MackeyTop Q q) where
  one_smul t := Subtype.ext (by rw [coe_op_smul_top, unop_one]; exact t.2)
  mul_smul r s t := Subtype.ext (by simp only [coe_op_smul_top, unop_mul, quadTop_mul, mul_assoc])
  smul_zero r := Subtype.ext (by simp [coe_op_smul_top])
  smul_add r t t' := Subtype.ext (by simp [coe_op_smul_top, add_mul])
  add_smul r s t := Subtype.ext (by simp [coe_op_smul_top, mul_add])
  zero_smul t := Subtype.ext (by simp [coe_op_smul_top])

instance : IsScalarTower k (QuadAlg Q q)ᵐᵒᵖ (MackeyTop Q q) where
  smul_assoc c r t := Subtype.ext (by
    show (t : TensorKLR Q ν ν') * quadTop q (unop (c • r)) =
      c • ((t : TensorKLR Q ν ν') * quadTop q r.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (TensorKLR Q ν ν') (QuadAlg Q q)ᵐᵒᵖ (MackeyTop Q q) where
  smul_comm a r t := Subtype.ext (by
    rw [coe_op_smul_top, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul_top, smul_eq_mul,
      smul_eq_mul, mul_assoc])

variable (Q q) in
/-- The `k`-submodule `(1_{α,γ} ⊗ 1_{β,δ}) (R(ν'') ⊗ R(ν'''))` of `R(ν'') ⊗ R(ν''')`. -/
def quadBotSub : Submodule k (TensorKLR Q ν'' ν''') where
  carrier := {x | quadBot q 1 * x = x}
  add_mem' {a b} ha hb := by simp_all [mul_add]
  zero_mem' := mul_zero _
  smul_mem' c a ha := by simp_all [mul_smul_comm]

variable (Q q) in
/-- The `(R', R(ν'') ⊗ R(ν'''))`-bimodule `(1_{α,γ} ⊗ 1_{β,δ}) (R(ν'') ⊗ R(ν'''))`, i.e.
`_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''}` in KL I, Proposition 2.18. -/
abbrev MackeyBot : Type _ := quadBotSub Q q

theorem mem_quadBotSub {x : TensorKLR Q ν'' ν'''} : x ∈ quadBotSub Q q ↔ quadBot q 1 * x = x :=
  Iff.rfl

theorem quadBot_mul_mem (r : QuadAlg Q q) (x : MackeyBot Q q) :
    quadBot q r * (x : TensorKLR Q ν'' ν''') ∈ quadBotSub Q q := by
  rw [mem_quadBotSub, ← mul_assoc, quadBot_one_mul]

instance : SMul (QuadAlg Q q) (MackeyBot Q q) :=
  ⟨fun r x => ⟨quadBot q r * x, quadBot_mul_mem r x⟩⟩

theorem coe_smul_bot (r : QuadAlg Q q) (x : MackeyBot Q q) :
    ((r • x : MackeyBot Q q) : TensorKLR Q ν'' ν''') = quadBot q r * x := rfl

instance : Module (QuadAlg Q q) (MackeyBot Q q) where
  one_smul x := Subtype.ext (by rw [coe_smul_bot]; exact x.2)
  mul_smul r s x := Subtype.ext (by simp only [coe_smul_bot, quadBot_mul, mul_assoc])
  smul_zero r := Subtype.ext (by simp [coe_smul_bot])
  smul_add r x x' := Subtype.ext (by simp [coe_smul_bot, mul_add])
  add_smul r s x := Subtype.ext (by simp [coe_smul_bot, add_mul])
  zero_smul x := Subtype.ext (by simp [coe_smul_bot])

instance : IsScalarTower k (QuadAlg Q q) (MackeyBot Q q) where
  smul_assoc c r x := Subtype.ext (by
    show quadBot q (c • r) * (x : TensorKLR Q ν'' ν''') =
      c • (quadBot q r * (x : TensorKLR Q ν'' ν'''))
    rw [map_smul, smul_mul_assoc])

/-- The right action of `R(ν'') ⊗ R(ν''')` on `MackeyBot`, an `R'`-linear map. -/
def botRMul (c : TensorKLR Q ν'' ν''') : MackeyBot Q q →ₗ[QuadAlg Q q] MackeyBot Q q where
  toFun x := ⟨x * c, by rw [mem_quadBotSub, ← mul_assoc, x.2]⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (by
    simp only [RingHom.id_apply, coe_smul_bot]
    exact mul_assoc _ _ _)

@[simp] theorem coe_botRMul (c : TensorKLR Q ν'' ν''') (x : MackeyBot Q q) :
    ((botRMul c x : MackeyBot Q q) : TensorKLR Q ν'' ν''') = x * c := rfl

variable (Q q) in
/-- **The balanced tensor product of KL I, Proposition 2.18**:
`(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'} (_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''})`,
a left `R(ν) ⊗ R(ν')`-module; the right `R(ν'') ⊗ R(ν''')`-action is `MackeyX.rightAct`. -/
abbrev MackeyX : Type _ :=
  BalancedTensor k (TensorKLR Q ν ν') (QuadAlg Q q) (MackeyTop Q q) (MackeyBot Q q)

/-- The right action of `R(ν'') ⊗ R(ν''')` on `MackeyX`. -/
noncomputable def MackeyX.rightAct (c : TensorKLR Q ν'' ν''') :
    MackeyX Q q →ₗ[TensorKLR Q ν ν'] MackeyX Q q :=
  BalancedTensor.mapRight (botRMul c)

@[simp] theorem MackeyX.rightAct_tmul (c : TensorKLR Q ν'' ν''') (t : MackeyTop Q q)
    (x : MackeyBot Q q) :
    MackeyX.rightAct c (BalancedTensor.tmul t x : MackeyX Q q) =
      BalancedTensor.tmul t (botRMul c x) := rfl

end Bimodules

end KLRAlgebra

end Categorification.KLR

end
