/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicK0

/-!
# Kang–Kashiwara Theorem 4.5: `R^Λ(β + α_i) e(β, i)` is a projective right `R^Λ(β)`-module

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, **Theorem 4.5** (`th:proj`): for
`β ∈ Q⁺` and `i ∈ I`, `R^Λ(β + α_i) e(β, i)` is a projective right `R^Λ(β)`-module.

Here, with `ν = {i} + β`:

* `actF b`: right multiplication by `cL b` on `F^Λ = R^Λ(ν)`; `FE = F^Λ e(β, i)` is its image for
  `b = 1`, a right `R^Λ(β)`-module (`Module (CycKLR k Q a β)ᵐᵒᵖ (FE Q i β a)`, through
  `rhoFE : R(β) → End(FE)ᵐᵒᵖ`, which kills the cyclotomic ideal: `cL_mem_cycIdeal`).
* `projective_FE` (**KK Theorem 4.5**): `FE` is a projective right `R^Λ(β)`-module. Proof: by
  the split exact sequence `0 → K_1 e(i, β) → K_0 → F^Λ → 0` of right `R(β)`-modules
  (`splitMap_pMap`, `splitMap_act`, `range_pMap`), `FE` is a direct summand of
  `K_0 e(β, i) ≅ ⊕_{shuffles} R^Λ(β)[t]` (`coordL`, `embL`), and `R^Λ(β)[t]` is a free right
  `R^Λ(β)`-module (`polyOpEquiv`).

Domain `k`, factorized `Q` with unit leading coefficients, monic `a_i`, `β ≠ 0`. (KK work over a
graded commutative ring with the Cartan-datum form of `Q`; the argument used here is KK's.)
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep MulOpposite
open scoped TensorProduct

/-! ### `S[t]` is a free right `S`-module -/

section PolyOp

variable (S : Type*) [Ring S]

/-- `S[t] ≅ ⊕_{n ∈ ℕ} S` as right `S`-modules. -/
noncomputable def polyOpEquiv : Polynomial S ≃ₗ[Sᵐᵒᵖ] (ℕ →₀ Sᵐᵒᵖ) where
  toFun p := Finsupp.onFinset p.support (fun n => op (p.coeff n)) (fun n h => by
    rw [Polynomial.mem_support_iff]; intro h'; exact h (by rw [h', op_zero]))
  invFun g := g.sum fun n c => Polynomial.monomial n (unop c)
  map_add' p q := by ext n; simp [Finsupp.onFinset_apply]
  map_smul' c p := by
    ext n
    simp [Finsupp.onFinset_apply, Polynomial.coeff_smul, MulOpposite.smul_eq_mul_unop]
  left_inv p := by
    show (Finsupp.onFinset _ _ _).sum _ = p
    rw [Finsupp.onFinset_sum _ (fun _ => by simp)]
    simp only [unop_op]
    exact (Polynomial.as_sum_support p).symm
  right_inv g := by
    ext n
    simp [Finsupp.onFinset_apply, Finsupp.sum, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial]
    split_ifs with h
    · rw [op_unop]
    · simp only [Finsupp.mem_support_iff, not_not] at h; rw [h, op_zero]

theorem op_smul_poly (x : S) (p : Polynomial S) : op x • p = p * Polynomial.C x :=
  Polynomial.ext fun n => by
    rw [Polynomial.coeff_smul, Polynomial.coeff_mul_C, MulOpposite.smul_eq_mul_unop, unop_op]

instance projective_poly_op : Module.Projective Sᵐᵒᵖ (Polynomial S) :=
  Module.Projective.of_equiv (polyOpEquiv S).symm

theorem projective_pi_poly_op (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.Projective Sᵐᵒᵖ (ι → Polynomial S) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := Sᵐᵒᵖ)
    (M := fun _ : ι => Polynomial S))

end PolyOp

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

theorem castKLR_mem_cycIdeal (a : I → Polynomial k) {μ μ' : Multiset I} (h : μ = μ')
    (z : KLRAlgebra k Q μ) : castKLR Q h z ∈ cycIdeal Q a μ' ↔ z ∈ cycIdeal Q a μ := by
  subst h; rfl

/-! ### The right `R^Λ(β)`-module `F^Λ e(β, i)` -/

section FE

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)

/-- `cL` carries the cyclotomic ideal of `R(β)` into that of `R({i} + β)`. -/
theorem cL_mem_cycIdeal {j : Rb} (hj : j ∈ cycIdeal Q a β) : cL Q i β j ∈ cycIdeal Q a (Si + β) := by
  induction hj using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    by_cases hβ : 0 < Multiset.card β
    · have h0 : 0 < Multiset.card (β + Si) := by
        rw [add_comm]; exact zero_lt_card_single_add i β
      rw [cycElt_eq a hβ, cL_mul, cL_eq_cast, ← cycAt_zero_mul_oneConcat i β a h0 hβ]
      exact TwoSidedIdeal.mul_mem_right _ _ _ ((castKLR_mem_cycIdeal a _ _).2
        (TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a h0)))
    · rw [show cycElt Q a s = 0 by simp [cycElt, hβ], cL_zero]
      exact TwoSidedIdeal.zero_mem _
  | zero => rw [cL_zero]; exact TwoSidedIdeal.zero_mem _
  | add y z _ _ hy hz => rw [cL_add]; exact TwoSidedIdeal.add_mem _ hy hz
  | neg y _ hy =>
    rw [neg_eq_neg_one_mul, show (-1 : Rb) * y = (-1 : k) • y by simp, cL_smul, neg_one_smul]
    exact TwoSidedIdeal.neg_mem _ hy
  | left_absorb c y _ hy => rw [cL_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hy
  | right_absorb c y _ hy => rw [cL_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hy

variable (Q) in
/-- Right multiplication by `cL b` on `F^Λ = R^Λ({i} + β)`. -/
noncomputable def actF (b : Rb) : FLam Q (Si + β) a →ₗ[R] FLam Q (Si + β) a :=
  ((cycIdeal Q a (Si + β)).asIdeal).mapQ _ (LinearMap.toSpanSingleton R R (cL Q i β b))
    (fun z hz => by
      show z * cL Q i β b ∈ (cycIdeal Q a (Si + β)).asIdeal
      rw [TwoSidedIdeal.mem_asIdeal] at hz ⊢
      exact TwoSidedIdeal.mul_mem_right _ _ _ hz)

theorem actF_mk (b : Rb) (y : R) :
    actF Q i β a b (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y * cL Q i β b) := rfl

theorem actF_actF (u v : Rb) (f : FLam Q (Si + β) a) :
    actF Q i β a u (actF Q i β a v f) = actF Q i β a (v * u) f := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ f
  rw [actF_mk, actF_mk, actF_mk, mul_assoc, cL_mul]

theorem actF_add (u v : Rb) (f : FLam Q (Si + β) a) :
    actF Q i β a (u + v) f = actF Q i β a u f + actF Q i β a v f := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ f
  rw [actF_mk, actF_mk, actF_mk, cL_add, mul_add, Submodule.Quotient.mk_add]

theorem actF_smul (r : k) (u : Rb) (f : FLam Q (Si + β) a) :
    actF Q i β a (r • u) f = r • actF Q i β a u f := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ f
  rw [actF_mk, actF_mk, cL_smul, mul_smul_comm]
  rfl

theorem actF_zero (f : FLam Q (Si + β) a) : actF Q i β a 0 f = 0 := by
  rw [← zero_smul k (0 : Rb), actF_smul, zero_smul]

theorem actF_eq_zero {j : Rb} (hj : j ∈ cycIdeal Q a β) (f : FLam Q (Si + β) a) :
    actF Q i β a j f = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ f
  rw [actF_mk, Submodule.Quotient.mk_eq_zero, TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.mul_mem_left _ _ _ (cL_mem_cycIdeal i β a hj)

theorem piMap_act0 (b : Rb) (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    piMap a (zero_lt_card_single_add i β) (act0 Q i β a b z) =
      actF Q i β a b (piMap a (zero_lt_card_single_add i β) z) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

theorem act0_act0 (u v : Rb) (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    act0 Q i β a u (act0 Q i β a v z) = act0 Q i β a (v * u) z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act0_mk, act0_mk, act0_mk, mul_assoc, cL_mul]

variable (Q) in
/-- `F^Λ e(β, i)`, the image of right multiplication by `e(β, i) = cL 1`. -/
noncomputable def FEsub : Submodule k (FLam Q (Si + β) a) :=
  LinearMap.range ((actF Q i β a 1).restrictScalars k)

variable (Q) in
/-- **KK's `F^Λ e(β, i) = R^Λ(β + α_i) e(β, i)`**. -/
abbrev FE : Type _ := ↥(FEsub Q i β a)

theorem actF_one_of_mem {f : FLam Q (Si + β) a} (hf : f ∈ FEsub Q i β a) :
    actF Q i β a 1 f = f := by
  obtain ⟨g, rfl⟩ := hf
  show actF Q i β a 1 (actF Q i β a 1 g) = actF Q i β a 1 g
  rw [actF_actF, mul_one]

theorem actF_mem (b : Rb) (f : FLam Q (Si + β) a) : actF Q i β a b f ∈ FEsub Q i β a :=
  ⟨actF Q i β a b f, by
    show actF Q i β a 1 (actF Q i β a b f) = _
    rw [actF_actF, mul_one]⟩

variable (Q) in
/-- The right action of `b ∈ R(β)` on `F^Λ e(β, i)`. -/
noncomputable def actE (b : Rb) : FE Q i β a →ₗ[k] FE Q i β a :=
  ((actF Q i β a b).restrictScalars k).restrict (fun f _ => actF_mem i β a b f)

theorem actE_apply (b : Rb) (f : FE Q i β a) :
    (actE Q i β a b f : FLam Q (Si + β) a) = actF Q i β a b f := rfl

variable (Q) in
/-- `R(β) → End(F^Λ e(β, i))ᵐᵒᵖ`. -/
noncomputable def rhoFE : Rb →ₐ[k] (Module.End k (FE Q i β a))ᵐᵒᵖ where
  toFun b := op (actE Q i β a b)
  map_one' := by
    rw [← op_one]; congr 1
    ext f; exact actF_one_of_mem i β a f.2
  map_mul' u v := by
    rw [← op_mul]; congr 1
    ext f
    rw [actE_apply, Module.End.mul_apply, actE_apply, actE_apply, actF_actF]
  map_zero' := by
    rw [← op_zero]; congr 1
    ext f; show actF Q i β a 0 f = 0; exact actF_zero (Q := Q) i β a f
  map_add' u v := by
    rw [← op_add]; congr 1
    ext f; show actF Q i β a (u + v) f = actF Q i β a u f + actF Q i β a v f
    exact actF_add (Q := Q) i β a u v f
  commutes' r := by
    rw [MulOpposite.algebraMap_apply]; congr 1
    ext f
    rw [actE_apply, Algebra.algebraMap_eq_smul_one, actF_smul, actF_one_of_mem i β a f.2,
      Module.algebraMap_end_apply]
    rfl

variable (Q) in
/-- `R^Λ(β) → End(F^Λ e(β, i))ᵐᵒᵖ`. -/
noncomputable def rhoFEbar : CycKLR k Q a β →ₐ[k] (Module.End k (FE Q i β a))ᵐᵒᵖ :=
  CycKLR.lift (rhoFE Q i β a) (fun s => by
    show op (actE Q i β a (cycElt Q a s)) = 0
    rw [← op_zero]; congr 1
    ext f; exact actF_eq_zero i β a (cycElt_mem_cycIdeal Q a s) f)

/-- **The right `R^Λ(β)`-module structure** of `F^Λ e(β, i)`. -/
noncomputable instance instModuleFE : Module (CycKLR k Q a β)ᵐᵒᵖ (FE Q i β a) :=
  Module.compHom _ ((RingEquiv.opOp (Module.End k (FE Q i β a))).symm.toRingHom.comp
    (RingHom.op (rhoFEbar Q i β a).toRingHom))

theorem op_mk_smul_FE (b : Rb) (f : FE Q i β a) :
    (op (CycKLR.mk k Q a β b) • f : FE Q i β a) = actE Q i β a b f := by
  show (unop (rhoFEbar Q i β a (CycKLR.mk k Q a β b))) f = _
  rw [rhoFEbar, CycKLR.lift_mk]
  rfl

end FE

/-! ### The section of `π : K_0 → F^Λ` and Theorem 4.5 -/

section Proj

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (i : I) (β : Multiset I) (a : I → Polynomial k)
  (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
  (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
  (hβ : 0 < Multiset.card β)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "K0" => KZero Q (Si + β) a (zero_lt_card_single_add i β)

omit [DecidableEq I] in
include hβ in
theorem one_lt_card_single_add : 1 < Multiset.card (Si + β) := by
  rw [card_single_add]; omega

variable (Q) in
/-- `z ↦ z e − P(r(z e))` on `K_0`, `r` the splitting of `P`. -/
noncomputable def tauK : K0 →ₗ[k] K0 :=
  (act0 Q i β a 1).restrictScalars k -
    (pMap a (zero_lt_card_single_add i β) (one_lt_card_single_add i β hβ) (Multiset.card β)
      (card_single_add i β).symm).restrictScalars k ∘ₗ
      splitMap Q hPQ hP i β a hsym hQ ha (one_lt_card_single_add i β hβ) hβ ∘ₗ
        (act0 Q i β a 1).restrictScalars k

theorem tauK_apply (z : K0) :
    tauK Q hPQ hP i β a hsym hQ ha hβ z = act0 Q i β a 1 z -
      pMap a (zero_lt_card_single_add i β) (one_lt_card_single_add i β hβ) (Multiset.card β)
        (card_single_add i β).symm
        (splitMap Q hPQ hP i β a hsym hQ ha (one_lt_card_single_add i β hβ) hβ
          (act0 Q i β a 1 z)) := rfl

theorem tauK_eq_zero {z : K0} (hz : piMap a (zero_lt_card_single_add i β) z = 0) :
    tauK Q hPQ hP i β a hsym hQ ha hβ z = 0 := by
  have h1 := one_lt_card_single_add i β hβ
  rw [← LinearMap.mem_ker, ← range_pMap a _ h1 (Multiset.card β) (card_single_add i β).symm]
    at hz
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [tauK_apply, ← pMap_act, act1_mk, cR_one, splitMap_pMap, sub_self]

theorem tauK_act0 (b : Rb) (z : K0) :
    tauK Q hPQ hP i β a hsym hQ ha hβ (act0 Q i β a b z) =
      act0 Q i β a b (tauK Q hPQ hP i β a hsym hQ ha hβ z) := by
  rw [tauK_apply, tauK_apply, map_sub, act0_act0, act0_act0, mul_one, one_mul, ← pMap_act,
    ← splitMap_act, act0_act0, one_mul]

variable (Q) in
/-- **The section of `π : K_0 → F^Λ`** (from the splitting of `P`). -/
noncomputable def secF : FLam Q (Si + β) a →ₗ[k] K0 :=
  (LinearMap.ker ((piMap a (zero_lt_card_single_add i β)).restrictScalars k)).liftQ
      (tauK Q hPQ hP i β a hsym hQ ha hβ) (fun _ hz => LinearMap.mem_ker.2
        (tauK_eq_zero hPQ hP i β a hsym hQ ha hβ (LinearMap.mem_ker.1 hz))) ∘ₗ
    (((piMap a (zero_lt_card_single_add i β)).restrictScalars k).quotKerEquivOfSurjective
      (piMap_surjective a _)).symm.toLinearMap

theorem secF_piMap (z : K0) :
    secF Q hPQ hP i β a hsym hQ ha hβ (piMap a (zero_lt_card_single_add i β) z) =
      tauK Q hPQ hP i β a hsym hQ ha hβ z := by
  have h : (((piMap a (zero_lt_card_single_add i β)).restrictScalars k).quotKerEquivOfSurjective
      (piMap_surjective a _)).symm (piMap a (zero_lt_card_single_add i β) z) =
        Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [secF, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]

theorem piMap_secF (f : FLam Q (Si + β) a) :
    piMap a (zero_lt_card_single_add i β) (secF Q hPQ hP i β a hsym hQ ha hβ f) =
      actF Q i β a 1 f := by
  obtain ⟨z, rfl⟩ := piMap_surjective (Q := Q) a (zero_lt_card_single_add i β) f
  have h1 := one_lt_card_single_add i β hβ
  rw [secF_piMap, tauK_apply, map_sub, piMap_act0]
  have : piMap a (zero_lt_card_single_add i β) (pMap a (zero_lt_card_single_add i β) h1
      (Multiset.card β) (card_single_add i β).symm (splitMap Q hPQ hP i β a hsym hQ ha h1 hβ
        (act0 Q i β a 1 z))) = 0 := by
    rw [← LinearMap.mem_ker, ← range_pMap a _ h1 (Multiset.card β) (card_single_add i β).symm]
    exact LinearMap.mem_range_self _ _
  rw [this, sub_zero]

theorem secF_actF (b : Rb) (f : FLam Q (Si + β) a) :
    secF Q hPQ hP i β a hsym hQ ha hβ (actF Q i β a b f) =
      act0 Q i β a b (secF Q hPQ hP i β a hsym hQ ha hβ f) := by
  obtain ⟨z, rfl⟩ := piMap_surjective (Q := Q) a (zero_lt_card_single_add i β) f
  rw [← piMap_act0, secF_piMap, secF_piMap, tauK_act0]

local notation "Sh0" => Shuffle (Seq.card_add' β Si)
local notation "Rl" => CycKLR k Q a β

variable (Q) in
/-- `F^Λ e(β, i) → K_0 e(β, i) ≅ ⊕_u R^Λ(β)[t]`. -/
noncomputable def inclFE : FE Q i β a →ₗ[Rlᵐᵒᵖ] (Sh0 → Polynomial Rl) where
  toFun f := coordL Q hPQ hP i β a hβ (secF Q hPQ hP i β a hsym hQ ha hβ f)
  map_add' f g := by simp only [Submodule.coe_add, map_add]
  map_smul' c f := by
    obtain ⟨x, rfl⟩ : ∃ x, op x = c := ⟨unop c, op_unop c⟩
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective (k := k) (Q := Q) (a := a) (ν := β) x
    rw [op_mk_smul_FE, actE_apply, secF_actF, coordL_act0, RingHom.id_apply]
    funext u
    rw [Pi.smul_apply, op_smul_poly]

variable (Q) in
/-- `⊕_u R^Λ(β)[t] ≅ K_0 e(β, i) → F^Λ e(β, i)`. -/
noncomputable def projFE : (Sh0 → Polynomial Rl) →ₗ[Rlᵐᵒᵖ] FE Q i β a where
  toFun c := ⟨actF Q i β a 1 (piMap a (zero_lt_card_single_add i β) (embL Q hPQ hP i β a hβ c)),
    actF_mem i β a 1 _⟩
  map_add' c d := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
  map_smul' c d := by
    obtain ⟨x, rfl⟩ : ∃ x, op x = c := ⟨unop c, op_unop c⟩
    obtain ⟨b, rfl⟩ := CycKLR.mk_surjective (k := k) (Q := Q) (a := a) (ν := β) x
    apply Subtype.ext
    rw [RingHom.id_apply, op_mk_smul_FE, actE_apply]
    have : (op (CycKLR.mk k Q a β b) • d : Sh0 → Polynomial Rl) =
        fun u => d u * Polynomial.C (CycKLR.mk k Q a β b) := by
      funext u; rw [Pi.smul_apply, op_smul_poly]
    simp only
    rw [this, embL_mul_C, piMap_act0, actF_actF, actF_actF, one_mul, mul_one]

theorem projFE_inclFE (f : FE Q i β a) :
    projFE Q hPQ hP i β a hβ (inclFE Q hPQ hP i β a hsym hQ ha hβ f) = f := by
  apply Subtype.ext
  show actF Q i β a 1 (piMap a _ (embL Q hPQ hP i β a hβ
    (coordL Q hPQ hP i β a hβ (secF Q hPQ hP i β a hsym hQ ha hβ f)))) = f
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (secF Q hPQ hP i β a hsym hQ ha hβ f)
  rw [← hy, embL_coordL, ← act0_mk, piMap_act0, hy, piMap_secF, actF_actF, actF_actF,
    mul_one, mul_one, actF_one_of_mem i β a f.2]

include hPQ hP hsym hQ ha hβ in
/-- **Kang–Kashiwara, Theorem 4.5**: `R^Λ(β + α_i) e(β, i)` is a projective right
`R^Λ(β)`-module. -/
theorem projective_FE : Module.Projective (CycKLR k Q a β)ᵐᵒᵖ (FE Q i β a) := by
  have := projective_pi_poly_op (CycKLR k Q a β) Sh0
  exact Module.Projective.of_split (inclFE Q hPQ hP i β a hsym hQ ha hβ) (projFE Q hPQ hP i β a hβ)
    (LinearMap.ext fun f => projFE_inclFE hPQ hP i β a hsym hQ ha hβ f)

end Proj

end KLRAlgebra

end Categorification.KLR
