/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendDerived
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.VacuumBraidColumnDimension

set_option backward.isDefEq.respectTransparency false

/-!
# The braiding bimodules fix the red-first projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Corollary 6.8: `𝔅_i P⁰ ≅ P⁰`, read ungraded. Let `b = (i_n, …, i_1)` be a list of black labels
and, for a red order `κ`, let `e⁰_{κ,b}` (`redFirstViol`) be the idempotent of the red strands in
the order `κ` followed by the black strands `i_1, …, i_n`, in the quotient `V` of braided Stendhal
diagrams by violated idempotents. The red-first projective is `P⁰_{κ,b} = e⁰_{κ,b} V e_κ`, a right
module over the corner `e_κ V e_κ`, and `e⁰_{κ',b} B(κ', κ) = e⁰_{κ',b} V e_κ`. For a nonzero
diagram `r₀ ∈ e_{κ'} V e_κ` with no black strands, let `r_b` (`redBraid`) be `r₀` with the black
strands of `b` added at the right. Then left multiplication by `r_b` is a bijection
`e⁰_{κ,b} V e_κ → e⁰_{κ',b} V e_κ` (`bijective_redBraid_mul`), right linear over the corner. This
holds for all red orders `κ'`, `κ`; Webster states the case of an adjacent transposition.

The proof is Webster's: `P⁰_{κ,b}` is obtained from the case without black strands by the
functors `𝔉_i`, which commute with the braiding bimodules (Proposition 6.7 in its module form,
`violMk_mult_surjective_append_op`, `violMk_mult_injective_append_op`; steps
`RedFirstData.surj_append`, `RedFirstData.inj_append`). Without black strands `e_{κ'} V e_κ` has
dimension at most one (`exists_smul_eq_of_nil`), and it is nonzero when `κ'` and `κ` are red
orders of loadings (`exists_ne_zero_of_nil`).

## Main definitions and results

* `TensorAlong.mapRight`: the map of tensor products along `φ` induced by a map of the right
  factors.
* `BraidedStendhalAlgebra.blackWeight`, `redFirstViol`, `redBraid`: the black weight of a list
  of labels, the red-first idempotents and the braids `r_b`.
* `BraidedStendhalAlgebra.bijective_redBraid_mul`: **Corollary 6.8**.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

/-! ### Maps of tensor products along a homomorphism -/

namespace TensorAlong

variable {k : Type*} [CommRing k] {A C : Type*} [Ring A] [Algebra k A] [Ring C] [Algebra k C]
  {φ : C →ₙₐ[k] A} {e₂ : A} {e₁ e₀ e₀' : C}

/-- The map `x ⊗ y ↦ x ⊗ f y` of tensor products along `φ`, for a map `f` of the right factors
compatible with the corners and with the left action of the corner algebra `e₁ C e₁`. -/
def mapRight (f : C →ₗ[k] C) (hf₁ : ∀ y, e₁ * f y * e₀' = f (e₁ * y * e₀))
    (hf₂ : ∀ c y, f (e₁ * c * e₁ * y) = e₁ * c * e₁ * f y) :
    TensorAlong k A C φ e₂ e₁ e₀ →ₗ[k] TensorAlong k A C φ e₂ e₁ e₀' :=
  (rel k A C φ e₂ e₁ e₀).liftQ (mkQ k A C φ e₂ e₁ e₀' ∘ₗ TensorProduct.map LinearMap.id f) <| by
    rw [rel, Submodule.span_le]
    rintro t (⟨x, y, rfl⟩ | ⟨x, c, y, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.comp_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, sub_eq_zero]
    · rw [← hf₁]
      exact tmul_corner (φ := φ) (e₂ := e₂) (e₁ := e₁) (e₀ := e₀') x (f y)
    · rw [hf₂]
      exact tmul_balance (φ := φ) (e₂ := e₂) (e₁ := e₁) (e₀ := e₀') x c (f y)

@[simp] theorem mapRight_tmul (f : C →ₗ[k] C) (hf₁ : ∀ y, e₁ * f y * e₀' = f (e₁ * y * e₀))
    (hf₂ : ∀ c y, f (e₁ * c * e₁ * y) = e₁ * c * e₁ * f y) (x : A) (y : C) :
    mapRight f hf₁ hf₂ (tmul x y : TensorAlong k A C φ e₂ e₁ e₀) = tmul x (f y) :=
  rfl

end TensorAlong

end

end Categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial Equiv MulOpposite

noncomputable section

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

namespace BraidedStendhalAlgebra

/-! ### One black strand more -/

section Step

variable {Q Λ} (i : I) (ν : Multiset I) {κ' κ : List (Fin ℓ)}

set_option quotPrecheck false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option quotPrecheck false in
local notation "eS" κ:max => violMk k Q Λ ν (redProj k Q Λ ν κ)
set_option quotPrecheck false in
local notation "eR" κ:max => violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ)
set_option quotPrecheck false in
local notation "φ" => appendViol Q Λ i ν

/-- The hypotheses on the idempotents `E = e⁰_{κ,b}`, `E' = e⁰_{κ',b}` and the braid `r = r_b`
for one number of black strands. -/
structure RedFirstData (κ' κ : List (Fin ℓ)) (E E' r : ViolQuotient k Q Λ ν) : Prop where
  left : eS κ * E = E
  right : E * eS κ = E
  left' : eS κ' * E' = E'
  right' : E' * eS κ' = E'
  braid_left : E' * r = r
  braid_right : r * E = r
  idem : E * E = E
  idem' : E' * E' = E'

variable {i ν} {E E' r : ViolQuotient k Q Λ ν}

theorem idemS_mul_self (κ : List (Fin ℓ)) : eS κ * eS κ = eS κ :=
  (isIdempotentElem_violMk_redProj k Q Λ ν κ).eq

theorem idemR_mul_phi (κ : List (Fin ℓ)) : eR κ * φ (eS κ) = φ (eS κ) :=
  ((Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ νᵢ κ)).mp
    (appendViol_mem_corner Q Λ i ν κ ((Subsemigroup.mem_corner_iff
      (isIdempotentElem_violMk_redProj k Q Λ ν κ)).mpr
      ⟨idemS_mul_self κ, idemS_mul_self κ⟩))).1

theorem phi_mul_idemR (κ : List (Fin ℓ)) : φ (eS κ) * eR κ = φ (eS κ) :=
  ((Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ νᵢ κ)).mp
    (appendViol_mem_corner Q Λ i ν κ ((Subsemigroup.mem_corner_iff
      (isIdempotentElem_violMk_redProj k Q Λ ν κ)).mpr
      ⟨idemS_mul_self κ, idemS_mul_self κ⟩))).2

/-- Appending a black strand preserves the hypotheses `RedFirstData`. -/
theorem RedFirstData.append (h : RedFirstData ν κ' κ E E' r) :
    RedFirstData νᵢ κ' κ (φ E) (φ E') (φ r) where
  left := by rw [← h.left, map_mul, ← mul_assoc, idemR_mul_phi]
  right := by rw [← h.right, map_mul, mul_assoc, phi_mul_idemR]
  left' := by rw [← h.left', map_mul, ← mul_assoc, idemR_mul_phi]
  right' := by rw [← h.right', map_mul, mul_assoc, phi_mul_idemR]
  braid_left := by rw [← map_mul, h.braid_left]
  braid_right := by rw [← map_mul, h.braid_right]
  idem := by rw [← map_mul, h.idem]
  idem' := by rw [← map_mul, h.idem']


/-! The tensor products of Proposition 6.7 for `𝔉_i`, over the opposite algebras. -/

theorem isIdempotentElem_op_violMk (ν : Multiset I) (κ : List (Fin ℓ)) :
    IsIdempotentElem (op (violMk k Q Λ ν (redProj k Q Λ ν κ))) := by
  change op _ * op _ = op _
  rw [← op_mul, (isIdempotentElem_violMk_redProj k Q Λ ν κ).eq]

variable (i ν) in
/-- The multiplication `y ⊗ x ↦ φ(y) x` of Proposition 6.7 for `𝔉_i`, over the opposite
algebras. -/
abbrev multF (κ' κ : List (Fin ℓ)) :
    TensorAlong k (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ (ViolQuotient k Q Λ ν)ᵐᵒᵖ (appendViolOp Q Λ i ν)
      (op (eR κ)) (op (eS κ)) (op (eS κ')) →ₗ[k] (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ :=
  TensorAlong.mult (isIdempotentElem_op_violMk (Q := Q) (Λ := Λ) νᵢ κ)
    (isIdempotentElem_op_violMk (Q := Q) (Λ := Λ) ν κ)
    (isIdempotentElem_op_violMk (Q := Q) (Λ := Λ) ν κ')

theorem unop_multF_tmul (x : (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ) (y : (ViolQuotient k Q Λ ν)ᵐᵒᵖ) :
    (multF i ν κ' κ (TensorAlong.tmul x y)).unop =
      φ (eS κ' * y.unop * eS κ) * x.unop * eR κ := by
  rw [TensorAlong.mult_tmul]
  simp only [unop_mul, unop_op, appendViolOp_apply, mul_assoc]

variable (hQ : KLRSymm Q) (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : IsReducedChoice ρ)

theorem RedFirstData.mul_eq_of_corner (h : RedFirstData ν κ' κ E E' r) {c : ViolQuotient k Q Λ ν}
    (hc : E * c * eS κ = c) : E * c = c := by
  rw [← hc, ← mul_assoc, ← mul_assoc, h.idem]

include hQ hρ in
/-- Surjectivity of `c ↦ r c` passes from `b` to `i :: b`. -/
theorem RedFirstData.surj_append (h : RedFirstData ν κ' κ E E' r)
    (hS : ∀ w, E' * w * eS κ = w → ∃ c, E * c * eS κ = c ∧ w = r * c)
    (z : ViolQuotient k Q Λ νᵢ) (hz : φ E' * z * eR κ = z) :
    ∃ c, φ E * c * eR κ = c ∧ z = φ r * c := by
  obtain ⟨t, ht⟩ := violMk_mult_surjective_append_op Q Λ i ν hQ ρ hρ κ' κ (op z)
  have ht' : multF i ν κ' κ t = op (eR κ) * op z * appendViolOp Q Λ i ν (op (eS κ')) := ht
  have key : ∀ t, ∃ c, φ E * c * eR κ = c ∧ φ E' * (multF i ν κ' κ t).unop = φ r * c := by
    intro t
    induction t using TensorAlong.induction_on with
    | tmul x y =>
      obtain ⟨c₀, hc₀, hw⟩ := hS (E' * y.unop * eS κ) (by
        rw [← mul_assoc, ← mul_assoc, h.idem', mul_assoc, mul_assoc, idemS_mul_self,
          ← mul_assoc])
      refine ⟨φ c₀ * x.unop * eR κ, ?_, ?_⟩
      · rw [← mul_assoc, ← mul_assoc, ← map_mul, h.mul_eq_of_corner hc₀, mul_assoc,
          (isIdempotentElem_violMk_redProj k Q Λ νᵢ κ).eq]
      · have e : E' * (eS κ' * y.unop) * eS κ = E' * y.unop * eS κ := by
          rw [← mul_assoc E', h.right']
        rw [unop_multF_tmul, ← mul_assoc, ← mul_assoc, ← map_mul, ← mul_assoc, e, hw,
          map_mul, mul_assoc, mul_assoc, mul_assoc]
    | add s t hs ht =>
      obtain ⟨c₁, hc₁, h₁⟩ := hs
      obtain ⟨c₂, hc₂, h₂⟩ := ht
      exact ⟨c₁ + c₂, by rw [mul_add, add_mul, hc₁, hc₂], by
        rw [map_add, unop_add, mul_add, h₁, h₂, mul_add]⟩
  obtain ⟨c, hc, hct⟩ := key t
  refine ⟨c, hc, ?_⟩
  rw [← hct, ht']
  simp only [unop_mul, unop_op, appendViolOp_apply]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, h.right', hz]

variable (i ν) in
/-- The map of the tensor products of Proposition 6.7 induced by a map `g` of the right factors
(read in `V`, not in its opposite). -/
def mapF {κ'' : List (Fin ℓ)} (g : ViolQuotient k Q Λ ν →ₗ[k] ViolQuotient k Q Λ ν)
    (hg₁ : ∀ v, eS κ'' * g v * eS κ = g (eS κ' * v * eS κ))
    (hg₂ : ∀ v d, g (v * (eS κ * d * eS κ)) = g v * (eS κ * d * eS κ)) :
    TensorAlong k (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ (ViolQuotient k Q Λ ν)ᵐᵒᵖ (appendViolOp Q Λ i ν)
      (op (eR κ)) (op (eS κ)) (op (eS κ')) →ₗ[k]
    TensorAlong k (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ (ViolQuotient k Q Λ ν)ᵐᵒᵖ (appendViolOp Q Λ i ν)
      (op (eR κ)) (op (eS κ)) (op (eS κ'')) :=
  TensorAlong.mapRight
    { toFun := fun y => op (g y.unop)
      map_add' := fun y y' => by simp
      map_smul' := fun c y => by simp }
    (fun y => by
      apply MulOpposite.unop_injective
      have := hg₁ y.unop
      simp only [mul_assoc] at this
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, unop_mul, unop_op, mul_assoc] using this)
    (fun c y => by
      apply MulOpposite.unop_injective
      have := hg₂ y.unop c.unop
      simp only [mul_assoc] at this
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, unop_mul, unop_op, mul_assoc] using this)

theorem mapF_tmul {κ'' : List (Fin ℓ)} (g : ViolQuotient k Q Λ ν →ₗ[k] ViolQuotient k Q Λ ν)
    (hg₁ : ∀ v, eS κ'' * g v * eS κ = g (eS κ' * v * eS κ))
    (hg₂ : ∀ v d, g (v * (eS κ * d * eS κ)) = g v * (eS κ * d * eS κ))
    (x : (ViolQuotient k Q Λ νᵢ)ᵐᵒᵖ) (y : (ViolQuotient k Q Λ ν)ᵐᵒᵖ) :
    mapF i ν g hg₁ hg₂ (TensorAlong.tmul x y) = TensorAlong.tmul x (op (g y.unop)) :=
  rfl

/-- Left multiplication by `a`, as a map of the right factors. -/
theorem mulLeft_hyp₁ {κ'' : List (Fin ℓ)} {a : ViolQuotient k Q Λ ν} (ha₁ : eS κ'' * a = a)
    (ha₂ : a * eS κ' = a) (v : ViolQuotient k Q Λ ν) :
    eS κ'' * LinearMap.mulLeft k a v * eS κ = LinearMap.mulLeft k a (eS κ' * v * eS κ) := by
  simp only [LinearMap.mulLeft_apply, ← mul_assoc, ha₁, ha₂]

theorem mulLeft_hyp₂ (a : ViolQuotient k Q Λ ν) (v d : ViolQuotient k Q Λ ν) :
    LinearMap.mulLeft k a (v * (eS κ * d * eS κ)) = LinearMap.mulLeft k a v * (eS κ * d * eS κ) := by
  simp only [LinearMap.mulLeft_apply, mul_assoc]

/-- Multiplying the right factor by `a` multiplies the image of Proposition 6.7 by `φ a`. -/
theorem unop_multF_mapF_mulLeft {κ'' : List (Fin ℓ)} {a : ViolQuotient k Q Λ ν}
    (ha₁ : eS κ'' * a = a) (ha₂ : a * eS κ' = a) (t) :
    (multF i ν κ'' κ (mapF i ν (LinearMap.mulLeft k a) (mulLeft_hyp₁ ha₁ ha₂) (mulLeft_hyp₂ a)
      t)).unop = φ a * (multF i ν κ' κ t).unop := by
  induction t using TensorAlong.induction_on with
  | tmul x y =>
    rw [mapF_tmul, unop_multF_tmul, unop_multF_tmul, unop_op, LinearMap.mulLeft_apply,
      ← mul_assoc, ha₁, ← mul_assoc, ← mul_assoc, ← map_mul, ← mul_assoc, ← mul_assoc, ha₂]
  | add s t hs ht => rw [map_add, map_add, unop_add, hs, ht, map_add, unop_add, mul_add]

include hQ hρ in
/-- Injectivity of `c ↦ r c` passes from `b` to `i :: b`. -/
theorem RedFirstData.inj_append (h : RedFirstData ν κ' κ E E' r)
    (hS : ∀ w, E' * w * eS κ = w → ∃ c, E * c * eS κ = c ∧ w = r * c)
    (hI : ∀ c, E * c * eS κ = c → r * c = 0 → c = 0)
    (z : ViolQuotient k Q Λ νᵢ) (hz : φ E * z * eR κ = z) (hrz : φ r * z = 0) : z = 0 := by
  -- the inverse `σ` of `c ↦ r c`, composed with the projection `v ↦ E' v e_κ`
  have hproj : ∀ v, E' * (E' * v * eS κ) * eS κ = E' * v * eS κ := fun v => by
    rw [← mul_assoc, ← mul_assoc, h.idem', mul_assoc, mul_assoc, idemS_mul_self, ← mul_assoc]
  have uniq : ∀ a b, E * a * eS κ = a → E * b * eS κ = b → r * a = r * b → a = b :=
    fun a b ha hb hab => sub_eq_zero.1 (hI _ (by rw [mul_sub, sub_mul, ha, hb])
      (by rw [mul_sub, hab, sub_self]))
  choose σ hσY hσ using fun v => hS _ (hproj v)
  have σadd : ∀ v w, σ (v + w) = σ v + σ w := fun v w => uniq _ _ (hσY _)
    (by rw [mul_add, add_mul, hσY, hσY]) (by rw [mul_add, ← hσ, ← hσ, ← hσ, mul_add, add_mul])
  have σsmul : ∀ (c : k) v, σ (c • v) = c • σ v := fun c v => uniq _ _ (hσY _)
    (by rw [mul_smul_comm, smul_mul_assoc, hσY]) (by rw [mul_smul_comm, ← hσ, ← hσ,
      mul_smul_comm, smul_mul_assoc])
  let gσ : ViolQuotient k Q Λ ν →ₗ[k] ViolQuotient k Q Λ ν :=
    { toFun := σ, map_add' := σadd, map_smul' := σsmul }
  have eSS : ∀ a, a * eS κ * eS κ = a * eS κ := fun a => by rw [mul_assoc, idemS_mul_self]
  have hE : ∀ c, E * c * eS κ = c → eS κ * c * eS κ = c := fun c hc => by
    rw [← hc]
    simp only [← mul_assoc, h.left, eSS]
  have hσ₁ : ∀ v, eS κ * gσ v * eS κ = gσ (eS κ' * v * eS κ) := fun v => by
    change eS κ * σ v * eS κ = σ (eS κ' * v * eS κ)
    rw [hE _ (hσY v)]
    refine uniq _ _ (hσY v) (hσY _) ?_
    rw [← hσ, ← hσ]
    simp only [← mul_assoc, h.right', eSS]
  have hσ₂ : ∀ v d, gσ (v * (eS κ * d * eS κ)) = gσ v * (eS κ * d * eS κ) := fun v d => by
    change σ _ = σ v * _
    refine uniq _ _ (hσY _) ?_ ?_
    · simp only [← mul_assoc, eSS]
      rw [h.mul_eq_of_corner (hσY v)]
    · rw [← hσ, ← mul_assoc r, ← hσ]
      simp only [← mul_assoc, eSS]
  have hrE : r * eS κ = r := by rw [← h.braid_right, mul_assoc, h.right]
  have hEr : eS κ' * r = r := by rw [← h.braid_left, ← mul_assoc, h.left']
  let R := mapF i ν (κ' := κ) (κ := κ) (κ'' := κ) (LinearMap.mulLeft k E) (mulLeft_hyp₁ h.left h.right)
    (mulLeft_hyp₂ (κ := κ) E)
  let T := mapF i ν (κ' := κ) (κ := κ) (κ'' := κ') (LinearMap.mulLeft k r) (mulLeft_hyp₁ hEr hrE)
    (mulLeft_hyp₂ (κ := κ) r)
  let T' := mapF i ν (κ' := κ') (κ := κ) (κ'' := κ) gσ hσ₁ hσ₂
  have hTR : ∀ t, T' (T (R t)) = R t := fun t => by
    induction t using TensorAlong.induction_on with
    | tmul x y =>
      simp only [R, T, T', mapF_tmul, unop_op, LinearMap.mulLeft_apply]
      have e₁ : σ (r * (E * y.unop)) = E * y.unop * eS κ := by
        refine uniq _ _ (hσY _) ?_ ?_
        · rw [← mul_assoc, ← mul_assoc, h.idem, mul_assoc, mul_assoc, idemS_mul_self,
            ← mul_assoc]
        · rw [← hσ, ← mul_assoc, ← mul_assoc, h.braid_left, ← mul_assoc, h.braid_right,
            ← mul_assoc, h.braid_right]
      change TensorAlong.tmul x (op (σ (r * (E * y.unop)))) = _
      rw [e₁, TensorAlong.tmul_corner, TensorAlong.tmul_corner (y := op (E * y.unop))]
      congr 2
      apply MulOpposite.unop_injective
      simp only [unop_mul, unop_op]
      rw [mul_assoc _ (eS κ) (eS κ), idemS_mul_self]
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  obtain ⟨t, ht⟩ := violMk_mult_surjective_append_op Q Λ i ν hQ ρ hρ κ κ (op z)
  have hzR : z * eR κ = z := calc
    z * eR κ = φ E * z * eR κ * eR κ := by rw [hz]
    _ = z := by rw [mul_assoc (φ E * z), (isIdempotentElem_violMk_redProj k Q Λ νᵢ κ).eq, hz]
  have hφEz : φ E * z = z := by
    rw [← hz, ← mul_assoc, ← mul_assoc, ← map_mul, h.idem]
  have hφE : φ (eS κ) * z = z := by
    rw [← hφEz, ← mul_assoc, ← map_mul, h.left]
  have ht' : (multF i ν κ κ t).unop = z := by
    rw [show multF i ν κ κ t = _ from ht]
    simp only [unop_mul, unop_op, appendViolOp_apply]
    rw [hzR, hφE]
  have h0 : multF i ν κ' κ (T (R t)) = 0 := by
    apply MulOpposite.unop_injective
    dsimp only [T, R]
    rw [unop_multF_mapF_mulLeft hEr hrE, unop_multF_mapF_mulLeft h.left h.right, ht', hφEz, hrz, unop_zero]
  have hT : T (R t) = 0 :=
    violMk_mult_injective_append_op Q Λ i ν hQ ρ hρ κ' κ (h0.trans (map_zero _).symm)
  have hR : R t = 0 := by rw [← hTR, hT, map_zero]
  rw [← hφEz, ← ht']
  have : (multF i ν κ κ (R t)).unop = φ E * (multF i ν κ κ t).unop :=
    unop_multF_mapF_mulLeft h.left h.right t
  rw [← this, hR, map_zero, unop_zero]

end Step

/-! ### No black strands -/

section Nil

variable {Q Λ}

omit [DecidableEq I] in
theorem exists_lbl_eq_inr_nil (s : Seq (stendhalWeight ℓ (0 : Multiset I)))
    (a : Fin (Multiset.card (stendhalWeight ℓ (0 : Multiset I)))) : ∃ r, s.lbl a = .inr r := by
  have h := s.mem a
  simp only [stendhalWeight, Multiset.map_zero, zero_add, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr.symm⟩

omit [DecidableEq I] in
theorem redWord_eq_map_nil (s : Seq (stendhalWeight ℓ (0 : Multiset I))) :
    redWord s = (List.finRange _).map fun a => (exists_lbl_eq_inr_nil s a).choose :=
  List.filterMap_eq_map_iff_forall_eq_some.2 fun a _ =>
    Sum.getRight?_eq_some_iff.2 (exists_lbl_eq_inr_nil s a).choose_spec

omit [DecidableEq I] in
/-- Without black strands a loading is determined by its red word. -/
theorem eq_of_redWord_eq_nil {s s' : Seq (stendhalWeight ℓ (0 : Multiset I))}
    (h : redWord s = redWord s') : s = s' := by
  rw [redWord_eq_map_nil, redWord_eq_map_nil, ← List.ofFn_eq_map, ← List.ofFn_eq_map] at h
  have h' := List.ofFn_injective h
  apply Subtype.ext
  funext a
  change s.lbl a = s'.lbl a
  rw [(exists_lbl_eq_inr_nil s a).choose_spec, (exists_lbl_eq_inr_nil s' a).choose_spec,
    congrFun h' a]

omit [DecidableEq I] in
/-- Without black strands a permutation of a loading is determined by its red word. -/
theorem eq_of_redWord_smul_eq_nil (s : Seq (stendhalWeight ℓ (0 : Multiset I)))
    {g g' : Perm (Fin (Multiset.card (stendhalWeight ℓ (0 : Multiset I))))}
    (h : redWord (g • s) = redWord (g' • s)) : g = g' := by
  have H := (redWord_smul_eq_iff s g g').1 h
  have hmono : StrictMono (g' * g⁻¹ : Perm _) := fun a b hab => by
    obtain ⟨r, hr⟩ := exists_lbl_eq_inr_nil s (g⁻¹ a)
    obtain ⟨r', hr'⟩ := exists_lbl_eq_inr_nil s (g⁻¹ b)
    have := (H _ _ r r' hr hr').1 (by simpa using hab)
    simpa using this
  have h1 : (g' * g⁻¹ : Perm _) = 1 := Equiv.ext fun a => congrFun hmono.eq_id a
  rw [mul_inv_eq_one] at h1
  exact h1.symm

omit [DecidableEq I] in
theorem subsingleton_cornerIdx_nil (κ' κ : List (Fin ℓ)) :
    Subsingleton {b : BlackIdx (ℓ := ℓ) (0 : Multiset I) //
      redWord (b.1.2.1 • b.1.1) = κ' ∧ redWord b.1.1 = κ} := by
  constructor
  rintro ⟨⟨⟨s, g, u⟩, hu⟩, h₁, h₂⟩ ⟨⟨⟨s', g', u'⟩, hu'⟩, h₁', h₂'⟩
  dsimp only at h₁ h₂ h₁' h₂' hu hu'
  obtain rfl : s = s' := eq_of_redWord_eq_nil (h₂.trans h₂'.symm)
  obtain rfl : g = g' := eq_of_redWord_smul_eq_nil s (h₁.trans h₁'.symm)
  obtain rfl : u = u' := Finsupp.ext fun a => by
    obtain ⟨r, hr⟩ := exists_lbl_eq_inr_nil s a
    rw [hu a (by rw [hr]; rfl), hu' a (by rw [hr]; rfl)]
  rfl

variable (hQ : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ (0 : Multiset I)))) → List ℕ)
  (hρ : IsReducedChoice ρ)

include hQ hρ in
/-- Without black strands, `e_{κ'} V e_κ` has dimension at most one. -/
theorem exists_smul_eq_of_nil (κ' κ : List (Fin ℓ)) {w w₀ : ViolQuotient k Q Λ 0}
    (hw : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * w * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = w)
    (hw₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * w₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = w₀)
    (hne : w₀ ≠ 0) : ∃ c : k, w = c • w₀ := by
  have := subsingleton_cornerIdx_nil (I := I) κ' κ
  let b := cornerBasis (Λ := Λ) (k := k) hQ ρ hρ κ' κ
  have : Module.Free k (cornerSpace k Q Λ 0 κ' κ) := Module.Free.of_basis b
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 (by
    rw [← b.mk_eq_rank'', Cardinal.le_one_iff_subsingleton]; infer_instance)
  have lift : ∀ x, violMk k Q Λ 0 (redProj k Q Λ 0 κ') * x *
      violMk k Q Λ 0 (redProj k Q Λ 0 κ) = x → ∃ c : k, x = c • violMk k Q Λ 0 v₀ := by
    intro x hx
    obtain ⟨y, rfl⟩ := violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := 0) x
    obtain ⟨c, hc⟩ := hv₀ ⟨_, ⟨y, rfl⟩⟩
    refine ⟨c, ?_⟩
    rw [← hx, ← map_mul, ← map_mul, ← map_smul]
    congr 1
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul] at this
    rw [this]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, redProj,
      mul_assoc]
  obtain ⟨c, rfl⟩ := lift w hw
  obtain ⟨c₀, rfl⟩ := lift w₀ hw₀
  have hc₀ : c₀ ≠ 0 := by rintro rfl; exact hne (zero_smul _ _)
  exact ⟨c / c₀, by rw [smul_smul, div_mul_cancel₀ _ hc₀]⟩

include hQ in
/-- Without black strands, `e_{κ'} V e_κ` is nonzero when `κ'` and `κ` are red orders of
loadings. -/
theorem exists_ne_zero_of_nil (s t : Seq (stendhalWeight ℓ (0 : Multiset I))) :
    ∃ r₀ : ViolQuotient k Q Λ 0, r₀ ≠ 0 ∧ violMk k Q Λ 0 (redProj k Q Λ 0 (redWord s)) * r₀ *
      violMk k Q Λ 0 (redProj k Q Λ 0 (redWord t)) = r₀ := by
  have hd := finrank_vacuum_braidColumn Q Λ hQ s t
  have : Nontrivial (violCorner k Q Λ 0 s (redWord t)) :=
    Module.nontrivial_of_finrank_pos (by rw [hd]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : violCorner k Q Λ 0 s (redWord t))
  obtain ⟨h₁, h₂⟩ := mem_violCorner_iff.1 x.2
  refine ⟨x.1, fun h => hx (Subtype.ext h), ?_⟩
  rw [mul_assoc, h₂, ← h₁, ← mul_assoc, ← map_mul, redProj_mul_e, ite_eq_left rfl]

end Nil

/-! ### Corollary 6.8 -/

section Main

variable {Q Λ}

/-- The black weight `i_1 + ⋯ + i_n` of a list `(i_n, …, i_1)` of labels. -/
def blackWeight : List I → Multiset I
  | [] => 0
  | i :: b => {i} + blackWeight b

variable (Q Λ) in
/-- The red-first idempotent `e⁰_{κ,b}` of `V`: the red strands in the order `κ`, followed by the
black strands of `b`, added one at a time at the right. -/
noncomputable def redFirstViol (κ : List (Fin ℓ)) : ∀ b : List I, ViolQuotient k Q Λ (blackWeight b)
  | [] => violMk k Q Λ 0 (redProj k Q Λ 0 κ)
  | i :: b => appendViol Q Λ i (blackWeight b) (redFirstViol κ b)

/-- The braid `r_b`: the diagram `r₀` without black strands, with the black strands of `b` added
at the right. -/
noncomputable def redBraid (r₀ : ViolQuotient k Q Λ 0) : ∀ b : List I,
    ViolQuotient k Q Λ (blackWeight b)
  | [] => r₀
  | i :: b => appendViol Q Λ i (blackWeight b) (redBraid r₀ b)

set_option quotPrecheck false in
local notation "eB" b:max κ:max =>
  violMk k Q Λ (blackWeight b) (redProj k Q Λ (blackWeight b) κ)

variable (hQ : KLRSymm Q)
  (ρ : ∀ ν : Multiset I, Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ ν, IsReducedChoice (ρ ν))

include hQ hρ in
theorem redFirstData_redBraid {κ' κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀)
    (hne : r₀ ≠ 0) (b : List I) :
    RedFirstData (blackWeight b) κ' κ (redFirstViol Q Λ κ b) (redFirstViol Q Λ κ' b)
        (redBraid r₀ b) ∧
      (∀ w, redFirstViol Q Λ κ' b * w * eB b κ = w →
        ∃ c, redFirstViol Q Λ κ b * c * eB b κ = c ∧ w = redBraid r₀ b * c) ∧
      (∀ c, redFirstViol Q Λ κ b * c * eB b κ = c → redBraid r₀ b * c = 0 → c = 0) := by
  induction b with
  | nil =>
    dsimp only [blackWeight, redFirstViol, redBraid]
    have i₁ : ∀ κ, violMk k Q Λ 0 (redProj k Q Λ 0 κ) * violMk k Q Λ 0 (redProj k Q Λ 0 κ) =
        violMk k Q Λ 0 (redProj k Q Λ 0 κ) := fun κ => idemS_mul_self κ
    have hl : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ = r₀ := by
      conv_lhs => rw [← hr₀]
      rw [← mul_assoc, ← mul_assoc, i₁, hr₀]
    have hr : r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀ := by
      conv_lhs => rw [← hr₀]
      rw [mul_assoc, i₁, hr₀]
    refine ⟨⟨i₁ κ, i₁ κ, i₁ κ', i₁ κ', hl, hr, i₁ κ, i₁ κ'⟩, fun w hw => ?_, fun c hc hrc => ?_⟩
    · obtain ⟨c, rfl⟩ := exists_smul_eq_of_nil hQ (ρ 0) (hρ 0) κ' κ hw hr₀ hne
      refine ⟨c • violMk k Q Λ 0 (redProj k Q Λ 0 κ), ?_, ?_⟩
      · rw [mul_smul_comm, smul_mul_assoc, i₁, i₁]
      · rw [mul_smul_comm, hr]
    · by_cases he : violMk k Q Λ 0 (redProj k Q Λ 0 κ) = 0
      · rw [← hc, he, zero_mul, zero_mul]
      · obtain ⟨a, rfl⟩ := exists_smul_eq_of_nil hQ (ρ 0) (hρ 0) κ κ hc
          (by rw [i₁, i₁]) he
        rw [mul_smul_comm, hr, smul_eq_zero] at hrc
        rw [hrc.resolve_right hne, zero_smul]
  | cons i b ih =>
    obtain ⟨h, hS, hI⟩ := ih
    exact ⟨h.append, fun z hz => h.surj_append hQ (ρ _) (hρ _) hS z hz,
      fun z hz hrz => h.inj_append hQ (ρ _) (hρ _) hS hI z hz hrz⟩

theorem redBraid_mul_mem {κ' κ : List (Fin ℓ)} {b : List I} {r₀ : ViolQuotient k Q Λ 0}
    (h : RedFirstData (blackWeight b) κ' κ (redFirstViol Q Λ κ b) (redFirstViol Q Λ κ' b)
      (redBraid r₀ b)) {c : ViolQuotient k Q Λ (blackWeight b)}
    (hc : redFirstViol Q Λ κ b * c * eB b κ = c) :
    redFirstViol Q Λ κ' b * (redBraid r₀ b * c) * eB b κ = redBraid r₀ b * c := by
  rw [← mul_assoc, h.braid_left, mul_assoc, ← hc, mul_assoc _ (eB b κ), idemS_mul_self]

include hQ hρ in
/-- **Webster, Corollary 6.8** (arXiv:1309.3796v3): `𝔅(κ', κ) P⁰ ≅ P⁰`. For any nonzero diagram
`r₀ ∈ e_{κ'} V e_κ` without black strands, and any list `b` of black labels, left multiplication
by `r_b` (`redBraid`) is a bijection from `P⁰_{κ,b} = e⁰_{κ,b} V e_κ` onto
`𝔅(κ', κ) P⁰_{κ',b} = e⁰_{κ',b} V e_κ`; it commutes with the right action of the corner
`e_κ V e_κ`. Webster's statement is the case of an adjacent transposition; this holds for all red
orders `κ'`, `κ` (ungraded). -/
theorem bijective_redBraid_mul {κ' κ : List (Fin ℓ)} {r₀ : ViolQuotient k Q Λ 0}
    (hr₀ : violMk k Q Λ 0 (redProj k Q Λ 0 κ') * r₀ * violMk k Q Λ 0 (redProj k Q Λ 0 κ) = r₀)
    (hne : r₀ ≠ 0) (b : List I) :
    Function.Bijective fun c : {c // redFirstViol Q Λ κ b * c * eB b κ = c} =>
      (⟨redBraid r₀ b * c.1, redBraid_mul_mem
        (redFirstData_redBraid hQ ρ hρ hr₀ hne b).1 c.2⟩ :
        {w // redFirstViol Q Λ κ' b * w * eB b κ = w}) := by
  obtain ⟨h, hS, hI⟩ := redFirstData_redBraid hQ ρ hρ hr₀ hne b
  refine ⟨fun c c' hcc => Subtype.ext ?_, fun w => ?_⟩
  · have e := congrArg Subtype.val hcc
    dsimp only at e
    refine sub_eq_zero.1 (hI _ ?_ (by rw [mul_sub, e, sub_self]))
    rw [mul_sub, sub_mul, c.2, c'.2]
  · obtain ⟨c, hc, hw⟩ := hS w.1 w.2
    exact ⟨⟨c, hc⟩, Subtype.ext hw.symm⟩

end Main

end BraidedStendhalAlgebra

end

end Categorification.Stendhal
