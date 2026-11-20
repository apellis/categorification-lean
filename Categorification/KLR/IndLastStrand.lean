/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.IndDecomp
import Categorification.TypeA.LastStrand
import Categorification.Algebra.InductionAlongRes

/-!
# The last strand of an induced module: the part from the right factor

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18 (the Mackey filtration), in the case
where one strand coloured `i` is restricted off the right of an induced module. This is the
KLR input of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5: in `E_i S(M)` the diagrams in which the removed
strand stays to the right of the cut form a submodule `≅ S(₂E_i M)`.

Let `ν' = ν₀' + i`. For an `R(ν) ⊗ R(ν')`-module `N`, write `₂N = (1 ⊗ 1_{ν₀',i}) N`, an
`R(ν) ⊗ R(ν₀')`-module (`KLRAlgebra.ResRight`). Appending a strand coloured `i` on the right
gives a map

`Φ : Ind_{ν,ν₀'} ₂N → Ind_{ν,ν'} N`, `r ⊗ n ↦ ι(r ⊗ 1_i) ⊗ n`

(`KLRAlgebra.indAppend`). It intertwines `R(ν + ν₀')`, acting on the target through
`a ↦ ι(a ⊗ 1_i)` (`KLRAlgebra.indAppend_smul`). In the shuffle decomposition
`Ind_{ν,ν'} N ≅ ⊕_u N` (`KLRAlgebra.indDecompOf`) it is the inclusion of the summands of the
shuffles fixing the last strand (`KLRAlgebra.indDecompOf_indAppend_ext`,
`KLRAlgebra.indDecompOf_indAppend_top`); in particular `Φ` is injective
(`KLRAlgebra.indAppend_injective`).

## Main definitions

* `KLRAlgebra.appendR`: `a ↦ ι(a ⊗ 1_i)`, `R(γ) → R(γ + i)`.
* `KLRAlgebra.tensorAppendR`: `R(ν) ⊗ R(ν₀') → R(ν) ⊗ R(ν₀' + i)`.
* `KLRAlgebra.ResRight`: the module `₂N`.
* `KLRAlgebra.indAppend`: the map `Φ`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

local notation "Si" i => (Singleton.singleton i : Multiset I)

/-! ### Appending a strand on the right -/

section Append

variable (Q) (γ : Multiset I) (i : I)

/-- Appending a strand coloured `i` on the right: `a ↦ ι(a ⊗ 1_i)`. -/
noncomputable def appendR : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q (γ + Si i) where
  toFun x := concat Q γ (Si i) (x ⊗ₜ 1)
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero]
  map_add' x y := by rw [TensorProduct.add_tmul, map_add]
  map_mul' x y := by rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_smul' c x := by rw [← TensorProduct.smul_tmul', map_smul]; rfl

/-- `appendR` as a linear map. -/
noncomputable def appendRLin : KLRAlgebra k Q γ →ₗ[k] KLRAlgebra k Q (γ + Si i) :=
  (concat Q γ (Si i)).comp ((TensorProduct.mk k _ _).flip 1)

variable {Q γ i}

theorem appendRLin_apply (a : KLRAlgebra k Q γ) : appendRLin Q γ i a = appendR Q γ i a := rfl

theorem appendR_apply (a : KLRAlgebra k Q γ) : appendR Q γ i a = concat Q γ (Si i) (a ⊗ₜ 1) :=
  rfl

theorem appendR_one : appendR Q γ i 1 = oneConcat Q γ (Si i) := concat_one

theorem appendR_ψw {α : List ℕ} (hα : ValidWord (Multiset.card γ) α) :
    appendR Q γ i (ψw α) = ψw α * oneConcat Q γ (Si i) := by
  rw [appendR_apply, ← ψw_nil (Q := Q) (ν := Si i), concat_ψw_tmul_ψw hα (validWord_nil _)]
  simp [shiftWord]

end Append

section Cast

theorem castKLR_ψw' {μ μ' : Multiset I} (h : μ = μ') (ρ : List ℕ) :
    castKLR Q h (ψw ρ) = ψw ρ := by
  subst h; rfl

end Cast

/-! ### Appending on the right of the second tensor factor -/

section TensorAppend

variable (Q) (ν ν₀' : Multiset I) (i : I)

/-- `a ⊗ b ↦ a ⊗ ι(b ⊗ 1_i)`, `R(ν) ⊗ R(ν₀') → R(ν) ⊗ R(ν₀' + i)`. -/
noncomputable def tensorAppendR : TensorKLR Q ν ν₀' →ₙₐ[k] TensorKLR Q ν (ν₀' + Si i) where
  toFun := TensorProduct.map LinearMap.id (appendRLin Q ν₀' i)
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' s t := by
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [add_mul, map_add, hs, hs']
    | tmul a b =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simp only [mul_add, map_add, ht, ht']
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
          LinearMap.id_apply, appendRLin_apply, map_mul]

variable {Q ν ν₀' i}

theorem tensorAppendR_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν₀') :
    tensorAppendR Q ν ν₀' i (a ⊗ₜ b) = a ⊗ₜ appendR Q ν₀' i b := rfl

theorem tensorAppendR_one :
    tensorAppendR Q ν ν₀' i 1 = 1 ⊗ₜ oneConcat Q ν₀' (Si i) := by
  rw [Algebra.TensorProduct.one_def, tensorAppendR_tmul, appendR_one]

/-- **Associativity of appending**: `ι(ι(t) ⊗ 1_i) = ι(t')` for `t' = (1 ⊗ append)(t)`. -/
theorem castKLR_appendR_concat (t : TensorKLR Q ν ν₀') :
    castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i (concat Q ν ν₀' t)) =
      concat Q ν (ν₀' + Si i) (tensorAppendR Q ν ν₀' i t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht, map_add]
  | tmul a b => rw [appendR_apply, concat_assoc, tensorAppendR_tmul, appendR_apply]

end TensorAppend

/-! ### The module `₂N` and the map `Φ` -/

section IndAppend

variable (Q) (ν ν₀' : Multiset I) (i : I)

/-- `tensorAppendR` as a nonunital ring map. -/
noncomputable abbrev tensorAppendHom : TensorKLR Q ν ν₀' →ₙ+* TensorKLR Q ν (ν₀' + Si i) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (tensorAppendR Q ν ν₀' i)

/-- **`₂N = (1 ⊗ 1_{ν₀',i}) N`**, an `R(ν) ⊗ R(ν₀')`-module through `tensorAppendR`. -/
abbrev ResRight (N : Type*) [AddCommGroup N] [Module (TensorKLR Q ν (ν₀' + Si i)) N] : Type _ :=
  InductionAlong.Res (tensorAppendHom Q ν ν₀' i) N

variable {Q ν ν₀' i}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]

noncomputable instance : Module k (ResRight Q ν ν₀' i N) :=
  Module.compHom _ (algebraMap k (TensorKLR Q ν ν₀'))

instance : IsScalarTower k (TensorKLR Q ν ν₀') (ResRight Q ν ν₀' i N) where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (TensorKLR Q ν ν₀') c) • (t • n)
    rw [Algebra.smul_def, mul_smul]

theorem ResRight.val_smul_k (c : k) (n : ResRight Q ν ν₀' i N) : (c • n).val = c • n.val := by
  change tensorAppendR Q ν ν₀' i (algebraMap k _ c) • n.val = c • n.val
  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc]
  exact congrArg (c • ·) n.prop

/-- The bimodule part of `Φ`: `r ↦ ι(r ⊗ 1_i)`, `R(ν + ν₀') 1_{ν,ν₀'} → R(ν + ν') 1_{ν,ν'}`. -/
noncomputable def indAppendBimod : IndBimod Q ν ν₀' →ₗ[k] IndBimod Q ν (ν₀' + Si i) where
  toFun r := ⟨castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i r), by
    rw [Graded.mem_leftIdeal]
    have hr : (r : KLRAlgebra k Q (ν + ν₀')) = r * concat Q ν ν₀' 1 := by
      rw [concat_one]; exact r.2.symm
    rw [hr, map_mul, map_mul, castKLR_appendR_concat, mul_assoc, concat_mul_oneConcat]⟩
  map_add' r r' := Subtype.ext (by simp)
  map_smul' c r := Subtype.ext (by
    change castKLR Q _ (appendR Q (ν + ν₀') i (c • (r : KLRAlgebra k Q (ν + ν₀')))) =
      c • castKLR Q _ (appendR Q (ν + ν₀') i r)
    rw [map_smul, map_smul])

theorem coe_indAppendBimod (r : IndBimod Q ν ν₀') :
    ((indAppendBimod (i := i) r : IndBimod Q ν (ν₀' + Si i)) : KLRAlgebra k Q _) =
      castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i r) := rfl

theorem indAppendBimod_op_smul (t : TensorKLR Q ν ν₀') (r : IndBimod Q ν ν₀') :
    indAppendBimod (i := i) (op t • r) = op (tensorAppendR Q ν ν₀' i t) • indAppendBimod r :=
  Subtype.ext (by
    rw [coe_indAppendBimod, coe_op_smul, coe_op_smul, coe_indAppendBimod, unop_op, unop_op,
      map_mul, map_mul, castKLR_appendR_concat])

theorem indAppendBimod_smul (a : KLRAlgebra k Q (ν + ν₀')) (r : IndBimod Q ν ν₀') :
    indAppendBimod (i := i) (a • r) =
      castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i a) • indAppendBimod r :=
  Subtype.ext (by
    rw [coe_indAppendBimod, Submodule.coe_smul, Submodule.coe_smul, coe_indAppendBimod,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul])

/-- The bilinear map `(r, n) ↦ ι(r ⊗ 1_i) ⊗ n`. -/
noncomputable def indAppendBil :
    IndBimod Q ν ν₀' →ₗ[k] ResRight Q ν ν₀' i N →ₗ[k] Ind Q ν (ν₀' + Si i) N :=
  LinearMap.mk₂ k (fun r n => BalancedTensor.tmul (indAppendBimod r) n.val)
    (fun r r' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c r n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun r n n' => by rw [InductionAlong.Res.val_add, BalancedTensor.tmul_add])
    (fun c r n => by rw [ResRight.val_smul_k, BalancedTensor.tmul_smul])

/-- **The map `Φ : Ind_{ν,ν₀'} ₂N → Ind_{ν,ν'} N`**, `r ⊗ n ↦ ι(r ⊗ 1_i) ⊗ n`. -/
noncomputable def indAppend : Ind Q ν ν₀' (ResRight Q ν ν₀' i N) →ₗ[k] Ind Q ν (ν₀' + Si i) N :=
  BalancedTensor.lift indAppendBil (fun r t n => by
    change BalancedTensor.tmul (indAppendBimod (op t • r)) n.val =
      BalancedTensor.tmul (indAppendBimod r) (tensorAppendR Q ν ν₀' i t • n.val)
    rw [indAppendBimod_op_smul, BalancedTensor.op_smul_tmul])

theorem indAppend_tmul (r : IndBimod Q ν ν₀') (n : ResRight Q ν ν₀' i N) :
    indAppend (BalancedTensor.tmul r n) = BalancedTensor.tmul (indAppendBimod r) n.val := rfl

/-- `Φ` intertwines `a` with `ι(a ⊗ 1_i)`. -/
theorem indAppend_smul (a : KLRAlgebra k Q (ν + ν₀')) (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    indAppend (a • x) =
      castKLR Q (add_assoc ν ν₀' (Si i)) (appendR Q (ν + ν₀') i a) • indAppend x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul r n =>
    rw [BalancedTensor.smul_tmul', indAppend_tmul, indAppend_tmul, indAppendBimod_smul,
      BalancedTensor.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end IndAppend

/-! ### `Φ` in shuffle coordinates -/

section Coordinates

variable {ν ν₀' : Multiset I} {i : I}

omit [DecidableEq I] in
theorem card_add_singleton_eq :
    Multiset.card (ν + ν₀') + 1 = Multiset.card (ν + (ν₀' + ({i} : Multiset I))) := by
  simp [add_assoc]

/-- Reduced words for the shuffles of `(ν, ν₀' + i)`: the canonical word of `v` on the shuffles
`v ⊕ 1` fixing the last strand, the canonical word otherwise. -/
noncomputable def lastWord (u : Shuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))) :
    List ℕ :=
  if hu : u.1 (lastPos (card_add_singleton_eq (i := i))) = lastPos (card_add_singleton_eq (i := i)) then
    canWord _ (Classical.choose (exists_extShuffle_eq (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
      (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') hu)).1
  else shufWord u

omit [DecidableEq I] in
theorem lastWord_extShuffle (v : Shuffle (Seq.card_add' ν ν₀')) :
    lastWord (extShuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) (card_add_singleton_eq (i := i))
      (Seq.card_add' ν ν₀') v) = canWord _ v.1 := by
  have hu : (extShuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
      (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v).1
        (lastPos (card_add_singleton_eq (i := i))) = lastPos (card_add_singleton_eq (i := i)) :=
    extPerm_last _ v.1
  simp only [lastWord, hu, ↓reduceDIte]
  have := Classical.choose_spec (exists_extShuffle_eq (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
      (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') hu)
  rw [extShuffle_injective _ _ _ this]

omit [DecidableEq I] in
theorem lastWord_spec (u : Shuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))) :
    IsReduced (Multiset.card (ν + (ν₀' + ({i} : Multiset I)))) (lastWord u) ∧
      wordProd (Multiset.card (ν + (ν₀' + ({i} : Multiset I)))) (lastWord u) = u.1 := by
  by_cases hu : u.1 (lastPos (card_add_singleton_eq (i := i))) = lastPos (card_add_singleton_eq (i := i))
  · obtain ⟨v, rfl⟩ := exists_extShuffle_eq (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
      (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') hu
    rw [lastWord_extShuffle, extShuffle_val]
    exact ⟨isReduced_canWord_ext (card_add_singleton_eq (i := i)) v.1,
      wordProd_canWord_ext (card_add_singleton_eq (i := i)) v.1⟩
  · simp only [lastWord, hu, ↓reduceDIte]
    exact shufWord_spec u

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]

variable (σ : Shuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) → List ℕ)
  (hσ : ∀ u, IsReduced (Multiset.card (ν + (ν₀' + ({i} : Multiset I)))) (σ u) ∧
    wordProd (Multiset.card (ν + (ν₀' + ({i} : Multiset I)))) (σ u) = u.1)
  (hext : ∀ v : Shuffle (Seq.card_add' ν ν₀'), σ (extShuffle
    (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) (card_add_singleton_eq (i := i))
    (Seq.card_add' ν ν₀') v) = canWord _ v.1)

include hext in
/-- **`Φ` on the shuffle basis**: `Φ(ŵ_v^* ⊗ n) = ŵ_{v ⊕ 1}^* ⊗ n`, for any choice of words `σ`
that uses the canonical word of `v` at `v ⊕ 1`. -/
theorem indAppend_tmul_hatWRevSubOf (v : Shuffle (Seq.card_add' ν ν₀'))
    (n : ResRight Q ν ν₀' i N) :
    indAppend (BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v) n) =
      BalancedTensor.tmul (hatWRevSubOf (k := k) (Q := Q) σ (extShuffle
        (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) (card_add_singleton_eq (i := i))
        (Seq.card_add' ν ν₀') v)) n.val := by
  rw [indAppend_tmul]
  have hα : ValidWord (Multiset.card (ν + ν₀')) (shufWord v).reverse :=
    validWord_reverse.2 (validWord_canWord _ _)
  have key : indAppendBimod (i := i) (hatWRevSub (k := k) (Q := Q) v) =
      op (tensorAppendR Q ν ν₀' i 1) • hatWRevSubOf σ (extShuffle
        (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) (card_add_singleton_eq (i := i))
        (Seq.card_add' ν ν₀') v) := by
    apply Subtype.ext
    rw [coe_indAppendBimod, coe_op_smul, unop_op, coe_hatWRevSub, hatWRev_eq,
      coe_hatWRevSubOf, hatWRevOf, hext, mul_assoc, oneConcat_mul_concat,
      ← concat_one, map_mul, map_mul, castKLR_appendR_concat, appendR_ψw hα, map_mul,
      castKLR_ψw', mul_assoc, ← castKLR_appendR_concat, ← appendR_one, ← map_mul, ← map_mul,
      one_mul]
    rfl
  rw [key, BalancedTensor.op_smul_tmul]
  exact congrArg _ n.prop

/-- **`Φ` on the shuffle basis** for the words `lastWord`. -/
theorem indAppend_tmul_hatWRevSub (v : Shuffle (Seq.card_add' ν ν₀'))
    (n : ResRight Q ν ν₀' i N) :
    indAppend (BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v) n) =
      BalancedTensor.tmul (hatWRevSubOf (k := k) (Q := Q) lastWord (extShuffle
        (Seq.card_add' ν (ν₀' + ({i} : Multiset I))) (card_add_singleton_eq (i := i))
        (Seq.card_add' ν ν₀') v)) n.val :=
  indAppend_tmul_hatWRevSubOf lastWord lastWord_extShuffle v n

variable (hsym : KLRSymm Q)

include hext in
/-- **`Φ` in shuffle coordinates**: the coordinates of `Φ x` are those of `x`, placed at the
shuffles `v ⊕ 1`. -/
theorem indDecompOf_indAppend (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    indDecompOf σ hsym hσ N (indAppend x) =
      ∑ v, Pi.single (extShuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
        (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v)
          (indDecomp hsym (ResRight Q ν ν₀' i N) x v).val := by
  conv_lhs => rw [← (indDecomp hsym (ResRight Q ν ν₀' i N)).symm_apply_apply x]
  rw [indDecomp_symm_apply, map_sum, map_sum]
  simp only [indAppend_tmul_hatWRevSubOf σ hext, indDecompOf_tmul_hatWRevSubOf]

include hext in
/-- The coordinate of `Φ x` at a shuffle `v ⊕ 1` fixing the last strand. -/
theorem indDecompOf_indAppend_ext (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N))
    (v : Shuffle (Seq.card_add' ν ν₀')) :
    indDecompOf σ hsym hσ N (indAppend x)
        (extShuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I)))
          (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v) =
      (indDecomp hsym (ResRight Q ν ν₀' i N) x v).val := by
  rw [indDecompOf_indAppend σ hσ hext, Finset.sum_apply, Finset.sum_eq_single v]
  · exact Pi.single_eq_same _ _
  · intro v' _ hv'
    exact Pi.single_eq_of_ne (fun he => hv' (extShuffle_injective _ _ _ he).symm) _
  · intro hv; exact absurd (Finset.mem_univ v) hv

include hext in
/-- The coordinates of `Φ x` vanish at the shuffles moving the last strand. -/
theorem indDecompOf_indAppend_top (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N))
    (u : Shuffle (Seq.card_add' ν (ν₀' + ({i} : Multiset I))))
    (hu : u.1 (lastPos (card_add_singleton_eq (i := i))) ≠
      lastPos (card_add_singleton_eq (i := i))) :
    indDecompOf σ hsym hσ N (indAppend x) u = 0 := by
  rw [indDecompOf_indAppend σ hσ hext, Finset.sum_apply]
  refine Finset.sum_eq_zero fun v _ => Pi.single_eq_of_ne (fun he => hu ?_) _
  rw [he, extShuffle_val]
  exact extPerm_last _ v.1

include hsym in
/-- **`Φ` is injective.** -/
theorem indAppend_injective :
    Function.Injective (indAppend (Q := Q) (ν := ν) (ν₀' := ν₀') (i := i) (N := N)) := by
  intro x y hxy
  apply (indDecomp hsym (ResRight Q ν ν₀' i N)).injective
  funext v
  apply InductionAlong.Res.ext
  rw [← indDecompOf_indAppend_ext lastWord lastWord_spec lastWord_extShuffle hsym,
    ← indDecompOf_indAppend_ext lastWord lastWord_spec lastWord_extShuffle hsym, hxy]

end Coordinates

end KLRAlgebra

end Categorification.KLR
