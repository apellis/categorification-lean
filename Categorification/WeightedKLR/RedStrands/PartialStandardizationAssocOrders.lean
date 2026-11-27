/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutOneStepLeft
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocInd3Transport
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocRelabelComp

/-!
# Iterated partial standardization does not depend on the order of the cuts

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+r}}` defined
after Definition 5.4. Webster defines the partial standardization with several blocks in one
step and uses without proof that it agrees with iterated partial standardization, in any order
of the cuts. For three blocks the two iterations are `BlocksStandard` (cut between the last two
blocks first, labels `Fin (a + (m + r))`) and `BlocksStandardL` (cut between the first two
blocks first, labels `Fin ((a + m) + r)`). Both are one-step partial standardizations
(`blocksStandardOneStepEquiv`, `blocksStandardOneStepEquivL`); here the two one-step models are
identified along the relabelling `Fin.cast (add_assoc a m r)` of the red strands
(`blocksOneStepQuotAssocEquiv`), so that the two iterations agree
(`blocksStandardAssocEquiv`).

## Main definitions

* `Stendhal.blocksAssocFactorEquiv`: `(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ) ≃ T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`
  for the two labellings of the red strands.
* `Stendhal.BlocksAssocInput`: a module over the three blocks, for the other nesting.
* `Stendhal.blocksAssocKLR`: the relabelling of the affine KLR algebra of all strands.

## Main results

* `Stendhal.blocksOneStepQuotAssocEquiv`: the two one-step models agree.
* `Stendhal.blocksStandardAssocEquiv`: `BlocksStandardL ≃ BlocksStandard`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)

local notation "ε" => Fin.cast (Nat.add_assoc a m r)
local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m r)
local notation "cₑ" => Sum.map (id : I → I) (Fin.cast (Nat.add_assoc a m r))
local notation "S" => stendhalQ Q Λ
local notation "Sₗ" => stendhalQ Q (Λ ∘ Fin.cast (Nat.add_assoc a m r))

/-! ### The red labels of the blocks -/

omit [DecidableEq I] in
theorem cast_castAdd_castAdd :
    ε ∘ Fin.castAdd r ∘ Fin.castAdd m = (Fin.castAdd (m + r) : Fin a → Fin (a + (m + r))) :=
  funext fun _ => Fin.ext rfl

omit [DecidableEq I] in
theorem cast_castAdd_natAdd :
    ε ∘ Fin.castAdd r ∘ Fin.natAdd a = (Fin.natAdd a ∘ Fin.castAdd r : Fin m → Fin (a + (m + r))) :=
  funext fun _ => Fin.ext rfl

omit [DecidableEq I] in
theorem cast_natAdd :
    ε ∘ Fin.natAdd (a + m) = (Fin.natAdd a ∘ Fin.natAdd m : Fin r → Fin (a + (m + r))) :=
  funext fun _ => Fin.ext (Nat.add_assoc _ _ _)

/-- **The algebras of the three blocks for the two nestings agree**:
`(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ) ≃ T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
def blocksAssocFactorEquiv : blocksFactorAlgebraL Q ΛL θ β γ ≃ₐ[k] blocksFactorAlgebra Q Λ θ β γ :=
  (Algebra.TensorProduct.assoc k k k _ _ _).trans
    (Algebra.TensorProduct.congr
      (tensorProductAlgebraCast Q
        (congrArg (Λ ∘ ·) (cast_castAdd_castAdd (a := a) (m := m) (r := r))) θ)
      (Algebra.TensorProduct.congr
        (tensorProductAlgebraCast Q
          (congrArg (Λ ∘ ·) (cast_castAdd_natAdd (a := a) (m := m) (r := r))) β)
        (tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) (cast_natAdd (a := a) (m := m) (r := r))) γ)))

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]

/-- A module over `T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`, as a module over
`(T^A(θ) ⊗ T^M(β)) ⊗ T^R(γ)`. -/
@[nolint unusedArguments]
def BlocksAssocInput (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin (a + (m + r)) → I →₀ ℕ) (_θ _β _γ : Multiset I) (N : Type*) : Type _ := N

local notation "Nₗ" => BlocksAssocInput Q Λ θ β γ N

instance : AddCommGroup Nₗ := inferInstanceAs (AddCommGroup N)
instance : Module k Nₗ := inferInstanceAs (Module k N)
instance : Module (blocksFactorAlgebraL Q ΛL θ β γ) Nₗ :=
  Module.compHom N (blocksAssocFactorEquiv Q Λ θ β γ).toAlgHom.toRingHom

omit [Module k N] [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksAssocInput_smul (t : blocksFactorAlgebraL Q ΛL θ β γ) (n : Nₗ) :
    t • n = blocksAssocFactorEquiv Q Λ θ β γ t • (show N from n) := rfl

instance : IsScalarTower k (blocksFactorAlgebraL Q ΛL θ β γ) Nₗ where
  smul_assoc c t n := by
    rw [blocksAssocInput_smul, blocksAssocInput_smul,
      show blocksAssocFactorEquiv Q Λ θ β γ (c • t) = c • blocksAssocFactorEquiv Q Λ θ β γ t from
        (blocksAssocFactorEquiv Q Λ θ β γ).toLinearEquiv.map_smul c t]
    exact smul_assoc c (blocksAssocFactorEquiv Q Λ θ β γ t) (show N from n)

/-! ### Relabelling the affine KLR algebras along `Fin.cast` -/

local notation "α̂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd m)) (stendhalWeight a θ))
local notation "β̂ₗ" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight m β))
local notation "δₗ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd (a + m))) (stendhalWeight r γ)
local notation "αᵣ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "β̂ᵣ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β))
local notation "γ̂ᵣ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ))

/-- The relabelling of the affine KLR algebra of a weight along `Fin.cast`, followed by an
identification of weights. -/
def blocksAssocRelabel (μ : Multiset (I ⊕ Fin ((a + m) + r)))
    (μ' : Multiset (I ⊕ Fin (a + (m + r))))
    (w : μ.map cₑ = μ') : KLRAlgebra k Sₗ μ ≃ₐ[k] KLRAlgebra k S μ' :=
  (relabelEquiv (stendhalRelabel Q Λ ε (Fin.cast_injective _) μ)).trans (castKLR S w)

private theorem castKLR_trans'' {μ₁ μ₂ μ₃ : Multiset (I ⊕ Fin (a + (m + r)))}
    (h₁ : μ₁ = μ₂) (h₂ : μ₂ = μ₃) (z : KLRAlgebra k S μ₁) :
    castKLR S h₂ (castKLR S h₁ z) = castKLR S (h₁.trans h₂) z := by
  subst h₁ h₂; rfl

/-- The relabelling intertwines the inclusions `ι_{μ₁,μ₂}`. -/
theorem blocksAssocRelabel_concat {μ₁ μ₂ : Multiset (I ⊕ Fin ((a + m) + r))}
    {μ₁' μ₂' : Multiset (I ⊕ Fin (a + (m + r)))} (w₁ : μ₁.map cₑ = μ₁') (w₂ : μ₂.map cₑ = μ₂')
    (w : (μ₁ + μ₂).map cₑ = μ₁' + μ₂') (t : TensorKLR Sₗ μ₁ μ₂) :
    blocksAssocRelabel Q Λ (μ₁ + μ₂) (μ₁' + μ₂') w (concat Sₗ μ₁ μ₂ t) =
      concat S μ₁' μ₂' (Algebra.TensorProduct.congr (blocksAssocRelabel Q Λ μ₁ μ₁' w₁)
        (blocksAssocRelabel Q Λ μ₂ μ₂' w₂) t) := by
  have h1 := stendhalRelabelAdd_concat Q Λ ε (Fin.cast_injective (Nat.add_assoc a m r)) t
  have h2 := castKLR_concat (Q := S) w₁ w₂
    (stendhalRelabelTensor Q Λ ε (Fin.cast_injective (Nat.add_assoc a m r)) μ₁ μ₂ t)
  have h3 : blocksAssocRelabel Q Λ (μ₁ + μ₂) (μ₁' + μ₂') w (concat Sₗ μ₁ μ₂ t) =
      castKLR S (add_eq_add_of_eq w₁ w₂) (stendhalRelabelAdd Q Λ ε
        (Fin.cast_injective (Nat.add_assoc a m r)) μ₁ μ₂ (concat Sₗ μ₁ μ₂ t)) :=
    (castKLR_trans'' Q Λ _ _ _).symm
  rw [h3, h1, h2]
  congr 1
  clear h1 h2 h3
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]
  | tmul u v =>
    exact castTensor_tmul (Q := S) w₁ w₂ _ _

omit [DecidableEq I] in
theorem blocksAssocWeight_head : (α̂).map cₑ = αᵣ := by
  rw [← map_sumMap_comp, ← map_sumMap_comp]
  exact congrArg (fun g => (stendhalWeight a θ).map (Sum.map (id : I → I) g))
    (cast_castAdd_castAdd (a := a) (m := m) (r := r))

omit [DecidableEq I] in
theorem blocksAssocWeight_mid : (β̂ₗ).map cₑ = β̂ᵣ := by
  rw [← map_sumMap_comp, ← map_sumMap_comp, ← map_sumMap_comp]
  exact congrArg (fun g => (stendhalWeight m β).map (Sum.map (id : I → I) g))
    (cast_castAdd_natAdd (a := a) (m := m) (r := r))

omit [DecidableEq I] in
theorem blocksAssocWeight_last : (δₗ).map cₑ = γ̂ᵣ := by
  rw [← map_sumMap_comp, ← map_sumMap_comp]
  exact congrArg (fun g => (stendhalWeight r γ).map (Sum.map (id : I → I) g))
    (cast_natAdd (a := a) (m := m) (r := r))

omit [DecidableEq I] in
theorem blocksAssocWeight_tail : (β̂ₗ + δₗ).map cₑ = β̂ᵣ + γ̂ᵣ := by
  rw [Multiset.map_add, blocksAssocWeight_mid, blocksAssocWeight_last]

omit [DecidableEq I] in
theorem blocksAssocWeight : (α̂ + (β̂ₗ + δₗ)).map cₑ = αᵣ + (β̂ᵣ + γ̂ᵣ) := by
  rw [Multiset.map_add, blocksAssocWeight_head, blocksAssocWeight_tail]

/-- **The relabelling of the affine KLR algebra of all strands** from the alphabet
`Fin ((a + m) + r)` to `Fin (a + (m + r))`. -/
abbrev blocksAssocKLR : KLRAlgebra k Sₗ (α̂ + (β̂ₗ + δₗ)) ≃ₐ[k] KLRAlgebra k S (αᵣ + (β̂ᵣ + γ̂ᵣ)) :=
  blocksAssocRelabel Q Λ _ _ (blocksAssocWeight θ β γ)

/-- The relabelling of the affine KLR algebras of the three blocks. -/
abbrev blocksAssocTensor : TensorKLR3 Sₗ α̂ β̂ₗ δₗ ≃ₐ[k] TensorKLR3 S αᵣ β̂ᵣ γ̂ᵣ :=
  Algebra.TensorProduct.congr (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_head θ))
    (Algebra.TensorProduct.congr (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_mid β))
      (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_last γ)))

/-- The relabelling intertwines the inclusions `ι₃` of the three blocks. -/
theorem blocksAssocKLR_concat3 (t : TensorKLR3 Sₗ α̂ β̂ₗ δₗ) :
    blocksAssocKLR Q Λ θ β γ (concat3 Sₗ α̂ β̂ₗ δₗ t) =
      concat3 S αᵣ β̂ᵣ γ̂ᵣ (blocksAssocTensor Q Λ θ β γ t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul u v =>
    rw [concat3_tmul, blocksAssocRelabel_concat Q Λ (blocksAssocWeight_head θ)
      (blocksAssocWeight_tail β γ)]
    change concat S _ _ (_ ⊗ₜ blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_tail β γ)
      (concat Sₗ _ _ v)) = concat3 S αᵣ β̂ᵣ γ̂ᵣ (_ ⊗ₜ _)
    rw [blocksAssocRelabel_concat Q Λ (blocksAssocWeight_mid β) (blocksAssocWeight_last γ),
      concat3_tmul]
    rfl

/-! ### The affine input quotients of the two one-step models agree -/

private theorem nf {n₁ n₂ m' : ℕ} (Λ₂ : Fin n₂ → I →₀ ℕ) (g : Fin n₁ → Fin n₂)
    (hg : Function.Injective g) (f : Fin m' → Fin n₁) (hf : Function.Injective f)
    (ν : Multiset I)
    (y : KLRAlgebra k (stendhalQ Q Λ₂)
      (((stendhalWeight m' ν).map (Sum.map (id : I → I) f)).map (Sum.map (id : I → I) g))) :
    redSubfamilyProjection Q (Λ₂ ∘ g) f hf ν
      ((relabelEquiv (stendhalRelabel Q Λ₂ g hg _)).symm y) =
      redSubfamilyProjection Q Λ₂ (g ∘ f) (hg.comp hf) ν
        (castKLR (stendhalQ Q Λ₂) (map_sumMap_comp g f _).symm y) := by
  rw [redSubfamilyProjection_relabel Q g hg, AlgEquiv.apply_symm_apply]

/-- The affine input quotients of the first block agree. -/
theorem blocksAssoc_head (x : KLRAlgebra k Sₗ α̂) :
    tensorProductAlgebraCast Q
        (congrArg (Λ ∘ ·) (cast_castAdd_castAdd (a := a) (m := m) (r := r))) θ
      (cutPrefixProjection (a := a) (r := m) Q (blocksLeftLabels ΛL) θ
        ((relabelEquiv (stendhalRelabel Q ΛL (Fin.castAdd r) (Fin.castAdd_injective (a + m) r)
          _)).symm x)) =
      cutPrefixProjection (a := a) (r := m + r) Q Λ θ
        (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_head θ) x) := by
  rw [cutPrefixProjection, cutPrefixProjection, nf, redSubfamilyProjection_relabel Q ε
    (Fin.cast_injective _), redSubfamilyProjection_congr Q cast_castAdd_castAdd _
    (Fin.castAdd_injective _ _)]
  congr 1
  rw [stendhalRelabel_castKLR, castKLR_trans'', castKLR_trans'']
  rfl

/-- The affine input quotients of the middle block agree. -/
theorem blocksAssoc_mid (y : KLRAlgebra k Sₗ β̂ₗ) :
    tensorProductAlgebraCast Q
        (congrArg (Λ ∘ ·) (cast_castAdd_natAdd (a := a) (m := m) (r := r))) β
      (cutSuffixProjection (a := a) (r := m) Q (blocksLeftLabels ΛL) β
        ((relabelEquiv (stendhalRelabel Q ΛL (Fin.castAdd r) (Fin.castAdd_injective (a + m) r)
          _)).symm y)) =
      cutPrefixProjection (a := m) (r := r) Q (blocksTailLabels Λ) β
        ((relabelEquiv (stendhalRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
          _)).symm (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_mid β) y)) := by
  rw [cutSuffixProjection, cutPrefixProjection, nf, nf, redSubfamilyProjection_relabel Q ε
    (Fin.cast_injective _), redSubfamilyProjection_congr Q cast_castAdd_natAdd _
    ((Fin.natAdd_injective _ _).comp (Fin.castAdd_injective _ _))]
  congr 1
  rw [stendhalRelabel_castKLR, castKLR_trans'', castKLR_trans'']
  change _ = castKLR S _ (castKLR S _ _)
  rw [castKLR_trans'']
  rfl

/-- The affine input quotients of the last block agree. -/
theorem blocksAssoc_last (z : KLRAlgebra k Sₗ δₗ) :
    tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) (cast_natAdd (a := a) (m := m) (r := r))) γ
      (cutSuffixProjection (a := a + m) (r := r) Q ΛL γ z) =
      cutSuffixProjection (a := m) (r := r) Q (blocksTailLabels Λ) γ
        ((relabelEquiv (stendhalRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
          _)).symm (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_last γ) z)) := by
  rw [cutSuffixProjection, cutSuffixProjection, nf, redSubfamilyProjection_relabel Q ε
    (Fin.cast_injective _), redSubfamilyProjection_congr Q cast_natAdd _
    ((Fin.natAdd_injective _ _).comp (Fin.natAdd_injective _ _))]
  congr 1
  change _ = castKLR S _ (castKLR S _ _)
  rw [castKLR_trans'', castKLR_trans'']
  rfl

/-- **The affine input quotients of the two one-step models agree** along the relabelling of the
affine KLR algebras of the three blocks. -/
theorem blocksAssocFactorEquiv_oneStepMap (t : TensorKLR3 Sₗ α̂ β̂ₗ δₗ) :
    blocksAssocFactorEquiv Q Λ θ β γ (blocksOneStepMap3L Q ΛL θ β γ t) =
      blocksOneStepMap Q Λ θ β γ (blocksAssocTensor Q Λ θ β γ t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul x u =>
    induction u using TensorProduct.inductionOn with
    | add u u' hu hu' =>
      rw [TensorProduct.tmul_add, map_add, map_add, hu, hu', map_add, map_add]
    | tmul y z =>
      change blocksAssocFactorEquiv Q Λ θ β γ (blocksOneStepMapL Q ΛL θ β γ
          ((Algebra.TensorProduct.assoc k k k _ _ _).symm (x ⊗ₜ (y ⊗ₜ z)))) =
        blocksOneStepMap Q Λ θ β γ (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_head θ) x ⊗ₜ
          (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_mid β) y ⊗ₜ
            blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_last γ) z))
      rw [Algebra.TensorProduct.assoc_symm_tmul, blocksOneStepMapL_tmul, blocksOneStepMap_tmul]
      change blocksAssocFactorEquiv Q Λ θ β γ
          ((cutPrefixProjection (a := a) (r := m) Q (blocksLeftLabels ΛL) θ
            ((relabelEquiv (stendhalRelabel Q ΛL (Fin.castAdd r)
              (Fin.castAdd_injective (a + m) r) _)).symm x) ⊗ₜ
          cutSuffixProjection (a := a) (r := m) Q (blocksLeftLabels ΛL) β
            ((relabelEquiv (stendhalRelabel Q ΛL (Fin.castAdd r)
              (Fin.castAdd_injective (a + m) r) _)).symm y)) ⊗ₜ
          cutSuffixProjection (a := a + m) (r := r) Q ΛL γ z) =
        cutPrefixProjection (a := a) (r := m + r) Q Λ θ
            (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_head θ) x) ⊗ₜ
          (cutPrefixProjection (a := m) (r := r) Q (blocksTailLabels Λ) β
            ((relabelEquiv (stendhalRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
              _)).symm (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_mid β) y)) ⊗ₜ
          cutSuffixProjection (a := m) (r := r) Q (blocksTailLabels Λ) γ
            ((relabelEquiv (stendhalRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
              _)).symm (blocksAssocRelabel Q Λ _ _ (blocksAssocWeight_last γ) z)))
      rw [← blocksAssoc_head, ← blocksAssoc_mid, ← blocksAssoc_last]
      rfl

/-! ### The two one-step models agree -/

local notation "N₃ₗ" => BlocksOneStepInputL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N)
local notation "N₃" => BlocksOneStepInput Q Λ θ β γ N

/-- **The one-step inductions of the two nestings agree**, semilinearly along the relabelling of
the affine KLR algebra of all strands. -/
def blocksAssocInd3Equiv : Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ ≃ₗ[k] Ind3 S αᵣ β̂ᵣ γ̂ᵣ N₃ :=
  ind3Transport (blocksAssocKLR Q Λ θ β γ) (blocksAssocTensor Q Λ θ β γ)
    (blocksAssocKLR_concat3 Q Λ θ β γ) (LinearEquiv.refl k N) (fun t n => by
      change blocksAssocFactorEquiv Q Λ θ β γ (blocksOneStepMap3L Q ΛL θ β γ t) •
          (show N from n) =
        blocksOneStepMap Q Λ θ β γ (blocksAssocTensor Q Λ θ β γ t) • (show N from n)
      rw [blocksAssocFactorEquiv_oneStepMap])

omit [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksAssocInd3Equiv_smul (z : KLRAlgebra k Sₗ (α̂ + (β̂ₗ + δₗ)))
    (y : Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ) :
    blocksAssocInd3Equiv Q Λ θ β γ N (z • y) =
      blocksAssocKLR Q Λ θ β γ z • blocksAssocInd3Equiv Q Λ θ β γ N y :=
  ind3Transport_smul _ _ _ _ _ z y

omit [DecidableEq I] in
private theorem isRedOrdered_map_cast {μ : Multiset (I ⊕ Fin ((a + m) + r))} (s : Seq μ) :
    IsRedOrdered (Seq.map cₑ s) ↔ IsRedOrdered s := by
  constructor
  · intro hs p q u t hpq hp hq
    have hc := Multiset.card_map cₑ μ
    have h := hs (Fin.cast hc.symm p) (Fin.cast hc.symm q) (ε u) (ε t) hpq
      (by rw [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, hp]; rfl)
      (by rw [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, hq]; rfl)
    exact h
  · intro hs p q u t hpq hp hq
    rw [Seq.map_lbl] at hp hq
    rcases hsp : s.lbl (Fin.cast (Multiset.card_map cₑ μ) p) with i | u'
    · rw [hsp] at hp; cases hp
    rcases hsq : s.lbl (Fin.cast (Multiset.card_map cₑ μ) q) with j | t'
    · rw [hsq] at hq; cases hq
    rw [hsp, Sum.map_inr, Sum.inr.injEq] at hp
    rw [hsq, Sum.map_inr, Sum.inr.injEq] at hq
    subst hp hq
    exact hs _ _ u' t' hpq hsp hsq

omit [DecidableEq I] in
private theorem isRedOrdered_seq_cast {μ μ' : Multiset (I ⊕ Fin (a + (m + r)))} (h : μ = μ')
    (s : Seq μ) : IsRedOrdered (Seq.cast h s) ↔ IsRedOrdered s := by
  subst h; rfl

/-- The relabelling carries the red-ordered loadings to the red-ordered loadings. -/
theorem blocksAssocKLR_eSum :
    blocksAssocKLR Q Λ θ β γ
        (eSum Sₗ (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ)) =
      eSum S (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ) := by
  classical
  let E : Seq (α̂ + (β̂ₗ + δₗ)) ≃ Seq (αᵣ + (β̂ᵣ + γ̂ᵣ)) :=
    (Seq.mapEquiv (sumMap_injective _ (Fin.cast_injective (Nat.add_assoc a m r))) _).trans
      { toFun := Seq.cast (blocksAssocWeight θ β γ)
        invFun := Seq.cast (blocksAssocWeight θ β γ).symm
        left_inv := fun s => Subtype.ext (funext fun _ => Seq.apply_congr s (by simp))
        right_inv := fun s => Subtype.ext (funext fun _ => Seq.apply_congr s (by simp)) }
  rw [eSum, eSum, map_sum]
  refine Finset.sum_equiv E (fun s => ?_) (fun s _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change IsRedOrdered s ↔ IsRedOrdered (Seq.cast (blocksAssocWeight θ β γ) (Seq.map cₑ s))
    rw [isRedOrdered_seq_cast, isRedOrdered_map_cast]
  · change castKLR S _ (relabelEquiv (stendhalRelabel Q Λ ε _ _) (e s)) = _
    rw [relabelEquiv_apply, relabelHom_e, castKLR_e]
    rfl

omit [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem map_excludedSpace_blocksAssocInd3Equiv :
    (excludedSpace (Algebra.lsmul k k (Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ) :
        KLRAlgebra k Sₗ (α̂ + (β̂ₗ + δₗ)) →ₐ[k] Module.End k (Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ))
      (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ)).map
        (blocksAssocInd3Equiv Q Λ θ β γ N : Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ →ₗ[k] Ind3 S αᵣ β̂ᵣ γ̂ᵣ N₃) =
      excludedSpace (Algebra.lsmul k k (Ind3 S αᵣ β̂ᵣ γ̂ᵣ N₃) :
        KLRAlgebra k S (αᵣ + (β̂ᵣ + γ̂ᵣ)) →ₐ[k] Module.End k (Ind3 S αᵣ β̂ᵣ γ̂ᵣ N₃))
        (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ) := by
  ext v
  obtain ⟨y, rfl⟩ := (blocksAssocInd3Equiv Q Λ θ β γ N).surjective v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  change (eSum Sₗ (blocksOneStepOrderedL (a := a) (m := m) (r := r) θ β γ) :
      KLRAlgebra k Sₗ (α̂ + (β̂ₗ + δₗ))) • y = 0 ↔
    (eSum S (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ) :
      KLRAlgebra k S (αᵣ + (β̂ᵣ + γ̂ᵣ))) • blocksAssocInd3Equiv Q Λ θ β γ N y = 0
  rw [← blocksAssocKLR_eSum, ← blocksAssocInd3Equiv_smul, LinearEquiv.map_eq_zero_iff]

/-- **The one-step partial standardizations of the two nestings agree.** -/
def blocksOneStepQuotAssocEquiv :
    BlocksOneStepQuotL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) ≃ₗ[k]
      BlocksOneStepQuot Q Λ θ β γ N :=
  Submodule.Quotient.equiv _ _ (blocksAssocInd3Equiv Q Λ θ β γ N)
    (map_excludedSpace_blocksAssocInd3Equiv Q Λ θ β γ N)

omit [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
theorem blocksOneStepQuotAssocEquiv_mk (y : Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ) :
    blocksOneStepQuotAssocEquiv Q Λ θ β γ N (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (blocksAssocInd3Equiv Q Λ θ β γ N y) := by
  rw [blocksOneStepQuotAssocEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

variable (hQ : KLRSymm Q)

/-- **Iterated partial standardization with three blocks does not depend on the order of the
cuts**: standardizing first at the cut between the first two blocks gives the same module as
standardizing first at the cut between the last two blocks. -/
def blocksStandardAssocEquiv :
    BlocksStandardL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ ≃ₗ[k]
      BlocksStandard Q Λ θ β γ N hQ :=
  ((blocksStandardOneStepEquivL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ).trans
    (blocksOneStepQuotAssocEquiv Q Λ θ β γ N)).trans
      (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm

theorem blocksStandardOneStepEquiv_assocEquiv
    (x : BlocksStandardL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ) :
    blocksStandardOneStepEquiv Q Λ θ β γ N hQ (blocksStandardAssocEquiv Q Λ θ β γ N hQ x) =
      blocksOneStepQuotAssocEquiv Q Λ θ β γ N
        (blocksStandardOneStepEquivL Q ΛL θ β γ (BlocksAssocInput Q Λ θ β γ N) hQ x) := by
  exact (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).apply_symm_apply _

omit [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] in
/-- **The identification of the one-step models is compatible with the affine actions of all
strands**, along the relabelling `blocksAssocKLR` of the affine KLR algebra of all strands. -/
theorem blocksOneStepQuotAssocEquiv_mk_smul (z : KLRAlgebra k Sₗ (α̂ + (β̂ₗ + δₗ)))
    (y : Ind3 Sₗ α̂ β̂ₗ δₗ N₃ₗ) :
    blocksOneStepQuotAssocEquiv Q Λ θ β γ N (Submodule.Quotient.mk (z • y)) =
      Submodule.Quotient.mk
        (blocksAssocKLR Q Λ θ β γ z • blocksAssocInd3Equiv Q Λ θ β γ N y) :=
  (blocksOneStepQuotAssocEquiv_mk Q Λ θ β γ N _).trans
    (congrArg Submodule.Quotient.mk (blocksAssocInd3Equiv_smul Q Λ θ β γ N z y))

end Categorification.Stendhal
