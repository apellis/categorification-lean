/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocBlocksLeft
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocCutInner

/-!
# The first quotient of an iterated partial standardization can be taken last

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardizations with several blocks (after Definition 5.4), in the order of cuts of
`PartialStandardizationAssocBlocksLeft`: `BlocksStandardL` first standardizes at the cut between
the first two blocks and then at the cut before the last block. As in
`PartialStandardizationAssocCutInner` for the other order, the first standardization is
replaced by the affine induced module `Y` of the first two blocks, on which the outer affine
algebras act (`blocksShuffleActionL`), and the outer affine induction of `Y` modulo the part
supported on unordered loadings of all strands is the iterated standardization
(`blocksStandardEquivL`), compatibly with the affine action (`blocksStandardEquivL_smul`).

## Main definitions

* `Stendhal.blocksShuffleHeadL`, `Stendhal.blocksShuffleLast`: the actions of the affine algebra
  of the first two blocks and of the last block on `Y`.
* `Stendhal.BlocksShuffleInputL`: `Y` as a module over the outer affine algebras.
* `Stendhal.BlocksShuffleQuotL`: the outer affine induction of `Y` modulo the unordered part.

## Main results

* `Stendhal.eSum_redOrdered_smul_mapRight_eq_zero_of_left`: the induced excluded part is
  excluded, for a part killed by the idempotents whose first block is red-ordered.
* `Stendhal.blocksStandardEquivL`: `BlocksShuffleQuotL ≃ BlocksStandardL`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-! ### Excluded parts killed by the idempotents with red-ordered first block -/

section Excl

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {ν ν' : Multiset (I ⊕ Fin ℓ)}
  {S : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} (hS : KLRSymm S)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (TensorKLR S ν ν') M]
  [IsScalarTower k (TensorKLR S ν ν') M]

include hS in
/-- **The induced excluded part is excluded**: if `K ⊆ M` is killed by `e(a) ⊗ e(b)` whenever
`a` is red-ordered, then the image of `Ind K` in `Ind M` is killed by the red-ordered
loadings. -/
theorem eSum_redOrdered_smul_mapRight_eq_zero_of_left (K : Submodule (TensorKLR S ν ν') M)
    (hK : ∀ n ∈ K, ∀ (a : Seq ν) (b : Seq ν'), IsRedOrdered a →
      (e a ⊗ₜ e b : TensorKLR S ν ν') • n = 0)
    (z : Ind S ν ν' K) :
    (redOrderedSum : KLRAlgebra k S (ν + ν')) •
      BalancedTensor.mapRight (k := k) (B := KLRAlgebra k S (ν + ν')) K.subtype z = 0 := by
  classical
  rw [← LinearMap.map_smul]
  let σ : Shuffle (Seq.card_add' ν ν') → List ℕ := fun u => canWord _ u.1
  have hσ : ∀ u, IsReduced (ν + ν').card (σ u) ∧ wordProd (ν + ν').card (σ u) = u.1 :=
    fun u => ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  induction z using indShuffle_induction hS K σ hσ with
  | hz => rw [smul_zero, map_zero]
  | ha x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]
  | ht u n =>
    rw [← mul_smul, redOrderedSum, eSum, Finset.sum_mul, Finset.sum_smul, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hso : IsRedOrdered s := (Finset.mem_filter.1 hs).2
    rw [e_mul_ψw, mul_smul, idem_smul_indShuffleUnit, wordProd_reverse, inv_inv, (hσ u).2,
      LinearMap.map_smul]
    have hzero : concatIdem (Q := S) (u.1 • s) • n = 0 := by
      by_cases hc : u.1 • s ∈ concatSet ν ν'
      · obtain ⟨a, b, hab⟩ := mem_concatSet.1 hc
        rw [← hab, concatIdem_append]
        exact Subtype.ext (hK n n.2 a b (isRedOrdered_left_of_shuffle hso u hab.symm))
      · rw [concatIdem_of_not_mem hc, zero_smul]
    rw [hzero]
    change _ • BalancedTensor.tmul _ ((K.subtype) 0) = 0
    rw [map_zero, BalancedTensor.tmul_zero, smul_zero]

end Excl

/-! ### The outer affine algebras acting on the affine induced module of the first two blocks -/

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ((a + m) + r) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebraL Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebraL Q Λ θ β γ) N]

local notation "A₀" => blocksLastAlgebra Q Λ γ
local notation "Dᵢ" => cutFactorAlgebra Q (blocksLeftLabels Λ) θ β
local notation "Y" => CutShuffle Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)
local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight (a + m) (θ + β))
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd (a + m))) (stendhalWeight r γ)
local notation "S" => stendhalQ Q Λ
local notation "Sᵢ" => stendhalQ Q (blocksLeftLabels Λ)

/-- **The action of the last block on the affine induced module of the first two blocks**, by
functoriality. -/
def blocksShuffleLast : A₀ →ₐ[k] Module.End k Y where
  __ := (cutShuffleEnd Q (blocksLeftLabels Λ) θ β).comp (blocksLastRingHom Q Λ θ β γ N)
  commutes' c := by
    change cutShuffleEnd Q (blocksLeftLabels Λ) θ β (blocksLastEnd Q Λ θ β γ N _) = _
    have h : blocksLastEnd Q Λ θ β γ N (algebraMap k A₀ c) =
        c • (LinearMap.id : Module.End Dᵢ (BlocksInnerL Q Λ θ β γ N)) :=
      LinearMap.ext fun n => by
        change ((1 : Dᵢ) ⊗ₜ[k] (algebraMap k A₀ c) : blocksFactorAlgebraL Q Λ θ β γ) •
          (n : N) = c • (n : N)
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, smul_assoc]
        exact congrArg (c • ·) (one_smul (blocksFactorAlgebraL Q Λ θ β γ) (show N from n))
    rw [h, cutShuffleEnd_smul_id]
    rfl

theorem blocksShuffleLast_apply (t : A₀) (y : Y) :
    blocksShuffleLast Q Λ θ β γ N t y =
      cutShuffleMap Q (blocksLeftLabels Λ) θ β (blocksLastEnd Q Λ θ β γ N t) y := rfl

/-- The relabelling of the affine algebra of the first two blocks into the alphabet of all red
strands. -/
abbrev blocksHeadRelabelL :=
  redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective (a + m) r) (θ + β)

/-- The outer affine algebra of the first two blocks, as the inner affine algebra. -/
def blocksHeadMapL : KLRAlgebra k S α →ₐ[k] KLRAlgebra k Sᵢ
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd m)) (stendhalWeight a θ) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight m β)) :=
  (castKLR Sᵢ (cutInputWeights_add (a := a) (r := m) θ β).symm).toAlgHom.comp
    (relabelEquiv (blocksHeadRelabelL Q Λ θ β)).symm.toAlgHom

/-- **The action of the outer affine algebra of the first two blocks on their affine induced
module.** -/
def blocksShuffleHeadL : KLRAlgebra k S α →ₐ[k] Module.End k Y :=
  (cutShuffleAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)).comp
    (blocksHeadMapL Q Λ θ β)

theorem commute_blocksShuffleLast (z : KLRAlgebra k S α) (t : A₀) :
    Commute (blocksShuffleHeadL Q Λ θ β γ N z) (blocksShuffleLast Q Λ θ β γ N t) :=
  LinearMap.ext fun y => by
    change blocksHeadMapL Q Λ θ β z • cutShuffleMap Q (blocksLeftLabels Λ) θ β _ y =
      cutShuffleMap Q (blocksLeftLabels Λ) θ β _ (blocksHeadMapL Q Λ θ β z • y)
    exact (LinearMap.map_smul _ _ _).symm

/-- The action of both outer affine algebras on the affine induced module of the first two
blocks. -/
def blocksShuffleActionL : TensorKLR S α δ →ₐ[k] Module.End k Y :=
  Algebra.TensorProduct.lift (blocksShuffleHeadL Q Λ θ β γ N)
    ((blocksShuffleLast Q Λ θ β γ N).comp (cutSuffixProjection (a := a + m) (r := r) Q Λ γ))
    (fun z _ => commute_blocksShuffleLast Q Λ θ β γ N z _)

/-- The affine induced module of the first two blocks, as a module over the outer affine
algebras. -/
@[nolint unusedArguments]
def BlocksShuffleInputL (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin ((a + m) + r) → I →₀ ℕ) (_θ _β _γ : Multiset I) (N : Type*) [AddCommGroup N]
    [Module k N] [Module (blocksFactorAlgebraL _Q _Λ _θ _β _γ) N] : Type _ :=
  CutShuffle _Q (blocksLeftLabels _Λ) _θ _β (BlocksInnerL _Q _Λ _θ _β _γ N)

local notation "Yₒ" => BlocksShuffleInputL Q Λ θ β γ N

instance : AddCommGroup Yₒ := inferInstanceAs (AddCommGroup Y)
instance : Module k Yₒ := inferInstanceAs (Module k Y)
instance : Module (TensorKLR S α δ) Yₒ :=
  Module.compHom Y (blocksShuffleActionL Q Λ θ β γ N).toRingHom

theorem blocksShuffleInputL_smul (t : TensorKLR S α δ) (y : Yₒ) :
    t • y = blocksShuffleActionL Q Λ θ β γ N t (show Y from y) := rfl

instance : IsScalarTower k (TensorKLR S α δ) Yₒ where
  smul_assoc c t y := by
    rw [blocksShuffleInputL_smul, blocksShuffleInputL_smul, map_smul]
    rfl

/-! ### The first standardization as a quotient of `Y` over the outer affine algebras -/

variable (hQ : KLRSymm Q)

local notation "Mid" => CutInput Q Λ (θ + β) γ (BlocksMidL Q Λ θ β γ N hQ)
local notation "πᵢ" => Submodule.mkQ (excludedSpace
  (cutShuffleAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N))
  (cutOrderedLoadings (a := a) (r := m) θ β))

/-- The outer affine algebra of the first two blocks acts on the first standardization through
its action on `Y`. -/
theorem cutStandardAction_prefix_mk (z : KLRAlgebra k S α) (y : Y) :
    cutStandardAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) hQ
      (cutPrefixProjection (a := a + m) (r := r) Q Λ (θ + β) z) (πᵢ y) =
      πᵢ (blocksShuffleHeadL Q Λ θ β γ N z y) := by
  have h := cutStandardAction_affine Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N) hQ
    (blocksHeadMapL Q Λ θ β z)
  have hz : castKLR Sᵢ (cutInputWeights_add (a := a) (r := m) θ β)
      (blocksHeadMapL Q Λ θ β z) = (relabelEquiv (blocksHeadRelabelL Q Λ θ β)).symm z :=
    castKLR_castAlg_symm _ _
  rw [hz] at h
  exact LinearMap.congr_fun h (πᵢ y)

/-- The quotient map from `Y` to the first standardization, `k`-linearly. -/
def blocksShuffleQuotientKL : Yₒ →ₗ[k] Mid := πᵢ

private theorem blocksShuffleQuotientKL_smul (t : TensorKLR S α δ) (y : Yₒ) :
    blocksShuffleQuotientKL Q Λ θ β γ N hQ (t • y) =
      t • blocksShuffleQuotientKL Q Λ θ β γ N hQ y := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', add_smul]
  | tmul t z =>
    rw [blocksShuffleInputL_smul]
    change πᵢ (blocksShuffleHeadL Q Λ θ β γ N t
        (blocksShuffleLast Q Λ θ β γ N (cutSuffixProjection (a := a + m) (r := r) Q Λ γ z)
          (show Y from y))) =
      blocksMidActionL Q Λ θ β γ N hQ (cutPrefixProjection (a := a + m) (r := r) Q Λ (θ + β) t
        ⊗ₜ[k] cutSuffixProjection (a := a + m) (r := r) Q Λ γ z) (πᵢ (show Y from y))
    rw [blocksMidActionL, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
    exact (cutStandardAction_prefix_mk Q Λ θ β γ N hQ t _).symm

/-- **The quotient map from `Y` to the first standardization**, linear over the outer affine
algebras. -/
def blocksShuffleQuotientL : Yₒ →ₗ[TensorKLR S α δ] Mid where
  toFun := blocksShuffleQuotientKL Q Λ θ β γ N hQ
  map_add' := map_add _
  map_smul' := blocksShuffleQuotientKL_smul Q Λ θ β γ N hQ

theorem blocksShuffleQuotientL_apply (y : Yₒ) :
    blocksShuffleQuotientL Q Λ θ β γ N hQ y = πᵢ (show Y from y) := rfl

theorem blocksShuffleQuotientL_surjective :
    Function.Surjective (blocksShuffleQuotientL Q Λ θ β γ N hQ) := by
  intro z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (excludedSpace
    (cutShuffleAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N))
    (cutOrderedLoadings (a := a) (r := m) θ β)) (show BlocksMidL Q Λ θ β γ N hQ from z)
  exact ⟨y, hy⟩

/-- The part of `Y` supported on unordered loadings of the first two blocks, a submodule over
the outer affine algebras. -/
abbrev blocksShuffleExcludedL : Submodule (TensorKLR S α δ) Yₒ :=
  LinearMap.ker (blocksShuffleQuotientL Q Λ θ β γ N hQ)

theorem mem_blocksShuffleExcludedL {y : Yₒ} :
    y ∈ blocksShuffleExcludedL Q Λ θ β γ N hQ ↔
      cutShuffleAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)
        (eSum Sᵢ (cutOrderedLoadings (a := a) (r := m) θ β)) (show Y from y) = 0 := by
  rw [LinearMap.mem_ker]
  exact (Submodule.Quotient.mk_eq_zero _).trans LinearMap.mem_ker

omit [DecidableEq I] in
private theorem isRedOrdered_of_map {n n' : ℕ} {f : Fin n → Fin n'} (hf : StrictMono f)
    {μ : Multiset (I ⊕ Fin n)} (s : Seq μ)
    (hs : IsRedOrdered (Seq.map (Sum.map (id : I → I) f) s)) : IsRedOrdered s := by
  intro p q u t hpq hp hq
  have hc := Multiset.card_map (Sum.map (id : I → I) f) μ
  refine hf.lt_iff_lt.1 (hs (Fin.cast hc.symm p) (Fin.cast hc.symm q) (f u) (f t) hpq ?_ ?_)
  · rw [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, hp]; rfl
  · rw [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, hq]; rfl

omit [DecidableEq I] in
private theorem isRedOrdered_seqCast {n : ℕ} {μ μ' : Multiset (I ⊕ Fin n)} (h : μ = μ')
    (s : Seq μ) (hs : IsRedOrdered s) : IsRedOrdered (Seq.cast h s) := by
  intro p q u t hpq hp hq
  exact hs _ _ u t hpq hp hq

/-- The outer affine idempotent of a red-ordered loading of the first two blocks is a
red-ordered inner idempotent. -/
theorem blocksHeadMapL_e (b : Seq α) (hb : IsRedOrdered b) :
    ∃ c, IsRedOrdered c ∧ blocksHeadMapL Q Λ θ β (e b) = e c := by
  let s := (blocksHeadRelabelL Q Λ θ β).equiv.symm b
  have hs : Seq.map (Sum.map (id : I → I) (Fin.castAdd r)) s = b :=
    Seq.map_mapEquiv_symm (Sum.map_injective.mpr ⟨Function.injective_id,
      Fin.castAdd_injective (a + m) r⟩) b
  refine ⟨Seq.cast (cutInputWeights_add (a := a) (r := m) θ β).symm s,
    isRedOrdered_seqCast _ _ (isRedOrdered_of_map (Fin.strictMono_castAdd r) s
      (hs ▸ hb)), ?_⟩
  change castKLR Sᵢ _ ((relabelEquiv (blocksHeadRelabelL Q Λ θ β)).symm (e b)) = _
  rw [relabelEquiv_symm_apply, relabelHom_e, castKLR_e]
  rfl

/-- **The part of `Y` supported on unordered loadings of the first two blocks is killed by
every red-ordered loading of the first two blocks.** -/
theorem blocksShuffleExcludedL_e (y : Yₒ) (hy : y ∈ blocksShuffleExcludedL Q Λ θ β γ N hQ)
    (a' : Seq α) (b : Seq δ) (ha : IsRedOrdered a') :
    (e a' ⊗ₜ[k] e b : TensorKLR S α δ) • y = 0 := by
  classical
  obtain ⟨c, hc, he⟩ := blocksHeadMapL_e Q Λ θ β a' ha
  rw [blocksShuffleInputL_smul]
  change blocksShuffleHeadL Q Λ θ β γ N (e a')
    (blocksShuffleLast Q Λ θ β γ N (cutSuffixProjection (a := a + m) (r := r) Q Λ γ (e b))
      (show Y from y)) = 0
  rw [← Module.End.mul_apply, (commute_blocksShuffleLast Q Λ θ β γ N _ _).eq,
    Module.End.mul_apply]
  change blocksShuffleLast Q Λ θ β γ N _
    (cutShuffleAction Q (blocksLeftLabels Λ) θ β (BlocksInnerL Q Λ θ β γ N)
      (blocksHeadMapL Q Λ θ β (e a')) (show Y from y)) = 0
  have hcP : (e c * eSum Sᵢ (cutOrderedLoadings (a := a) (r := m) θ β) :
      KLRAlgebra k Sᵢ _) = e c := by
    simp [e_mul_eSum, cutOrderedLoadings, hc]
  rw [he, ← hcP, map_mul, Module.End.mul_apply,
    (mem_blocksShuffleExcludedL Q Λ θ β γ N hQ).1 hy, map_zero, map_zero]

/-! ### The iterated standardization as one quotient of the outer induction of `Y` -/

local notation "W" => Ind S α δ (BlocksShuffleInputL Q Λ θ β γ N)
local notation "Vₒ" => CutShuffle Q Λ (θ + β) γ (BlocksMidL Q Λ θ β γ N hQ)
local notation "Fₒ" => cutOrderedLoadings (a := a + m) (r := r) (θ + β) γ

/-- The outer affine induction of the quotient map `Y → 𝕊_first`. -/
def blocksShuffleIndL : W →ₗ[KLRAlgebra k S (α + δ)] Vₒ :=
  BalancedTensor.mapRight (blocksShuffleQuotientL Q Λ θ β γ N hQ)

theorem blocksShuffleIndL_surjective :
    Function.Surjective (blocksShuffleIndL Q Λ θ β γ N hQ) :=
  indMapRight_surjective (cutStendhalQ_symm Q Λ hQ) _
    (blocksShuffleQuotientL_surjective Q Λ θ β γ N hQ)

/-- **The outer affine induction of `Y` modulo the part supported on unordered loadings of all
strands.** -/
abbrev BlocksShuffleQuotL : Type _ :=
  W ⧸ excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W) Fₒ

/-- The map from the outer induction of `Y` to the iterated standardization. -/
def blocksStandardOfShuffleL : W →ₗ[k] BlocksStandardL Q Λ θ β γ N hQ :=
  (excludedSpace (cutShuffleAction Q Λ (θ + β) γ (BlocksMidL Q Λ θ β γ N hQ)) Fₒ).mkQ ∘ₗ
    (blocksShuffleIndL Q Λ θ β γ N hQ).restrictScalars k

theorem blocksStandardOfShuffleL_surjective :
    Function.Surjective (blocksStandardOfShuffleL Q Λ θ β γ N hQ) :=
  (Submodule.mkQ_surjective _).comp (blocksShuffleIndL_surjective Q Λ θ β γ N hQ)

/-- **The kernel of the map to the iterated standardization** is the part of the outer
induction of `Y` supported on unordered loadings of all strands. -/
theorem blocksStandardOfShuffleL_eq_zero_iff (w : W) :
    blocksStandardOfShuffleL Q Λ θ β γ N hQ w = 0 ↔
      (eSum S Fₒ : KLRAlgebra k S (α + δ)) • w = 0 := by
  classical
  have hΦ : blocksStandardOfShuffleL Q Λ θ β γ N hQ w = 0 ↔
      blocksShuffleIndL Q Λ θ β γ N hQ ((eSum S Fₒ : KLRAlgebra k S (α + δ)) • w) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).trans (LinearMap.mem_ker.trans ?_)
    exact (iff_of_eq (congrArg (· = 0) ((blocksShuffleIndL Q Λ θ β γ N hQ).map_smul _ w).symm))
  rw [hΦ]
  constructor
  · intro h
    have hex := indMapRight_exact (cutStendhalQ_symm Q Λ hQ)
      (blocksShuffleExcludedL Q Λ θ β γ N hQ).subtype (blocksShuffleQuotientL Q Λ θ β γ N hQ)
      (LinearMap.exact_subtype_ker_map _)
    obtain ⟨z, hz⟩ := (hex _).1 h
    have h0 := eSum_redOrdered_smul_mapRight_eq_zero_of_left (cutStendhalQ_symm Q Λ hQ)
      (blocksShuffleExcludedL Q Λ θ β γ N hQ)
      (fun n hn a' b ha => blocksShuffleExcludedL_e Q Λ θ β γ N hQ n hn a' b ha) z
    rw [hz, ← mul_smul] at h0
    rw [← (eSum_idem (Q := S) Fₒ).eq]
    exact h0
  · intro h
    rw [h, map_zero]

theorem ker_blocksStandardOfShuffleL :
    LinearMap.ker (blocksStandardOfShuffleL Q Λ θ β γ N hQ) =
      excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W)
        Fₒ := by
  ext w
  exact LinearMap.mem_ker.trans (blocksStandardOfShuffleL_eq_zero_iff Q Λ θ β γ N hQ w)

/-- **The iterated standardization, first cut first, is the outer induction of the affine
induced module of the first two blocks modulo the part supported on unordered loadings of all
strands**: the first quotient can be taken last. -/
def blocksStandardEquivL :
    BlocksShuffleQuotL Q Λ θ β γ N ≃ₗ[k] BlocksStandardL Q Λ θ β γ N hQ :=
  (Submodule.quotEquivOfEq _ _ (ker_blocksStandardOfShuffleL Q Λ θ β γ N hQ).symm).trans
    ((blocksStandardOfShuffleL Q Λ θ β γ N hQ).quotKerEquivOfSurjective
      (blocksStandardOfShuffleL_surjective Q Λ θ β γ N hQ))

theorem blocksStandardEquivL_mk (w : W) :
    blocksStandardEquivL Q Λ θ β γ N hQ (Submodule.Quotient.mk w) =
      blocksStandardOfShuffleL Q Λ θ β γ N hQ w := rfl

/-- The identification is compatible with the affine action of all strands, which acts on the
iterated standardization through `T^λ((θ + β) + γ)`. -/
theorem blocksStandardEquivL_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksStandardEquivL Q Λ θ β γ N hQ (Submodule.Quotient.mk (z • w)) =
      blocksStandardActionL Q Λ θ β γ N hQ (TensorProductAlgebra.mk Q Λ ((θ + β) + γ)
        (orderProjection Q Λ ((θ + β) + γ) (StendhalAlgebraAllOrders.ofKLR k Q Λ ((θ + β) + γ)
          (castKLR S (cutInputWeights_add (a := a + m) (r := r) (θ + β) γ) z))))
        (blocksStandardEquivL Q Λ θ β γ N hQ (Submodule.Quotient.mk w)) := by
  rw [blocksStandardEquivL_mk, blocksStandardEquivL_mk, blocksStandardActionL,
    cutStandardAction_affine]
  change Submodule.Quotient.mk (blocksShuffleIndL Q Λ θ β γ N hQ (z • w)) =
    Submodule.Quotient.mk (z • blocksShuffleIndL Q Λ θ β γ N hQ w)
  rw [LinearMap.map_smul]

end Categorification.Stendhal
