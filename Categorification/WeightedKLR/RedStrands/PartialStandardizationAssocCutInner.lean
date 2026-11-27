/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocExcl
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksExact

/-!
# The inner quotient of an iterated partial standardization can be taken last

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardizations with several blocks (after Definition 5.4). For three consecutive
blocks the partial standardization `BlocksStandard` first standardizes at the inner cut and
then at the outer cut. Here the inner standardization is replaced by the inner affine induced
module `Y` (before excluding unordered loadings of the last two blocks), on which the outer
affine algebras of the two outer blocks act (`blocksShuffleInput`). The outer affine induction
of `Y` modulo the part supported on unordered loadings of all strands is isomorphic to the
iterated standardization (`blocksStandardEquiv`), compatibly with the affine action
(`blocksStandardEquiv_smul`).

## Main definitions

* `Stendhal.cutShuffleEnd`: affine induction at a cut on endomorphisms, a ring map.
* `Stendhal.blocksShuffleHead`, `Stendhal.blocksShuffleTail`: the actions of the first block
  and of the affine algebra of the last two blocks on `Y`.
* `Stendhal.BlocksShuffleInput`: `Y` as a module over the outer affine algebras.
* `Stendhal.BlocksShuffleQuot`: the outer affine induction of `Y` modulo the unordered part.

## Main results

* `Stendhal.blocksStandardEquiv`: `BlocksShuffleQuot ≃ BlocksStandard`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-! ### Affine induction at a cut on endomorphisms -/

section Functorial

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

/-- **Affine induction at a cut on endomorphisms**, the ring map
`End_D(N) → End_k(Ind N)`. -/
def cutShuffleEnd :
    Module.End (cutFactorAlgebra Q Λ θ β) N →+* Module.End k (CutShuffle Q Λ θ β N) where
  toFun g := (cutShuffleMap Q Λ θ β g).restrictScalars k
  map_one' := BalancedTensor.ext fun _ _ => rfl
  map_mul' _ _ := BalancedTensor.ext fun _ _ => rfl
  map_zero' := BalancedTensor.ext fun _ _ => BalancedTensor.tmul_zero _
  map_add' _ _ := BalancedTensor.ext fun _ _ => BalancedTensor.tmul_add _ _ _

theorem cutShuffleEnd_apply (g : Module.End (cutFactorAlgebra Q Λ θ β) N)
    (y : CutShuffle Q Λ θ β N) : cutShuffleEnd Q Λ θ β g y = cutShuffleMap Q Λ θ β g y := rfl

theorem cutShuffleEnd_smul_id (c : k) :
    cutShuffleEnd Q Λ θ β (c • (LinearMap.id : Module.End (cutFactorAlgebra Q Λ θ β) N)) =
      c • (LinearMap.id : Module.End k (CutShuffle Q Λ θ β N)) :=
  BalancedTensor.ext fun _ _ => BalancedTensor.tmul_smul _ _ _

end Functorial

/-! ### The outer affine algebras acting on the inner affine induced module -/

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]

local notation "A₀" => blocksHeadAlgebra Q Λ θ
local notation "Nᵢ" => BlocksInner Q Λ θ β γ N
local notation "Y" => CutShuffle Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ))
local notation "S" => stendhalQ Q Λ
local notation "Sᵢ" => stendhalQ Q (blocksTailLabels Λ)

/-- **The action of the first block on the inner affine induced module**, by functoriality. -/
def blocksShuffleHead : A₀ →ₐ[k] Module.End k Y where
  __ := (cutShuffleEnd Q (blocksTailLabels Λ) β γ).comp (blocksHeadRingHom Q Λ θ β γ N)
  commutes' c := by
    change cutShuffleEnd Q (blocksTailLabels Λ) β γ (blocksHeadEnd Q Λ θ β γ N _) = _
    have h : blocksHeadEnd Q Λ θ β γ N (algebraMap k A₀ c) =
        c • (LinearMap.id : Module.End (cutFactorAlgebra Q (blocksTailLabels Λ) β γ)
          (BlocksInner Q Λ θ β γ N)) := LinearMap.ext fun n => by
      change ((algebraMap k A₀ c) ⊗ₜ[k] (1 : cutFactorAlgebra Q (blocksTailLabels Λ) β γ) :
        blocksFactorAlgebra Q Λ θ β γ) • (n : N) = c • (n : N)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', smul_assoc]
      exact congrArg (c • ·) (one_smul (blocksFactorAlgebra Q Λ θ β γ) (show N from n))
    rw [h, cutShuffleEnd_smul_id]
    rfl

theorem blocksShuffleHead_apply (t : A₀) (y : Y) :
    blocksShuffleHead Q Λ θ β γ N t y =
      cutShuffleMap Q (blocksTailLabels Λ) β γ (blocksHeadEnd Q Λ θ β γ N t) y := rfl

/-- The relabelling of the affine algebra of the last two blocks into the alphabet of all red
strands. -/
abbrev blocksTailRelabel :=
  redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a) (β + γ)

/-- The outer affine algebra of the last two blocks, as the inner affine algebra. -/
def blocksTailMap : KLRAlgebra k S δ →ₐ[k] KLRAlgebra k Sᵢ
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β) +
      Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)) :=
  (castKLR Sᵢ (cutInputWeights_add (a := m) (r := r) β γ).symm).toAlgHom.comp
    (relabelEquiv (blocksTailRelabel Q Λ β γ)).symm.toAlgHom

/-- **The action of the outer affine algebra of the last two blocks on the inner affine
induced module.** -/
def blocksShuffleTail : KLRAlgebra k S δ →ₐ[k] Module.End k Y :=
  (cutShuffleAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)).comp
    (blocksTailMap Q Λ β γ)

theorem commute_blocksShuffleHead (t : A₀) (z : KLRAlgebra k S δ) :
    Commute (blocksShuffleHead Q Λ θ β γ N t) (blocksShuffleTail Q Λ θ β γ N z) :=
  LinearMap.ext fun y => by
    change cutShuffleMap Q (blocksTailLabels Λ) β γ _ (blocksTailMap Q Λ β γ z • y) =
      blocksTailMap Q Λ β γ z • cutShuffleMap Q (blocksTailLabels Λ) β γ _ y
    exact LinearMap.map_smul _ _ _

/-- The action of both outer affine algebras on the inner affine induced module. -/
def blocksShuffleAction : TensorKLR S α δ →ₐ[k] Module.End k Y :=
  Algebra.TensorProduct.lift
    ((blocksShuffleHead Q Λ θ β γ N).comp (cutPrefixProjection Q Λ θ))
    (blocksShuffleTail Q Λ θ β γ N)
    (fun _ z => commute_blocksShuffleHead Q Λ θ β γ N _ z)

/-- The inner affine induced module, as a module over the outer affine algebras. -/
@[nolint unusedArguments]
def BlocksShuffleInput (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin (a + (m + r)) → I →₀ ℕ) (_θ _β _γ : Multiset I) (N : Type*) [AddCommGroup N]
    [Module k N] [Module (blocksFactorAlgebra _Q _Λ _θ _β _γ) N] : Type _ :=
  CutShuffle _Q (blocksTailLabels _Λ) _β _γ (BlocksInner _Q _Λ _θ _β _γ N)

local notation "Yₒ" => BlocksShuffleInput Q Λ θ β γ N

instance : AddCommGroup Yₒ := inferInstanceAs (AddCommGroup Y)
instance : Module k Yₒ := inferInstanceAs (Module k Y)
instance : Module (TensorKLR S α δ) Yₒ :=
  Module.compHom Y (blocksShuffleAction Q Λ θ β γ N).toRingHom

theorem blocksShuffleInput_smul (t : TensorKLR S α δ) (y : Yₒ) :
    t • y = blocksShuffleAction Q Λ θ β γ N t (show Y from y) := rfl

instance : IsScalarTower k (TensorKLR S α δ) Yₒ where
  smul_assoc c t y := by
    rw [blocksShuffleInput_smul, blocksShuffleInput_smul, map_smul]
    rfl

/-! ### The inner standardization as a quotient of `Y` over the outer affine algebras -/

variable (hQ : KLRSymm Q)

local notation "Mid" => CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)
local notation "πᵢ" => Submodule.mkQ (excludedSpace
  (cutShuffleAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N))
  (cutOrderedLoadings (a := m) (r := r) β γ))

/-- The outer affine algebra of the last two blocks acts on the inner standardization through
its action on `Y`. -/
theorem cutStandardAction_suffix_mk (z : KLRAlgebra k S δ) (y : Y) :
    cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
      (cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ) z) (πᵢ y) =
      πᵢ (blocksShuffleTail Q Λ θ β γ N z y) := by
  have h := cutStandardAction_affine Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
    (blocksTailMap Q Λ β γ z)
  have hz : castKLR Sᵢ (cutInputWeights_add (a := m) (r := r) β γ)
      (blocksTailMap Q Λ β γ z) = (relabelEquiv (blocksTailRelabel Q Λ β γ)).symm z :=
    castKLR_castAlg_symm _ _
  rw [hz] at h
  exact LinearMap.congr_fun h (πᵢ y)

/-- The quotient map from `Y` to the inner standardization, `k`-linearly. -/
def blocksShuffleQuotientK : Yₒ →ₗ[k] Mid := πᵢ

private theorem blocksShuffleQuotientK_smul (t : TensorKLR S α δ) (y : Yₒ) :
    blocksShuffleQuotientK Q Λ θ β γ N hQ (t • y) =
      t • blocksShuffleQuotientK Q Λ θ β γ N hQ y := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', add_smul]
  | tmul t z =>
    rw [blocksShuffleInput_smul]
    change πᵢ (blocksShuffleHead Q Λ θ β γ N (cutPrefixProjection Q Λ θ t)
        (blocksShuffleTail Q Λ θ β γ N z (show Y from y))) =
      blocksMidAction Q Λ θ β γ N hQ (cutPrefixProjection Q Λ θ t ⊗ₜ[k]
        cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ) z) (πᵢ (show Y from y))
    rw [blocksMidAction, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply,
      cutStandardAction_suffix_mk]
    rfl

/-- **The quotient map from `Y` to the inner standardization**, linear over the outer affine
algebras. -/
def blocksShuffleQuotient : Yₒ →ₗ[TensorKLR S α δ] Mid where
  toFun := blocksShuffleQuotientK Q Λ θ β γ N hQ
  map_add' := map_add _
  map_smul' := blocksShuffleQuotientK_smul Q Λ θ β γ N hQ

theorem blocksShuffleQuotient_apply (y : Yₒ) :
    blocksShuffleQuotient Q Λ θ β γ N hQ y = πᵢ (show Y from y) := rfl

theorem blocksShuffleQuotient_surjective :
    Function.Surjective (blocksShuffleQuotient Q Λ θ β γ N hQ) := by
  intro z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (excludedSpace
    (cutShuffleAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N))
    (cutOrderedLoadings (a := m) (r := r) β γ)) (show BlocksMid Q Λ θ β γ N hQ from z)
  exact ⟨y, hy⟩

/-- The part of `Y` supported on unordered loadings of the last two blocks, a submodule over
the outer affine algebras. -/
abbrev blocksShuffleExcluded : Submodule (TensorKLR S α δ) Yₒ :=
  LinearMap.ker (blocksShuffleQuotient Q Λ θ β γ N hQ)

theorem mem_blocksShuffleExcluded {y : Yₒ} :
    y ∈ blocksShuffleExcluded Q Λ θ β γ N hQ ↔
      cutShuffleAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
        (eSum Sᵢ (cutOrderedLoadings (a := m) (r := r) β γ)) (show Y from y) = 0 := by
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

/-- The outer affine idempotent of a red-ordered loading of the last two blocks is a
red-ordered inner idempotent. -/
theorem blocksTailMap_e (b : Seq δ) (hb : IsRedOrdered b) :
    ∃ c, IsRedOrdered c ∧ blocksTailMap Q Λ β γ (e b) = e c := by
  let s := (blocksTailRelabel Q Λ β γ).equiv.symm b
  have hs : Seq.map (Sum.map (id : I → I) (Fin.natAdd a)) s = b :=
    Seq.map_mapEquiv_symm (Sum.map_injective.mpr ⟨Function.injective_id,
      Fin.natAdd_injective (m + r) a⟩) b
  refine ⟨Seq.cast (cutInputWeights_add (a := m) (r := r) β γ).symm s,
    isRedOrdered_seqCast _ _ (isRedOrdered_of_map (strictMono_natAdd' (a := a)) s
      (hs ▸ hb)), ?_⟩
  change castKLR Sᵢ _ ((relabelEquiv (blocksTailRelabel Q Λ β γ)).symm (e b)) = _
  rw [relabelEquiv_symm_apply, relabelHom_e, castKLR_e]
  rfl

/-- **The part of `Y` supported on unordered inner loadings is killed by every red-ordered
loading of the last two blocks.** -/
theorem blocksShuffleExcluded_e (y : Yₒ) (hy : y ∈ blocksShuffleExcluded Q Λ θ β γ N hQ)
    (a' : Seq α) (b : Seq δ) (hb : IsRedOrdered b) :
    (e a' ⊗ₜ[k] e b : TensorKLR S α δ) • y = 0 := by
  classical
  obtain ⟨c, hc, he⟩ := blocksTailMap_e Q Λ β γ b hb
  rw [blocksShuffleInput_smul]
  change blocksShuffleHead Q Λ θ β γ N _
    (cutShuffleAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
      (blocksTailMap Q Λ β γ (e b)) (show Y from y)) = 0
  have hcP : (e c * eSum Sᵢ (cutOrderedLoadings (a := m) (r := r) β γ) :
      KLRAlgebra k Sᵢ _) = e c := by
    simp [e_mul_eSum, cutOrderedLoadings, hc]
  rw [he, ← hcP, map_mul, Module.End.mul_apply,
    (mem_blocksShuffleExcluded Q Λ θ β γ N hQ).1 hy, map_zero, map_zero]

/-! ### The iterated standardization as one quotient of the outer induction of `Y` -/

local notation "W" => Ind S α δ (BlocksShuffleInput Q Λ θ β γ N)
local notation "Vₒ" => CutShuffle Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)
local notation "Fₒ" => cutOrderedLoadings (a := a) (r := m + r) θ (β + γ)

/-- The outer affine induction of the quotient map `Y → 𝕊_inner`. -/
def blocksShuffleInd : W →ₗ[KLRAlgebra k S (α + δ)] Vₒ :=
  BalancedTensor.mapRight (blocksShuffleQuotient Q Λ θ β γ N hQ)

theorem blocksShuffleInd_surjective : Function.Surjective (blocksShuffleInd Q Λ θ β γ N hQ) :=
  indMapRight_surjective (cutStendhalQ_symm Q Λ hQ) _
    (blocksShuffleQuotient_surjective Q Λ θ β γ N hQ)

/-- **The outer affine induction of `Y` modulo the part supported on unordered loadings of all
strands.** -/
abbrev BlocksShuffleQuot : Type _ :=
  W ⧸ excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W) Fₒ

/-- The map from the outer induction of `Y` to the iterated standardization. -/
def blocksStandardOfShuffle : W →ₗ[k] BlocksStandard Q Λ θ β γ N hQ :=
  (excludedSpace (cutShuffleAction Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)) Fₒ).mkQ ∘ₗ
    (blocksShuffleInd Q Λ θ β γ N hQ).restrictScalars k

theorem blocksStandardOfShuffle_surjective :
    Function.Surjective (blocksStandardOfShuffle Q Λ θ β γ N hQ) :=
  (Submodule.mkQ_surjective _).comp (blocksShuffleInd_surjective Q Λ θ β γ N hQ)

/-- **The kernel of the map to the iterated standardization** is the part of the outer
induction of `Y` supported on unordered loadings of all strands. -/
theorem blocksStandardOfShuffle_eq_zero_iff (w : W) :
    blocksStandardOfShuffle Q Λ θ β γ N hQ w = 0 ↔
      (eSum S Fₒ : KLRAlgebra k S (α + δ)) • w = 0 := by
  classical
  have hΦ : blocksStandardOfShuffle Q Λ θ β γ N hQ w = 0 ↔
      blocksShuffleInd Q Λ θ β γ N hQ ((eSum S Fₒ : KLRAlgebra k S (α + δ)) • w) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).trans (LinearMap.mem_ker.trans ?_)
    exact (iff_of_eq (congrArg (· = 0) ((blocksShuffleInd Q Λ θ β γ N hQ).map_smul _ w).symm))
  rw [hΦ]
  constructor
  · intro h
    have hex := indMapRight_exact (cutStendhalQ_symm Q Λ hQ)
      (blocksShuffleExcluded Q Λ θ β γ N hQ).subtype (blocksShuffleQuotient Q Λ θ β γ N hQ)
      (LinearMap.exact_subtype_ker_map _)
    obtain ⟨z, hz⟩ := (hex _).1 h
    have h0 := eSum_redOrdered_smul_mapRight_eq_zero (cutStendhalQ_symm Q Λ hQ)
      (blocksShuffleExcluded Q Λ θ β γ N hQ)
      (fun n hn a' b hb => blocksShuffleExcluded_e Q Λ θ β γ N hQ n hn a' b hb) z
    rw [hz, ← mul_smul] at h0
    rw [← (eSum_idem (Q := S) Fₒ).eq]
    exact h0
  · intro h
    rw [h, map_zero]

theorem ker_blocksStandardOfShuffle :
    LinearMap.ker (blocksStandardOfShuffle Q Λ θ β γ N hQ) =
      excludedSpace (Algebra.lsmul k k W : KLRAlgebra k S (α + δ) →ₐ[k] Module.End k W)
        Fₒ := by
  ext w
  exact LinearMap.mem_ker.trans (blocksStandardOfShuffle_eq_zero_iff Q Λ θ β γ N hQ w)

/-- **The iterated standardization is the outer induction of the inner affine induced module
modulo the part supported on unordered loadings of all strands**: the inner quotient can be
taken last. -/
def blocksStandardEquiv :
    BlocksShuffleQuot Q Λ θ β γ N ≃ₗ[k] BlocksStandard Q Λ θ β γ N hQ :=
  (Submodule.quotEquivOfEq _ _ (ker_blocksStandardOfShuffle Q Λ θ β γ N hQ).symm).trans
    ((blocksStandardOfShuffle Q Λ θ β γ N hQ).quotKerEquivOfSurjective
      (blocksStandardOfShuffle_surjective Q Λ θ β γ N hQ))

theorem blocksStandardEquiv_mk (w : W) :
    blocksStandardEquiv Q Λ θ β γ N hQ (Submodule.Quotient.mk w) =
      blocksStandardOfShuffle Q Λ θ β γ N hQ w := rfl

/-- The identification is compatible with the affine action of all strands, which acts on the
iterated standardization through `T^λ(θ + (β + γ))`. -/
theorem blocksStandardEquiv_smul (z : KLRAlgebra k S (α + δ)) (w : W) :
    blocksStandardEquiv Q Λ θ β γ N hQ (Submodule.Quotient.mk (z • w)) =
      blocksStandardAction Q Λ θ β γ N hQ (TensorProductAlgebra.mk Q Λ (θ + (β + γ))
        (orderProjection Q Λ (θ + (β + γ)) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + (β + γ))
          (castKLR S (cutInputWeights_add (a := a) (r := m + r) θ (β + γ)) z))))
        (blocksStandardEquiv Q Λ θ β γ N hQ (Submodule.Quotient.mk w)) := by
  rw [blocksStandardEquiv_mk, blocksStandardEquiv_mk, blocksStandardAction,
    cutStandardAction_affine]
  change Submodule.Quotient.mk (blocksShuffleInd Q Λ θ β γ N hQ (z • w)) =
    Submodule.Quotient.mk (z • blocksShuffleInd Q Λ θ β γ N hQ w)
  rw [LinearMap.map_smul]

end Categorification.Stendhal
