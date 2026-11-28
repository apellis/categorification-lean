/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksStandardBasis

/-!
# The standard basis of a partial standardization with three blocks

Webster, arXiv:1309.3796v3, §5.1, the partial standardizations after Definition 5.4, in the
induced model (`BlocksStandard`); used in §7.3, proof of Lemma 7.19, for the standard basis of
`S_+` (Webster states no basis of a partial standardization). By `blocksStandardShuffleEquiv`,
`𝕊^{A;M;R}(N)` is the module of families `G : Sh_out → Sh_in → N` whose rows are inner
coordinates of elements of `ε_{u_out} 𝕊^{M;R}(N)`. Here the row condition is made explicit:

  `𝕊^{A;M;R}(N) ≅ {G | ε^in_{u_in} G(u_out, u_in) = G(u_out, u_in) and
    E_{u_out,u_in} G(u_out, u_in) = G(u_out, u_in) for all u_out, u_in}`

(`mem_blocksShuffleCoords_iff`), with `E_{u_out,u_in}` an element of the block algebra
`T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))` (`blocksRowIdem`): the image of `ε_{u_out}` in the coordinate
`u_in` (`blocksMidShuffleEquiv_cutShuffleIdem_smul`).

The outer suffix loadings (red labels in `Fin (a + (m + r))`) are matched with the inner affine
loadings (red labels in `Fin (m + r)`) by an explicit bijection of index sets (`tailSeqEquiv`),
under which the two quotient maps onto `T^{MR}(β + γ)` agree on idempotents
(`cutSuffixProjection_e_tailSeqEquiv`).

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.tailSeqEquiv`, `Stendhal.blocksRowIdem`.

## Main results

* `Stendhal.blocksMidShuffleEquiv_cutShuffleIdem_smul`, `Stendhal.mem_blocksShuffleCoords_iff`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)

local notation "αo" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r)))
  (stendhalWeight a θ)
local notation "δo" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (stendhalWeight (m + r) (β + γ))
local notation "αi" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "δi" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "ShO" => Shuffle (Seq.card_add' αo δo)
local notation "ShI" => Shuffle (Seq.card_add' αi δi)

omit [DecidableEq I] in
/-- Transport of loadings along an equality of weights, as an equivalence. -/
def seqCastEquiv {μ μ' : Multiset (I ⊕ Fin (m + r))} (h : μ = μ') : Seq μ ≃ Seq μ' where
  toFun := Seq.cast h
  invFun := Seq.cast h.symm
  left_inv s := by subst h; rfl
  right_inv s := by subst h; rfl

variable (a) in
/-- **The matching of index sets**: inner affine loadings of the blocks `M; R` (red labels in
`Fin (m + r)`) correspond to outer suffix loadings (red labels in `Fin (a + (m + r))`). -/
def tailSeqEquiv : Seq (αi + δi) ≃ Seq δo :=
  (seqCastEquiv (cutInputWeights_add (a := m) (r := r) β γ)).trans
    (redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a) (β + γ)).equiv

/-- **The two quotient maps onto `T^{MR}(β + γ)` agree on matched idempotents.** -/
theorem cutSuffixProjection_e_tailSeqEquiv (t : Seq (αi + δi)) :
    cutSuffixProjection Q Λ (β + γ) (e (tailSeqEquiv a Q Λ β γ t)) =
      affineToTensor Q (blocksTailLabels Λ) β γ (e t) := by
  have h : (relabelEquiv (redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
      (β + γ))).symm (e (tailSeqEquiv a Q Λ β γ t)) =
      e (Seq.cast (cutInputWeights_add (a := m) (r := r) β γ) t) :=
    (AlgEquiv.symm_apply_eq _).2 (relabelHom_e (redSubfamilyRelabel Q Λ (Fin.natAdd a)
      (Fin.natAdd_injective (m + r) a) (β + γ))
        (Seq.cast (cutInputWeights_add (a := m) (r := r) β γ) t)).symm
  simp only [cutSuffixProjection, redSubfamilyProjection, affineToTensor, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, h, castKLR_e]

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N] (hQ : KLRSymm Q)

local notation "Inner" => CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "Mid" => CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)

/-- An inner coordinate, as an element of the module over the three blocks. -/
def innerVal : Inner →+ BlocksInner Q Λ θ β γ N := AddMonoidHom.id _

/-- The action of the outer affine block algebra on the middle stage. -/
def midSmul (b : TensorKLR (stendhalQ Q Λ) αo δo) (z : BlocksMid Q Λ θ β γ N hQ) :
    BlocksMid Q Λ θ β γ N hQ :=
  (b • (show Mid from z) : Mid)

theorem midSmul_sum {ι : Type*} (s : Finset ι) (b : ι → TensorKLR (stendhalQ Q Λ) αo δo)
    (z : BlocksMid Q Λ θ β γ N hQ) :
    midSmul Q Λ θ β γ N hQ (∑ i ∈ s, b i) z = ∑ i ∈ s, midSmul Q Λ θ β γ N hQ (b i) z := by
  change (∑ i ∈ s, b i) • (show Mid from z) = ∑ i ∈ s, (b i • (show Mid from z) : Mid)
  exact Finset.sum_smul

/-- A pure tensor of outer loading idempotents acts on the middle stage through the first block
and the inner affine algebra. -/
theorem tmul_smul_blocksMid (p : Seq αo) (t : Seq (αi + δi)) (z : BlocksMid Q Λ θ β γ N hQ) :
    midSmul Q Λ θ β γ N hQ (e p ⊗ₜ e (tailSeqEquiv a Q Λ β γ t)) z =
      blocksHeadAction Q Λ θ β γ N (cutPrefixProjection Q Λ θ (e p))
        (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
          (affineToTensor Q (blocksTailLabels Λ) β γ (e t)) z) := by
  change blocksMidAction Q Λ θ β γ N hQ (cutInputMap Q Λ θ (β + γ) (e p ⊗ₜ e _)) z = _
  rw [cutInputMap, Algebra.TensorProduct.map_tmul, blocksMidAction,
    Algebra.TensorProduct.lift_tmul, cutSuffixProjection_e_tailSeqEquiv]
  rfl

/-- The image of `ε_{u_out}` in the inner coordinate `u_in`, an element of the block algebra
`T^A(θ) ⊗ (T^M(β) ⊗ T^R(γ))`. -/
def blocksRowIdem (u : ShO) (v : ShI) : blocksFactorAlgebra Q Λ θ β γ :=
  ∑ s ∈ cutOrderedLoadings (a := a) (r := m + r) θ (β + γ),
    ∑ p ∈ Finset.univ.filter (fun p : Seq αo × Seq δo => p.1.append p.2 = u.1 • s),
      cutPrefixProjection Q Λ θ (e p.1) ⊗ₜ
        cutInputMap Q (blocksTailLabels Λ) β γ
          (concatIdem (Q := stendhalQ Q (blocksTailLabels Λ))
            (v.1 • (tailSeqEquiv a Q Λ β γ).symm p.2))

/-- **`ε_{u_out}` in inner coordinates**: the coordinate `u_in` of `ε_{u_out} z` is
`E_{u_out,u_in}` applied to the coordinate `u_in` of `z`. -/
theorem blocksMidShuffleEquiv_cutShuffleIdem_smul (u : ShO) (z : BlocksMid Q Λ θ β γ N hQ)
    (v : ShI) :
    innerVal Q Λ θ β γ N ((blocksMidShuffleEquiv Q Λ θ β γ N hQ
        (midSmul Q Λ θ β γ N hQ (cutShuffleIdem Q Λ θ (β + γ) u) z) : ShI → Inner) v) =
      blocksRowIdem Q Λ θ β γ u v •
        innerVal Q Λ θ β γ N ((blocksMidShuffleEquiv Q Λ θ β γ N hQ z : ShI → Inner) v) := by
  have hs : ∀ {ι : Type _} (t : Finset ι) (f : ι → blocksFactorAlgebra Q Λ θ β γ)
      (x : BlocksInner Q Λ θ β γ N), (∑ i ∈ t, f i) • x = ∑ i ∈ t, f i • x :=
    fun _ _ _ => Finset.sum_smul
  rw [cutShuffleIdem, midSmul_sum, map_sum, Submodule.coe_sum, Finset.sum_apply, map_sum,
    blocksRowIdem, hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [concatIdem, midSmul_sum, map_sum, Submodule.coe_sum, Finset.sum_apply, map_sum, hs]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨t, rfl⟩ := (tailSeqEquiv a Q Λ β γ).surjective p₂
  have h1 := blocksMidShuffleEquiv_head Q Λ θ β γ N hQ (cutPrefixProjection Q Λ θ (e p₁))
    (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
      (affineToTensor Q (blocksTailLabels Λ) β γ (e t)) z) v
  have h2 := blocksMidShuffleEquiv_tail_e Q Λ θ β γ N hQ t z v
  rw [h2] at h1
  rw [tmul_smul_blocksMid]
  refine (congrArg (innerVal Q Λ θ β γ N) h1).trans ?_
  rw [Equiv.symm_apply_apply]
  change ((cutPrefixProjection Q Λ θ (e p₁) ⊗ₜ[k] 1 : blocksFactorAlgebra Q Λ θ β γ) •
      (((1 : blocksHeadAlgebra Q Λ θ) ⊗ₜ[k]
        cutInputMap Q (blocksTailLabels Λ) β γ (concatIdem (v.1 • t)) :
          blocksFactorAlgebra Q Λ θ β γ) • (_ : N)) : N) = _
  exact (mul_smul _ _ _).symm.trans
    (congrArg (fun d : blocksFactorAlgebra Q Λ θ β γ => d • (show N from
      (blocksMidShuffleEquiv Q Λ θ β γ N hQ z : ShI → Inner) v))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]))

/-- **The standard basis of the partial standardization with three blocks**: a family
`G : Sh_out → Sh_in → N` is a coordinate vector of `𝕊^{A;M;R}(N)` iff
`ε^in_{u_in} G(u_out, u_in) = G(u_out, u_in)` and `E_{u_out,u_in} G(u_out, u_in) =
G(u_out, u_in)` for all `u_out`, `u_in`. -/
theorem mem_blocksShuffleCoords_iff (G : ShO → ShI → Inner) :
    G ∈ blocksShuffleCoords Q Λ θ β γ N hQ ↔
      (∀ u v, cutShuffleIdem Q (blocksTailLabels Λ) β γ v • G u v = G u v) ∧
        ∀ u v, blocksRowIdem Q Λ θ β γ u v • innerVal Q Λ θ β γ N (G u v) =
          innerVal Q Λ θ β γ N (G u v) := by
  have hin : ∀ h : ShI → Inner, h ∈ cutShuffleCoords Q (blocksTailLabels Λ) β γ
      (BlocksInner Q Λ θ β γ N) ↔ ∀ v, cutShuffleIdem Q (blocksTailLabels Λ) β γ v • h v = h v :=
    fun h => by
      simp only [cutShuffleCoords, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
      exact forall_congr' fun v => cutShuffleIdem_mem_range_iff _ _ _ _ _ v (h v)
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fun u => (hin _).1 (blocksMidShuffleEquiv Q Λ θ β γ N hQ (g u)).2, fun u v => ?_⟩
    have hgu : midSmul Q Λ θ β γ N hQ (cutShuffleIdem Q Λ θ (β + γ) u) (g u) = g u := by
      have := hg u (Set.mem_univ u)
      exact (cutShuffleIdem_mem_range_iff Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ) u (g u)).1 this
    change blocksRowIdem Q Λ θ β γ u v • innerVal Q Λ θ β γ N
        ((blocksMidShuffleEquiv Q Λ θ β γ N hQ (g u) : ShI → Inner) v) =
      innerVal Q Λ θ β γ N ((blocksMidShuffleEquiv Q Λ θ β γ N hQ (g u) : ShI → Inner) v)
    rw [← blocksMidShuffleEquiv_cutShuffleIdem_smul, hgu]
  · rintro ⟨h1, h2⟩
    let g : ShO → BlocksMid Q Λ θ β γ N hQ := fun u =>
      (blocksMidShuffleEquiv Q Λ θ β γ N hQ).symm ⟨G u, (hin _).2 (h1 u)⟩
    have hg : ∀ u, (blocksMidShuffleEquiv Q Λ θ β γ N hQ (g u) : ShI → Inner) = G u := fun u =>
      congrArg Subtype.val ((blocksMidShuffleEquiv Q Λ θ β γ N hQ).apply_symm_apply _)
    refine ⟨g, fun u _ => ?_, funext fun u => hg u⟩
    refine (cutShuffleIdem_mem_range_iff Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ) u (g u)).2 ?_
    change midSmul Q Λ θ β γ N hQ (cutShuffleIdem Q Λ θ (β + γ) u) (g u) = g u
    apply (blocksMidShuffleEquiv Q Λ θ β γ N hQ).injective
    refine Subtype.ext (funext fun v => ?_)
    change innerVal Q Λ θ β γ N ((blocksMidShuffleEquiv Q Λ θ β γ N hQ
      (midSmul Q Λ θ β γ N hQ (cutShuffleIdem Q Λ θ (β + γ) u) (g u)) : ShI → Inner) v) =
        innerVal Q Λ θ β γ N ((blocksMidShuffleEquiv Q Λ θ β γ N hQ (g u) : ShI → Inner) v)
    rw [blocksMidShuffleEquiv_cutShuffleIdem_smul, hg]
    exact h2 u v

end Categorification.Stendhal
