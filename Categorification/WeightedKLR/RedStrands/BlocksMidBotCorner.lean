/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardIdentityCorner
import Categorification.KLR.MackeyBotCorner
import Categorification.KLR.SeqSplit

/-!
# The bottom corner of a Mackey layer at the outer cut of three blocks

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the bottom factor
at `S_+`).

For three blocks `A | M | R` the partial standardization is iterated: first at the inner cut
`M | R`, giving `BlocksMid X = 𝕊_{M|R}(X)`, then at the outer cut `A | MR`. For a Mackey datum
`q` of the outer cut whose weight `q.β` is the weight `αi` of the middle block (read in the
outer labels), the bottom idempotent `E = quadBot 1 = 1_{α,γ} ⊗ 1_{β,δ}` acts on the input
`BlocksMid X` of the outer cut as the product of two commuting idempotents
(`quadBot_one_smul_cutInput_blocksMid`):

* the head factor `1_{α,γ}`, through `T^A(θ)` (`botHeadIdem`);
* the factor `1_{β,δ}`, which is the identity `1_{αi, δi}` of the two inner blocks seen in
  `T^{MR}(β + γ)` (`cutSuffixProjection_castAlg_oneConcat`, `botInnerIdem`).

So the corner `E · BlocksMid X` is the corner `e(αi δi) 𝕊_{M|R}(X)` cut down by the head
factor (`mem_botCorner_cutInput_blocksMid_iff`). By `cutIdentityCornerEquivConcat`, only the
identity shuffle coordinate survives there; the head acts on each coordinate. Hence
`E · BlocksMid X ≅ ε_1 X ∩ 1_{αi δi} X ∩ (fixed points of 1_{α,γ})`
(`botCornerBlocksEquiv`),
with inverse the identity-shuffle copy `n ↦ 1 ⊗ n` (`botCornerBlocksEquiv_symm_apply`).

The relabelling step: the second-block projection of the outer cut sends `e(c ∘ s)` to the
image of `e(s)` in `T^{MR}`, as the inner affine map does (`cutSuffixProjection_e_map`), and
the image of the concatenations of `q.β` and `q.δ` is the image of the concatenations of `αi`
and `δi` (`image_seqCast_concatSet_eq_map`, via `Seq.mem_concatSet_iff_prefixWt`). The red
labels of the two inner blocks are `blocksTailLabels Λ = Λ ∘ Fin.natAdd a` by definition.

Webster's proof does not spell this out. Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.botHeadIdem`, `Stendhal.botInnerIdem`, `Stendhal.botBlocksCorner`,
  `Stendhal.botCornerBlocksEquiv`.

## Main results

* `KLR.Seq.mem_concatSet_iff_prefixWt`, `Stendhal.cutSuffixProjection_e_map`,
  `Stendhal.cutSuffixProjection_castAlg_oneConcat`,
  `Stendhal.quadBot_one_smul_cutInput_blocksMid`,
  `Stendhal.mem_botCorner_cutInput_blocksMid_iff`, `Stendhal.botCornerBlocksEquiv_apply`,
  `Stendhal.botCornerBlocksEquiv_symm_apply`.
-/

noncomputable section

namespace Categorification.KLR.Seq

variable {I J : Type*}

theorem prefixWt_cast {μ μ' : Multiset I} (h : μ = μ') (s : Seq μ) (n : ℕ)
    (hn : n ≤ Multiset.card μ') :
    prefixWt (Seq.cast h s) n hn = prefixWt s n (h ▸ hn) := by
  subst h; rfl

theorem prefixWt_map (f : J → I) {μ : Multiset J} (s : Seq μ) (n : ℕ)
    (hn : n ≤ Multiset.card (μ.map f)) :
    prefixWt (Seq.map f s) n hn = (prefixWt s n (by simpa using hn)).map f := by
  rw [prefixWt, prefixWt, Multiset.map_map]
  rfl

theorem prefixWt_congr {μ : Multiset I} (s : Seq μ) {n n' : ℕ} (h : n = n')
    (hn : n ≤ Multiset.card μ) (hn' : n' ≤ Multiset.card μ) :
    prefixWt s n hn = prefixWt s n' hn' := by
  subst h; rfl

/-- **A loading of `μ + ν` is a concatenation iff its first `|μ|` labels have weight `μ`.** -/
theorem mem_concatSet_iff_prefixWt [DecidableEq I] {μ ν : Multiset I} (s : Seq (μ + ν)) :
    s ∈ KLRAlgebra.concatSet μ ν ↔ prefixWt s (Multiset.card μ) (by simp) = μ := by
  constructor
  · intro hs
    obtain ⟨i, j, rfl⟩ := KLRAlgebra.mem_concatSet.1 hs
    conv_rhs => rw [← i.2]
    rw [prefixWt]
    refine Multiset.map_congr rfl fun a _ => ?_
    exact append_apply_lt i j _ a.2
  · intro hp
    have hsum := prefixWt_add_suffixWt s (Multiset.card μ) (by simp)
    have hsuf : suffixWt s (Multiset.card μ) (by simp) = ν := by
      rw [hp] at hsum; exact add_left_cancel hsum
    refine KLRAlgebra.mem_concatSet.2 ⟨Seq.cast hp (prefixSeq s _ (by simp)),
      Seq.cast hsuf (suffixSeq s _ (by simp)), ?_⟩
    apply Subtype.ext
    funext x
    by_cases hx : x.val < Multiset.card μ
    · rw [append_apply_lt _ _ _ hx, cast_apply, prefixSeq_apply]
      exact congrArg s.1 (Fin.ext rfl)
    · rw [append_apply_ge _ _ _ (by omega), cast_apply, suffixSeq_apply]
      exact congrArg s.1 (Fin.ext (by simp; omega))

end Categorification.KLR.Seq

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ)
  (θ β γ : Multiset I)

local notation "αi" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β)
local notation "δi" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ)
local notation "cR" => Sum.map (id : I → I) (Fin.natAdd a : Fin (m + r) → Fin (a + (m + r)))

section Relabel

/-- **The second-block projection of the outer cut on a relabelled idempotent**:
`e(c ∘ s) ↦` the image of `e(s)` under the inner affine map. -/
theorem cutSuffixProjection_e_map (s : Seq (stendhalWeight (m + r) (β + γ))) :
    cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ) (e (Seq.map cR s)) =
      affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ
        (e (Seq.cast (cutInputWeights_add (a := m) (r := r) β γ).symm s)) := by
  have h : (e (Seq.map cR s) : KLRAlgebra k (stendhalQ Q Λ) _) =
      relabelEquiv (redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective (m + r) a)
        (β + γ)) (e s) := by rw [relabelEquiv_apply, relabelHom_e]; rfl
  rw [h, cutSuffixProjection, redSubfamilyProjection]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  rw [affineToTensor]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_e]
  rfl

/-- The concatenations of `q.β = c(αi)` and `q.δ` are the relabelled concatenations of `αi`
and `δi`. -/
theorem image_seqCast_concatSet_eq_map {βo δo' : Multiset (I ⊕ Fin (a + (m + r)))}
    (h : βo + δo' = (stendhalWeight (m + r) (β + γ)).map cR) (hβ : βo = (αi).map cR) :
    (concatSet βo δo').image (seqCast h) =
      (concatSet αi δi).image
        (fun s' => Seq.map cR (Seq.cast (cutInputWeights_add (a := m) (r := r) β γ) s')) := by
  subst hβ
  have hle : Multiset.card ((αi).map cR) ≤
      Multiset.card ((stendhalWeight (m + r) (β + γ)).map cR) := by
    rw [← h, Multiset.card_add]; omega
  have key : ∀ t, t ∈ (concatSet _ δo').image (seqCast h) ↔
      Seq.prefixWt t _ hle = (αi).map cR := by
    intro t
    constructor
    · intro ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
      rw [seqCast_eq_cast, Seq.prefixWt_cast]
      exact (Seq.mem_concatSet_iff_prefixWt t₀).1 ht₀
    · intro ht
      refine Finset.mem_image.2 ⟨Seq.cast h.symm t, ?_, ?_⟩
      · rw [Seq.mem_concatSet_iff_prefixWt, Seq.prefixWt_cast]
        exact ht
      · rw [seqCast_eq_cast]
        rfl
  have hc : Function.Injective cR :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.natAdd_injective (m + r) a⟩
  ext t
  rw [key]
  constructor
  · intro ht
    obtain ⟨s, rfl⟩ := (Seq.map_bijective hc _).2 t
    refine Finset.mem_image.2 ⟨Seq.cast (cutInputWeights_add (a := m) (r := r) β γ).symm s,
      ?_, rfl⟩
    rw [Seq.mem_concatSet_iff_prefixWt, Seq.prefixWt_cast]
    rw [Seq.prefixWt_map] at ht
    exact (Seq.prefixWt_congr s (by simp) _ _).trans (Multiset.map_injective hc ht)
  · intro ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht
    rw [Seq.prefixWt_map, Seq.prefixWt_cast]
    congr 1
    exact (Seq.prefixWt_congr _ (by simp) _ _).trans ((Seq.mem_concatSet_iff_prefixWt s').1 hs')

/-- **The identity of the middle block on the inner cut**: for `q.β = c(αi)`, the second-block
projection of the outer cut sends `1_{q.β, q.δ}` to the image of `1_{αi, δi}` under the inner
affine map. -/
theorem cutSuffixProjection_castAlg_oneConcat {βo δo' : Multiset (I ⊕ Fin (a + (m + r)))}
    (h : βo + δo' = (stendhalWeight (m + r) (β + γ)).map cR) (hβ : βo = (αi).map cR) :
    cutSuffixProjection (a := a) (r := m + r) Q Λ (β + γ)
        (castAlg (stendhalQ Q Λ) h (oneConcat (stendhalQ Q Λ) βo δo')) =
      affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ
        (oneConcat (stendhalQ Q (blocksTailLabels Λ)) αi δi) := by
  rw [oneConcat, castAlg_eSum, image_seqCast_concatSet_eq_map β γ h hβ, oneConcat, eSum, eSum,
    map_sum, map_sum, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s' _ => ?_
    rw [cutSuffixProjection_e_map]
    rfl
  · intro x _ y _ hxy
    exact congrArg (Seq.cast (cutInputWeights_add (a := m) (r := r) β γ).symm)
      ((Seq.map_bijective (Sum.map_injective.2
        ⟨Function.injective_id, Fin.natAdd_injective (m + r) a⟩) _).1 hxy)

end Relabel

/-- Two commuting idempotent endomorphisms: `P P' z = z` iff `P' z = z` and `P z = z`. -/
theorem endFixed_mul_iff_of_commute {V : Type*} [AddCommGroup V] [Module k V]
    {P P' : Module.End k V} (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P')
    (hc : Commute P P') (z : V) : P (P' z) = z ↔ P' z = z ∧ P z = z := by
  constructor
  · intro h
    have h1 : P' z = z := by
      conv_lhs => rw [← h]
      change (P' * (P * P')) z = z
      rw [← mul_assoc, ← hc.eq, mul_assoc, hP'.eq]
      exact h
    refine ⟨h1, ?_⟩
    conv_lhs => rw [← h]
    change (P * (P * P')) z = z
    rw [← mul_assoc, hP.eq]
    exact h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

section Corner

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  (hQ : KLRSymm Q)

local notation "αo" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r)))
  (stendhalWeight a θ)
local notation "δo" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (stendhalWeight (m + r) (β + γ))
local notation "Nₒ" => CutInput Q Λ θ (β + γ) (BlocksMid Q Λ θ β γ N hQ)
local notation "Inner" => CutInput Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "CSi" => CutStandard Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
local notation "LCi" => cutLoadCorner Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
  (concatSet αi δi)
local notation "ILi" => inputLoadCorner Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N)
  (concatSet αi δi)
local notation "Sh" => Shuffle (Seq.card_add' αi δi)

variable {ν ν' : Multiset (I ⊕ Fin (a + (m + r)))} (q : MackeyQuad ν ν'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ))))

/-- The head factor `1_{α,γ}` of `quadBot 1`, in `T^A(θ)`. -/
def botHeadIdem : blocksHeadAlgebra Q Λ θ :=
  cutPrefixProjection (a := a) (r := m + r) Q Λ θ
    (castAlg (stendhalQ Q Λ) q.h₃ (oneConcat (stendhalQ Q Λ) q.α q.γ))

/-- The inner factor of `quadBot 1`: the identity of `αi ⊗ δi` in `T^{MR}(β + γ)`. -/
def botInnerIdem : TensorProductAlgebra k Q (blocksTailLabels Λ) (β + γ) :=
  affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ
    (oneConcat (stendhalQ Q (blocksTailLabels Λ)) αi δi)

theorem botHeadIdem_idem : IsIdempotentElem (botHeadIdem Q Λ θ β γ q) :=
  ((oneConcat_idem (Q := stendhalQ Q Λ)).map (castAlg (stendhalQ Q Λ) q.h₃)).map
    (cutPrefixProjection (a := a) (r := m + r) Q Λ θ)

theorem botInnerIdem_idem :
    IsIdempotentElem (botInnerIdem (a := a) (m := m) (r := r) Q Λ β γ) :=
  (oneConcat_idem (Q := stendhalQ Q (blocksTailLabels Λ))).map
    (affineToTensor (a := m) (r := r) Q (blocksTailLabels Λ) β γ)

/-- **`quadBot 1` on the input of the outer cut**: for `q.β = c(αi)` it acts on `BlocksMid X`
as the head factor `1_{α,γ}` composed with the inner identity `1_{αi, δi}`. -/
theorem quadBot_one_smul_cutInput_blocksMid (hβ : q.β = (αi).map cR) (z : Nₒ) :
    (quadBot (Q := stendhalQ Q Λ) q 1 : TensorKLR (stendhalQ Q Λ) αo δo) • z =
      blocksHeadAction Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q)
        (cutStandardAction Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
          (botInnerIdem Q Λ β γ) z) := by
  have h1 : (1 : QuadAlg (stendhalQ Q Λ) q) = ((1 : KLRAlgebra k (stendhalQ Q Λ) q.α) ⊗ₜ
      (1 : KLRAlgebra k (stendhalQ Q Λ) q.β)) ⊗ₜ
      ((1 : KLRAlgebra k (stendhalQ Q Λ) q.γ) ⊗ₜ
        (1 : KLRAlgebra k (stendhalQ Q Λ) q.δ)) := rfl
  rw [h1, quadBot_tmul, ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def,
    concat_one, concat_one]
  change blocksMidAction Q Λ θ β γ N hQ (cutInputMap Q Λ θ (β + γ) _) z = _
  simp only [cutInputMap, Algebra.TensorProduct.map_tmul]
  rw [cutSuffixProjection_castAlg_oneConcat Q Λ β γ q.h₄ hβ]
  rfl

/-- **The bottom corner at the outer cut**: for `q.β = c(αi)`, `z ∈ E · BlocksMid X` iff `z`
lies in the corner `e(αi δi) 𝕊_{M|R}(X)` and is fixed by the head factor. -/
theorem mem_botCorner_cutInput_blocksMid_iff (hβ : q.β = (αi).map cR) (z : Nₒ) :
    z ∈ botCorner (stendhalQ Q Λ) q Nₒ ↔
      z ∈ LCi ∧ blocksHeadAction Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q) z = z := by
  rw [mem_botCorner, quadBot_one_smul_cutInput_blocksMid Q Λ θ β γ N hQ q hβ]
  exact endFixed_mul_iff_of_commute ((botHeadIdem_idem Q Λ θ β γ q).map _)
    ((botInnerIdem_idem Q Λ β γ).map _) (commute_blocksHeadAction Q Λ θ β γ N hQ _ _) z

/-- The head acts on each shuffle coordinate of the inner standardization. -/
theorem cutStandardShuffleEquiv_blocksHeadAction (t : blocksHeadAlgebra Q Λ θ) (z : CSi)
    (u : Sh) :
    (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
        (blocksHeadAction Q Λ θ β γ N t z) : Sh → Inner) u =
      blocksHeadEnd Q Λ θ β γ N t
        ((cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ z :
          Sh → Inner) u) :=
  cutStandardShuffleEquiv_map Q (blocksTailLabels Λ) β γ hQ _ z u

/-- **The bottom corner of the inner input**: the identity-shuffle corner
`ε_1 X ∩ 1_{αi δi} X` of the inner input on which the head factor `1_{α,γ}` acts
trivially. -/
def botBlocksCorner : Submodule k Inner :=
  ILi ⊓ LinearMap.eqLocus
    ((blocksHeadEnd Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q)).restrictScalars k) LinearMap.id

theorem mem_botBlocksCorner {n : Inner} :
    n ∈ botBlocksCorner Q Λ θ β γ N q ↔
      n ∈ ILi ∧ blocksHeadEnd Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q) n = n :=
  Iff.rfl

/-- The head preserves the corner `e(T) 𝕊_{M|R}(X)`. -/
theorem blocksHeadAction_mem_cutLoadCorner (t : blocksHeadAlgebra Q Λ θ)
    (T : Finset (Seq (αi + δi))) {z : CSi}
    (hz : z ∈ cutLoadCorner Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ T) :
    blocksHeadAction Q Λ θ β γ N t z ∈
      cutLoadCorner Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ T := by
  rw [mem_cutLoadCorner] at hz ⊢
  rw [← Module.End.mul_apply, ← (commute_blocksHeadAction Q Λ θ β γ N hQ t _).eq,
    Module.End.mul_apply, hz]

/-- The identity-shuffle corner equivalence of the inner cut, at `T = concatSet αi δi`. -/
abbrev innerIdentityCornerEquiv : LCi ≃ₗ[k] ILi :=
  cutIdentityCornerEquivConcat Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
    (concatSet αi δi) subset_rfl

local notation "Ei" => innerIdentityCornerEquiv Q Λ θ β γ N hQ

/-- On the corner `e(αi δi) 𝕊_{M|R}(X)`, an element is fixed by the head factor iff its
identity coordinate is. -/
theorem blocksHeadAction_fixed_iff (z : LCi) :
    blocksHeadAction Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q) z = z ↔
      blocksHeadEnd Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q)
          ((cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
            (z : CSi) : Sh → Inner) shufOne) =
        (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
            (z : CSi) : Sh → Inner) shufOne := by
  rw [← cutStandardShuffleEquiv_blocksHeadAction]
  constructor
  · intro h
    rw [h]
  · intro h
    have hm := blocksHeadAction_mem_cutLoadCorner Q Λ θ β γ N hQ (botHeadIdem Q Λ θ β γ q)
      _ z.2
    have := (innerIdentityCornerEquiv Q Λ θ β γ N hQ).injective
      (a₁ := ⟨_, hm⟩) (a₂ := z) (Subtype.ext h)
    exact congrArg Subtype.val this

variable {q}

/-- The bottom corner, as a submodule of the corner `e(αi δi) 𝕊_{M|R}(X)`. -/
def botCornerToLoad (hβ : q.β = (αi).map cR) :
    botCorner (stendhalQ Q Λ) q Nₒ →ₗ[k] LCi where
  toFun z := ⟨(show CSi from (z : Nₒ)),
    ((mem_botCorner_cutInput_blocksMid_iff Q Λ θ β γ N hQ q hβ z).1 z.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fixed points of the head factor in `e(αi δi) 𝕊_{M|R}(X)` lie in the bottom corner. -/
def loadToBotCorner (hβ : q.β = (αi).map cR) :
    LinearMap.eqLocus ((blocksHeadAction Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q)).comp
        (Submodule.subtype LCi)) (Submodule.subtype LCi) →ₗ[k]
      botCorner (stendhalQ Q Λ) q Nₒ where
  toFun y := ⟨(show Nₒ from ((y : LCi) : CSi)),
    (mem_botCorner_cutInput_blocksMid_iff Q Λ θ β γ N hQ q hβ _).2 ⟨(y : LCi).2, y.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The bottom corner at the outer cut is the bottom corner of the inner input**: for a
Mackey datum `q` whose weight `β` is the weight of the middle block, the identity coordinate of
the inner standardization is a `k`-linear isomorphism from `E · BlocksMid X`,
`E = quadBot 1`, onto the corner `ε_1 X ∩ 1_{αi δi} X` of the inner input fixed by the head
factor `1_{α,γ}`. -/
def botCornerBlocksEquiv (hβ : q.β = (αi).map cR) :
    botCorner (stendhalQ Q Λ) q Nₒ ≃ₗ[k] botBlocksCorner Q Λ θ β γ N q :=
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict (botBlocksCorner Q Λ θ β γ N q)
      ((Submodule.subtype ILi) ∘ₗ (Ei).toLinearMap ∘ₗ
        botCornerToLoad Q Λ θ β γ N hQ hβ)
      (fun z => ⟨(Ei
          (botCornerToLoad Q Λ θ β γ N hQ hβ z)).2,
        (blocksHeadAction_fixed_iff Q Λ θ β γ N hQ q _).1
          ((mem_botCorner_cutInput_blocksMid_iff Q Λ θ β γ N hQ q hβ z).1 z.2).2⟩))
    (loadToBotCorner Q Λ θ β γ N hQ hβ ∘ₗ
      LinearMap.codRestrict _ ((Ei).symm.toLinearMap ∘ₗ
        Submodule.inclusion inf_le_left)
      (fun n => by
        have hy : (Ei
            ((Ei).symm
              (Submodule.inclusion inf_le_left n)) : Inner) = n :=
          congrArg Subtype.val ((Ei).apply_symm_apply _)
        refine (blocksHeadAction_fixed_iff Q Λ θ β γ N hQ q
          ((Ei).symm
            (Submodule.inclusion inf_le_left n))).2 ?_
        change blocksHeadEnd Q Λ θ β γ N (botHeadIdem Q Λ θ β γ q)
          (Ei ((Ei).symm
            (Submodule.inclusion inf_le_left n)) : Inner) =
          (Ei ((Ei).symm
            (Submodule.inclusion inf_le_left n)) : Inner)
        rw [hy]
        exact n.2.2))
    (LinearMap.ext fun n => by
      apply Subtype.ext
      exact congrArg (fun y => ((y : ILi) : Inner))
        ((Ei).apply_symm_apply
          (Submodule.inclusion inf_le_left n)))
    (LinearMap.ext fun z => by
      apply Subtype.ext
      exact congrArg (fun y => ((y : LCi) : CSi))
        ((Ei).symm_apply_apply
          (botCornerToLoad Q Λ θ β γ N hQ hβ z)))

/-- The bottom corner equivalence is the identity shuffle coordinate. -/
theorem botCornerBlocksEquiv_apply (hβ : q.β = (αi).map cR)
    (z : botCorner (stendhalQ Q Λ) q Nₒ) :
    (botCornerBlocksEquiv Q Λ θ β γ N hQ hβ z : Inner) =
      (cutStandardShuffleEquiv Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) hQ
        (show CSi from (z : Nₒ)) : Sh → Inner) shufOne := by
  rw [botCornerBlocksEquiv, LinearEquiv.coe_ofLinearMap]
  rfl

/-- **The inverse is the identity-shuffle copy** `n ↦ 1 ⊗ n` of the inner input. -/
theorem botCornerBlocksEquiv_symm_apply (hβ : q.β = (αi).map cR)
    (n : botBlocksCorner Q Λ θ β γ N q) :
    ((botCornerBlocksEquiv Q Λ θ β γ N hQ hβ).symm n : Nₒ) =
      cutStandardUnit Q (blocksTailLabels Λ) β γ (BlocksInner Q Λ θ β γ N) (n : Inner) := by
  rw [botCornerBlocksEquiv, LinearEquiv.symm_ofLinearMap]
  exact cutIdentityCornerEquiv_symm_apply (concatSet αi δi)
    (fun u hu s hs n => concatIdem_smul_eq_zero_of_ne_one u hu s hs n)
    (Submodule.inclusion inf_le_left n)

end Corner

end Categorification.Stendhal
