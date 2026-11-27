/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDescent

/-!
# The shuffle decomposition of a partial standardization at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+r}}` (after Definition 5.4), in the induced
model `Stendhal.CutStandard`: the affine induced module modulo the part supported on loadings
whose red strands are out of order.

For a module `N` over the block algebra `D = T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)` we prove

  `𝕊(N) ≅ ⊕_u ε_u N`   (as `k`-modules),

the sum running over the shuffles `u` (minimal coset representatives for the two blocks), where
`ε_u = ∑_{s red-ordered} 1_{u s}` is an idempotent of the affine block algebra. So the partial
standardization is the sum of the shuffle diagrams `ψ_u` cut down by `ε_u`: exactly the shuffle
diagrams with no crossing of two red strands survive. This is the standard basis of a partial
standardization over its block algebra; Webster states no basis of a partial standardization,
and his Proposition 5.7 (exactness) follows from it. The proof combines the shuffle lemma for
the induced module (Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 2.16 and Lemma 2.20,
`KLR.KLRAlgebra.indDecomp`) with the identification of a quotient by a kernel with an image.

## Main definitions

* `Stendhal.cutShuffleIdem u`: the idempotent `ε_u = ∑_{s red-ordered} 1_{u s}`.
* `Stendhal.cutStandardShuffleEquiv`: `𝕊(N) ≅ {g : Shuffle → N | ∀ u, g u ∈ ε_u N}`.

## Main results

* `Stendhal.cutStandardShuffleEquiv_mkQ`: the class of `y` has coordinates `ε_u y_u`, with
  `y_u` the shuffle coordinates of `y` (`KLR.KLRAlgebra.indDecomp`).
* `Stendhal.cutStandardShuffleEquiv_e_smul`: a loading idempotent `e(s)` acts on the coordinate
  `u` through `1_{u s}`.
* `Stendhal.cutStandardShuffleEquiv_unit`: the identity-shuffle copy of `N` is the coordinate
  `u = 1`.
* `Stendhal.cutShuffleIdem_mem_range_iff`: `g u ∈ ε_u N` iff `ε_u g u = g u`.
* `Stendhal.cutShuffleIdem_one_smul`: `ε_1` acts as the identity on `N`.

Any commutative ring `k`, symmetric `Q`.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)
local notation "F" => cutOrderedLoadings (a := a) (r := r) θ β
local notation "B" => TensorKLR S α δ

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

local notation "N₀" => CutInput Q Λ θ β N
local notation "M" => CutShuffle Q Λ θ β N
local notation "V" => CutStandard Q Λ θ β N

/-- The idempotent `ε_u = ∑_{s red-ordered} 1_{u s}` of the affine block algebra cutting down
the shuffle `u`. -/
def cutShuffleIdem (u : Sh) : B := ∑ s ∈ F, concatIdem (Q := S) (u.1 • s)

/-- The idempotents `1_t` of the affine block algebra are orthogonal. -/
theorem concatIdem_mul_concatIdem (t t' : Seq (α + δ)) :
    (concatIdem (Q := S) t * concatIdem t' : B) = if t = t' then concatIdem t else 0 := by
  split_ifs with h
  · subst h
    exact (concatIdem_idem t).eq
  · rw [concatIdem, concatIdem, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun p' hp' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    rw [Algebra.TensorProduct.tmul_mul_tmul, e_mul_e, e_mul_e]
    split_ifs with h₁ h₂
    · exact absurd (hp.symm.trans (by rw [h₁, h₂, hp'])) h
    · rw [TensorProduct.tmul_zero]
    · rw [TensorProduct.zero_tmul]
    · rw [TensorProduct.zero_tmul]

theorem concatIdem_mul_cutShuffleIdem (u : Sh) (s : Seq (α + δ)) :
    (concatIdem (Q := S) (u.1 • s) * cutShuffleIdem Q Λ θ β u : B) =
      if s ∈ F then concatIdem (u.1 • s) else 0 := by
  rw [cutShuffleIdem, Finset.mul_sum]
  simp only [concatIdem_mul_concatIdem, smul_left_cancel_iff]
  exact Finset.sum_ite_eq F s _

theorem cutShuffleIdem_mul_concatIdem (u : Sh) (s : Seq (α + δ)) :
    (cutShuffleIdem Q Λ θ β u * concatIdem (Q := S) (u.1 • s) : B) =
      if s ∈ F then concatIdem (u.1 • s) else 0 := by
  rw [cutShuffleIdem, Finset.sum_mul]
  simp only [concatIdem_mul_concatIdem, smul_left_cancel_iff]
  exact Finset.sum_ite_eq' F s _

theorem cutShuffleIdem_idem (u : Sh) : IsIdempotentElem (cutShuffleIdem Q Λ θ β u) := by
  rw [IsIdempotentElem]
  conv_lhs => enter [2]; rw [cutShuffleIdem]
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun s hs => ?_).trans rfl
  simp only [cutShuffleIdem_mul_concatIdem, hs, ↓reduceIte]

/-- The action of `ε_u` on the input module, as a `k`-linear map. -/
def cutShuffleIdemMap (u : Sh) : N₀ →ₗ[k] N₀ :=
  DistribSMul.toLinearMap k N₀ (cutShuffleIdem Q Λ θ β u)

theorem cutShuffleIdemMap_apply (u : Sh) (n : N₀) :
    cutShuffleIdemMap Q Λ θ β N u n = cutShuffleIdem Q Λ θ β u • n := rfl

/-- The coordinates `(ε_u N)_u` of the partial standardization. -/
def cutShuffleCoords : Submodule k (Sh → N₀) :=
  Submodule.pi Set.univ fun u => LinearMap.range (cutShuffleIdemMap Q Λ θ β N u)

variable (hQ : KLRSymm Q)

local notation "Φ" => indDecomp (cutStendhalQ_symm Q Λ hQ) N₀
local notation "P" => cutShuffleAction Q Λ θ β N (eSum S F)

/-- On shuffle coordinates, the projection onto the red-ordered loadings acts by `ε_u`. -/
theorem indDecomp_eSum_smul (y : M) (u : Sh) :
    Φ (P y) u = cutShuffleIdem Q Λ θ β u • Φ y u := by
  change Φ (eSum S F • y) u = _
  rw [eSum, Finset.sum_smul, map_sum, Finset.sum_apply, cutShuffleIdem, Finset.sum_smul]
  exact Finset.sum_congr rfl fun s _ => indDecomp_e_smul _ _ s y u

/-- The image of the projection onto the red-ordered loadings, in shuffle coordinates. -/
theorem map_range_eSum :
    (LinearMap.range P).map (Φ).toLinearMap = cutShuffleCoords Q Λ θ β N := by
  ext g
  simp only [Submodule.mem_map, LinearMap.mem_range, cutShuffleCoords, Submodule.mem_pi,
    Set.mem_univ, true_implies]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ u
    exact ⟨Φ y u, (indDecomp_eSum_smul Q Λ θ β N hQ y u).symm⟩
  · intro h
    choose n hn using h
    refine ⟨P ((Φ).symm n), ⟨_, rfl⟩, funext fun u => ?_⟩
    change Φ (P ((Φ).symm n)) u = g u
    rw [indDecomp_eSum_smul Q Λ θ β N hQ, LinearEquiv.apply_symm_apply]
    exact hn u

/-- **The shuffle decomposition of the partial standardization at a cut**:
`𝕊(N) ≅ ⊕_u ε_u N` as `k`-modules, `u` running over the shuffles of the two blocks. -/
def cutStandardShuffleEquiv : V ≃ₗ[k] cutShuffleCoords Q Λ θ β N :=
  ((P).quotKerEquivRange.trans (LinearEquiv.submoduleMap (Φ) (LinearMap.range P))).trans
    (LinearEquiv.ofEq _ _ (map_range_eSum Q Λ θ β N hQ))

/-- The class of `y` has the shuffle coordinates `ε_u y_u`. -/
theorem cutStandardShuffleEquiv_mkQ (y : M) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ (Submodule.mkQ _ y) : Sh → N₀) u =
      cutShuffleIdem Q Λ θ β u • Φ y u :=
  indDecomp_eSum_smul Q Λ θ β N hQ y u

/-- A loading idempotent `e(s)` acts on the shuffle coordinate `u` through `1_{u s}`. -/
theorem cutStandardShuffleEquiv_e_smul (s : Seq (α + δ)) (y : M) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ (Submodule.mkQ _ ((e s : KLRAlgebra k S (α + δ)) • y)) :
      Sh → N₀) u =
      concatIdem (Q := S) (u.1 • s) •
        (cutStandardShuffleEquiv Q Λ θ β N hQ (Submodule.mkQ _ y) : Sh → N₀) u := by
  rw [cutStandardShuffleEquiv_mkQ, cutStandardShuffleEquiv_mkQ, indDecomp_e_smul, ← mul_smul,
    ← mul_smul, cutShuffleIdem_mul_concatIdem, concatIdem_mul_cutShuffleIdem]

/-- A coordinate lies in `ε_u N` iff it is fixed by `ε_u`. -/
theorem cutShuffleIdem_mem_range_iff (u : Sh) (n : N₀) :
    n ∈ LinearMap.range (cutShuffleIdemMap Q Λ θ β N u) ↔ cutShuffleIdem Q Λ θ β u • n = n := by
  refine ⟨?_, fun h => ⟨n, by rw [cutShuffleIdemMap_apply, h]⟩⟩
  rintro ⟨m, rfl⟩
  rw [cutShuffleIdemMap_apply, ← mul_smul, (cutShuffleIdem_idem Q Λ θ β u).eq]

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- The input module is supported on concatenations of red-ordered loadings. -/
private theorem concatIdem_smul_eq_zero_of_not_mem (s : Seq (α + δ)) (hs : s ∉ F) (n : N₀) :
    concatIdem (Q := S) s • n = 0 := by
  classical
  by_contra h
  have h' : ¬ ∀ m : N₀,
      concatIdem (Q := S) ((shufOne : Sh).1 • s) • m = 0 := by
    simpa only [shufOne, one_smul] using fun H => h (H n)
  obtain ⟨a', b', he, ha, hb, _, _⟩ := cutShuffle_supported_input Q Λ θ β N s shufOne h'
  simp only [shufOne, one_smul] at he
  exact hs (by simpa [cutOrderedLoadings, he] using cut_isRedOrdered_append θ β ha hb)

/-- The identity-shuffle unit has the shuffle coordinates of `u = 1`. -/
private theorem indDecomp_indShuffleUnit (n : N₀) :
    Φ (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀ n) = Pi.single shufOne n :=
  indDecomp_tmul_oneConcat (ν := α) (ν' := δ) (cutStendhalQ_symm Q Λ hQ) N₀ n

include hQ in
/-- `ε_1` acts as the identity on the input module. -/
theorem cutShuffleIdem_one_smul (n : N₀) : cutShuffleIdem Q Λ θ β (shufOne : Sh) • n = n := by
  have key := indDecomp_indShuffleUnit Q Λ θ β N hQ n
  have h : P (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀ n) =
      indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀ n :=
    indShuffle_eSum_unit (Q := S) (ν := α) (ν' := δ) N₀ F
      (concatIdem_smul_eq_zero_of_not_mem Q Λ θ β N) n
  have h3 := indDecomp_eSum_smul Q Λ θ β N hQ
    (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀ n) shufOne
  rw [h, key, Pi.single_eq_same] at h3
  exact h3.symm

/-- The identity-shuffle copy of the input is the shuffle coordinate `u = 1`. -/
theorem cutStandardShuffleEquiv_unit (n : N₀) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ (cutStandardUnit Q Λ θ β N n) : Sh → N₀) =
      Pi.single shufOne n := by
  funext u
  rw [show cutStandardUnit Q Λ θ β N n = Submodule.mkQ _
    (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀ n) from rfl,
    cutStandardShuffleEquiv_mkQ]
  refine (congrArg (fun g : Sh → N₀ => cutShuffleIdem Q Λ θ β u • g u)
    (indDecomp_indShuffleUnit Q Λ θ β N hQ n)).trans ?_
  by_cases hu : u = shufOne
  · subst hu
    simp only [Pi.single_eq_same]
    exact cutShuffleIdem_one_smul Q Λ θ β N hQ n
  · simp only [Pi.single_eq_of_ne hu, smul_zero]

end Categorification.Stendhal
