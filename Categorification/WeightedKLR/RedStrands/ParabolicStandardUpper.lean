/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleLayer
import Categorification.WeightedKLR.RedStrands.TwoPieceLoading

/-!
# Loadings above a two-piece loading act by zero on a standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.20. Let `N` be a module over `T^{λ'}_θ ⊗ R^{λ_{ℓ+1}}_β` on which `e(c) ⊗ 1` acts
by zero for every red-ordered loading `c` strictly above `t` (for instance `S_t ⊠ R e(u)`).
Then on the standardization `S(N)` the idempotent `e(s)` acts by zero for every red-ordered
loading `s` strictly above the two-piece loading `t λ_{ℓ+1} u`.

The point is a count: such an `s` has at least `|θ| + ℓ` strands left of its last red strand,
so only the trivial shuffle contributes, `s` is a concatenation `c d`, and the comparison of
black counts forces `c` strictly above `t`.

## Main results

* `parabolicStandardAction_upper_eq_zero`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "μ" => stendhalWeight (ℓ+1) (θ+β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β
local notation "C" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)
local notation "N₀" => ParabolicInput Q Λ θ β N
local notation "ρ" => parabolicShuffleAction Q Λ θ β N
local notation "ρT" => parabolicStandardAction Q Λ θ β N hQ
local notation "π" => TensorProductAlgebra.mk Q Λ (θ+β)
local notation "π'" => TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ
local notation "q" => StendhalAlgebraAllOrders.ofKLR k Q Λ (θ+β)

variable {θ β} in
/-- A red-ordered loading strictly above `t λ_{ℓ+1} u` has its last red strand at position at
least `|θ| + ℓ`. -/
theorem card_le_redPos_last {t : Seq (stendhalWeight ℓ θ)} {u : Seq β} {s : Seq μ}
    (hs : IsRedOrdered s) (hlt : StendhalLT (twoPieceLoading θ β t u) s) :
    (α).card ≤ (redPos s (Fin.last ℓ)).val := by
  have h := sum_blackCount_add_le s hs θ.toFinset
  have hθ : ∑ i ∈ θ.toFinset, θ.count i ≤ ∑ i ∈ θ.toFinset, blackCount s (Fin.last ℓ) i :=
    Finset.sum_le_sum fun i _ => by
      simpa [blackCount_twoPieceLoading_last] using hlt.1 (Fin.last ℓ) i
  rw [Multiset.toFinset_sum_count_eq] at hθ
  have hα : (α).card = θ.card + ℓ := by simp [stendhalWeight]
  omega

variable {N}

include hQ in
private theorem upper_affine (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    (hN : ∀ (c : Seq (stendhalWeight ℓ θ)) (hc : IsRedOrdered c), StendhalLT t c → ∀ n : N,
      ((π' (StendhalAlgebra.e c hc) ⊗ₜ[k] (1 : C)) : parabolicFactorAlgebra Q Λ θ β) • n = 0)
    (s : Seq μ) (hs : IsRedOrdered s) (hlt : StendhalLT (twoPieceLoading θ β t u) s) :
    ρ (e (Seq.cast (Eq.symm H) s)) = 0 := by
  set s' := Seq.cast (Eq.symm H) s with hs'
  have his : Seq.cast H s' = s :=
    (show ∀ {a b : Multiset (I ⊕ Fin (ℓ+1))} (h : a=b) (x : Seq b),
      Seq.cast h (Seq.cast h.symm x) = x from fun h x => by subst h; rfl) H s
  let p : Fin (α+δ).card := Fin.cast (congrArg Multiset.card H).symm (redPos s (Fin.last ℓ))
  have hp : s'.lbl p = .inr (Fin.last ℓ) := lbl_redPos s (Fin.last ℓ)
  have hcard : (α).card ≤ p.val := card_le_redPos_last hs hlt
  apply LinearMap.ext; intro z
  apply (indDecomp (ν := α) (ν' := δ) (stendhalQ_swap_symm Q Λ hQ) N₀).injective
  funext w
  change indDecomp _ N₀ ((e s' : KLRAlgebra k S (α+δ)) • z) w = _
  rw [indDecomp_e_smul]
  have hz : ∀ n : N₀, concatIdem (Q := S) (w.1 • s') • n = 0 := by
    by_contra hn
    have he := parabolicShuffle_last_red Q Λ θ β N s' p hp w hn
    have he' := w.1.eq_symm_apply.mpr he
    have hw := lastRedShuffle_eq_one (Seq.card_add' α δ) w (by simp [stendhalWeight])
      (show (α).card ≤ (w.1.symm (Seq.posR α ⟨0,by simp [stendhalWeight]⟩)).val by
        rw [← he']; exact hcard)
    obtain ⟨a, b, hab, ha, -, -, hvb⟩ := parabolicShuffle_supported_input Q Λ θ β N s' w hn
    obtain ⟨a₀, rfl⟩ := (Seq.map_bijective (addRedColor_injective ℓ) _).surjective a
    have ha₀ := isRedOrdered_of_map_castSucc ha
    have hsc : s = concatLoading θ β a₀ b := by
      rw [← his, concatLoading, ← hab, hw, one_smul]
    rw [hsc] at hlt
    have htc := stendhalLT_of_concatLoading hvb hlt
    apply hn
    intro n
    change parabolicInputMap Q Λ θ β (concatIdem (w.1 • s')) • (n : N) = 0
    rw [hab, concatIdem_append]
    simp only [parabolicInputMap, Algebra.TensorProduct.map_tmul]
    rw [redSubfamilyProjection_e Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ a₀ ha₀,
      show (π' (StendhalAlgebra.e a₀ ha₀) ⊗ₜ[k] parabolicLastCyclotomic Q Λ β (e b) :
          parabolicFactorAlgebra Q Λ θ β) =
        (π' (StendhalAlgebra.e a₀ ha₀) ⊗ₜ[k] (1 : C)) *
          ((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ) ⊗ₜ[k]
            parabolicLastCyclotomic Q Λ β (e b)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
      mul_smul]
    exact hN a₀ ha₀ htc _
  rw [hz]
  change 0 = indDecomp _ N₀ 0 w
  rw [map_zero]; rfl

private theorem proj_ordered' (s : Seq μ) (hs : IsRedOrdered s) :
    orderProjection Q Λ (θ+β) (q (e s)) = StendhalAlgebra.e s hs :=
  Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))

/-- **Loadings above a two-piece loading act by zero** (Webster, arXiv:1309.3796v2, proof of
Prop. 5.20). If `e(c) ⊗ 1` kills `N` for every red-ordered `c` strictly above `t`, then `e(s)`
kills the standardization of `N` for every red-ordered `s` strictly above `t λ_{ℓ+1} u`. -/
theorem parabolicStandardAction_upper_eq_zero (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    (hN : ∀ (c : Seq (stendhalWeight ℓ θ)) (hc : IsRedOrdered c), StendhalLT t c → ∀ n : N,
      ((π' (StendhalAlgebra.e c hc) ⊗ₜ[k] (1 : C)) : parabolicFactorAlgebra Q Λ θ β) • n = 0)
    (s : Seq μ) (hs : IsRedOrdered s) (hlt : StendhalLT (twoPieceLoading θ β t u) s) :
    ρT (π (StendhalAlgebra.e s hs)) = 0 := by
  let s' := Seq.cast (Eq.symm H) s
  have his : Seq.cast H s' = s :=
    (show ∀ {a b : Multiset (I ⊕ Fin (ℓ+1))} (h : a=b) (x : Seq b),
      Seq.cast h (Seq.cast h.symm x) = x from fun h x => by subst h; rfl) H s
  rw [← proj_ordered' Q Λ θ β s hs, ← his, ← castKLR_e, parabolicStandardAction_affine]
  apply orderedShuffleAction_eq_zero_of_eq_zero
  exact upper_affine Q Λ θ β hQ t u hN s hs hlt

end Categorification.Stendhal
