/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomPermutation
import Categorification.WeightedKLR.RedStrands.BlockShuffleCrossing

/-!
# Mixed crossing products of bottom-permuted braid indices

Webster, arXiv:1309.3796v3, proof of Lemma 6.12, p. 66. A mixed
right ascent gives the next leading term when the right extension is
an eligible bottom-block index. The product and leading term differ
by shorter subwords projected to the same top and changed bottom.
With an original word of length at most one the product is exact.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open scoped BigOperators

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)

/-- Multiplication by a mixed right crossing has the swapped index as its
leading term, provided that permutation occurs among the bottom-block
indices. The dominance conclusion compares the two bottom loadings. -/
theorem braidColumnBottomBlockIndex_mixed_product (s : Seq μ)
    (n n' : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (hn' : (∑ r, (n' r + 1)) = m) (σ : Perm (Fin ℓ))
    (φ φ' : {φ : Perm (Fin m) // ProjectiveBlockIndex s φ})
    {j : ℕ} (hj : j + 1 < m)
    (hstep : braidColumnBottomBlockIndex n' hn' σ φ'.val =
      braidColumnBottomBlockIndex n hn σ φ.val * sadj m j)
    (hascent : braidColumnBottomBlockIndex n hn σ φ.val ⟨j, by omega⟩ <
      braidColumnBottomBlockIndex n hn σ φ.val ⟨j+1,hj⟩)
    {r : Fin ℓ} {i : I}
    (hr : ((braidColumnBottomBlockIndex n hn σ φ.val)⁻¹ • s).lbl ⟨j, by omega⟩ = .inr r)
    (hi : ((braidColumnBottomBlockIndex n hn σ φ.val)⁻¹ • s).lbl ⟨j+1,hj⟩ = .inl i)
    {u v : List ℕ} (hu : IsReduced m u) (hv : IsReduced m v)
    (hw : wordProd m u = braidColumnBottomBlockIndex n hn σ φ.val)
    (hw' : wordProd m v = braidColumnBottomBlockIndex n' hn' σ φ'.val) :
    let b := (braidColumnBottomBlockIndex n hn σ φ.val)⁻¹ • s
    let c := (braidColumnBottomBlockIndex n' hn' σ φ'.val)⁻¹ • s
    let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) s c
    let product := F (ψw u * e b) * F (ψ j * e c)
    let target := F (ψw v * e c)
    StendhalLT b c ∧
      product - target ∈
        (lowSpan k (stendhalQ Q Λ) μ (subProds m (u ++ [j])) (u.length - 1)).map f ∧
      (u.length ≤ 1 → product = target) := by
  intro b c f product target
  have hcut : c = sadj m j • b := by
    dsimp [b,c]
    rw [hstep, mul_inv_rev, sadj_inv, mul_smul]
  have hback : sadj m j • c = b := by rw [hcut, sadj_smul_smul]
  have hprod : wordProd m (u ++ [j]) = wordProd m v := by
    rw [wordProd_append, wordProd_singleton, hw, hw', hstep]
  have huj : IsReduced m (u ++ [j]) := by
    refine ⟨validWord_append.2 ⟨hu.1, validWord_cons.2 ⟨hj, validWord_nil m⟩⟩, ?_⟩
    rw [List.length_append, List.length_singleton, wordProd_append, wordProd_singleton,
      hu.2, hw, length_mul_sadj_of_lt hj hascent]
  have he : (e b : R) * (ψ j * e c) = ψ j * e c := by
    have h := e_mul_std (Q := Q) (Λ := Λ) [j] 1 c
    simpa only [wordProd_singleton, hback, ψw_cons, ψw_nil, mul_one, map_one] using h
  have hP : product = F (ψw u * ψ j * e c) := by
    calc
      _ = F ((ψw u * e b) * (ψ j * e c)) := (map_mul F _ _).symm
      _ = _ := congrArg F (by rw [mul_assoc (ψw u), he, mul_assoc])
  have htarget : (wordProd m v) • c = s := by
    rw [hw']
    exact smul_inv_smul _ _
  have hp (a : List ℕ) (ha : wordProd m a = wordProd m v) :
      f (ψw a * e c) = F (ψw a * e c) := by
    change F (e s * ((ψw a * e c) * e c)) = _
    rw [mul_assoc (ψw a), e_mul_self]
    have ha' : wordProd m a • c = s := ha ▸ htarget
    have h := e_mul_std (Q := Q) (Λ := Λ) a 1 c
    simpa only [ha', map_one, mul_one] using congrArg F h
  refine ⟨?_, ?_, ?_⟩
  · rw [hcut]
    exact stendhalLT_sadj hj hr hi (fun d h => lbl_eq_inr_unique h hr)
  · have hraw := braidEquiv_sub_mem_lowSpan
      (Q := stendhalQ Q Λ) (braidEquiv_of_isReduced huj hv hprod) huj.1 1 c
    have hlen : (u ++ [j]).length - 2 = u.length - 1 := by simp
    have hm := Submodule.mem_map_of_mem (f := f) hraw
    simp only [hlen, map_one, mul_one, map_sub] at hm
    rw [hp (u ++ [j]) hprod, hp v rfl] at hm
    simp only [ψw_append, ψw_cons, ψw_nil, mul_one] at hm
    rw [hP]
    exact hm
  · intro hshort
    rw [hP, rightCrossing_eq_of_short_reduced huj hv hprod hshort]

end Categorification.Stendhal
