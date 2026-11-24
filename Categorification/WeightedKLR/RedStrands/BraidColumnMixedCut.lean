/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerBimodule
import Categorification.WeightedKLR.RedStrands.BraidColumnBlockPermutation

/-!
# Earlier products at a mixed cut in a braid column

Webster, arXiv:1309.3796v2, pp. 65–66, proof of Lemma 6.11. A mixed right
descent with a red immediately followed by a black gives a cut through a
strictly higher bottom loading when the swapped wiring is still eligible.
The diagram factors through that earlier product up to shorter subword
terms. For a word of length at most three and distinct endpoints, projection
kills the error because it has no crossings.
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

/-- At a mixed right descent, a cut at the higher bottom loading puts the
chosen braid-column diagram in the corresponding earlier eligible product
up to the shorter subword terms of the same loading pair. -/
theorem braidColumnBlockIndex_earlier_mixed_cut (s : Seq μ) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    (φ : {φ : Perm (Fin m) // ProjectiveBlockIndex s φ})
    {j : ℕ} (hj : j + 1 < m)
    (hφ' : ProjectiveBlockIndex s (φ.val * sadj m j))
    {r : Fin ℓ} {i : I}
    (hr : (φ.val⁻¹ • s).lbl ⟨j, by omega⟩ = .inr r)
    (hi : (φ.val⁻¹ • s).lbl ⟨j+1,hj⟩ = .inl i)
    (hd : braidColumnBlockIndex n hn σ φ.val ⟨j+1,hj⟩ <
      braidColumnBlockIndex n hn σ φ.val ⟨j,by omega⟩)
    {u v : List ℕ} (hu : IsReduced m u) (hv : IsReduced m v)
    (hw : wordProd m u = braidColumnBlockIndex n hn σ φ.val)
    (hw' : wordProd m v = (braidColumnIndexOfProjective s n hn σ
      ⟨φ.val * sadj m j, hφ'⟩).val)
    (p : MvPolynomial (Fin m) k) :
    let t := braidBlockPermutation n hn σ • s
    let b := φ.val⁻¹ • s
    let c := (φ.val * sadj m j)⁻¹ • s
    let f := braidColumnLoadingProjection (Q := Q) (Λ := Λ) t b
    StendhalLT b c ∧
      F (ψ j * pol p * e b) ∈ cornerBimodule (F (e c)) (F (e b)) ∧
      F (ψw u * pol p * e b) -
      F (ψw v * e c) * F (ψ j * pol p * e b) ∈
      (lowSpan k (stendhalQ Q Λ) μ (subProds m u) (u.length - 2)).map f := by
  intro t b c f
  let w := braidColumnBlockIndex n hn σ φ.val
  change wordProd m v = braidColumnBlockIndex n hn σ (φ.val * sadj m j) at hw'
  have hcut : c = sadj m j • b := by
    dsimp [b, c]
    rw [mul_inv_rev, sadj_inv, mul_smul]
  have hshort := length_mul_sadj_of_gt hj hd
  have hprod : wordProd m (v ++ [j]) = w := by
    rw [wordProd_append, wordProd_singleton, hw']
    change (braidBlockPermutation n hn σ * (φ.val * sadj m j)) * sadj m j = _
    rw [mul_assoc, mul_assoc, TypeA.sadj_mul_self, mul_one]
    rfl
  have hv' : wordProd m v = w * sadj m j := by
    rw [hw']
    exact (mul_assoc _ _ _).symm
  have hvj : IsReduced m (v ++ [j]) := by
    refine ⟨validWord_append.2 ⟨hv.1, validWord_cons.2 ⟨hj, validWord_nil m⟩⟩, ?_⟩
    rw [List.length_append, List.length_singleton, hv.2, hv', hshort, hprod]
  have hleft : w • b = t := by
    dsimp [w, b, t]
    rw [braidColumnBlockIndex_smul, smul_inv_smul]
  have hproject (a : List ℕ) (ha : wordProd m a = w) :
      f (ψw a * pol p * e b) = F (ψw a * pol p * e b) := by
    change F (e t * ((ψw a * pol p * e b) * e b)) = _
    rw [mul_assoc (ψw a * pol p), e_mul_self]
    rw [← hleft, ← ha, e_mul_std]
  have hmiddle : (e c : R) * (ψ j * pol p * e b) = ψ j * pol p * e b := by
    rw [hcut]
    simpa only [wordProd_singleton, ψw_cons, ψw_nil, mul_one] using
      (e_mul_std (Q := Q) (Λ := Λ) [j] p b)
  have hfactor : (ψw (v ++ [j]) * pol p * e b : R) =
      (ψw v * e c) * (ψ j * pol p * e b) := by
    rw [mul_assoc (ψw v), hmiddle, ψw_append]
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcut]
    exact stendhalLT_sadj hj hr hi (fun d h => lbl_eq_inr_unique h hr)
  · refine mem_cornerBimodule.mpr ⟨?_, ?_⟩
    · rw [← map_mul, hmiddle]
    · rw [← map_mul, mul_assoc (ψ j * pol p), e_mul_self]
  · have h := braidColumnBlockIndex_wordChange (Q := Q) (Λ := Λ) s n hn σ φ
      hu hvj hw hprod p
    change f (ψw u * pol p * e b) - f (ψw (v ++ [j]) * pol p * e b) ∈ _ at h
    rwa [hproject u hw, hproject (v ++ [j]) hprod, hfactor, map_mul F (ψw v * e c) (ψ j * pol p * e b)] at h


/-- Polynomial terms have no crossings and stay at a single loading.
A projected shorter-word error vanishes if its bound is at most one and the
top and bottom loadings are distinct. -/
theorem braidColumnLoadingProjection_map_lowSpan_eq_bot (top bottom : Seq μ)
    (hne : top ≠ bottom) (S : Set (Perm (Fin m))) (L : ℕ) (hL : L ≤ 1) :
    (lowSpan k (stendhalQ Q Λ) μ S L).map
      (braidColumnLoadingProjection (Q := Q) (Λ := Λ) top bottom) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [lowSpan, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, p, b, _, _, ha, rfl⟩, rfl⟩
  have ha₀ : a = [] := List.length_eq_zero_iff.1 (by omega)
  subst a
  change F (e top * (((ψw [] : R) * pol p * e b) * e bottom)) ∈
    (⊥ : Submodule k (ViolQuotient k Q Λ ν))
  rw [ψw_nil, one_mul, mul_assoc (pol p), e_mul_e]
  by_cases hb : b = bottom
  · subst b
    rw [ite_eq_left rfl, ← mul_assoc, (e_commute_pol _ p).eq, mul_assoc, e_mul_e,
      ite_eq_right hne, mul_zero, map_zero]
    exact zero_mem _
  · rw [ite_eq_right hb, mul_zero, mul_zero, map_zero]
    exact zero_mem _

end Categorification.Stendhal
