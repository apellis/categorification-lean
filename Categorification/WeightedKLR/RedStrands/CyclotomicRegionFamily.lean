/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRegion
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.TwoRep.RouqFamilyPi

/-!
# The black action on region categories

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.25, black part. The region category of weight `μ`
is the product over multisets `ν` of red labels of the weight-`μ` spaces of the cyclotomic KLR
algebras with highest weight `Σ_{r ∈ ν} lam r` and cyclotomic polynomials `∏_{r ∈ ν} p r i`
(`region`). When each `p r i` is monic of degree `⟨h_i, lam r⟩`, the products of the cyclotomic
Rouquier families form a Rouquier family on the region categories (`regionFamily`), satisfying
Brundan's mixed upward relations and mixed inversion. Hence the Cautis–Lauda presentation acts
on the region categories (`regionPresCL`), black strand by black strand, as in Webster's
Theorem 4.25.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ℓ : ℕ} {p : Fin ℓ → I → k[X]}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {lam : Fin ℓ → X}

omit [DecidableEq I] in
theorem regionPoly_monic (hp : ∀ r i, (p r i).Monic) (ν : Multiset (Fin ℓ)) (i : I) :
    (regionPoly p ν i).Monic :=
  monic_multiset_prod_of_monic _ _ fun r _ => hp r i

omit [DecidableEq I] in
theorem regionPoly_natDegree (hp : ∀ r i, (p r i).Monic)
    (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
    (ν : Multiset (Fin ℓ)) (i : I) :
    ((regionPoly p ν i).natDegree : ℤ) = RD.pair (RD.iY i) (regionHighest lam ν) := by
  rw [regionPoly, natDegree_multiset_prod_of_monic _ (by simpa using fun r _ => hp r i),
    regionHighest, map_multiset_sum, Multiset.map_map, Multiset.map_map]
  push_cast [Nat.cast_multiset_sum, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun r _ => hpdeg r i

variable (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **The Rouquier family on the region categories**: the product over multisets `ν` of red
labels of the cyclotomic Rouquier families with highest weight `regionHighest lam ν` and
cyclotomic polynomials `regionPoly p ν`. -/
def regionFamily :
    RouqFamily (B := LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) RD :=
  RouqFamily.pi fun ν : Multiset (Fin ℓ) =>
    cyclotomicFamily.{u, v, w} hQ hlead (regionPoly_monic hp ν) RD (regionHighest lam ν)
      (regionPoly_natDegree RD hp hpdeg ν) hdeg

/-- The objects of the region family are the region categories. -/
theorem regionFamily_obj (μ : X) :
    (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).obj μ = region Q p RD lam μ := rfl

variable (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ,
    -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)

include hsupp in
/-- Brundan's mixed upward relations hold on the region categories. -/
theorem regionFamily_brundanUpKLR :
    BrundanUpKLR (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (cyclotomicScalars hQ hlead RD hdeg) :=
  RouqUpKLR.pi fun ν => cyclotomicFamily_brundanUpKLR hQ hlead (regionPoly_monic hp ν) RD
    (regionHighest lam ν) (regionPoly_natDegree RD hp hpdeg ν) hdeg hsupp

/-- Brundan's mixed inversion holds on the region categories. -/
theorem regionFamily_mixedInversion :
    BrundanMixedInversion (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg) :=
  RouqFamily.brundanMixedInversion_pi fun ν => cyclotomicFamily_mixedInversion RD
    (regionHighest lam ν) hQ hlead (regionPoly_monic hp ν) (regionPoly_natDegree RD hp hpdeg ν)
    hdeg

/-- **The black part of Webster's Theorem 4.25**: for Kang–Kashiwara families `Q` with
weighted homogeneous `Q_ij`, the Cautis–Lauda presentation with the scalars of `Q` acts on the
region categories, with `E_i` and `F_i` acting by cyclotomic induction and restriction on every
factor. -/
def regionPresCL (hhom : ∀ i j, i ≠ j →
      (Q i j).IsWeightedHomogeneous ![C.dot i i, C.dot j j] (-2 * C.dot i j)) :
    Pseudofunctor (RevBicat
      (KL3.Diagram.CL.presCL RD k (cyclotomicScalars hQ hlead RD hdeg)).Bicat)
      (LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) :=
  (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).presCLPseudofunctor
    (cyclotomicScalars hQ hlead RD hdeg)
    (regionFamily_brundanUpKLR RD hQ hlead hp hpdeg hdeg
      fun i j h => coeff_eq_zero_of_lt_of_hom C (hhom i j h))
    (regionFamily_mixedInversion RD hQ hlead hp hpdeg hdeg) (fun _ => rfl)
    (kkScalars_s_eq_zero C hQ _ hhom)

end Categorification.Stendhal
