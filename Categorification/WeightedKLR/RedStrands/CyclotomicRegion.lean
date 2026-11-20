/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.PiBiproduct
import Categorification.WeightedKLR.RedStrands.CyclotomicRedGlobal

/-!
# The region categories of the cyclotomic representation of `𝒯`

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.25. Fix red labels `r` with highest weights
`lam r` and cyclotomic polynomials `p r`. A finite multiset `ν` of red labels has the highest
weight `Σ_{r ∈ ν} lam r` (`regionHighest`) and the cyclotomic polynomials
`∏_{r ∈ ν} p r i` (`regionPoly`). The category of a region of weight `μ` is the product over
all `ν` of the weight-`μ` spaces of the cyclotomic KLR algebras for `ν` (`region`): the weight
of a region does not determine the red lines on one side of it in general.

On these categories
* an upward black strand `i` acts by cyclotomic restriction on each factor (`regionUp`);
* a downward black strand `i` acts by cyclotomic induction on each factor (`regionDown`);
* a red line `r` pulls back from the factor `ν` to the factor `r ::ₘ ν` and is zero on the
  factors without `r` (`regionRed`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {ℓ : ℕ} (p : Fin ℓ → I → k[X])
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (lam : Fin ℓ → X)

/-- The cyclotomic polynomials of a multiset of red labels. -/
def regionPoly (ν : Multiset (Fin ℓ)) (i : I) : k[X] := (ν.map fun r => p r i).prod

/-- The highest weight of a multiset of red labels. -/
def regionHighest (ν : Multiset (Fin ℓ)) : X := (ν.map lam).sum

omit [DecidableEq I] in
theorem regionPoly_cons (r : Fin ℓ) (ν : Multiset (Fin ℓ)) (i : I) :
    regionPoly p (r ::ₘ ν) i = p r i * regionPoly p ν i := by
  simp [regionPoly]

omit [DecidableEq I] in
theorem regionPoly_dvd_cons (r : Fin ℓ) (ν : Multiset (Fin ℓ)) (i : I) :
    regionPoly p ν i ∣ regionPoly p (r ::ₘ ν) i :=
  ⟨p r i, by rw [regionPoly_cons, mul_comm]⟩

theorem regionHighest_cons (r : Fin ℓ) (ν : Multiset (Fin ℓ)) :
    regionHighest lam ν + lam r = regionHighest lam (r ::ₘ ν) := by
  simp [regionHighest, add_comm]

/-- **The category of a region of weight `μ`**: the product over all multisets `ν` of red labels
of the weight-`μ` spaces of the cyclotomic KLR algebras for `ν`. -/
abbrev region (μ : X) : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k :=
  LinearCat.of k (∀ ν : Multiset (Fin ℓ),
    weightSpace.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) μ)

instance (a : I → k[X]) (Λ x : X) :
    Limits.HasFiniteBiproducts (weightSpace.{u, v, w} Q a RD Λ x) := by
  change Limits.HasFiniteBiproducts (∀ β : WeightBlocks RD Λ x,
    ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
  infer_instance

/-! ### Black strands -/

/-- The factors of an upward black strand: cyclotomic restriction. -/
abbrev upFactor (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂) (ν ν' : Multiset (Fin ℓ))
    (hν : ν = ν') :
    weightSpace.{u, v, w} Q (regionPoly p ν') RD (regionHighest lam ν') μ₂ ⥤
      weightSpace.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) μ := by
  subst hν
  exact (globalF.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) i h).obj

/-- The factors of a downward black strand: cyclotomic induction. -/
abbrev downFactor (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂) (ν ν' : Multiset (Fin ℓ))
    (hν : ν = ν') :
    weightSpace.{u, v, w} Q (regionPoly p ν') RD (regionHighest lam ν') μ ⥤
      weightSpace.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) μ₂ := by
  subst hν
  exact (globalE.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) i h).obj

instance upFactor_additive (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : ν = ν') :
    (upFactor Q p RD lam i h ν ν' hν).Additive := by
  subst hν; exact inferInstanceAs (globalF Q (regionPoly p ν) RD _ i h).obj.Additive

instance upFactor_linear (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : ν = ν') :
    (upFactor Q p RD lam i h ν ν' hν).Linear k := by
  subst hν; exact inferInstanceAs ((globalF Q (regionPoly p ν) RD _ i h).obj.Linear k)

instance downFactor_additive (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : ν = ν') :
    (downFactor Q p RD lam i h ν ν' hν).Additive := by
  subst hν; exact inferInstanceAs (globalE Q (regionPoly p ν) RD _ i h).obj.Additive

instance downFactor_linear (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : ν = ν') :
    (downFactor Q p RD lam i h ν ν' hν).Linear k := by
  subst hν; exact inferInstanceAs ((globalE Q (regionPoly p ν) RD _ i h).obj.Linear k)

/-- **An upward black strand `i`** between the regions `μ` (left) and `μ + i_X` (right):
cyclotomic restriction on every factor. -/
def regionUp (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂) :
    region.{u, v, w} Q p RD lam μ₂ ⟶ region Q p RD lam μ :=
  LinearCat.LinFun.of (blockRes id (upFactor Q p RD lam i h))

/-- **A downward black strand `i`** between the regions `μ + i_X` (left) and `μ` (right):
cyclotomic induction on every factor. -/
def regionDown (i : I) {μ μ₂ : X} (h : μ + RD.iX i = μ₂) :
    region.{u, v, w} Q p RD lam μ ⟶ region Q p RD lam μ₂ :=
  LinearCat.LinFun.of (blockRes id (downFactor Q p RD lam i h))

/-! ### Red lines -/

/-- Red pullback on weight spaces into the weight space of a highest weight `Λ'` equal to
`Λ + δ`. -/
abbrev redPullbackAt {a b : I → k[X]} (hab : ∀ i, a i ∣ b i) (Λ δ : X) {Λ' : X}
    (hΛ : Λ + δ = Λ') {x y : X} (h : y + δ = x) :
    weightSpace.{u, v, w} Q a RD Λ x ⥤ weightSpace Q b RD Λ' y := by
  subst hΛ
  exact (globalRedPullback.{u, v, w} Q hab RD Λ δ h).obj

instance redPullbackAt_additive {a b : I → k[X]} (hab : ∀ i, a i ∣ b i) (Λ δ : X) {Λ' : X}
    (hΛ : Λ + δ = Λ') {x y : X} (h : y + δ = x) :
    (redPullbackAt Q RD hab Λ δ hΛ h).Additive := by
  subst hΛ; exact inferInstanceAs (globalRedPullback Q hab RD Λ δ h).obj.Additive

instance redPullbackAt_linear {a b : I → k[X]} (hab : ∀ i, a i ∣ b i) (Λ δ : X) {Λ' : X}
    (hΛ : Λ + δ = Λ') {x y : X} (h : y + δ = x) :
    (redPullbackAt Q RD hab Λ δ hΛ h).Linear k := by
  subst hΛ; exact inferInstanceAs ((globalRedPullback Q hab RD Λ δ h).obj.Linear k)

/-- The factors of a red line `r`: pullback from the factor `ν` to the factor `r ::ₘ ν`. -/
abbrev redFactor (r : Fin ℓ) {μ μ₂ : X} (h : μ + lam r = μ₂) (ν ν' : Multiset (Fin ℓ))
    (hν : r ::ₘ ν = ν') :
    weightSpace.{u, v, w} Q (regionPoly p ν) RD (regionHighest lam ν) μ₂ ⥤
      weightSpace.{u, v, w} Q (regionPoly p ν') RD (regionHighest lam ν') μ := by
  subst hν
  exact redPullbackAt Q RD (regionPoly_dvd_cons p r ν) _ (lam r) (regionHighest_cons lam r ν) h

instance redFactor_additive (r : Fin ℓ) {μ μ₂ : X} (h : μ + lam r = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : r ::ₘ ν = ν') :
    (redFactor Q p RD lam r h ν ν' hν).Additive := by
  subst hν; dsimp only [redFactor]; infer_instance

instance redFactor_linear (r : Fin ℓ) {μ μ₂ : X} (h : μ + lam r = μ₂)
    (ν ν' : Multiset (Fin ℓ)) (hν : r ::ₘ ν = ν') :
    (redFactor Q p RD lam r h ν ν' hν).Linear k := by
  subst hν; dsimp only [redFactor]; infer_instance

instance (r : Fin ℓ) (ν' : Multiset (Fin ℓ)) :
    Subsingleton {ν : Multiset (Fin ℓ) // r ::ₘ ν = ν'} :=
  ⟨fun a b => Subtype.ext (Multiset.cons_inj_right r |>.mp (a.2.trans b.2.symm))⟩

instance (r : Fin ℓ) (ν' : Multiset (Fin ℓ)) :
    Finite {ν : Multiset (Fin ℓ) // r ::ₘ ν = ν'} :=
  Finite.of_subsingleton

/-- **A red line `r`** between the regions `μ` (left) and `μ + lam r` (right): pullback along
the cyclotomic quotients from the factor `ν` to the factor `r ::ₘ ν`, and zero on the factors
without `r` (Webster, arXiv:1309.3796v3, Theorem 4.25, the functor `I^λ`). -/
def regionRed (r : Fin ℓ) {μ μ₂ : X} (h : μ + lam r = μ₂) :
    region.{u, v, w} Q p RD lam μ₂ ⟶ region Q p RD lam μ :=
  LinearCat.LinFun.of (blockSum (fun ν => r ::ₘ ν) (redFactor Q p RD lam r h))

end Categorification.Stendhal
