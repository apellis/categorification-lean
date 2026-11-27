/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongBaseChange
import Categorification.TwoRep.BlockSumCrossingBraid
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDotSlide
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownMates

/-!
# The quotient crossings of a red line are natural for downward crossings

Webster, arXiv:1309.3796v3, (4.4d), in the proof of Theorem 4.25. The quotient crossing
`z ⊗ n ↦ π(z) ⊗ n` of a downward black strand with a red line is the base change of induction
along the cyclotomic projections (`cyclotomicRedDownQuotient_eq_baseChange`). Base change is
compatible with composites of inductions and with the crossing `ψ`, which the projection sends
to `ψ`; so a red line passes through a downward crossing (`cyclotomicRedDownQuotient_cross`,
`cyclotomicRedDownQuotient_signedCross`). Assembling through the weight-space blocks
(`globalRedDownQuotient_cross_app`) and the region factors (`regionRedDownQuotient_cross`) gives
the hypothesis `DownQuotCrossNatural` for the region model (`regionDownQuotCrossNatural`), and
with it the naturality (4.4d) of the red/up crossings (`regionUpIsoCrossNatural`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial InductionAlong

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)

set_option backward.isDefEq.respectTransparency false in
/-- **The quotient crossing is base change of induction** along the cyclotomic projections. -/
theorem cyclotomicRedDownQuotient_eq_baseChange (i : I) {β γ : Multiset I} (h : {i} + β = γ) :
    cyclotomicRedDownQuotient.{u, v, w} Q hab i h =
      baseChange.{max u v, w} (cyclotomicRedProjection Q hab β).toRingHom
        (cyclotomicRedProjection Q hab γ).toRingHom
        (cyclotomicRedProjection_lastEmb Q hab i h) := by
  refine NatTrans.ext (funext fun M => ModuleCat.hom_ext (Ind.ext fun z n => ?_))
  change (cyclotomicRedDownQuotient Q hab i h).app M (Ind.tmul z n) = _
  rw [cyclotomicRedDownQuotient_tmul]
  rfl

variable (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ)
  (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ)

set_option backward.isDefEq.respectTransparency false in
/-- **A red line passes through a downward crossing** on blocks: the two ways of moving the
quotient crossings through `ψ` agree. -/
theorem cyclotomicRedDownQuotient_cross :
    Functor.whiskerRight (cyclotomicRedDownQuotient.{u, v, w} Q hab j h₁) (ind Q b i h₂) ≫
        Functor.whiskerLeft (ind Q a j h₁) (cyclotomicRedDownQuotient Q hab i h₂) ≫
        Functor.whiskerRight (cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
      Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (cross Q b i j h₁ h₂ h₃ h₄) ≫
        Functor.whiskerRight (cyclotomicRedDownQuotient Q hab i h₃) (ind Q b j h₄) ≫
        Functor.whiskerLeft (ind Q a i h₃) (cyclotomicRedDownQuotient Q hab j h₄) := by
  simp only [cyclotomicRedDownQuotient_eq_baseChange]
  have C1 := baseChange_comp.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab β).toRingHom (cyclotomicRedProjection Q hab δ).toRingHom
    (cyclotomicRedProjection_lastEmb Q hab j h₁) (cyclotomicRedProjection_lastEmb Q hab i h₂)
  have C2 := baseChange_comp.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab β').toRingHom (cyclotomicRedProjection Q hab δ).toRingHom
    (cyclotomicRedProjection_lastEmb Q hab i h₃) (cyclotomicRedProjection_lastEmb Q hab j h₄)
  have N := baseChange_natTrans.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab δ).toRingHom
    (fun x => (cyclotomicRedProjection_lastEmb Q hab i h₂ _).trans
      (congrArg _ (cyclotomicRedProjection_lastEmb Q hab j h₁ x)))
    (fun x => (cyclotomicRedProjection_lastEmb Q hab j h₄ _).trans
      (congrArg _ (cyclotomicRedProjection_lastEmb Q hab i h₃ x)))
    (intertwines_crossElt Q b i j h₁ h₂ h₃ h₄)
    (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄)
    (by simp only [crossElt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      cyclotomicRedProjection_mk])
  simp only [cross, Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% C1, ← reassoc_of% N]
  congr 2
  rw [← Functor.isoWhiskerLeft_inv, Iso.eq_inv_comp, Functor.isoWhiskerLeft_hom,
    ← Category.assoc, ← C2]
  simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id,
    Functor.whiskerRight_id']
  erw [Category.comp_id]

/-- **A red line passes through a downward crossing** on blocks, for the signed crossing of the
cyclotomic family. -/
theorem cyclotomicRedDownQuotient_signedCross :
    Functor.whiskerRight (cyclotomicRedDownQuotient.{u, v, w} Q hab j h₁) (ind Q b i h₂) ≫
        Functor.whiskerLeft (ind Q a j h₁) (cyclotomicRedDownQuotient Q hab i h₂) ≫
        Functor.whiskerRight (signedCross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
      Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (signedCross Q b i j h₁ h₂ h₃ h₄) ≫
        Functor.whiskerRight (cyclotomicRedDownQuotient Q hab i h₃) (ind Q b j h₄) ≫
        Functor.whiskerLeft (ind Q a i h₃) (cyclotomicRedDownQuotient Q hab j h₄) := by
  have key := cyclotomicRedDownQuotient_cross Q hab i j h₁ h₂ h₃ h₄
  by_cases hij : i = j
  · unfold signedCross
    rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true hij)]
    have hR : Functor.whiskerRight (-cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
        -Functor.whiskerRight (cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) := by
      ext M : 2
      exact (cyclotomicRedPullback Q hab δ).map_neg
    have hL : Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (-cross Q b i j h₁ h₂ h₃ h₄) =
        -Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (cross Q b i j h₁ h₂ h₃ h₄) := by
      ext M : 2
      rfl
    rw [hR, hL, Preadditive.comp_neg, Preadditive.comp_neg, Preadditive.neg_comp, key]
  · unfold signedCross
    rw [ite_eq_right_of_eq_false _ _ (eq_false hij), ite_eq_right_of_eq_false _ _ (eq_false hij)]
    exact key

section Hexagon

open CategoryTheory.Bicategory

universe w₁ v₁ u₂

variable {K : Type w₁} [CommRing K] {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : LinearCat.{w₁, v₁, u₂} K}
  {P₀ : X₀ ⟶ Y₀} {P₁ : X₁ ⟶ Y₁} {P₂ : X₂ ⟶ Y₂} {P₃ : X₃ ⟶ Y₃}
  {A₁ : X₀ ⟶ X₁} {A₂ : X₁ ⟶ X₂} {A₃ : X₀ ⟶ X₃} {A₄ : X₃ ⟶ X₂}
  {B₁ : Y₀ ⟶ Y₁} {B₂ : Y₁ ⟶ Y₂} {B₃ : Y₀ ⟶ Y₃} {B₄ : Y₃ ⟶ Y₂}

/-- A hexagon of 2-cells in `LinearCat`, moving a 1-morphism `P` through a 2-cell between
composites, holds when it holds on components. -/
theorem linearCat_hexagon_ext (q₁ : P₀ ≫ B₁ ⟶ A₁ ≫ P₁) (q₂ : P₁ ≫ B₂ ⟶ A₂ ≫ P₂)
    (q₃ : P₀ ≫ B₃ ⟶ A₃ ≫ P₃) (q₄ : P₃ ≫ B₄ ⟶ A₄ ≫ P₂) (cA : A₁ ≫ A₂ ⟶ A₃ ≫ A₄)
    (cB : B₁ ≫ B₂ ⟶ B₃ ≫ B₄)
    (H : ∀ N, CrossHexagon q₁.hom q₂.hom q₃.hom q₄.hom cA.hom cB.hom N) :
    (α_ _ _ _).inv ≫ q₁ ▷ B₂ ≫ (α_ _ _ _).hom ≫ A₁ ◁ q₂ ≫ (α_ _ _ _).inv ≫ cA ▷ P₂ ≫
        (α_ _ _ _).hom =
      P₀ ◁ cB ≫ (α_ _ _ _).inv ≫ q₃ ▷ B₄ ≫ (α_ _ _ _).hom ≫ A₃ ◁ q₄ := by
  apply ObjectProperty.hom_ext
  ext N
  change 𝟙 _ ≫ B₂.obj.map (q₁.hom.app N) ≫ 𝟙 _ ≫ q₂.hom.app (A₁.obj.obj N) ≫ 𝟙 _ ≫
      P₂.obj.map (cA.hom.app N) ≫ 𝟙 _ =
    cB.hom.app (P₀.obj.obj N) ≫ 𝟙 _ ≫ B₄.obj.map (q₃.hom.app N) ≫ 𝟙 _ ≫
      q₄.hom.app (A₃.obj.obj N)
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.id_comp]
  exact H N

end Hexagon

section Global

open CategoryTheory.Bicategory

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X) (i j : I)
  {x x₁ x₂ x₃ y y₁ y₂ y₃ : X}
  (hx₁ : x + RD.iX j = x₁) (hx₂ : x₁ + RD.iX i = x₂) (hx₃ : x + RD.iX i = x₃)
  (hx₄ : x₃ + RD.iX j = x₂)
  (hy₁ : y + RD.iX j = y₁) (hy₂ : y₁ + RD.iX i = y₂) (hy₃ : y + RD.iX i = y₃)
  (hy₄ : y₃ + RD.iX j = y₂)
  (e₀ : y + δ = x) (e₁ : y₁ + δ = x₁) (e₂ : y₂ + δ = x₂) (e₃ : y₃ + δ = x₃)

/-- **A red line passes through a downward crossing on weight spaces**, componentwise. -/
theorem globalRedDownQuotient_cross_app (N : (weightSpace.{u, v, w} Q a RD Λ x).carrier) :
    CrossHexagon (globalRedDownQuotient.{u, v, w} Q hab RD Λ δ j hx₁ hy₁ e₀ e₁).hom
      (globalRedDownQuotient Q hab RD Λ δ i hx₂ hy₂ e₁ e₂).hom
      (globalRedDownQuotient Q hab RD Λ δ i hx₃ hy₃ e₀ e₃).hom
      (globalRedDownQuotient Q hab RD Λ δ j hx₄ hy₄ e₃ e₂).hom
      (globalCross Q a RD Λ i j hx₁ hx₂ hx₃ hx₄).hom
      (globalCross Q b RD (Λ + δ) i j hy₁ hy₂ hy₃ hy₄).hom N := by
  unfold CrossHexagon
  exact
blockResCross_blockCross_app (blockSucc RD Λ j hx₁) (blockSucc RD Λ i hx₂)
    (blockSucc RD Λ i hx₃) (blockSucc RD Λ j hx₄) (blockSucc RD (Λ + δ) j hy₁)
    (blockSucc RD (Λ + δ) i hy₂) (blockSucc RD (Λ + δ) i hy₃) (blockSucc RD (Λ + δ) j hy₄)
    (redBlock RD Λ δ e₀) (redBlock RD Λ δ e₁) (redBlock RD Λ δ e₃) (redBlock RD Λ δ e₂)
    (blockSucc_redBlock RD Λ δ j hx₁ hy₁ e₀ e₁) (blockSucc_redBlock RD Λ δ i hx₂ hy₂ e₁ e₂)
    (blockSucc_redBlock RD Λ δ i hx₃ hy₃ e₀ e₃) (blockSucc_redBlock RD Λ δ j hx₄ hy₄ e₃ e₂)
    (blockSucc_comm RD Λ i j hx₁ hx₂ hx₃ hx₄) (blockSucc_comm RD (Λ + δ) i j hy₁ hy₂ hy₃ hy₄)
    (indBlock Q a RD Λ j hx₁) (indBlock Q a RD Λ i hx₂) (indBlock Q a RD Λ i hx₃)
    (indBlock Q a RD Λ j hx₄) (indBlock Q b RD (Λ + δ) j hy₁) (indBlock Q b RD (Λ + δ) i hy₂)
    (indBlock Q b RD (Λ + δ) i hy₃) (indBlock Q b RD (Λ + δ) j hy₄)
    (redPullbackBlock Q hab RD Λ δ e₀) (redPullbackBlock Q hab RD Λ δ e₁)
    (redPullbackBlock Q hab RD Λ δ e₃) (redPullbackBlock Q hab RD Λ δ e₂)
    (fun _ _ _ _ hb hd hb' hd' => signedCross Q a i j (blockSucc_eq RD Λ j hb)
      (blockSucc_eq RD Λ i hd) (blockSucc_eq RD Λ i hb') (blockSucc_eq RD Λ j hd'))
    (fun _ _ _ _ hb hd hb' hd' => signedCross Q b i j (blockSucc_eq RD (Λ + δ) j hb)
      (blockSucc_eq RD (Λ + δ) i hd) (blockSucc_eq RD (Λ + δ) i hb')
      (blockSucc_eq RD (Λ + δ) j hd'))
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab j (blockSucc_eq RD (Λ + δ) j hβ))
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab j (blockSucc_eq RD (Λ + δ) j hβ))
    (fun _ _ _ _ f₁ f₂ f₃ f₄ Z => NatTrans.congr_app (cyclotomicRedDownQuotient_signedCross Q hab
      i j (blockSucc_eq RD (Λ + δ) j f₁) (blockSucc_eq RD (Λ + δ) i f₂)
      (blockSucc_eq RD (Λ + δ) i f₃) (blockSucc_eq RD (Λ + δ) j f₄)) Z) N

/-- A red line passes through a downward crossing, for a red pullback into a highest weight
`Λ' = Λ + δ`, componentwise. -/
theorem redPullbackAtDownQuotient_cross_app {Λ' : X} (hΛ : Λ + δ = Λ')
    (N : (weightSpace.{u, v, w} Q a RD Λ x).carrier) :
    CrossHexagon (redPullbackAtDownQuotient.{u, v, w} Q RD hab Λ δ hΛ j hx₁ hy₁ e₀ e₁)
      (redPullbackAtDownQuotient Q RD hab Λ δ hΛ i hx₂ hy₂ e₁ e₂)
      (redPullbackAtDownQuotient Q RD hab Λ δ hΛ i hx₃ hy₃ e₀ e₃)
      (redPullbackAtDownQuotient Q RD hab Λ δ hΛ j hx₄ hy₄ e₃ e₂)
      (globalCross Q a RD Λ i j hx₁ hx₂ hx₃ hx₄).hom
      (globalCross Q b RD Λ' i j hy₁ hy₂ hy₃ hy₄).hom N := by
  subst hΛ
  exact globalRedDownQuotient_cross_app Q hab RD Λ δ i j hx₁ hx₂ hx₃ hx₄ hy₁ hy₂ hy₃ hy₄
    e₀ e₁ e₂ e₃ N

end Global

section Region

open CategoryTheory.Bicategory

variable {Q} {ℓ : ℕ} {p : Fin ℓ → I → k[X]}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {lam : Fin ℓ → X}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ,
    -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)

/-- The crossing of two downward strands in the region model: on each factor, the crossing of
the cyclotomic family. -/
def regionCross (i j : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX j = μ₁) (h₂ : μ₁ + RD.iX i = μ₂)
    (h₃ : μ + RD.iX i = μ₃) (h₄ : μ₃ + RD.iX j = μ₂) :
    regionDown.{u, v, w} Q p RD lam j h₁ ≫ regionDown Q p RD lam i h₂ ⟶
      regionDown Q p RD lam i h₃ ≫ regionDown Q p RD lam j h₄ :=
  ObjectProperty.homMk (blockResIdCross (downFactor Q p RD lam j h₁) (downFactor Q p RD lam i h₂)
    (downFactor Q p RD lam i h₃) (downFactor Q p RD lam j h₄) fun ν =>
      (globalCross Q (regionPoly p ν) RD (regionHighest lam ν) i j h₁ h₂ h₃ h₄).hom)

/-- The crossings of the region family are the region crossings. -/
theorem regionFamily_cross (i j : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX j = μ₁)
    (h₂ : μ₁ + RD.iX i = μ₂) (h₃ : μ + RD.iX i = μ₃) (h₄ : μ₃ + RD.iX j = μ₂) :
    (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).cross i j h₁ h₂ h₃ h₄ =
      regionCross RD i j h₁ h₂ h₃ h₄ :=
  rfl

/-- **A red line passes through a downward crossing in the region model** (Webster,
arXiv:1309.3796v3, (4.4d) read downward, proof of Theorem 4.25). -/
theorem regionRedDownQuotient_cross (r : Fin ℓ) (i j : I) {μ μi μj μij ρ ρi ρj ν : X}
    (f₁ : μi + RD.iX i = μ) (f₂ : μij + RD.iX j = μi) (hR : μij + lam r = ν)
    (q₁ : μi + lam r = ρi) (q₂ : ν + RD.iX j = ρi) (hr : μ + lam r = ρ)
    (q₃ : ρi + RD.iX i = ρ) (q₄ : ρj + RD.iX j = ρ) (q₅ : ν + RD.iX i = ρj)
    (g₁ : μj + RD.iX j = μ) (g₂ : μij + RD.iX i = μj) (g₃ : μj + lam r = ρj) :
    (α_ _ _ _).inv ≫ regionRedDownQuotient.{u, v, w} Q p RD lam r j f₂ hR q₁ q₂ ▷
        regionDown Q p RD lam i f₁ ≫ (α_ _ _ _).hom ≫
      regionDown Q p RD lam j q₂ ◁ regionRedDownQuotient Q p RD lam r i f₁ q₁ hr q₃ ≫
      (α_ _ _ _).inv ≫ regionCross RD i j q₂ q₃ q₅ q₄ ▷ regionRed Q p RD lam r hr ≫
        (α_ _ _ _).hom =
    regionRed Q p RD lam r hR ◁ regionCross RD i j f₂ f₁ g₂ g₁ ≫ (α_ _ _ _).inv ≫
      regionRedDownQuotient Q p RD lam r i g₂ hR g₃ q₅ ▷ regionDown Q p RD lam j g₁ ≫
      (α_ _ _ _).hom ≫
      regionDown Q p RD lam i q₅ ◁ regionRedDownQuotient Q p RD lam r j g₁ g₃ hr q₄ :=
  linearCat_hexagon_ext _ _ _ _ _ _ (blockResCrossRev_crossHexagon (fun ν => r ::ₘ ν)
    (redFactor Q p RD lam r hR) (redFactor Q p RD lam r q₁) (redFactor Q p RD lam r hr)
    (redFactor Q p RD lam r g₃)
    (downFactor Q p RD lam j q₂) (downFactor Q p RD lam i q₃) (downFactor Q p RD lam i q₅)
    (downFactor Q p RD lam j q₄)
    (downFactor Q p RD lam j f₂) (downFactor Q p RD lam i f₁) (downFactor Q p RD lam i g₂)
    (downFactor Q p RD lam j g₁)
    (redFactorDownQuotient Q p RD lam r j f₂ hR q₁ q₂)
    (redFactorDownQuotient Q p RD lam r i f₁ q₁ hr q₃)
    (redFactorDownQuotient Q p RD lam r i g₂ hR g₃ q₅)
    (redFactorDownQuotient Q p RD lam r j g₁ g₃ hr q₄)
    (fun ν => (globalCross Q (regionPoly p ν) RD (regionHighest lam ν) i j q₂ q₃ q₅ q₄).hom)
    (fun ν => (globalCross Q (regionPoly p ν) RD (regionHighest lam ν) i j f₂ f₁ g₂ g₁).hom)
    fun ν _ h Z => by
      subst h
      exact redPullbackAtDownQuotient_cross_app Q (regionPoly_dvd_cons p r ν) RD
        (regionHighest lam ν) (lam r) i j q₂ q₃ q₅ q₄ f₂ f₁ g₂ g₁ hR q₁ hr g₃
        (regionHighest_cons lam r ν) Z)

/-- **The quotient crossings `a′` of the region model are natural for downward crossings**
(Webster, arXiv:1309.3796v3, (4.4d) read downward, proof of Theorem 4.25). -/
theorem regionDownQuotCrossNatural :
    DoubleDiagram.DownQuotCrossNatural (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (fun r _ _ h => regionRed Q p RD lam r h)
      (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄) := by
  intro r i j _ _ _ _ _ _ _ _ f₁ f₂ hR q₁ q₂ hr q₃ q₄ q₅ g₁ g₂ g₃
  rw [regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r j f₂ hR q₁ q₂,
    regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i f₁ q₁ hr q₃,
    regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i g₂ hR g₃ q₅,
    regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r j g₁ g₃ hr q₄]
  exact regionRedDownQuotient_cross RD r i j f₁ f₂ hR q₁ q₂ hr q₃ q₄ q₅ g₁ g₂ g₃

include hsupp in
/-- **The red/up crossings of the region model are natural for upward crossings** (Webster,
arXiv:1309.3796v3, (4.4d), proof of Theorem 4.25). -/
theorem regionUpIsoCrossNatural :
    DoubleDiagram.UpIsoCrossNatural (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (fun r _ _ h => regionRed Q p RD lam r h)
      (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄)
      (cyclotomicScalars hQ hlead RD hdeg) :=
  (DoubleDiagram.upIsoCrossNatural_iff_downQuotCrossNatural _ _ _ _
    (regionFamily_brundanUpKLR RD hQ hlead hp hpdeg hdeg hsupp)
    (regionFamily_mixedInversion RD hQ hlead hp hpdeg hdeg)).2
    (regionDownQuotCrossNatural RD hQ hlead hp hpdeg hdeg)

end Region

end Categorification.Stendhal
