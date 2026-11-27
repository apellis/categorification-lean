/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicGlobalCapTensor
import Categorification.WeightedKLR.RedStrands.CyclotomicRegion

/-!
# The red/down dot crossing and the leftward caps

Webster, arXiv:1309.3796v3, §4.6, proof of Theorem 4.25. For a red line with cyclotomic
parameters `b i = X ^ d * a i`, the red/down dot crossing `E_i I^δ ⟶ I^δ E_i`
(`globalRedDotCrossing`) slides through the leftward caps `E_i F_i ⟶ 1` of Brundan,
arXiv:1501.00350v1, (1.15), (1.17): the dot crossing followed by the upstairs cap is the red/up
crossing followed by the red pullback of the downstairs cap (`globalRedDotCrossing_capL_app`,
`redPullbackAtDotCrossing_capL`). On corner tensors the dot crossing sends `π(z) ⊗ n` to
`z y^d ⊗ n` (`dotCrossing_cornerTensor`); the caps act by the opposite caps
(`globalLoc_capL_capTensor`), which the red projection intertwines
(`redProjection_cyclotomicOppositeCap`).

This identifies the red/down dot crossing as the mate of the red/up crossing under the left
adjunctions `F_i ⊣ E_i`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra CyclotomicAction Polynomial InductionAlong
open scoped ModuleCat.Algebra

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]}
  (hab : ∀ i, a i ∣ b i) (i : I) (β : Multiset I) (d : ℕ)

local notation "Si" => (Singleton.singleton i : Multiset I)

/-- The red projection of two-sided corners is onto. -/
theorem cornerRedProjection_surjective :
    Function.Surjective (cornerRedProjection Q i hab β) := by
  intro c
  obtain ⟨y, hy⟩ := cyclotomicRedProjection_surjective Q hab (Si + β) c.val
  have he := AbsentColour.cyclotomicLast_one Q i b β
  have he' := AbsentColour.cyclotomicLast_one Q i a β
  have hi := AbsentColour.lastIdem_mul Q i b β
  let e := AbsentColour.lastIdem Q i b β
  refine ⟨⟨e * y * e, ?_, ?_⟩, Subtype.ext ?_⟩
  · rw [← he]
    change e * (e * y * e) = e * y * e
    rw [← mul_assoc, ← mul_assoc, hi]
  · rw [← he]
    change (e * y * e) * e = e * y * e
    rw [mul_assoc, hi]
  · change cyclotomicRedProjection Q hab (Si + β) (e * y * e) = c.val
    have hp : cyclotomicRedProjection Q hab (Si + β) e = AbsentColour.lastIdem Q i a β := by
      change cyclotomicRedProjection Q hab (Si + β) (AbsentColour.cyclotomicLast Q i b β 1) =
        AbsentColour.cyclotomicLast Q i a β 1
      rw [he, he', cyclotomicRedProjection_mk]
    rw [map_mul, map_mul, hp, hy]
    change AbsentColour.cyclotomicLast Q i a β 1 * c.val * AbsentColour.cyclotomicLast Q i a β 1 = _
    rw [he', c.2.1, c.2.2]

variable (hi : b i = X ^ d * a i)

set_option backward.isDefEq.respectTransparency false in
/-- **The red/down dot crossing on corner tensors**: after the red/up crossing, it sends
`π(z) ⊗ n` to `z y^d ⊗ n`. -/
theorem dotCrossing_cornerTensor (N : ModuleCat.{max (max u v) w} (CycKLR k Q a β))
    (c : AbsentColour.Corner Q i b β) (n : N) :
    ((res Q b i rfl).map ((cyclotomicRedDotCrossing.{u, v, w} Q hab i rfl d hi).app N)).hom
      (((cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).inv.app
        ((ind Q a i rfl).obj N)).hom ((resIndIso.{u, v, w} i β N).inv.hom
          ((AbsentColour.resIndEquiv Q i a β N).symm
            (BalancedTensor.tmul (cornerRedProjection Q i hab β c) n)))) =
      (resIndIso.{u, v, w} i β ((cyclotomicRedPullback Q hab β).obj N)).inv.hom
        ((AbsentColour.resIndEquiv Q i b β _).symm
          (BalancedTensor.tmul (cornerDotPow Q i β b d c) n)) := by
  apply Res.ext
  change (cyclotomicRedDotCrossing.{u, v, w} Q hab i rfl d hi).app N
    (Ind.tmul (cyclotomicRedCornerProjection Q hab i rfl ⟨c.1, by
      change c.1 * AbsentColour.cyclotomicLast Q i b β 1 = c.1
      rw [AbsentColour.cyclotomicLast_one]; exact c.2.2⟩) n) = _
  rw [cyclotomicRedDotCrossing_tmul]
  refine congrArg (fun z => Ind.tmul (N := (cyclotomicRedPullback Q hab β).obj N) z n)
    (Subtype.ext ?_)
  change c.1 * dotElt Q b i rfl ^ d * lastEmb Q b i rfl 1 = c.1 * dotElt Q b i rfl ^ d
  have h2 := (cornerDotPow Q i β b d c).2.2
  rw [← AbsentColour.cyclotomicLast_one] at h2
  exact h2

section Global

open TwoRep QuantumGroup

universe u₁

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X)
  {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂)
  (h : y + δ = x) (h₂ : y₂ + δ = x₂)

theorem globalF_map_app {M M' : weightSpace.{u, v, w} Q b RD (Λ + δ) y₂} (f : M ⟶ M')
    (β : WeightBlocks RD (Λ + δ) y) :
    ((globalF Q b RD (Λ + δ) i hy).obj.map f) β =
      (res Q b i (blockSucc_eq RD (Λ + δ) i (rfl : blockSucc RD (Λ + δ) i hy β = _))).map
        (f (blockSucc RD (Λ + δ) i hy β)) := rfl

theorem globalRedDotCrossing_app (X₀ : weightSpace.{u, v, w} Q a RD Λ x)
    (d' : WeightBlocks RD (Λ + δ) y₂) :
    (globalRedDotCrossing.{u, v, w} Q hab RD Λ δ i hx hy h h₂ d hi).hom.app X₀ d' =
      blockResCrossRevApp (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
        (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
        (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
        (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
        (fun _ _ hβ => cyclotomicRedDotCrossing.{u, v, w} Q hab i
          (blockSucc_eq RD (Λ + δ) i hβ) d hi) X₀ d' := rfl

theorem globalRedPullbackResIso_inv_app (N : weightSpace.{u, v, w} Q a RD Λ x₂)
    (β : WeightBlocks RD (Λ + δ) y) :
    ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).inv.hom.app N) β =
      (cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).inv.app
        (N (redBlock RD Λ δ h₂ (blockSucc RD (Λ + δ) i hy β))) := rfl

theorem globalRedPullbackResIso_hom_app (N : weightSpace.{u, v, w} Q a RD Λ x₂)
    (β : WeightBlocks RD (Λ + δ) y) :
    ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).hom.hom.app N) β =
      (cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).hom.app
        (N (redBlock RD Λ δ h₂ (blockSucc RD (Λ + δ) i hy β))) := rfl

theorem globalRedPullback_map_app {M M' : weightSpace.{u, v, w} Q a RD Λ x} (f : M ⟶ M')
    (β : WeightBlocks RD (Λ + δ) y) :
    ((globalRedPullback Q hab RD Λ δ h).obj.map f) β =
      (cyclotomicRedPullback Q hab β.1).map (f (redBlock RD Λ δ h β)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem dotCrossing_cupIso (X₀ : weightSpace.{u, v, w} Q a RD Λ x)
    (β : WeightBlocks RD (Λ + δ) y) :
    (cyclotomicRedPullback Q hab β.1).map (cupIso Q a RD Λ i hx X₀ (redBlock RD Λ δ h β)).hom ≫
        ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).inv.hom.app
          ((globalE Q a RD Λ i hx).obj.obj X₀)) β ≫
        ((globalF Q b RD (Λ + δ) i hy).obj.map
          ((globalRedDotCrossing.{u, v, w} Q hab RD Λ δ i hx hy h h₂ d hi).hom.app X₀)) β =
      (cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).inv.app
          ((ind Q a i rfl).obj (X₀ (redBlock RD Λ δ h β))) ≫
        (res Q b i rfl).map ((cyclotomicRedDotCrossing.{u, v, w} Q hab i rfl d hi).app
          (X₀ (redBlock RD Λ δ h β))) ≫
        (cupIso Q b RD (Λ + δ) i hy ((globalRedPullback Q hab RD Λ δ h).obj.obj X₀) β).hom := by
  rw [globalF_map_app, globalRedDotCrossing_app, globalRedPullbackResIso_inv_app]
  have hn := (cyclotomicRedPullbackResIso.{u, v, w} Q hab i (rfl : {i} + β.1 = _)).inv.naturality
    (blockι (blockSucc RD Λ i hx) (indBlock Q a RD Λ i hx) X₀ ⟨redBlock RD Λ δ h β, rfl⟩)
  erw [reassoc_of% hn, ← Functor.map_comp, map_ι_blockResCrossRevApp (blockSucc RD Λ i hx)
    (blockSucc RD (Λ + δ) i hy) (redBlock RD Λ δ h) (redBlock RD Λ δ h₂)
    (blockSucc_redBlock RD Λ δ i hx hy h h₂) (indBlock Q a RD Λ i hx)
    (indBlock Q b RD (Λ + δ) i hy) (redPullbackBlock Q hab RD Λ δ h)
    (redPullbackBlock Q hab RD Λ δ h₂) _
    (fun d' => (fibreMap_redBlock_bijective RD Λ δ i hx hy h h₂ d').1) X₀ ⟨β, rfl⟩,
    Functor.map_comp]
  rfl

variable (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)
  (hΛa : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hΛb : ∀ i, ((b i).natDegree : ℤ) = RD.pair (RD.iY i) (Λ + δ))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option backward.isDefEq.respectTransparency false in
/-- **The red/down dot crossing slides through the leftward caps** (Webster, arXiv:1309.3796v3,
§4.6, proof of Theorem 4.25), at every block: the dot crossing followed by the upstairs cap is
the red/up crossing followed by the red pullback of the downstairs cap. -/
theorem globalRedDotCrossing_capL_app (X₀ : weightSpace.{u, v, w} Q a RD Λ x)
    (β : WeightBlocks RD (Λ + δ) y) :
    ((globalF Q b RD (Λ + δ) i hy).obj.map
        ((globalRedDotCrossing.{u, v, w} Q hab RD Λ δ i hx hy h h₂ d hi).hom.app X₀)) β ≫
      ((globalLoc.{u, v, w} RD (Λ + δ) hQ hlead hb hΛb hdeg i (sub_add_cancel y (RD.iX i))
        hy).capL.hom.app ((globalRedPullback Q hab RD Λ δ h).obj.obj X₀)) β =
    ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).hom.hom.app
        ((globalE Q a RD Λ i hx).obj.obj X₀)) β ≫
      ((globalRedPullback Q hab RD Λ δ h).obj.map
        ((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛa hdeg i (sub_add_cancel x (RD.iX i))
          hx).capL.hom.app X₀)) β := by
  have hie : ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).inv.hom.app
      ((globalE Q a RD Λ i hx).obj.obj X₀)) β ≫
      ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).hom.hom.app
        ((globalE Q a RD Λ i hx).obj.obj X₀)) β = 𝟙 _ := by
    rw [globalRedPullbackResIso_inv_app, globalRedPullbackResIso_hom_app]
    exact Iso.inv_hom_id_app _ _
  have hei : ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).hom.hom.app
      ((globalE Q a RD Λ i hx).obj.obj X₀)) β ≫
      ((globalRedPullbackResIso.{u, v, w} Q hab RD Λ δ i hx hy h h₂).inv.hom.app
        ((globalE Q a RD Λ i hx).obj.obj X₀)) β = 𝟙 _ := by
    rw [globalRedPullbackResIso_inv_app, globalRedPullbackResIso_hom_app]
    exact Iso.hom_inv_id_app _ _
  let eβ : _ ≅ _ := ⟨_, _, hie, hei⟩
  rw [← ((cyclotomicRedPullback Q hab β.1).mapIso
    (cupIso Q a RD Λ i hx X₀ (redBlock RD Λ δ h β)) ≪≫ eβ).cancel_iso_hom_left]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eβ]
  rw [Category.assoc, Category.assoc, reassoc_of% (dotCrossing_cupIso Q hab i d hi RD Λ δ hx hy h h₂ X₀ β),
    reassoc_of% hie, globalRedPullback_map_app, ← Functor.map_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ : ∃ t, (resIndIso.{u, v, w} i β.1 (X₀ (redBlock RD Λ δ h β))).inv.hom
      ((AbsentColour.resIndEquiv Q i a β.1 _).symm t) = u :=
    ⟨AbsentColour.resIndEquiv Q i a β.1 _
      ((resIndIso.{u, v, w} i β.1 (X₀ (redBlock RD Λ δ h β))).hom.hom u), by
        rw [LinearEquiv.symm_apply_apply]
        change ((resIndIso.{u, v, w} i β.1 (X₀ (redBlock RD Λ δ h β))).hom ≫
          (resIndIso.{u, v, w} i β.1 (X₀ (redBlock RD Λ δ h β))).inv).hom u = u
        rw [Iso.hom_inv_id]
        rfl⟩
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul c n =>
    obtain ⟨c, rfl⟩ := cornerRedProjection_surjective Q hab i β.1 c
    have L := globalLoc_capL_capTensor RD (Λ + δ) hQ hlead hb hΛb hdeg i
      (sub_add_cancel y (RD.iX i)) hy ((globalRedPullback Q hab RD Λ δ h).obj.obj X₀) β
      (cornerDotPow Q i β.1 b d c) n
    have R := globalLoc_capL_capTensor RD Λ hQ hlead ha hΛa hdeg i
      (sub_add_cancel x (RD.iX i)) hx X₀ (redBlock RD Λ δ h β)
      (cornerRedProjection Q i hab β.1 c) n
    have M := dotCrossing_cornerTensor Q hab i β.1 d hi (X₀ (redBlock RD Λ δ h β)) c n
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [M]
    refine L.trans (Eq.trans ?_ R.symm)
    change cyclotomicRedProjection Q hab β.1 _ • n = _
    rw [redProjection_cyclotomicOppositeCap Q i β.1 hab hQ hlead ha hb RD Λ (Λ + δ) (hΛa i)
      (hΛb i) (hdeg i) d hi c]


end Global


section RedPullbackAt

open TwoRep QuantumGroup

universe u₁

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X)
  {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂)
  (h : y + δ = x) (h₂ : y₂ + δ = x₂)
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)
  (hΛa : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **The red/down dot crossing slides through the leftward caps**, for a red pullback into a
highest weight `Λ' = Λ + δ` (Webster, arXiv:1309.3796v3, §4.6, proof of Theorem 4.25). -/
theorem redPullbackAtDotCrossing_capL {Λ' : X} (hΛ : Λ + δ = Λ')
    (hΛb : ∀ i, ((b i).natDegree : ℤ) = RD.pair (RD.iY i) Λ')
    (X₀ : weightSpace.{u, v, w} Q a RD Λ x) :
    (globalF Q b RD Λ' i hy).obj.map
        ((redPullbackAtDotCrossing.{u, v, w} Q RD hab Λ δ hΛ i hx hy h h₂ d hi).app X₀) ≫
      (globalLoc.{u, v, w} RD Λ' hQ hlead hb hΛb hdeg i (sub_add_cancel y (RD.iX i))
        hy).capL.hom.app ((redPullbackAt Q RD hab Λ δ hΛ h).obj X₀) =
    (redPullbackAtResIso.{u, v, w} Q RD hab Λ δ hΛ i hx hy h h₂).hom.app
        ((globalE Q a RD Λ i hx).obj.obj X₀) ≫
      (redPullbackAt Q RD hab Λ δ hΛ h).map
        ((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛa hdeg i (sub_add_cancel x (RD.iX i))
          hx).capL.hom.app X₀) := by
  subst hΛ
  funext β
  exact globalRedDotCrossing_capL_app Q hab i d hi RD Λ δ hx hy h h₂ hQ hlead ha hb hΛa hΛb hdeg
    X₀ β

end RedPullbackAt

end Categorification.Stendhal
