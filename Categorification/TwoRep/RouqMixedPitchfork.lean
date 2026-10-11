import Categorification.TwoRep.RouqMixedCup

/-!
# All-weight mixed scalar pitchforks

`RouqFamily.mixedCap_pitchfork` and `RouqFamily.mixedCup_pitchfork` prove the
actual distinct-colour cap and cup equations of Brundan,
*On the definition of Kac–Moody 2-category*, Theorem 5.3 (5.7).
They remove the inequalities in Lemma 5.2 without changing its morphisms.

Both equations characterize the same partial mate under the derived left
adjunctions. For a square with an i-edge `a → b`, the cap equation is known
when `⟨hᵢ, a⟩ < dᵢⱼ`, and the cup equation when `dᵢⱼ ≤ ⟨hᵢ, b⟩`.
Since `⟨hᵢ, b⟩ = ⟨hᵢ, a⟩ + 2`, these ranges cover every weight.
The mate identity therefore supplies both equations everywhere.

The scalar is `tᵢⱼ`, and mixed invertibility is precisely the original
relation (1.7) for the actual right mate. The upward KLR parameters remain
unrestricted rectangular parameters over a commutative ring. No reflected
family, cyclicity premise, grading, or scalar normalization is assumed.
These are morphism identities, not CL presentation relation consumers or
an aggregate verification of `presNM`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : RootDatum C X Y}
  (S : RouqFamily (B := B) RD)

/-- The inverse mixed crossing, scaled by `tᵢⱼ`, has the upward crossing as its
partial left mate at every weight. -/
theorem mixed_mate (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)] :
    mateEquiv (S.adjL i h₁) (S.adjL i h₇)
      ((P.t i j : k) • inv (S.mixedSigma i j h₆ h₇ h₁ h₂)) =
      S.cross j i h₁ h₂ h₆ h₇ := by
  by_cases hh : RD.pair (RD.iY i) a < C.dij i j
  · apply (mateEquiv_eq_iff_counit (S.adjL i h₁) (S.adjL i h₇) _ _).mpr
    simp only [Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_symm_apply,
      source_whiskerLeft_smul, Linear.smul_comp]
    have hp := S.mixedCap_pitchfork_of_lt P H i j hij h₆ h₇ h₁ h₂ hh
    have ht := congrArg (fun z =>
      (α_ (S.E i h₁) (S.E j h₂) (S.F i h₇)).inv ≫ z) hp.symm
    simpa only [Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc] using ht
  · apply (mateEquiv_eq_iff (S.adjL i h₁) (S.adjL i h₇) _ _).mpr
    simp only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply,
      source_smul_whiskerRight, Linear.comp_smul, Linear.smul_comp, Category.assoc]
    have hw := pair_step i h₁
    exact S.mixedCup_pitchfork_of_ge P H i j hij h₁ h₂ h₆ h₇ (by omega)

/-- Brundan Theorem 5.3 (5.7), cap equation for distinct colours at every weight.
Both caps are the counits of the derived left adjunctions. -/
theorem mixedCap_pitchfork (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {b c d f : X}
    (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    [IsIso (S.mixedSigma i j h₂ h₃ h₄ h₅)] :
    S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom ≫
      S.E j h₂ ◁ (S.adjL i h₃).counit ≫ (ρ_ (S.E j h₂)).hom =
    (P.t i j : k) • ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).hom ≫
      S.E i h₄ ◁ inv (S.mixedSigma i j h₂ h₃ h₄ h₅) ≫
      (α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).inv ≫
      (S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  have ht := (mateEquiv_eq_iff_counit (S.adjL i h₄) (S.adjL i h₃) _ _).mp
    (S.mixed_mate P H i j hij h₄ h₅ h₂ h₃)
  simp only [Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_symm_apply,
    source_whiskerLeft_smul, Linear.smul_comp] at ht
  have hp := congrArg (fun z =>
    (α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).hom ≫ z) ht.symm
  simpa only [Linear.comp_smul, Category.assoc, Iso.hom_inv_id_assoc] using hp

/-- Brundan Theorem 5.3 (5.7), cup equation for distinct colours at every weight.
Both cups are the units of the derived left adjunctions. -/
theorem mixedCup_pitchfork (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)] :
    (λ_ (S.E j h₂)).inv ≫ (S.adjL i h₁).unit ▷ S.E j h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫
      S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ =
    (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adjL i h₇).unit ≫
      (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).inv ≫
      inv (S.mixedSigma i j h₆ h₇ h₁ h₂) ▷ S.E i h₇ ≫
      (α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).hom) := by
  have ht := (mateEquiv_eq_iff (S.adjL i h₁) (S.adjL i h₇) _ _).mp
    (S.mixed_mate P H i j hij h₁ h₂ h₆ h₇)
  simpa only [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply,
    source_smul_whiskerRight, Linear.comp_smul, Linear.smul_comp, Category.assoc] using ht

end RouqFamily
end Categorification.TwoRep
