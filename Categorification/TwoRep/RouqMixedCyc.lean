import Categorification.TwoRep.RouqMixedPitchfork
/-!
# Scalar-corrected double mates of mixed crossings

`RouqFamily.mixed_cross_doubleMate` compares the actual composite right and
left adjunction mates of a distinct-colour upward crossing. For `cross j i`,
the correction is `t j i * (t i j)⁻¹`. Its intended downstream use is the
left crossing-cyclicity relation in the ungraded CL interpretation.

The input consists of unrestricted rectangular upward KLR parameters and
invertibility of the two actual mixed squares in Rouquier's original
inversion relation. The proof uses the two all-weight pitchforks and
contravariant composition of conjugate mates; it assumes no cyclicity.
This module does not yet verify the interpreted CL presentation relations.
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

omit [AdditiveWhiskering B] in
private lemma mixedCyc_mate_smul {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a}
    {l₂ : c ⟶ d} {r₂ : d ⟶ c} (A : l₁ ⊣ r₁) (D : l₂ ⊣ r₂)
    {g : a ⟶ c} {h : b ⟶ d} (s : k) (f : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv A D (s • f) = s • mateEquiv A D f := by
  simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply, source_whiskerLeft_smul, source_smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD)

/-- Taking a composite right mate and then a composite left mate of
`cross j i` multiplies it by `tⱼᵢ / tᵢⱼ`, at every weight. -/
theorem mixed_cross_doubleMate (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)]
    [IsIso (S.mixedSigma j i h₁ h₂ h₆ h₇)] :
    conjugateEquiv ((S.adjL j h₂).comp (S.adjL i h₁))
      ((S.adjL i h₇).comp (S.adjL j h₆))
      (conjugateEquiv ((S.adj j h₆).comp (S.adj i h₇))
        ((S.adj i h₁).comp (S.adj j h₂)) (S.cross j i h₁ h₂ h₆ h₇)) =
    ((P.t j i : k) * (((P.t i j)⁻¹ : kˣ) : k)) • S.cross j i h₁ h₂ h₆ h₇ := by
  have hm := S.mixed_mate P H i j hij h₁ h₂ h₆ h₇
  have hm' := S.mixed_mate P H j i hij.symm h₆ h₇ h₁ h₂
  have hc := congrArg (mateEquiv (S.adj i h₁) (S.adj i h₇)) hm'
  rw [mixedCyc_mate_smul, mixedCyc_mate_smul, Bicategory.iterated_mateEquiv_conjugateEquiv] at hc
  change (P.t j i : k) •
    conjugateEquiv _ _ (inv (S.mixedSigma j i h₁ h₂ h₆ h₇)) =
      S.mixedSigma i j h₆ h₇ h₁ h₂ at hc
  have hd : conjugateEquiv ((S.adj i h₇).comp (S.adjL j h₂))
      ((S.adjL j h₆).comp (S.adj i h₁)) (S.mixedSigma j i h₁ h₂ h₆ h₇) =
        (P.t j i : k) • inv (S.mixedSigma i j h₆ h₇ h₁ h₂) := by
    apply (cancel_mono (S.mixedSigma i j h₆ h₇ h₁ h₂)).mp
    rw [Linear.smul_comp, IsIso.inv_hom_id]
    conv_lhs => rhs; rw [← hc]
    rw [Linear.comp_smul, Bicategory.conjugateEquiv_comp,
      IsIso.inv_hom_id, Bicategory.conjugateEquiv_id]
  rw [← Bicategory.iterated_mateEquiv_conjugateEquiv (S.adj j h₆) (S.adj j h₂)
      (S.adj i h₁) (S.adj i h₇),
    ← Bicategory.iterated_mateEquiv_conjugateEquiv (S.adjL j h₂) (S.adjL j h₆)
      (S.adjL i h₇) (S.adjL i h₁)]
  change mateEquiv (S.adjL i h₁) (S.adjL i h₇)
    (mateEquiv (S.adjL j h₂) (S.adjL j h₆)
      (mateEquiv (S.adj i h₇) (S.adj i h₁) (S.mixedSigma j i h₁ h₂ h₆ h₇))) = _
  rw [Bicategory.iterated_mateEquiv_conjugateEquiv (S.adj i h₇) (S.adj i h₁)
    (S.adjL j h₆) (S.adjL j h₂), hd, mixedCyc_mate_smul]
  rw [mixedCyc_mate_smul] at hm
  have hm₀ := congrArg ((((P.t i j)⁻¹ : kˣ) : k) • ·) hm
  simp only [smul_smul, Units.inv_mul, one_smul] at hm₀
  rw [hm₀, smul_smul]
end RouqFamily
end Categorification.TwoRep
