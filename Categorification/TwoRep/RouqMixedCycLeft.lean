import Categorification.TwoRep.RouqMixedCycRight
import Categorification.TwoRep.RouqMixedCyc
/-!
# Mixed left crossing cyclicity in the Rouquier interpretation

`RouqFamily.mixed_cycCrossL_rel` annihilates the actual left crossing-cyclicity
relation of the CL presentation at every weight for distinct ordered colours.
The hypotheses are unrestricted rectangular upward KLR relations and
invertibility of the two original mixed squares, over a commutative scalar ring
with linear Hom categories and whiskering.

A private two-pair rotation identity identifies the five interpreted layers
with the composite right mate. The scalar double-mate theorem then compares it
with the original downward crossing, with coefficient `tⱼᵢ⁻¹`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open StringDiagrams Diagrams.BicatInterp
private theorem rot2GL_aux {C : Type*} [Bicategory C] {a b b' c : C}
    {R₁ : a ⟶ b} {E₁ : b ⟶ a} {R₂ : b ⟶ c} {E₂ : c ⟶ b}
    {S₁ : a ⟶ b'} {F₁ : b' ⟶ a} {S₂ : b' ⟶ c} {F₂ : c ⟶ b'}
    (adjB₁ : E₁ ⊣ R₁) (adjB₂ : E₂ ⊣ R₂) (adjT₁ : F₁ ⊣ S₁) (adjT₂ : F₂ ⊣ S₂)
    (x : F₂ ≫ F₁ ⟶ E₂ ≫ E₁) :
    (R₁ ≫ R₂) ◁ (adjT₂.unit ▷ 𝟙 c) ≫
        ((R₁ ≫ R₂) ◁ (ρ_ (F₂ ≫ S₂)).hom ≫ (α_ (R₁ ≫ R₂) F₂ S₂).inv ≫
          ((R₁ ≫ R₂) ≫ F₂) ◁ (λ_ S₂).inv) ≫
        ((R₁ ≫ R₂) ≫ F₂) ◁ (adjT₁.unit ▷ S₂) ≫
        (((R₁ ≫ R₂) ≫ F₂) ◁ (α_ F₁ S₁ S₂).hom ≫ (α_ (R₁ ≫ R₂) F₂ (F₁ ≫ (S₁ ≫ S₂))).hom ≫
          (R₁ ≫ R₂) ◁ (α_ F₂ F₁ (S₁ ≫ S₂)).inv) ≫
        (R₁ ≫ R₂) ◁ (x ▷ (S₁ ≫ S₂)) ≫
        ((α_ R₁ R₂ ((E₂ ≫ E₁) ≫ (S₁ ≫ S₂))).hom ≫
          R₁ ◁ (R₂ ◁ (α_ E₂ E₁ (S₁ ≫ S₂)).hom ≫ (α_ R₂ E₂ (E₁ ≫ (S₁ ≫ S₂))).inv ≫
            (R₂ ≫ E₂) ◁ (α_ E₁ S₁ S₂).inv)) ≫
        R₁ ◁ (adjB₂.counit ▷ ((E₁ ≫ S₁) ≫ S₂)) ≫
        (R₁ ◁ (λ_ _).hom ≫ R₁ ◁ (α_ E₁ S₁ S₂).hom ≫ (α_ R₁ E₁ (S₁ ≫ S₂)).inv ≫ (λ_ _).inv) ≫
        𝟙 a ◁ (adjB₁.counit ▷ (S₁ ≫ S₂)) =
      ((R₁ ≫ R₂) ◁ (λ_ (𝟙 c)).hom ≫ (λ_ ((R₁ ≫ R₂) ≫ 𝟙 c)).inv) ≫
        𝟙 a ◁ ((Bicategory.conjugateEquiv (adjB₂.comp adjB₁) (adjT₂.comp adjT₁)) x ▷ 𝟙 c) ≫
          𝟙 a ◁ ((ρ_ (S₁ ≫ S₂)).hom ≫ (λ_ (S₁ ≫ S₂)).inv) := by
  rw [Bicategory.conjugateEquiv_apply']
  simp only [Bicategory.Adjunction.comp_unit, Bicategory.Adjunction.comp_counit,
    Bicategory.Adjunction.compUnit, Bicategory.Adjunction.compCounit]
  bicategory

private theorem rot2GL_key {S : Signature} {D : Type*} [Bicategory D] (M : Model S D)
    {a b b' c : FB S} {r₁ : a ⟶ b} {e₁ : b ⟶ a} {r₂ : b ⟶ c} {e₂ : c ⟶ b}
    {s₁ : a ⟶ b'} {f₁ : b' ⟶ a} {s₂ : b' ⟶ c} {f₂ : c ⟶ b'}
    (adjB₁ : M.lift.map e₁ ⊣ M.lift.map r₁) (adjB₂ : M.lift.map e₂ ⊣ M.lift.map r₂)
    (adjT₁ : M.lift.map f₁ ⊣ M.lift.map s₁) (adjT₂ : M.lift.map f₂ ⊣ M.lift.map s₂)
    (x : M.lift.map f₂ ≫ M.lift.map f₁ ⟶ M.lift.map e₂ ≫ M.lift.map e₁)
    {p₁ : a ⟶ c} {q₁ d₁ c₁ : c ⟶ c} (σp₁ : p₁ ≅ r₁ ≫ r₂) (σq₁ : q₁ ≅ 𝟙 c) (σd₁ : d₁ ≅ 𝟙 c)
    (σc₁ : c₁ ≅ f₂ ≫ s₂) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adjT₂.unit)
    {p₂ : a ⟶ b'} {q₂ : b' ⟶ c} {d₂ c₂ : b' ⟶ b'} (σp₂ : p₂ ≅ (r₁ ≫ r₂) ≫ f₂) (σq₂ : q₂ ≅ s₂)
    (σd₂ : d₂ ≅ 𝟙 b') (σc₂ : c₂ ≅ f₁ ≫ s₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = adjT₁.unit)
    {p₃ q₃ : a ⟶ c} {d₃ c₃ : c ⟶ a} (σp₃ : p₃ ≅ r₁ ≫ r₂) (σq₃ : q₃ ≅ s₁ ≫ s₂)
    (σd₃ : d₃ ≅ f₂ ≫ f₁) (σc₃ : c₃ ≅ e₂ ≫ e₁) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = x)
    {p₄ : a ⟶ b} {q₄ : b ⟶ c} {d₄ c₄ : b ⟶ b} (σp₄ : p₄ ≅ r₁) (σq₄ : q₄ ≅ (e₁ ≫ s₁) ≫ s₂)
    (σd₄ : d₄ ≅ r₂ ≫ e₂) (σc₄ : c₄ ≅ 𝟙 b) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hg₄ : M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom = adjB₂.counit)
    {p₅ d₅ c₅ : a ⟶ a} {q₅ : a ⟶ c} (σp₅ : p₅ ≅ 𝟙 a) (σq₅ : q₅ ≅ s₁ ≫ s₂)
    (σd₅ : d₅ ≅ r₁ ≫ e₁) (σc₅ : c₅ ≅ 𝟙 a) (g₅ : M.lift.map d₅ ⟶ M.lift.map c₅)
    (hg₅ : M.lift.map₂ σd₅.inv ≫ g₅ ≫ M.lift.map₂ σc₅.hom = adjB₁.counit)
    {p₆ : a ⟶ a} {q₆ : c ⟶ c} {d₆ c₆ : a ⟶ c} (σp₆ : p₆ ≅ 𝟙 a) (σq₆ : q₆ ≅ 𝟙 c)
    (σd₆ : d₆ ≅ r₁ ≫ r₂) (σc₆ : c₆ ≅ s₁ ≫ s₂) (g₆ : M.lift.map d₆ ⟶ M.lift.map c₆)
    (hg₆ : M.lift.map₂ σd₆.inv ≫ g₆ ≫ M.lift.map₂ σc₆.hom =
      Bicategory.conjugateEquiv (adjB₂.comp adjB₁) (adjT₂.comp adjT₁) x)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ P₅ Q₅ Q P₆ Q₆ : a ⟶ c}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₄ : Q₄ ⟶ P₅)
    (A₅ : P₅ ⟶ p₅ ≫ (d₅ ≫ q₅)) (B₅ : p₅ ≫ (c₅ ≫ q₅) ⟶ Q₅) (E₅ : Q₅ ⟶ Q)
    (F₀ : P ⟶ P₆) (A₆ : P₆ ⟶ p₆ ≫ (d₆ ≫ q₆)) (B₆ : p₆ ≫ (c₆ ≫ q₆) ⟶ Q₆) (F₁ : Q₆ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ ≫
            (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₄ ≫
              (M.lift.map₂ A₅ ≫ midK M p₅ q₅ g₅ ≫ M.lift.map₂ B₅) ≫ M.lift.map₂ E₅ =
      M.lift.map₂ F₀ ≫ (M.lift.map₂ A₆ ≫ midK M p₆ q₆ g₆ ≫ M.lift.map₂ B₆) ≫
        M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃, midK_canon M σp₄ σq₄ σd₄ σc₄ g₄, hg₄,
    midK_canon M σp₅ σq₅ σd₅ σc₅ g₅, hg₅, midK_canon M σp₆ σq₆ σd₆ σc₆ g₆, hg₆]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (r₁ ≫ r₂) (𝟙 c) (x := 𝟙 c) (y := f₂ ≫ s₂) adjT₂.unit ≫
      M.lift.map₂ ((r₁ ≫ r₂) ◁ (ρ_ (f₂ ≫ s₂)).hom ≫ (α_ (r₁ ≫ r₂) f₂ s₂).inv ≫
        ((r₁ ≫ r₂) ≫ f₂) ◁ (λ_ s₂).inv) ≫
      midK M ((r₁ ≫ r₂) ≫ f₂) s₂ (x := 𝟙 b') (y := f₁ ≫ s₁) adjT₁.unit ≫
      M.lift.map₂ (((r₁ ≫ r₂) ≫ f₂) ◁ (α_ f₁ s₁ s₂).hom ≫
        (α_ (r₁ ≫ r₂) f₂ (f₁ ≫ (s₁ ≫ s₂))).hom ≫ (r₁ ≫ r₂) ◁ (α_ f₂ f₁ (s₁ ≫ s₂)).inv) ≫
      midK M (r₁ ≫ r₂) (s₁ ≫ s₂) (x := f₂ ≫ f₁) (y := e₂ ≫ e₁) x ≫
      M.lift.map₂ ((α_ r₁ r₂ ((e₂ ≫ e₁) ≫ (s₁ ≫ s₂))).hom ≫
        r₁ ◁ (r₂ ◁ (α_ e₂ e₁ (s₁ ≫ s₂)).hom ≫ (α_ r₂ e₂ (e₁ ≫ (s₁ ≫ s₂))).inv ≫
          (r₂ ≫ e₂) ◁ (α_ e₁ s₁ s₂).inv)) ≫
      midK M r₁ ((e₁ ≫ s₁) ≫ s₂) (x := r₂ ≫ e₂) (y := 𝟙 b) adjB₂.counit ≫
      M.lift.map₂ (r₁ ◁ (λ_ _).hom ≫ r₁ ◁ (α_ e₁ s₁ s₂).hom ≫ (α_ r₁ e₁ (s₁ ≫ s₂)).inv ≫
        (λ_ _).inv) ≫
      midK M (𝟙 a) (s₁ ≫ s₂) (x := r₁ ≫ e₁) (y := 𝟙 a) adjB₁.counit =
      M.lift.map₂ ((r₁ ≫ r₂) ◁ (λ_ (𝟙 c)).hom ≫ (λ_ ((r₁ ≫ r₂) ≫ 𝟙 c)).inv) ≫
        midK M (𝟙 a) (𝟙 c) (x := r₁ ≫ r₂) (y := s₁ ≫ s₂)
          (Bicategory.conjugateEquiv (adjB₂.comp adjB₁) (adjT₂.comp adjT₁) x) ≫
          M.lift.map₂ (𝟙 a ◁ ((ρ_ (s₁ ≫ s₂)).hom ≫ (λ_ (s₁ ≫ s₂)).inv)) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      lift_map₂_rightUnitor_hom, lift_map_comp]
    exact rot2GL_aux adjB₁ adjB₂ adjT₁ adjT₂ x
  rw [lift_map₂_eq M _ ((r₁ ≫ r₂) ◁ (ρ_ (f₂ ≫ s₂)).hom ≫ (α_ (r₁ ≫ r₂) f₂ s₂).inv ≫
      ((r₁ ≫ r₂) ≫ f₂) ◁ (λ_ s₂).inv),
    lift_map₂_eq M _ (((r₁ ≫ r₂) ≫ f₂) ◁ (α_ f₁ s₁ s₂).hom ≫
      (α_ (r₁ ≫ r₂) f₂ (f₁ ≫ (s₁ ≫ s₂))).hom ≫ (r₁ ≫ r₂) ◁ (α_ f₂ f₁ (s₁ ≫ s₂)).inv),
    lift_map₂_eq M _ ((α_ r₁ r₂ ((e₂ ≫ e₁) ≫ (s₁ ≫ s₂))).hom ≫
      r₁ ◁ (r₂ ◁ (α_ e₂ e₁ (s₁ ≫ s₂)).hom ≫ (α_ r₂ e₂ (e₁ ≫ (s₁ ≫ s₂))).inv ≫
        (r₂ ≫ e₂) ◁ (α_ e₁ s₁ s₂).inv)),
    lift_map₂_eq M _ (r₁ ◁ (λ_ _).hom ≫ r₁ ◁ (α_ e₁ s₁ s₂).hom ≫
      (α_ r₁ e₁ (s₁ ≫ s₂)).inv ≫ (λ_ _).inv), reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _


open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : RootDatum C X Y}
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh
open QStrong (sig0_colourSrc_g sig0_colourTgt_g sig0_dom_cross_g sig0_cod_cross_g
  sh_ud sh_ud' sh_dd)

private theorem dual_dn_g (i : I) : Letter.dual (dn i) = up i := rfl

private abbrev dnArrow (i : I) (μ : X) : fo (S := psig RD) μ ⟶ fo (sh RD (dn i) + μ) :=
  FreeBicategory.Hom.of (⟨⟨dn i, μ⟩, rfl, rfl⟩ : rq (S := psig RD) μ ⟶ rq (sh RD (dn i) + μ))
private abbrev upArrow (i : I) (μ : X) : fo (S := psig RD) (sh RD (dn i) + μ) ⟶ fo μ :=
  FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + μ⟩, rfl, sh_ud i μ⟩ :
    rq (S := psig RD) (sh RD (dn i) + μ) ⟶ rq μ)
private abbrev swapDnArrow (i j : I) (μ : X) :
    fo (S := psig RD) (sh RD (dn j) + μ) ⟶ fo (sh RD (dn j) + (sh RD (dn i) + μ)) :=
  FreeBicategory.Hom.of (⟨⟨dn i, sh RD (dn j) + μ⟩, rfl, sh_dd i j μ⟩ :
    rq (S := psig RD) (sh RD (dn j) + μ) ⟶ rq (sh RD (dn j) + (sh RD (dn i) + μ)))
private abbrev swapUpArrow (i j : I) (μ : X) :
    fo (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ⟶ fo (sh RD (dn j) + μ) :=
  FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn j) + (sh RD (dn i) + μ)⟩, rfl, sh_ud' i j μ⟩ :
    rq (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ⟶ rq (sh RD (dn j) + μ))

private lemma crossDom_fw (j i : I) (μ : X) (h e) :
    fw (S := psig RD) μ ((psig RD).dom (.gen (.cross true j i (sh RD (dn j) + (sh RD (dn i) + μ)))))
      (sh RD (dn j) + (sh RD (dn i) + μ)) h e =
      swapUpArrow (RD := RD) i j μ ≫ upArrow j μ := by
  exact comp_of_congr (sh_ud' (RD := RD) i j μ) rfl
    (congrArg (Col.mk (up j)) (sh_ud' (RD := RD) i j μ))

private lemma crossCod_fw (j i : I) (μ : X) (h e) :
    fw (S := psig RD) μ ((psig RD).cod (.gen (.cross true j i (sh RD (dn j) + (sh RD (dn i) + μ)))))
      (sh RD (dn j) + (sh RD (dn i) + μ)) h e =
      upArrow (RD := RD) j (sh RD (dn i) + μ) ≫ upArrow i μ := by
  exact comp_of_congr (sh_ud (RD := RD) j (sh RD (dn i) + μ)) rfl
    (congrArg (Col.mk (up i)) (sh_ud (RD := RD) j (sh RD (dn i) + μ)))

private abbrev cup1 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [], .cup ⟨dn i, (sh RD (dn j) + μ)⟩, [⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩]⟩

private lemma cup1_core (j i : I) (μ : X) (hv : (cup1 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup1 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cup1 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cup1 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv (sh_dd (RD := RD) i j μ)) (Valid.dom_end_of hv (sh_dd (RD := RD) i j μ) (sh_dd (RD := RD) i j μ))
        (Valid.right_ok_of hv (sh_dd (RD := RD) i j μ)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cup1 (RD := RD) j i μ).right μ (Valid.right_ok_of hv (sh_dd (RD := RD) i j μ)) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cup1 (RD := RD) j i μ).left (sh RD (dn j) + (sh RD (dn i) + μ)) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ((psig RD).dom (cup1 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ)) (Valid.ok_dom_of hv (sh_dd (RD := RD) i j μ)) (Valid.dom_end_of hv (sh_dd (RD := RD) i j μ) (sh_dd (RD := RD) i j μ)))
        (y := fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ((psig RD).cod (cup1 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ)) (Valid.ok_cod_of hv (sh_dd (RD := RD) i j μ)) (Valid.cod_end_of hv (sh_dd (RD := RD) i j μ) (sh_dd (RD := RD) i j μ)))
        ((S.adj i (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := (sh RD (dn j) + μ)) (dn_reg i rfl (sh_dd i j μ))).unit) ≫
      S.model.lift.map₂ (layerSplit (cup1 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cup1 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv (sh_dd (RD := RD) i j μ)) (Valid.cod_end_of hv (sh_dd (RD := RD) i j μ) (sh_dd (RD := RD) i j μ))
        (Valid.right_ok_of hv (sh_dd (RD := RD) i j μ)) rfl).inv := by
  rfl

private abbrev cup2 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn i, (sh RD (dn j) + μ)⟩], .cup ⟨dn j, μ⟩, [⟨up i, (sh RD (dn j) + (sh RD (dn i) + μ))⟩, ⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩]⟩

private lemma cup2_core (j i : I) (μ : X) (hv : (cup2 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup2 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cup2 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cup2 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + μ) (cup2 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cup2 (RD := RD) j i μ).left (sh RD (dn j) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn j) + μ) ((psig RD).dom (cup2 (RD := RD) j i μ).gen) (sh RD (dn j) + μ) (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl))
        (y := fw (S := psig RD) (sh RD (dn j) + μ) ((psig RD).cod (cup2 (RD := RD) j i μ).gen) (sh RD (dn j) + μ) (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl))
        ((S.adj j (x := (sh RD (dn j) + μ)) (y := μ) (dn_reg j rfl rfl)).unit) ≫
      S.model.lift.map₂ (layerSplit (cup2 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cup2 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev cross3 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .gen (.cross true j i (sh RD (dn j) + (sh RD (dn i) + μ))), [⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩]⟩

private lemma cross3_core (j i : I) (μ : X) (hv : (cross3 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cross3 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cross3 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cross3 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cross3 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cross3 (RD := RD) j i μ).left μ (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) μ ((psig RD).dom (cross3 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ)) (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl))
        (y := fw (S := psig RD) μ ((psig RD).cod (cross3 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ)) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl))
        ((S.genImg Sc).gen (cross3 (RD := RD) j i μ).gen μ (sh RD (dn j) + (sh RD (dn i) + μ)) ((hc.left_end hv).symm) rfl
          (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl)) ≫
      S.model.lift.map₂ (layerSplit (cross3 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cross3 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev cap4 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩, ⟨up i, (sh RD (dn i) + μ)⟩], .cap ⟨dn j, (sh RD (dn i) + μ)⟩, [⟨dn i, μ⟩]⟩

private lemma cap4_core (j i : I) (μ : X) (hv : (cap4 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap4 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cap4 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn i) + μ) (sh RD (dn i) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cap4 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn i) + μ) (cap4 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cap4 (RD := RD) j i μ).left (sh RD (dn i) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn i) + μ) ((psig RD).dom (cap4 (RD := RD) j i μ).gen) (sh RD (dn i) + μ) (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl))
        (y := fw (S := psig RD) (sh RD (dn i) + μ) ((psig RD).cod (cap4 (RD := RD) j i μ).gen) (sh RD (dn i) + μ) (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl))
        ((S.adj j (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := (sh RD (dn i) + μ)) (dn_reg j rfl rfl)).counit) ≫
      S.model.lift.map₂ (layerSplit (cap4 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn i) + μ) (sh RD (dn i) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cap4 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev cap5 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩], .cap ⟨dn i, μ⟩, []⟩

private lemma cap5_core (j i : I) (μ : X) (hv : (cap5 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap5 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cap5 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).dom (cap5 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) μ (cap5 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cap5 (RD := RD) j i μ).left μ (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) μ ((psig RD).dom (cap5 (RD := RD) j i μ).gen) μ (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl))
        (y := fw (S := psig RD) μ ((psig RD).cod (cap5 (RD := RD) j i μ).gen) μ (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl))
        ((S.adj i (x := (sh RD (dn i) + μ)) (y := μ) (dn_reg i rfl rfl)).counit) ≫
      S.model.lift.map₂ (layerSplit (cap5 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).cod (cap5 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev down6 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨sh RD (dn j) + (sh RD (dn i) + μ), [], .gen (.cross false j i μ), []⟩

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
omit [AdditiveWhiskering B] in
private lemma midK_smul' {S' : Signature} (M : Model S' B) {a b c d : FB S'}
    (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c} (t : k) (g : M.lift.map x ⟶ M.lift.map y) :
    midK M p q (t • g) = t • midK M p q g := by
  rw [midK, midK, source_smul_whiskerRight]
  exact source_whiskerLeft_smul _ _ _

omit [AdditiveWhiskering B] in
private lemma scaled_midK {S' : Signature} (M : Model S' B) {a b c d : FB S'}
    (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c} (t : k) (g : M.lift.map x ⟶ M.lift.map y)
    {P P' Q Q' : M.lift.obj a ⟶ M.lift.obj d}
    (u : P ⟶ P') (v : P' ⟶ M.lift.map (p ≫ (x ≫ q)))
    (w : M.lift.map (p ≫ (y ≫ q)) ⟶ Q') (z : Q' ⟶ Q)
    (f : P ⟶ Q) (hf : f = u ≫ (v ≫ midK M p q g ≫ w) ≫ z) :
    t • f = u ≫ (v ≫ midK M p q (t • g) ≫ w) ≫ z := by
  rw [hf, midK_smul']
  simp only [Linear.smul_comp, Linear.comp_smul]

omit [AdditiveWhiskering B] in
private lemma cross_congr' (j i : I) {l n n' m n₂ n₂' : X} (hn : n = n₂) (hn' : n' = n₂')
    (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX j = m) (h₃ : l + RD.iX j = n') (h₄ : n' + RD.iX i = m)
    (h₁' : l + RD.iX i = n₂) (h₂' : n₂ + RD.iX j = m) (h₃' : l + RD.iX j = n₂')
    (h₄' : n₂' + RD.iX i = m)
    (e₁ : S.E i h₁' ≫ S.E j h₂' = S.E i h₁ ≫ S.E j h₂)
    (e₂ : S.E j h₃ ≫ S.E i h₄ = S.E j h₃' ≫ S.E i h₄') :
    eqToHom e₁ ≫ S.cross j i h₁ h₂ h₃ h₄ ≫ eqToHom e₂ = S.cross j i h₁' h₂' h₃' h₄' := by
  subst hn hn'
  simp

omit [AdditiveWhiskering B] in
private lemma conjugate_smul {a b : B} {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a}
    (A : l₁ ⊣ r₁) (D : l₂ ⊣ r₂) (t : k) (f : l₂ ⟶ l₁) :
    conjugateEquiv A D (t • f) = t • conjugateEquiv A D f := by
  simp only [Bicategory.conjugateEquiv_apply', source_whiskerLeft_smul,
    source_smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

/-- The original downward crossing is the scalar-corrected right mate, for distinct colours. -/
theorem mixed_crossDn_rightMate (H : BrundanUpKLR S Sc) (i j : I) (hij : i ≠ j)
    {a b c e : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)]
    [IsIso (S.mixedSigma j i h₁ h₂ h₆ h₇)] :
    S.crossDn Sc j i h₇ h₆ h₂ h₁ =
      (((Sc.t j i)⁻¹ : kˣ) : k) •
        conjugateEquiv ((S.adj j h₆).comp (S.adj i h₇))
          ((S.adj i h₁).comp (S.adj j h₂)) (S.cross j i h₁ h₂ h₆ h₇) := by
  unfold crossDn
  apply (conjugateEquiv ((S.adjL j h₂).comp (S.adjL i h₁))
    ((S.adjL i h₇).comp (S.adjL j h₆))).injective
  rw [conjugate_smul, conjugate_smul, Equiv.apply_symm_apply,
    S.mixed_cross_doubleMate Sc H i j hij h₁ h₂ h₆ h₇, smul_smul]
  rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem rotationLayers (H : BrundanUpKLR S Sc) (j i : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma i j (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn i) + μ)) (c := (sh RD (dn j) + μ)) (d := μ)
      (dn_reg j rfl rfl) (dn_reg i rfl rfl) (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl))]
    [IsIso (S.mixedSigma j i (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn j) + μ)) (c := (sh RD (dn i) + μ)) (d := μ)
      (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl) (dn_reg j rfl rfl) (dn_reg i rfl rfl))]
    (hv1 : (cup1 (RD := RD) j i μ).Valid)
    (hc1 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup1 (RD := RD) j i μ).dom)
    (hv2 : (cup2 (RD := RD) j i μ).Valid)
    (hc2 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup2 (RD := RD) j i μ).dom)
    (hv3 : (cross3 (RD := RD) j i μ).Valid)
    (hc3 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cross3 (RD := RD) j i μ).dom)
    (hv4 : (cap4 (RD := RD) j i μ).Valid)
    (hc4 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap4 (RD := RD) j i μ).dom)
    (hv5 : (cap5 (RD := RD) j i μ).Valid)
    (hc5 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap5 (RD := RD) j i μ).dom)
    (hv6 : (down6 (RD := RD) j i μ).Valid)
    (hc6 : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (down6 (RD := RD) j i μ).dom)
    {P Q : fo (S := psig RD) μ ⟶ fo (sh RD (dn j) + (sh RD (dn i) + μ))}
    (E0 : P ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cup1 (RD := RD) j i μ).dom.word μ hc1.1 hc1.2.1)
    (E1 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cup1 (RD := RD) j i μ).cod.word μ (hc1.cod hv1).1 (hc1.cod hv1).2.1) ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cup2 (RD := RD) j i μ).dom.word μ hc2.1 hc2.2.1)
    (E2 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cup2 (RD := RD) j i μ).cod.word μ (hc2.cod hv2).1 (hc2.cod hv2).2.1) ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cross3 (RD := RD) j i μ).dom.word μ hc3.1 hc3.2.1)
    (E3 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cross3 (RD := RD) j i μ).cod.word μ (hc3.cod hv3).1 (hc3.cod hv3).2.1) ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cap4 (RD := RD) j i μ).dom.word μ hc4.1 hc4.2.1)
    (E4 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cap4 (RD := RD) j i μ).cod.word μ (hc4.cod hv4).1 (hc4.cod hv4).2.1) ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cap5 (RD := RD) j i μ).dom.word μ hc5.1 hc5.2.1)
    (E5 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (cap5 (RD := RD) j i μ).cod.word μ (hc5.cod hv5).1 (hc5.cod hv5).2.1) ⟶ Q)
    (F0 : P ⟶ fw (sh RD (dn j) + (sh RD (dn i) + μ)) (down6 (RD := RD) j i μ).dom.word μ hc6.1 hc6.2.1) (F1 : (fw (sh RD (dn j) + (sh RD (dn i) + μ)) (down6 (RD := RD) j i μ).cod.word μ (hc6.cod hv6).1 (hc6.cod hv6).2.1) ⟶ Q) :
    (((Sc.t j i)⁻¹ : kˣ) : k) • (S.model.lift.map₂ E0 ≫
      coreC (S.genImg Sc) hv1 hc1 ≫ S.model.lift.map₂ E1 ≫
      coreC (S.genImg Sc) hv2 hc2 ≫ S.model.lift.map₂ E2 ≫
      coreC (S.genImg Sc) hv3 hc3 ≫ S.model.lift.map₂ E3 ≫
      coreC (S.genImg Sc) hv4 hc4 ≫ S.model.lift.map₂ E4 ≫
      coreC (S.genImg Sc) hv5 hc5 ≫ S.model.lift.map₂ E5) =
    S.model.lift.map₂ F0 ≫ coreC (S.genImg Sc) hv6 hc6 ≫ S.model.lift.map₂ F1 := by
  erw [cup1_core S Sc j i μ, cup2_core S Sc j i μ, cross3_core S Sc j i μ,
    cap4_core S Sc j i μ, cap5_core S Sc j i μ]
  unfold coreC core
  dsimp only [cup1, cup2, cross3, cap4, cap5, down6, Signature.endR, psig_colourTgt, psig_colourSrc,
    Signature.pivotal_dom_cup, Signature.pivotal_cod_cup, Signature.pivotal_dom_cap,
    Signature.pivotal_cod_cap, Signature.pivotal_dom_gen, Signature.pivotal_cod_gen,
    Signature.pivotal_left_cup, Signature.pivotal_right_cup, Signature.pivotal_left_cap,
    Signature.pivotal_right_cap, Signature.pivotal_left_gen, Signature.pivotal_right_gen,
    sig0_dom_cross_g, sig0_cod_cross_g, wd_cons, wd_nil, wt_cons, wt_nil, inv_dual,
    sig0_colourTgt_g, sig0_colourSrc_g]
  dsimp only [genImg]
  rw [S.mixed_crossDn_rightMate Sc H i j hij]
  refine scaled_midK S.model _ _ _ _ _ _ _ _ _ ?_
  dsimp only [fw]
  refine rot2GL_key S.model
    (a := fo (S := psig RD) μ) (b := fo (S := psig RD) (sh RD (dn i) + μ))
    (b' := fo (S := psig RD) (sh RD (dn j) + μ))
    (c := fo (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)))
    (r₁ := dnArrow (RD := RD) i μ) (e₁ := upArrow i μ)
    (r₂ := dnArrow j (sh RD (dn i) + μ)) (e₂ := upArrow j (sh RD (dn i) + μ))
    (s₁ := dnArrow j μ) (f₁ := upArrow j μ)
    (s₂ := swapDnArrow i j μ) (f₂ := swapUpArrow i j μ)
    (S.adj i (x := (sh RD (dn i) + μ)) (y := μ) (dn_reg i rfl rfl))
    (S.adj j (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := (sh RD (dn i) + μ)) (dn_reg j rfl rfl))
    (S.adj j (x := (sh RD (dn j) + μ)) (y := μ) (dn_reg j rfl rfl))
    (S.adj i (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := (sh RD (dn j) + μ)) (dn_reg i rfl (sh_dd i j μ)))
    (S.cross j i (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl)
      (dn_reg j rfl rfl) (dn_reg i rfl rfl))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso ?c1) _ ?hg1
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg2
    (Iso.refl _) (Iso.refl _) (eqToIso ?d3) (eqToIso ?c3) _ ?hg3
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg4
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg5
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case c1 =>
    exact comp_of_congr rfl (congrArg (Col.mk (up i)) (sh_dd (RD := RD) i j μ)) rfl
  case d3 => exact crossDom_fw (RD := RD) j i μ _ _
  case c3 => exact crossCod_fw (RD := RD) j i μ _ _
  case hg1 =>
    simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp]
    erw [eqToIso.hom, lift_map₂_eqToHom, eqToHom_refl, Category.comp_id]
  case hg2 | hg4 | hg5 =>
    simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id]
  case hg3 =>
    simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
    exact S.cross_congr' j i (sh_ud' (RD := RD) i j μ) (sh_ud j (sh RD (dn i) + μ))
      _ _ _ _ _ _ _ _ _ _
  case hg6 =>
    simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id]
    congr 1

/-- The left rotation evaluates to the unchanged downward crossing, with its ordered scalar. -/
theorem mixed_cycCrossL (H : BrundanUpKLR S Sc) (j i : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma i j (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn i) + μ)) (c := (sh RD (dn j) + μ)) (d := μ)
      (dn_reg j rfl rfl) (dn_reg i rfl rfl) (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl))]
    [IsIso (S.mixedSigma j i (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn j) + μ)) (c := (sh RD (dn i) + μ)) (d := μ)
      (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl) (dn_reg j rfl rfl) (dn_reg i rfl rfl))] :
    (((Sc.t j i)⁻¹ : kˣ) : k) •
      (S.interp Sc (KL3.Diagram.wt RD μ [dn j, dn i]) μ).map
        (ObjectProperty.homMk (X := obAdmissible μ [dn j, dn i])
          (Y := mixedSwapAdmissible j i μ) (rotCrossL RD j i μ)) =
      (S.interp Sc (KL3.Diagram.wt RD μ [dn j, dn i]) μ).map
        (ObjectProperty.homMk (X := obAdmissible μ [dn j, dn i])
          (Y := mixedSwapAdmissible j i μ) (downCross RD j i μ)) := by
  change _ • admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, obAdmissible, mixedSwapAdmissible, rotCrossL, downCross, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, dual_dn_g]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize g1 : sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ)) = y at *
  obtain rfl : y = sh RD ((false, j) : Letter I) + μ := by rw [← g1, sh_up, sh_dn, sh_dn]; abel
  generalize g2 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← g2, sh_up, sh_dn]; abel
  generalize g4 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ)) = w at *
  obtain rfl : w = sh RD ((false, i) : Letter I) + μ := by rw [← g4, sh_up, sh_dn]; abel
  generalize g3 : sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + μ) = z at *
  obtain rfl : μ = z := by rw [← g3, sh_up, sh_dn]; abel
  generalize g5 : sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = v at *
  obtain rfl : v = sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ) := by rw [← g5]; abel
  conv_lhs =>
    arg 2
    change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  conv_rhs => change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  try rw [eqToHom_word ?w0 _]
  try rw [eqToHom_word ?w1 _]
  try erw [eqToHom_word ?w2 _]
  try erw [eqToHom_word ?w3 _]
  try erw [eqToHom_word ?w4 _]
  try erw [eqToHom_word ?w5 _]
  try erw [eqToHom_word ?w6 _]
  try erw [eqToHom_word ?w7 _]
  · exact rotationLayers S Sc H j i hij μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals
      first | rfl | (rw [g1]) | (rw [g2]) | (rw [g3]) | (rw [g4]) | (rw [g5])
    all_goals rfl

/-- The actual CL mixed left crossing-cyclicity relation vanishes for distinct ordered colours. -/
theorem mixed_cycCrossL_rel (H : BrundanUpKLR S Sc) (j i : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma i j (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn i) + μ)) (c := (sh RD (dn j) + μ)) (d := μ)
      (dn_reg j rfl rfl) (dn_reg i rfl rfl) (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl))]
    [IsIso (S.mixedSigma j i (a := (sh RD (dn j) + (sh RD (dn i) + μ))) (b := (sh RD (dn j) + μ)) (c := (sh RD (dn i) + μ)) (d := μ)
      (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl) (dn_reg j rfl rfl) (dn_reg i rfl rfl))] :
    admissibleMap (S.genImg Sc) (obAdmissible μ [dn j, dn i]).property
      (mixedSwapAdmissible j i μ).property
      (CL.relationCL RD k Sc (.cycCrossL j i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    ((((Sc.t j i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j i μ) -
      LinDiagram.of (downCross RD j i μ)) = 0
  erw [map_sub, map_smul, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.mixed_cycCrossL Sc H j i hij μ)

end RouqFamily
end Categorification.TwoRep
