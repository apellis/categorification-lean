import Categorification.TwoRep.RouqMixedPitchfork
import Categorification.TwoRep.RouqMixedCycRight
/-!
# The mixed CL down-up relations in the Rouquier interpretation

`RouqFamily.mixed_downupEF_rel` and `RouqFamily.mixed_downupFE_rel` annihilate
both original CL down-up relations using the original generator interpretation.
The two sideways crossings are respectively the right mate `mixedSigma j i`
and `tⱼᵢ` times its inverse. Each relation uses one actual mixed-square
invertibility hypothesis, unrestricted `BrundanUpKLR`, and the derived left
adjunctions. Colours are distinct; weights and ordered CL scalars are arbitrary.
No cyclicity or presentation-preservation hypothesis is assumed.

The private three-layer comparisons keep validity and boundary witnesses
independent of the actual diagrams. Their final transports are mapped only
after the free endpoints have been fixed.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams
universe w₁ w₂ u₀ u₁ u₂ v₁ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C] (M : Model S C)
omit M in
/-- The mate of `w` under right adjunctions, read as the composite "cup on the left, `w`, cap on
the right" of three whiskered layers. -/
private theorem sideRG_aux {a b c d : C} {E : a ⟶ b} {R : b ⟶ a} {E' : d ⟶ c} {R' : c ⟶ d} {F : b ⟶ c} {G : a ⟶ d}
    (adj₁ : E ⊣ R) (adj₂ : E' ⊣ R') (w : G ≫ E' ⟶ E ≫ F) :
    (R ≫ G) ◁ (adj₂.unit ▷ 𝟙 d) ≫
        ((R ≫ G) ◁ (ρ_ (E' ≫ R')).hom ≫ (α_ R G (E' ≫ R')).hom ≫ R ◁ (α_ G E' R').inv) ≫
        R ◁ (w ▷ R') ≫
        (R ◁ (α_ E F R').hom ≫ (α_ R E (F ≫ R')).inv ≫ (λ_ _).inv) ≫
        𝟙 b ◁ (adj₁.counit ▷ (F ≫ R')) =
      ((R ≫ G) ◁ (λ_ (𝟙 d)).hom ≫ (ρ_ (R ≫ G)).hom) ≫ mateEquiv adj₁ adj₂ w ≫
        ((λ_ (F ≫ R')).inv ≫ (λ_ (𝟙 b ≫ (F ≫ R'))).inv) := by
  rw [mateEquiv_apply']
  bicategory

omit M in
/-- The mate of `w` under left adjunctions, read as the composite "cup on the right, `w`, cap on
the left" of three whiskered layers. -/
private theorem sideLG_aux {a b c d : C} {R : b ⟶ a} {E : a ⟶ b} {R' : c ⟶ d} {E' : d ⟶ c} {F : b ⟶ c} {G : a ⟶ d}
    (A₁ : R ⊣ E) (A₂ : R' ⊣ E') (w : E ≫ F ⟶ G ≫ E') :
    𝟙 b ◁ (A₁.unit ▷ (F ≫ R')) ≫
        ((λ_ _).hom ≫ (α_ R E (F ≫ R')).hom ≫ R ◁ (α_ E F R').inv) ≫
        R ◁ (w ▷ R') ≫
        (R ◁ (α_ G E' R').hom ≫ (α_ R G (E' ≫ R')).inv ≫ (R ≫ G) ◁ (ρ_ (E' ≫ R')).inv) ≫
        (R ≫ G) ◁ (A₂.counit ▷ 𝟙 d) =
      ((λ_ (𝟙 b ≫ (F ≫ R'))).hom ≫ (λ_ (F ≫ R')).hom) ≫ (mateEquiv A₁ A₂).symm w ≫
        ((ρ_ (R ≫ G)).inv ≫ (R ≫ G) ◁ (λ_ (𝟙 d)).inv) := by
  rw [mateEquiv_symm_apply']
  bicategory

private theorem sideRG_key {x y z t : FB S} {r : x ⟶ y} {e : y ⟶ x} {e' : t ⟶ z} {r' : z ⟶ t} {f : x ⟶ z} {g : y ⟶ t}
    (adj₁ : M.lift.map e ⊣ M.lift.map r) (adj₂ : M.lift.map e' ⊣ M.lift.map r')
    (w : M.lift.map g ≫ M.lift.map e' ⟶ M.lift.map e ≫ M.lift.map f)
    {p₁ : x ⟶ t} {q₁ d₁ c₁ : t ⟶ t} (σp₁ : p₁ ≅ r ≫ g) (σq₁ : q₁ ≅ 𝟙 t) (σd₁ : d₁ ≅ 𝟙 t)
    (σc₁ : c₁ ≅ e' ≫ r') (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj₂.unit)
    {p₂ : x ⟶ y} {q₂ : z ⟶ t} {d₂ c₂ : y ⟶ z} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r')
    (σd₂ : d₂ ≅ g ≫ e') (σc₂ : c₂ ≅ e ≫ f) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ d₃ c₃ : x ⟶ x} {q₃ : x ⟶ t} (σp₃ : p₃ ≅ 𝟙 x) (σq₃ : q₃ ≅ f ≫ r') (σd₃ : d₃ ≅ r ≫ e)
    (σc₃ : c₃ ≅ 𝟙 x) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = adj₁.counit)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ t}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ r ≫ g) (F₁ : f ≫ r' ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ mateEquiv adj₁ adj₂ w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (r ≫ g) (𝟙 t) (x := 𝟙 t) (y := e' ≫ r') adj₂.unit ≫
      M.lift.map₂ ((r ≫ g) ◁ (ρ_ (e' ≫ r')).hom ≫ (α_ r g (e' ≫ r')).hom ≫
        r ◁ (α_ g e' r').inv) ≫
      midK M r r' (x := g ≫ e') (y := e ≫ f) w ≫
      M.lift.map₂ (r ◁ (α_ e f r').hom ≫ (α_ r e (f ≫ r')).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 x) (f ≫ r') (x := r ≫ e) (y := 𝟙 x) adj₁.counit =
      M.lift.map₂ ((r ≫ g) ◁ (λ_ (𝟙 t)).hom ≫ (ρ_ (r ≫ g)).hom) ≫ mateEquiv adj₁ adj₂ w ≫
        M.lift.map₂ ((λ_ (f ≫ r')).inv ≫ (λ_ (𝟙 x ≫ (f ≫ r'))).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map_comp]
    exact sideRG_aux adj₁ adj₂ w
  rw [lift_map₂_eq M _ ((r ≫ g) ◁ (ρ_ (e' ≫ r')).hom ≫ (α_ r g (e' ≫ r')).hom ≫
      r ◁ (α_ g e' r').inv),
    lift_map₂_eq M _ (r ◁ (α_ e f r').hom ≫ (α_ r e (f ≫ r')).inv ≫ (λ_ _).inv),
    reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc]
  erw [Category.assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ F₀, lift_map₂_eq M _ F₁]

private theorem sideLG_key {x y z t : FB S} {r : x ⟶ y} {e : y ⟶ x} {e' : t ⟶ z} {r' : z ⟶ t} {f : x ⟶ z} {g : y ⟶ t}
    (A₁ : M.lift.map r ⊣ M.lift.map e) (A₂ : M.lift.map r' ⊣ M.lift.map e')
    (w : M.lift.map e ≫ M.lift.map f ⟶ M.lift.map g ≫ M.lift.map e')
    {p₁ d₁ c₁ : x ⟶ x} {q₁ : x ⟶ t} (σp₁ : p₁ ≅ 𝟙 x) (σq₁ : q₁ ≅ f ≫ r') (σd₁ : d₁ ≅ 𝟙 x)
    (σc₁ : c₁ ≅ r ≫ e) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = A₁.unit)
    {p₂ : x ⟶ y} {q₂ : z ⟶ t} {d₂ c₂ : y ⟶ z} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r')
    (σd₂ : d₂ ≅ e ≫ f) (σc₂ : c₂ ≅ g ≫ e') (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = w)
    {p₃ : x ⟶ t} {q₃ d₃ c₃ : t ⟶ t} (σp₃ : p₃ ≅ r ≫ g) (σq₃ : q₃ ≅ 𝟙 t) (σd₃ : d₃ ≅ e' ≫ r')
    (σc₃ : c₃ ≅ 𝟙 t) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = A₂.counit)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q : x ⟶ t}
    (E₀ : P ⟶ P₁) (A₁' : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂' : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃' : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ f ≫ r') (F₁ : r ≫ g ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁' ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂' ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃' ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ (mateEquiv A₁ A₂).symm w ≫ M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (𝟙 x) (f ≫ r') (x := 𝟙 x) (y := r ≫ e) A₁.unit ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ r e (f ≫ r')).hom ≫ r ◁ (α_ e f r').inv) ≫
      midK M r r' (x := e ≫ f) (y := g ≫ e') w ≫
      M.lift.map₂ (r ◁ (α_ g e' r').hom ≫ (α_ r g (e' ≫ r')).inv ≫
        (r ≫ g) ◁ (ρ_ (e' ≫ r')).inv) ≫
        midK M (r ≫ g) (𝟙 t) (x := e' ≫ r') (y := 𝟙 t) A₂.counit =
      M.lift.map₂ ((λ_ (𝟙 x ≫ (f ≫ r'))).hom ≫ (λ_ (f ≫ r')).hom) ≫
        (mateEquiv A₁ A₂).symm w ≫
        M.lift.map₂ ((ρ_ (r ≫ g)).inv ≫ (r ≫ g) ◁ (λ_ (𝟙 t)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_inv,
      lift_map_comp]
    exact sideLG_aux A₁ A₂ w
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ r e (f ≫ r')).hom ≫ r ◁ (α_ e f r').inv),
    lift_map₂_eq M _ (r ◁ (α_ g e' r').hom ≫ (α_ r g (e' ≫ r')).inv ≫
      (r ≫ g) ◁ (ρ_ (e' ≫ r')).inv),
    reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc]
  erw [Category.assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ F₀, lift_map₂_eq M _ F₁]

end Categorification.Diagrams.BicatInterp

namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh
open QStrong (sig0_colourSrc_g sig0_colourTgt_g sig0_dom_cross_g sig0_cod_cross_g
  dual_up_g sh_ud sh_ud' sh_dd)

private theorem sideShift (i j : I) (μ : X) :
    sh RD (up i) + (sh RD (dn j) + μ) + RD.iX j = sh RD (up i) + μ := by
  rw [sh_up, sh_dn]; abel

abbrev mixedFEAdmissible (i j : I) (μ : X) :
    Admissible (S := psig RD) (KL3.Diagram.wt RD μ [up i, dn j] : X) μ :=
  ⟨ob RD μ [dn j, up i],
    ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩⟩

private abbrev rA (j : I) (μ : X) : fo (S := psig RD) μ ⟶ fo (sh RD (dn j) + μ) :=
  FreeBicategory.Hom.of (⟨⟨dn j, μ⟩, rfl, rfl⟩ : rq (S := psig RD) μ ⟶ rq (sh RD (dn j) + μ))
private abbrev eA (j : I) (μ : X) : fo (S := psig RD) (sh RD (dn j) + μ) ⟶ fo μ :=
  FreeBicategory.Hom.of (⟨⟨up j, sh RD (dn j) + μ⟩, rfl, sh_ud j μ⟩ :
    rq (S := psig RD) (sh RD (dn j) + μ) ⟶ rq μ)
private abbrev fA (i : I) (μ : X) : fo (S := psig RD) μ ⟶ fo (sh RD (up i) + μ) :=
  FreeBicategory.Hom.of (⟨⟨up i, μ⟩, rfl, rfl⟩ : rq (S := psig RD) μ ⟶ rq (sh RD (up i) + μ))
private abbrev rB (i j : I) (μ : X) : fo (S := psig RD) (sh RD (up i) + μ) ⟶ fo (sh RD (up i) + (sh RD (dn j) + μ)) :=
  FreeBicategory.Hom.of (⟨⟨dn j, sh RD (up i) + μ⟩, rfl, by
    exact @add_left_comm X _ (sh RD (dn j)) (sh RD (up i)) μ⟩ :
    rq (S := psig RD) (sh RD (up i) + μ) ⟶ rq (sh RD (up i) + (sh RD (dn j) + μ)))
private abbrev eB (i j : I) (μ : X) : fo (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ⟶ fo (sh RD (up i) + μ) :=
  FreeBicategory.Hom.of (⟨⟨up j, sh RD (up i) + (sh RD (dn j) + μ)⟩, rfl, by
    change sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + μ)) = _
    rw [sh_up, sh_up, sh_dn]; abel⟩ :
    rq (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ⟶ rq (sh RD (up i) + μ))

private abbrev sideCup (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [], .cup ⟨dn j, (sh RD (up i) + μ)⟩, [⟨up i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩]⟩
private lemma sideCup_core (i j : I) (μ : X) (hv : (sideCup (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCup (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (sideCup (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).dom (sideCup (RD := RD) i j μ).gen)
        (Valid.ok_dom_of hv (by exact @add_left_comm X _ _ _ _)) (Valid.dom_end_of hv (by exact @add_left_comm X _ _ _ _) (by exact @add_left_comm X _ _ _ _)) (Valid.right_ok_of hv (by exact @add_left_comm X _ _ _ _)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (sideCup (RD := RD) i j μ).right μ (Valid.right_ok_of hv (by exact @add_left_comm X _ _ _ _)) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (sideCup (RD := RD) i j μ).left (sh RD (up i) + (sh RD (dn j) + μ)) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ((psig RD).dom (sideCup (RD := RD) i j μ).gen) (sh RD (up i) + (sh RD (dn j) + μ)) (Valid.ok_dom_of hv (by exact @add_left_comm X _ _ _ _)) (Valid.dom_end_of hv (by exact @add_left_comm X _ _ _ _) (by exact @add_left_comm X _ _ _ _)))
        (y := fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ((psig RD).cod (sideCup (RD := RD) i j μ).gen) (sh RD (up i) + (sh RD (dn j) + μ)) (Valid.ok_cod_of hv (by exact @add_left_comm X _ _ _ _)) (Valid.cod_end_of hv (by exact @add_left_comm X _ _ _ _) (by exact @add_left_comm X _ _ _ _)))
        (by exact (S.adj j (x := (sh RD (up i) + (sh RD (dn j) + μ))) (y := (sh RD (up i) + μ)) (sideShift i j μ)).unit) ≫
      S.model.lift.map₂ (layerSplit (sideCup (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).cod (sideCup (RD := RD) i j μ).gen)
        (Valid.ok_cod_of hv (by exact @add_left_comm X _ _ _ _)) (Valid.cod_end_of hv (by exact @add_left_comm X _ _ _ _) (by exact @add_left_comm X _ _ _ _)) (Valid.right_ok_of hv (by exact @add_left_comm X _ _ _ _)) rfl).inv := by
  rfl

private abbrev sideCross (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [⟨dn j, (sh RD (up i) + μ)⟩], .gen (.cross true j i (sh RD (dn j) + μ)), [⟨dn j, μ⟩]⟩
private lemma sideCross_core (i j : I) (μ : X) (hv : (sideCross (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCross (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (sideCross (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).dom (sideCross (RD := RD) i j μ).gen)
        (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl) (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + μ) (sideCross (RD := RD) i j μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (sideCross (RD := RD) i j μ).left (sh RD (up i) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (up i) + μ) ((psig RD).dom (sideCross (RD := RD) i j μ).gen) (sh RD (dn j) + μ) (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl))
        (y := fw (S := psig RD) (sh RD (up i) + μ) ((psig RD).cod (sideCross (RD := RD) i j μ).gen) (sh RD (dn j) + μ) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl))
        ((S.genImg Sc).gen (sideCross (RD := RD) i j μ).gen (sh RD (up i) + μ) (sh RD (dn j) + μ) ((hc.left_end hv).symm) rfl
          (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl)
          (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl)) ≫
      S.model.lift.map₂ (layerSplit (sideCross (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).cod (sideCross (RD := RD) i j μ).gen)
        (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl) (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev sideCap (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [⟨dn j, (sh RD (up i) + μ)⟩, ⟨up i, μ⟩], .cap ⟨dn j, μ⟩, []⟩
private lemma sideCap_core (i j : I) (μ : X) (hv : (sideCap (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCap (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (sideCap (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).dom (sideCap (RD := RD) i j μ).gen)
        (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl) (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) μ (sideCap (RD := RD) i j μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (sideCap (RD := RD) i j μ).left μ (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) μ ((psig RD).dom (sideCap (RD := RD) i j μ).gen) μ (Valid.ok_dom_of hv rfl) (Valid.dom_end_of hv rfl rfl))
        (y := fw (S := psig RD) μ ((psig RD).cod (sideCap (RD := RD) i j μ).gen) μ (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl))
        ((S.adj j (dn_reg j rfl rfl)).counit) ≫
      S.model.lift.map₂ (layerSplit (sideCap (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).cod (sideCap (RD := RD) i j μ).gen)
        (Valid.ok_cod_of hv rfl) (Valid.cod_end_of hv rfl rfl) (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

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

private theorem sideLayers (i j : I) (μ : X)
    (hv1 : (sideCup (RD := RD) i j μ).Valid)
    (hc1 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCup (RD := RD) i j μ).dom)
    (hv2 : (sideCross (RD := RD) i j μ).Valid)
    (hc2 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCross (RD := RD) i j μ).dom)
    (hv3 : (sideCap (RD := RD) i j μ).Valid)
    (hc3 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (sideCap (RD := RD) i j μ).dom)
    {P Q : fo (S := psig RD) μ ⟶ fo (sh RD (up i) + (sh RD (dn j) + μ))}
    (E0 : P ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCup (RD := RD) i j μ).dom.word μ hc1.1 hc1.2.1)
    (E1 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCup (RD := RD) i j μ).cod.word μ (hc1.cod hv1).1 (hc1.cod hv1).2.1) ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCross (RD := RD) i j μ).dom.word μ hc2.1 hc2.2.1)
    (E2 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCross (RD := RD) i j μ).cod.word μ (hc2.cod hv2).1 (hc2.cod hv2).2.1) ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCap (RD := RD) i j μ).dom.word μ hc3.1 hc3.2.1)
    (E3 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (sideCap (RD := RD) i j μ).cod.word μ (hc3.cod hv3).1 (hc3.cod hv3).2.1) ⟶ Q)
    (F0 : P ⟶ rA j μ ≫ fA i (sh RD (dn j) + μ))
    (F1 : fA i μ ≫ rB i j μ ⟶ Q) :
    S.model.lift.map₂ E0 ≫ coreC (S.genImg Sc) hv1 hc1 ≫ S.model.lift.map₂ E1 ≫
      coreC (S.genImg Sc) hv2 hc2 ≫ S.model.lift.map₂ E2 ≫
      coreC (S.genImg Sc) hv3 hc3 ≫ S.model.lift.map₂ E3 =
    S.model.lift.map₂ F0 ≫ S.mixedSigma j i (cross_up_reg i (sh RD (dn j) + μ))
      (sideShift i j μ) (dn_reg j rfl rfl) (cross_up_reg i μ) ≫ S.model.lift.map₂ F1 := by
  erw [sideCup_core S Sc i j μ, sideCross_core S Sc i j μ, sideCap_core S Sc i j μ]
  dsimp only [sideCup, sideCross, sideCap, Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
    Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
    Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
    Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
    Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross_g, sig0_cod_cross_g,
    wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, sig0_colourTgt_g, sig0_colourSrc_g]
  dsimp only [fw]
  refine sideRG_key S.model
    (x := fo (S := psig RD) μ) (y := fo (S := psig RD) (sh RD (dn j) + μ))
    (z := fo (S := psig RD) (sh RD (up i) + μ))
    (t := fo (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)))
    (r := rA (RD := RD) j μ) (e := eA j μ) (r' := rB i j μ) (e' := eB i j μ)
    (f := fA i μ) (g := fA i (sh RD (dn j) + μ))
    (S.adj j (dn_reg j rfl rfl)) (S.adj j (sideShift i j μ))
    (S.cross j i (cross_up_reg i (sh RD (dn j) + μ)) (sideShift i j μ)
      (dn_reg j rfl rfl) (cross_up_reg i μ))
    (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
    (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
    (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
    _ _ _ _ _ _ _ _ _ _ F0 F1
  case e1 | e2 | e3 | e5 | e6 | e9 | e10 | e12 => rfl
  case e7 | e11 => rfl
  case e4 =>
    dsimp only [fw, psig, Signature.pivotal, sig0, KL3.Diagram.inv, List.reverse_cons,
      List.reverse_nil, List.map_cons, List.map_nil, List.append_nil]
    apply congrArg₂ (fun a b => a ≫ b)
    · apply hom_of_congr
      exact congrArg (fun x => (⟨up j, x⟩ : Col I X)) (@add_left_comm X _ _ _ _)
    · rfl
  case e8 =>
    exact comp_of_congr (congrArg (rq (S := psig RD)) (sh_ud j μ)) rfl
      (congrArg (fun x => (⟨up i, x⟩ : Col I X)) (sh_ud j μ))
  case hg1 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
  case hg3 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
  case hg2 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    dsimp only [genImg]
    exact S.cross_congr' j i rfl (sh_ud j μ) _ _ _ _ _ _ _ _ _ _
/-- The original left sideways crossing is the right-adjunction mixed mate. -/
theorem mixed_crossl (i j : I) (μ : X) :
    (S.interp Sc (KL3.Diagram.wt RD μ [up i, dn j]) μ).map
      (ObjectProperty.homMk (X := obAdmissible μ [up i, dn j])
        (Y := mixedFEAdmissible i j μ) (crossl RD i j μ)) =
      S.mixedSigma j i (cross_up_reg i (sh RD (dn j) + μ))
        (sideShift i j μ) (dn_reg j rfl rfl) (cross_up_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, obAdmissible, mixedFEAdmissible, crossl, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom]
  simp only [show ∀ j : I, (dn j).dual = up j from fun _ => rfl]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize g1 : sh RD ((true, j) : Letter I) + (sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = z at *
  obtain rfl : z = sh RD ((true, i) : Letter I) + μ := by rw [← g1, sh_up, sh_up, sh_dn]; abel
  generalize g2 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← g2, sh_up, sh_dn]; abel
  generalize g3 : sh RD ((false, j) : Letter I) + (sh RD ((true, i) : Letter I) + μ) = z at *
  obtain rfl : z = sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ) := by rw [← g3]; abel
  conv_lhs =>
    change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word (M := S.model) ?w0 _]
  erw [eqToHom_word (M := S.model) ?w1 _]
  erw [eqToHom_word (M := S.model) ?w2 _]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    erw [eqToHom_lift S.model (f := fA i μ ≫ rB i j μ)
      (g := fA i μ ≫ rB i j μ) rfl]
  · have h := sideLayers S Sc i j μ ?hv1 ?hc1 ?hv2 ?hc2 ?hv3 ?hc3
      ?E0 ?E1 ?E2 ?E3 (𝟙 _) (𝟙 _)
    erw [PrelaxFunctor.map₂_id, Category.id_comp, PrelaxFunctor.map₂_id, Category.comp_id] at h
    exact h
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals first | rfl | (simp only [g2, g3]; rfl)
private abbrev rightCup (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [⟨dn j, (sh RD (up i) + μ)⟩, ⟨up i, μ⟩], .cup ⟨up j, (sh RD (dn j) + μ)⟩, []⟩
private abbrev rightCross (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [⟨dn j, (sh RD (up i) + μ)⟩], .gen (.cross true i j (sh RD (dn j) + μ)), [⟨dn j, μ⟩]⟩
private abbrev rightCap (i j : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (up i) + (sh RD (dn j) + μ)), [], .cap ⟨up j, (sh RD (up i) + (sh RD (dn j) + μ))⟩, [⟨up i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩]⟩
private lemma rightCup_core (i j : I) (μ : X) (hv : (rightCup (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCup (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (rightCup (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (μ) (μ) μ (hc.left_ok hv) rfl ((psig RD).dom (rightCup (RD := RD) i j μ).gen) (Valid.ok_dom_of hv (sh_ud j μ)) (Valid.dom_end_of hv (sh_ud j μ) (sh_ud j μ)) (Valid.right_ok_of hv (sh_ud j μ)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (μ) (rightCup (RD := RD) i j μ).right (μ) (Valid.right_ok_of hv (sh_ud j μ)) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (rightCup (RD := RD) i j μ).left (μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (μ) ((psig RD).dom (rightCup (RD := RD) i j μ).gen) (μ) (Valid.ok_dom_of hv (sh_ud j μ)) (Valid.dom_end_of hv (sh_ud j μ) (sh_ud j μ)))
        (y := fw (S := psig RD) (μ) ((psig RD).cod (rightCup (RD := RD) i j μ).gen) (μ) (Valid.ok_cod_of hv (sh_ud j μ)) (Valid.cod_end_of hv (sh_ud j μ) (sh_ud j μ)))
        ((S.genImg Sc).gen (rightCup (RD := RD) i j μ).gen (μ) (μ) (sh_ud j μ) (sh_ud j μ) (Valid.ok_dom_of hv (sh_ud j μ)) (Valid.dom_end_of hv (sh_ud j μ) (sh_ud j μ)) (Valid.ok_cod_of hv (sh_ud j μ)) (Valid.cod_end_of hv (sh_ud j μ) (sh_ud j μ))) ≫ S.model.lift.map₂ (layerSplit (rightCup (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (μ) (μ) μ (hc.left_ok hv) rfl ((psig RD).cod (rightCup (RD := RD) i j μ).gen) (Valid.ok_cod_of hv (sh_ud j μ)) (Valid.cod_end_of hv (sh_ud j μ) (sh_ud j μ)) (Valid.right_ok_of hv (sh_ud j μ)) rfl).inv := by
  rfl

private lemma rightCross_core (i j : I) (μ : X) (hv : (rightCross (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCross (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (rightCross (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + μ) (sh RD (dn j) + μ) μ (hc.left_ok hv) rfl ((psig RD).dom (rightCross (RD := RD) i j μ).gen) (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) (rfl)) (Valid.right_ok_of hv (rfl)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + μ) (rightCross (RD := RD) i j μ).right (μ) (Valid.right_ok_of hv (rfl)) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (rightCross (RD := RD) i j μ).left (sh RD (up i) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (up i) + μ) ((psig RD).dom (rightCross (RD := RD) i j μ).gen) (sh RD (dn j) + μ) (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) (rfl)))
        (y := fw (S := psig RD) (sh RD (up i) + μ) ((psig RD).cod (rightCross (RD := RD) i j μ).gen) (sh RD (dn j) + μ) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) (rfl)))
        ((S.genImg Sc).gen (rightCross (RD := RD) i j μ).gen (sh RD (up i) + μ) (sh RD (dn j) + μ) ((hc.left_end hv).symm) (rfl) (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) (rfl)) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) (rfl))) ≫ S.model.lift.map₂ (layerSplit (rightCross (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + μ) (sh RD (dn j) + μ) μ (hc.left_ok hv) rfl ((psig RD).cod (rightCross (RD := RD) i j μ).gen) (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) (rfl)) (Valid.right_ok_of hv (rfl)) rfl).inv := by
  rfl

private lemma rightCap_core (i j : I) (μ : X) (hv : (rightCap (RD := RD) i j μ).Valid)
    (hc : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCap (RD := RD) i j μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (rightCap (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) μ (hc.left_ok hv) rfl ((psig RD).dom (rightCap (RD := RD) i j μ).gen) (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) (rfl)) (Valid.right_ok_of hv (rfl)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (rightCap (RD := RD) i j μ).right (μ) (Valid.right_ok_of hv (rfl)) rfl)
        (fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) (rightCap (RD := RD) i j μ).left (sh RD (up i) + (sh RD (dn j) + μ)) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ((psig RD).dom (rightCap (RD := RD) i j μ).gen) (sh RD (up i) + (sh RD (dn j) + μ)) (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) (rfl)))
        (y := fw (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)) ((psig RD).cod (rightCap (RD := RD) i j μ).gen) (sh RD (up i) + (sh RD (dn j) + μ)) (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) (rfl)))
        ((S.genImg Sc).gen (rightCap (RD := RD) i j μ).gen (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) (rfl) (rfl) (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) (rfl)) (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) (rfl))) ≫ S.model.lift.map₂ (layerSplit (rightCap (RD := RD) i j μ) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) (sh RD (up i) + (sh RD (dn j) + μ)) μ (hc.left_ok hv) rfl ((psig RD).cod (rightCap (RD := RD) i j μ).gen) (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) (rfl)) (Valid.right_ok_of hv (rfl)) rfl).inv := by
  rfl

private theorem rightLayers (i j : I) (μ : X)
    (hv1 : (rightCup (RD := RD) i j μ).Valid)
    (hc1 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCup (RD := RD) i j μ).dom)
    (hv2 : (rightCross (RD := RD) i j μ).Valid)
    (hc2 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCross (RD := RD) i j μ).dom)
    (hv3 : (rightCap (RD := RD) i j μ).Valid)
    (hc3 : Cond (sh RD (up i) + (sh RD (dn j) + μ)) μ (rightCap (RD := RD) i j μ).dom)
    {P Q : fo (S := psig RD) μ ⟶ fo (sh RD (up i) + (sh RD (dn j) + μ))}
    (E0 : P ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCup (RD := RD) i j μ).dom.word μ hc1.1 hc1.2.1)
    (E1 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCup (RD := RD) i j μ).cod.word μ (hc1.cod hv1).1 (hc1.cod hv1).2.1) ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCross (RD := RD) i j μ).dom.word μ hc2.1 hc2.2.1)
    (E2 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCross (RD := RD) i j μ).cod.word μ (hc2.cod hv2).1 (hc2.cod hv2).2.1) ⟶ fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCap (RD := RD) i j μ).dom.word μ hc3.1 hc3.2.1)
    (E3 : (fw (sh RD (up i) + (sh RD (dn j) + μ)) (rightCap (RD := RD) i j μ).cod.word μ (hc3.cod hv3).1 (hc3.cod hv3).2.1) ⟶ Q)
    (F0 : P ⟶ fA i μ ≫ rB i j μ)
    (F1 : rA j μ ≫ fA i (sh RD (dn j) + μ) ⟶ Q) :
    S.model.lift.map₂ E0 ≫ coreC (S.genImg Sc) hv1 hc1 ≫ S.model.lift.map₂ E1 ≫
      coreC (S.genImg Sc) hv2 hc2 ≫ S.model.lift.map₂ E2 ≫
      coreC (S.genImg Sc) hv3 hc3 ≫ S.model.lift.map₂ E3 =
    S.model.lift.map₂ F0 ≫ (mateEquiv (S.adjL j (dn_reg j rfl rfl)) (S.adjL j (sideShift i j μ))).symm
      (S.cross i j (dn_reg j rfl rfl) (cross_up_reg i μ)
        (cross_up_reg i (sh RD (dn j) + μ)) (sideShift i j μ)) ≫ S.model.lift.map₂ F1 := by
  erw [rightCup_core S Sc i j μ, rightCross_core S Sc i j μ, rightCap_core S Sc i j μ]
  dsimp only [rightCup, rightCross, rightCap, Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
    Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
    Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
    Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
    Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross_g, sig0_cod_cross_g,
    wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, sig0_colourTgt_g, sig0_colourSrc_g]
  dsimp only [fw]
  refine sideLG_key S.model
    (x := fo (S := psig RD) μ) (y := fo (S := psig RD) (sh RD (dn j) + μ))
    (z := fo (S := psig RD) (sh RD (up i) + μ))
    (t := fo (S := psig RD) (sh RD (up i) + (sh RD (dn j) + μ)))
    (r := rA (RD := RD) j μ) (e := eA j μ) (r' := rB i j μ) (e' := eB i j μ)
    (f := fA i μ) (g := fA i (sh RD (dn j) + μ))
    (S.adjL j (dn_reg j rfl rfl)) (S.adjL j (sideShift i j μ))
    (S.cross i j (dn_reg j rfl rfl) (cross_up_reg i μ)
      (cross_up_reg i (sh RD (dn j) + μ)) (sideShift i j μ))
    (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
    (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
    (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
    _ _ _ _ _ _ _ _ _ _ F0 F1
  case e1 | e2 | e3 | e5 | e6 | e8 | e9 | e10 | e12 => rfl
  case e4 =>
    dsimp only [fw, psig, Signature.pivotal, sig0, KL3.Diagram.inv, List.reverse_cons,
      List.reverse_nil, List.map_cons, List.map_nil, List.append_nil]
    apply congrArg₂ (fun a b => a ≫ b)
    · apply hom_of_congr
      exact congrArg (fun x => (⟨dn j, x⟩ : Col I X)) (sh_ud j μ)
    · rfl
  case e7 =>
    exact comp_of_congr (congrArg (rq (S := psig RD)) (sh_ud j μ)) rfl
      (congrArg (fun x => (⟨up i, x⟩ : Col I X)) (sh_ud j μ))
  case e11 =>
    have hs : sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + μ)) = sh RD (up i) + μ := by
      rw [sh_up, sh_up, sh_dn]; abel
    exact comp_of_congr (congrArg (rq (S := psig RD)) hs) rfl
      (congrArg (fun x => (⟨dn j, x⟩ : Col I X)) hs)
  case hg1 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    dsimp only [genImg]
    erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
  case hg2 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    dsimp only [genImg]
    exact S.cross_congr' i j (sh_ud j μ) rfl _ _ _ _ _ _ _ _ _ _
  case hg3 =>
    erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
    dsimp only [genImg]
    erw [eqToHom_refl, Category.comp_id]
    apply S.adjL_counit_congr
    change sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + μ)) = sh RD (up i) + μ
    rw [sh_up, sh_up, sh_dn]; abel
/-- The original right sideways crossing is the inverse left mate. -/
theorem mixed_crossr_mate (i j : I) (μ : X) :
    (S.interp Sc (KL3.Diagram.wt RD μ [up i, dn j]) μ).map
      (ObjectProperty.homMk (X := mixedFEAdmissible i j μ)
        (Y := obAdmissible μ [up i, dn j]) (crossr RD i j μ)) =
      (mateEquiv (S.adjL j (dn_reg j rfl rfl)) (S.adjL j (sideShift i j μ))).symm
      (S.cross i j (dn_reg j rfl rfl) (cross_up_reg i μ)
        (cross_up_reg i (sh RD (dn j) + μ)) (sideShift i j μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, obAdmissible, mixedFEAdmissible, crossr, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom]
  simp only [show ∀ j : I, (up j).dual = dn j from fun _ => rfl]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize g1 : sh RD ((true, j) : Letter I) + (sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = z at *
  obtain rfl : z = sh RD ((true, i) : Letter I) + μ := by rw [← g1, sh_up, sh_up, sh_dn]; abel
  generalize g2 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← g2, sh_up, sh_dn]; abel
  generalize g3 : sh RD ((false, j) : Letter I) + (sh RD ((true, i) : Letter I) + μ) = z at *
  obtain rfl : z = sh RD ((true, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ) := by rw [← g3]; abel
  conv_lhs =>
    change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word (M := S.model) ?w0 _]
  erw [eqToHom_word (M := S.model) ?w1 _]
  erw [eqToHom_word (M := S.model) ?w2 _]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    erw [eqToHom_lift S.model (f := rA j μ ≫ fA i (sh RD (dn j) + μ))
      (g := rA j μ ≫ fA i (sh RD (dn j) + μ)) rfl]
  · have h := rightLayers S Sc i j μ ?hv1 ?hc1 ?hv2 ?hc2 ?hv3 ?hc3
      ?E0 ?E1 ?E2 ?E3 (𝟙 _) (𝟙 _)
    erw [PrelaxFunctor.map₂_id, Category.id_comp, PrelaxFunctor.map₂_id, Category.comp_id] at h
    exact h
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals first | rfl | (simp only [g1]; rfl) | (simp only [g2]; rfl)
variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

private theorem mixed_leftMate_inverse (H : BrundanUpKLR S Sc)
    (i j : I) (hij : i ≠ j) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)] :
    (mateEquiv (S.adjL i h₁) (S.adjL i h₇)).symm
      (S.cross j i h₁ h₂ h₆ h₇) =
        (Sc.t i j : k) • inv (S.mixedSigma i j h₆ h₇ h₁ h₂) := by
  exact (Equiv.symm_apply_eq _).mpr (S.mixed_mate Sc H i j hij h₁ h₂ h₆ h₇).symm

/-- The original right sideways crossing is the scalar multiple of the inverse mixed mate. -/
theorem mixed_crossr (H : BrundanUpKLR S Sc) (i j : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma j i (cross_up_reg i (sh RD (dn j) + μ))
      (sideShift i j μ) (dn_reg j rfl rfl) (cross_up_reg i μ))] :
    (S.interp Sc (KL3.Diagram.wt RD μ [up i, dn j]) μ).map
      (ObjectProperty.homMk (X := mixedFEAdmissible i j μ)
        (Y := obAdmissible μ [up i, dn j]) (crossr RD i j μ)) =
    (Sc.t j i : k) • inv (S.mixedSigma j i (cross_up_reg i (sh RD (dn j) + μ))
      (sideShift i j μ) (dn_reg j rfl rfl) (cross_up_reg i μ)) := by
  rw [S.mixed_crossr_mate]
  exact S.mixed_leftMate_inverse Sc H j i hij.symm _ _ _ _

/-- The actual CL down-up relation on `EᵢFⱼ`, with coefficient `tⱼᵢ`. -/
theorem mixed_downupEF_rel (H : BrundanUpKLR S Sc) (i j : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma j i (cross_up_reg i (sh RD (dn j) + μ))
      (sideShift i j μ) (dn_reg j rfl rfl) (cross_up_reg i μ))] :
    admissibleMap (S.genImg Sc) (obAdmissible μ [up i, dn j]).property
      (obAdmissible μ [up i, dn j]).property
      (CL.relationCL RD k Sc (.downupEF i j hij μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) -
      (Sc.t j i : k) • LinDiagram.of (𝟙 _)) = 0
  erw [map_sub, map_smul, admissibleMap_of, admissibleMap_of]
  apply sub_eq_zero.mpr
  change (S.interp Sc (KL3.Diagram.wt RD μ [up i, dn j]) μ).map
    ((ObjectProperty.homMk (X := obAdmissible μ [up i, dn j])
      (Y := mixedFEAdmissible i j μ) (crossl RD i j μ)) ≫
     (ObjectProperty.homMk (X := mixedFEAdmissible i j μ)
      (Y := obAdmissible μ [up i, dn j]) (crossr RD i j μ))) =
    (Sc.t j i : k) • (S.interp Sc (KL3.Diagram.wt RD μ [up i, dn j]) μ).map
      (𝟙 (obAdmissible μ [up i, dn j]))
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, S.mixed_crossl, S.mixed_crossr Sc H i j hij μ,
    Linear.comp_smul, IsIso.hom_inv_id]

/-- The actual CL down-up relation on `FᵢEⱼ`, with coefficient `tᵢⱼ`. -/
theorem mixed_downupFE_rel (H : BrundanUpKLR S Sc) (i j : I) (hij : i ≠ j) (μ : X)
    [IsIso (S.mixedSigma i j (cross_up_reg j (sh RD (dn i) + μ))
      (sideShift j i μ) (dn_reg i rfl rfl) (cross_up_reg j μ))] :
    admissibleMap (S.genImg Sc) (mixedFEAdmissible j i μ).property
      (mixedFEAdmissible j i μ).property
      (CL.relationCL RD k Sc (.downupFE i j hij μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
      (Sc.t i j : k) • LinDiagram.of (𝟙 _)) = 0
  erw [map_sub, map_smul, admissibleMap_of, admissibleMap_of]
  apply sub_eq_zero.mpr
  change (S.interp Sc (KL3.Diagram.wt RD μ [up j, dn i]) μ).map
    ((ObjectProperty.homMk (X := mixedFEAdmissible j i μ)
      (Y := obAdmissible μ [up j, dn i]) (crossr RD j i μ)) ≫
     (ObjectProperty.homMk (X := obAdmissible μ [up j, dn i])
      (Y := mixedFEAdmissible j i μ) (crossl RD j i μ))) =
    (Sc.t i j : k) • (S.interp Sc (KL3.Diagram.wt RD μ [up j, dn i]) μ).map
      (𝟙 (mixedFEAdmissible j i μ))
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, S.mixed_crossl, S.mixed_crossr Sc H j i hij.symm μ,
    Linear.smul_comp, IsIso.inv_hom_id]
  rfl

end RouqFamily
end Categorification.TwoRep
