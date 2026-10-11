import Categorification.TwoRep.RouqCyc
import Categorification.TwoRep.RouqMixedNonpositive
import Categorification.TwoRep.ModelQStrongCyc
/-!
# Right crossing cyclicity in the Rouquier interpretation

`RouqFamily.mixed_cycCrossR_rel` annihilates the actual right crossing-cyclicity
relation of the CL presentation at every weight and for arbitrary ordered
colours. This direction follows from the definition of the downward crossing;
it needs neither mixed inversion nor an upward KLR hypothesis.

Concrete free-word transports and the five interpreted rotation layers are
checked separately before applying the two-strand rotation identity. No scalar
normalization is imposed. The left crossing relation is not proved here.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
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
  dual_up_g sh_ud sh_ud' sh_dd)


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

private lemma capDom_fw (i : I) (μ : X) (h e) :
    fw (S := psig RD) (sh RD (dn i) + μ) ((psig RD).dom (.cap ⟨up i, sh RD (dn i) + μ⟩))
      (sh RD (dn i) + μ) h e = upArrow (RD := RD) i μ ≫ dnArrow i μ := by
  exact comp_of_congr (sh_ud (RD := RD) i μ) rfl
    (congrArg (Col.mk (dn i)) (sh_ud (RD := RD) i μ))

private lemma cupOne_hom (j : I) (μ : X) :
    FreeBicategory.Hom.of (⟨⟨dn j, sh RD (up j) + (sh RD (dn j) + μ)⟩,
      sh_ud (RD := RD) j μ, by
        change sh RD (dn j) + (sh RD (up j) + (sh RD (dn j) + μ)) = _
        rw [sh_ud (RD := RD) j μ]⟩ : rq (S := psig RD) μ ⟶ rq (sh RD (dn j) + μ)) =
      dnArrow (RD := RD) j μ := by
  exact hom_of_congr (congrArg (Col.mk (dn j)) (sh_ud (RD := RD) j μ))

private lemma cupTwo_hom (i j : I) (μ : X) :
    FreeBicategory.Hom.of (⟨⟨dn i, sh RD (up i) + (sh RD (dn j) + (sh RD (dn i) + μ))⟩,
      sh_ud' (RD := RD) i j μ, by
        change sh RD (dn i) + (sh RD (up i) + (sh RD (dn j) + (sh RD (dn i) + μ))) = _
        rw [sh_ud' (RD := RD) i j μ]; exact sh_dd i j μ⟩ :
      rq (S := psig RD) (sh RD (dn j) + μ) ⟶ rq (sh RD (dn j) + (sh RD (dn i) + μ))) =
      swapDnArrow (RD := RD) i j μ := by
  exact hom_of_congr (congrArg (Col.mk (dn i)) (sh_ud' (RD := RD) i j μ))

private abbrev cup1 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩], .cup ⟨up j, (sh RD (dn j) + μ)⟩, []⟩

private lemma cup1_core (j i : I) (μ : X) (hv : (cup1 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup1 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cup1 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).dom (cup1 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv (sh_ud (RD := RD) j μ)) (Valid.dom_end_of hv (sh_ud (RD := RD) j μ) (sh_ud (RD := RD) j μ))
        (Valid.right_ok_of hv (sh_ud (RD := RD) j μ)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) μ (cup1 (RD := RD) j i μ).right μ (Valid.right_ok_of hv (sh_ud (RD := RD) j μ)) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cup1 (RD := RD) j i μ).left μ (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) μ ((psig RD).dom (cup1 (RD := RD) j i μ).gen) μ
          (Valid.ok_dom_of hv (sh_ud (RD := RD) j μ)) (Valid.dom_end_of hv (sh_ud (RD := RD) j μ) (sh_ud (RD := RD) j μ)))
        (y := fw (S := psig RD) μ ((psig RD).cod (cup1 (RD := RD) j i μ).gen) μ
          (Valid.ok_cod_of hv (sh_ud (RD := RD) j μ)) (Valid.cod_end_of hv (sh_ud (RD := RD) j μ) (sh_ud (RD := RD) j μ)))
        ((S.adjL j (x := (sh RD (dn j) + μ)) (y := μ) (dn_reg j rfl rfl)).unit) ≫
      S.model.lift.map₂ (layerSplit (cup1 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ μ μ
        (hc.left_ok hv) rfl ((psig RD).cod (cup1 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv (sh_ud (RD := RD) j μ)) (Valid.cod_end_of hv (sh_ud (RD := RD) j μ) (sh_ud (RD := RD) j μ))
        (Valid.right_ok_of hv (sh_ud (RD := RD) j μ)) rfl).inv := by
  rfl

private abbrev cup2 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩, ⟨up j, (sh RD (dn j) + μ)⟩], .cup ⟨up i, (sh RD (dn j) + (sh RD (dn i) + μ))⟩, [⟨dn j, μ⟩]⟩

private lemma cup2_core (j i : I) (μ : X) (hv : (cup2 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cup2 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cup2 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cup2 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv (sh_ud' (RD := RD) i j μ)) (Valid.dom_end_of hv (sh_ud' (RD := RD) i j μ) (sh_ud' (RD := RD) i j μ))
        (Valid.right_ok_of hv (sh_ud' (RD := RD) i j μ)) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + μ) (cup2 (RD := RD) j i μ).right μ (Valid.right_ok_of hv (sh_ud' (RD := RD) i j μ)) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cup2 (RD := RD) j i μ).left (sh RD (dn j) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn j) + μ) ((psig RD).dom (cup2 (RD := RD) j i μ).gen) (sh RD (dn j) + μ)
          (Valid.ok_dom_of hv (sh_ud' (RD := RD) i j μ)) (Valid.dom_end_of hv (sh_ud' (RD := RD) i j μ) (sh_ud' (RD := RD) i j μ)))
        (y := fw (S := psig RD) (sh RD (dn j) + μ) ((psig RD).cod (cup2 (RD := RD) j i μ).gen) (sh RD (dn j) + μ)
          (Valid.ok_cod_of hv (sh_ud' (RD := RD) i j μ)) (Valid.cod_end_of hv (sh_ud' (RD := RD) i j μ) (sh_ud' (RD := RD) i j μ)))
        ((S.adjL i (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := (sh RD (dn j) + μ)) (dn_reg i rfl (sh_dd i j μ))).unit) ≫
      S.model.lift.map₂ (layerSplit (cup2 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + μ) (sh RD (dn j) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cup2 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv (sh_ud' (RD := RD) i j μ)) (Valid.cod_end_of hv (sh_ud' (RD := RD) i j μ) (sh_ud' (RD := RD) i j μ))
        (Valid.right_ok_of hv (sh_ud' (RD := RD) i j μ)) rfl).inv := by
  rfl

private abbrev cross3 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn j, (sh RD (dn i) + μ)⟩, ⟨dn i, μ⟩], .gen (.cross true j i (sh RD (dn j) + (sh RD (dn i) + μ))), [⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩]⟩

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
        (x := fw (S := psig RD) μ ((psig RD).dom (cross3 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ))
          (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl))
        (y := fw (S := psig RD) μ ((psig RD).cod (cross3 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ))
          (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl))
        ((S.genImg Sc).gen (cross3 (RD := RD) j i μ).gen μ (sh RD (dn j) + (sh RD (dn i) + μ)) ((hc.left_end hv).symm) rfl
          (Valid.ok_dom_of hv ((hc.left_end hv).symm)) (Valid.dom_end_of hv ((hc.left_end hv).symm) rfl)
          (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl)) ≫
      S.model.lift.map₂ (layerSplit (cross3 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) μ (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cross3 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv ((hc.left_end hv).symm)) (Valid.cod_end_of hv ((hc.left_end hv).symm) rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev cap4 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [⟨dn j, (sh RD (dn i) + μ)⟩], .cap ⟨up i, (sh RD (dn i) + μ)⟩, [⟨up j, (sh RD (dn j) + (sh RD (dn i) + μ))⟩, ⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩]⟩

private lemma cap4_core (j i : I) (μ : X) (hv : (cap4 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap4 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cap4 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn i) + μ) (sh RD (dn i) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cap4 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn i) + μ) (cap4 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cap4 (RD := RD) j i μ).left (sh RD (dn i) + μ) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn i) + μ) ((psig RD).dom (cap4 (RD := RD) j i μ).gen) (sh RD (dn i) + μ)
          (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) rfl))
        (y := fw (S := psig RD) (sh RD (dn i) + μ) ((psig RD).cod (cap4 (RD := RD) j i μ).gen) (sh RD (dn i) + μ)
          (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) rfl))
        ((S.adjL i (x := (sh RD (dn i) + μ)) (y := sh RD (up i) + (sh RD (dn i) + μ)) (up_reg i rfl rfl)).counit) ≫
      S.model.lift.map₂ (layerSplit (cap4 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn i) + μ) (sh RD (dn i) + μ) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cap4 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) rfl)
        (Valid.right_ok_of hv rfl) rfl).inv := by
  rfl

private abbrev cap5 (j i : I) (μ : X) : Layer (psig RD) :=
  ⟨(sh RD (dn j) + (sh RD (dn i) + μ)), [], .cap ⟨up j, (sh RD (dn j) + (sh RD (dn i) + μ))⟩, [⟨dn i, (sh RD (dn j) + μ)⟩, ⟨dn j, μ⟩]⟩

private lemma cap5_core (j i : I) (μ : X) (hv : (cap5 (RD := RD) j i μ).Valid)
    (hc : Cond (sh RD (dn j) + (sh RD (dn i) + μ)) μ (cap5 (RD := RD) j i μ).dom) :
    coreC (S.genImg Sc) hv hc =
      S.model.lift.map₂ (layerSplit (cap5 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).dom (cap5 (RD := RD) j i μ).gen)
        (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) rfl)
        (Valid.right_ok_of hv rfl) rfl).hom ≫
      midK S.model
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cap5 (RD := RD) j i μ).right μ (Valid.right_ok_of hv rfl) rfl)
        (fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) (cap5 (RD := RD) j i μ).left (sh RD (dn j) + (sh RD (dn i) + μ)) (hc.left_ok hv) rfl)
        (x := fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ((psig RD).dom (cap5 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ))
          (Valid.ok_dom_of hv (rfl)) (Valid.dom_end_of hv (rfl) rfl))
        (y := fw (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)) ((psig RD).cod (cap5 (RD := RD) j i μ).gen) (sh RD (dn j) + (sh RD (dn i) + μ))
          (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) rfl))
        ((S.adjL j (x := (sh RD (dn j) + (sh RD (dn i) + μ))) (y := sh RD (up j) + (sh RD (dn j) + (sh RD (dn i) + μ))) (up_reg j rfl rfl)).counit) ≫
      S.model.lift.map₂ (layerSplit (cap5 (RD := RD) j i μ) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) (sh RD (dn j) + (sh RD (dn i) + μ)) μ
        (hc.left_ok hv) rfl ((psig RD).cod (cap5 (RD := RD) j i μ).gen)
        (Valid.ok_cod_of hv (rfl)) (Valid.cod_end_of hv (rfl) rfl)
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

/-- The swapped two-downward-strand boundary, at the original outer regions. -/
abbrev mixedSwapAdmissible (j i : I) (μ : X) :
    Admissible (S := psig RD) (KL3.Diagram.wt RD μ [dn j, dn i] : X) μ :=
  ⟨ob RD μ [dn i, dn j],
    ⟨⟨@add_left_comm X _ _ _ _, rfl, trivial⟩, rfl, @add_left_comm X _ _ _ _⟩⟩

private theorem rotationLayers (j i : I) (μ : X)
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
    (((Sc.t i j)⁻¹ : kˣ) : k) • (S.model.lift.map₂ E0 ≫
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
  rw [crossDn]
  refine scaled_midK S.model _ _ _ _ _ _ _ _ _ ?_
  dsimp only [fw]
  refine rot2G_key S.model
    (a := fo (S := psig RD) μ) (b := fo (S := psig RD) (sh RD (dn i) + μ))
    (b' := fo (S := psig RD) (sh RD (dn j) + μ))
    (c := fo (S := psig RD) (sh RD (dn j) + (sh RD (dn i) + μ)))
    (r₁ := dnArrow (RD := RD) i μ) (e₁ := upArrow i μ)
    (r₂ := dnArrow j (sh RD (dn i) + μ)) (e₂ := upArrow j (sh RD (dn i) + μ))
    (s₁ := dnArrow j μ) (f₁ := upArrow j μ)
    (s₂ := swapDnArrow i j μ) (f₂ := swapUpArrow i j μ)
    (S.adjL i (x := sh RD ((false, i) : Letter I) + μ) (y := μ) (dn_reg i rfl rfl))
    (S.adjL j (x := sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))
      (y := sh RD ((false, i) : Letter I) + μ) (dn_reg j rfl rfl))
    (S.adjL j (x := sh RD ((false, j) : Letter I) + μ) (y := μ) (dn_reg j rfl rfl))
    (S.adjL i (x := sh RD ((false, j) : Letter I) + (sh RD ((false, i) : Letter I) + μ))
      (y := sh RD ((false, j) : Letter I) + μ) (dn_reg i rfl (sh_dd i j μ)))
    (S.cross j i (dn_reg i rfl (sh_dd i j μ)) (dn_reg j rfl rfl)
      (dn_reg j rfl rfl) (dn_reg i rfl rfl))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (whiskerRightIso (eqToIso (cupOne_hom (RD := RD) j μ)) _) _ ?hg1
    (Iso.refl _) (α_ _ _ _) (Iso.refl _)
    (whiskerRightIso (eqToIso (cupTwo_hom (RD := RD) i j μ)) _) _ ?hg2
    (Iso.refl _) (Iso.refl _) (eqToIso ?d3) (eqToIso ?c3) _ ?hg3
    (Iso.refl _) (Iso.refl _) (eqToIso ?d4) (Iso.refl _) _ ?hg4
    (Iso.refl _) (Iso.refl _) (eqToIso ?d5) (Iso.refl _) _ ?hg5
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case d3 => exact crossDom_fw (RD := RD) j i μ _ _
  case c3 => exact crossCod_fw (RD := RD) j i μ _ _
  case d4 => exact capDom_fw (RD := RD) i μ _ _
  case d5 => exact capDom_fw (RD := RD) j (sh RD (dn i) + μ) _ _
  case hg1 | hg2 =>
    simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp, whiskerRightIso_hom,
      eqToIso.hom, lift_map₂_whiskerRight, lift_map₂_eqToHom]
    erw [eqToHom_refl, id_whiskerRight, Category.comp_id]
  case hg3 =>
    simp only [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
    exact S.cross_congr' j i (sh_ud' (RD := RD) i j μ) (sh_ud j (sh RD ((false, i) : Letter I) + μ))
      _ _ _ _ _ _ _ _ _ _
  case hg4 =>
    simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, eqToIso.inv,
      lift_map₂_eqToHom]
    erw [Category.comp_id]
    exact S.adjL_counit_congr i (sh_ud i μ) _ _ _
  case hg5 =>
    simp only [Iso.refl_hom, PrelaxFunctor.map₂_id, eqToIso.inv,
      lift_map₂_eqToHom]
    erw [Category.comp_id]
    exact S.adjL_counit_congr j (sh_ud j (sh RD ((false, i) : Letter I) + μ)) _ _ _
  case hg6 =>
    simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
    erw [Category.comp_id]
    congr 1

/-- The right rotation evaluates to the unchanged downward crossing, with its ordered scalar. -/
theorem mixed_cycCrossR (j i : I) (μ : X) :
    (((Sc.t i j)⁻¹ : kˣ) : k) •
      (S.interp Sc (KL3.Diagram.wt RD μ [dn j, dn i]) μ).map
        (ObjectProperty.homMk (X := obAdmissible μ [dn j, dn i])
          (Y := mixedSwapAdmissible j i μ) (rotCrossR RD j i μ)) =
      (S.interp Sc (KL3.Diagram.wt RD μ [dn j, dn i]) μ).map
        (ObjectProperty.homMk (X := obAdmissible μ [dn j, dn i])
          (Y := mixedSwapAdmissible j i μ) (downCross RD j i μ)) := by
  change _ • admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, obAdmissible, mixedSwapAdmissible, rotCrossR, downCross, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, dual_up_g]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize g1 : sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = y at *
  obtain rfl : y = sh RD ((false, j) : Letter I) + μ := by rw [← g1, sh_up, sh_dn]; abel
  generalize g2 : sh RD ((true, j) : Letter I) + (sh RD ((false, j) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← g2, sh_up, sh_dn]; abel
  generalize g3 : sh RD ((true, i) : Letter I) + (sh RD ((true, j) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ))) = z at *
  obtain rfl : μ = z := by rw [← g3, sh_up, sh_up, sh_dn, sh_dn]; abel
  generalize g4 : sh RD ((true, j) : Letter I) + (sh RD ((false, i) : Letter I) + (sh RD ((false, j) : Letter I) + μ)) = w at *
  obtain rfl : w = sh RD ((false, i) : Letter I) + μ := by rw [← g4, sh_up, sh_dn, sh_dn]; abel
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
  · exact rotationLayers S Sc j i μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals first | rfl | (simp only [g1, g2, g3, g4]; rfl)

/-- The actual CL right crossing-cyclicity relation vanishes for all ordered colours. -/
theorem mixed_cycCrossR_rel (j i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (obAdmissible μ [dn j, dn i]).property
      (mixedSwapAdmissible j i μ).property
      (CL.relationCL RD k Sc (.cycCrossR j i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    ((((Sc.t i j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD j i μ) -
      LinDiagram.of (downCross RD j i μ)) = 0
  erw [map_sub, map_smul, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.mixed_cycCrossR Sc j i μ)

end RouqFamily
end Categorification.TwoRep
