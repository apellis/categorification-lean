/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Grassmannian
import Categorification.Diagrams.KL3.Grading
import Categorification.Diagrams.KL3.Pitchfork

/-!
# The symmetry `ψ̃` of `U`: reflection in a horizontal axis

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2
(TeX label `sec_symm`), paragraph "Reflect across the x-axis and invert orientation", eq. (3.44).

KL III: "This transformation preserves the order of composition of 1-morphisms, but is
contravariant with respect to composition of 2-morphisms. Hence, by extending this
transformation to sums of diagrams we get a 2-isomorphism `ψ̃ : U → U^co`, `λ ↦ λ`,
`1_μ E_s 1_λ {t} ↦ 1_μ E_s 1_λ {-t}`, and on 2-morphisms `ψ̃` reflects the diagrams
representing summands across the `x`-axis and inverts the orientation. [...] it is clear that
`ψ̃` is invertible since its square is the identity."

Reflecting a diagram across the `x`-axis reverses the orientation of every strand; inverting the
orientation afterwards restores it. Hence `ψ̃` fixes all regions and all 1-morphisms, and on
generators (`Psi.gen`, `Psi.shape`):

* dots and crossings are reflected: `x ↦ x` and `ψ_{ij} : E_i E_j ⟶ E_j E_i` goes to
  `ψ_{ji} : E_j E_i ⟶ E_i E_j` (the same for downward strands), with no signs;
* the cup `1 ⟶ c c*` goes to the cap `c c* ⟶ 1` (in the library's labelling: `cup c ↦ cap c*`),
  and the cap `c* c ⟶ 1` goes to the cup `1 ⟶ c* c` (`cap c ↦ cup c*`).

In our formalization `U` has no grading shifts (`Categorification.Diagrams.KL3.Presentation`), so
`{t} ↦ {-t}` becomes the statement that `ψ̃` preserves the degree of every 2-morphism
(`psiU_homDeg`): the reflected 2-morphism `y ⟶ x` of a 2-morphism `x ⟶ y` of degree `d` has
degree `d`, i.e. is a 2-morphism `y{-t'} ⟶ x{-t}` of degree zero if the original was one
`x{t} ⟶ y{t'}`.

## Construction

`ψ̃` is constructed by the library's soundness theorem `Presentation.lift` as a `k`-linear functor
`psiU RD k : (pres RD k).Presented ⥤ (pres RD k).Presentedᵒᵖ` (the opposite category of a
`k`-linear category is `k`-linear, `CategoryTheory.linearOpposite`). On a diagram it reverses
the order of the layers and reflects every generator (`reflD`), so it is the identity on objects
and contravariant on 2-morphisms; `psiU_whisk` says that it commutes with whiskering, i.e.
preserves horizontal composition (a strict 2-functor `U → U^co`). The soundness hypotheses are:

* the interchange law is reflected to the interchange law (`reflLin_interchange`);
* the zigzag relations (3.1)–(3.2) are exchanged: the reflection of the left zigzag of `c` is the
  right zigzag of `c*` and vice versa;
* every relation of Definition 3.1 is reflected to a relation that holds in `U`
  (`psiL_relation`): (3.3) `cycDotR ↔ cycDotL`; `eq_cyclic_cross-gen` `cycCrossR j i ↔
  cycCrossL i j`; bubbles, the curl relations and the relations `eq_downup_ij-gen` are
  reflected to themselves (all bubbles, real and fake, are fixed: `psiL_cwL`, `psiL_ccwL`);
  `eq_ident_decomp` is reflected to itself after sliding the dots around the cups and caps
  (`dg_dots_cap_dn`, `dg_dots_cupUp`, …) and reindexing the double sum (`sum_triangle_swap`);
  the relations of
  `R(ν)` on upward strands are exchanged among themselves (`eq_nil_dotslide`: the two forms;
  `eq_dot_slide_ij-gen`: `slideLNe c d ↔ slideRNe d c`; `eq_r3_easy-gen`: `braid c d e ↔
  braid e d c`), the polynomial terms being fixed because dots on different strands commute.

## Main results

* `psiU RD k : (pres RD k).Presented ⥤ (pres RD k).Presentedᵒᵖ`, `k`-linear;
  `psiU_diag`: on a diagram it is the reflected diagram; `psiU_whisk`: it commutes with
  whiskering;
* `psiU_psiU`, `psiU_comp_leftOp`: `ψ̃² = 1`;
* `psiU_homDeg`: `ψ̃` preserves degrees;
* `psiU_dg`: `ψ̃` on normal-form diagrams; on generators `psiU_dot`, `psiU_cross`,
  `psiU_cup_EF`, `psiU_cup_FE`, `psiU_cap_EF`, `psiU_cap_FE`;
* on bubbles: `psiU_cwU`, `psiU_ccwU` (all bubbles, including fake bubbles, are fixed);
* `KPsi.lin_kreflLin_relation`: the horizontal flip is a symmetry of the diagrammatic KLR
  relations, for arbitrary `Q` (KL I, end of §2.1).

The opposite of a `k`-linear category is `k`-linear (`CategoryTheory.linearOpposite`; not in the
pinned Mathlib).
-/

noncomputable section

namespace CategoryTheory

universe w₀ v₀ u₀

/-- The opposite of an `R`-linear category is `R`-linear, with `r • f.op = (r • f).op`. -/
instance linearOpposite (R : Type w₀) [Semiring R] (C : Type u₀) [Category.{v₀} C] [Preadditive C]
    [Linear R C] : Linear R Cᵒᵖ where
  homModule _ _ :=
    { smul := fun r f => (r • f.unop).op
      one_smul := fun f => Quiver.Hom.unop_inj (one_smul R f.unop)
      mul_smul := fun r s f => Quiver.Hom.unop_inj (mul_smul r s f.unop)
      smul_zero := fun r => Quiver.Hom.unop_inj (smul_zero r)
      smul_add := fun r f g => Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      add_smul := fun r s f => Quiver.Hom.unop_inj (add_smul r s f.unop)
      zero_smul := fun f => Quiver.Hom.unop_inj (zero_smul R f.unop) }
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ g.unop r f.unop)
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ r g.unop f.unop)

@[simp] theorem unop_smul' {R : Type w₀} [Semiring R] {C : Type u₀} [Category.{v₀} C]
    [Preadditive C] [Linear R C] {X Y : Cᵒᵖ} (r : R) (f : X ⟶ Y) : (r • f).unop = r • f.unop :=
  rfl

@[simp] theorem op_smul' {R : Type w₀} [Semiring R] {C : Type u₀} [Category.{v₀} C]
    [Preadditive C] [Linear R C] {X Y : C} (r : R) (f : X ⟶ Y) : (r • f).op = r • f.op :=
  rfl

end CategoryTheory

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

namespace Psi

variable {RD}

/-! ## Reflection of generators, layers and diagrams -/

/-- The reflection of a generator across the `x`-axis, followed by the inversion of the
orientation of all strands: dots are fixed, the crossing `(ε,i)(ε,j) ⟶ (ε,j)(ε,i)` goes to
`(ε,j)(ε,i) ⟶ (ε,i)(ε,j)`, `cup c ↦ cap c*`, `cap c ↦ cup c*`. -/
def gen : (psig RD).Gen → (psig RD).Gen
  | .gen (.dot c) => .gen (.dot c)
  | .gen (.cross ε i j ν) => .gen (.cross ε j i ν)
  | .cup c => .cap ((inv RD).dual c)
  | .cap c => .cup ((inv RD).dual c)

theorem inv_dual_dual (c : Col I X) : (inv RD).dual ((inv RD).dual c) = c := (inv RD).dual_dual c

theorem gen_dom (g : (psig RD).Gen) : (psig RD).dom (gen g) = (psig RD).cod g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · show [(inv RD).dual ((inv RD).dual c), (inv RD).dual c] = [c, (inv RD).dual c]
    rw [inv_dual_dual]
  · rfl

theorem gen_cod (g : (psig RD).Gen) : (psig RD).cod (gen g) = (psig RD).dom g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · rfl
  · show [(inv RD).dual c, (inv RD).dual ((inv RD).dual c)] = [(inv RD).dual c, c]
    rw [inv_dual_dual]

theorem gen_left (g : (psig RD).Gen) : (psig RD).left (gen g) = (psig RD).left g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · exact add_left_comm (sh RD (ε, j)) (sh RD (ε, i)) ν
  · rfl
  · show (sig0 RD).colourSrc ((inv RD).dual c) = c.r
    rw [(inv RD).src_dual]; rfl

theorem gen_right (g : (psig RD).Gen) : (psig RD).right (gen g) = (psig RD).right g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · rfl
  · show (sig0 RD).colourSrc ((inv RD).dual c) = c.r
    rw [(inv RD).src_dual]; rfl

theorem gen_gen (g : (psig RD).Gen) : gen (gen g) = g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · show PivotalGen.cup ((inv RD).dual ((inv RD).dual c)) = _
    rw [inv_dual_dual]
  · show PivotalGen.cap ((inv RD).dual ((inv RD).dual c)) = _
    rw [inv_dual_dual]

theorem deg_gen (g : (psig RD).Gen) : deg RD (gen g) = deg RD g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · rfl
  · show -C.dot j i = -C.dot i j
    rw [C.symm]
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 + sgn (!s) * RD.pair (RD.iY i) (sh RD (s, i) + r)) =
      di C i * (1 - sgn s * RD.pair (RD.iY i) (sh RD (s, i) + r))
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false] <;> ring
  · obtain ⟨⟨s, i⟩, r⟩ := c
    show di C i * (1 - sgn (!s) * RD.pair (RD.iY i) (sh RD (!s, i) + (sh RD (s, i) + r))) =
      di C i * (1 + sgn s * RD.pair (RD.iY i) r)
    rw [← add_assoc, show ((!s, i) : Letter I) = Letter.dual (s, i) from rfl, sh_dual_add_sh,
      zero_add]
    cases s <;> simp only [Bool.not_false, Bool.not_true, sgn_true, sgn_false] <;> ring

/-- The reflection of a layer: the same strands, the reflected generator. -/
def rlay (L : Layer (psig RD)) : Layer (psig RD) := ⟨L.start, L.left, gen L.gen, L.right⟩

theorem rlay_valid {L : Layer (psig RD)} (hv : L.Valid) : (rlay L).Valid where
  left_ok := hv.left_ok
  left_end := (gen_left L.gen).symm ▸ hv.left_end
  dom_ok := by
    show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen))
    rw [gen_left, gen_dom]; exact hv.cod_ok
  dom_end := by
    show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).dom (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_dom, gen_right]; exact hv.cod_end
  cod_ok := by
    show (psig RD).ok ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen))
    rw [gen_left, gen_cod]; exact hv.dom_ok
  cod_end := by
    show (psig RD).endR ((psig RD).left (gen L.gen)) ((psig RD).cod (gen L.gen)) =
      (psig RD).right (gen L.gen)
    rw [gen_left, gen_cod, gen_right]; exact hv.dom_end
  right_ok := by
    show (psig RD).ok ((psig RD).right (gen L.gen)) L.right
    rw [gen_right]; exact hv.right_ok

theorem rlay_dom (L : Layer (psig RD)) : (rlay L).dom = L.cod :=
  Obj.ext rfl (by simp only [Layer.dom_word, Layer.cod_word, rlay, gen_dom])

theorem rlay_cod (L : Layer (psig RD)) : (rlay L).cod = L.dom :=
  Obj.ext rfl (by simp only [Layer.dom_word, Layer.cod_word, rlay, gen_cod])

theorem rlay_rlay (L : Layer (psig RD)) : rlay (rlay L) = L := by
  simp only [rlay, gen_gen]

theorem rlay_whisker (L : Layer (psig RD)) (u : Obj (psig RD)) (v : List (psig RD).Colour) :
    rlay (L.whisker u v) = (rlay L).whisker u v := rfl

/-- The reflected list of layers: reversed, each layer reflected. -/
def rrev (ls : List (Layer (psig RD))) : List (Layer (psig RD)) := (ls.map rlay).reverse

@[simp] theorem rrev_nil : rrev ([] : List (Layer (psig RD))) = [] := rfl

theorem rrev_append (ls ms : List (Layer (psig RD))) : rrev (ls ++ ms) = rrev ms ++ rrev ls := by
  simp [rrev]

theorem rrev_rrev (ls : List (Layer (psig RD))) : rrev (rrev ls) = ls := by
  simp [rrev, List.map_reverse, List.map_map, Function.comp_def, rlay_rlay]

theorem chain_rrev {a b : Obj (psig RD)} {ls : List (Layer (psig RD))} (h : Chain a ls b) :
    Chain b (rrev ls) a := by
  induction ls generalizing a with
  | nil => exact h.symm
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rw [show L :: ls = [L] ++ ls from rfl, rrev_append]
    exact (ih hc).append ⟨rlay_valid hv, rlay_dom L, rlay_cod L⟩

/-- The reflection of a diagram `d : a ⟶ b` across the `x`-axis (with inverted orientation), a
diagram `b ⟶ a`. -/
def reflD {a b : Obj (psig RD)} (d : a ⟶ b) : b ⟶ a :=
  Diagram.mk (rrev (Diagram.layers d)) (chain_rrev (Diagram.chain d))

@[simp] theorem layers_reflD {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.layers (reflD d) = rrev (Diagram.layers d) := rfl

theorem reflD_id (a : Obj (psig RD)) : reflD (𝟙 a) = 𝟙 a := rfl

theorem reflD_comp {a b c : Obj (psig RD)} (f : a ⟶ b) (g : b ⟶ c) :
    reflD (f ≫ g) = reflD g ≫ reflD f := by
  ext; simp [rrev_append]

theorem reflD_reflD {a b : Obj (psig RD)} (d : a ⟶ b) : reflD (reflD d) = d := by
  ext; simp [rrev_rrev]

theorem reflD_whisker {a b : Obj (psig RD)} (d : a ⟶ b) (u : Obj (psig RD))
    (v : List (psig RD).Colour) (hw : a.WhiskerOK u v) :
    reflD (Diagram.whisker d u v hw) =
      Diagram.whisker (reflD d) u v ((Diagram.chain d).whiskerOK hw) := by
  ext; simp [rrev, List.map_reverse, List.map_map, Function.comp_def, rlay_whisker]

theorem degree_reflD {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.degree (deg RD) (reflD d) = Diagram.degree (deg RD) d := by
  simp only [Diagram.degree, layers_reflD, rrev, List.map_reverse, List.sum_reverse, List.map_map,
    Function.comp_def, rlay, deg_gen]

/-- The reflection of linear combinations of diagrams. -/
def reflLin {a b : Obj (psig RD)} (f : LinDiagram k a b) : LinDiagram k b a :=
  Finsupp.mapDomain reflD f

end Psi

open Psi

/-! ## The reflection functor on the free 2-category -/

/-- The reflection on the free 2-category, with values in the opposite of `U`. -/
def psiFree : Obj (psig RD) ⥤ (pres RD k).Presentedᵒᵖ where
  obj a := op ((pres RD k).obj a)
  map d := ((pres RD k).diag (reflD d)).op
  map_id a := by rw [reflD_id, Presentation.diag_id]; rfl
  map_comp f g := by rw [reflD_comp, Presentation.diag_comp]; rfl

/-- `P.lin ∘ reflLin`: the reflection of a linear combination of diagrams, in `U`. -/
def psiL {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k).obj b ⟶ (pres RD k).obj a :=
  (pres RD k).lin (reflLin k f)

variable {RD k}

theorem psiL_of {a b : Obj (psig RD)} (d : a ⟶ b) :
    psiL RD k (LinDiagram.of d) = (pres RD k).diag (reflD d) := by
  rw [psiL, reflLin, Finsupp.mapDomain_single]; rfl

theorem psiL_single {a b : Obj (psig RD)} (d : a ⟶ b) (r : k) :
    psiL RD k (Finsupp.single d r) = r • (pres RD k).diag (reflD d) := by
  rw [psiL, reflLin, Finsupp.mapDomain_single, Presentation.lin_single]

theorem psiL_add {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    psiL RD k (f + g) = psiL RD k f + psiL RD k g := by
  rw [psiL, reflLin, Finsupp.mapDomain_add, Presentation.lin_add]; rfl

theorem psiL_smul {a b : Obj (psig RD)} (r : k) (f : LinDiagram k a b) :
    psiL RD k (r • f) = r • psiL RD k f := by
  rw [psiL, reflLin, Finsupp.mapDomain_smul, Presentation.lin_smul]; rfl

theorem psiL_zero {a b : Obj (psig RD)} : psiL RD k (0 : LinDiagram k a b) = 0 := by
  rw [psiL, reflLin, Finsupp.mapDomain_zero, Presentation.lin_zero]

/-- `psiL` as a `k`-linear map. -/
def psiLM (a b : Obj (psig RD)) :
    LinDiagram k a b →ₗ[k] ((pres RD k).obj b ⟶ (pres RD k).obj a) where
  toFun := psiL RD k
  map_add' := psiL_add
  map_smul' := psiL_smul

theorem psiL_neg {a b : Obj (psig RD)} (f : LinDiagram k a b) : psiL RD k (-f) = -psiL RD k f :=
  (psiLM a b).map_neg f

theorem psiL_sub {a b : Obj (psig RD)} (f g : LinDiagram k a b) :
    psiL RD k (f - g) = psiL RD k f - psiL RD k g :=
  (psiLM a b).map_sub f g

theorem psiL_sum {a b : Obj (psig RD)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    psiL RD k (∑ x ∈ s, f x) = ∑ x ∈ s, psiL RD k (f x) :=
  map_sum (psiLM a b) f s

theorem psiL_id (a : Obj (psig RD)) : psiL RD k (𝟙 (Free.of k a)) = 𝟙 _ := by
  rw [show (𝟙 (Free.of k a) : LinDiagram k a a) = LinDiagram.of (𝟙 a) from rfl, psiL_of,
    reflD_id, Presentation.diag_id]

theorem psiL_comp {a b c : Obj (psig RD)} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    psiL RD k (f ≫ g) = psiL RD k g ≫ psiL RD k f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, psiL_zero, psiL_zero, Limits.comp_zero]
  | add f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, psiL_add, psiL_add, h₁, h₂, Preadditive.comp_add]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, psiL_zero, psiL_zero, Limits.zero_comp]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, psiL_add, psiL_add, h₁, h₂, Preadditive.add_comp]
    | single e s =>
      erw [Free.single_comp_single]
      rw [psiL_single, psiL_single, psiL_single, reflD_comp, Presentation.diag_comp,
        Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

theorem freeLift_psiFree {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (freeLift k (psiFree RD k)).map f = (psiL RD k f).op := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero, psiL_zero]; rfl
  | add f₁ f₂ h₁ h₂ => rw [Functor.map_add, h₁, h₂, psiL_add, op_add]
  | single d r =>
    rw [freeLift_map_single, psiL_single]
    rfl

theorem psiL_whisker {a b : Obj (psig RD)} (f : LinDiagram k a b) (u : Obj (psig RD))
    (v : List (psig RD).Colour) (hw : a.WhiskerOK u v) :
    psiL RD k (LinDiagram.whisker f u v hw) = (pres RD k).whisk (psiL RD k f) u v := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [psiL_zero, show LinDiagram.whisker (0 : LinDiagram k a b) u v hw = 0 from
      Finsupp.mapDomain_zero, psiL_zero, Presentation.whisk_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [LinDiagram.whisker_add, psiL_add, psiL_add, h₁, h₂, Presentation.whisk_add]
  | single d r =>
    rw [LinDiagram.whisker_single, psiL_single, psiL_single, Presentation.whisk_smul,
      Presentation.whisk_diag _ _ _ _ ((Diagram.chain d).whiskerOK hw), reflD_whisker]


/-! ## Normal forms -/

namespace Psi

/-- The reflection of the shape of a generator. -/
def shape : Shape I → Shape I
  | .dot l => .dot l
  | .cross ε i j => .cross ε j i
  | .cup l => .cap l.dual
  | .cap l => .cup l.dual

@[simp] theorem shape_dot (l : Letter I) : shape (.dot l) = .dot l := rfl
@[simp] theorem shape_cross (ε : Bool) (i j : I) : shape (.cross ε i j) = .cross ε j i := rfl
@[simp] theorem shape_cup (l : Letter I) : shape (.cup l) = .cap l.dual := rfl
@[simp] theorem shape_cap (l : Letter I) : shape (.cap l) = .cup l.dual := rfl

theorem shape_shape (g : Shape I) : shape (shape g) = g := by
  cases g <;> simp

theorem shape_dom (g : Shape I) : (shape g).dom = g.cod := by
  cases g <;> simp

theorem shape_cod (g : Shape I) : (shape g).cod = g.dom := by
  cases g <;> simp

/-- The reflection of a layer datum. -/
def ld (x : LayerData I) : LayerData I := (x.1, shape x.2.1, x.2.2)

/-- The reflection of a normal-form list of layers: reversed, each layer reflected. -/
def rls (ls : List (LayerData I)) : List (LayerData I) := (ls.map ld).reverse

@[simp] theorem rls_nil : rls ([] : List (LayerData I)) = [] := rfl

theorem rls_cons (x : LayerData I) (ls : List (LayerData I)) : rls (x :: ls) = rls ls ++ [ld x] := by
  simp [rls]

theorem rls_append (ls ms : List (LayerData I)) : rls (ls ++ ms) = rls ms ++ rls ls := by
  simp [rls]

theorem rls_rls (ls : List (LayerData I)) : rls (rls ls) = ls := by
  simp [rls, List.map_reverse, List.map_map, Function.comp_def, ld, shape_shape]

theorem rls_replicate (n : ℕ) (x : LayerData I) : rls (List.replicate n x) = List.replicate n (ld x) := by
  simp [rls, List.map_replicate, List.reverse_replicate]

theorem rls_singleton (x : LayerData I) : rls [x] = [ld x] := rfl

theorem sChain_rls {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    SChain t (rls ls) s := by
  induction ls generalizing s with
  | nil => exact (show s = t from h).symm
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [rls_cons]
    exact (ih h).append ⟨by simp [ld, shape_dom], by simp [ld, shape_cod]⟩

theorem rlay_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    rlay (lay RD μ u g v) = lay RD μ u (shape g) v := by
  refine Layer.ext ?_ ?_ ?_ rfl
  · show wt RD μ (u ++ g.dom ++ v) = wt RD μ (u ++ (shape g).dom ++ v)
    rw [shape_dom]; exact wt_lay_dom RD μ u g v
  · show wd RD (wt RD μ (g.dom ++ v)) u = wd RD (wt RD μ ((shape g).dom ++ v)) u
    rw [shape_dom, wt_append, wt_append, Shape.wt_dom_eq_wt_cod]
  · show gen (g.gen RD (wt RD μ v)) = (shape g).gen RD (wt RD μ v)
    cases g with
    | dot l => rfl
    | cross ε i j => rfl
    | cup l =>
      show PivotalGen.cap ((inv RD).dual ⟨l, sh RD l.dual + wt RD μ v⟩) = .cap ⟨l.dual, wt RD μ v⟩
      rw [inv_dual]; simp
    | cap l =>
      show PivotalGen.cup ((inv RD).dual ⟨l, wt RD μ v⟩) =
        .cup ⟨l.dual, sh RD l.dual.dual + wt RD μ v⟩
      rw [inv_dual, Letter.dual_dual]

theorem layers_reflD_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) :
    Diagram.layers (reflD (mkD RD μ ls h)) = layList RD μ (rls ls) := by
  simp only [layers_reflD, layers_mkD, rrev, layList, rls, List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact rlay_lay μ x.1 x.2.1 x.2.2

theorem reflD_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    reflD (mkD RD μ ls h) = mkD RD μ (rls ls) (sChain_rls h) :=
  Diagram.ext (layers_reflD_mkD μ ls h)

end Psi

open Psi

theorem mkD_congr (μ : X) {s t : List (Letter I)} {ls ls' : List (LayerData I)} (e : ls = ls')
    (h : SChain s ls t) (h' : SChain s ls' t) : mkD RD μ ls h = mkD RD μ ls' h' := by
  subst e; rfl

theorem psiL_of_mkD (μ : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t) :
    psiL RD k (LinDiagram.of (mkD RD μ ls h)) = dg RD k μ t s (rls ls) := by
  rw [psiL_of, reflD_mkD, dg_of]


/-! ## Reflections of the diagrams of Definition 3.1 -/

section Diagrams

variable (i j : I)

theorem reflD_downDot (μ : X) : reflD (downDot RD i μ) = downDot RD i μ := by
  rw [downDot, reflD_mkD]; rfl

theorem reflD_rotDotR (μ : X) : reflD (rotDotR RD i μ) = rotDotL RD i μ := by
  rw [rotDotR, reflD_mkD]; rfl

theorem reflD_rotDotL (μ : X) : reflD (rotDotL RD i μ) = rotDotR RD i μ := by
  rw [rotDotL, reflD_mkD]; rfl

theorem reflD_downCross (μ : X) : reflD (downCross RD j i μ) = downCross RD i j μ := by
  rw [downCross, reflD_mkD]; rfl

theorem reflD_rotCrossR (μ : X) : reflD (rotCrossR RD j i μ) = rotCrossL RD i j μ := by
  rw [rotCrossR, reflD_mkD]; rfl

theorem reflD_rotCrossL (μ : X) : reflD (rotCrossL RD j i μ) = rotCrossR RD i j μ := by
  rw [rotCrossL, reflD_mkD]; rfl

theorem reflD_crossl (μ : X) : reflD (crossl RD i j μ) = crossr RD i j μ := by
  rw [crossl, reflD_mkD]; rfl

theorem reflD_crossr (μ : X) : reflD (crossr RD i j μ) = crossl RD i j μ := by
  rw [crossr, reflD_mkD]; rfl

theorem reflD_curlR (lam : X) : reflD (curlR RD i lam) = curlR RD i lam := by
  rw [curlR, reflD_mkD]; rfl

theorem reflD_curlL (μ : X) : reflD (curlL RD i μ) = curlL RD i μ := by
  rw [curlL, reflD_mkD]; rfl

theorem reflD_cwReal (lam : X) (m : ℕ) : reflD (cwReal RD lam i m) = cwReal RD lam i m := by
  rw [cwReal, reflD_mkD]
  exact mkD_congr lam (by rw [rls_append, rls_append, rls_replicate]; rfl) _ _

theorem reflD_ccwReal (lam : X) (m : ℕ) : reflD (ccwReal RD lam i m) = ccwReal RD lam i m := by
  rw [ccwReal, reflD_mkD]
  exact mkD_congr lam (by rw [rls_append, rls_append, rls_replicate]; rfl) _ _

theorem reflD_dots (μ : X) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) (n : ℕ) :
    reflD (dots RD μ u l v n) = dots RD μ u l v n := by
  rw [dots, reflD_mkD]
  exact mkD_congr μ (by simp [rls_replicate, ld]) _ _

end Diagrams

/-! ## Bubbles -/

section Bubbles

theorem reflLin_bubR (lam : X) (t : List (Letter I)) (b : LEnd RD k (ob RD lam [])) :
    reflLin k (bubR RD k lam t b) = bubR RD k lam t (reflLin k b) := by
  simp only [bubR, reflLin, LinDiagram.cast, LinDiagram.whisker, ← Finsupp.mapDomain_comp]
  congr 1
  funext d
  apply Diagram.ext
  simp [rrev, List.map_reverse, List.map_map, Function.comp_def, rlay_whisker]

theorem reflLin_bubL (μ : X) (t : List (Letter I)) (b : LEnd RD k (ob RD (wt RD μ t) [])) :
    reflLin k (bubL RD k μ t b) = bubL RD k μ t (reflLin k b) := by
  simp only [bubL, reflLin, LinDiagram.cast, LinDiagram.whisker, ← Finsupp.mapDomain_comp]
  congr 1
  funext d
  apply Diagram.ext
  simp [rrev, List.map_reverse, List.map_map, Function.comp_def, rlay_whisker]

theorem psiL_bubR (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    psiL RD k (bubR RD k lam [l] b) = bubRU RD k lam l (psiL RD k b) := by
  rw [psiL, reflLin_bubR, lin_bubR]; rfl

theorem psiL_bubL (μ : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD μ [l]) [])) :
    psiL RD k (bubL RD k μ [l] b) = bubLU RD k μ l (psiL RD k b) := by
  rw [psiL, reflLin_bubL, lin_bubL]; rfl

/-- A ring homomorphism commutes with the infinite Grassmannian recursion. -/
theorem map_grassInv {A B : Type*} [Ring A] [Ring B] (φ : A →+* B) (c : ℕ → A) (n : ℕ) :
    φ (grassInv c n) = grassInv (fun a => φ (c a)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [grassInv_zero, grassInv_zero, map_one]
    | succ n =>
      rw [grassInv_succ, grassInv_succ, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ih _ (by omega)]

variable (RD k) in
/-- The reflection on `END(1_λ)`: an antihomomorphism to a commutative ring, hence a ring
homomorphism. -/
def psiEnd (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k).obj (ob RD lam [])) where
  toFun := psiL RD k
  map_one' := psiL_id _
  map_mul' f g := by
    show psiL RD k (g ≫ f) = psiL RD k g ≫ psiL RD k f
    rw [psiL_comp]; exact endEmpty_comm RD k lam _ _
  map_zero' := psiL_zero
  map_add' := psiL_add

variable (RD k) in
/-- The class map on `END(1_λ)`, as a ring homomorphism. -/
def linEnd (lam : X) : LEnd RD k (ob RD lam []) →+* End ((pres RD k).obj (ob RD lam [])) :=
  (KLR.Diagram.linAlg (pres RD k) (ob RD lam [])).toRingHom

theorem psiL_ccwR (lam : X) (i : I) (m : ℤ) :
    psiL RD k (ccwR RD k lam i m) = (pres RD k).lin (ccwR RD k lam i m) := by
  unfold ccwR
  split_ifs
  · rw [psiL_of, reflD_ccwReal]; rfl
  · rw [psiL_zero, Presentation.lin_zero]

theorem psiL_cwR (lam : X) (i : I) (m : ℤ) :
    psiL RD k (cwR RD k lam i m) = (pres RD k).lin (cwR RD k lam i m) := by
  unfold cwR
  split_ifs
  · rw [psiL_of, reflD_cwReal]; rfl
  · rw [psiL_zero, Presentation.lin_zero]

/-- **`ψ̃` fixes all clockwise bubbles** (real and fake). -/
theorem psiL_cwL (lam : X) (i : I) (m : ℤ) :
    psiL RD k (cwL RD k lam i m) = cwU RD k lam i m := by
  unfold cwU cwL
  split_ifs
  · rw [psiL_of, reflD_cwReal]; rfl
  · show psiEnd RD k lam _ = linEnd RD k lam _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    exact psiL_ccwR lam i _
  · rw [psiL_zero, Presentation.lin_zero]

/-- **`ψ̃` fixes all counterclockwise bubbles** (real and fake). -/
theorem psiL_ccwL (lam : X) (i : I) (m : ℤ) :
    psiL RD k (ccwL RD k lam i m) = ccwU RD k lam i m := by
  unfold ccwU ccwL
  split_ifs
  · rw [psiL_of, reflD_ccwReal]; rfl
  · show psiEnd RD k lam _ = linEnd RD k lam _
    rw [map_grassInv, map_grassInv]
    congr 1
    funext a
    exact psiL_cwR lam i _
  · rw [psiL_zero, Presentation.lin_zero]

end Bubbles


/-! ## Polynomials in commuting elements under antihomomorphisms -/

section NcEval

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

theorem ncEval_antimul' (φ : A →ₗ[k] B) (h1 : φ 1 = 1) (hmul : ∀ a b, φ (a * b) = φ b * φ a)
    {n : ℕ} (y : Fin n → A) (hc : ∀ a b, Commute (φ (y a)) (φ (y b)))
    (p : MvPolynomial (Fin n) k) : φ (KLR.ncEval y p) = KLR.ncEval (fun a => φ (y a)) p := by
  have hpow : ∀ (a : Fin n) (t : ℕ), φ (y a ^ t) = φ (y a) ^ t := by
    intro a t
    induction t with
    | zero => simp [h1]
    | succ t ih => rw [pow_succ, hmul, ih, pow_succ']
  have hlist : ∀ (l : List (Fin n)) (s : Fin n →₀ ℕ),
      φ (l.map fun a => y a ^ s a).prod = (l.map fun a => φ (y a) ^ s a).prod := by
    intro l s
    induction l with
    | nil => simp [h1]
    | cons a l ih =>
      have hcomm : Commute (φ (y a) ^ s a) (l.map fun a => φ (y a) ^ s a).prod :=
        Commute.list_prod_right _ _ fun w hw => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
          exact ((hc a b).pow_left _).pow_right _
      rw [List.map_cons, List.prod_cons, hmul, ih, hpow, List.map_cons, List.prod_cons, hcomm.eq]
  simp only [KLR.ncEval, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Algebra.smul_def, map_smul, List.ofFn_eq_map, hlist, ← List.ofFn_eq_map, Algebra.smul_def]

end NcEval

/-! ## The reflection of KLR diagrams -/

namespace KPsi

/-- The reflection of a KLR generator across the `x`-axis. -/
def kgen : KLR.Diagram.Gen I → KLR.Diagram.Gen I
  | .dot c => .dot c
  | .cross c d => .cross d c

/-- The reflection of a KLR layer. -/
def klay (L : Layer (KLR.Diagram.sig I)) : Layer (KLR.Diagram.sig I) :=
  ⟨L.start, L.left, kgen L.gen, L.right⟩

theorem klay_dom (L : Layer (KLR.Diagram.sig I)) : (klay L).dom = L.cod := by
  obtain ⟨_, l, g, r⟩ := L; cases g <;> rfl

theorem klay_cod (L : Layer (KLR.Diagram.sig I)) : (klay L).cod = L.dom := by
  obtain ⟨_, l, g, r⟩ := L; cases g <;> rfl

/-- The reflection of a list of KLR layers. -/
def krev (ls : List (Layer (KLR.Diagram.sig I))) : List (Layer (KLR.Diagram.sig I)) :=
  (ls.map klay).reverse

theorem krev_append (ls ms : List (Layer (KLR.Diagram.sig I))) :
    krev (ls ++ ms) = krev ms ++ krev ls := by
  simp [krev]

theorem chain_krev {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : Chain b (krev ls) a := by
  induction ls generalizing a with
  | nil => exact h.symm
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    rw [show L :: ls = [L] ++ ls from rfl, krev_append]
    exact (ih hc).append ⟨Layer.valid_of_subsingleton _, klay_dom L, klay_cod L⟩

/-- The reflection of a KLR diagram `d : a ⟶ b`, a diagram `b ⟶ a`. -/
def kreflD {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) : b ⟶ a :=
  Diagram.mk (krev (Diagram.layers d)) (chain_krev (Diagram.chain d))

theorem kreflD_comp {a b c : Obj (KLR.Diagram.sig I)} (f : a ⟶ b) (g : b ⟶ c) :
    kreflD (f ≫ g) = kreflD g ≫ kreflD f := by
  apply Diagram.ext; simp [kreflD, krev_append]

theorem kreflD_id (a : Obj (KLR.Diagram.sig I)) : kreflD (𝟙 a) = 𝟙 a := rfl

variable (k) in
/-- The reflection of linear combinations of KLR diagrams. -/
def kreflLin {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) : LinDiagram k b a :=
  Finsupp.mapDomain kreflD f

theorem kreflLin_of {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    kreflLin k (LinDiagram.of d) = LinDiagram.of (kreflD d) := Finsupp.mapDomain_single

theorem kreflLin_sub {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    kreflLin k (f - g) = kreflLin k f - kreflLin k g :=
  (Finsupp.lmapDomain k k (kreflD (a := a) (b := b))).map_sub f g

theorem kreflLin_zero {a b : Obj (KLR.Diagram.sig I)} :
    kreflLin k (0 : LinDiagram k a b) = 0 := Finsupp.mapDomain_zero

theorem kreflLin_add {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    kreflLin k (f + g) = kreflLin k f + kreflLin k g := Finsupp.mapDomain_add

theorem kreflLin_single {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) (r : k) :
    kreflLin k (Finsupp.single d r : LinDiagram k a b) = Finsupp.single (kreflD d) r :=
  Finsupp.mapDomain_single

theorem kreflLin_comp {a b c : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (g : LinDiagram k b c) : kreflLin k (f ≫ g) = kreflLin k g ≫ kreflLin k f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, kreflLin_zero, kreflLin_zero, Limits.comp_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Preadditive.add_comp, kreflLin_add, kreflLin_add, h₁, h₂, Preadditive.comp_add]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, kreflLin_zero, kreflLin_zero, Limits.zero_comp]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, kreflLin_add, kreflLin_add, h₁, h₂, Preadditive.add_comp]
    | single e s =>
      erw [Free.single_comp_single]
      rw [kreflLin_single, kreflLin_single, kreflLin_single, kreflD_comp]
      erw [Free.single_comp_single]
      rw [mul_comm]

section Rel

variable (Q : I → I → MvPolynomial (Fin 2) k)

local notation "P" => KLR.Diagram.pres k Q

open KLR.Diagram in
/-- The reflection kills polynomials in pairwise commuting dots, up to the relations. -/
theorem lin_kreflLin_lpoly {w : Obj (KLR.Diagram.sig I)} {n : ℕ} (y : Fin n → (w ⟶ w))
    (hy : ∀ a, kreflD (y a) = y a)
    (hc : ∀ a b, @Commute (End ((P).obj w)) _ ((P).diag (y a)) ((P).diag (y b)))
    (p : MvPolynomial (Fin n) k) :
    (P).lin (kreflLin k (lpoly k y p)) = (P).lin (lpoly k y p) := by
  let φ : End (Free.of k w) →ₗ[k] End ((P).obj w) :=
    ((P).linMap w w).comp (Finsupp.lmapDomain k k (kreflD (a := w) (b := w)))
  have hφ : ∀ f, φ f = (P).lin (kreflLin k f) := fun _ => rfl
  have h1 : φ 1 = 1 := by
    rw [hφ]
    show (P).lin (kreflLin k (LinDiagram.of (𝟙 w))) = 𝟙 _
    rw [kreflLin_of, kreflD_id]; exact (P).lin_id w
  have hmul : ∀ f g, φ (f * g) = φ g * φ f := by
    intro f g
    rw [hφ, hφ, hφ, End.mul_def, End.mul_def, kreflLin_comp, Presentation.lin_comp]
  have hyφ : ∀ a, φ (LinDiagram.of (y a)) = (P).diag (y a) := by
    intro a; rw [hφ, kreflLin_of, hy]; rfl
  have := ncEval_antimul' φ h1 hmul (fun a => LinDiagram.of (y a))
    (fun a b => by rw [hyφ, hyφ]; exact hc a b) p
  rw [← hφ]
  refine this.trans ?_
  simp only [hyφ]
  rw [← KLR.Diagram.linAlg_apply (P), AlgHom.map_ncEval]
  simp only [KLR.Diagram.linAlg_apply, Presentation.lin_of]

open KLR.Diagram in
theorem commute_diag_dots2 (c d : I) (a b : Fin 2) :
    @Commute (End ((P).obj (KLR.Diagram.ob [c, d]))) _
      ((P).diag ((![D0 c d, D1 c d] : Fin 2 → _) a))
      ((P).diag ((![D0 c d, D1 c d] : Fin 2 → _) b)) := by
  have h : (P).diag (D1 c d ≫ D0 c d) = (P).diag (D0 c d ≫ D1 c d) :=
    (interchange_at Q [] [] [] (.dot c) (.dot d) (D0 c d ≫ D1 c d) (D1 c d ≫ D0 c d)
      rfl rfl).symm
  rw [Presentation.diag_comp, Presentation.diag_comp] at h
  fin_cases a <;> fin_cases b
  · exact Commute.refl _
  · exact h
  · exact h.symm
  · exact Commute.refl _

open KLR.Diagram in
theorem commute_diag_dots3 (c d : I) (a b : Fin 3) :
    @Commute (End ((P).obj (KLR.Diagram.ob [c, d, c]))) _
      ((P).diag ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) a))
      ((P).diag ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) b)) := by
  have h01 : (P).diag (E1 c d c ≫ E0 c d c) = (P).diag (E0 c d c ≫ E1 c d c) :=
    (interchange_at Q [] [] [c] (.dot c) (.dot d) (E0 c d c ≫ E1 c d c) (E1 c d c ≫ E0 c d c)
      rfl rfl).symm
  have h02 : (P).diag (E2 c d c ≫ E0 c d c) = (P).diag (E0 c d c ≫ E2 c d c) :=
    (interchange_at Q [] [d] [] (.dot c) (.dot c) (E0 c d c ≫ E2 c d c) (E2 c d c ≫ E0 c d c)
      rfl rfl).symm
  have h12 : (P).diag (E2 c d c ≫ E1 c d c) = (P).diag (E1 c d c ≫ E2 c d c) :=
    (interchange_at Q [c] [] [] (.dot d) (.dot c) (E1 c d c ≫ E2 c d c) (E2 c d c ≫ E1 c d c)
      rfl rfl).symm
  rw [Presentation.diag_comp, Presentation.diag_comp] at h01 h02 h12
  fin_cases a <;> fin_cases b
  all_goals first
    | exact Commute.refl _
    | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h12 | exact h12.symm

open KLR.Diagram in
/-- **The KLR relations are symmetric under the reflection across the `x`-axis** (KL I, end of
§2.1): every reflected relation holds. -/
theorem lin_kreflLin_relation (r : KLR.Diagram.Rel I) :
    (P).lin (kreflLin k (KLR.Diagram.relation k Q r)) = 0 := by
  cases r with
  | sqEq c =>
    have e : kreflLin k (KLR.Diagram.relation k Q (.sqEq c)) = KLR.Diagram.relation k Q (.sqEq c) := by
      rw [KLR.Diagram.relation, kreflLin_of, kreflD_comp]; rfl
    rw [e]; exact (P).lin_rel_self (.sqEq c)
  | sqNe c d h =>
    have H : (P).lin (LinDiagram.of (X2 c d ≫ X2 d c) - lpoly k ![D0 c d, D1 c d] (Q c d)) = 0 :=
      (P).lin_rel_self (.sqNe c d h)
    rw [Presentation.lin_sub] at H
    show (P).lin (kreflLin k (LinDiagram.of (X2 c d ≫ X2 d c) -
      lpoly k ![D0 c d, D1 c d] (Q c d))) = 0
    rw [kreflLin_sub, Presentation.lin_sub, lin_kreflLin_lpoly Q _ (fun a => by fin_cases a <;> rfl)
      (commute_diag_dots2 Q c d), kreflLin_of, kreflD_comp]
    exact H
  | slideLEq c =>
    have e : kreflLin k (KLR.Diagram.relation k Q (.slideLEq c)) = KLR.Diagram.relation k Q (.slideREq c) := by
      simp only [KLR.Diagram.relation, kreflLin_sub, kreflLin_of, kreflD_comp]; rfl
    rw [e]; exact (P).lin_rel_self (.slideREq c)
  | slideLNe c d h =>
    have e : kreflLin k (KLR.Diagram.relation k Q (.slideLNe c d h)) =
        KLR.Diagram.relation k Q (.slideRNe d c (Ne.symm h)) := by
      simp only [KLR.Diagram.relation, kreflLin_sub, kreflLin_of, kreflD_comp]; rfl
    rw [e]; exact (P).lin_rel_self (.slideRNe d c (Ne.symm h))
  | slideREq c =>
    have e : kreflLin k (KLR.Diagram.relation k Q (.slideREq c)) = KLR.Diagram.relation k Q (.slideLEq c) := by
      simp only [KLR.Diagram.relation, kreflLin_sub, kreflLin_of, kreflD_comp]; rfl
    rw [e]; exact (P).lin_rel_self (.slideLEq c)
  | slideRNe c d h =>
    have e : kreflLin k (KLR.Diagram.relation k Q (.slideRNe c d h)) =
        KLR.Diagram.relation k Q (.slideLNe d c (Ne.symm h)) := by
      simp only [KLR.Diagram.relation, kreflLin_sub, kreflLin_of, kreflD_comp]; rfl
    rw [e]; exact (P).lin_rel_self (.slideLNe d c (Ne.symm h))
  | braid c d e h =>
    have h' : ¬ (e = c ∧ e ≠ d) := fun ⟨h₁, h₂⟩ => h ⟨h₁.symm, h₁ ▸ h₂⟩
    have e' : kreflLin k (KLR.Diagram.relation k Q (.braid c d e h)) = KLR.Diagram.relation k Q (.braid e d c h') := by
      simp only [KLR.Diagram.relation, kreflLin_sub, kreflLin_of, kreflD_comp]; rfl
    rw [e']; exact (P).lin_rel_self (.braid e d c h')
  | braidQ c d h =>
    have H : (P).lin (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
        lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (Q c d))) = 0 :=
      (P).lin_rel_self (.braidQ c d h)
    rw [Presentation.lin_sub, Presentation.lin_sub] at H
    show (P).lin (kreflLin k (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
      lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (Q c d)))) = 0
    rw [kreflLin_sub, kreflLin_sub, Presentation.lin_sub, Presentation.lin_sub,
      lin_kreflLin_lpoly Q _ (fun a => by fin_cases a <;> rfl) (commute_diag_dots3 Q c d),
      kreflLin_of, kreflLin_of, kreflD_comp, kreflD_comp, kreflD_comp, kreflD_comp]
    exact H

end Rel

end KPsi


/-! ## The upward KLR relations -/

section Upward

theorem shape_upShape (g : KLR.Diagram.Gen I) : shape (upShape g) = upShape (KPsi.kgen g) := by
  cases g <;> rfl

theorem rlay_upLay (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    rlay (upLay RD μ L) = upLay RD μ (KPsi.klay L) := by
  rw [upLay, rlay_lay, shape_upShape]; rfl

theorem reflD_upDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    reflD (upDiag RD μ d) = upDiag RD μ (KPsi.kreflD d) := by
  apply Diagram.ext
  simp only [layers_reflD, layers_upDiag, rrev, KPsi.kreflD, Diagram.layers_mk, KPsi.krev,
    List.map_reverse, List.map_map, Function.comp_def, rlay_upLay]

theorem psiL_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    psiL RD k (upLin RD k μ f) =
      (upFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).lin (KPsi.kreflLin k f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [upLin, Finsupp.mapDomain_zero, psiL_zero, KPsi.kreflLin_zero, Presentation.lin_zero,
      Functor.map_zero]
  | add f g hf hg =>
    rw [upLin, Finsupp.mapDomain_add, ← upLin, ← upLin, psiL_add, hf, hg, KPsi.kreflLin_add,
      Presentation.lin_add, Functor.map_add]
  | single d r =>
    rw [upLin, Finsupp.mapDomain_single, psiL_single, reflD_upDiag, KPsi.kreflLin_single,
      Presentation.lin_single, Functor.map_smul, upFunctor_diag]

end Upward

/-! ## Reindexing the decomposition sums -/

theorem sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1), G f g =
      ∑ g ∈ Finset.range N, ∑ a ∈ Finset.range (N - g), G (g + a) g := by
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun g => Finset.Ico g N)]
  · refine Finset.sum_congr rfl fun g _ => ?_
    exact Finset.sum_Ico_eq_sum_range _ _ _
  · intro f g
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- The double sum of the decomposition of `1_{EF1_λ}` is symmetric under exchanging the numbers
of dots on the cap and on the cup. -/
theorem sum_triangle_swap {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1), F (N - 1 - f) g (f - g) =
      ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1), F (f - g) g (N - 1 - f) := by
  rw [sum_triangle N (fun f g => F (N - 1 - f) g (f - g)),
    sum_triangle N (fun f g => F (f - g) g (N - 1 - f))]
  refine Finset.sum_congr rfl fun g hg => ?_
  simp only [Finset.mem_range] at hg
  rw [← Finset.sum_range_reflect (fun a => F (g + a - g) g (N - 1 - (g + a))) (N - g)]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_range] at ha
  have e₁ : N - 1 - (g + a) = g + (N - g - 1 - a) - g := by omega
  have e₂ : g + a - g = N - 1 - (g + (N - g - 1 - a)) := by omega
  rw [e₁, e₂]

/-! ## The reflected relations hold -/

section Relations

variable (i : I) (lam : X)

theorem psiL_of_cupDotEF (m : ℕ) :
    psiL RD k (LinDiagram.of (cupDotEF RD lam i m)) =
      dg RD k lam [up i, dn i] [] (dotCapEFLs i m) := by
  rw [cupDotEF, psiL_of_mkD, rls_append, rls_replicate]
  exact dg_dots_cap_dn RD k lam i m

theorem psiL_of_dotCapEF (m : ℕ) :
    psiL RD k (LinDiagram.of (dotCapEF RD lam i m)) =
      dg RD k lam [] [up i, dn i] (cupDotEFLs i m) := by
  rw [dotCapEF, psiL_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cupUp RD k i lam m).symm

theorem psiL_of_cupDotFE (m : ℕ) :
    psiL RD k (LinDiagram.of (cupDotFE RD lam i m)) =
      dg RD k lam [dn i, up i] [] (dotCapFELs i m) := by
  rw [cupDotFE, psiL_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cap_up RD k lam i m).symm

theorem psiL_of_dotCapFE (m : ℕ) :
    psiL RD k (LinDiagram.of (dotCapFE RD lam i m)) =
      dg RD k lam [] [dn i, up i] (cupDotFELs i m) := by
  rw [dotCapFE, psiL_of_mkD, rls_append, rls_replicate]
  exact (dg_dots_cupDn RD k i lam m).symm

theorem psiL_decompEFSum :
    psiL RD k (decompEFSum RD k i lam) = (pres RD k).lin (decompEFSum RD k i lam) := by
  unfold decompEFSum
  rw [psiL_sum, lin_finsum RD k]
  simp only [psiL_sum, lin_finsum RD k, psiL_comp, Presentation.lin_comp,
    psiL_of_cupDotEF, psiL_of_dotCapEF, psiL_ccwL, Category.assoc]
  simp only [dotCapEF, cupDotEF, lin_of_mkD RD k]
  exact sum_triangle_swap (ip RD i lam).toNat (fun a g b =>
    dg RD k lam [up i, dn i] [] (dotCapEFLs i a) ≫ ccwU RD k lam i (-ip RD i lam - 1 + g) ≫
      dg RD k lam [] [up i, dn i] (cupDotEFLs i b))

theorem psiL_decompFESum :
    psiL RD k (decompFESum RD k i lam) = (pres RD k).lin (decompFESum RD k i lam) := by
  unfold decompFESum
  rw [psiL_sum, lin_finsum RD k]
  simp only [psiL_sum, lin_finsum RD k, psiL_comp, Presentation.lin_comp,
    psiL_of_cupDotFE, psiL_of_dotCapFE, psiL_cwL, Category.assoc]
  simp only [dotCapFE, cupDotFE, lin_of_mkD RD k]
  exact sum_triangle_swap (-ip RD i lam).toNat (fun a g b =>
    dg RD k lam [dn i, up i] [] (dotCapFELs i a) ≫ cwU RD k lam i (ip RD i lam - 1 + g) ≫
      dg RD k lam [] [dn i, up i] (cupDotFELs i b))

theorem psiL_curlRHS :
    psiL RD k (curlRHS RD k i lam) = (pres RD k).lin (curlRHS RD k i lam) := by
  unfold curlRHS
  rw [psiL_neg, psiL_sum, Presentation.lin_neg, lin_finsum RD k]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [psiL_comp, psiL_of, reflD_dots, psiL_bubR, psiL_cwL, Presentation.lin_comp, lin_bubR,
    Presentation.lin_of]
  exact (bubRU_comm RD k lam (up i) _ _).symm

theorem psiL_curlLHS (μ : X) :
    psiL RD k (curlLHS RD k i μ) = (pres RD k).lin (curlLHS RD k i μ) := by
  unfold curlLHS
  rw [psiL_sum, lin_finsum RD k]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [psiL_comp, psiL_of, reflD_dots, psiL_bubL, psiL_ccwL, Presentation.lin_comp, lin_bubL,
    Presentation.lin_of]
  exact (bubLU_comm RD k μ (up i) _ _).symm

end Relations

/-- **Every relation of Definition 3.1, reflected across the `x`-axis (with orientations
inverted), holds in `U`.** -/
theorem psiL_relation (r : Rel RD) : psiL RD k (relation k r) = 0 := by
  cases r with
  | cycDotR i μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_rotDotR, reflD_downDot, sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl
  | cycDotL i μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_rotDotL, reflD_downDot, sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl
  | cwNeg i lam α h =>
    rw [relation, psiL_of, reflD_cwReal]
    exact (pres RD k).lin_rel_self (.inr (.cwNeg i lam α h))
  | ccwNeg i lam α h =>
    rw [relation, psiL_of, reflD_ccwReal]
    exact (pres RD k).lin_rel_self (.inr (.ccwNeg i lam α h))
  | cwOne i lam h =>
    have H : (pres RD k).lin (relation (RD := RD) k (.cwOne i lam h)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.cwOne i lam h))
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_cwReal]
    exact H
  | ccwOne i lam h =>
    have H : (pres RD k).lin (relation (RD := RD) k (.ccwOne i lam h)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.ccwOne i lam h))
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_ccwReal]
    exact H
  | curlR i lam =>
    have H : (pres RD k).lin (relation (RD := RD) k (.curlR i lam)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.curlR i lam))
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiL_sub, psiL_of, reflD_curlR, psiL_curlRHS]
    exact H
  | curlL i μ =>
    have H : (pres RD k).lin (relation (RD := RD) k (.curlL i μ)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.curlL i μ))
    rw [relation, Presentation.lin_sub] at H
    rw [relation, psiL_sub, psiL_of, reflD_curlL, psiL_curlLHS]
    exact H
  | decompEF i lam =>
    have H : (pres RD k).lin (relation (RD := RD) k (.decompEF i lam)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.decompEF i lam))
    rw [relation, Presentation.lin_sub, Presentation.lin_add] at H
    rw [relation, psiL_sub, psiL_add, psiL_of, psiL_of, reflD_comp, reflD_crossl,
      reflD_crossr, psiL_decompEFSum]
    exact H
  | decompFE i lam =>
    have H : (pres RD k).lin (relation (RD := RD) k (.decompFE i lam)) = 0 :=
      (pres RD k).lin_rel_self (.inr (.decompFE i lam))
    rw [relation, Presentation.lin_sub, Presentation.lin_add] at H
    rw [relation, psiL_sub, psiL_add, psiL_of, psiL_of, reflD_comp, reflD_crossl,
      reflD_crossr, psiL_decompFESum]
    exact H
  | cycCrossR j i μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_rotCrossR, reflD_downCross, sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.cycCrossL i j μ)) rfl
  | cycCrossL j i μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_rotCrossL, reflD_downCross, sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.cycCrossR i j μ)) rfl
  | downupEF i j h μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_comp, reflD_crossl, reflD_crossr,
      sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.downupEF i j h μ)) rfl
  | downupFE i j h μ =>
    rw [relation, psiL_sub, psiL_of, psiL_of, reflD_comp, reflD_crossl, reflD_crossr,
      sub_eq_zero]
    exact (pres RD k).diag_eq_of_rel (.inr (.downupFE i j h μ)) rfl
  | klr μ r =>
    rw [relation, psiL_upLin, KPsi.lin_kreflLin_relation, Functor.map_zero]


/-! ## The zigzag relations and the interchange law -/

/-- The reflection of the left zigzag of `c` is the right zigzag of `c*`. -/
theorem diag_reflD_zigL (c : Col I X) :
    (pres RD k).diag (reflD (Pivotal.zigL (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD k).diag_eq_id_of_layers _ (Pivotal.zigR (inv RD).toColourDuality ((inv RD).dual c))
    (Obj.ext rfl (by show [c] = [(inv RD).dual ((inv RD).dual c)]; rw [inv_dual_dual])) ?_
    ((zigzags RD k) ((inv RD).dual c)).2
  simp only [layers_reflD, rrev, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    Layer.wl, Layer.wr, rlay, Psi.gen, List.append_nil, inv_dual_dual]
  rfl

/-- The reflection of the right zigzag of `c` is the left zigzag of `c*`. -/
theorem diag_reflD_zigR (c : Col I X) :
    (pres RD k).diag (reflD (Pivotal.zigR (inv RD).toColourDuality c)) = 𝟙 _ := by
  refine (pres RD k).diag_eq_id_of_layers _ (Pivotal.zigL (inv RD).toColourDuality ((inv RD).dual c))
    (Obj.ext ((inv RD).src_dual c).symm rfl) ?_ ((zigzags RD k) ((inv RD).dual c)).1
  simp only [layers_reflD, rrev, Pivotal.zigL, Pivotal.zigR, Diagram.layers_leftZigzag,
    Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    Layer.wl, Layer.wr, rlay, Psi.gen, List.append_nil]
  rw [(inv RD).src_dual c]

/-- The reflection of the interchange law is the interchange law. -/
theorem psiL_interchange (x : InterchangeData (psig RD)) (hx : x.Valid) :
    psiL RD k (InterchangeData.rel k hx) = 0 := by
  let x' : InterchangeData (psig RD) := ⟨x.start, gen x.g, x.mid, gen x.h⟩
  have e₁ : x'.gh₁ = rlay x.hg₂ := by
    simp [x', InterchangeData.gh₁, InterchangeData.hg₂, rlay, gen_dom]
  have e₂ : x'.gh₂ = rlay x.hg₁ := by
    simp [x', InterchangeData.gh₂, InterchangeData.hg₁, rlay, gen_cod]
  have e₃ : x'.hg₁ = rlay x.gh₂ := by
    simp [x', InterchangeData.hg₁, InterchangeData.gh₂, rlay, gen_dom]
  have e₄ : x'.hg₂ = rlay x.gh₁ := by
    simp [x', InterchangeData.hg₂, InterchangeData.gh₁, rlay, gen_cod]
  have hx' : x'.Valid :=
    ⟨e₁ ▸ rlay_valid hx.hg₂, e₂ ▸ rlay_valid hx.hg₁, e₃ ▸ rlay_valid hx.gh₂, e₄ ▸ rlay_valid hx.gh₁⟩
  have hw : x'.dom.WhiskerOK (Obj.nil x.start) [] := ⟨trivial, rfl, trivial⟩
  have ha : x'.dom.whisker (Obj.nil x.start) [] = x.cod :=
    Obj.ext rfl (by simp [x', InterchangeData.dom, InterchangeData.cod, Obj.whisker, Obj.nil,
      gen_dom])
  have hb : x'.cod.whisker (Obj.nil x.start) [] = x.dom :=
    Obj.ext rfl (by simp [x', InterchangeData.dom, InterchangeData.cod, Obj.whisker, Obj.nil,
      gen_cod])
  have key := (pres RD k).diag_interchange x' hx' (Obj.nil x.start) [] hw ha hb
  have hs : ∀ y : InterchangeData (psig RD), ((y.sign : ℤ) : k) = 1 := by
    intro y; simp [InterchangeData.sign, Signature.IsEven.odd_eq_false]
  rw [hs, one_smul] at key
  rw [InterchangeData.rel, psiL_sub, psiL_smul, psiL_of, psiL_of, hs, one_smul, sub_eq_zero]
  refine ((pres RD k).diag_eq_of_layers_eq ?_).trans (key.symm.trans
    ((pres RD k).diag_eq_of_layers_eq ?_))
  · simp only [layers_reflD, rrev, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, ← e₃, ← e₄]
    simp [Layer.whisker, Obj.nil]; exact ⟨rfl, rfl⟩
  · simp only [layers_reflD, rrev, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
      Diagram.layers_mk, Diagram.layers_cast, Diagram.layers_whisker, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, ← e₁, ← e₂]
    simp [Layer.whisker, Obj.nil]; exact ⟨rfl, rfl⟩

/-- Every defining relation of `pres RD k` is reflected to a relation of `U`. -/
theorem psiL_rel (r : (pres RD k).Rel) : psiL RD k ((pres RD k).rel r) = 0 := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · show psiL RD k (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [psiL_sub, psiL_of, psiL_of, diag_reflD_zigL]
    exact sub_self _
  · show psiL RD k (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _)) = 0
    rw [psiL_sub, psiL_of, psiL_of, diag_reflD_zigR]
    exact sub_self _
  · exact psiL_relation r

variable (RD k)

/-- The reflection functor on the free 2-category respects all the relations of `U`. -/
theorem psiFree_respects : (pres RD k).Respects (psiFree RD k) where
  rel r u v hw := by
    rw [freeLift_psiFree, psiL_whisker, psiL_rel, Presentation.whisk_zero]; rfl
  interchange x hx u v hw := by
    rw [freeLift_psiFree, psiL_whisker, psiL_interchange, Presentation.whisk_zero]; rfl

/-! ## The 2-functor `ψ̃ : U → U^co` -/

/-- **The symmetry `ψ̃ : U → U^co` of KL III (3.44)**: reflection of diagrams across the
`x`-axis, with the orientations of the strands inverted. It is the identity on objects and
1-morphisms (`psiU_obj`) and contravariant on 2-morphisms. -/
def psiU : (pres RD k).Presented ⥤ (pres RD k).Presentedᵒᵖ :=
  (pres RD k).lift (psiFree_respects RD k)

instance : (psiU RD k).Additive := by unfold psiU; infer_instance

instance : (psiU RD k).Linear k := by unfold psiU; infer_instance

variable {RD k}

@[simp] theorem psiU_obj (a : Obj (psig RD)) : (psiU RD k).obj ((pres RD k).obj a) = op ((pres RD k).obj a) :=
  rfl

theorem psiU_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (psiU RD k).map ((pres RD k).lin f) = (psiL RD k f).op := by
  unfold psiU; rw [Presentation.lift_lin, freeLift_psiFree]

/-- `ψ̃` on a diagram: the reflected diagram. -/
@[simp] theorem psiU_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (psiU RD k).map ((pres RD k).diag d) = ((pres RD k).diag (reflD d)).op := by
  unfold psiU; rw [Presentation.lift_diag]; rfl

/-- `ψ̃` on normal-form diagrams: reverse the layers and reflect each generator (`Psi.shape`:
dots are fixed, `ψ_{ij} ↦ ψ_{ji}`, `cup l ↦ cap l*`, `cap l ↦ cup l*`). -/
theorem psiU_dg (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    (psiU RD k).map (dg RD k μ s t ls) = (dg RD k μ t s (rls ls)).op := by
  by_cases h : SChain s ls t
  · rw [dg_of h, psiU_diag, reflD_mkD, dg_of]
  · have h₂ : ¬ SChain t (rls ls) s := by
      intro h'
      have := sChain_rls h'
      rw [rls_rls] at this
      exact h this
    rw [dg_of_not h, Functor.map_zero, dg_of_not h₂]
    rfl


/-- **`ψ̃` is a strict 2-functor**: it commutes with whiskering, i.e. with horizontal composition
with identity 2-morphisms (the order of 1-morphisms is preserved). -/
theorem psiU_whisk {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) :
    (psiU RD k).map ((pres RD k).whisk f u v) =
      ((pres RD k).whisk ((psiU RD k).map f).unop u v).op := by
  obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective f
  rw [Presentation.whisk_lin, psiU_lin, psiU_lin, Quiver.Hom.unop_op]
  congr 1
  by_cases h : a.WhiskerOK u v
  · rw [LinDiagram.whisk_of_ok _ h, psiL_whisker]
  · rw [LinDiagram.whisk_of_not_ok _ h, psiL_zero]
    by_cases hg : reflLin k g = 0
    · rw [psiL, hg, Presentation.lin_zero, Presentation.whisk_zero]
    · have hb : ¬ b.WhiskerOK u v := fun hb => h (LinDiagram.whiskerOK_of_ne_zero hg hb)
      rw [psiL, Presentation.whisk_lin, LinDiagram.whisk_of_not_ok _ hb, Presentation.lin_zero]

theorem reflLin_reflLin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    reflLin k (reflLin k f) = f := by
  rw [reflLin, reflLin, ← Finsupp.mapDomain_comp,
    show (reflD ∘ reflD : (a ⟶ b) → (a ⟶ b)) = id from funext reflD_reflD, Finsupp.mapDomain_id]

/-- **`ψ̃² = 1`** (KL III: "`ψ̃` is invertible since its square is the identity"). -/
theorem psiU_psiU {a b : Obj (psig RD)} (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    ((psiU RD k).map ((psiU RD k).map f).unop).unop = f := by
  obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective f
  rw [psiU_lin, Quiver.Hom.unop_op, psiL, psiU_lin, Quiver.Hom.unop_op, psiL, reflLin_reflLin]

/-- **`ψ̃² = 1`**, as an equality of functors: `ψ̃` is an isomorphism `U ≅ U^co`. -/
theorem psiU_comp_leftOp : psiU RD k ⋙ (psiU RD k).leftOp = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  simp only [Functor.comp_map, Functor.leftOp_map, Functor.id_map, eqToHom_refl,
    Category.id_comp, Category.comp_id, Quiver.Hom.op_unop]
  exact psiU_psiU (a := X.as) (b := Y.as) f

/-- **`ψ̃` preserves degrees** (KL III (3.44): `1_μ E_s 1_λ {t} ↦ 1_μ E_s 1_λ {-t}`; a
2-morphism `x{t} ⟶ y{t'}` of degree zero goes to `y{-t'} ⟶ x{-t}`, of degree zero). -/
theorem psiU_homDeg {a b : Obj (psig RD)} {f : (pres RD k).obj a ⟶ (pres RD k).obj b} {t : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) a b t) :
    ((psiU RD k).map f).unop ∈ (pres RD k).homDeg (deg RD) b a t := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  rw [psiU_lin, Quiver.Hom.unop_op]
  exact Presentation.lin_mem_homDeg (LinDiagram.mapDomain_mem_homDeg _ degree_reflD hg)

/-! ### `ψ̃` on generators and bubbles -/

section Generators

variable (μ : X) (i j : I)

/-- `ψ̃` fixes dots. -/
theorem psiU_dot (l : Letter I) :
    (psiU RD k).map (dg RD k μ [l] [l] [([], .dot l, [])]) = (dg RD k μ [l] [l] [([], .dot l, [])]).op :=
  psiU_dg μ _ _ _

/-- `ψ̃` sends the crossing `ψ_{ij}` to `ψ_{ji}` (upward and downward). -/
theorem psiU_cross (ε : Bool) :
    (psiU RD k).map (dg RD k μ [(ε, i), (ε, j)] [(ε, j), (ε, i)] [([], .cross ε i j, [])]) =
      (dg RD k μ [(ε, j), (ε, i)] [(ε, i), (ε, j)] [([], .cross ε j i, [])]).op :=
  psiU_dg μ _ _ _

/-- `ψ̃` sends the cup `1_λ ⟶ E_i F_i 1_λ` to the cap `E_i F_i 1_λ ⟶ 1_λ`. -/
theorem psiU_cup_EF :
    (psiU RD k).map (dg RD k μ [] [up i, dn i] [([], .cup (up i), [])]) =
      (dg RD k μ [up i, dn i] [] [([], .cap (dn i), [])]).op :=
  psiU_dg μ _ _ _

/-- `ψ̃` sends the cup `1_λ ⟶ F_i E_i 1_λ` to the cap `F_i E_i 1_λ ⟶ 1_λ`. -/
theorem psiU_cup_FE :
    (psiU RD k).map (dg RD k μ [] [dn i, up i] [([], .cup (dn i), [])]) =
      (dg RD k μ [dn i, up i] [] [([], .cap (up i), [])]).op :=
  psiU_dg μ _ _ _

/-- `ψ̃` sends the cap `F_i E_i 1_λ ⟶ 1_λ` to the cup `1_λ ⟶ F_i E_i 1_λ`. -/
theorem psiU_cap_FE :
    (psiU RD k).map (dg RD k μ [dn i, up i] [] [([], .cap (up i), [])]) =
      (dg RD k μ [] [dn i, up i] [([], .cup (dn i), [])]).op :=
  psiU_dg μ _ _ _

/-- `ψ̃` sends the cap `E_i F_i 1_λ ⟶ 1_λ` to the cup `1_λ ⟶ E_i F_i 1_λ`. -/
theorem psiU_cap_EF :
    (psiU RD k).map (dg RD k μ [up i, dn i] [] [([], .cap (dn i), [])]) =
      (dg RD k μ [] [up i, dn i] [([], .cup (up i), [])]).op :=
  psiU_dg μ _ _ _

/-- **`ψ̃` fixes all clockwise bubbles**, real and fake. -/
theorem psiU_cwU (m : ℤ) : (psiU RD k).map (cwU RD k μ i m) = (cwU RD k μ i m).op := by
  rw [cwU, psiU_lin, psiL_cwL]

/-- **`ψ̃` fixes all counterclockwise bubbles**, real and fake. -/
theorem psiU_ccwU (m : ℤ) : (psiU RD k).map (ccwU RD k μ i m) = (ccwU RD k μ i m).op := by
  rw [ccwU, psiU_lin, psiL_ccwL]

end Generators

end Categorification.KL3.Diagram
