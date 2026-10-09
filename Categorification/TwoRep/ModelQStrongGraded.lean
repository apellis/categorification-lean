/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongMixed
import Categorification.TwoRep.InterpHomogeneous

/-!
# The model of a `Q`-strong 2-representation preserves degrees

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.2 and (`eq_defF`): `1_λ F_i` is the right
adjoint of `E_i 1_λ` shifted by `⟨-(α_i, λ) - d_i⟩`. The model of `U_Q(g)` given by a `Q`-strong
2-representation (`Categorification.TwoRep.ModelQStrong`) sends a downward strand `F_i 1_μ` to the
right adjoint `R = F_i⟨(α_i, μ - α_i) + d_i⟩` itself, so that the units and counits of `E ⊣ R` have
degree `0`. Hence the model preserves the grading of `U` (KL III Definition 3.1, `deg RD`) up to an
offset on 1-morphisms: a downward strand of colour `⟨(-, i), μ⟩` (right weight `μ`) has offset
`cCol = d_i (1 - ⟨i, μ⟩) = -((α_i, μ - α_i) + d_i)`, upward strands have offset `0`, and the offset of
a word is the sum over its strands (`cWord`).

## Main results

* `QStrong.genHomogeneous_degOff`: the image of every generator `g : x ⟶ y` of `U` is homogeneous of
  degree `deg g + cWord y - cWord x` (`degOff`): dots, upward crossings (by definition), downward
  dots and crossings (mates of homogeneous 2-morphisms under the normalized left adjunctions),
  cups and caps of both orientations (the left adjunction `R ⊣ E` of the `α_i`-string has unit of
  degree `-2 d_i (⟨i, λ⟩ + 1)`, `QStrong.isHomogeneous_adjL_unit`);
* `QStrong.isHomogeneous_interp_degOff`: hence the image of a diagram `d : a ⟶ b` of degree `n`
  is homogeneous of degree `n + cWord b - cWord a`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open KrullSchmidtCat (HomFinite)

universe w v u u₁

section Generic

open GradedHomBicat GradedHomCat

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

/-- **Mates of homogeneous 2-morphisms** under homogeneous adjunctions are homogeneous. -/
theorem isHomogeneous_conjugateEquiv_symm' {a b : GradedHomBicat B} {l₁ l₂ : a ⟶ b}
    {r₁ r₂ : b ⟶ a} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) {d₁ d₂ e : ℤ}
    (hu : IsHomogeneous adj₁.unit d₁) (hc : IsHomogeneous adj₂.counit d₂) {α : r₁ ⟶ r₂}
    (hα : IsHomogeneous α e) :
    IsHomogeneous ((conjugateEquiv adj₁ adj₂).symm α) (d₁ + e + d₂) := by
  rw [conjugateEquiv_symm_apply']
  have h1 : IsHomogeneous (λ_ l₂).inv 0 := isHomogeneous_leftUnitor_inv _
  have h2 : IsHomogeneous (α_ l₁ r₁ l₂).hom 0 := isHomogeneous_associator_hom _ _ _
  have h3 : IsHomogeneous (ρ_ l₁).hom 0 := isHomogeneous_rightUnitor_hom _
  exact (h1.comp ((isHomogeneous_whiskerRight hu l₂).comp (h2.comp ((isHomogeneous_whiskerLeft l₁
    (isHomogeneous_whiskerRight hα l₂)).comp ((isHomogeneous_whiskerLeft l₁ hc).comp h3 rfl) rfl)
    rfl) rfl) rfl).of_eq (by ring)

theorem isHomogeneous_transportLeft_unit {a b : GradedHomBicat B} {R R' : b ⟶ a} {E : a ⟶ b}
    (e : R = R') (adj : R ⊣ E) {n : ℤ} (h : IsHomogeneous adj.unit n) :
    IsHomogeneous (QStrong.transportLeft e adj).unit n := by
  subst e; exact h

theorem isHomogeneous_transportLeft_counit {a b : GradedHomBicat B} {R R' : b ⟶ a} {E : a ⟶ b}
    (e : R = R') (adj : R ⊣ E) {n : ℤ} (h : IsHomogeneous adj.counit n) :
    IsHomogeneous (QStrong.transportLeft e adj).counit n := by
  subst e; exact h

/-- The comparison `K^•(Regrade B d) → K^•(B)` multiplies degrees by `d`. -/
theorem isHomogeneous_comparison_map₂ (d : ℤ) {a b : GradedHomBicat (Regrade B d)} {f g : a ⟶ b}
    {η : f ⟶ g} {n : ℤ} (h : IsHomogeneous η n) :
    IsHomogeneous ((Regrade.comparison d).map₂ η) (d * n) := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨_, Regrade.comparison_map₂_of₂ d n x⟩

theorem isHomogeneous_comparison_mapAdjunction_unit (d : ℤ)
    {a b : GradedHomBicat (Regrade B d)} {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) {n : ℤ}
    (h : IsHomogeneous adj.unit n) :
    IsHomogeneous ((Regrade.comparison d).mapAdjunction adj).unit (d * n) := by
  rw [StrictPseudofunctor.mapAdjunction_unit']
  exact ((isHomogeneous_eqToHom _).comp ((isHomogeneous_comparison_map₂ d h).comp
    (isHomogeneous_eqToHom _) rfl) rfl).of_eq (by ring)

theorem isHomogeneous_comparison_mapAdjunction_counit (d : ℤ)
    {a b : GradedHomBicat (Regrade B d)} {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) {n : ℤ}
    (h : IsHomogeneous adj.counit n) :
    IsHomogeneous ((Regrade.comparison d).mapAdjunction adj).counit (d * n) := by
  rw [StrictPseudofunctor.mapAdjunction_counit']
  exact ((isHomogeneous_eqToHom _).comp ((isHomogeneous_comparison_map₂ d h).comp
    (isHomogeneous_eqToHom _) rfl) rfl).of_eq (by ring)

end Generic

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable (RD) in
/-- The degree offset of a strand: `0` for `E_i`, `d_i (1 - ⟨i, μ⟩)` for `F_i` with right weight
`μ` (CL's `F_i 1_μ` is the right adjoint of `E_i 1_{μ - α_i}` shifted by `⟨-(α_i, μ - α_i) - d_i⟩`). -/
def cCol (c : Col I X) : ℤ := if c.l.1 then 0 else di C c.l.2 * (1 - RD.pair (RD.iY c.l.2) c.r)

variable (RD) in
/-- The degree offset of a word: the sum over its strands. -/
def cWord (w : List (Col I X)) : ℤ := (w.map (cCol RD)).sum

@[simp] theorem cWord_nil : cWord RD [] = 0 := rfl

@[simp] theorem cWord_cons (c : Col I X) (w : List (Col I X)) :
    cWord RD (c :: w) = cCol RD c + cWord RD w := by
  simp [cWord]

@[simp] theorem cWord_append (u w : List (Col I X)) :
    cWord RD (u ++ w) = cWord RD u + cWord RD w := by
  simp [cWord]

@[simp] theorem cCol_up (i : I) (r : X) : cCol RD ⟨(true, i), r⟩ = 0 := rfl

@[simp] theorem cCol_dn (i : I) (r : X) :
    cCol RD ⟨(false, i), r⟩ = di C i * (1 - RD.pair (RD.iY i) r) := rfl

variable (RD) in
/-- The degree of the image of a generator: its degree in `U` plus the offset of its target minus
that of its source. -/
def degOff (g : (psig RD).Gen) : ℤ :=
  deg RD g + cWord RD ((psig RD).cod g) - cWord RD ((psig RD).dom g)

/-! ### The degrees of the images of the generators -/

theorem degOff_dot (c : Col I X) : degOff RD (.gen (.dot c)) = C.dot c.l.2 c.l.2 := by
  show C.dot c.l.2 c.l.2 + cWord RD [c] - cWord RD [c] = _
  ring

theorem degOff_cross_up (i j : I) (ν : X) : degOff RD (.gen (.cross true i j ν)) = -C.dot i j := by
  show -C.dot i j + cWord RD (wd RD ν [(true, j), (true, i)]) -
    cWord RD (wd RD ν [(true, i), (true, j)]) = _
  simp

theorem degOff_cross_dn (i j : I) (ν : X) :
    degOff RD (.gen (.cross false i j ν)) = -C.dot i j := by
  show -C.dot i j + cWord RD (wd RD ν [(false, j), (false, i)]) -
    cWord RD (wd RD ν [(false, i), (false, j)]) = _
  simp only [wd_cons, wd_nil, wt_cons, wt_nil, cWord_cons, cWord_nil, cCol_dn, sh_dn, map_add,
    map_neg, RD.pair_iY_iX_eq_A, add_zero]
  have := di_mul_A_comm C i j
  linear_combination (-1 : ℤ) * this

theorem degOff_cup_up (i : I) (r : X) :
    degOff RD (.cup ⟨(true, i), r⟩) = -(2 * di C i * (RD.pair (RD.iY i) r + 1)) := by
  show di C i * (1 - sgn true * RD.pair (RD.iY i) (sh RD (true, i) + r)) +
    cWord RD [⟨(true, i), r⟩, ⟨(false, i), sh RD (true, i) + r⟩] - cWord RD [] = _
  simp only [cWord_cons, cWord_nil, cCol_up, cCol_dn, sh_up, map_add, RD.pair_iY_iX_self, sgn_true]
  ring

theorem degOff_cup_dn (i : I) (r : X) : degOff RD (.cup ⟨(false, i), r⟩) = 0 := by
  show di C i * (1 - sgn false * RD.pair (RD.iY i) (sh RD (false, i) + r)) +
    cWord RD [⟨(false, i), r⟩, ⟨(true, i), sh RD (false, i) + r⟩] - cWord RD [] = _
  simp only [cWord_cons, cWord_nil, cCol_up, cCol_dn, sh_dn, map_add, map_neg,
    RD.pair_iY_iX_self, sgn_false]
  ring

theorem degOff_cap_up (i : I) (r : X) :
    degOff RD (.cap ⟨(true, i), r⟩) = 2 * di C i * (RD.pair (RD.iY i) r + 1) := by
  show di C i * (1 + sgn true * RD.pair (RD.iY i) r) + cWord RD [] -
    cWord RD [⟨(false, i), sh RD (true, i) + r⟩, ⟨(true, i), r⟩] = _
  simp only [cWord_cons, cWord_nil, cCol_up, cCol_dn, sh_up, map_add, RD.pair_iY_iX_self, sgn_true]
  ring

theorem degOff_cap_dn (i : I) (r : X) : degOff RD (.cap ⟨(false, i), r⟩) = 0 := by
  show di C i * (1 + sgn false * RD.pair (RD.iY i) r) + cWord RD [] -
    cWord RD [⟨(true, i), sh RD (false, i) + r⟩, ⟨(false, i), r⟩] = _
  simp only [cWord_cons, cWord_nil, cCol_up, cCol_dn, sgn_false]
  ring


/-! ### The left adjunctions -/

variable (S : QStrong B C RD k Q)

theorem isHomogeneous_adjLAux_unit (i : I) (b : X) (r : ℤ) {x y : X}
    (e : b + r • RD.iX i = x) (e' : b + (r + 1) • RD.iX i = y) (h : x + RD.iX i = y) :
    IsHomogeneous (adjLAux (S := S) i b r e e' h).unit
      (-(2 * di C i * (RD.pair (RD.iY i) x + 1))) := by
  subst e e'
  exact isHomogeneous_transportLeft_unit _ _
    ((isHomogeneous_comparison_mapAdjunction_unit _ _
      ((S.toStrongSl2 i b).leftAdjN_spec r).1).of_eq (by
        simp only [StrongSl2.wt, toStrongSl2, pair_string]; ring))

theorem isHomogeneous_adjLAux_counit (i : I) (b : X) (r : ℤ) {x y : X}
    (e : b + r • RD.iX i = x) (e' : b + (r + 1) • RD.iX i = y) (h : x + RD.iX i = y) :
    IsHomogeneous (adjLAux (S := S) i b r e e' h).counit
      (2 * di C i * (RD.pair (RD.iY i) x + 1)) := by
  subst e e'
  exact isHomogeneous_transportLeft_counit _ _
    ((isHomogeneous_comparison_mapAdjunction_counit _ _
      ((S.toStrongSl2 i b).leftAdjN_spec r).2.1).of_eq (by
        simp only [StrongSl2.wt, toStrongSl2, pair_string]; ring))

/-- The unit of the left adjunction `R ⊣ E_i 1_λ` of the model has degree `-2 d_i (⟨i, λ⟩ + 1)`. -/
theorem isHomogeneous_adjL_unit (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (adjL (S := S) i h).unit (-(2 * di C i * (RD.pair (RD.iY i) x + 1))) :=
  S.isHomogeneous_adjLAux_unit i _ _ _ _ h

/-- The counit of the left adjunction `R ⊣ E_i 1_λ` of the model has degree `2 d_i (⟨i, λ⟩ + 1)`. -/
theorem isHomogeneous_adjL_counit (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (adjL (S := S) i h).counit (2 * di C i * (RD.pair (RD.iY i) x + 1)) :=
  S.isHomogeneous_adjLAux_counit i _ _ _ _ h

theorem isHomogeneous_adjR_unit (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (S.adjR i h).unit 0 := isHomogeneous_incl₂ _

theorem isHomogeneous_adjR_counit (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (S.adjR i h).counit 0 := isHomogeneous_incl₂ _

theorem isHomogeneous_dotQ (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (S.dotQ i h) (C.dot i i) :=
  (isHomogeneous_of₂ _ _).smul _

theorem isHomogeneous_crossQ (i j : I) {l n m n' : X} (h₁ : l + RD.iX j = n)
    (h₂ : n + RD.iX i = m) (h₃ : l + RD.iX i = n') (h₄ : n' + RD.iX j = m) :
    IsHomogeneous (S.crossQ i j h₁ h₂ h₃ h₄) (-C.dot i j) :=
  isHomogeneous_of₂ _ _

theorem isHomogeneous_dotDnQ (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsHomogeneous (dotDnQ (S := S) i h) (C.dot i i) :=
  (isHomogeneous_conjugateEquiv_symm' _ _ (S.isHomogeneous_adjL_unit i h)
    (S.isHomogeneous_adjL_counit i h) (S.isHomogeneous_dotQ i h)).of_eq (by ring)

theorem isHomogeneous_crossDnQ (Sc : CL.CLScalars C k) (i j : I) {a n n' b : X}
    (hj : n' + RD.iX j = b) (hi : a + RD.iX i = n') (hi' : n + RD.iX i = b)
    (hj' : a + RD.iX j = n) :
    IsHomogeneous (crossDnQ (S := S) Sc i j hj hi hi' hj') (-C.dot i j) := by
  refine ((isHomogeneous_conjugateEquiv_symm' _ _
    (isHomogeneous_comp_unit _ _ (S.isHomogeneous_adjL_unit i hi')
      (S.isHomogeneous_adjL_unit j hj'))
    (isHomogeneous_comp_counit _ _ (S.isHomogeneous_adjL_counit j hj)
      (S.isHomogeneous_adjL_counit i hi))
    (S.isHomogeneous_crossQ i j hj' hi' hi hj)).smul _).of_eq ?_
  subst hi hj' hj
  simp only [map_add, RD.pair_iY_iX_eq_A]
  have h1 := di_mul_A_comm C i j
  linear_combination (-2 : ℤ) * h1

variable (Sc : CL.CLScalars C k)

/-- **The model preserves degrees** up to the offsets of words: the image of every generator `g` of
`U` is homogeneous of degree `deg g + cWord (cod g) - cWord (dom g)`. -/
theorem genHomogeneous_degOff (g : (psig RD).Gen) :
    GenHomogeneous (S.genImg Sc) (degOff RD) g := by
  intro a b ha hb hd hde hc hce
  rcases g with ⟨⟨⟨_ | _, i⟩, r⟩ | ⟨_ | _, i, j, ν⟩⟩ | ⟨⟨_ | _, i⟩, r⟩ | ⟨⟨_ | _, i⟩, r⟩
  · exact (S.isHomogeneous_dotDnQ i _).of_eq (degOff_dot (RD := RD) ⟨(false, i), r⟩).symm
  · exact (S.isHomogeneous_dotQ i _).of_eq (degOff_dot (RD := RD) ⟨(true, i), r⟩).symm
  · obtain rfl : ν = b := hde
    exact (S.isHomogeneous_crossDnQ Sc i j _ _ _ _).of_eq (degOff_cross_dn i j ν).symm
  · obtain rfl : ν = b := hde
    exact (S.isHomogeneous_crossQ i j _ _ _ _).of_eq (degOff_cross_up i j ν).symm
  · subst hde
    exact (S.isHomogeneous_adjR_unit i _).of_eq (degOff_cup_dn i r).symm
  · subst hde
    exact (S.isHomogeneous_adjL_unit i _).of_eq (degOff_cup_up i r).symm
  · subst hce
    exact (S.isHomogeneous_adjR_counit i _).of_eq (degOff_cap_dn i r).symm
  · have ha' : r = a := ha
    subst ha' hce
    exact (S.isHomogeneous_adjL_counit i _).of_eq (degOff_cap_up i r).symm

theorem cWord_append' (u w : List (psig RD).Colour) :
    cWord RD (u ++ w) = cWord RD u + cWord RD w := cWord_append u w

/-- The offsets telescope along a chain of layers. -/
theorem chain_degOff : ∀ (a : Obj (psig RD)) (ls : List (Layer (psig RD))) (b : Obj (psig RD)),
    Chain a ls b → (ls.map fun L => degOff RD L.gen).sum =
      (ls.map fun L => deg RD L.gen).sum + cWord RD b.word - cWord RD a.word
  | _, [], _, h => by cases h; simp
  | a, L :: ls, b, h => by
    obtain ⟨_, rfl, h'⟩ := h
    rw [List.map_cons, List.sum_cons, chain_degOff L.cod ls b h', List.map_cons, List.sum_cons]
    simp only [degOff, Layer.cod, Layer.dom, cWord_append']
    ring

/-- **The image of a diagram** `d : a ⟶ b` is homogeneous of degree
`deg d + cWord b - cWord a`. -/
theorem isHomogeneous_interp_degOff (s₀ t₀ : X) {a b : Obj (psig RD)} (d : a ⟶ b) :
    IsHomogeneous ((interp (S.genImg Sc) s₀ t₀).functor.map d)
      (Diagram.degree (deg RD) d + cWord RD b.word - cWord RD a.word) :=
  (isHomogeneous_interp_map s₀ t₀ d (fun L _ => S.genHomogeneous_degOff Sc L.gen)).of_eq
    (chain_degOff a _ b d.2)

theorem isHomogeneous_freeLift_degOff (s₀ t₀ : X) {a b : Obj (psig RD)}
    {g : LinDiagram k a b} {n : ℤ} (hg : g ∈ LinDiagram.homDeg k (deg RD) a b n) :
    IsHomogeneous ((freeLift k (interp (S.genImg Sc) s₀ t₀).functor).map g)
      (n + cWord RD b.word - cWord RD a.word) := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    erw [freeLift_map_single, one_smul]
    have hd' : Diagram.degree (deg RD) d = n := hd
    exact (S.isHomogeneous_interp_degOff Sc s₀ t₀ d).of_eq (by rw [hd']; rfl)
  | zero => erw [Functor.map_zero]; exact isHomogeneous_zero _
  | add x y _ _ hx hy => erw [Functor.map_add]; exact hx.add hy
  | smul r x _ hx => erw [Functor.map_smul]; exact hx.smul r

/-- **The interpretation of a 2-morphism of degree `n`** of a presentation on the signature of `U`
(for instance `U_Q(g)` itself) between words `a`, `b` is homogeneous of degree
`n + cWord b - cWord a`. -/
theorem isHomogeneous_lift_degOff (P : Presentation (psig RD) k) (s₀ t₀ : X)
    (h : P.Respects (interp (S.genImg Sc) s₀ t₀).functor) {a b : Obj (psig RD)}
    {f : P.obj a ⟶ P.obj b} {n : ℤ} (hf : f ∈ P.homDeg (deg RD) a b n) :
    IsHomogeneous ((P.lift h).map f) (n + cWord RD b.word - cWord RD a.word) := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  rw [Presentation.lift_lin]
  exact S.isHomogeneous_freeLift_degOff Sc s₀ t₀ hg

end QStrong

end Model

end Categorification.TwoRep
