/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Furling
import Categorification.TwoRep.BlockSumCross
import Categorification.KLR.Unfurling.Intertwine

/-!
# Furling: the crossings of `g`

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`, and §3.3, Lemma with label `lem:gamma-homo`: the upward crossing of `g` on
`E_j E_i = ⊕ E_a E_b` is the image of `ψ` under the unfurling homomorphism `γ`
(`KLR.Unfurling.crossImage`), read on the summands of the paths `β → β + a → β + a + b` of
labels `a` over `j` and then `b` over `i`.

In the notation of `crossImage` (output labels `t`, the left strand being the last
1-morphism), on the summand of the path `β →a→ →b→` (the word `E_a ≫ E_b`, input labels
`(b, a)`):

* `i ≠ j`: the crossing `E_a ≫ E_b ⟶ E_b ≫ E_a` of `g̃`, followed by `P°_{ab}(y_L, y_R)`, to the
  swapped path `β →b→ →a→`;
* `a = b`: the crossing followed by `h_a(y_L, y_R)⁻¹`, where `ϖ_a(x) - ϖ_a(y) = (x - y) h_a(x, y)`;
* `i = j`, `a ≠ b`: `(ϖ_b(y_L) - ϖ_a(y_R))⁻¹` on the same path, minus the crossing followed by
  `(ϖ_a(y_L) - ϖ_b(y_R))⁻¹` to the swapped path.

The inverses are `Ring.inverse` in the endomorphism rings of the words of `g̃`, so the
crossing is defined without hypotheses; for nilpotent dots the elements inverted are units
(their constant terms `ϖ_b(0) - ϖ_a(0)` and `ϖ_a'(0)` are nonzero). A swapped path whose edges
are not relevant does not occur in the sum; its term is dropped.

## Main definitions and results

* `Furling.gen₂`: the generator of `(E_j ≫ E_i) M` on the summand of a path;
  `Furling.gen₂_ext`: maps out of `(E_j ≫ E_i) M` are determined on these generators;
  `Furling.gen₂_natural`.
* `Furling.cross D i j h₁ h₂ h₃ h₄ : E_j ≫ E_i ⟶ E_i ≫ E_j`, with the generator formula
  `Furling.gen₂_cross` (and `Furling.crossNext_def`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

universe u₁ u₂ v₁ wk u₃ u₄

namespace Furling

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]

/-! ## Polynomials in the dots of a word of length two of `g̃` -/

/-- `p(y_L, y_R)` on `E_a ≫ E_b`, with `y_L` the dot on the last 1-morphism `E_b` (the left
strand) and `y_R` the dot on `E_a`. -/
def pairEval {a b : J} {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
    (p : MvPolynomial (Fin 2) k) : End (S.E a h₁ ≫ S.E b h₂) :=
  KLR.ncEval ![S.E a h₁ ◁ S.dot b h₂, S.dot a h₁ ▷ S.E b h₂] p

variable {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

/-- The component of the crossing of `g` from the path `→a→ →b→` (the word `E_a ≫ E_b`) to the
swapped path `→b→ →a→`: the crossing of `g̃` followed by `P°_{ab}(y_L, y_R)` for colours `i ≠ j`,
by `h_a(y_L, y_R)⁻¹` for `a = b`, and by `-(ϖ_a(y_L) - ϖ_b(y_R))⁻¹` for `a ≠ b` of the same
colour (Webster, arXiv:1603.06311v3, formulas with labels `com0new`, `com0newer`,
`com0newerer`; `KLR.Unfurling.crossImage`). -/
def swapCell (same : Prop) [Decidable same] {a b : J} {x y y' z : Xc} (h₁ : x + RDc.iX a = y)
    (h₂ : y + RDc.iX b = z) (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z) :
    S.E a h₁ ≫ S.E b h₂ ⟶ S.E b h₃ ≫ S.E a h₄ :=
  S.cross b a h₁ h₂ h₃ h₄ ≫
    if same then
      if a = b then Ring.inverse (M₀ := End (S.E b h₃ ≫ S.E a h₄))
        (pairEval S h₃ h₄ (KLR.Unfurling.pwDiff D a))
      else -Ring.inverse (M₀ := End (S.E b h₃ ≫ S.E a h₄)) (pairEval S h₃ h₄
        (KLR.Unfurling.pwAt D.pw a 0 - KLR.Unfurling.pwAt D.pw b 1))
    else pairEval S h₃ h₄ (D.unit a b)

/-- The component of the crossing of `g` from the path `→a→ →b→` to itself, for `a ≠ b` of the
same colour: `(ϖ_b(y_L) - ϖ_a(y_R))⁻¹`. -/
def selfCell {a b : J} {x y z : Xc} (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z) :
    S.E a h₁ ≫ S.E b h₂ ⟶ S.E a h₁ ≫ S.E b h₂ :=
  Ring.inverse (M₀ := End (S.E a h₁ ≫ S.E b h₂)) (pairEval S h₁ h₂ (KLR.Unfurling.pwAt D.pw b 0 - KLR.Unfurling.pwAt D.pw a 1))

/-! ## Paths of length two -/

variable {i j : I} {l l' l'' : X} (h₁ : l + RD.iX j = l') (h₂ : l' + RD.iX i = l'')

/-- **The generator of `(E_j ≫ E_i) M` on the summand of a path** `e` then `e₂`. -/
abbrev gen₂ (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (e₂ : Φ.Edge i l')
    (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    (Ea Φ S h₂ e₂ δ hδ).obj ((Ea Φ S h₁ e e₂.src he.symm).obj (M e.src)) ⟶
      ((E Φ S j h₁ ≫ E Φ S i h₂).obj.obj M) δ :=
  (Ea Φ S h₂ e₂ δ hδ).map (genE Φ S j h₁ M ⟨e, he.symm⟩) ≫
    genE Φ S i h₂ ((E Φ S j h₁).obj.obj M) ⟨e₂, hδ⟩

omit [DecidableEq I] [DecidableEq J] in
theorem gen₂_eq (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (e₂ : Φ.Edge i l')
    (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    gen₂ Φ S h₁ h₂ M e e₂ he hδ =
      (Ea Φ S h₂ e₂ δ hδ).map (biproduct.ι (fun p : {e' : Φ.Edge j l // e'.tgt h₁ = e₂.src} =>
          (Ea Φ S h₁ p.1 e₂.src p.2).obj ((blockRes Edge.src (resSrc Φ S)).obj M p.1))
          ⟨e, he.symm⟩) ≫
        biproduct.ι (fun p : {e' : Φ.Edge i l' // e'.tgt h₂ = δ} =>
          (Ea Φ S h₂ p.1 δ p.2).obj ((blockRes Edge.src (resSrc Φ S)).obj
            ((E Φ S j h₁).obj.obj M) p.1)) ⟨e₂, hδ⟩ := rfl

omit [DecidableEq I] [DecidableEq J] in
/-- Maps out of `(E_j ≫ E_i) M` at a block are determined on the generators of paths. -/
theorem gen₂_ext (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) {δ : Φ.Blk l''} {W : blkCat Φ S δ.1}
    {g g' : ((E Φ S j h₁ ≫ E Φ S i h₂).obj.obj M) δ ⟶ W}
    (h : ∀ (e : Φ.Edge j l) (e₂ : Φ.Edge i l') (he : e₂.src = e.tgt h₁) (hδ : e₂.tgt h₂ = δ),
      gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ g = gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ g') : g = g' := by
  refine biproduct.hom_ext' _ _ fun p => ?_
  refine map_biproduct_hom_ext (Ea Φ S h₂ p.1 δ p.2) _ fun q => ?_
  have := h q.1 p.1 q.2.symm p.2
  rw [gen₂_eq] at this
  exact (Category.assoc _ _ _).symm.trans (this.trans (Category.assoc _ _ _))

omit [DecidableEq I] [DecidableEq J] in
theorem gen₂_natural {M M' : ∀ β : Φ.Blk l, blkCat Φ S β.1} (f : M ⟶ M') (e : Φ.Edge j l)
    (e₂ : Φ.Edge i l') (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ (E Φ S j h₁ ≫ E Φ S i h₂).obj.map f δ =
      (Ea Φ S h₂ e₂ δ hδ).map ((Ea Φ S h₁ e e₂.src he.symm).map (f e.src)) ≫
        gen₂ Φ S h₁ h₂ M' e e₂ he hδ := by
  change _ ≫ (blockSum (Edge.tgt h₂) (Φ.Ea S h₂)).map
    ((blockRes Edge.src (Φ.resSrc S)).map ((Φ.EFun S j h₁).map f)) δ = _
  rw [gen₂_eq, gen₂_eq]
  erw [Category.assoc, blockι_map (Edge.tgt h₂) (Φ.Ea S h₂)
    ((blockRes Edge.src (Φ.resSrc S)).map ((Φ.EFun S j h₁).map f)), ← Category.assoc,
    ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  erw [blockι_map (Edge.tgt h₁) (Φ.Ea S h₁) ((blockRes Edge.src (Φ.resSrc S)).map f)]
  rfl

/-! ## The crossing -/

omit [DecidableEq I] [DecidableEq J] [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
theorem comp_cell_natural {a b c : LinearCat.{wk, v₁, u₂} k} {F₁ : a ⟶ b} {F₂ : b ⟶ c}
    {G : a ⟶ c} (η : F₁ ≫ F₂ ⟶ G) {x y : (a : Type u₂)} (g : x ⟶ y) :
    F₂.obj.map (F₁.obj.map g) ≫ η.hom.app y = η.hom.app x ≫ G.obj.map g :=
  η.hom.naturality g

variable {Φ} in
/-- The edge of label `b` following an edge `e`. -/
abbrev Edge.next {i' j' : I} {m m' : X} (h : m + RD.iX j' = m') (e : Φ.Edge j' m) (b : J)
    (hb : Φ.π b = i') (hr : Φ.rel (e.tgt h).1 b) : Φ.Edge i' m' :=
  ⟨(e.tgt h, b), hb, hr⟩

variable {l₃ : X} (h₃ : l + RD.iX i = l₃) (h₄ : l₃ + RD.iX j = l'')

/-- The first edge `β →b→` of the swapped path. -/
abbrev swapFst (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i) (hs : Φ.rel e.src.1 b) :
    Φ.Edge i l :=
  ⟨(e.src, b), hb, hs⟩

/-- The second edge `→a→` of the swapped path. -/
abbrev swapSnd (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i) (hs : Φ.rel e.src.1 b)
    (hs' : Φ.rel (e.src.1 + Finsupp.single b 1) e.lbl) : Φ.Edge j l₃ :=
  Edge.next h₃ (swapFst Φ e b hb hs) e.lbl e.π_lbl hs'

omit [DecidableEq I] [DecidableEq J] in
theorem swapSnd_tgt (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i) (hr : Φ.rel (e.tgt h₁).1 b)
    (hs : Φ.rel e.src.1 b) (hs' : Φ.rel (e.src.1 + Finsupp.single b 1) e.lbl)
    {δ : Φ.Blk l''} (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (swapSnd Φ h₃ e b hb hs hs').tgt h₄ = δ := by
  rw [← hδ]
  exact Subtype.ext (add_right_comm _ _ _)

/-- The first edge `β →a→` of the path itself, read as an edge over `i = j`. -/
abbrev selfFst (hij : i = j) (e : Φ.Edge j l) : Φ.Edge i l :=
  ⟨(e.src, e.lbl), e.π_lbl.trans hij.symm, e.rel_src⟩

/-- The second edge `→b→` of the path itself, read as an edge over `j = i`. -/
abbrev selfSnd (hij : i = j) (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i)
    (hr : Φ.rel (e.tgt h₁).1 b) : Φ.Edge j l₃ :=
  Edge.next h₃ (selfFst Φ hij e) b (hb.trans hij) hr

omit [DecidableEq I] [DecidableEq J] in
theorem selfSnd_tgt (hij : i = j) (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i)
    (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''} (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (selfSnd Φ h₁ h₃ hij e b hb hr).tgt h₄ = δ := by
  rw [← hδ]; rfl

omit [DecidableEq I] [DecidableEq J] in
/-- Naturality of a 2-cell of `g̃` followed by the generator of a path. -/
theorem cell_gen₂_natural {i' j' : I} {m m' m'' : X} (k₁ : m + RD.iX i' = m')
    (k₂ : m' + RD.iX j' = m'') {y : LinearCat.{wk, v₁, u₂} k} (f₁ : Φ.Edge i' m)
    (f₂ : Φ.Edge j' m') (hf : f₂.src = f₁.tgt k₁) {δ : Φ.Blk m''} (hδ : f₂.tgt k₂ = δ)
    {F₁ : S.obj (Φ.wtT f₁.src.1) ⟶ y} {F₂ : y ⟶ S.obj (Φ.wtT δ.1)}
    (η : F₁ ≫ F₂ ⟶ S.E f₁.lbl (wt_tgt k₁ f₁ hf.symm) ≫ S.E f₂.lbl (wt_tgt k₂ f₂ hδ))
    {M M' : ∀ β : Φ.Blk m, blkCat Φ S β.1} (f : M ⟶ M') :
    F₂.obj.map (F₁.obj.map (f f₁.src)) ≫ η.hom.app (M' f₁.src) ≫
        gen₂ Φ S k₁ k₂ M' f₁ f₂ hf hδ =
      (η.hom.app (M f₁.src) ≫ gen₂ Φ S k₁ k₂ M f₁ f₂ hf hδ) ≫
        (E Φ S i' k₁ ≫ E Φ S j' k₂).obj.map f δ := by
  have h1 := comp_cell_natural η (f f₁.src)
  have h2 := gen₂_natural Φ S k₁ k₂ f f₁ f₂ hf hδ
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ gen₂ Φ S k₁ k₂ M' f₁ f₂ hf hδ) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (η.hom.app (M f₁.src) ≫ ·) h2.symm).trans ?_
  exact (Category.assoc _ _ _).symm

/-- The term of the crossing of `g` to the swapped path `β →b→ →a→`, if both of its edges are
relevant. -/
def crossSwap (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i)
    (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''} (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (Ea Φ S h₂ (Edge.next h₁ e b hb hr) δ hδ).obj ((Ea Φ S h₁ e (e.tgt h₁) rfl).obj (M e.src)) ⟶
      ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ :=
  open Classical in
  if hs : Φ.rel e.src.1 b ∧ Φ.rel (e.src.1 + Finsupp.single b 1) e.lbl then
    (swapCell S D (i = j) (wt_tgt h₁ e rfl) (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ)
        (wt_tgt h₃ (swapFst Φ e b hb hs.1) rfl)
        (wt_tgt h₄ (swapSnd Φ h₃ e b hb hs.1 hs.2)
          (swapSnd_tgt Φ h₁ h₂ h₃ h₄ e b hb hr hs.1 hs.2 hδ))).hom.app (M e.src) ≫
      gen₂ Φ S h₃ h₄ M (swapFst Φ e b hb hs.1) (swapSnd Φ h₃ e b hb hs.1 hs.2) rfl
        (swapSnd_tgt Φ h₁ h₂ h₃ h₄ e b hb hr hs.1 hs.2 hδ)
  else 0

/-- The term of the crossing of `g` on the path itself, for `i = j` and `a ≠ b`. -/
def crossSelf (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i)
    (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''} (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (Ea Φ S h₂ (Edge.next h₁ e b hb hr) δ hδ).obj ((Ea Φ S h₁ e (e.tgt h₁) rfl).obj (M e.src)) ⟶
      ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ :=
  if hij : i = j then
    if e.lbl = b then 0 else
      (selfCell S D (wt_tgt h₁ e rfl) (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ)).hom.app
          (M e.src) ≫
        gen₂ Φ S h₃ h₄ M (selfFst Φ hij e) (selfSnd Φ h₁ h₃ hij e b hb hr) rfl
          (selfSnd_tgt Φ h₁ h₂ h₃ h₄ hij e b hb hr hδ)
  else 0

/-- **The crossing of `g` on the summand of the path** `e` then the edge of label `b`
following it: the swapped-path term (if both edges of the swapped path are relevant) plus,
for `i = j` and `a ≠ b`, the term on the path itself. -/
def crossNext (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i)
    (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''} (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (Ea Φ S h₂ (Edge.next h₁ e b hb hr) δ hδ).obj ((Ea Φ S h₁ e (e.tgt h₁) rfl).obj (M e.src)) ⟶
      ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ :=
  crossSwap Φ S D h₁ h₂ h₃ h₄ M e b hb hr hδ + crossSelf Φ S D h₁ h₂ h₃ h₄ M e b hb hr hδ

/-- `crossNext` along an equality of blocks. -/
def crossKAux (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (γ : Φ.Blk l') (b : J)
    (hb : Φ.π b = i) (hr : Φ.rel γ.1 b) (he : γ = e.tgt h₁) {δ : Φ.Blk l''}
    (hδ : Edge.tgt h₂ (⟨(γ, b), hb, hr⟩ : Φ.Edge i l') = δ) :
    (Ea Φ S h₂ ⟨(γ, b), hb, hr⟩ δ hδ).obj ((Ea Φ S h₁ e γ he.symm).obj (M e.src)) ⟶
      ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ := by
  subst he; exact crossNext Φ S D h₁ h₂ h₃ h₄ M e b hb hr hδ

/-- The crossing of `g` on the summand of a path. -/
def crossK (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (e₂ : Φ.Edge i l')
    (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    (Ea Φ S h₂ e₂ δ hδ).obj ((Ea Φ S h₁ e e₂.src he.symm).obj (M e.src)) ⟶
      ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ :=
  crossKAux Φ S D h₁ h₂ h₃ h₄ M e e₂.src e₂.lbl e₂.2.1 e₂.2.2 he hδ

theorem crossK_next (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l) (b : J)
    (hb : Φ.π b = i) (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''}
    (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    crossK Φ S D h₁ h₂ h₃ h₄ M e (Edge.next h₁ e b hb hr) rfl hδ =
      crossNext Φ S D h₁ h₂ h₃ h₄ M e b hb hr hδ := rfl

theorem crossNext_natural {M M' : ∀ β : Φ.Blk l, blkCat Φ S β.1} (f : M ⟶ M')
    (e : Φ.Edge j l) (b : J) (hb : Φ.π b = i) (hr : Φ.rel (e.tgt h₁).1 b) {δ : Φ.Blk l''}
    (hδ : (Edge.next h₁ e b hb hr).tgt h₂ = δ) :
    (Ea Φ S h₂ (Edge.next h₁ e b hb hr) δ hδ).map
        ((Ea Φ S h₁ e (e.tgt h₁) rfl).map (f e.src)) ≫
        crossNext Φ S D h₁ h₂ h₃ h₄ M' e b hb hr hδ =
      crossNext Φ S D h₁ h₂ h₃ h₄ M e b hb hr hδ ≫ (E Φ S i h₃ ≫ E Φ S j h₄).obj.map f δ := by
  simp only [crossNext, Preadditive.comp_add, Preadditive.add_comp]
  congr 1
  · unfold crossSwap
    split_ifs with hs
    · exact cell_gen₂_natural Φ S h₃ h₄ (swapFst Φ e b hb hs.1) (swapSnd Φ h₃ e b hb hs.1 hs.2)
        rfl (swapSnd_tgt Φ h₁ h₂ h₃ h₄ e b hb hr hs.1 hs.2 hδ)
        (F₁ := S.E e.lbl (wt_tgt h₁ e rfl)) (F₂ := S.E b (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ))
        (swapCell S D (i = j) (wt_tgt h₁ e rfl) (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ)
          (wt_tgt h₃ (swapFst Φ e b hb hs.1) rfl)
          (wt_tgt h₄ (swapSnd Φ h₃ e b hb hs.1 hs.2)
            (swapSnd_tgt Φ h₁ h₂ h₃ h₄ e b hb hr hs.1 hs.2 hδ))) f
    · erw [comp_zero, zero_comp]
  · unfold crossSelf
    split_ifs with hij hab
    · erw [comp_zero, zero_comp]
    · exact cell_gen₂_natural Φ S h₃ h₄ (selfFst Φ hij e) (selfSnd Φ h₁ h₃ hij e b hb hr) rfl
        (selfSnd_tgt Φ h₁ h₂ h₃ h₄ hij e b hb hr hδ)
        (F₁ := S.E e.lbl (wt_tgt h₁ e rfl)) (F₂ := S.E b (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ))
        (selfCell S D (wt_tgt h₁ e rfl) (wt_tgt h₂ (Edge.next h₁ e b hb hr) hδ)) f
    · erw [comp_zero, zero_comp]

theorem crossK_natural {M M' : ∀ β : Φ.Blk l, blkCat Φ S β.1} (f : M ⟶ M') (e : Φ.Edge j l)
    (e₂ : Φ.Edge i l') (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    (Ea Φ S h₂ e₂ δ hδ).map ((Ea Φ S h₁ e e₂.src he.symm).map (f e.src)) ≫
        crossK Φ S D h₁ h₂ h₃ h₄ M' e e₂ he hδ =
      crossK Φ S D h₁ h₂ h₃ h₄ M e e₂ he hδ ≫ (E Φ S i h₃ ≫ E Φ S j h₄).obj.map f δ := by
  obtain ⟨⟨γ, b⟩, hb, hr⟩ := e₂
  obtain rfl : γ = e.tgt h₁ := he
  exact crossNext_natural Φ S D h₁ h₂ h₃ h₄ f e b hb hr hδ

/-- The components of the crossing of `g`. -/
def crossApp (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (δ : Φ.Blk l'') :
    ((E Φ S j h₁ ≫ E Φ S i h₂).obj.obj M) δ ⟶ ((E Φ S i h₃ ≫ E Φ S j h₄).obj.obj M) δ :=
  biproduct.desc fun p : {e₂ : Φ.Edge i l' // e₂.tgt h₂ = δ} =>
    Functor.biproductComparison (Ea Φ S h₂ p.1 δ p.2)
        (fun q : {e : Φ.Edge j l // e.tgt h₁ = p.1.src} =>
          (Ea Φ S h₁ q.1 p.1.src q.2).obj ((blockRes Edge.src (resSrc Φ S)).obj M q.1)) ≫
      biproduct.desc fun q => crossK Φ S D h₁ h₂ h₃ h₄ M q.1 p.1 q.2.symm p.2

@[reassoc]
theorem gen₂_crossApp (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l)
    (e₂ : Φ.Edge i l') (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ crossApp Φ S D h₁ h₂ h₃ h₄ M δ =
      crossK Φ S D h₁ h₂ h₃ h₄ M e e₂ he hδ := by
  rw [gen₂_eq]
  erw [Category.assoc, biproduct.ι_desc, ← Category.assoc, map_ι_biproductComparison,
    biproduct.ι_desc]

theorem crossApp_natural {M M' : ∀ β : Φ.Blk l, blkCat Φ S β.1} (f : M ⟶ M')
    (δ : Φ.Blk l'') :
    (E Φ S j h₁ ≫ E Φ S i h₂).obj.map f δ ≫ crossApp Φ S D h₁ h₂ h₃ h₄ M' δ =
      crossApp Φ S D h₁ h₂ h₃ h₄ M δ ≫ (E Φ S i h₃ ≫ E Φ S j h₄).obj.map f δ := by
  refine gen₂_ext Φ S h₁ h₂ M fun e e₂ he hδ => ?_
  calc _ = (gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ (E Φ S j h₁ ≫ E Φ S i h₂).obj.map f δ) ≫
        crossApp Φ S D h₁ h₂ h₃ h₄ M' δ := (Category.assoc _ _ _).symm
    _ = ((Ea Φ S h₂ e₂ δ hδ).map ((Ea Φ S h₁ e e₂.src he.symm).map (f e.src)) ≫
          gen₂ Φ S h₁ h₂ M' e e₂ he hδ) ≫ crossApp Φ S D h₁ h₂ h₃ h₄ M' δ := by
        rw [gen₂_natural]
    _ = (Ea Φ S h₂ e₂ δ hδ).map ((Ea Φ S h₁ e e₂.src he.symm).map (f e.src)) ≫
          crossK Φ S D h₁ h₂ h₃ h₄ M' e e₂ he hδ := by
        rw [Category.assoc, gen₂_crossApp]
    _ = crossK Φ S D h₁ h₂ h₃ h₄ M e e₂ he hδ ≫ (E Φ S i h₃ ≫ E Φ S j h₄).obj.map f δ :=
        crossK_natural Φ S D h₁ h₂ h₃ h₄ f e e₂ he hδ
    _ = (gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ crossApp Φ S D h₁ h₂ h₃ h₄ M δ) ≫
          (E Φ S i h₃ ≫ E Φ S j h₄).obj.map f δ := by rw [gen₂_crossApp]
    _ = _ := Category.assoc _ _ _

/-- **The upward crossing of `g`** `E_j ≫ E_i ⟶ E_i ≫ E_j` (Webster, arXiv:1603.06311v3,
Lemma `lem:g-action`, the image of `ψ` under `γ` of Lemma `lem:gamma-homo`). -/
def cross : E Φ S j h₁ ≫ E Φ S i h₂ ⟶ E Φ S i h₃ ≫ E Φ S j h₄ :=
  ObjectProperty.homMk
    { app := fun M δ => crossApp Φ S D h₁ h₂ h₃ h₄ M δ
      naturality := fun _ _ f => funext fun δ => crossApp_natural Φ S D h₁ h₂ h₃ h₄ f δ }

/-- **The crossing of `g` on generators**: on the summand of a path it is `crossK`, i.e.
`crossNext` (`crossK_next`). -/
@[simp] theorem gen₂_cross (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge j l)
    (e₂ : Φ.Edge i l') (he : e₂.src = e.tgt h₁) {δ : Φ.Blk l''} (hδ : e₂.tgt h₂ = δ) :
    gen₂ Φ S h₁ h₂ M e e₂ he hδ ≫ (cross Φ S D h₁ h₂ h₃ h₄).hom.app M δ =
      crossK Φ S D h₁ h₂ h₃ h₄ M e e₂ he hδ :=
  gen₂_crossApp Φ S D h₁ h₂ h₃ h₄ M e e₂ he hδ

end Furling

end Categorification.TwoRep
