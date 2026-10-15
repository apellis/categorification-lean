/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqModel
import Categorification.TwoRep.BlockSum
import Categorification.TwoRep.LinFunBiproduct

/-!
# Furling: the 1-morphisms of `g` from those of a cover `g̃`

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`: if the Kac–Moody algebra `g̃` of the unfurled graph acts on a category, the
original `g` acts on the same category with

  `E_i = ⊕_{a over i} E_a`,   `F_i = ⊕_{a over i} F_a`,

the weight of `g` being the push-forward of the weight of `g̃` along the cover `π : J → I`. This
file constructs the 1-morphisms, the adjunctions and the dots of this action from a Rouquier
family `S̃` of `g̃` in `LinearCat k`; the crossings and Rouquier's relations are separate.

## Weights and blocks

The labels over a colour are in general infinitely many, so the weights of `g` are not a
function of the weights of `g̃`. We index affinely (`Furling`): fix a base weight `x̃₀` of `g̃`
and a base weight `μ` of `g`, and call a finitely supported `β : J →₀ ℤ` a *block* of weight

  `wtG β = μ + ∑ₐ βₐ α_{π a}`   (for `g`),   `wtT β = x̃₀ + ∑ₐ βₐ α̃ₐ`   (for `g̃`).

The category of `g` at weight `λ` is the product of the categories `S̃.obj (wtT β)` over the
blocks `β` with `wtG β = λ` (`Furling.obj`).

## Relevant edges

`E_i` would be a sum over all labels `a` over `i`, which are infinitely many. A predicate
`rel β a` marks the *relevant* edges `β → β + a`; at each block only finitely many labels over
a colour are relevant, on outgoing and on incoming edges (`finite_out`, `finite_in`). The sums
run over the relevant edges only (`Furling.Edge`), so they are finite. (That `E_a` and `F_a`
vanish on irrelevant edges, which identifies these sums with the full ones, is a separate
hypothesis, used for the relations.) Then

* `E_i` sends `M` to `γ ↦ ⨁_{e : β → γ, label over i} E_{label e} (M β)`;
* `F_i` sends `N` to `β ↦ ⨁_{e : β → γ, label over i} F_{label e} (N γ)`;
* `E_i ⊣ F_i` is the composite of the adjunction between restriction along the source of an
  edge and the sum over the fibres of the source (`blockResAdjunction`), and the block-sum
  adjunction of the labelwise adjunctions `E_a ⊣ F_a`;
* the dot on the summand `e` of `E_i` is `ϖ_a(y)`, the polynomial `ϖ_a` evaluated at the dot `y`
  of `E_a` (Webster, loc. cit., the image of `x` under the homomorphism with label
  `eq:furling-homomorphism`).

## Main definitions

* `blockResAdjunction`: `blockRes s R ⊣ blockSum s L` from blockwise `R ⊣ L`.
* `Furling`, `Furling.Blk`, `Furling.Edge`, `Furling.obj`, `Furling.E`, `Furling.F`,
  `Furling.adj`, `Furling.dot`.
* Generator formulas: `Furling.genE_dot` (the dot on the summand of label `a` is `ϖ_a(y)`),
  `Furling.unit_projF` and `Furling.genE_counit` (the unit and counit of `E_i ⊣ F_i` on the
  summand of label `a` are the unit and counit of `E_a ⊣ F_a`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w₁ w₂ wk u₃ u₄

/-! ## Restriction is left adjoint to the block sum -/

section BlockRes

variable {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]
  [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]
  {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
  {R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a}
  (adj : ∀ (a : A) (d : Dd) (h : s a = d), R a d h ⊣ L a d h)

omit [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)] in
/-- The unit on the block `a` of `d`, for `s a = d`. -/
def blockResUnitAt : ∀ {a : A} {d : Dd} (h : s a = d) (N : ∀ d, D d),
    N d ⟶ (L a d h).obj ((R a (s a) rfl).obj (N (s a)))
  | a, _, rfl, N => (adj a (s a) rfl).unit.app (N (s a))

omit [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)] in
@[simp] theorem blockResUnitAt_rfl (a : A) (N : ∀ d, D d) :
    blockResUnitAt s adj (rfl : s a = s a) N = (adj a (s a) rfl).unit.app (N (s a)) := rfl

omit [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)] in
theorem blockResUnitAt_natural {a : A} {d : Dd} (h : s a = d) {N N' : ∀ d, D d}
    (f : N ⟶ N') :
    f d ≫ blockResUnitAt s adj h N' =
      blockResUnitAt s adj h N ≫ (L a d h).map ((R a (s a) rfl).map (f (s a))) := by
  subst h
  exact (adj a (s a) rfl).unit.naturality (f (s a))

/-- The unit of `blockRes s R ⊣ blockSum s L`. -/
def blockResUnit : 𝟭 (∀ d, D d) ⟶ blockRes s R ⋙ blockSum s L where
  app N d := biproduct.lift fun p : {a // s a = d} => blockResUnitAt s adj p.2 N
  naturality N N' f := funext fun d => biproduct.hom_ext _ _ fun p => by
    change (f d ≫ biproduct.lift fun p : {a // s a = d} => blockResUnitAt s adj p.2 N') ≫
        biproduct.π _ p =
      ((biproduct.lift fun p : {a // s a = d} => blockResUnitAt s adj p.2 N) ≫
        biproduct.map fun p : {a // s a = d} => (L p.1 d p.2).map ((R p.1 (s p.1) rfl).map (f (s p.1)))) ≫
        biproduct.π _ p
    rw [Category.assoc, biproduct.lift_π, Category.assoc, biproduct.map_π,
      biproduct.lift_π_assoc]
    exact blockResUnitAt_natural s adj p.2 f

/-- The counit of `blockRes s R ⊣ blockSum s L`. -/
def blockResCounit : blockSum s L ⋙ blockRes s R ⟶ 𝟭 (∀ a, C a) where
  app M a := (R a (s a) rfl).map (biproduct.π (fun p : {a' // s a' = s a} =>
      (L p.1 (s a) p.2).obj (M p.1)) ⟨a, rfl⟩) ≫ (adj a (s a) rfl).counit.app (M a)
  naturality M M' f := funext fun a => by
    change (R a (s a) rfl).map ((blockSum s L).map f (s a)) ≫
        (R a (s a) rfl).map (biproduct.π _ ⟨a, rfl⟩) ≫ (adj a (s a) rfl).counit.app (M' a) =
      ((R a (s a) rfl).map (biproduct.π _ ⟨a, rfl⟩) ≫ (adj a (s a) rfl).counit.app (M a)) ≫
        f a
    rw [← Functor.map_comp_assoc, blockSum_map, biproduct.map_π, Functor.map_comp,
      Category.assoc, Category.assoc]
    congr 1
    exact (adj a (s a) rfl).counit.naturality (f a)

variable [∀ a, Preadditive (C a)] [∀ a d h, (R a d h).Additive] [∀ a d h, (L a d h).Additive]

include adj in
/-- **Restriction along `s` is left adjoint to the block sum along `s`**, from blockwise
adjunctions `R ⊣ L` (finite sums are also products). -/
def blockResAdjunction : blockRes s R ⊣ blockSum s L :=
  Adjunction.mkOfUnitCounit
    { unit := blockResUnit s adj
      counit := blockResCounit s adj
      left_triangle := by
        ext N : 2
        funext a
        change (R a (s a) rfl).map (biproduct.lift fun p : {a' // s a' = s a} =>
            blockResUnitAt s adj p.2 N) ≫
            𝟙 _ ≫ ((R a (s a) rfl).map (biproduct.π _ ⟨a, rfl⟩) ≫
              (adj a (s a) rfl).counit.app ((R a (s a) rfl).obj (N (s a)))) = 𝟙 _
        rw [Category.id_comp, ← Category.assoc, ← Functor.map_comp, biproduct.lift_π]
        exact (adj a (s a) rfl).left_triangle_components (N (s a))
      right_triangle := by
        classical
        ext M : 2
        funext d
        refine biproduct.hom_ext' _ _ fun q => biproduct.hom_ext _ _ fun p => ?_
        obtain ⟨a, rfl⟩ := p
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_inv_app, Pi.comp_apply, Category.id_comp]
        change (biproduct.ι _ q ≫ (biproduct.lift fun p : {a' // s a' = s a} =>
            blockResUnitAt s adj p.2 ((blockSum s L).obj M)) ≫
            biproduct.map fun p : {a' // s a' = s a} =>
              (L p.1 (s a) p.2).map ((blockResCounit s adj).app M p.1)) ≫
            biproduct.π _ ⟨a, rfl⟩ =
          (biproduct.ι (fun p : {a' // s a' = s a} => (L p.1 (s a) p.2).obj (M p.1)) q ≫ 𝟙 _) ≫
            biproduct.π (fun p : {a' // s a' = s a} => (L p.1 (s a) p.2).obj (M p.1)) ⟨a, rfl⟩
        rw [Category.comp_id, Category.assoc, Category.assoc]
        erw [biproduct.map_π]
        rw [biproduct.lift_π_assoc, blockResUnitAt_rfl, ← Category.assoc]
        erw [← (adj a (s a) rfl).unit_naturality (biproduct.ι _ q)]
        dsimp only [blockResCounit, Functor.id_obj, Functor.comp_obj, Functor.id_map,
          Functor.comp_map]
        rw [Category.assoc, ← (L a (s a) rfl).map_comp,
          ← Category.assoc ((R a (s a) rfl).map (biproduct.ι _ q)), ← (R a (s a) rfl).map_comp]
        by_cases hq : q = ⟨a, rfl⟩
        · subst hq
          rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp]
          exact (adj a (s a) rfl).right_triangle_components (M a)
        · rw [biproduct.ι_π_ne _ hq, Functor.map_zero, zero_comp, Functor.map_zero, comp_zero] }

@[simp] theorem blockResAdjunction_unit_app_π (N : ∀ d, D d) {d : Dd} (p : {a // s a = d}) :
    (blockResAdjunction s adj).unit.app N d ≫ biproduct.π _ p =
      blockResUnitAt s adj p.2 N :=
  biproduct.lift_π _ _

@[simp] theorem blockResAdjunction_counit_app (M : ∀ a, C a) (a : A) :
    (blockResAdjunction s adj).counit.app M a =
      (R a (s a) rfl).map (biproduct.π (fun p : {a' // s a' = s a} =>
        (L p.1 (s a) p.2).obj (M p.1)) ⟨a, rfl⟩) ≫ (adj a (s a) rfl).counit.app (M a) := rfl

end BlockRes

/-! ## Furling data -/

variable {k : Type wk} [CommRing k]
  {J : Type u₁} {I : Type*} {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]

/-- **The combinatorial data of furling** (Webster, arXiv:1603.06311v3, §2.3): a cover
`π : J → I` of the colours, base weights `x̃₀` of `g̃` and `μ` of `g`, and a predicate `rel β a`
of relevant edges `β → β + a`, with finitely many relevant labels over each colour at each
block, outgoing and incoming. (That the 1-morphisms of irrelevant edges vanish is a separate
hypothesis, used for the relations.) -/
structure Furling (RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc)
    (RD : QuantumGroup.UDot.WeightDatum C X Y) where
  /-- The cover of the colours. -/
  π : J → I
  /-- The base weight `x̃₀` of `g̃`. -/
  base : Xc
  /-- The base weight `μ` of `g`. -/
  baseG : X
  /-- The relevant edges `β → β + a`. -/
  rel : (J →₀ ℤ) → J → Prop
  finite_out : ∀ (β : J →₀ ℤ) (i : I), {a | π a = i ∧ rel β a}.Finite
  finite_in : ∀ (γ : J →₀ ℤ) (i : I), {a | π a = i ∧ rel (γ - Finsupp.single a 1) a}.Finite

namespace Furling

variable {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (Φ : Furling RDc RD)

/-- The weight of `g̃` of a block: `x̃₀ + ∑ₐ βₐ α̃ₐ`. -/
def wtT (β : J →₀ ℤ) : Xc := Φ.base + β.sum fun a n => n • RDc.iX a

/-- The weight of `g` of a block: `μ + ∑ₐ βₐ α_{π a}`. -/
def wtG (β : J →₀ ℤ) : X := Φ.baseG + β.sum fun a n => n • RD.iX (Φ.π a)

theorem wtT_add_single (β : J →₀ ℤ) (a : J) :
    Φ.wtT β + RDc.iX a = Φ.wtT (β + Finsupp.single a 1) := by
  simp only [wtT]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
    Finsupp.sum_single_index (by simp), one_smul, add_assoc]

theorem wtG_add_single (β : J →₀ ℤ) (a : J) :
    Φ.wtG β + RD.iX (Φ.π a) = Φ.wtG (β + Finsupp.single a 1) := by
  simp only [wtG]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul]),
    Finsupp.sum_single_index (by simp), one_smul, add_assoc]

/-- The blocks of weight `λ` of `g`. -/
abbrev Blk (l : X) : Type u₁ := {β : J →₀ ℤ // Φ.wtG β = l}

/-- The relevant edges `β → β + a` with `β` of weight `λ` and `a` over `i`. -/
abbrev Edge (i : I) (l : X) : Type u₁ := {p : Φ.Blk l × J // Φ.π p.2 = i ∧ Φ.rel p.1.1 p.2}

variable {Φ}

/-- The source block of an edge. -/
abbrev Edge.src {i : I} {l : X} (e : Φ.Edge i l) : Φ.Blk l := e.1.1

/-- The label of an edge. -/
abbrev Edge.lbl {i : I} {l : X} (e : Φ.Edge i l) : J := e.1.2

theorem Edge.π_lbl {i : I} {l : X} (e : Φ.Edge i l) : Φ.π e.lbl = i := e.2.1

theorem Edge.rel_src {i : I} {l : X} (e : Φ.Edge i l) : Φ.rel e.src.1 e.lbl := e.2.2

/-- The target block of an edge. -/
def Edge.tgt {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) : Φ.Blk l' :=
  ⟨e.src.1 + Finsupp.single e.lbl 1, by
    rw [← Φ.wtG_add_single, e.src.2, e.π_lbl, h]⟩

@[simp] theorem Edge.tgt_val {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) :
    (e.tgt h).1 = e.src.1 + Finsupp.single e.lbl 1 := rfl

theorem Edge.ext {i : I} {l : X} {e e' : Φ.Edge i l} (hs : e.src = e'.src)
    (hl : e.lbl = e'.lbl) : e = e' :=
  Subtype.ext (Prod.ext hs hl)

instance finite_src (i : I) (l : X) (β : Φ.Blk l) : Finite {e : Φ.Edge i l // e.src = β} := by
  have := (Φ.finite_out β.1 i).to_subtype
  refine Finite.of_injective
    (fun e : {e : Φ.Edge i l // e.src = β} =>
      (⟨e.1.lbl, e.1.π_lbl, by have := e.1.rel_src; rwa [e.2] at this⟩ : {a | Φ.π a = i ∧ Φ.rel β.1 a}))
    fun e e' h => Subtype.ext (Edge.ext (e.2.trans e'.2.symm) (congrArg Subtype.val h))

theorem Edge.src_eq_of_tgt {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) :
    e.src.1 = (e.tgt h).1 - Finsupp.single e.lbl 1 := by
  simp

instance finite_tgt (i : I) {l l' : X} (h : l + RD.iX i = l') (γ : Φ.Blk l') :
    Finite {e : Φ.Edge i l // e.tgt h = γ} := by
  have := (Φ.finite_in γ.1 i).to_subtype
  refine Finite.of_injective
    (fun e : {e : Φ.Edge i l // e.tgt h = γ} =>
      (⟨e.1.lbl, e.1.π_lbl, by
        have := e.1.rel_src
        rwa [Edge.src_eq_of_tgt h, e.2] at this⟩ :
        {a | Φ.π a = i ∧ Φ.rel (γ.1 - Finsupp.single a 1) a}))
    fun e e' he => by
      have hl : e.1.lbl = e'.1.lbl := congrArg Subtype.val he
      refine Subtype.ext (Edge.ext (Subtype.ext ?_) hl)
      rw [Edge.src_eq_of_tgt h, Edge.src_eq_of_tgt h, e.2, e'.2, hl]

/-! ## The categories and 1-morphisms of `g` -/

variable (Φ)

variable (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]

/-- The category of a block. -/
abbrev blkCat (β : J →₀ ℤ) : LinearCat.{wk, v₁, u₂} k := S.obj (Φ.wtT β)

/-- **The category of `g` at weight `λ`**: the product of the categories of `g̃` of the blocks
of weight `λ`. -/
abbrev obj (l : X) : LinearCat.{wk, max u₁ v₁, max u₁ u₂} k :=
  LinearCat.of k (∀ β : Φ.Blk l, Φ.blkCat S β.1)

variable {Φ} in
theorem wt_tgt {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) {γ : Φ.Blk l'}
    (he : e.tgt h = γ) : Φ.wtT e.src.1 + RDc.iX e.lbl = Φ.wtT γ.1 := by
  rw [Φ.wtT_add_single, ← he]; rfl

/-- The transport of a block category along an equality of blocks. -/
abbrev blkTr {β β' : J →₀ ℤ} (h : β = β') : blkCat Φ S β ⟶ blkCat Φ S β' :=
  eqToHom (by rw [h])


/-- The restriction functor along the source of edges: the block of an edge is that of its
source. -/
abbrev resSrc {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    blkCat Φ S β.1 ⥤ blkCat Φ S e.src.1 :=
  (blkTr Φ S (congrArg Subtype.val h).symm).obj

/-- The inclusion functor of the block of an edge into that of its source. -/
abbrev incSrc {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    blkCat Φ S e.src.1 ⥤ blkCat Φ S β.1 :=
  (blkTr Φ S (congrArg Subtype.val h)).obj

instance {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    (resSrc Φ S e β h).Additive := (blkTr Φ S _).property.1

instance {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    (resSrc Φ S e β h).Linear k := (blkTr Φ S _).property.2

instance {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    (incSrc Φ S e β h).Additive := (blkTr Φ S _).property.1

instance {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    (incSrc Φ S e β h).Linear k := (blkTr Φ S _).property.2

/-- The transports along an equality of blocks are adjoint. -/
def resIncAdj {i : I} {l : X} (e : Φ.Edge i l) (β : Φ.Blk l) (h : e.src = β) :
    resSrc Φ S e β h ⊣ incSrc Φ S e β h := by
  subst h; exact Adjunction.id

/-- The 1-morphism `E_a` on an edge. -/
abbrev Ea {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : blkCat Φ S e.src.1 ⥤ blkCat Φ S γ.1 :=
  (S.E e.lbl (wt_tgt h e he)).obj

/-- The 1-morphism `F_a` on an edge. -/
abbrev Fa {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : blkCat Φ S γ.1 ⥤ blkCat Φ S e.src.1 :=
  (S.F e.lbl (wt_tgt h e he)).obj

instance {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : (Ea Φ S h e γ he).Additive := (S.E e.lbl (wt_tgt h e he)).property.1

instance {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : (Ea Φ S h e γ he).Linear k := (S.E e.lbl (wt_tgt h e he)).property.2

instance {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : (Fa Φ S h e γ he).Additive := (S.F e.lbl (wt_tgt h e he)).property.1

instance {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : (Fa Φ S h e γ he).Linear k := (S.F e.lbl (wt_tgt h e he)).property.2

/-- The functor `E_i = ⊕_{a over i} E_a`. -/
abbrev EFun (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (∀ β : Φ.Blk l, Φ.blkCat S β.1) ⥤ (∀ γ : Φ.Blk l', Φ.blkCat S γ.1) :=
  blockRes Edge.src (Φ.resSrc S) ⋙ blockSum (Edge.tgt h) (Φ.Ea S h)

/-- The functor `F_i = ⊕_{a over i} F_a`. -/
abbrev FFun (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (∀ γ : Φ.Blk l', Φ.blkCat S γ.1) ⥤ (∀ β : Φ.Blk l, Φ.blkCat S β.1) :=
  blockRes (Edge.tgt h) (Φ.Fa S h) ⋙ blockSum Edge.src (Φ.incSrc S)

instance (i : I) {l l' : X} (h : l + RD.iX i = l') : (Φ.EFun S i h).Additive := by
  have : (blockRes (Edge.src (Φ := Φ) (i := i) (l := l)) (Φ.resSrc S)).Additive := inferInstance
  have : (blockSum (Edge.tgt (Φ := Φ) h) (Φ.Ea S h)).Additive := inferInstance
  infer_instance

instance (i : I) {l l' : X} (h : l + RD.iX i = l') : (Φ.EFun S i h).Linear k := by
  have : (blockRes (Edge.src (Φ := Φ) (i := i) (l := l)) (Φ.resSrc S)).Linear k :=
    inferInstance
  have : (blockSum (Edge.tgt (Φ := Φ) h) (Φ.Ea S h)).Linear k := inferInstance
  infer_instance

instance (i : I) {l l' : X} (h : l + RD.iX i = l') : (Φ.FFun S i h).Additive := by
  have : (blockRes (Edge.tgt (Φ := Φ) h) (Φ.Fa S h)).Additive := inferInstance
  have : (blockSum (Edge.src (Φ := Φ) (i := i) (l := l)) (Φ.incSrc S)).Additive :=
    inferInstance
  infer_instance

instance (i : I) {l l' : X} (h : l + RD.iX i = l') : (Φ.FFun S i h).Linear k := by
  have : (blockRes (Edge.tgt (Φ := Φ) h) (Φ.Fa S h)).Linear k := inferInstance
  have : (blockSum (Edge.src (Φ := Φ) (i := i) (l := l)) (Φ.incSrc S)).Linear k :=
    inferInstance
  infer_instance

/-- **`E_i = ⊕_{a over i} E_a`** on the category of weight `λ`. -/
abbrev E (i : I) {l l' : X} (h : l + RD.iX i = l') : obj Φ S l ⟶ obj Φ S l' :=
  ⟨Φ.EFun S i h, ⟨inferInstance, inferInstance⟩⟩

/-- **`F_i = ⊕_{a over i} F_a`**, from weight `λ + α_i` to `λ`. -/
abbrev F (i : I) {l l' : X} (h : l + RD.iX i = l') : obj Φ S l' ⟶ obj Φ S l :=
  ⟨Φ.FFun S i h, ⟨inferInstance, inferInstance⟩⟩

theorem E_obj (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (Φ.E S i h).obj = Φ.EFun S i h := rfl

theorem F_obj (i : I) {l l' : X} (h : l + RD.iX i = l') :
    (Φ.F S i h).obj = Φ.FFun S i h := rfl

/-- The labelwise adjunctions `E_a ⊣ F_a` on edges. -/
abbrev adjA {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l) (γ : Φ.Blk l')
    (he : e.tgt h = γ) : Ea Φ S h e γ he ⊣ Fa Φ S h e γ he :=
  LinearCat.toAdjunction (S.adj e.lbl (wt_tgt h e he))

/-- The adjunction `E_i ⊣ F_i` of functors. -/
def adjFun (i : I) {l l' : X} (h : l + RD.iX i = l') : (E Φ S i h).obj ⊣ (F Φ S i h).obj :=
  (blockResAdjunction Edge.src (resIncAdj Φ S)).comp (blockAdjunction (Edge.tgt h) (adjA Φ S h))

/-- **The adjunction `E_i ⊣ F_i`**, the sum of the labelwise adjunctions `E_a ⊣ F_a`. -/
def adj (i : I) {l l' : X} (h : l + RD.iX i = l') : Bicategory.Adjunction (E Φ S i h) (F Φ S i h) :=
  LinearCat.ofAdjunction k (adjFun Φ S i h)

/-! ## The dots -/

/-- The dot `ϖ_a(y)` on the 1-morphism `E_a` of an edge. -/
def dotA (ϖ : J → Polynomial k) {i : I} {l l' : X} (h : l + RD.iX i = l') (e : Φ.Edge i l)
    (γ : Φ.Blk l') (he : e.tgt h = γ) : Ea Φ S h e γ he ⟶ Ea Φ S h e γ he :=
  (Polynomial.aeval (show End (S.E e.lbl (wt_tgt h e he)) from S.dot e.lbl (wt_tgt h e he))
    (ϖ e.lbl)).hom

/-- **The dot of `g`** on `E_i`: `ϖ_a(y)` on the summand of label `a` (Webster,
arXiv:1603.06311v3, the image of the dot under the homomorphism with label
`eq:furling-homomorphism`). -/
def dot (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l') :
    E Φ S i h ⟶ E Φ S i h :=
  ObjectProperty.homMk (Functor.whiskerLeft (blockRes Edge.src (resSrc Φ S))
    (blockSumMap (Edge.tgt h) (dotA Φ S ϖ h)))

/-- The generator of `E_i M` at the summand of an edge. -/
abbrev genE (i : I) {l l' : X} (h : l + RD.iX i = l') (M : ∀ β : Φ.Blk l, blkCat Φ S β.1)
    {γ : Φ.Blk l'} (p : {e : Φ.Edge i l // e.tgt h = γ}) :
    (Ea Φ S h p.1 γ p.2).obj (M p.1.src) ⟶ (E Φ S i h).obj.obj M γ :=
  blockι (Edge.tgt h) (Ea Φ S h) ((blockRes Edge.src (resSrc Φ S)).obj M) p

/-- The projection of `F_i N` onto the summand of an edge. -/
abbrev projF (i : I) {l l' : X} (h : l + RD.iX i = l')
    (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (e : Φ.Edge i l) :
    (F Φ S i h).obj.obj N e.src ⟶ (Fa Φ S h e (e.tgt h) rfl).obj (N (e.tgt h)) :=
  biproduct.π (fun p : {e' : Φ.Edge i l // e'.src = e.src} =>
    (incSrc Φ S p.1 e.src p.2).obj ((blockRes (Edge.tgt h) (Fa Φ S h)).obj N p.1)) ⟨e, rfl⟩

/-- The dot of `g` on the summand of label `a` is `ϖ_a(y)`. -/
@[simp] theorem genE_dot (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l')
    (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) {γ : Φ.Blk l'}
    (p : {e : Φ.Edge i l // e.tgt h = γ}) :
    genE Φ S i h M p ≫ (dot Φ S ϖ i h).hom.app M γ =
      (Polynomial.aeval
        (show End (S.E p.1.lbl (wt_tgt h p.1 p.2)) from S.dot p.1.lbl (wt_tgt h p.1 p.2))
        (ϖ p.1.lbl)).hom.app
        (M p.1.src) ≫ genE Φ S i h M p :=
  blockι_blockSumMap _ _ _ p

/-! ## Cups and caps -/

/-- The unit of `E_i ⊣ F_i` on the summand of an edge is the unit of `E_a ⊣ F_a`. -/
@[simp] theorem unit_projF (i : I) {l l' : X} (h : l + RD.iX i = l')
    (M : ∀ β : Φ.Blk l, blkCat Φ S β.1) (e : Φ.Edge i l) :
    (adj Φ S i h).unit.hom.app M e.src ≫ projF Φ S i h ((E Φ S i h).obj.obj M) e =
      (Φ.adjA S h e (e.tgt h) rfl).unit.app (M e.src) ≫
        (Fa Φ S h e (e.tgt h) rfl).map (genE Φ S i h M ⟨e, rfl⟩) := by
  change (Φ.adjFun S i h).unit.app M e.src ≫ _ = _
  rw [adjFun, Adjunction.comp_unit_app, Pi.comp_apply]
  erw [Category.assoc, blockSum_map]
  erw [biproduct.map_π]
  erw [← Category.assoc, blockResAdjunction_unit_app_π, blockResUnitAt_rfl]
  exact Category.id_comp _

/-- The counit of `E_i ⊣ F_i` on the summand of an edge is the counit of `E_a ⊣ F_a`. -/
@[simp] theorem genE_counit (i : I) {l l' : X} (h : l + RD.iX i = l')
    (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (e : Φ.Edge i l) :
    genE Φ S i h ((F Φ S i h).obj.obj N) (⟨e, rfl⟩ : {e' : Φ.Edge i l // e'.tgt h = e.tgt h}) ≫
        (adj Φ S i h).counit.hom.app N (e.tgt h) =
      (Ea Φ S h e (e.tgt h) rfl).map (projF Φ S i h N e) ≫
        (Φ.adjA S h e (e.tgt h) rfl).counit.app (N (e.tgt h)) := by
  change _ ≫ (Φ.adjFun S i h).counit.app N (e.tgt h) = _
  rw [adjFun, Adjunction.comp_counit_app, Pi.comp_apply]
  erw [← Category.assoc, blockι_map, Category.assoc]
  erw [biproduct.ι_desc, blockCounit_rfl, blockResAdjunction_counit_app]
  congr 1
  exact (Φ.Ea S h e (e.tgt h) rfl).congr_map (Category.comp_id _)

end Furling

end Categorification.TwoRep
