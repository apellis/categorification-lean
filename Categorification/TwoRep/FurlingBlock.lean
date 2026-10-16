/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingFamily
import Categorification.TwoRep.BiprodDecomp

/-!
# The summands of `F_i E_i` and `E_i F_i` of the furled action on a block

For the furled action `g` of a Rouquier family `g̃` (Webster, arXiv:1603.06311v3, §2.3,
`lem:g-action`), the 1-morphisms `F_i E_i 1_λ` and `E_i F_i 1_λ` on a block `δ` of weight `λ`
are sums over pairs of edges. We split them into

* the *shift-zero* summands `E_a F_a (N δ)` and `F_c E_c (N δ)`, one for each label `a` over `i`
  with an edge `δ - a →a→ δ` or `δ →a→ δ + a`: these are the summands of the coproduct of the
  `sl₂` data of the labels (Webster, Theorem `th:coproduct`), and
* the *mixed* summands `E_a F_b`, `F_b E_a` with `a ≠ b`.

Main definitions:

* `Lbl i δ`, `lab`: the labels at `δ` (indexed by `Fin (nLbl i δ)`), `inEdge`, `outEdge`: the
  canonical edges `δ - a →a→ δ` and `δ →c→ δ + c`.
* `srcIso`: `(F_i E_i N)_δ ≅ (⊞ₜ E_{a_t} F_{a_t} N_δ) ⊞ (⊞_{mixed} E_a F_b N_{δ-a+b})`.
* `tgtIso`: `(E_i F_i N)_δ ≅ (⊞ₜ F_{a_t} E_{a_t} N_δ) ⊞ (⊞_{mixed} F_b E_a N_{δ+b-a})`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe wk v₁ u₁ u₂ u₃ u₄

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

variable {i : I} {l l' : X}

/-! ## Canonical edges -/

section Canonical

variable {Φ}

omit [DecidableEq I] [DecidableEq J] in
theorem wtT_sub_add (β : J →₀ ℤ) (a : J) :
    Φ.wtT (β - Finsupp.single a 1) + RDc.iX a = Φ.wtT β := by
  rw [Φ.wtT_add_single, sub_add_cancel]

/-- The block `δ - a` of weight `λ`, for `δ` of weight `λ + αᵢ` and `a` over `i`. -/
def blkSub (h₁ : l + RD.iX i = l') (δ : Φ.Blk l') (a : J) (ha : Φ.π a = i) : Φ.Blk l :=
  ⟨δ.1 - Finsupp.single a 1, by
    have e := Φ.wtG_add_single (δ.1 - Finsupp.single a 1) a
    have hδ : Φ.wtG δ.1 = l + RD.iX i := δ.2.trans h₁.symm
    rw [sub_add_cancel, hδ, ha] at e
    exact add_right_cancel e⟩

/-- The edge `δ - a →a→ δ`. -/
def inEdge (h₁ : l + RD.iX i = l') (δ : Φ.Blk l') (a : J) (ha : Φ.π a = i)
    (hr : Φ.rel (δ.1 - Finsupp.single a 1) a) :
    Φ.Edge i l :=
  ⟨(blkSub h₁ δ a ha, a), ha, hr⟩

omit [DecidableEq I] [DecidableEq J] in
theorem inEdge_tgt (h₁ : l + RD.iX i = l') (δ : Φ.Blk l') (a : J) (ha : Φ.π a = i)
    (hr : Φ.rel (δ.1 - Finsupp.single a 1) a) : (inEdge h₁ δ a ha hr).tgt h₁ = δ :=
  Subtype.ext (by simp [inEdge, blkSub])

omit [DecidableEq I] [DecidableEq J] in
theorem src_val_of_tgt (h₁ : l + RD.iX i = l') {δ : Φ.Blk l'}
    (p : {e : Φ.Edge i l // e.tgt h₁ = δ}) :
    p.1.src.1 = δ.1 - Finsupp.single p.1.lbl 1 := by
  rw [Edge.src_eq_of_tgt h₁, p.2]

omit [DecidableEq I] [DecidableEq J] in
theorem rel_of_tgt (h₁ : l + RD.iX i = l') {δ : Φ.Blk l'} (p : {e : Φ.Edge i l // e.tgt h₁ = δ}) :
    Φ.rel (δ.1 - Finsupp.single p.1.lbl 1) p.1.lbl := by
  rw [← src_val_of_tgt h₁ p]; exact p.1.rel_src

omit [DecidableEq I] [DecidableEq J] in
/-- Every edge into `δ` is the canonical edge of its label. -/
theorem eq_inEdge (h₁ : l + RD.iX i = l') {δ : Φ.Blk l'} (p : {e : Φ.Edge i l // e.tgt h₁ = δ}) :
    p.1 = inEdge h₁ δ p.1.lbl p.1.π_lbl (rel_of_tgt h₁ p) :=
  Edge.ext (Subtype.ext (src_val_of_tgt h₁ p)) rfl

/-- The edge `δ →c→ δ + c`. -/
abbrev outEdge (δ : Φ.Blk l') (c : J) (hc : Φ.π c = i) (hr : Φ.rel δ.1 c) : Φ.Edge i l' :=
  ⟨(δ, c), hc, hr⟩

omit [DecidableEq I] [DecidableEq J] in
theorem rel_of_src {δ : Φ.Blk l'} (r : {e : Φ.Edge i l' // e.src = δ}) : Φ.rel δ.1 r.1.lbl := by
  have := r.1.rel_src; rwa [r.2] at this

omit [DecidableEq I] [DecidableEq J] in
/-- Every edge out of `δ` is the canonical edge of its label. -/
theorem eq_outEdge {δ : Φ.Blk l'} (r : {e : Φ.Edge i l' // e.src = δ}) :
    r.1 = outEdge δ r.1.lbl r.1.π_lbl (rel_of_src r) :=
  Edge.ext r.2 rfl

end Canonical

/-! ## The labels at a block -/

section Labels

variable {Φ}

variable (i) in
/-- The labels `a` over `i` with an edge `δ - a →a→ δ` or `δ →a→ δ + a`. -/
abbrev Lbl (δ : J →₀ ℤ) : Type u₁ :=
  {a : J // Φ.π a = i ∧ (Φ.rel (δ - Finsupp.single a 1) a ∨ Φ.rel δ a)}

instance (δ : J →₀ ℤ) : Finite (Lbl (Φ := Φ) i δ) :=
  Set.Finite.to_subtype (s := {a : J | Φ.π a = i ∧ (Φ.rel (δ - Finsupp.single a 1) a ∨
      Φ.rel δ a)})
    (((Φ.finite_in δ i).union (Φ.finite_out δ i)).subset fun a ha => by
      rcases ha.2 with h | h
      · exact Or.inl ⟨ha.1, h⟩
      · exact Or.inr ⟨ha.1, h⟩)

variable (Φ i) in
/-- The number of labels at `δ`. -/
abbrev nLbl (δ : J →₀ ℤ) : ℕ := Nat.card (Lbl (Φ := Φ) i δ)

variable (Φ i) in
/-- The labels at `δ`, indexed by `Fin (nLbl Φ i δ)`. -/
def lab (δ : J →₀ ℤ) (t : Fin (nLbl Φ i δ)) : J :=
  ((Finite.equivFin (Lbl (Φ := Φ) i δ)).symm t).1

omit [DecidableEq I] [DecidableEq J] in
theorem lab_π (δ : J →₀ ℤ) (t : Fin (nLbl Φ i δ)) : Φ.π (lab Φ i δ t) = i :=
  ((Finite.equivFin (Lbl (Φ := Φ) i δ)).symm t).2.1

omit [DecidableEq I] [DecidableEq J] in
theorem lab_rel (δ : J →₀ ℤ) (t : Fin (nLbl Φ i δ)) :
    Φ.rel (δ - Finsupp.single (lab Φ i δ t) 1) (lab Φ i δ t) ∨ Φ.rel δ (lab Φ i δ t) :=
  ((Finite.equivFin (Lbl (Φ := Φ) i δ)).symm t).2.2

omit [DecidableEq I] [DecidableEq J] in
theorem lab_injective (δ : J →₀ ℤ) : Function.Injective (lab Φ i δ) := fun _ _ h =>
  (Finite.equivFin (Lbl (Φ := Φ) i δ)).symm.injective (Subtype.ext h)

/-- The index of a label at `δ`. -/
def labIdx (δ : J →₀ ℤ) (a : J) (ha : Φ.π a = i)
    (hr : Φ.rel (δ - Finsupp.single a 1) a ∨ Φ.rel δ a) : Fin (nLbl Φ i δ) :=
  Finite.equivFin (Lbl (Φ := Φ) i δ) ⟨a, ha, hr⟩

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem lab_labIdx (δ : J →₀ ℤ) (a : J) (ha : Φ.π a = i)
    (hr : Φ.rel (δ - Finsupp.single a 1) a ∨ Φ.rel δ a) : lab Φ i δ (labIdx δ a ha hr) = a := by
  unfold lab labIdx; rw [Equiv.symm_apply_apply]

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem labIdx_lab (δ : J →₀ ℤ) (t : Fin (nLbl Φ i δ)) :
    labIdx δ (lab Φ i δ t) (lab_π δ t) (lab_rel δ t) = t := by
  unfold labIdx lab; rw [Subtype.coe_eta]; exact Equiv.apply_symm_apply _ _

end Labels

/-! ## Transports, projections and inclusions -/

section Maps

variable {Φ} {m m' : X} (h : m + RD.iX i = m')

/-- The transport of `F_a N` along an equality of blocks. -/
def trF (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) (e : Φ.Edge i m) {γ : Φ.Blk m'} (he : e.tgt h = γ) :
    (Fa Φ S h e γ he).obj (N γ) ≅ (Fa Φ S h e (e.tgt h) rfl).obj (N (e.tgt h)) := by
  subst he; exact Iso.refl _

omit [DecidableEq I] [DecidableEq J] [∀ (x : Xc), HasFiniteBiproducts (S.obj x).carrier] in
@[simp] theorem trF_rfl (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) (e : Φ.Edge i m) :
    trF S h N e rfl = Iso.refl _ := rfl

/-- The projection of `E_i M` onto the summand of an edge. -/
abbrev projEb (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) {γ : Φ.Blk m'}
    (p : {e : Φ.Edge i m // e.tgt h = γ}) :
    (E Φ S i h).obj.obj M γ ⟶ (Ea Φ S h p.1 γ p.2).obj (M p.1.src) :=
  biproduct.π (fun p : {e : Φ.Edge i m // e.tgt h = γ} =>
    (Ea Φ S h p.1 γ p.2).obj ((blockRes Edge.src (resSrc Φ S)).obj M p.1)) p

/-- The inclusion of the summand `F_b` of an edge `q` out of `β` into `(F_i N)_β`. -/
abbrev incFq (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) {β : Φ.Blk m}
    (q : {e : Φ.Edge i m // e.src = β}) :
    (incSrc Φ S q.1 β q.2).obj ((Fa Φ S h q.1 (q.1.tgt h) rfl).obj (N (q.1.tgt h))) ⟶
      (F Φ S i h).obj.obj N β :=
  biproduct.ι (fun q : {e : Φ.Edge i m // e.src = β} =>
    (incSrc Φ S q.1 β q.2).obj ((blockRes (Edge.tgt h) (Fa Φ S h)).obj N q.1)) q

/-- The projection of `(F_i N)_β` onto the summand `F_b` of an edge `q` out of `β`. -/
abbrev projFq (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) {β : Φ.Blk m}
    (q : {e : Φ.Edge i m // e.src = β}) :
    (F Φ S i h).obj.obj N β ⟶
      (incSrc Φ S q.1 β q.2).obj ((Fa Φ S h q.1 (q.1.tgt h) rfl).obj (N (q.1.tgt h))) :=
  biproduct.π (fun q : {e : Φ.Edge i m // e.src = β} =>
    (incSrc Φ S q.1 β q.2).obj ((blockRes (Edge.tgt h) (Fa Φ S h)).obj N q.1)) q

omit [DecidableEq I] [DecidableEq J] in
@[reassoc (attr := simp)]
theorem genE_projEb (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) {γ : Φ.Blk m'}
    (p : {e : Φ.Edge i m // e.tgt h = γ}) : genE Φ S i h M p ≫ projEb S h M p = 𝟙 _ :=
  biproduct.ι_π_self _ _

omit [DecidableEq I] [DecidableEq J] in
theorem genE_projEb_ne (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) {γ : Φ.Blk m'}
    {p p' : {e : Φ.Edge i m // e.tgt h = γ}} (hp : p ≠ p') :
    genE Φ S i h M p ≫ projEb S h M p' = 0 :=
  biproduct.ι_π_ne _ hp

omit [DecidableEq I] [DecidableEq J] in
@[reassoc (attr := simp)]
theorem incFq_projFq (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) {β : Φ.Blk m}
    (q : {e : Φ.Edge i m // e.src = β}) : incFq S h N q ≫ projFq S h N q = 𝟙 _ :=
  biproduct.ι_π_self _ _

omit [DecidableEq I] [DecidableEq J] in
theorem incFq_projFq_ne (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) {β : Φ.Blk m}
    {q q' : {e : Φ.Edge i m // e.src = β}} (hq : q ≠ q') : incFq S h N q ≫ projFq S h N q' = 0 :=
  biproduct.ι_π_ne _ hq

noncomputable instance fintypeTgt (γ : Φ.Blk m') : Fintype {e : Φ.Edge i m // e.tgt h = γ} :=
  Fintype.ofFinite _

noncomputable instance fintypeSrc (β : Φ.Blk m) : Fintype {e : Φ.Edge i m // e.src = β} :=
  Fintype.ofFinite _

omit [DecidableEq I] [DecidableEq J] in
theorem total_projE (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) (γ : Φ.Blk m') :
    ∑ p : {e : Φ.Edge i m // e.tgt h = γ}, projEb S h M p ≫ genE Φ S i h M p = 𝟙 _ := by
  classical
  exact biproduct_total'

omit [DecidableEq I] [DecidableEq J] in
theorem total_projFq (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) (β : Φ.Blk m) :
    ∑ q : {e : Φ.Edge i m // e.src = β}, projFq S h N q ≫ incFq S h N q = 𝟙 _ := by
  classical
  exact biproduct_total'

end Maps

/-! ## Composition helpers

Compositions through `genE` and the biproduct inclusions/projections of the blocks are only
well-typed up to unfolding instances, so we prove the relations among them by unification with
the following abstract statements. -/

section Helpers

variable {C' D' : Type*} [Category C'] [Category D']

theorem sr_id {A B P : C'} {Z : D'} (K : C' ⥤ D') (u : A ⟶ B) (u' : B ⟶ A) (v : B ⟶ P)
    (v' : P ⟶ B) (g : K.obj P ⟶ Z) (r : Z ⟶ K.obj P) (hu : u ≫ u' = 𝟙 A) (hv : v ≫ v' = 𝟙 B)
    (hg : g ≫ r = 𝟙 _) : (K.map (u ≫ v) ≫ g) ≫ r ≫ K.map (v' ≫ u') = 𝟙 _ := by
  rw [Category.assoc, reassoc_of% hg, ← K.map_comp, Category.assoc, reassoc_of% hv, hu,
    K.map_id]

theorem sr_id' {B P : C'} {Z : D'} (K : C' ⥤ D') (v : B ⟶ P) (v' : P ⟶ B) (g : K.obj P ⟶ Z)
    (r : Z ⟶ K.obj P) (hv : v ≫ v' = 𝟙 B) (hg : g ≫ r = 𝟙 _) :
    (K.map v ≫ g) ≫ r ≫ K.map v' = 𝟙 _ := by
  rw [Category.assoc, reassoc_of% hg, ← K.map_comp, hv, K.map_id]

variable [Preadditive D']

theorem comp_zero_mid {W X' Y' Z' V : D'} (f : W ⟶ X') (g : X' ⟶ Y') (r : Y' ⟶ Z') (h : Z' ⟶ V)
    (hgr : g ≫ r = 0) : (f ≫ g) ≫ r ≫ h = 0 := by
  rw [Category.assoc, reassoc_of% hgr, Limits.zero_comp, Limits.comp_zero]

theorem sr_zero {A B : C'} {Z : D'} [Preadditive C'] (K : C' ⥤ D') [K.Additive] (a : A ⟶ B)
    {A' : C'} (b : B ⟶ A') (g : K.obj B ⟶ Z) (r : Z ⟶ K.obj B) (hg : g ≫ r = 𝟙 _)
    (hab : a ≫ b = 0) : (K.map a ≫ g) ≫ r ≫ K.map b = 0 := by
  rw [Category.assoc, reassoc_of% hg, ← K.map_comp, hab, K.map_zero]

/-- A two-level decomposition of the identity. -/
theorem total_two {ιP : Type*} [Fintype ιP] {Q : ιP → Type*} [∀ p, Fintype (Q p)] {X' : D'}
    {Cp : ιP → Type*} [∀ p, Category (Cp p)] [∀ p, Preadditive (Cp p)] {Z : ∀ p, Cp p}
    (K : ∀ p, Cp p ⥤ D') [∀ p, (K p).Additive]
    (π : ∀ p, X' ⟶ (K p).obj (Z p)) (ι : ∀ p, (K p).obj (Z p) ⟶ X')
    (h : ∑ p, π p ≫ ι p = 𝟙 X') {W : ∀ p, Q p → Cp p} (π' : ∀ p q, Z p ⟶ W p q)
    (ι' : ∀ p q, W p q ⟶ Z p) (h' : ∀ p, ∑ q, π' p q ≫ ι' p q = 𝟙 (Z p)) :
    ∑ x : Σ p, Q p, (π x.1 ≫ (K x.1).map (π' x.1 x.2)) ≫ ((K x.1).map (ι' x.1 x.2) ≫ ι x.1) =
      𝟙 X' := by
  rw [Fintype.sum_sigma, ← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ∀ q, (π p ≫ (K p).map (π' p q)) ≫ ((K p).map (ι' p q) ≫ ι p) =
      π p ≫ (K p).map (π' p q ≫ ι' p q) ≫ ι p := fun q => by
    simp only [Category.assoc, Functor.map_comp]
  rw [Finset.sum_congr rfl fun q _ => e q, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Functor.map_sum, h', CategoryTheory.Functor.map_id, Category.id_comp]

omit [Preadditive D'] in
theorem sr_cancel {A B P P' : C'} {Z Z' : D'} (K : C' ⥤ D') (a : Z ⟶ K.obj P) (b : P ⟶ B)
    (u : B ⟶ A) (u' : A ⟶ B) (c : B ⟶ P') (d : K.obj P' ⟶ Z') (hu : u ≫ u' = 𝟙 B) :
    (a ≫ K.map (b ≫ u)) ≫ (K.map (u' ≫ c) ≫ d) = (a ≫ K.map b) ≫ (K.map c ≫ d) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← K.map_comp_assoc u u', hu, CategoryTheory.Functor.map_id, Category.id_comp]

end Helpers

/-! ## The summands of `F_i E_i` on a block -/

section Source

variable {Φ S} (h₁ : l + RD.iX i = l') (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l')

/-- The shift-zero summand `E_a F_a N_δ` of `(F_i E_i N)_δ`, `a = lab t`. -/
abbrev srcZ (t : Fin (nLbl Φ i δ.1)) : blkCat Φ S δ.1 :=
  (S.E (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).obj.obj
    ((S.F (lab Φ i δ.1 t) (wtT_sub_add (Φ := Φ) δ.1 _)).obj.obj (N δ))

/-- The edge `δ - a →a→ δ` of the label `a = lab t`. -/
abbrev pIn (t : Fin (nLbl Φ i δ.1))
    (hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)) :
    {e : Φ.Edge i l // e.tgt h₁ = δ} :=
  ⟨inEdge h₁ δ (lab Φ i δ.1 t) (lab_π δ.1 t) hr, inEdge_tgt h₁ δ _ _ hr⟩

open scoped Classical in
/-- The inclusion of the shift-zero summand of label `lab t` (zero if there is no edge into
`δ` of this label). -/
def sZ (t : Fin (nLbl Φ i δ.1)) : srcZ N δ t ⟶ ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) δ :=
  if hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t) then
    (Ea Φ S h₁ (pIn h₁ δ t hr).1 δ (pIn h₁ δ t hr).2).map
        ((trF S h₁ N (pIn h₁ δ t hr).1 (pIn h₁ δ t hr).2).hom ≫
          incF Φ S h₁ N (pIn h₁ δ t hr).1) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) (pIn h₁ δ t hr)
  else 0

open scoped Classical in
/-- The projection onto the shift-zero summand of label `lab t`. -/
def rZ (t : Fin (nLbl Φ i δ.1)) : ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) δ ⟶ srcZ N δ t :=
  if hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t) then
    projEb S h₁ ((F Φ S i h₁).obj.obj N) (pIn h₁ δ t hr) ≫
      (Ea Φ S h₁ (pIn h₁ δ t hr).1 δ (pIn h₁ δ t hr).2).map
        (projF Φ S i h₁ N (pIn h₁ δ t hr).1 ≫
          (trF S h₁ N (pIn h₁ δ t hr).1 (pIn h₁ δ t hr).2).inv)
  else 0

/-- The pairs `(p, q)` of an edge `p` into `δ` and an edge `q` out of its source with a
different label: the mixed summands `E_a F_b` of `(F_i E_i N)_δ`. -/
abbrev SrcMix : Type u₁ :=
  {x : Σ p : {e : Φ.Edge i l // e.tgt h₁ = δ}, {q : Φ.Edge i l // q.src = p.1.src} //
    x.2.1.lbl ≠ x.1.1.lbl}

noncomputable instance : Fintype (SrcMix h₁ δ) := Fintype.ofFinite _


/-- The mixed summand `E_a F_b N` of `(p, q)`. -/
abbrev srcM (x : SrcMix h₁ δ) : blkCat Φ S δ.1 :=
  (Ea Φ S h₁ x.1.1.1 δ x.1.1.2).obj ((incSrc Φ S x.1.2.1 x.1.1.1.src x.1.2.2).obj
    ((Fa Φ S h₁ x.1.2.1 (x.1.2.1.tgt h₁) rfl).obj (N (x.1.2.1.tgt h₁))))

/-- The inclusion of a mixed summand. -/
def sM (x : SrcMix h₁ δ) : srcM h₁ N δ x ⟶ ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) δ :=
  (Ea Φ S h₁ x.1.1.1 δ x.1.1.2).map (incFq S h₁ N x.1.2) ≫
    genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) x.1.1

/-- The projection onto a mixed summand. -/
def rM (x : SrcMix h₁ δ) : ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) δ ⟶ srcM h₁ N δ x :=
  projEb S h₁ ((F Φ S i h₁).obj.obj N) x.1.1 ≫ (Ea Φ S h₁ x.1.1.1 δ x.1.1.2).map
    (projFq S h₁ N x.1.2)

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
include hzero in
omit [DecidableEq I] [DecidableEq J] [∀ (x : Xc), HasFiniteBiproducts (S.obj x).carrier] in
theorem isZero_srcZ (t : Fin (nLbl Φ i δ.1))
    (hr : ¬ Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)) :
    IsZero (srcZ N δ t) :=
  Functor.map_isZero (LinearCat.evalAt _) (hzero _ _ (wtT_sub_add (Φ := Φ) δ.1 _) hr)

include hzero in
omit [DecidableEq I] [DecidableEq J] in
theorem sZ_rZ (t : Fin (nLbl Φ i δ.1)) : sZ h₁ N δ t ≫ rZ h₁ N δ t = 𝟙 _ := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · simp only [sZ, rZ, hr, ↓reduceDIte]
    exact sr_id _ _ _ _ _ _ _ (Iso.hom_inv_id _) (incF_projF Φ S h₁ N _)
      (genE_projEb S h₁ _ _)
  · exact (isZero_srcZ N δ hzero t hr).eq_of_src _ _

omit [DecidableEq I] [DecidableEq J] in
theorem pIn_ne {t t' : Fin (nLbl Φ i δ.1)} (htt : t ≠ t')
    (hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t))
    (hr' : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t') 1) (lab Φ i δ.1 t')) :
    pIn h₁ δ t hr ≠ pIn h₁ δ t' hr' := fun h =>
  htt (lab_injective δ.1 (congrArg (fun p => p.1.lbl) h))

omit [DecidableEq I] [DecidableEq J] in
theorem sZ_rZ_ne {t t' : Fin (nLbl Φ i δ.1)} (htt : t ≠ t') : sZ h₁ N δ t ≫ rZ h₁ N δ t' = 0 := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · by_cases hr' : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t') 1) (lab Φ i δ.1 t')
    · simp only [sZ, rZ, hr, hr', ↓reduceDIte]
      exact comp_zero_mid _ _ _ _ (genE_projEb_ne S h₁ _ (pIn_ne h₁ δ htt hr hr'))
    · simp only [rZ, hr', ↓reduceDIte, Limits.comp_zero]
  · simp only [sZ, hr, ↓reduceDIte, Limits.zero_comp]

omit [DecidableEq I] [DecidableEq J] in
theorem sM_rM (x : SrcMix h₁ δ) : sM h₁ N δ x ≫ rM h₁ N δ x = 𝟙 _ :=
  sr_id' _ _ _ _ _ (incFq_projFq S h₁ N _) (genE_projEb S h₁ _ _)

omit [DecidableEq I] in
theorem sM_rM_ne {x x' : SrcMix h₁ δ} (hx : x ≠ x') : sM h₁ N δ x ≫ rM h₁ N δ x' = 0 := by
  obtain ⟨⟨p, q⟩, hq⟩ := x
  obtain ⟨⟨p', q'⟩, hq'⟩ := x'
  by_cases hp : p = p'
  · subst hp
    have hqq : q ≠ q' := fun h => hx (by subst h; rfl)
    exact sr_zero _ _ _ _ _ (genE_projEb S h₁ _ _) (incFq_projFq_ne S h₁ N hqq)
  · exact comp_zero_mid _ _ _ _ (genE_projEb_ne S h₁ _ hp)

omit [DecidableEq I] in
theorem sZ_rM (t : Fin (nLbl Φ i δ.1)) (x : SrcMix h₁ δ) : sZ h₁ N δ t ≫ rM h₁ N δ x = 0 := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · obtain ⟨⟨p, q⟩, hq⟩ := x
    simp only [sZ, hr, ↓reduceDIte]
    by_cases hp : pIn h₁ δ t hr = p
    · subst hp
      refine sr_zero _ _ _ _ _ (genE_projEb S h₁ _ _) ?_
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (incFq_projFq_ne S h₁ N
        (q := ⟨(pIn h₁ δ t hr).1, rfl⟩) (q' := q)
        (fun h => hq (congrArg (fun q => q.1.lbl) h).symm))).trans Limits.comp_zero)
    · exact comp_zero_mid _ _ _ _ (genE_projEb_ne S h₁ _ hp)
  · simp only [sZ, hr, ↓reduceDIte, Limits.zero_comp]

omit [DecidableEq I] in
theorem sM_rZ (x : SrcMix h₁ δ) (t : Fin (nLbl Φ i δ.1)) : sM h₁ N δ x ≫ rZ h₁ N δ t = 0 := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · obtain ⟨⟨p, q⟩, hq⟩ := x
    simp only [rZ, hr, ↓reduceDIte]
    by_cases hp : p = pIn h₁ δ t hr
    · subst hp
      refine sr_zero _ _ _ _ _ (genE_projEb S h₁ _ _) ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (incFq_projFq_ne S h₁ N (q := q)
        (q' := ⟨(pIn h₁ δ t hr).1, rfl⟩) (fun h => hq (congrArg (fun q => q.1.lbl) h)))).trans
        Limits.zero_comp)
    · exact comp_zero_mid _ _ _ _ (genE_projEb_ne S h₁ _ hp)
  · simp only [rZ, hr, ↓reduceDIte, Limits.comp_zero]


omit [DecidableEq I] [DecidableEq J] in
theorem inEdge_congr {a a' : J} (h : a = a') (ha : Φ.π a = i) (ha' : Φ.π a' = i)
    (hr : Φ.rel (δ.1 - Finsupp.single a 1) a) (hr' : Φ.rel (δ.1 - Finsupp.single a' 1) a') :
    inEdge h₁ δ a ha hr = inEdge h₁ δ a' ha' hr' := by
  subst h; rfl

omit [DecidableEq I] in
theorem src_total :
    ∑ t, rZ h₁ N δ t ≫ sZ h₁ N δ t + ∑ x, rM h₁ N δ x ≫ sM h₁ N δ x = 𝟙 _ := by
  classical
  have H := total_two (Cp := fun p : {e : Φ.Edge i l // e.tgt h₁ = δ} => blkCat Φ S p.1.src.1)
    (Z := fun p => (F Φ S i h₁).obj.obj N p.1.src)
    (Q := fun p : {e : Φ.Edge i l // e.tgt h₁ = δ} => {q : Φ.Edge i l // q.src = p.1.src})
    (W := fun _ q => (incSrc Φ S q.1 _ q.2).obj
      ((Fa Φ S h₁ q.1 (q.1.tgt h₁) rfl).obj (N (q.1.tgt h₁))))
    (fun p => Ea Φ S h₁ p.1 δ p.2)
    (projEb S h₁ ((F Φ S i h₁).obj.obj N)) (genE Φ S i h₁ ((F Φ S i h₁).obj.obj N))
    (total_projE S h₁ _ δ) (fun _ q => projFq S h₁ N q) (fun _ q => incFq S h₁ N q)
    (fun p => total_projFq S h₁ N p.1.src)
  refine Eq.trans ?_ H
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Σ p : {e : Φ.Edge i l // e.tgt h₁ = δ},
    {q : Φ.Edge i l // q.src = p.1.src} => x.2.1.lbl ≠ x.1.1.lbl), add_comm]
  congr 1
  · rw [show instFintypeSrcMix h₁ δ = Subtype.fintype _ from Subsingleton.elim _ _]
    exact Finset.sum_congr rfl fun _ _ => rfl
  · rw [← Fintype.sum_subtype_add_sum_subtype
      (fun t => Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t))]
    have hz : ∑ t : {t // ¬ Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)},
        rZ h₁ N δ t ≫ sZ h₁ N δ t = 0 :=
      Finset.sum_eq_zero fun t _ => by simp only [rZ, t.2, ↓reduceDIte, Limits.zero_comp]
    rw [hz, add_zero]
    refine Fintype.sum_bijective (fun t => ⟨⟨pIn h₁ δ t.1 t.2, ⟨(pIn h₁ δ t.1 t.2).1, rfl⟩⟩,
      not_not.mpr rfl⟩) ⟨fun t t' h => Subtype.ext (lab_injective δ.1
        (congrArg (fun x => x.1.1.1.lbl) h)), fun x => ?_⟩ _ _ fun t => ?_
    · obtain ⟨⟨p, q⟩, hx⟩ := x
      have hl : q.1.lbl = p.1.lbl := not_not.mp hx
      have ht := lab_labIdx δ.1 p.1.lbl p.1.π_lbl (Or.inl (rel_of_tgt h₁ p))
      have hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 (labIdx δ.1 p.1.lbl p.1.π_lbl
          (Or.inl (rel_of_tgt h₁ p)))) 1) (lab Φ i δ.1 (labIdx δ.1 p.1.lbl p.1.π_lbl
          (Or.inl (rel_of_tgt h₁ p)))) := by rw [ht]; exact rel_of_tgt h₁ p
      have hp : pIn h₁ δ _ hr = p :=
        Subtype.ext ((inEdge_congr h₁ δ ht _ _ hr _).trans (eq_inEdge h₁ p).symm)
      refine ⟨⟨_, hr⟩, Subtype.ext (Sigma.subtype_ext hp ?_)⟩
      exact (congrArg Subtype.val hp).trans
        (Edge.ext (q.2.trans rfl).symm hl.symm)
    · simp only [rZ, sZ, t.2, ↓reduceDIte]
      exact sr_cancel _ _ _ _ _ _ _ (Iso.inv_hom_id _)

end Source

/-! ## The summands of `E_i F_i` on a block -/

section Target

variable {Φ S} {l'' : X} (h₂ : l' + RD.iX i = l'') (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1)
  (δ : Φ.Blk l')

/-- The shift-zero summand `F_c E_c N_δ` of `(E_i F_i N)_δ`, `c = lab t`. -/
abbrev tgtZ (t : Fin (nLbl Φ i δ.1)) : blkCat Φ S δ.1 :=
  (S.F (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).obj.obj
    ((S.E (lab Φ i δ.1 t) (Φ.wtT_add_single δ.1 _)).obj.obj (N δ))

/-- The edge `δ →c→ δ + c` of the label `c = lab t`. -/
abbrev rOut (t : Fin (nLbl Φ i δ.1)) (hr : Φ.rel δ.1 (lab Φ i δ.1 t)) :
    {e : Φ.Edge i l' // e.src = δ} :=
  ⟨outEdge δ (lab Φ i δ.1 t) (lab_π δ.1 t) hr, rfl⟩

open scoped Classical in
/-- The inclusion of the shift-zero summand of label `lab t` (zero if there is no edge out of
`δ` of this label). -/
def sZ' (t : Fin (nLbl Φ i δ.1)) : tgtZ N δ t ⟶ ((E Φ S i h₂ ≫ F Φ S i h₂).obj.obj N) δ :=
  if hr : Φ.rel δ.1 (lab Φ i δ.1 t) then
    (Fa Φ S h₂ (rOut δ t hr).1 _ rfl).map (genE Φ S i h₂ N ⟨(rOut δ t hr).1, rfl⟩) ≫
      incFq S h₂ ((E Φ S i h₂).obj.obj N) (rOut δ t hr)
  else 0

open scoped Classical in
/-- The projection onto the shift-zero summand of label `lab t`. -/
def rZ' (t : Fin (nLbl Φ i δ.1)) : ((E Φ S i h₂ ≫ F Φ S i h₂).obj.obj N) δ ⟶ tgtZ N δ t :=
  if hr : Φ.rel δ.1 (lab Φ i δ.1 t) then
    projFq S h₂ ((E Φ S i h₂).obj.obj N) (rOut δ t hr) ≫
      (Fa Φ S h₂ (rOut δ t hr).1 _ rfl).map (projEb S h₂ N ⟨(rOut δ t hr).1, rfl⟩)
  else 0

/-- The pairs `(r, s)` of an edge `r` out of `δ` and an edge `s` into its target with a
different label: the mixed summands `F_b E_a` of `(E_i F_i N)_δ`. -/
abbrev TgtMix : Type u₁ :=
  {y : Σ r : {e : Φ.Edge i l' // e.src = δ}, {s : Φ.Edge i l' // s.tgt h₂ = r.1.tgt h₂} //
    y.2.1.lbl ≠ y.1.1.lbl}

noncomputable instance : Fintype (TgtMix h₂ δ) := Fintype.ofFinite _


/-- The mixed summand `F_b E_a N` of `(r, s)`. -/
abbrev tgtM (y : TgtMix h₂ δ) : blkCat Φ S δ.1 :=
  (incSrc Φ S y.1.1.1 δ y.1.1.2).obj ((Fa Φ S h₂ y.1.1.1 (y.1.1.1.tgt h₂) rfl).obj
    ((Ea Φ S h₂ y.1.2.1 (y.1.1.1.tgt h₂) y.1.2.2).obj (N y.1.2.1.src)))

/-- The inclusion of a mixed summand. -/
def sM' (y : TgtMix h₂ δ) : tgtM h₂ N δ y ⟶ ((E Φ S i h₂ ≫ F Φ S i h₂).obj.obj N) δ :=
  (incSrc Φ S y.1.1.1 δ y.1.1.2).map ((Fa Φ S h₂ y.1.1.1 (y.1.1.1.tgt h₂) rfl).map
    (genE Φ S i h₂ N y.1.2)) ≫ incFq S h₂ ((E Φ S i h₂).obj.obj N) y.1.1

/-- The projection onto a mixed summand. -/
def rM' (y : TgtMix h₂ δ) : ((E Φ S i h₂ ≫ F Φ S i h₂).obj.obj N) δ ⟶ tgtM h₂ N δ y :=
  projFq S h₂ ((E Φ S i h₂).obj.obj N) y.1.1 ≫ (incSrc Φ S y.1.1.1 δ y.1.1.2).map
    ((Fa Φ S h₂ y.1.1.1 (y.1.1.1.tgt h₂) rfl).map (projEb S h₂ N y.1.2))

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

include hzero in
omit [DecidableEq I] [DecidableEq J] [∀ (x : Xc), HasFiniteBiproducts (S.obj x).carrier] in
theorem isZero_tgtZ (t : Fin (nLbl Φ i δ.1)) (hr : ¬ Φ.rel δ.1 (lab Φ i δ.1 t)) :
    IsZero (tgtZ N δ t) :=
  Functor.map_isZero _ (Functor.map_isZero (LinearCat.evalAt _)
    (hzero _ _ (Φ.wtT_add_single δ.1 _) hr))

theorem map_comp_eq_id {C₁ C₂ : Type*} [Category C₁] [Category C₂] (K : C₁ ⥤ C₂) {A B : C₁}
    {v : A ⟶ B} {v' : B ⟶ A} (hv : v ≫ v' = 𝟙 A) : K.map v ≫ K.map v' = 𝟙 _ := by
  rw [← K.map_comp, hv, CategoryTheory.Functor.map_id]

theorem map_comp_eq_zero {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Preadditive C₁]
    [Preadditive C₂] (K : C₁ ⥤ C₂) [K.Additive] {A B A' : C₁}
    {v : A ⟶ B} {v' : B ⟶ A'} (hv : v ≫ v' = 0) : K.map v ≫ K.map v' = 0 := by
  rw [← K.map_comp, hv, K.map_zero]

include hzero in
omit [DecidableEq I] [DecidableEq J] in
theorem sZ_rZ' (t : Fin (nLbl Φ i δ.1)) : sZ' h₂ N δ t ≫ rZ' h₂ N δ t = 𝟙 _ := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · simp only [sZ', rZ', hr, ↓reduceDIte]
    exact sr_id' _ _ _ _ _ (genE_projEb S h₂ _ _) (incFq_projFq S h₂ _ _)
  · exact (isZero_tgtZ N δ hzero t hr).eq_of_src _ _

omit [DecidableEq I] [DecidableEq J] in
theorem rOut_ne {t t' : Fin (nLbl Φ i δ.1)} (htt : t ≠ t') (hr : Φ.rel δ.1 (lab Φ i δ.1 t))
    (hr' : Φ.rel δ.1 (lab Φ i δ.1 t')) : rOut δ t hr ≠ rOut δ t' hr' := fun h =>
  htt (lab_injective δ.1 (congrArg (fun p => p.1.lbl) h))

omit [DecidableEq I] [DecidableEq J] in
theorem sZ_rZ_ne' {t t' : Fin (nLbl Φ i δ.1)} (htt : t ≠ t') :
    sZ' h₂ N δ t ≫ rZ' h₂ N δ t' = 0 := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · by_cases hr' : Φ.rel δ.1 (lab Φ i δ.1 t')
    · simp only [sZ', rZ', hr, hr', ↓reduceDIte]
      exact comp_zero_mid _ _ _ _ (incFq_projFq_ne S h₂ _ (rOut_ne δ htt hr hr'))
    · simp only [rZ', hr', ↓reduceDIte, Limits.comp_zero]
  · simp only [sZ', hr, ↓reduceDIte, Limits.zero_comp]

omit [DecidableEq I] [DecidableEq J] in
theorem sM_rM' (y : TgtMix h₂ δ) : sM' h₂ N δ y ≫ rM' h₂ N δ y = 𝟙 _ :=
  sr_id' _ _ _ _ _ (map_comp_eq_id _ (genE_projEb S h₂ _ _)) (incFq_projFq S h₂ _ _)

omit [DecidableEq I] in
theorem sM_rM_ne' {y y' : TgtMix h₂ δ} (hy : y ≠ y') : sM' h₂ N δ y ≫ rM' h₂ N δ y' = 0 := by
  obtain ⟨⟨r, q⟩, hq⟩ := y
  obtain ⟨⟨r', q'⟩, hq'⟩ := y'
  by_cases hr : r = r'
  · subst hr
    have hqq : q ≠ q' := fun h => hy (by subst h; rfl)
    exact sr_zero _ _ _ _ _ (incFq_projFq S h₂ _ _)
      (map_comp_eq_zero _ (genE_projEb_ne S h₂ _ hqq))
  · exact comp_zero_mid _ _ _ _ (incFq_projFq_ne S h₂ _ hr)

omit [DecidableEq I] in
theorem sZ_rM' (t : Fin (nLbl Φ i δ.1)) (y : TgtMix h₂ δ) : sZ' h₂ N δ t ≫ rM' h₂ N δ y = 0 := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · obtain ⟨⟨r, q⟩, hq⟩ := y
    simp only [sZ', hr, ↓reduceDIte]
    by_cases hp : rOut δ t hr = r
    · subst hp
      exact sr_zero _ _ _ _ _ (incFq_projFq S h₂ _ _) (genE_projEb_ne S h₂ _
        (p := ⟨(rOut δ t hr).1, rfl⟩) (p' := q)
        (fun h => hq (congrArg (fun q => q.1.lbl) h).symm))
    · exact comp_zero_mid _ _ _ _ (incFq_projFq_ne S h₂ _ hp)
  · simp only [sZ', hr, ↓reduceDIte, Limits.zero_comp]

omit [DecidableEq I] in
theorem sM_rZ' (y : TgtMix h₂ δ) (t : Fin (nLbl Φ i δ.1)) : sM' h₂ N δ y ≫ rZ' h₂ N δ t = 0 := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · obtain ⟨⟨r, q⟩, hq⟩ := y
    simp only [rZ', hr, ↓reduceDIte]
    by_cases hp : r = rOut δ t hr
    · subst hp
      exact sr_zero _ _ _ _ _ (incFq_projFq S h₂ _ _) (map_comp_eq_zero _ (genE_projEb_ne S h₂ _
        (p := q) (p' := ⟨(rOut δ t hr).1, rfl⟩) (fun h => hq (congrArg (fun q => q.1.lbl) h))))
    · exact comp_zero_mid _ _ _ _ (incFq_projFq_ne S h₂ _ hp)
  · simp only [rZ', hr, ↓reduceDIte, Limits.comp_zero]

omit [DecidableEq I] [DecidableEq J] in
theorem outEdge_congr {c c' : J} (h : c = c') (hc : Φ.π c = i) (hc' : Φ.π c' = i)
    (hr : Φ.rel δ.1 c) (hr' : Φ.rel δ.1 c') : outEdge δ c hc hr = outEdge δ c' hc' hr' := by
  subst h; rfl

omit [DecidableEq I] in
theorem tgt_total :
    ∑ t, rZ' h₂ N δ t ≫ sZ' h₂ N δ t + ∑ y, rM' h₂ N δ y ≫ sM' h₂ N δ y = 𝟙 _ := by
  classical
  have H := total_two
    (Cp := fun r : {e : Φ.Edge i l' // e.src = δ} => blkCat Φ S (r.1.tgt h₂).1)
    (Z := fun r => (E Φ S i h₂).obj.obj N (r.1.tgt h₂))
    (Q := fun r : {e : Φ.Edge i l' // e.src = δ} =>
      {s : Φ.Edge i l' // s.tgt h₂ = r.1.tgt h₂})
    (W := fun _ s => (Ea Φ S h₂ s.1 _ s.2).obj (N s.1.src))
    (fun r => Fa Φ S h₂ r.1 (r.1.tgt h₂) rfl ⋙ incSrc Φ S r.1 δ r.2)
    (projFq S h₂ ((E Φ S i h₂).obj.obj N)) (incFq S h₂ ((E Φ S i h₂).obj.obj N))
    (total_projFq S h₂ _ δ) (fun _ s => projEb S h₂ N s) (fun _ s => genE Φ S i h₂ N s)
    (fun r => total_projE S h₂ N (r.1.tgt h₂))
  refine Eq.trans ?_ H
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : Σ r : {e : Φ.Edge i l' // e.src = δ},
    {s : Φ.Edge i l' // s.tgt h₂ = r.1.tgt h₂} => y.2.1.lbl ≠ y.1.1.lbl), add_comm]
  congr 1
  · rw [show instFintypeTgtMix h₂ δ = Subtype.fintype _ from Subsingleton.elim _ _]
    exact Finset.sum_congr rfl fun _ _ => rfl
  · rw [← Fintype.sum_subtype_add_sum_subtype (fun t => Φ.rel δ.1 (lab Φ i δ.1 t))]
    have hz : ∑ t : {t // ¬ Φ.rel δ.1 (lab Φ i δ.1 t)}, rZ' h₂ N δ t ≫ sZ' h₂ N δ t = 0 :=
      Finset.sum_eq_zero fun t _ => by simp only [rZ', t.2, ↓reduceDIte, Limits.zero_comp]
    rw [hz, add_zero]
    refine Fintype.sum_bijective (fun t => ⟨⟨rOut δ t.1 t.2, ⟨(rOut δ t.1 t.2).1, rfl⟩⟩,
      not_not.mpr rfl⟩) ⟨fun t t' h => Subtype.ext (lab_injective δ.1
        (congrArg (fun x => x.1.1.1.lbl) h)), fun y => ?_⟩ _ _ fun t => ?_
    · obtain ⟨⟨r, q⟩, hy⟩ := y
      have hl : q.1.lbl = r.1.lbl := not_not.mp hy
      have ht := lab_labIdx δ.1 r.1.lbl r.1.π_lbl (Or.inr (rel_of_src r))
      have hr : Φ.rel δ.1 (lab Φ i δ.1 (labIdx δ.1 r.1.lbl r.1.π_lbl
          (Or.inr (rel_of_src r)))) := by rw [ht]; exact rel_of_src r
      have hp : rOut δ _ hr = r :=
        Subtype.ext ((outEdge_congr δ ht (lab_π _ _) _ hr _).trans (eq_outEdge r).symm)
      refine ⟨⟨_, hr⟩, Subtype.ext (Sigma.subtype_ext hp ?_)⟩
      refine (congrArg Subtype.val hp).trans (Edge.ext ?_ hl.symm)
      apply Subtype.ext
      rw [Edge.src_eq_of_tgt h₂ r.1, Edge.src_eq_of_tgt h₂ q.1, q.2, hl]
    · simp only [rZ', sZ', t.2, ↓reduceDIte]
      rfl

end Target

/-! ## The decompositions -/

section Iso

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {Φ S} {l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
  (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (δ : Φ.Blk l')
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

/-- **`(F_i E_i N)_δ` as a biproduct** of the shift-zero summands `E_a F_a N_δ` (labels `a` at
`δ`) and the mixed summands `E_a F_b N_{δ-a+b}`, `a ≠ b`. -/
def srcIso : ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) δ ≅
    (⨁ srcZ (i := i) N δ) ⊞ (⨁ srcM h₁ N δ) :=
  isoOfDecomp₂ (ι := Fin (nLbl Φ i δ.1)) (κ := SrcMix h₁ δ) (Y := srcZ (i := i) N δ)
    (Z := srcM h₁ N δ) (sZ h₁ N δ) (rZ h₁ N δ) (sM h₁ N δ) (rM h₁ N δ) (sZ_rZ h₁ N δ hzero)
    (fun _ _ h => sZ_rZ_ne h₁ N δ h) (sM_rM h₁ N δ) (fun _ _ h => sM_rM_ne h₁ N δ h)
    (sZ_rM h₁ N δ) (sM_rZ h₁ N δ) (src_total h₁ N δ)

/-- **`(E_i F_i N)_δ` as a biproduct** of the shift-zero summands `F_c E_c N_δ` (labels `c` at
`δ`) and the mixed summands `F_b E_a N_{δ+b-a}`, `a ≠ b`. -/
def tgtIso : ((E Φ S i h₂ ≫ F Φ S i h₂).obj.obj N) δ ≅
    (⨁ tgtZ (i := i) N δ) ⊞ (⨁ tgtM h₂ N δ) :=
  isoOfDecomp₂ (ι := Fin (nLbl Φ i δ.1)) (κ := TgtMix h₂ δ) (Y := tgtZ (i := i) N δ)
    (Z := tgtM h₂ N δ) (sZ' h₂ N δ) (rZ' h₂ N δ) (sM' h₂ N δ) (rM' h₂ N δ) (sZ_rZ' h₂ N δ hzero)
    (fun _ _ h => sZ_rZ_ne' h₂ N δ h) (sM_rM' h₂ N δ) (fun _ _ h => sM_rM_ne' h₂ N δ h)
    (sZ_rM' h₂ N δ) (sM_rZ' h₂ N δ) (tgt_total h₂ N δ)

end Iso

end Furling

end Categorification.TwoRep
