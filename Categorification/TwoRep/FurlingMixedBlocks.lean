/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixedEntries

/-!
# Rectangular block decompositions for mixed words

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`; Brundan, arXiv:1501.00350v1, (1.6)–(1.7).

Decompose both mixed words for an arbitrary weight square, construct the
partial matching of their relevant paths, and prove the discarded summands
zero from cover mixed inversion and vanishing irrelevant edges.
-/

noncomputable section
namespace Categorification.TwoRep.Furling
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe wk v₁ u₁ u₂ u₃ u₄
variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
namespace MixedBlocks
variable {i j : I} {l m n t : X}
  (h₁ : l + RD.iX j = m) (h₂ : m + RD.iX i = t)
  (h₃ : l + RD.iX i = n) (h₄ : n + RD.iX j = t)
  (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (δ : Φ.Blk m)

abbrev Src : Type u₁ :=
  Σ p : {e : Φ.Edge j l // e.tgt h₁ = δ}, {q : Φ.Edge i l // q.src = p.1.src}

abbrev srcObj (x : Src (i := i) h₁ δ) : blkCat Φ S δ.1 :=
  (Ea Φ S h₁ x.1.1 δ x.1.2).obj ((incSrc Φ S x.2.1 x.1.1.src x.2.2).obj
    ((Fa Φ S h₃ x.2.1 (x.2.1.tgt h₃) rfl).obj (N (x.2.1.tgt h₃))))

def srcIn (x : Src (i := i) h₁ δ) : srcObj h₁ h₃ N δ x ⟶
    ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) δ :=
  (Ea Φ S h₁ x.1.1 δ x.1.2).map (incFq S h₃ N x.2) ≫
    genE Φ S j h₁ ((F Φ S i h₃).obj.obj N) x.1

def srcOut (x : Src (i := i) h₁ δ) : ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) δ ⟶
    srcObj h₁ h₃ N δ x :=
  projEb S h₁ ((F Φ S i h₃).obj.obj N) x.1 ≫
    (Ea Φ S h₁ x.1.1 δ x.1.2).map (projFq S h₃ N x.2)

omit [DecidableEq I] [DecidableEq J] in
theorem srcIn_srcOut (x : Src (i := i) h₁ δ) :
    srcIn h₁ h₃ N δ x ≫ srcOut h₁ h₃ N δ x = 𝟙 _ :=
  sr_id' _ _ _ _ _ (incFq_projFq S h₃ N _) (genE_projEb S h₁ _ _)

omit [DecidableEq I] in
theorem srcIn_srcOut_ne {x x' : Src (i := i) h₁ δ} (hx : x ≠ x') :
    srcIn h₁ h₃ N δ x ≫ srcOut h₁ h₃ N δ x' = 0 := by
  obtain ⟨p, q⟩ := x
  obtain ⟨p', q'⟩ := x'
  by_cases hp : p = p'
  · subst hp
    have hqq : q ≠ q' := fun h => hx (by subst h; rfl)
    exact sr_zero _ _ _ _ _ (genE_projEb S h₁ _ _) (incFq_projFq_ne S h₃ N hqq)
  · exact comp_zero_mid _ _ _ _ (genE_projEb_ne S h₁ _ hp)

omit [DecidableEq I] [DecidableEq J] in
theorem src_total : ∑ x, srcOut h₁ h₃ N δ x ≫ srcIn h₁ h₃ N δ x = 𝟙 _ := by
  classical
  exact total_two (Cp := fun p : {e : Φ.Edge j l // e.tgt h₁ = δ} => blkCat Φ S p.1.src.1)
    (Z := fun p => (F Φ S i h₃).obj.obj N p.1.src)
    (Q := fun p : {e : Φ.Edge j l // e.tgt h₁ = δ} => {q : Φ.Edge i l // q.src = p.1.src})
    (W := fun _ q => (incSrc Φ S q.1 _ q.2).obj
      ((Fa Φ S h₃ q.1 (q.1.tgt h₃) rfl).obj (N (q.1.tgt h₃))))
    (fun p => Ea Φ S h₁ p.1 δ p.2)
    (projEb S h₁ ((F Φ S i h₃).obj.obj N)) (genE Φ S j h₁ ((F Φ S i h₃).obj.obj N))
    (total_projE S h₁ _ δ) (fun _ q => projFq S h₃ N q) (fun _ q => incFq S h₃ N q)
    (fun p => total_projFq S h₃ N p.1.src)

def srcIso : ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) δ ≅ ⨁ srcObj h₁ h₃ N δ :=
  isoOfDecomp (srcIn h₁ h₃ N δ) (srcOut h₁ h₃ N δ) (srcIn_srcOut h₁ h₃ N δ)
    (fun _ _ h => srcIn_srcOut_ne h₁ h₃ N δ h) (src_total h₁ h₃ N δ)

abbrev Tgt : Type u₁ :=
  Σ r : {e : Φ.Edge i m // e.src = δ}, {s : Φ.Edge j n // s.tgt h₄ = r.1.tgt h₂}

abbrev tgtObj (y : Tgt h₂ h₄ δ) : blkCat Φ S δ.1 :=
  (incSrc Φ S y.1.1 δ y.1.2).obj ((Fa Φ S h₂ y.1.1 (y.1.1.tgt h₂) rfl).obj
    ((Ea Φ S h₄ y.2.1 (y.1.1.tgt h₂) y.2.2).obj (N y.2.1.src)))

def tgtIn (y : Tgt h₂ h₄ δ) : tgtObj h₂ h₄ N δ y ⟶
    ((E Φ S j h₄ ≫ F Φ S i h₂).obj.obj N) δ :=
  (incSrc Φ S y.1.1 δ y.1.2).map ((Fa Φ S h₂ y.1.1 (y.1.1.tgt h₂) rfl).map
    (genE Φ S j h₄ N y.2)) ≫ incFq S h₂ ((E Φ S j h₄).obj.obj N) y.1

def tgtOut (y : Tgt h₂ h₄ δ) : ((E Φ S j h₄ ≫ F Φ S i h₂).obj.obj N) δ ⟶
    tgtObj h₂ h₄ N δ y :=
  projFq S h₂ ((E Φ S j h₄).obj.obj N) y.1 ≫ (incSrc Φ S y.1.1 δ y.1.2).map
    ((Fa Φ S h₂ y.1.1 (y.1.1.tgt h₂) rfl).map (projEb S h₄ N y.2))

omit [DecidableEq I] [DecidableEq J] in
theorem tgtIn_tgtOut (y : Tgt h₂ h₄ δ) :
    tgtIn h₂ h₄ N δ y ≫ tgtOut h₂ h₄ N δ y = 𝟙 _ :=
  sr_id' _ _ _ _ _ (map_comp_eq_id _ (genE_projEb S h₄ _ _)) (incFq_projFq S h₂ _ _)

omit [DecidableEq I] in
theorem tgtIn_tgtOut_ne {y y' : Tgt h₂ h₄ δ} (hy : y ≠ y') :
    tgtIn h₂ h₄ N δ y ≫ tgtOut h₂ h₄ N δ y' = 0 := by
  obtain ⟨r, q⟩ := y
  obtain ⟨r', q'⟩ := y'
  by_cases hr : r = r'
  · subst hr
    have hqq : q ≠ q' := fun h => hy (by subst h; rfl)
    exact sr_zero _ _ _ _ _ (incFq_projFq S h₂ _ _)
      (map_comp_eq_zero _ (genE_projEb_ne S h₄ _ hqq))
  · exact comp_zero_mid _ _ _ _ (incFq_projFq_ne S h₂ _ hr)

omit [DecidableEq I] [DecidableEq J] in
theorem tgt_total : ∑ y, tgtOut h₂ h₄ N δ y ≫ tgtIn h₂ h₄ N δ y = 𝟙 _ := by
  classical
  exact total_two (Cp := fun r : {e : Φ.Edge i m // e.src = δ} => blkCat Φ S (r.1.tgt h₂).1)
    (Z := fun r => (E Φ S j h₄).obj.obj N (r.1.tgt h₂))
    (Q := fun r : {e : Φ.Edge i m // e.src = δ} => {s : Φ.Edge j n // s.tgt h₄ = r.1.tgt h₂})
    (W := fun r s => (Ea Φ S h₄ s.1 (r.1.tgt h₂) s.2).obj (N s.1.src))
    (fun r => (Fa Φ S h₂ r.1 (r.1.tgt h₂) rfl) ⋙ incSrc Φ S r.1 δ r.2)
    (projFq S h₂ ((E Φ S j h₄).obj.obj N)) (incFq S h₂ ((E Φ S j h₄).obj.obj N))
    (total_projFq S h₂ _ δ) (fun _ s => projEb S h₄ N s) (fun _ s => genE Φ S j h₄ N s)
    (fun r => total_projE S h₄ N (r.1.tgt h₂))

def tgtIso : ((E Φ S j h₄ ≫ F Φ S i h₂).obj.obj N) δ ≅ ⨁ tgtObj h₂ h₄ N δ :=
  isoOfDecomp (tgtIn h₂ h₄ N δ) (tgtOut h₂ h₄ N δ) (tgtIn_tgtOut h₂ h₄ N δ)
    (fun _ _ h => tgtIn_tgtOut_ne h₂ h₄ N δ h) (tgt_total h₂ h₄ N δ)

def liveSrc (x : Src (i := i) h₁ δ) : Prop :=
  Φ.rel δ.1 x.2.1.lbl ∧ Φ.rel (x.1.1.src.1 + Finsupp.single x.2.1.lbl 1) x.1.1.lbl

def liveTgt (y : Tgt h₂ h₄ δ) : Prop :=
  Φ.rel (δ.1 - Finsupp.single y.2.1.lbl 1) y.2.1.lbl ∧
    Φ.rel (δ.1 - Finsupp.single y.2.1.lbl 1) y.1.1.lbl

omit [DecidableEq I] [DecidableEq J] in
theorem rel_src (x : Src (i := i) h₁ δ) : Φ.rel x.1.1.src.1 x.2.1.lbl := by
  have h := x.2.1.rel_src
  rw [x.2.2] at h
  exact h

omit [DecidableEq I] [DecidableEq J] in
theorem swapped_tgt (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x) :
    (swapSnd Φ h₃ x.1.1 x.2.1.lbl x.2.1.π_lbl (rel_src h₁ δ x) hx.2).tgt h₄ =
      (outEdge δ x.2.1.lbl x.2.1.π_lbl hx.1).tgt h₂ := by
  apply Subtype.ext
  have e : x.1.1.src.1 + Finsupp.single x.1.1.lbl 1 = δ.1 := congrArg Subtype.val x.1.2
  show x.1.1.src.1 + Finsupp.single x.2.1.lbl 1 + Finsupp.single x.1.1.lbl 1 =
    δ.1 + Finsupp.single x.2.1.lbl 1
  rw [← e, add_right_comm]

def graphY (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x) : Tgt h₂ h₄ δ :=
  ⟨⟨outEdge δ x.2.1.lbl x.2.1.π_lbl hx.1, rfl⟩,
    ⟨swapSnd Φ h₃ x.1.1 x.2.1.lbl x.2.1.π_lbl (rel_src h₁ δ x) hx.2,
      swapped_tgt h₁ h₂ h₃ h₄ δ x hx⟩⟩

def graphX (y : Tgt h₂ h₄ δ) (hy : liveTgt h₂ h₄ δ y) : Src (i := i) h₁ δ :=
  ⟨⟨inEdge h₁ δ y.2.1.lbl y.2.1.π_lbl hy.1, inEdge_tgt h₁ δ _ _ hy.1⟩,
    ⟨⟨(blkSub h₁ δ y.2.1.lbl y.2.1.π_lbl, y.1.1.lbl), y.1.1.π_lbl, hy.2⟩, rfl⟩⟩

omit [DecidableEq I] [DecidableEq J] in
theorem graphY_eq (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x) (y : Tgt h₂ h₄ δ)
    (e₁ : y.1.1.lbl = x.2.1.lbl) (e₂ : y.2.1.lbl = x.1.1.lbl) :
    graphY h₁ h₂ h₃ h₄ δ x hx = y := by
  obtain ⟨r, s⟩ := y
  dsimp only at e₁ e₂
  have hr : (⟨outEdge δ x.2.1.lbl x.2.1.π_lbl hx.1, rfl⟩ :
      {e : Φ.Edge i m // e.src = δ}) = r :=
    Subtype.ext (Edge.ext r.2.symm e₁.symm)
  refine Sigma.subtype_ext hr ?_
  refine Edge.ext (Subtype.ext ?_) e₂.symm
  show x.1.1.src.1 + Finsupp.single x.2.1.lbl 1 = s.1.src.1
  have e₃ := Edge.src_eq_of_tgt h₄ s.1
  rw [s.2] at e₃
  rw [e₃, e₂, Edge.tgt_val, r.2, e₁, src_val_of_tgt h₁ x.1]
  abel

omit [DecidableEq I] [DecidableEq J] in
theorem graphX_eq (y : Tgt h₂ h₄ δ) (hy : liveTgt h₂ h₄ δ y) (x : Src (i := i) h₁ δ)
    (e₁ : x.1.1.lbl = y.2.1.lbl) (e₂ : x.2.1.lbl = y.1.1.lbl) :
    graphX h₁ h₂ h₄ δ y hy = x := by
  obtain ⟨p, q⟩ := x
  dsimp only at e₁ e₂
  have hp : (⟨inEdge h₁ δ y.2.1.lbl y.2.1.π_lbl hy.1, inEdge_tgt h₁ δ _ _ hy.1⟩ :
      {e : Φ.Edge j l // e.tgt h₁ = δ}) = p :=
    Subtype.ext ((inEdge_congr h₁ δ e₁.symm _ _ hy.1 (rel_of_tgt h₁ p)).trans (eq_inEdge h₁ p).symm)
  refine Sigma.subtype_ext hp ?_
  refine Edge.ext (Subtype.ext ?_) e₂.symm
  show δ.1 - Finsupp.single y.2.1.lbl 1 = q.1.src.1
  rw [q.2, src_val_of_tgt h₁ p, e₁]

omit [DecidableEq I] [DecidableEq J] in
theorem live_graphY (x : Src (i := i) h₁ δ) (hx : liveSrc h₁ δ x) :
    liveTgt h₂ h₄ δ (graphY h₁ h₂ h₃ h₄ δ x hx) := by
  refine ⟨rel_of_tgt h₁ x.1, ?_⟩
  have h := rel_src h₁ δ x
  rw [src_val_of_tgt h₁ x.1] at h
  exact h

omit [DecidableEq I] [DecidableEq J] in
theorem live_graphX (y : Tgt h₂ h₄ δ) (hy : liveTgt h₂ h₄ δ y) :
    liveSrc h₁ δ (graphX h₁ h₂ h₄ δ y hy) := by
  refine ⟨rel_of_src y.1, ?_⟩
  have e : y.2.1.src.1 = δ.1 - Finsupp.single y.2.1.lbl 1 + Finsupp.single y.1.1.lbl 1 := by
    rw [Edge.src_eq_of_tgt h₄ y.2.1, y.2.2, Edge.tgt_val, y.1.2]
    abel
  have h := y.2.1.rel_src
  rw [e] at h
  exact h

def graphEquiv : {x // liveSrc (i := i) h₁ δ x} ≃ {y // liveTgt h₂ h₄ δ y} where
  toFun x := ⟨graphY h₁ h₂ h₃ h₄ δ x.1 x.2, live_graphY h₁ h₂ h₃ h₄ δ x.1 x.2⟩
  invFun y := ⟨graphX h₁ h₂ h₄ δ y.1 y.2, live_graphX h₁ h₂ h₄ δ y.1 y.2⟩
  left_inv x := Subtype.ext (graphX_eq h₁ h₂ h₄ δ (graphY h₁ h₂ h₃ h₄ δ x.1 x.2)
    (live_graphY h₁ h₂ h₃ h₄ δ x.1 x.2) x.1 rfl rfl)
  right_inv y := Subtype.ext (graphY_eq h₁ h₂ h₃ h₄ δ (graphX h₁ h₂ h₄ δ y.1 y.2)
    (live_graphX h₁ h₂ h₄ δ y.1 y.2) y.1 rfl rfl)

variable (hcover : BrundanMixedInversion S)
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

include hcover hzero in
omit [DecidableEq I] [DecidableEq J] [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
theorem isZero_src (hij : i ≠ j) (x : Src (i := i) h₁ δ) (hx : ¬ liveSrc h₁ δ x) :
    IsZero (srcObj h₁ h₃ N δ x) := by
  obtain ⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  have hab : p.lbl ≠ b := fun e => hij (hb.symm.trans ((congrArg Φ.π e).symm.trans p.π_lbl))
  have e₄ : Φ.wtT (p.src.1 + Finsupp.single b 1) + RDc.iX p.lbl =
      Φ.wtT ((p.tgt h₁).1 + Finsupp.single b 1) := by
    rw [Φ.wtT_add_single, Edge.tgt_val, add_right_comm]
  apply mixed_source_zero_of_dropped S hcover hab (wt_tgt h₁ p rfl)
    (Φ.wtT_add_single (p.tgt h₁).1 b)
    (wt_tgt h₃ (swapFst Φ p b hb hrb) rfl) e₄
  rcases not_and_or.mp hx with h | h
  · exact Or.inl (hzero _ b _ h)
  · exact Or.inr (hzero _ _ e₄ h)

include hcover hzero in
omit [DecidableEq I] [DecidableEq J] [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
theorem isZero_tgt (hij : i ≠ j) (y : Tgt h₂ h₄ δ) (hy : ¬ liveTgt h₂ h₄ δ y) :
    IsZero (tgtObj h₂ h₄ N δ y) := by
  obtain ⟨⟨⟨⟨rs, c⟩, hc, hrc⟩, hr⟩, ⟨s, hs⟩⟩ := y
  change rs = δ at hr
  subst rs
  have hab : s.lbl ≠ c := fun e => hij (hc.symm.trans ((congrArg Φ.π e).symm.trans s.π_lbl))
  have e₃ : Φ.wtT (δ.1 - Finsupp.single s.lbl 1) + RDc.iX c = Φ.wtT s.src.1 := by
    rw [Φ.wtT_add_single, Edge.src_eq_of_tgt h₄ s, hs]
    congr 1
    show _ = δ.1 + Finsupp.single c 1 - Finsupp.single s.lbl 1
    abel
  apply mixed_target_zero_of_dropped S hcover hab (wtT_sub_add δ.1 s.lbl)
    (wt_tgt h₂ ⟨(δ, c), hc, hrc⟩ rfl) e₃ (wt_tgt h₄ s hs)
  rcases not_and_or.mp hy with h | h
  · exact Or.inl (hzero _ _ (wtT_sub_add δ.1 s.lbl) h)
  · exact Or.inr (hzero _ _ e₃ h)

end MixedBlocks
end Categorification.TwoRep.Furling
