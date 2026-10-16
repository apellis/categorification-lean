/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingBlock
import Categorification.TwoRep.FurlingSigma

/-!
# The mixed blocks of Rouquier's maps for the furled action

For the furled action `g` of a Rouquier family `g̃` (Webster, arXiv:1603.06311v3, §2.3, Lemma
with label `lem:g-action`), we compute the entries of the rightward crossing
`σ : F_i E_i 1_λ ⟶ E_i F_i 1_λ` (J. Brundan, arXiv:1501.00350v1, (1.6)) and of the other
components of Rouquier's maps (Brundan, (1.8), (1.9)) that involve the *mixed* summands
`E_a F_b` and `F_b E_a` (`a ≠ b` labels over `i`) of the decompositions `srcIso`, `tgtIso` of a
block `δ`:

* `sM_sigma_rZ'`: `σ` maps the mixed summands `E_a F_b` to zero in the shift-zero summands
  `F_c E_c`;
* `sZ_sigma_rM'`: `σ` maps the shift-zero summands `E_a F_a` to zero in the mixed summands;
* `isIso_mixed`: the block of `σ` between the mixed summands is invertible, given that the mixed
  sideways crossings of the cover are invertible (hypothesis `hmix`) and that the 1-morphisms of
  irrelevant edges vanish (hypothesis `hzero`). The matrix is monomial: `E_a F_b` (edges
  `p : δ - a →a→ δ`, `q : δ - a →b→`) goes to `F_b E_a` (edges `δ →b→ δ + b`,
  `δ - a + b →a→ δ + b`), and its entry is the sideways crossing of `g̃`.
* `sM_pow_counit`, `unit_pow_rM'`: the dotted caps `F_i ◁ yⁿ ≫ ε` and cups `η ≫ yⁿ ▷ F_i` of
  Rouquier's maps (Brundan, (1.8), (1.9)) vanish on the mixed summands.

The hypothesis `hmix` asks that for labels `a ≠ b` of one colour the composite
`E_a F_b ⟶ F_b E_b E_a F_b ⟶ F_b E_a E_b F_b ⟶ F_b E_a` (unit of `E_b ⊣ F_b`, the
swapped-path component `swapCell` of the crossing of `g`, counit of `E_b ⊣ F_b`) is invertible.
This is the invertibility of the mixed sideways crossings in Brundan's definition of the
Kac–Moody 2-category (Brundan, arXiv:1501.00350v1, Definition 1.1, for distinct colours of
`g̃`); `swapCell` is the crossing of `g̃` followed by the unit `-(ϖ_a(y_L) - ϖ_b(y_R))⁻¹`, so this
is to be discharged from the corresponding statement for the cover (`KLR.Unfurling`, mixed
inversion). Here it is an explicit hypothesis about the cover `S̃` only.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe wk v₁ u₁ u₂ u₃ u₄

namespace Furling

/-! ## Composition helpers -/

section Helpers

variable {C' D' : Type*} [Category C'] [Category D']

theorem chain_swap_id (K : C' ⥤ D') {A B B' : D'}
    {V V₁ V₂ W : C'} (a : A ⟶ B) (s : B ⟶ B') (pr : B' ⟶ K.obj W) (u : A ⟶ K.obj V)
    (X₁ : V ⟶ V₁) (X₂ : V₁ ⟶ V₂) (g : V₂ ⟶ W) (π : W ⟶ V₂)
    (h : a ≫ s ≫ pr = u ≫ K.map (X₁ ≫ X₂ ≫ g)) (hg : g ≫ π = 𝟙 _) :
    a ≫ s ≫ (pr ≫ K.map π) = u ≫ K.map (X₁ ≫ X₂) := by
  rw [← Category.assoc s, ← Category.assoc a, ← Category.assoc a, Category.assoc a, h,
    Category.assoc, ← K.map_comp, Category.assoc, Category.assoc, hg, Category.comp_id]

theorem map_id_comp_chain (K : C' ⥤ D') {U V : C'} {Z T : D'} (i : U ⟶ U) (f : U ⟶ V)
    (g : K.obj V ⟶ Z) (t : Z ⟶ T) (hi : i = 𝟙 U) :
    (K.map (i ≫ f) ≫ g) ≫ t = (K.map f ≫ g) ≫ t := by
  rw [hi, Category.id_comp]

theorem comp_comp_step {A B : D'} (g : A ⟶ B) (a b : B ⟶ B) (φ ψ : A ⟶ A)
    (h₁ : g ≫ a = φ ≫ g) (h₂ : g ≫ b = ψ ≫ g) : g ≫ (a ≫ b) = (φ ≫ ψ) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

theorem isIso_of_eq_hom {X' Y' : D'} {f g : X' ⟶ Y'} (h : f = g) (hg : IsIso g) : IsIso f :=
  h ▸ hg

theorem isZero_src_of_isIso {X' Y' : D'} (f : X' ⟶ Y') (hf : IsIso f) (h : IsZero Y') :
    IsZero X' := by
  have := hf; exact h.of_iso (asIso f)

theorem isZero_tgt_of_isIso {X' Y' : D'} (f : X' ⟶ Y') (hf : IsIso f) (h : IsZero X') :
    IsZero Y' := by
  have := hf; exact h.of_iso (asIso f).symm

variable [Preadditive C'] [Preadditive D']

theorem chain_zero {A B B' Q R : D'} (a : A ⟶ B) (s : B ⟶ B') (pr : B' ⟶ Q) (m : Q ⟶ R)
    (h : a ≫ s ≫ pr = 0) : a ≫ s ≫ (pr ≫ m) = 0 := by
  rw [← Category.assoc s, ← Category.assoc a, ← Category.assoc a, Category.assoc a, h,
    zero_comp]

theorem chain_swap_zero (K : C' ⥤ D') [K.PreservesZeroMorphisms] {A B B' : D'}
    {V V₁ V₂ W W' : C'} (a : A ⟶ B) (s : B ⟶ B') (pr : B' ⟶ K.obj W) (u : A ⟶ K.obj V)
    (X₁ : V ⟶ V₁) (X₂ : V₁ ⟶ V₂) (g : V₂ ⟶ W) (π : W ⟶ W')
    (h : a ≫ s ≫ pr = u ≫ K.map (X₁ ≫ X₂ ≫ g)) (hg : g ≫ π = 0) :
    a ≫ s ≫ (pr ≫ K.map π) = 0 := by
  rw [← Category.assoc s, ← Category.assoc a, ← Category.assoc a, Category.assoc a, h,
    Category.assoc, ← K.map_comp, Category.assoc, Category.assoc, hg, comp_zero, comp_zero,
    K.map_zero, comp_zero]

theorem counit_chain_zero (K : C' ⥤ D') [K.PreservesZeroMorphisms] {Y₀ Y₁ Y₂ : C'}
    {Z T : D'} (i : Y₀ ⟶ Y₁) (g : K.obj Y₁ ⟶ Z) (θ : Z ⟶ Z) (eps : Z ⟶ T) (φ : K ⟶ K)
    (pr : Y₁ ⟶ Y₂) (c : K.obj Y₂ ⟶ T) (hg : g ≫ θ = φ.app Y₁ ≫ g)
    (hc : g ≫ eps = K.map pr ≫ c) (hz : i ≫ pr = 0) : (K.map i ≫ g) ≫ (θ ≫ eps) = 0 := by
  rw [Category.assoc, ← Category.assoc g, hg, Category.assoc, hc, ← Category.assoc,
    φ.naturality, Category.assoc, ← K.map_comp_assoc, hz, K.map_zero, zero_comp, comp_zero]

theorem unit_chain_zero (K : C' ⥤ D') [K.PreservesZeroMorphisms] {A B : D'} {V W W' : C'}
    (u : A ⟶ B) (t : B ⟶ B) (pr : B ⟶ K.obj W) (u' : A ⟶ K.obj V) (g : V ⟶ W) (θ : W ⟶ W)
    (φ : V ⟶ V) (m : W ⟶ W') (hn : t ≫ pr = pr ≫ K.map θ) (hu : u ≫ pr = u' ≫ K.map g)
    (hg : g ≫ θ = φ ≫ g) (hz : g ≫ m = 0) : (u ≫ t) ≫ (pr ≫ K.map m) = 0 := by
  rw [Category.assoc, ← Category.assoc t, hn, Category.assoc, ← Category.assoc u, hu,
    Category.assoc, ← K.map_comp, ← K.map_comp, ← Category.assoc, hg, Category.assoc, hz,
    comp_zero, K.map_zero, comp_zero]

end Helpers

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc} {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  {S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc}
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

/-! ## The dots on generators -/

section Dots

omit [DecidableEq I] [DecidableEq J] in
/-- The powers of the dot of `g` on the summand of an edge of label `a` are the powers of
`ϖ_a(y)`. -/
theorem genE_powComp_dot (ϖ : J → Polynomial k) (i : I) {m m' : X} (h : m + RD.iX i = m')
    (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) {γ : Φ.Blk m'} (p : {e : Φ.Edge i m // e.tgt h = γ})
    (n : ℕ) :
    genE Φ S i h M p ≫ (powComp (dot Φ S ϖ i h) n).hom.app M γ =
      (powComp (dotA Φ S ϖ h p.1 γ p.2) n).app (M p.1.src) ≫ genE Φ S i h M p := by
  induction n with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih => exact comp_comp_step _ _ _ _ _ ih (genE_dot Φ S ϖ i h M p)

omit [DecidableEq I] [DecidableEq J] [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
/-- A right adjoint of a zero 1-morphism of `g̃` is zero. -/
theorem isZero_F_of_isZero_E {a : J} {x y : Xc} (h : x + RDc.iX a = y) (hz : IsZero (S.E a h))
    (M : (S.obj y : Type u₂)) : IsZero ((S.F a h).obj.obj M) := by
  have hEF : IsZero ((S.E a h).obj.obj ((S.F a h).obj.obj M)) :=
    Functor.map_isZero (LinearCat.evalAt _) hz
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  rw [← (LinearCat.toAdjunction (S.adj a h)).right_triangle_components M,
    hEF.eq_of_src ((LinearCat.toAdjunction (S.adj a h)).counit.app M) 0,
    Functor.map_zero, comp_zero]

end Dots

variable {i : I} {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')
  (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1)

/-! ## `σ` on the summands, in terms of edges -/

section Core

variable (p : Φ.Edge i l)

/-- `σ` of `g` on a mixed summand `E_a F_b`, projected to a summand `F_c E_d` with `c ≠ b` or
`d ≠ a`, vanishes. -/
theorem genFE_sigma_zero_of (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (hab : b ≠ p.lbl)
    (c : J) (hc : Φ.π c = i) (hrc : Φ.rel (p.tgt h₁).1 c)
    (s : {e : Φ.Edge i l' // e.tgt h₂ = (Edge.next h₁ p c hc hrc).tgt h₂})
    (hs : c = b → s.1.lbl ≠ p.lbl) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hrc) ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hrc) _ rfl).map (projEb S h₂ N s)) = 0 := by
  by_cases hcb : c = b
  · subst hcb
    by_cases hsw : Φ.rel (p.src.1 + Finsupp.single c 1) p.lbl
    · exact chain_swap_zero _ _ _ _ _ _ _ _ _
        (genFE_sigma_projF_swap Φ S D h₁ h₂ N p c hb hrb hrc hsw)
        (genE_projEb_ne S h₂ N fun h => hs rfl (congrArg (fun e => e.1.lbl) h).symm)
    · exact chain_zero _ _ _ _
        (genFE_sigma_projF_swap_of_not_rel Φ S D h₁ h₂ N p c hb hrb hrc hsw)
  · exact chain_zero _ _ _ _
      (genFE_sigma_projF_zero Φ S D h₁ h₂ N p b hb hrb c hc hrc (Ne.symm hcb) hab)

/-- `σ` of `g` on a shift-zero summand `E_a F_a`, projected to a mixed summand `F_c E_d`
(`d ≠ c`), vanishes. -/
theorem genFE_self_sigma_zero (c : J) (hc : Φ.π c = i) (hrc : Φ.rel (p.tgt h₁).1 c)
    (s : {e : Φ.Edge i l' // e.tgt h₂ = (Edge.next h₁ p c hc hrc).tgt h₂})
    (hs : s.1.lbl ≠ c) :
    genFE Φ S h₁ N p p.lbl p.π_lbl p.rel_src ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hrc) ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hrc) _ rfl).map (projEb S h₂ N s)) = 0 := by
  by_cases hac : p.lbl = c
  · subst hac
    exact chain_swap_zero _ _ _ _ _ _ _ _ _
      (genFE_sigma_projF_swap Φ S D h₁ h₂ N p p.lbl p.π_lbl p.rel_src hrc hrc)
      (genE_projEb_ne S h₂ N fun h => hs (congrArg (fun e => e.1.lbl) h).symm)
  · exact chain_swap_zero _ _ _ _ _ _ _ _ _
      (genFE_sigma_projF_self Φ S D h₁ h₂ N p c hc hrc hac)
      (genE_projEb_ne S h₂ N fun h => hs (congrArg (fun e => e.1.lbl) h).symm)

end Core

/-! ## The blocks of `σ` involving mixed summands -/

section Blocks

variable (δ : Φ.Blk l')

omit [DecidableEq I] [DecidableEq J] in
theorem rel_srcMix (x : SrcMix h₁ δ) : Φ.rel x.1.1.1.src.1 x.1.2.1.lbl := by
  have := x.1.2.1.rel_src; rwa [x.1.2.2] at this

/-- `σ` of `g` on a mixed summand `E_a F_b`, projected to `F_c E_d` with `c ≠ b` or `d ≠ a`,
vanishes. -/
theorem sM_sigma_zero (x : SrcMix h₁ δ) (r : {e : Φ.Edge i l' // e.src = δ})
    (s : {e : Φ.Edge i l' // e.tgt h₂ = r.1.tgt h₂})
    (hs : r.1.lbl = x.1.2.1.lbl → s.1.lbl ≠ x.1.1.1.lbl) :
    sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      (projFq S h₂ ((E Φ S i h₂).obj.obj N) r ≫
        (incSrc Φ S r.1 δ r.2).map ((Fa Φ S h₂ r.1 (r.1.tgt h₂) rfl).map (projEb S h₂ N s))) =
      0 := by
  obtain ⟨⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩, hne⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  obtain ⟨⟨⟨rs, c⟩, hc, hrc⟩, hr⟩ := r
  change rs = p.tgt h₁ at hr
  subst rs
  exact genFE_sigma_zero_of D h₁ h₂ N p b hb hrb hne c hc hrc s hs

/-- **Mixed to shift-zero**: `σ` of `g` maps the mixed summands `E_a F_b` (`a ≠ b`) to zero in the
shift-zero summands `F_c E_c` of a block. -/
theorem sM_sigma_rZ' (x : SrcMix h₁ δ) (t : Fin (nLbl Φ i δ.1)) :
    sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rZ' h₂ N δ t = 0 := by
  by_cases hr : Φ.rel δ.1 (lab Φ i δ.1 t)
  · simp only [rZ', hr, ↓reduceDIte]
    exact sM_sigma_zero D h₁ h₂ N δ x (rOut δ t hr) ⟨(rOut δ t hr).1, rfl⟩
      fun h h' => x.2 (h.symm.trans h')
  · simp only [rZ', hr, ↓reduceDIte, Limits.comp_zero]

/-- The self summand of an edge into `δ`, followed by `σ`, vanishes on the mixed summands. -/
theorem self_sigma_rM' (p : {e : Φ.Edge i l // e.tgt h₁ = δ}) (y : TgtMix h₂ δ) :
    ((Ea Φ S h₁ p.1 δ p.2).map ((trF S h₁ N p.1 p.2).hom ≫ incF Φ S h₁ N p.1) ≫
      genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) p) ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫
      rM' h₂ N δ y = 0 := by
  obtain ⟨p, hp⟩ := p
  subst hp
  obtain ⟨⟨⟨⟨⟨rs, c⟩, hc, hrc⟩, hr⟩, s⟩, hne⟩ := y
  change rs = p.tgt h₁ at hr
  subst rs
  refine (map_id_comp_chain _ (trF S h₁ N p rfl).hom _ _ _ rfl).trans ?_
  exact genFE_self_sigma_zero D h₁ h₂ N p c hc hrc s hne

/-- **Shift-zero to mixed**: `σ` of `g` maps the shift-zero summands `E_a F_a` to zero in the mixed
summands `F_c E_d` (`c ≠ d`) of a block. -/
theorem sZ_sigma_rM' (t : Fin (nLbl Φ i δ.1)) (y : TgtMix h₂ δ) :
    sZ h₁ N δ t ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rM' h₂ N δ y = 0 := by
  by_cases hr : Φ.rel (δ.1 - Finsupp.single (lab Φ i δ.1 t) 1) (lab Φ i δ.1 t)
  · simp only [sZ, hr, ↓reduceDIte]
    exact self_sigma_rM' D h₁ h₂ N δ (pIn h₁ δ t hr) y
  · simp only [sZ, hr, ↓reduceDIte, Limits.zero_comp]

end Blocks

/-! ## Caps and cups on the mixed summands -/

section CapsCups

variable (δ : Φ.Blk l')

omit [DecidableEq I] [DecidableEq J] in
theorem whisker_counit_app {m m' : X} (h : m + RD.iX i = m')
    (M : ∀ γ : Φ.Blk m', blkCat Φ S γ.1) (γ : Φ.Blk m') (θ : E Φ S i h ⟶ E Φ S i h) :
    (F Φ S i h ◁ θ ≫ (adj Φ S i h).counit).hom.app M γ =
      θ.hom.app ((F Φ S i h).obj.obj M) γ ≫ (adj Φ S i h).counit.hom.app M γ :=
  rfl

omit [DecidableEq I] [DecidableEq J] in
theorem unit_whisker_app {m m' : X} (h : m + RD.iX i = m')
    (M : ∀ β : Φ.Blk m, blkCat Φ S β.1) (β : Φ.Blk m) (θ : E Φ S i h ⟶ E Φ S i h) :
    ((adj Φ S i h).unit ≫ θ ▷ F Φ S i h).hom.app M β =
      (adj Φ S i h).unit.hom.app M β ≫ (F Φ S i h).obj.map (θ.hom.app M) β :=
  rfl

/-- **Caps on mixed summands**: the dotted caps `F_i ◁ yⁿ ≫ ε` of Rouquier's map vanish on the mixed
summands `E_a F_b` (`a ≠ b`). -/
theorem sM_pow_counit (x : SrcMix h₁ δ) (n : ℕ) :
    sM h₁ N δ x ≫ (F Φ S i h₁ ◁ powComp ((rouqData Φ S D).dot i h₁) n ≫
      (adj Φ S i h₁).counit).hom.app N δ = 0 := by
  rw [whisker_counit_app]
  obtain ⟨⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩, hne⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  exact counit_chain_zero _ _ _ _ _ _ _ _
    (genE_powComp_dot D.pw i h₁ ((F Φ S i h₁).obj.obj N) ⟨p, rfl⟩ n)
    (genE_counit Φ S i h₁ N p)
    (incFq_projFq_ne S h₁ N (q := ⟨sameSrc Φ p b hb hrb, rfl⟩) (q' := ⟨p, rfl⟩)
      fun h => hne (congrArg (fun e => e.1.lbl) h))

/-- **Cups on mixed summands**: the dotted cups `η ≫ yⁿ ▷ F_i` of Rouquier's map vanish on the mixed
summands `F_c E_d` (`c ≠ d`). -/
theorem unit_pow_rM' (y : TgtMix h₂ δ) (n : ℕ) :
    ((adj Φ S i h₂).unit ≫ powComp ((rouqData Φ S D).dot i h₂) n ▷ F Φ S i h₂).hom.app N δ ≫
      rM' h₂ N δ y = 0 := by
  rw [unit_whisker_app]
  obtain ⟨⟨⟨r, hr⟩, s⟩, hne⟩ := y
  subst hr
  exact unit_chain_zero (Fa Φ S h₂ r _ rfl) _ _ _ _ _ _ _ _
    (projF_natural Φ S h₂ ((powComp ((rouqData Φ S D).dot i h₂) n).hom.app N) r)
    (unit_projF Φ S i h₂ N r)
    (genE_powComp_dot D.pw i h₂ N ⟨r, rfl⟩ n)
    (genE_projEb_ne S h₂ N fun h => hne (congrArg (fun e => e.1.lbl) h).symm)

end CapsCups

/-! ## The mixed block of `σ` -/

section Monomial

/-- `σ` of `g` on `E_a F_b` projected to `F_b E_a` along the swapped path: the sideways
crossing of `swapCell` (unit and counit of `E_b ⊣ F_b`). -/
theorem genFE_sigma_swap_entry (p : Φ.Edge i l) (b : J) (hb : Φ.π b = i)
    (hrb : Φ.rel p.src.1 b) (hr : Φ.rel (p.tgt h₁).1 b)
    (hs : Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
      (projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p b hb hr) ≫
        (Fa Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map (projEb S h₂ N
          ⟨swapSnd Φ h₁ p b hb hrb hs, swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl⟩)) =
      (adjA Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
          ((swapCell S D (i = i) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hr) rfl)
              (wt_tgt h₁ (swapFst Φ p b hb hrb) rfl)
              (wt_tgt h₂ (swapSnd Φ h₁ p b hb hrb hs)
                (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl))).hom.app
              ((Fa Φ S h₁ (sameSrc Φ p b hb hrb) _ rfl).obj (N ((sameSrc Φ p b hb hrb).tgt h₁))) ≫
            (Ea Φ S h₂ (swapSnd Φ h₁ p b hb hrb hs) _
                (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl)).map
              ((adjA Φ S h₁ (sameSrc Φ p b hb hrb) _ rfl).counit.app
                (N ((sameSrc Φ p b hb hrb).tgt h₁)))) :=
  chain_swap_id _ _ _ _ _ _ _ _ _ (genFE_sigma_projF_swap Φ S D h₁ h₂ N p b hb hrb hr hs)
    (genE_projEb S h₂ N _)

variable (δ : Φ.Blk l')

variable (Φ) in
/-- The mixed summands `E_a F_b` (edges `p : δ - a →a→ δ`, `q : δ - a →b→`) on the graph of
the mixed block: the swapped path `δ - a →b→ →a→ δ + b` is relevant. -/
def PMix (x : SrcMix h₁ δ) : Prop :=
  Φ.rel δ.1 x.1.2.1.lbl ∧ Φ.rel (x.1.1.1.src.1 + Finsupp.single x.1.2.1.lbl 1) x.1.1.1.lbl

variable (Φ) in
/-- The mixed summands `F_c E_d` (edges `r : δ →c→`, `s : →d→ δ + c`) on the graph of the
mixed block: the swapped path `δ - d →c→ →d→ δ + c` is relevant at its first edges. -/
def QMix (y : TgtMix h₂ δ) : Prop :=
  Φ.rel (δ.1 - Finsupp.single y.1.2.1.lbl 1) y.1.2.1.lbl ∧
    Φ.rel (δ.1 - Finsupp.single y.1.2.1.lbl 1) y.1.1.1.lbl

omit [DecidableEq I] [DecidableEq J] in
theorem swapSnd_tgt_mix (x : SrcMix h₁ δ) (hx : PMix Φ h₁ δ x) :
    (swapSnd Φ h₁ x.1.1.1 x.1.2.1.lbl x.1.2.1.π_lbl (rel_srcMix h₁ δ x) hx.2).tgt h₂ =
      (outEdge δ x.1.2.1.lbl x.1.2.1.π_lbl hx.1).tgt h₂ := by
  apply Subtype.ext
  have e : x.1.1.1.src.1 + Finsupp.single x.1.1.1.lbl 1 = δ.1 := congrArg Subtype.val x.1.1.2
  show x.1.1.1.src.1 + Finsupp.single x.1.2.1.lbl 1 + Finsupp.single x.1.1.1.lbl 1 =
    δ.1 + Finsupp.single x.1.2.1.lbl 1
  rw [← e, add_right_comm]

/-- The mixed summand `F_b E_a` (edges `δ →b→ δ + b`, `δ - a + b →a→ δ + b`) matched with
`E_a F_b` by the mixed block of `σ`. -/
def graphY (x : SrcMix h₁ δ) (hx : PMix Φ h₁ δ x) : TgtMix h₂ δ :=
  ⟨⟨⟨outEdge δ x.1.2.1.lbl x.1.2.1.π_lbl hx.1, rfl⟩,
    ⟨swapSnd Φ h₁ x.1.1.1 x.1.2.1.lbl x.1.2.1.π_lbl (rel_srcMix h₁ δ x) hx.2,
      swapSnd_tgt_mix h₁ h₂ δ x hx⟩⟩, x.2.symm⟩

/-- The mixed summand `E_d F_c` (edges `δ - d →d→ δ`, `δ - d →c→`) matched with `F_c E_d`. -/
def graphX (y : TgtMix h₂ δ) (hy : QMix Φ h₂ δ y) : SrcMix h₁ δ :=
  ⟨⟨⟨inEdge h₁ δ y.1.2.1.lbl y.1.2.1.π_lbl hy.1, inEdge_tgt h₁ δ _ _ hy.1⟩,
    ⟨⟨(blkSub h₁ δ y.1.2.1.lbl y.1.2.1.π_lbl, y.1.1.1.lbl), y.1.1.1.π_lbl, hy.2⟩, rfl⟩⟩,
    y.2.symm⟩

omit [DecidableEq I] [DecidableEq J] in
theorem graphY_eq (x : SrcMix h₁ δ) (hx : PMix Φ h₁ δ x) (y : TgtMix h₂ δ)
    (e₁ : y.1.1.1.lbl = x.1.2.1.lbl) (e₂ : y.1.2.1.lbl = x.1.1.1.lbl) :
    graphY h₁ h₂ δ x hx = y := by
  obtain ⟨⟨r, s⟩, hy⟩ := y
  dsimp only at e₁ e₂
  have hr : (⟨outEdge δ x.1.2.1.lbl x.1.2.1.π_lbl hx.1, rfl⟩ :
      {e : Φ.Edge i l' // e.src = δ}) = r :=
    Subtype.ext (Edge.ext r.2.symm e₁.symm)
  refine Subtype.ext (Sigma.subtype_ext hr ?_)
  refine Edge.ext (Subtype.ext ?_) e₂.symm
  show x.1.1.1.src.1 + Finsupp.single x.1.2.1.lbl 1 = s.1.src.1
  have e₃ := Edge.src_eq_of_tgt h₂ s.1
  rw [s.2] at e₃
  rw [e₃, e₂, Edge.tgt_val, r.2, e₁, src_val_of_tgt h₁ x.1.1]
  abel

omit [DecidableEq I] [DecidableEq J] in
theorem graphX_eq (y : TgtMix h₂ δ) (hy : QMix Φ h₂ δ y) (x : SrcMix h₁ δ)
    (e₁ : x.1.1.1.lbl = y.1.2.1.lbl) (e₂ : x.1.2.1.lbl = y.1.1.1.lbl) :
    graphX h₁ h₂ δ y hy = x := by
  obtain ⟨⟨p, q⟩, hx⟩ := x
  dsimp only at e₁ e₂
  have hp : (⟨inEdge h₁ δ y.1.2.1.lbl y.1.2.1.π_lbl hy.1, inEdge_tgt h₁ δ _ _ hy.1⟩ :
      {e : Φ.Edge i l // e.tgt h₁ = δ}) = p :=
    Subtype.ext ((inEdge_congr h₁ δ e₁.symm _ _ hy.1 (rel_of_tgt h₁ p)).trans (eq_inEdge h₁ p).symm)
  refine Subtype.ext (Sigma.subtype_ext hp ?_)
  refine Edge.ext (Subtype.ext ?_) e₂.symm
  show δ.1 - Finsupp.single y.1.2.1.lbl 1 = q.1.src.1
  rw [q.2, src_val_of_tgt h₁ p, e₁]

omit [DecidableEq I] [DecidableEq J] in
theorem qMix_graphY (x : SrcMix h₁ δ) (hx : PMix Φ h₁ δ x) :
    QMix Φ h₂ δ (graphY h₁ h₂ δ x hx) := by
  refine ⟨rel_of_tgt h₁ x.1.1, ?_⟩
  have := rel_srcMix h₁ δ x
  rw [src_val_of_tgt h₁ x.1.1] at this
  exact this

omit [DecidableEq I] [DecidableEq J] in
theorem pMix_graphX (y : TgtMix h₂ δ) (hy : QMix Φ h₂ δ y) :
    PMix Φ h₁ δ (graphX h₁ h₂ δ y hy) := by
  refine ⟨rel_of_src y.1.1, ?_⟩
  have e : y.1.2.1.src.1 =
      δ.1 - Finsupp.single y.1.2.1.lbl 1 + Finsupp.single y.1.1.1.lbl 1 := by
    rw [Edge.src_eq_of_tgt h₂ y.1.2.1, y.1.2.2, Edge.tgt_val, y.1.1.2]
    abel
  have := y.1.2.1.rel_src
  rw [e] at this
  exact this

/-- **The graph of the mixed block**: `E_a F_b ↦ F_b E_a`. -/
def graphEquiv : {x // PMix Φ h₁ δ x} ≃ {y // QMix Φ h₂ δ y} where
  toFun x := ⟨graphY h₁ h₂ δ x.1 x.2, qMix_graphY h₁ h₂ δ x.1 x.2⟩
  invFun y := ⟨graphX h₁ h₂ δ y.1 y.2, pMix_graphX h₁ h₂ δ y.1 y.2⟩
  left_inv x := Subtype.ext (graphX_eq h₁ h₂ δ (graphY h₁ h₂ δ x.1 x.2)
    (qMix_graphY h₁ h₂ δ x.1 x.2) x.1 rfl rfl)
  right_inv y := Subtype.ext (graphY_eq h₁ h₂ δ (graphX h₁ h₂ δ y.1 y.2)
    (pMix_graphX h₁ h₂ δ y.1 y.2) y.1 rfl rfl)

variable (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))
  (hmix : ∀ (j : I) (a b : J), a ≠ b → Φ.π a = j → Φ.π b = j → ∀ {x y y' z : Xc}
    (e₁ : x + RDc.iX a = y) (e₂ : y + RDc.iX b = z) (e₃ : x + RDc.iX b = y')
    (e₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type u₂)),
    IsIso ((S.adj b e₂).unit.hom.app ((S.E a e₁).obj.obj ((S.F b e₃).obj.obj M)) ≫
      (S.F b e₂).obj.map ((swapCell S D (j = j) e₁ e₂ e₃ e₄).hom.app ((S.F b e₃).obj.obj M) ≫
        (S.E a e₄).obj.map ((S.adj b e₃).counit.hom.app M))))

include hmix in
/-- The entries of the mixed block of `σ` on its graph are invertible. -/
theorem isIso_entry (x : SrcMix h₁ δ) (hx : PMix Φ h₁ δ x) :
    IsIso (sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rM' h₂ N δ (graphY h₁ h₂ δ x hx)) := by
  obtain ⟨⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩, hne⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  exact isIso_of_eq_hom (genFE_sigma_swap_entry D h₁ h₂ N p b hb hrb hx.1 hx.2)
    (hmix i p.lbl b (Ne.symm hne) p.π_lbl hb (wt_tgt h₁ p rfl)
      (wt_tgt h₂ (Edge.next h₁ p b hb hx.1) rfl) (wt_tgt h₁ (swapFst Φ p b hb hrb) rfl)
      (wt_tgt h₂ (swapSnd Φ h₁ p b hb hrb hx.2)
        (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hx.1 hrb hx.2 rfl))
      (N ((sameSrc Φ p b hb hrb).tgt h₁)))

include hzero hmix in
omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
/-- A mixed summand `E_a F_b` off the graph is zero: it is isomorphic to `F_b E_a`, which
contains `E_a` or `F_b` of an irrelevant edge. -/
theorem isZero_srcM (x : SrcMix h₁ δ) (hx : ¬ PMix Φ h₁ δ x) : IsZero (srcM h₁ N δ x) := by
  obtain ⟨⟨⟨p, hp⟩, ⟨⟨⟨qs, b⟩, hb, hrb⟩, hq⟩⟩, hne⟩ := x
  subst hp
  change qs = p.src at hq
  subst qs
  have h₄ : Φ.wtT (p.src.1 + Finsupp.single b 1) + RDc.iX p.lbl =
      Φ.wtT ((p.tgt h₁).1 + Finsupp.single b 1) := by
    rw [Φ.wtT_add_single, Edge.tgt_val, add_right_comm]
  refine isZero_src_of_isIso _ (hmix i p.lbl b (Ne.symm hne) p.π_lbl hb (wt_tgt h₁ p rfl)
    (Φ.wtT_add_single (p.tgt h₁).1 b) (wt_tgt h₁ (sameSrc Φ p b hb hrb) rfl) h₄
    (N ((sameSrc Φ p b hb hrb).tgt h₁))) ?_
  rcases not_and_or.mp hx with h | h
  · exact isZero_F_of_isZero_E _ (hzero _ b _ h) _
  · exact Functor.map_isZero _ (Functor.map_isZero (LinearCat.evalAt _) (hzero _ _ h₄ h))

include hzero hmix in
omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
/-- A mixed summand `F_c E_d` off the graph is zero: it is isomorphic to `E_d F_c`, which
contains `E_d` or `F_c` of an irrelevant edge. -/
theorem isZero_tgtM (y : TgtMix h₂ δ) (hy : ¬ QMix Φ h₂ δ y) : IsZero (tgtM h₂ N δ y) := by
  obtain ⟨⟨⟨⟨⟨rs, c⟩, hc, hrc⟩, hr⟩, ⟨s, hs⟩⟩, hne⟩ := y
  change rs = δ at hr
  subst rs
  have h₃ : Φ.wtT (δ.1 - Finsupp.single s.lbl 1) + RDc.iX c = Φ.wtT s.src.1 := by
    rw [Φ.wtT_add_single, Edge.src_eq_of_tgt h₂ s, hs]
    congr 1
    show _ = δ.1 + Finsupp.single c 1 - Finsupp.single s.lbl 1
    abel
  refine isZero_tgt_of_isIso _ (hmix i s.lbl c hne s.π_lbl hc (wtT_sub_add δ.1 s.lbl)
    (wt_tgt h₂ ⟨(δ, c), hc, hrc⟩ rfl) h₃ (wt_tgt h₂ s hs) (N s.src)) ?_
  rcases not_and_or.mp hy with h | h
  · exact Functor.map_isZero (LinearCat.evalAt _) (hzero _ _ (wtT_sub_add δ.1 s.lbl) h)
  · exact Functor.map_isZero (S.E s.lbl (wtT_sub_add δ.1 s.lbl)).obj
      (isZero_F_of_isZero_E h₃ (hzero _ _ h₃ h) _)

include hzero hmix in
/-- **The mixed block of `σ` is invertible.** The matrix of `σ` of `g` between the mixed
summands `E_a F_b` of `(F_i E_i N)_δ` and `F_c E_d` of `(E_i F_i N)_δ` is monomial along
`graphEquiv`, with the sideways crossings of `swapCell` as entries; off the graph the summands
are zero. Hypotheses: the 1-morphisms of irrelevant edges vanish (`hzero`), and the mixed
sideways crossings of the cover are invertible (`hmix`, Brundan, arXiv:1501.00350v1,
Definition 1.1, for distinct colours `a ≠ b` of `g̃` over one colour of `g`). -/
theorem isIso_mixed :
    IsIso (matrixW fun x y =>
      sM h₁ N δ x ≫ (sigma Φ S D h₁ h₂).hom.app N δ ≫ rM' h₂ N δ y) :=
  isIso_matrix_of_monomial _ (graphEquiv h₁ h₂ δ)
    (fun x y hx _ hne => sM_sigma_zero D h₁ h₂ N δ x y.1.1 y.1.2
      fun e₁ e₂ => hne (graphY_eq h₁ h₂ δ x hx y e₁ e₂))
    (fun x hx => isIso_entry D h₁ h₂ N δ hmix x hx)
    (fun x hx => isZero_srcM D h₁ N δ hzero hmix x hx)
    (fun y hy => isZero_tgtM D h₂ N δ hzero hmix y hy)

end Monomial

end Furling

end Categorification.TwoRep
