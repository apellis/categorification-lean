/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingCross

/-!
# Furling: the rightward crossings of `g` on blocks

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2.3, Lemma with
label `lem:g-action`; J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, (1.6). The rightward crossing `σ : E_i F_i 1_λ ⟶ F_i E_i 1_λ` of `g`
(`RightwardCrossing.sigma` of the unit of `E_i ⊣ F_i` at `λ`, the same-colour crossing
`Furling.cross`, and the counit at `λ - α_i`) on the summand `E_a F_b` (an edge `p : β →a→ γ`
of `E` and an edge `q : β →b→` of `F` with the same source `β`), followed by the projection to
the summand `F_c` (an edge `r : γ →c→`):

* `c = b` (`genFE_sigma_projF_swap`): the unit of `E_b ⊣ F_b`, the swapped-path component
  `swapCell` of the crossing of `g`, and the counit of `E_b ⊣ F_b` (the sideways crossing of
  `swapCell`), to the summand `F_b E_a`, if the swapped path is relevant, and zero otherwise
  (`genFE_sigma_projF_swap_of_not_rel`). For `a ≠ b` this is the mixed block; for `a = b`
  the diagonal block.
* `c ≠ b`, `a = b` (`genFE_sigma_projF_self`): the **teleporter**, the unit of `E_c ⊣ F_c`,
  the component `selfCell = (ϖ_c(y_L) - ϖ_a(y_R))⁻¹` on `E_a E_c`, and the counit of
  `E_a ⊣ F_a`, to the summand `F_c E_c`.
* `c ≠ b`, `a ≠ b` (`genFE_sigma_projF_zero`): zero.

With `Furling.unit_projF` and `Furling.genE_counit` (cups and caps) and `Furling.genE_dot`
(dots), these describe `σ` of `g` blockwise, as in the coproduct layer
(`RouqCoproduct.rouqSig`, `sigma_eq_teleporter`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

universe u₁ u₂ v₁ wk u₃ u₄

namespace LinearCat

variable {k : Type wk} [CommRing k]

/-- The rightward crossing in `LinearCat k`, componentwise. -/
theorem sigma_hom_app {C₁ C₂ C₃ : LinearCat.{wk, v₁, u₂} k} {E₁ : C₁ ⟶ C₂} {E₂ : C₂ ⟶ C₃}
    {R₁ : C₂ ⟶ C₁} {R₂ : C₃ ⟶ C₂} (η₂ : 𝟙 C₂ ⟶ E₂ ≫ R₂) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 C₂) (N : (C₂ : Type u₂)) :
    (RightwardCrossing.sigma η₂ τ ε₁).hom.app N =
      η₂.hom.app (E₁.obj.obj (R₁.obj.obj N)) ≫ R₂.obj.map (τ.hom.app (R₁.obj.obj N)) ≫
        R₂.obj.map (E₂.obj.map (ε₁.hom.app N)) := by
  rw [RightwardCrossing.sigma_eq]
  change 𝟙 _ ≫ η₂.hom.app (E₁.obj.obj (R₁.obj.obj N)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (τ.hom.app (R₁.obj.obj N)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (E₂.obj.map (ε₁.hom.app N)) ≫ 𝟙 _ = _
  simp

end LinearCat


/-! ## Bookkeeping in a category -/

section Chain

variable {C D : Type*} [Category C] [Category D]

theorem comp_chain_three {B₀ B₁ B₂ B₃ P₀ P₁ P₂ Q : C} (U : B₀ ⟶ B₁) (T : B₁ ⟶ B₂)
    (V : B₂ ⟶ B₃) (π₃ : B₃ ⟶ Q) (π₂ : B₂ ⟶ P₂) (π₁ : B₁ ⟶ P₁) (v : P₂ ⟶ Q) (t : P₁ ⟶ P₂)
    (w₁ : B₀ ⟶ P₀) (w₂ : P₀ ⟶ P₁) (hV : V ≫ π₃ = π₂ ≫ v) (hT : T ≫ π₂ = π₁ ≫ t)
    (hU : U ≫ π₁ = w₁ ≫ w₂) :
    (U ≫ T ≫ V) ≫ π₃ = w₁ ≫ w₂ ≫ t ≫ v := by
  rw [Category.assoc, Category.assoc, hV, ← Category.assoc T, hT, Category.assoc,
    ← Category.assoc U, hU, Category.assoc]

theorem comp_unit_map_chain (F : D ⥤ C) {A B : C} {B' Z₁ Z₂ Z₃ Z₄ : D} (g : A ⟶ B)
    (u : B ⟶ F.obj B') (u' : A ⟶ F.obj Z₁) (g' : Z₁ ⟶ B') (a : B' ⟶ Z₂) (b : Z₂ ⟶ Z₃)
    (a' : Z₁ ⟶ Z₃) (c : Z₃ ⟶ Z₄) (hu : g ≫ u = u' ≫ F.map g') (ha : g' ≫ a ≫ b = a') :
    g ≫ u ≫ F.map a ≫ F.map b ≫ F.map c = u' ≫ F.map (a' ≫ c) := by
  rw [← Category.assoc, hu, Category.assoc, ← F.map_comp, ← F.map_comp, ← F.map_comp,
    ← Category.assoc, ← Category.assoc, Category.assoc g', ha]

theorem map_comp_chain (F : D ⥤ C) {Z₀ Z₁ Z₂ : D} {A B : C} (x : Z₀ ⟶ Z₁) (y : Z₁ ⟶ Z₂)
    (z : F.obj Z₂ ⟶ A) (w : A ⟶ B) (v : F.obj Z₁ ⟶ B) (h : (F.map y ≫ z) ≫ w = v) :
    F.map (x ≫ y) ≫ z ≫ w = F.map x ≫ v := by
  rw [F.map_comp, Category.assoc, ← h, Category.assoc]

theorem cell_chain {A₀ A₁ A₂ B₁ T : C} (a : A₀ ⟶ A₁) (κ : A₁ ⟶ A₂) (κ' : A₀ ⟶ B₁)
    (b : B₁ ⟶ A₂) (rest : A₂ ⟶ T) (r : B₁ ⟶ T) (h₁ : a ≫ κ = κ' ≫ b) (h₂ : b ≫ rest = r) :
    a ≫ κ ≫ rest = κ' ≫ r := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

theorem map_counit_chain (H : D ⥤ C) {U V W U' : D} {Z T : C} (x : U ⟶ V) (y : V ⟶ W)
    (g : H.obj W ⟶ Z) (m : Z ⟶ T) (z : W ⟶ U') (w : H.obj U' ⟶ T) (c : U ⟶ U')
    (hg : g ≫ m = H.map z ≫ w) (hy : x ≫ y ≫ z = c) :
    H.map x ≫ (H.map y ≫ g) ≫ m = H.map c ≫ w := by
  rw [Category.assoc, hg, ← hy]
  simp only [Functor.map_comp, Category.assoc]

theorem map_section_chain (K : D ⥤ C) {U V : D} {W : C} (x : U ⟶ V) (π : V ⟶ U)
    (u : K.obj U ⟶ W) (h : x ≫ π = 𝟙 U) : K.map x ≫ K.map π ≫ u = u := by
  rw [← Category.assoc, ← K.map_comp, h, K.map_id, Category.id_comp]

theorem map_zero_chain [Preadditive D] [Preadditive C] (K : D ⥤ C) [K.PreservesZeroMorphisms]
    {U V U' : D} {W : C} (x : U ⟶ V) (π : V ⟶ U') (u : K.obj U' ⟶ W) (h : x ≫ π = 0) :
    K.map x ≫ K.map π ≫ u = 0 := by
  rw [← Category.assoc, ← K.map_comp, h, K.map_zero, zero_comp]

theorem comp_map_zero_comp [Preadditive D] [Preadditive C] (K : D ⥤ C)
    [K.PreservesZeroMorphisms] {U V : D} {A W : C} (a : A ⟶ K.obj U) (w : K.obj V ⟶ W) :
    a ≫ K.map (0 : U ⟶ V) ≫ w = 0 := by
  rw [K.map_zero, zero_comp, comp_zero]

theorem comp_zero_comp' [Preadditive C] {A B Z T : C} (a : A ⟶ B) (m : Z ⟶ T) :
    a ≫ (0 : B ⟶ Z) ≫ m = 0 := by
  rw [zero_comp, comp_zero]

theorem comp_add_chain [Preadditive C] {A B Z T : C} (a : A ⟶ B) (x y : B ⟶ Z) (m : Z ⟶ T) :
    a ≫ (x + y) ≫ m = a ≫ x ≫ m + a ≫ y ≫ m := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

theorem map_add_zero_chain [Preadditive D] [Preadditive C] (K : D ⥤ C)
    [K.PreservesZeroMorphisms] {U V : D} {A : C} (u : A ⟶ K.obj U) (x y : U ⟶ V)
    (hx : x = 0) (hy : y = 0) : u ≫ K.map (x + y) = 0 := by
  rw [hx, hy, add_zero, K.map_zero, comp_zero]

theorem map_add_chain [Preadditive D] {U V : D} {A : C} (K : D ⥤ C) (u : A ⟶ K.obj U)
    (x y z : U ⟶ V) (hy : y = 0) (hx : x = z) : u ≫ K.map (x + y) = u ≫ K.map z := by
  rw [hy, add_zero, hx]

theorem map_add_chain' [Preadditive D] {U V : D} {A : C} (K : D ⥤ C) (u : A ⟶ K.obj U)
    (x y z : U ⟶ V) (hx : x = 0) (hy : y = z) : u ≫ K.map (x + y) = u ≫ K.map z := by
  rw [hx, zero_add, hy]

end Chain

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
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)

variable {i : I} {l l' l'' : X} (h₁ : l + RD.iX i = l') (h₂ : l' + RD.iX i = l'')

omit [DecidableEq I] [DecidableEq J] in
/-- The projections of `F_i N` are natural. -/
theorem projF_natural {m m' : X} (h : m + RD.iX i = m') {N N' : ∀ γ : Φ.Blk m', blkCat Φ S γ.1}
    (g : N ⟶ N') (e : Φ.Edge i m) :
    (F Φ S i h).obj.map g e.src ≫ projF Φ S i h N' e =
      projF Φ S i h N e ≫ (Fa Φ S h e (e.tgt h) rfl).map (g (e.tgt h)) :=
  biproduct.map_π (fun q : {e' : Φ.Edge i m // e'.src = e.src} =>
    (incSrc Φ S q.1 e.src q.2).map ((blockRes (Edge.tgt h) (Fa Φ S h)).map g q.1)) ⟨e, rfl⟩

/-- The inclusion of the summand `F_b N` of an edge into `F_i N`. -/
abbrev incF {m m' : X} (h : m + RD.iX i = m') (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1)
    (e : Φ.Edge i m) :
    (Fa Φ S h e (e.tgt h) rfl).obj (N (e.tgt h)) ⟶ (F Φ S i h).obj.obj N e.src :=
  biproduct.ι (C := blkCat Φ S e.src.1) (fun q : {e' : Φ.Edge i m // e'.src = e.src} =>
    (incSrc Φ S q.1 e.src q.2).obj ((blockRes (Edge.tgt h) (Fa Φ S h)).obj N q.1)) ⟨e, rfl⟩

omit [DecidableEq I] [DecidableEq J] in
theorem incF_projF {m m' : X} (h : m + RD.iX i = m') (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1)
    (e : Φ.Edge i m) : incF Φ S h N e ≫ projF Φ S i h N e = 𝟙 _ :=
  biproduct.ι_π_self _ _

omit [DecidableEq I] [DecidableEq J] in
theorem incF_projF_of_ne {m m' : X} (h : m + RD.iX i = m') (N : ∀ γ : Φ.Blk m', blkCat Φ S γ.1)
    (e : Φ.Edge i m) (d : J) (hd : Φ.π d = i) (hrd : Φ.rel e.src.1 d) (hne : e.lbl ≠ d) :
    incF Φ S h N e ≫ projF Φ S i h N ⟨(e.src, d), hd, hrd⟩ = 0 :=
  biproduct.ι_π_ne _ fun h' => hne (congrArg (fun q => q.1.lbl) h')

/-- The edge `β →b→` of `F` with the source of an edge `p`. -/
abbrev sameSrc (p : Φ.Edge i l) (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) : Φ.Edge i l :=
  ⟨(p.src, b), hb, hrb⟩

/-- **The generator of `E_i F_i N` on the summand `E_a F_b`**: an edge `p : β →a→ γ` of `E` and
the edge `β →b→` of `F`. -/
abbrev genFE (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (p : Φ.Edge i l) (b : J) (hb : Φ.π b = i)
    (hrb : Φ.rel p.src.1 b) :
    (Ea Φ S h₁ p (p.tgt h₁) rfl).obj ((Fa Φ S h₁ (sameSrc Φ p b hb hrb)
        ((sameSrc Φ p b hb hrb).tgt h₁) rfl).obj (N ((sameSrc Φ p b hb hrb).tgt h₁))) ⟶
      ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) (p.tgt h₁) :=
  (Ea Φ S h₁ p (p.tgt h₁) rfl).map
      (incF Φ S h₁ N (sameSrc Φ p b hb hrb)) ≫
    genE Φ S i h₁ ((F Φ S i h₁).obj.obj N) ⟨p, rfl⟩

/-- **The rightward crossing of `g`** at weight `λ = l'`: Brundan (1.6) for the adjunctions
`E_i ⊣ F_i` and the same-colour crossing of `g`. -/
abbrev sigma : F Φ S i h₁ ≫ E Φ S i h₁ ⟶ E Φ S i h₂ ≫ F Φ S i h₂ :=
  RightwardCrossing.sigma (adj Φ S i h₂).unit (cross Φ S D h₁ h₂ h₁ h₂) (adj Φ S i h₁).counit


/-- `σ` of `g` followed by the projection to the summand `F_c` of an edge `r`: the unit of
`E_c ⊣ F_c`, then `F_c` of the generator of `r`, the crossing and the counit. -/
theorem sigma_projF (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (r : Φ.Edge i l') :
    (sigma Φ S D h₁ h₂).hom.app N r.src ≫ projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) r =
      (adjA Φ S h₂ r (r.tgt h₂) rfl).unit.app (((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) r.src) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          (genE Φ S i h₂ ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) ⟨r, rfl⟩) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          ((cross Φ S D h₁ h₂ h₁ h₂).hom.app ((F Φ S i h₁).obj.obj N) (r.tgt h₂)) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          ((E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N) (r.tgt h₂)) := by
  rw [LinearCat.sigma_hom_app]
  exact comp_chain_three _ _ _ _ _ _ _ _ _ _
    (projF_natural Φ S h₂ ((E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)) r)
    (projF_natural Φ S h₂ ((cross Φ S D h₁ h₂ h₁ h₂).hom.app ((F Φ S i h₁).obj.obj N)) r)
    (unit_projF Φ S i h₂ ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) r)

/-- The generator of the summand `E_a F_b` followed by the generator of `E_c` and the crossing
of `g`: the crossing of `g` on the path `β →a→ →c→`, after the inclusion of `F_b`. -/
theorem map_genFE_genE_cross (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (p : Φ.Edge i l) (b : J)
    (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J) (hc : Φ.π c = i)
    (hr : Φ.rel (p.tgt h₁).1 c) :
    (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (genFE Φ S h₁ N p b hb hrb) ≫
        genE Φ S i h₂ ((F Φ S i h₁ ≫ E Φ S i h₁).obj.obj N) ⟨Edge.next h₁ p c hc hr, rfl⟩ ≫
        (cross Φ S D h₁ h₂ h₁ h₂).hom.app ((F Φ S i h₁).obj.obj N)
          ((Edge.next h₁ p c hc hr).tgt h₂) =
      (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((Ea Φ S h₁ p (p.tgt h₁) rfl).map
            (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
        crossNext Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl := by
  exact map_comp_chain _ _ _ _ _ _
    (gen₂_cross Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p (Edge.next h₁ p c hc hr) rfl rfl)

/-- **`σ` of `g` on the summand `E_a F_b`, projected to `F_c`**, through the crossing of `g` on
the path `β →a→ →c→` (`crossNext`). -/
theorem genFE_sigma_projF (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (p : Φ.Edge i l) (b : J)
    (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J) (hc : Φ.π c = i)
    (hr : Φ.rel (p.tgt h₁).1 c) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hr) =
      (adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
              ((Ea Φ S h₁ p (p.tgt h₁) rfl).map
                (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
            crossNext Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
            (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
              ((Edge.next h₁ p c hc hr).tgt h₂)) := by
  rw [sigma_projF Φ S D h₁ h₂ N (Edge.next h₁ p c hc hr)]
  refine (comp_unit_map_chain (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl) _ _ _
    ((Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (genFE Φ S h₁ N p b hb hrb)) _ _ _ _
    ((adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit_naturality
      (genFE Φ S h₁ N p b hb hrb)).symm
    (map_genFE_genE_cross Φ S D h₁ h₂ N p b hb hrb c hc hr)).trans ?_
  exact congrArg (_ ≫ ·)
    (congrArg (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (Category.assoc _ _ _))

omit [DecidableEq I] [DecidableEq J] in
theorem genE_natural {m m' : X} (h : m + RD.iX i = m') {M M' : ∀ β : Φ.Blk m, blkCat Φ S β.1}
    (g : M ⟶ M') {γ : Φ.Blk m'} (q : {e : Φ.Edge i m // e.tgt h = γ}) :
    genE Φ S i h M q ≫ (E Φ S i h).obj.map g γ =
      (Ea Φ S h q.1 γ q.2).map (g q.1.src) ≫ genE Φ S i h M' q :=
  blockι_map (Edge.tgt h) (Φ.Ea S h) ((blockRes Edge.src (Φ.resSrc S)).map g) q

omit [DecidableEq I] [DecidableEq J] in
/-- **Collapsing an output path against the counit**: a 2-cell `κ` of `g̃` into the path
`q` then `f₂`, after the inclusion of `F_b` along `q` and followed by the counit of
`E_i ⊣ F_i`, is `κ` followed by the counit of `E_b ⊣ F_b`. -/
theorem cell_gen₂_counit (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (q : Φ.Edge i l) (d : J)
    (hd : Φ.π d = i) (hrd : Φ.rel (q.tgt h₁).1 d) {δ : Φ.Blk l''}
    (hδ : (Edge.next h₁ q d hd hrd).tgt h₂ = δ)
    {y : LinearCat.{wk, v₁, u₂} k} {G₁ : S.obj (Φ.wtT q.src.1) ⟶ y} {G₂ : y ⟶ S.obj (Φ.wtT δ.1)}
    (κ : G₁ ≫ G₂ ⟶ S.E q.lbl (wt_tgt h₁ q rfl) ≫
      S.E d (wt_tgt h₂ (Edge.next h₁ q d hd hrd) hδ)) :
    G₂.obj.map (G₁.obj.map (incF Φ S h₁ N q)) ≫ κ.hom.app ((F Φ S i h₁).obj.obj N q.src) ≫
        gen₂ Φ S h₁ h₂ ((F Φ S i h₁).obj.obj N) q (Edge.next h₁ q d hd hrd) rfl hδ ≫
        (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N) δ =
      κ.hom.app ((Fa Φ S h₁ q (q.tgt h₁) rfl).obj (N (q.tgt h₁))) ≫
        (Ea Φ S h₂ (Edge.next h₁ q d hd hrd) δ hδ).map
          ((adjA Φ S h₁ q (q.tgt h₁) rfl).counit.app (N (q.tgt h₁))) ≫
        genE Φ S i h₂ N ⟨Edge.next h₁ q d hd hrd, hδ⟩ := by
  refine (cell_chain _ _ _ _ _ _ (comp_cell_natural κ (incF Φ S h₁ N q))
    (map_counit_chain (Ea Φ S h₂ (Edge.next h₁ q d hd hrd) δ hδ)
      ((Ea Φ S h₁ q (q.tgt h₁) rfl).map (incF Φ S h₁ N q)) _ _ _ _ _ _
      (genE_natural Φ S h₂ ((adj Φ S i h₁).counit.hom.app N) ⟨Edge.next h₁ q d hd hrd, hδ⟩)
      ((congrArg (_ ≫ ·) (genE_counit Φ S i h₁ N q)).trans
        (map_section_chain _ _ _ _ (incF_projF Φ S h₁ N q))))).trans ?_
  rfl

omit [DecidableEq I] [DecidableEq J] in
/-- A 2-cell of `g̃` into a path whose first edge is not `q`, after the inclusion of `F_b`
along `q` and followed by the counit of `E_i ⊣ F_i`, vanishes. -/
theorem cell_gen₂_counit_of_ne (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (q : Φ.Edge i l) (e : J)
    (he : Φ.π e = i) (hre : Φ.rel q.src.1 e) (hne : q.lbl ≠ e) (d : J) (hd : Φ.π d = i)
    (hrd : Φ.rel ((sameSrc Φ q e he hre).tgt h₁).1 d) {δ : Φ.Blk l''}
    (hδ : (Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd).tgt h₂ = δ)
    {y : LinearCat.{wk, v₁, u₂} k} {G₁ : S.obj (Φ.wtT q.src.1) ⟶ y} {G₂ : y ⟶ S.obj (Φ.wtT δ.1)}
    (κ : G₁ ≫ G₂ ⟶ S.E e (wt_tgt h₁ (sameSrc Φ q e he hre) rfl) ≫
      S.E d (wt_tgt h₂ (Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd) hδ)) :
    G₂.obj.map (G₁.obj.map (incF Φ S h₁ N q)) ≫ κ.hom.app ((F Φ S i h₁).obj.obj N q.src) ≫
        gen₂ Φ S h₁ h₂ ((F Φ S i h₁).obj.obj N) (sameSrc Φ q e he hre)
          (Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd) rfl hδ ≫
        (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N) δ = 0 := by
  refine (cell_chain _ _ _ _ _ _ (comp_cell_natural κ (incF Φ S h₁ N q))
    (map_counit_chain (Ea Φ S h₂ (Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd) δ hδ)
      ((Ea Φ S h₁ (sameSrc Φ q e he hre) _ rfl).map (incF Φ S h₁ N q)) _ _ _ _ _ _
      (genE_natural Φ S h₂ ((adj Φ S i h₁).counit.hom.app N)
        ⟨Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd, hδ⟩)
      ((congrArg (_ ≫ ·) (genE_counit Φ S i h₁ N (sameSrc Φ q e he hre))).trans
        (map_zero_chain (Ea Φ S h₁ (sameSrc Φ q e he hre) _ rfl) (incF Φ S h₁ N q)
          (projF Φ S i h₁ N (sameSrc Φ q e he hre))
          ((adjA Φ S h₁ (sameSrc Φ q e he hre) _ rfl).counit.app (N (Edge.tgt h₁ (sameSrc Φ q e he hre))))
          (incF_projF_of_ne Φ S h₁ N q e he hre hne))))).trans ?_
  exact comp_map_zero_comp (Ea Φ S h₂ (Edge.next h₁ (sameSrc Φ q e he hre) d hd hrd) δ hδ) _ _

/-! ## The blocks of `σ` -/

section Blocks

variable (N : ∀ γ : Φ.Blk l', blkCat Φ S γ.1) (p : Φ.Edge i l)

/-- The summand `E_a F_b` against `F_c E_d` through the crossing: the two terms of
`crossNext`. -/
theorem genFE_sigma_projF_eq_add (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J)
    (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hr) =
      (adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
              ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
            crossSwap Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
            (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
              ((Edge.next h₁ p c hc hr).tgt h₂) +
          (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
              ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
            crossSelf Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
            (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
              ((Edge.next h₁ p c hc hr).tgt h₂)) :=
  (genFE_sigma_projF Φ S D h₁ h₂ N p b hb hrb c hc hr).trans
    (congrArg (_ ≫ ·) (congrArg (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
      (comp_add_chain _ _ _ _)))

/-- The swapped-path term of the crossing, after the inclusion of `F_b` along the edge
`β →b→` and the counit: for `c = b`, the swapped-path component followed by the counit of
`E_b ⊣ F_b`. -/
theorem crossSwap_counit_of_rel (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) (hs : Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    (Ea Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSwap Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p b hb hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N) ((Edge.next h₁ p b hb hr).tgt h₂) =
    (swapCell S D (i = i) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hr) rfl)
        (wt_tgt h₁ (swapFst Φ p b hb hrb) rfl)
        (wt_tgt h₂ (swapSnd Φ h₁ p b hb hrb hs)
          (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl))).hom.app
        ((Fa Φ S h₁ (sameSrc Φ p b hb hrb) _ rfl).obj (N ((sameSrc Φ p b hb hrb).tgt h₁))) ≫
      (Ea Φ S h₂ (swapSnd Φ h₁ p b hb hrb hs) _
          (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl)).map
        ((adjA Φ S h₁ (sameSrc Φ p b hb hrb) _ rfl).counit.app
          (N ((sameSrc Φ p b hb hrb).tgt h₁))) ≫
      genE Φ S i h₂ N ⟨swapSnd Φ h₁ p b hb hrb hs,
        swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl⟩ := by
  unfold crossSwap
  rw [dite_eq_left_of_eq_true (eq_true ⟨hrb, hs⟩)]
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  exact cell_gen₂_counit Φ S h₁ h₂ N (sameSrc Φ p b hb hrb) p.lbl p.π_lbl hs
    (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl)
    (swapCell S D (i = i) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hr) rfl)
        (wt_tgt h₁ (swapFst Φ p b hb hrb) rfl)
        (wt_tgt h₂ (swapSnd Φ h₁ p b hb hrb hs)
          (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl)))

/-- The swapped-path term vanishes against the inclusion along `β →b→` if `c ≠ b`. -/
theorem crossSwap_counit_of_ne (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J)
    (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c) (hbc : b ≠ c) :
    (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSwap Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p c hc hr).tgt h₂) = 0 := by
  unfold crossSwap
  by_cases hs : Φ.rel p.src.1 c ∧ Φ.rel (p.src.1 + Finsupp.single c 1) p.lbl
  · rw [dite_eq_left_of_eq_true (eq_true hs)]
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
    exact cell_gen₂_counit_of_ne Φ S h₁ h₂ N (sameSrc Φ p b hb hrb) c hc hs.1 hbc p.lbl
      p.π_lbl hs.2 (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p c hc hr hs.1 hs.2 rfl)
      (swapCell S D (i = i) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)
        (wt_tgt h₁ (swapFst Φ p c hc hs.1) rfl)
        (wt_tgt h₂ (swapSnd Φ h₁ p c hc hs.1 hs.2)
          (swapSnd_tgt Φ h₁ h₂ h₁ h₂ p c hc hr hs.1 hs.2 rfl)))
  · rw [dite_eq_right_of_eq_false (eq_false hs)]
    exact comp_zero_comp' _ _

/-- The swapped-path term vanishes if the second edge of the swapped path is irrelevant. -/
theorem crossSwap_counit_of_not_rel (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) (hs : ¬ Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    (Ea Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSwap Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p b hb hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p b hb hr).tgt h₂) = 0 := by
  unfold crossSwap
  rw [dite_eq_right_of_eq_false (eq_false fun h => hs h.2)]
  exact comp_zero_comp' _ _

/-- The same-path term vanishes against the inclusion along `β →b→` if `b ≠ a`. -/
theorem crossSelf_counit_of_ne (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J)
    (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c) (hba : b ≠ p.lbl) :
    (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSelf Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p c hc hr).tgt h₂) = 0 := by
  unfold crossSelf
  rw [dite_eq_left_of_eq_true (eq_true rfl)]
  by_cases hac : p.lbl = c
  · rw [ite_eq_left hac]
    exact comp_zero_comp' _ _
  · rw [ite_eq_right hac]
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
    exact cell_gen₂_counit_of_ne Φ S h₁ h₂ N (sameSrc Φ p b hb hrb) p.lbl p.π_lbl p.rel_src hba
      c hc hr (selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl)
      (selfCell S D (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl))

/-- The same-path term vanishes if `c = a`. -/
theorem crossSelf_counit_of_eq (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 p.lbl) :
    (Ea Φ S h₂ (Edge.next h₁ p p.lbl p.π_lbl hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSelf Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p p.lbl p.π_lbl hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p p.lbl p.π_lbl hr).tgt h₂) = 0 := by
  unfold crossSelf
  rw [dite_eq_left_of_eq_true (eq_true rfl), ite_eq_left rfl]
  exact comp_zero_comp' _ _

/-- The same-path term against the inclusion along `β →a→` (`F_a`), for `c ≠ a`: the
component `selfCell` followed by the counit of `E_a ⊣ F_a`. -/
theorem crossSelf_counit_self (c : J) (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c)
    (hac : p.lbl ≠ c) :
    (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map
          (incF Φ S h₁ N (sameSrc Φ p p.lbl p.π_lbl p.rel_src))) ≫
      crossSelf Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p c hc hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p c hc hr).tgt h₂) =
    (selfCell S D (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)).hom.app
        ((Fa Φ S h₁ (sameSrc Φ p p.lbl p.π_lbl p.rel_src) _ rfl).obj
          (N ((sameSrc Φ p p.lbl p.π_lbl p.rel_src).tgt h₁))) ≫
      (Ea Φ S h₂ (selfSnd Φ h₁ h₁ rfl p c hc hr) _
          (selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl)).map
        ((adjA Φ S h₁ (sameSrc Φ p p.lbl p.π_lbl p.rel_src) _ rfl).counit.app
          (N ((sameSrc Φ p p.lbl p.π_lbl p.rel_src).tgt h₁))) ≫
      genE Φ S i h₂ N ⟨selfSnd Φ h₁ h₁ rfl p c hc hr,
        selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl⟩ := by
  unfold crossSelf
  rw [dite_eq_left_of_eq_true (eq_true rfl), ite_eq_right hac]
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  exact cell_gen₂_counit Φ S h₁ h₂ N (sameSrc Φ p p.lbl p.π_lbl p.rel_src) c hc hr
    (selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl)
    (selfCell S D (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl))

/-- The same-path term vanishes against the inclusion along `β →b→` when `c = b`. -/
theorem crossSelf_counit_of_swap (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) :
    (Ea Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
        ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₁ N (sameSrc Φ p b hb hrb))) ≫
      crossSelf Φ S D h₁ h₂ h₁ h₂ ((F Φ S i h₁).obj.obj N) p b hb hr rfl ≫
      (E Φ S i h₂).obj.map ((adj Φ S i h₁).counit.hom.app N)
        ((Edge.next h₁ p b hb hr).tgt h₂) = 0 := by
  by_cases hba : b = p.lbl
  · subst hba
    exact crossSelf_counit_of_eq Φ S D h₁ h₂ N p _ hb hrb hr
  · exact crossSelf_counit_of_ne Φ S D h₁ h₂ N p b hb hrb b hb hr hba

/-- **`σ` of `g`, the swapped blocks** (`F_b`, `c = b`): on the summand `E_a F_b`, projected
to `F_b E_a`, the rightward crossing of `g` is the unit of `E_b ⊣ F_b`, the swapped-path
component `swapCell` of the crossing (the mixed component for `a ≠ b`, the diagonal one
`h_a⁻¹ ψ` for `a = b`), and the counit of `E_b ⊣ F_b`. -/
theorem genFE_sigma_projF_swap (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) (hs : Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p b hb hr) =
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
                (N ((sameSrc Φ p b hb hrb).tgt h₁))) ≫
            genE Φ S i h₂ N ⟨swapSnd Φ h₁ p b hb hrb hs,
              swapSnd_tgt Φ h₁ h₂ h₁ h₂ p b hb hr hrb hs rfl⟩) :=
  (genFE_sigma_projF_eq_add Φ S D h₁ h₂ N p b hb hrb b hb hr).trans
    (map_add_chain _ _ _ _ _ (crossSelf_counit_of_swap Φ S D h₁ h₂ N p b hb hrb hr)
      (crossSwap_counit_of_rel Φ S D h₁ h₂ N p b hb hrb hr hs))

/-- `σ` of `g` on `E_a F_b` projected to `F_b`, when the swapped path `β →b→ →a→` has an
irrelevant edge: zero. -/
theorem genFE_sigma_projF_swap_of_not_rel (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) (hs : ¬ Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p b hb hr) = 0 :=
  (genFE_sigma_projF_eq_add Φ S D h₁ h₂ N p b hb hrb b hb hr).trans
    (map_add_zero_chain _ _ _ _ (crossSwap_counit_of_not_rel Φ S D h₁ h₂ N p b hb hrb hr hs)
      (crossSelf_counit_of_swap Φ S D h₁ h₂ N p b hb hrb hr))

/-- **`σ` of `g`, the teleporter blocks** (`F_a`, `c ≠ a`): on the summand `E_a F_a`,
projected to `F_c E_c`, the rightward crossing of `g` is the unit of `E_c ⊣ F_c`, the
same-path component `selfCell = (ϖ_c(y_L) - ϖ_a(y_R))⁻¹` on `E_a E_c`, and the counit of
`E_a ⊣ F_a`. -/
theorem genFE_sigma_projF_self (c : J) (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c)
    (hac : p.lbl ≠ c) :
    genFE Φ S h₁ N p p.lbl p.π_lbl p.rel_src ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hr) =
      (adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((selfCell S D (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)).hom.app
              ((Fa Φ S h₁ (sameSrc Φ p p.lbl p.π_lbl p.rel_src) _ rfl).obj
                (N ((sameSrc Φ p p.lbl p.π_lbl p.rel_src).tgt h₁))) ≫
            (Ea Φ S h₂ (selfSnd Φ h₁ h₁ rfl p c hc hr) _
                (selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl)).map
              ((adjA Φ S h₁ (sameSrc Φ p p.lbl p.π_lbl p.rel_src) _ rfl).counit.app
                (N ((sameSrc Φ p p.lbl p.π_lbl p.rel_src).tgt h₁))) ≫
            genE Φ S i h₂ N ⟨selfSnd Φ h₁ h₁ rfl p c hc hr,
              selfSnd_tgt Φ h₁ h₂ h₁ h₂ rfl p c hc hr rfl⟩) :=
  (genFE_sigma_projF_eq_add Φ S D h₁ h₂ N p p.lbl p.π_lbl p.rel_src c hc hr).trans
    (map_add_chain' _ _ _ _ _
      (crossSwap_counit_of_ne Φ S D h₁ h₂ N p p.lbl p.π_lbl p.rel_src c hc hr hac)
      (crossSelf_counit_self Φ S D h₁ h₂ N p c hc hr hac))

/-- **`σ` of `g`, the vanishing blocks**: on `E_a F_b` projected to `F_c` with `c ≠ b` and
`b ≠ a`, the rightward crossing of `g` is zero. -/
theorem genFE_sigma_projF_zero (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J)
    (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c) (hbc : b ≠ c) (hba : b ≠ p.lbl) :
    genFE Φ S h₁ N p b hb hrb ≫ (sigma Φ S D h₁ h₂).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S i h₂).obj.obj N) (Edge.next h₁ p c hc hr) = 0 :=
  (genFE_sigma_projF_eq_add Φ S D h₁ h₂ N p b hb hrb c hc hr).trans
    (map_add_zero_chain _ _ _ _
      (crossSwap_counit_of_ne Φ S D h₁ h₂ N p b hb hrb c hc hr hbc)
      (crossSelf_counit_of_ne Φ S D h₁ h₂ N p b hb hrb c hc hr hba))

end Blocks

end Furling

end Categorification.TwoRep
