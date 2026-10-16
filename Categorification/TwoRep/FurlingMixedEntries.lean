/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixedZero

/-!
# The entries of a distinct-colour mixed crossing

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action`; Brundan, arXiv:1501.00350v1, (1.6)–(1.7).

Compute the actual right-adjunction mate on two-colour edge generators.
For different base colours the position-preserving term vanishes; the surviving
entry is the mate of `swapCell`, and all mismatched bent labels give zero.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe wk v₁ u₁ u₂ u₃ u₄
namespace LinearCat
variable {k : Type wk} [CommRing k]
theorem mate_hom_app {A B C D : LinearCat.{wk, v₁, u₂} k}
    {L₁ : A ⟶ B} {R₁ : B ⟶ A} {L₂ : C ⟶ D} {R₂ : D ⟶ C}
    {G : A ⟶ C} {H : B ⟶ D} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (τ : G ≫ L₂ ⟶ L₁ ≫ H) (M : (B : Type u₂)) :
    (mateEquiv a₁ a₂ τ).hom.app M =
      a₂.unit.hom.app (G.obj.obj (R₁.obj.obj M)) ≫ R₂.obj.map (τ.hom.app (R₁.obj.obj M)) ≫
        R₂.obj.map (H.obj.map (a₁.counit.hom.app M)) := by
  rw [mateEquiv_eq_comp]
  change 𝟙 _ ≫ a₂.unit.hom.app (G.obj.obj (R₁.obj.obj M)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (τ.hom.app (R₁.obj.obj M)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      R₂.obj.map (H.obj.map (a₁.counit.hom.app M)) ≫ 𝟙 _ = _
  simp
end LinearCat
namespace Furling.MixedEntry
private theorem zero_chain {C : Type*} [Category C] [HasZeroMorphisms C]
    {W X Y Z : C} (a : W ⟶ X) (b : Y ⟶ Z) : a ≫ (0 : X ⟶ Y) ≫ b = 0 := by simp

private theorem zero_map_chain {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (K : C ⥤ D) [K.PreservesZeroMorphisms]
    {W : D} {X Y : C} (a : W ⟶ K.obj X) : a ≫ K.map (0 : X ⟶ Y) = 0 := by simp
variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) k} (D : KLR.Unfurling.UnfurlingDatum k P J)
  {i j : I} {l m n t : X}
  (h₁ : l + RD.iX j = m) (h₂ : m + RD.iX i = t)
  (h₃ : l + RD.iX i = n) (h₄ : n + RD.iX j = t)

abbrev mixed : F Φ S i h₃ ≫ E Φ S j h₁ ⟶ E Φ S j h₄ ≫ F Φ S i h₂ :=
  mateEquiv (adj Φ S i h₃) (adj Φ S i h₂) (cross Φ S D h₁ h₂ h₃ h₄)

abbrev gen (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (p : Φ.Edge j l) (b : J)
    (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) :=
  (Ea Φ S h₁ p (p.tgt h₁) rfl).map
      (incF Φ S h₃ N (swapFst Φ p b hb hrb)) ≫
    genE Φ S j h₁ ((F Φ S i h₃).obj.obj N) ⟨p, rfl⟩

theorem mixed_projF (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (r : Φ.Edge i m) :
    (mixed Φ S D h₁ h₂ h₃ h₄).hom.app N r.src ≫ projF Φ S i h₂ ((E Φ S j h₄).obj.obj N) r =
      (adjA Φ S h₂ r (r.tgt h₂) rfl).unit.app (((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) r.src) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          (genE Φ S i h₂ ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) ⟨r, rfl⟩) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          ((cross Φ S D h₁ h₂ h₃ h₄).hom.app ((F Φ S i h₃).obj.obj N) (r.tgt h₂)) ≫
        (Fa Φ S h₂ r (r.tgt h₂) rfl).map
          ((E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N) (r.tgt h₂)) := by
  rw [LinearCat.mate_hom_app]
  exact comp_chain_three _ _ _ _ _ _ _ _ _ _
    (projF_natural Φ S h₂ ((E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N)) r)
    (projF_natural Φ S h₂ ((cross Φ S D h₁ h₂ h₃ h₄).hom.app ((F Φ S i h₃).obj.obj N)) r)
    (unit_projF Φ S i h₂ ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) r)

theorem map_gen_cross (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (p : Φ.Edge j l) (b : J)
    (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J) (hc : Φ.π c = i)
    (hr : Φ.rel (p.tgt h₁).1 c) :
    (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (gen Φ S h₁ h₃ N p b hb hrb) ≫
        genE Φ S i h₂ ((F Φ S i h₃ ≫ E Φ S j h₁).obj.obj N) ⟨Edge.next h₁ p c hc hr, rfl⟩ ≫
        (cross Φ S D h₁ h₂ h₃ h₄).hom.app ((F Φ S i h₃).obj.obj N)
          ((Edge.next h₁ p c hc hr).tgt h₂) =
      (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((Ea Φ S h₁ p (p.tgt h₁) rfl).map
            (incF Φ S h₃ N (swapFst Φ p b hb hrb))) ≫
        crossNext Φ S D h₁ h₂ h₃ h₄ ((F Φ S i h₃).obj.obj N) p c hc hr rfl :=
  map_comp_chain _ _ _ _ _ _
    (gen₂_cross Φ S D h₁ h₂ h₃ h₄ ((F Φ S i h₃).obj.obj N) p (Edge.next h₁ p c hc hr) rfl rfl)

theorem gen_mixed_projF (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (p : Φ.Edge j l) (b : J)
    (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b) (c : J) (hc : Φ.π c = i)
    (hr : Φ.rel (p.tgt h₁).1 c) :
    gen Φ S h₁ h₃ N p b hb hrb ≫ (mixed Φ S D h₁ h₂ h₃ h₄).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S j h₄).obj.obj N) (Edge.next h₁ p c hc hr) =
      (adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
          ((Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
              ((Ea Φ S h₁ p (p.tgt h₁) rfl).map
                (incF Φ S h₃ N (swapFst Φ p b hb hrb))) ≫
            crossNext Φ S D h₁ h₂ h₃ h₄ ((F Φ S i h₃).obj.obj N) p c hc hr rfl ≫
            (E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N)
              ((Edge.next h₁ p c hc hr).tgt h₂)) := by
  refine (congrArg (gen Φ S h₁ h₃ N p b hb hrb ≫ ·)
    (mixed_projF Φ S D h₁ h₂ h₃ h₄ N (Edge.next h₁ p c hc hr))).trans ?_
  refine (comp_unit_map_chain (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl) _ _ _
    ((Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (gen Φ S h₁ h₃ N p b hb hrb)) _ _ _ _
    ((adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit_naturality
      (gen Φ S h₁ h₃ N p b hb hrb)).symm
    (map_gen_cross Φ S D h₁ h₂ h₃ h₄ N p b hb hrb c hc hr)).trans ?_
  exact congrArg (_ ≫ ·)
    (congrArg (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map (Category.assoc _ _ _))

omit [DecidableEq I] [DecidableEq J] in
theorem cell_counit (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (q : Φ.Edge i l) (d : J)
    (hd : Φ.π d = j) (hrd : Φ.rel (q.tgt h₃).1 d) {δ : Φ.Blk t}
    (hδ : (Edge.next h₃ q d hd hrd).tgt h₄ = δ)
    {y : LinearCat.{wk, v₁, u₂} k} {G₁ : S.obj (Φ.wtT q.src.1) ⟶ y} {G₂ : y ⟶ S.obj (Φ.wtT δ.1)}
    (κ : G₁ ≫ G₂ ⟶ S.E q.lbl (wt_tgt h₃ q rfl) ≫
      S.E d (wt_tgt h₄ (Edge.next h₃ q d hd hrd) hδ)) :
    G₂.obj.map (G₁.obj.map (incF Φ S h₃ N q)) ≫ κ.hom.app ((F Φ S i h₃).obj.obj N q.src) ≫
        gen₂ Φ S h₃ h₄ ((F Φ S i h₃).obj.obj N) q (Edge.next h₃ q d hd hrd) rfl hδ ≫
        (E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N) δ =
      κ.hom.app ((Fa Φ S h₃ q (q.tgt h₃) rfl).obj (N (q.tgt h₃))) ≫
        (Ea Φ S h₄ (Edge.next h₃ q d hd hrd) δ hδ).map
          ((adjA Φ S h₃ q (q.tgt h₃) rfl).counit.app (N (q.tgt h₃))) ≫
        genE Φ S j h₄ N ⟨Edge.next h₃ q d hd hrd, hδ⟩ := by
  refine (cell_chain _ _ _ _ _ _ (comp_cell_natural κ (incF Φ S h₃ N q))
    (map_counit_chain (Ea Φ S h₄ (Edge.next h₃ q d hd hrd) δ hδ)
      ((Ea Φ S h₃ q (q.tgt h₃) rfl).map (incF Φ S h₃ N q)) _ _ _ _ _ _
      (genE_natural Φ S h₄ ((adj Φ S i h₃).counit.hom.app N) ⟨Edge.next h₃ q d hd hrd, hδ⟩)
      ((congrArg (_ ≫ ·) (genE_counit Φ S i h₃ N q)).trans
        (map_section_chain _ _ _ _ (incF_projF Φ S h₃ N q))))).trans ?_
  rfl

omit [DecidableEq I] [DecidableEq J] in
theorem cell_counit_ne (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (q : Φ.Edge i l) (e : J)
    (he : Φ.π e = i) (hre : Φ.rel q.src.1 e) (hne : q.lbl ≠ e) (d : J) (hd : Φ.π d = j)
    (hrd : Φ.rel ((sameSrc Φ q e he hre).tgt h₃).1 d) {δ : Φ.Blk t}
    (hδ : (Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd).tgt h₄ = δ)
    {y : LinearCat.{wk, v₁, u₂} k} {G₁ : S.obj (Φ.wtT q.src.1) ⟶ y} {G₂ : y ⟶ S.obj (Φ.wtT δ.1)}
    (κ : G₁ ≫ G₂ ⟶ S.E e (wt_tgt h₃ (sameSrc Φ q e he hre) rfl) ≫
      S.E d (wt_tgt h₄ (Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd) hδ)) :
    G₂.obj.map (G₁.obj.map (incF Φ S h₃ N q)) ≫ κ.hom.app ((F Φ S i h₃).obj.obj N q.src) ≫
        gen₂ Φ S h₃ h₄ ((F Φ S i h₃).obj.obj N) (sameSrc Φ q e he hre)
          (Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd) rfl hδ ≫
        (E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N) δ = 0 := by
  refine (cell_chain _ _ _ _ _ _ (comp_cell_natural κ (incF Φ S h₃ N q))
    (map_counit_chain (Ea Φ S h₄ (Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd) δ hδ)
      ((Ea Φ S h₃ (sameSrc Φ q e he hre) _ rfl).map (incF Φ S h₃ N q)) _ _ _ _ _ _
      (genE_natural Φ S h₄ ((adj Φ S i h₃).counit.hom.app N)
        ⟨Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd, hδ⟩)
      ((congrArg (_ ≫ ·) (genE_counit Φ S i h₃ N (sameSrc Φ q e he hre))).trans
        (map_zero_chain (Ea Φ S h₃ (sameSrc Φ q e he hre) _ rfl) (incF Φ S h₃ N q)
          (projF Φ S i h₃ N (sameSrc Φ q e he hre))
          ((adjA Φ S h₃ (sameSrc Φ q e he hre) _ rfl).counit.app (N (Edge.tgt h₃ (sameSrc Φ q e he hre))))
          (incF_projF_of_ne Φ S h₃ N q e he hre hne))))).trans ?_
  exact comp_map_zero_comp (Ea Φ S h₄ (Edge.next h₃ (sameSrc Φ q e he hre) d hd hrd) δ hδ) _ _

theorem gen_mixed_projF_swap (hij : i ≠ j)
    (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (p : Φ.Edge j l)
    (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (hr : Φ.rel (p.tgt h₁).1 b) (hs : Φ.rel (p.src.1 + Finsupp.single b 1) p.lbl) :
    gen Φ S h₁ h₃ N p b hb hrb ≫ (mixed Φ S D h₁ h₂ h₃ h₄).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S j h₄).obj.obj N) (Edge.next h₁ p b hb hr) =
      (adjA Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).unit.app _ ≫
        (Fa Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
          ((swapCell S D (i = j) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hr) rfl)
              (wt_tgt h₃ (swapFst Φ p b hb hrb) rfl)
              (wt_tgt h₄ (swapSnd Φ h₃ p b hb hrb hs)
                (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hr hrb hs rfl))).hom.app
              ((Fa Φ S h₃ (swapFst Φ p b hb hrb) _ rfl).obj (N ((swapFst Φ p b hb hrb).tgt h₃))) ≫
            (Ea Φ S h₄ (swapSnd Φ h₃ p b hb hrb hs) _
                (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hr hrb hs rfl)).map
              ((adjA Φ S h₃ (swapFst Φ p b hb hrb) _ rfl).counit.app
                (N ((swapFst Φ p b hb hrb).tgt h₃))) ≫
            genE Φ S j h₄ N ⟨swapSnd Φ h₃ p b hb hrb hs,
              swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hr hrb hs rfl⟩) := by
  refine (gen_mixed_projF Φ S D h₁ h₂ h₃ h₄ N p b hb hrb b hb hr).trans ?_
  apply congrArg (_ ≫ ·)
  apply congrArg (Fa Φ S h₂ (Edge.next h₁ p b hb hr) _ rfl).map
  simp only [crossNext, crossSelf, dite_eq_right hij, add_zero]
  unfold crossSwap
  rw [dite_eq_left_of_eq_true (eq_true ⟨hrb, hs⟩)]
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  exact cell_counit Φ S h₃ h₄ N (swapFst Φ p b hb hrb) p.lbl p.π_lbl hs
    (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hr hrb hs rfl)
    (swapCell S D (i = j) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p b hb hr) rfl)
      (wt_tgt h₃ (swapFst Φ p b hb hrb) rfl)
      (wt_tgt h₄ (swapSnd Φ h₃ p b hb hrb hs)
        (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p b hb hr hrb hs rfl)))

theorem gen_mixed_projF_ne (hij : i ≠ j)
    (N : ∀ γ : Φ.Blk n, blkCat Φ S γ.1) (p : Φ.Edge j l)
    (b : J) (hb : Φ.π b = i) (hrb : Φ.rel p.src.1 b)
    (c : J) (hc : Φ.π c = i) (hr : Φ.rel (p.tgt h₁).1 c) (hbc : b ≠ c) :
    gen Φ S h₁ h₃ N p b hb hrb ≫ (mixed Φ S D h₁ h₂ h₃ h₄).hom.app N (p.tgt h₁) ≫
        projF Φ S i h₂ ((E Φ S j h₄).obj.obj N) (Edge.next h₁ p c hc hr) = 0 := by
  refine (gen_mixed_projF Φ S D h₁ h₂ h₃ h₄ N p b hb hrb c hc hr).trans ?_
  have hz : (Ea Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map
      ((Ea Φ S h₁ p (p.tgt h₁) rfl).map (incF Φ S h₃ N (swapFst Φ p b hb hrb))) ≫
      crossNext Φ S D h₁ h₂ h₃ h₄ ((F Φ S i h₃).obj.obj N) p c hc hr rfl ≫
      (E Φ S j h₄).obj.map ((adj Φ S i h₃).counit.hom.app N)
        ((Edge.next h₁ p c hc hr).tgt h₂) = 0 := by
    simp only [crossNext, crossSelf, dite_eq_right hij, add_zero]
    unfold crossSwap
    split_ifs with hs
    · refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
      exact cell_counit_ne Φ S h₃ h₄ N (swapFst Φ p b hb hrb) c hc hs.1 hbc p.lbl p.π_lbl hs.2
        (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p c hc hr hs.1 hs.2 rfl)
        (swapCell S D (i = j) (wt_tgt h₁ p rfl) (wt_tgt h₂ (Edge.next h₁ p c hc hr) rfl)
          (wt_tgt h₃ (swapFst Φ p c hc hs.1) rfl)
          (wt_tgt h₄ (swapSnd Φ h₃ p c hc hs.1 hs.2)
            (swapSnd_tgt Φ h₁ h₂ h₃ h₄ p c hc hr hs.1 hs.2 rfl)))
    · exact zero_chain _ _
  exact (congrArg (fun f => (adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _ ≫
    (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).map f) hz).trans
      (zero_map_chain (Fa Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl)
        ((adjA Φ S h₂ (Edge.next h₁ p c hc hr) _ rfl).unit.app _))

end Furling.MixedEntry
end Categorification.TwoRep
