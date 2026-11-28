/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionQ
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackAppend
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackMatrix
import Categorification.Diagrams.KLR.MatEndNatEmbSigma

/-!
# The black action on the appended strands of an all-down boundary

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.31, and §4.6. A Cautis–Lauda diagram `ψ` acts on the
violating quotient by placing its mirror image to the right of every boundary (`blackMapQ`).
At an all-down boundary its component is the mirror diagram on the strands appended on the right
(`whiskerLeft_app_hom_diag`).

* For the dot on the downward strand `Fᵢ` (`dnDotQ`), the component is the dot on the last strand
  of the appended all-down boundary (`natEntry_blackMapQ_dot`), so the diagonal matrix of the
  black-action dot (`MatEnd.natEmb`) is `x_n` times the image of the unit under the matrix map of
  `Fᵢ` (`natEmb_blackMapQ_dot`).
* For the crossing of two downward strands `Fᵢ` (`dnCrossQ`), transported to `Fᵢ ⋙ Fᵢ`
  (`crossNatQ`), the component is the crossing of the last two strands
  (`natEntry_blackMapQ_cross`, `natEntry_crossNatQ`), and the diagonal matrix is `ψ_n` times the
  image of the unit under the matrix map of `FᵢFᵢ` (`natEmb_crossNatQ`).

These identify the dot and crossing of the categorical action of `U_Q(g)` (Cautis–Lauda,
arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) with those of Webster's induction
functors on modules over `T^λ` (arXiv:1309.3796v3, §5.1).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
open scoped Classical

section Generic

variable {S : Signature} {k : Type*} [CommRing k] (Pr : Presentation S k)

/-- Two diagrams with the same layers, framed by transports, have the same class. -/
theorem diag_conj_eq {c c' a b a' b' : Obj S} (D₁ : a ⟶ b) (D₂ : a' ⟶ b')
    (h₁ : Pr.obj c = Pr.obj a) (h₂ : Pr.obj b = Pr.obj c') (h₁' : Pr.obj c = Pr.obj a')
    (h₂' : Pr.obj b' = Pr.obj c') (hl : Diagram.layers D₁ = Diagram.layers D₂) :
    eqToHom h₁ ≫ Pr.diag D₁ ≫ eqToHom h₂ = eqToHom h₁' ≫ Pr.diag D₂ ≫ eqToHom h₂' := by
  obtain rfl := Pr.obj_injective (h₁.symm.trans h₁')
  obtain rfl := Pr.obj_injective (h₂.trans h₂'.symm)
  rw [Pr.diag_eq_of_layers_eq hl]

end Generic

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

/-- The mirror of a Cautis–Lauda diagram is the class of the mirrored diagram. -/
theorem blackMirrorHomQ_diag {μ : X} {s t : List (Letter I)} (d : ob RD μ s ⟶ ob RD μ t) :
    blackMirrorHomQ P hP ((CLQ.pres RD k sc).diag d) =
      P.diag (Diagram.cast ((blackMirror RD (fun r => (Λ r).val)).toLayerMap.map d)
        (blackMirror_obj_ob RD _ μ s) (blackMirror_obj_ob RD _ μ t)) := by
  refine Eq.trans ?_ (P.diag_cast _ _ _).symm
  unfold blackMirrorHomQ conjMap
  rw [Presentation.diag, blackMirrorIntoOf_lin, blackMirrorLinear_of]
  rfl

/-- The component of a whiskered diagram at a boundary is the diagram placed to the right of
the boundary word. -/
theorem whiskerLeft_app_hom_diag {μ ν : X} {v v' : List (DoubleStrand I ℓ)} (hv : RedFree v)
    (hv' : RedFree v') (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν)
    (D : obj RD (fun r => (Λ r).val) μ v ⟶ obj RD (fun r => (Λ r).val) μ v')
    (x : BoundaryCategory P μ) :
    ((whiskerLeft P hv hv' hν hν' (P.diag D)).app x).hom =
      eqToHom (tripleObj_appendRight P v hv hν x) ≫
        P.diag (Diagram.lwhisker (obj RD (fun r => (Λ r).val) 0 x.val.word) D
          (composable P x v)) ≫
          eqToHom (tripleObj_appendRight P v' hv' hν' x).symm := by
  rw [whiskerLeft_app_hom, P.wL_diag_of_composable _ _ (composable P x v)]

section Dot

variable (i : I) (ν : Multiset I)

/-- The position of the appended strand. -/
def lastPos : Fin (Multiset.card (stendhalWeight ℓ ({i} + ν))) :=
  ⟨Multiset.card (stendhalWeight ℓ ν), by rw [card_stendhalWeight_cons]; omega⟩

/-- The dot on the downward strand `Fᵢ`, as a Cautis–Lauda diagram. -/
def dnDotQ (μ : X) :
    (CLQ.pres RD k sc).obj (ob RD μ [dn i]) ⟶ (CLQ.pres RD k sc).obj (ob RD μ [dn i]) :=
  (CLQ.pres RD k sc).diag (mkD RD μ [([], .dot (dn i), [])] (by schain))

/-- **The black-action dot on the appended strand is the dot on the last strand.** -/
theorem natEntry_blackMapQ_dot (s : {s : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    KLR.Diagram.MatEnd.natEntry (blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν))
        (blackAct_downObj P i)
        (blackMapQ P hP (wt_downRightWeight (Λ := Λ) i ν) (wt_downRightWeight (Λ := Λ) i ν)
          (dnDotQ i _)) s =
      downDot P (appendDown i s) (lastPos i ν) := by
  have hl : (appendDown i s).val.lbl (lastPos i ν) = .inl i :=
    appendBlackLoading_lbl_of_eq i ν s.val _ rfl
  rw [downDot_of_black P _ _ i hl]
  unfold KLR.Diagram.MatEnd.natEntry downBlackDot downLayer
  have happ : (blackMapQ P hP (wt_downRightWeight (Λ := Λ) i ν) (wt_downRightWeight (Λ := Λ) i ν)
      (dnDotQ i _)).app (downObj P s) = (violatingFunctor P _).map
        ((whiskerLeft P _ _ _ _ (blackMirrorHomQ P hP (dnDotQ i _))).app (downTriple RD Λ s)) :=
    rfl
  rw [happ, show eqToHom (blackAct_downObj P i s) = (violatingFunctor P _).map
      (eqToHom (appendRight_downTriple i ν s)) from (eqToHom_map _ _).symm,
    show eqToHom (blackAct_downObj P i s).symm = (violatingFunctor P _).map
      (eqToHom (appendRight_downTriple i ν s).symm) from (eqToHom_map _ _).symm,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  simp only [InducedCategory.comp_hom, inducedCategory_eqToHom_hom, InducedCategory.homMk_hom]
  rw [dnDotQ, blackMirrorHomQ_diag, whiskerLeft_app_hom_diag]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Presentation.layer]
  rw [← Category.id_comp (P.diag (Diagram.layer _ _ _ _)),
    ← Category.comp_id (P.diag (Diagram.layer _ _ _ _)), ← eqToHom_refl _ rfl]
  apply diag_conj_eq
  simp only [Diagram.layers_lwhisker, Diagram.layers_cast, LayerMap.layers_map, layers_mkD,
    layList, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  have hw := word_appendDown i s
  have hn : (KLR.Diagram.word s.val).length = (lastPos (ℓ := ℓ) i ν : ℕ) := by
    simp [KLR.Diagram.word, lastPos]
  have ht : ((KLR.Diagram.word (appendBlackLoading i ν s.val)).take (lastPos (ℓ := ℓ) i ν)).map
      DoubleStrand.down = (KLR.Diagram.word s.val).map DoubleStrand.down := by
    rw [List.map_take, hw, List.take_left' (by simpa using hn)]
  have hd : ((KLR.Diagram.word (appendBlackLoading i ν s.val)).drop (lastPos (ℓ := ℓ) i ν + 1)).map
      DoubleStrand.down = [] := by
    rw [List.map_drop, hw, List.drop_eq_nil_iff]
    simp [hn]
  rw [ht, hd]
  have hr := endWeight_word (downTriple RD Λ s)
  apply Layer.ext
  · rfl
  · change (obj RD (fun r => (Λ r).val) 0 (downTriple RD Λ s).val.word).word ++ [] = _
    rw [List.append_nil]
    rfl
  · exact Prod.ext hr.symm rfl
  · rfl

/-- **The diagonal matrix of the black-action dot is the dot on the appended strand**: it is
`x_n` times the image of the unit under the matrix map of `Fᵢ`. -/
theorem natEmb_blackMapQ_dot :
    KLR.Diagram.MatEnd.natEmb (blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν))
        (blackAct_downObj P i)
        (blackMapQ P hP (wt_downRightWeight (Λ := Λ) i ν) (wt_downRightWeight (Λ := Λ) i ν)
          (dnDotQ i _)) =
      downX P (lastPos i ν) * blackMatrix P i 1 := by
  rw [blackMatrix_apply, KLR.Diagram.MatEnd.mapEmb_one, Finset.mul_sum,
    KLR.Diagram.MatEnd.natEmb]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [natEntry_blackMapQ_dot, downX, Finset.sum_mul, Finset.sum_eq_single (appendDown i s)]
  · rw [KLR.Diagram.MatEnd.single_mul_single, Category.id_comp]
  · intro t _ ht
    exact KLR.Diagram.MatEnd.single_mul_single_of_ne _ _ (Ne.symm ht)
  · simp

end Dot

section Cross

variable (i : I) (ν : Multiset I)

/-- The weight equation of the word `FᵢFᵢ` between the all-down weights. -/
theorem wt_downRightWeight₂ :
    wt RD (downRightWeight RD Λ ν) [(false, i), (false, i)] =
      downRightWeight RD Λ ({i} + ({i} + ν)) := by
  rw [show ([(false, i), (false, i)] : List (Letter I)) = [(false, i)] ++ [(false, i)] from rfl,
    wt_append, wt_downRightWeight, wt_downRightWeight]

/-- Appending `FᵢFᵢ` to an all-down triple gives the all-down triple of the twice appended
loading. -/
theorem appendRight_downTriple₂ (s : {s : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    appendRight (blackWord [(false, i), (false, i)]) (blackWord_redFree _)
        ((endWeight_blackWord RD _ _ _).trans (wt_downRightWeight₂ i ν)) (downTriple RD Λ s) =
      downTriple RD Λ (appendDown i (appendDown i s)) := by
  apply Subtype.ext
  apply DoubleBoundary.ext
  change (List.ofFn s.val.lbl).map DoubleStrand.down ++ _ =
    (List.ofFn (appendBlackLoading i _ (appendBlackLoading i ν s.val)).lbl).map DoubleStrand.down
  rw [ofFn_appendBlackLoading, ofFn_appendBlackLoading]
  simp [blackWord, DoubleStrand.down]

/-- The action of `FᵢFᵢ` on an all-down boundary object. -/
theorem blackAct₂_downObj (s : {s : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    (blackAct P [(false, i), (false, i)] (wt_downRightWeight₂ i ν)).obj (downObj P s) =
      downObj P (appendDown i (appendDown i s)) :=
  congrArg (violatingFunctor P _).obj (appendRight_downTriple₂ i ν s)

/-- The crossing of two downward strands `Fᵢ`, as a Cautis–Lauda diagram. -/
def dnCrossQ (μ : X) :
    (CLQ.pres RD k sc).obj (ob RD μ [dn i, dn i]) ⟶ (CLQ.pres RD k sc).obj (ob RD μ [dn i, dn i]) :=
  (CLQ.pres RD k sc).diag (mkD RD μ [([], .cross false i i, [])] (by schain))

/-- **The black-action crossing on the appended strands is the crossing of the last two
strands.** -/
theorem natEntry_blackMapQ_cross (s : {s : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    KLR.Diagram.MatEnd.natEntry (blackAct P [(false, i), (false, i)] (wt_downRightWeight₂ i ν))
        (blackAct₂_downObj P i ν)
        (blackMapQ P hP (wt_downRightWeight₂ i ν) (wt_downRightWeight₂ i ν) (dnCrossQ i _)) s =
      downCross P (appendDown i (appendDown i s)) (appendDown i (appendDown i s))
        (Multiset.card (stendhalWeight ℓ ν)) := by
  set t := appendDown i (appendDown i s) with ht_def
  have hc : Multiset.card (stendhalWeight ℓ ({i} + ({i} + ν))) =
      Multiset.card (stendhalWeight ℓ ν) + 2 := by
    rw [card_stendhalWeight_cons, card_stendhalWeight_cons]
  have hj : Multiset.card (stendhalWeight ℓ ν) + 1 <
      Multiset.card (stendhalWeight ℓ ({i} + ({i} + ν))) := by omega
  have h1 : t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν), by omega⟩ = .inl i := by
    rw [ht_def, appendBlackLoading_lbl_of_lt i _ _ _
      (by have := card_stendhalWeight_cons (ℓ := ℓ) i ν; dsimp only; omega)]
    exact appendBlackLoading_lbl_of_eq i ν _ _ rfl
  have h2 : t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν) + 1, hj⟩ = .inl i :=
    appendBlackLoading_lbl_of_eq i _ _ _
      (by have := card_stendhalWeight_cons (ℓ := ℓ) i ν; dsimp only; omega)
  have hts : t.val = TypeA.sadj _ (Multiset.card (stendhalWeight ℓ ν)) • t.val :=
    (KLR.Diagram.sadj_smul_eq_self t.val hj ((h1.trans h2.symm))).symm
  have hg : downCrossMove (t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν), by omega⟩)
      (t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν) + 1, hj⟩) =
        some (.black (.cross false i i)) := by
    rw [h1, h2]
    rfl
  rw [downCross_of_move P t t _ hj hts _ hg]
  unfold KLR.Diagram.MatEnd.natEntry downCrossLayer downLayer
  have happ : (blackMapQ P hP (wt_downRightWeight₂ i ν) (wt_downRightWeight₂ i ν)
      (dnCrossQ i _)).app (downObj P s) = (violatingFunctor P _).map
        ((whiskerLeft P _ _ _ _ (blackMirrorHomQ P hP (dnCrossQ i _))).app
          (downTriple RD Λ s)) :=
    rfl
  rw [happ, show eqToHom (blackAct₂_downObj P i ν s) = (violatingFunctor P _).map
      (eqToHom (appendRight_downTriple₂ i ν s)) from (eqToHom_map _ _).symm,
    show eqToHom (blackAct₂_downObj P i ν s).symm = (violatingFunctor P _).map
      (eqToHom (appendRight_downTriple₂ i ν s).symm) from (eqToHom_map _ _).symm,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  simp only [InducedCategory.comp_hom, inducedCategory_eqToHom_hom, InducedCategory.homMk_hom]
  rw [dnCrossQ, blackMirrorHomQ_diag, whiskerLeft_app_hom_diag]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Presentation.layer]
  rw [← Category.id_comp (P.diag (Diagram.layer _ _ _ _)),
    ← Category.comp_id (P.diag (Diagram.layer _ _ _ _)), ← eqToHom_refl _ rfl]
  apply diag_conj_eq
  simp only [Diagram.layers_lwhisker, Diagram.layers_cast, LayerMap.layers_map, layers_mkD,
    layList, Diagram.layers_layer, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  have hw : (KLR.Diagram.word t.val).map DoubleStrand.down =
      (KLR.Diagram.word s.val).map DoubleStrand.down ++
        [.inl (false, i), .inl (false, i)] := by
    rw [ht_def, word_appendDown, word_appendDown, List.append_assoc]
    rfl
  have hn : ((KLR.Diagram.word s.val).map DoubleStrand.down).length =
      Multiset.card (stendhalWeight ℓ ν) := by
    simp [KLR.Diagram.word]
  rw [List.map_take, List.map_drop, hw, List.take_left' hn, List.drop_eq_nil_of_le
    (by simp [hn])]
  have hr := endWeight_word (downTriple RD Λ s)
  apply Layer.ext
  · rfl
  · change (obj RD (fun r => (Λ r).val) 0 (downTriple RD Λ s).val.word).word ++ [] = _
    rw [List.append_nil]
    rfl
  · exact Prod.ext hr.symm rfl
  · rfl

/-- The black-action crossing as a natural endomorphism of `Fᵢ ⋙ Fᵢ`. -/
def crossNatQ :
    blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν) ⋙
        blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ({i} + ν)) ⟶
      blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν) ⋙
        blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ({i} + ν)) :=
  eqToHom (blackAct_append_eq P [(false, i)] [(false, i)] (wt_downRightWeight (Λ := Λ) i ν)
      (wt_downRightWeight (Λ := Λ) i ({i} + ν)) (wt_downRightWeight₂ i ν)).symm ≫
    blackMapQ P hP (wt_downRightWeight₂ i ν) (wt_downRightWeight₂ i ν) (dnCrossQ i _) ≫
    eqToHom (blackAct_append_eq P [(false, i)] [(false, i)] (wt_downRightWeight (Λ := Λ) i ν)
      (wt_downRightWeight (Λ := Λ) i ({i} + ν)) (wt_downRightWeight₂ i ν))

theorem natEntry_crossNatQ (s : {s : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    KLR.Diagram.MatEnd.natEntry (blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν) ⋙
        blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ({i} + ν)))
        (KLR.Diagram.MatEnd.compEq _ _ (blackAct_downObj P i) (blackAct_downObj P i))
        (crossNatQ P hP i ν) s =
      downCross P (appendDown i (appendDown i s)) (appendDown i (appendDown i s))
        (Multiset.card (stendhalWeight ℓ ν)) := by
  rw [← natEntry_blackMapQ_cross P hP i ν s]
  simp only [KLR.Diagram.MatEnd.natEntry, crossNatQ, NatTrans.comp_app, eqToHom_app,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **The diagonal matrix of the black-action crossing is the crossing of the appended
strands**: it is `ψ_n` times the image of the unit under the matrix map of `FᵢFᵢ`. -/
theorem natEmb_crossNatQ :
    KLR.Diagram.MatEnd.natEmb (blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ν) ⋙
        blackAct P [(false, i)] (wt_downRightWeight (Λ := Λ) i ({i} + ν)))
        (KLR.Diagram.MatEnd.compEq _ _ (blackAct_downObj P i) (blackAct_downObj P i))
        (crossNatQ P hP i ν) =
      downΨ P (Multiset.card (stendhalWeight ℓ ν)) *
        blackMatrix P i (blackMatrix P i 1) := by
  rw [blackMatrix_apply, blackMatrix_apply, ← KLR.Diagram.MatEnd.mapEmb_comp,
    KLR.Diagram.MatEnd.mapEmb_one, Finset.mul_sum, KLR.Diagram.MatEnd.natEmb]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [natEntry_crossNatQ]
  set t := appendDown i (appendDown i s) with ht_def
  change KLR.Diagram.MatEnd.single t t _ = downΨ P _ * KLR.Diagram.MatEnd.single t t (𝟙 _)
  have hc : Multiset.card (stendhalWeight ℓ ({i} + ({i} + ν))) =
      Multiset.card (stendhalWeight ℓ ν) + 2 := by
    rw [card_stendhalWeight_cons, card_stendhalWeight_cons]
  have hj : Multiset.card (stendhalWeight ℓ ν) + 1 <
      Multiset.card (stendhalWeight ℓ ({i} + ({i} + ν))) := by omega
  have h1 : t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν), by omega⟩ = .inl i := by
    rw [ht_def, appendBlackLoading_lbl_of_lt i _ _ _
      (by have := card_stendhalWeight_cons (ℓ := ℓ) i ν; dsimp only; omega)]
    exact appendBlackLoading_lbl_of_eq i ν _ _ rfl
  have h2 : t.val.lbl ⟨Multiset.card (stendhalWeight ℓ ν) + 1, hj⟩ = .inl i :=
    appendBlackLoading_lbl_of_eq i _ _ _
      (by have := card_stendhalWeight_cons (ℓ := ℓ) i ν; dsimp only; omega)
  have hts : TypeA.sadj _ (Multiset.card (stendhalWeight ℓ ν)) • t.val = t.val :=
    KLR.Diagram.sadj_smul_eq_self t.val hj (h1.trans h2.symm)
  funext a d
  rw [KLR.Diagram.MatEnd.mul_apply]
  by_cases ha : a = t
  · subst ha
    rw [Finset.sum_eq_single t]
    · rw [KLR.Diagram.MatEnd.single_apply_self, Category.id_comp]
      by_cases hd : d = t
      · subst hd
        rw [KLR.Diagram.MatEnd.single_apply_self]
        rfl
      · rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => hd h.2)]
        refine (downCross_of_not_adj P t d _ fun h => hd (Subtype.ext ?_)).symm
        rw [h, hts]
    · intro c _ hc
      rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => hc h.2), Limits.zero_comp]
    · simp
  · rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => ha h.1)]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [KLR.Diagram.MatEnd.single_apply_of_ne _ (fun h => ha h.1), Limits.zero_comp]

end Cross

end Categorification.Stendhal.DoubleDiagram
