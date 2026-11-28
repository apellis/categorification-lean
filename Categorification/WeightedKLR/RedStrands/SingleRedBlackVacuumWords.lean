/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqWordBlocks
import Categorification.WeightedKLR.RedStrands.SingleRedBlackInductionIdeal
import Categorification.WeightedKLR.RedStrands.SingleRedBlackVacuumIsoId

set_option backward.isDefEq.respectTransparency false

/-!
# The derived action on `F_𝐢 T^λ_∅`, one red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22 (b), for one red strand: the derived action of Theorem 4.31 sends the vacuum
`T^λ_∅` to `F_𝐢 T^λ_∅ ≅ e(𝐢) T^λ_ν` (in degree `0`, at the block `ν` of the content of `𝐢`).

* `upWord t`: the word `F_{t₀} ⋯ F_{tₙ}` of upward letters (the leftmost acts last), and
  `wt_upWord`: its left region is the weight of the block `t`;
* `listSeq t`: the sequence `tₙ ⋯ t₀` (the order in which the strands are added, left to
  right), and `appendSeq_listSeq`;
* **`upWordBlockIso`**: the block `t` of `F_{t₀} ⋯ F_{tₙ} T^λ_∅` is `e(tₙ ⋯ t₀) T^λ` in degree
  `0`, by induction on the word: one strand at a time (`blackPresCLMapUpBlockIso`), derived
  induction of a single module (`derivedFOfEqSingleRedFirstIdealIso`);
* **`vacuumSeqHom`, `vacuumSeqBlockIso`**: for every sequence `𝐢` of content `ν`, a 1-morphism
  `F_𝐢` out of the vacuum region into the region of `ν`, with `(F_𝐢 T^λ_∅)_ν ≅ e(𝐢) T^λ_ν`.
  This is the input `W` of `SingleRed.blackVacuumDerivedTensorIsoId` for `C₀ = T^λ_∅`.

The hypotheses are those of `blackPresCL`, including the route hypothesis `hΛ₀` of
`blackRouqFamily`.
-/

open CategoryTheory CategoryTheory.Limits MulOpposite

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra TwoRep QuantumGroup KL3.Diagram CyclotomicAction DoubleDiagram StringDiagrams
open scoped Classical
open Pseudofunctor.StrongTrans

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u₁

variable {I : Type} {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 1 → I →₀ ℕ}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : UDot.WeightDatum C X Y} {Λ₀ : X}

/-! ### Words and sequences -/

/-- The word `F_{t₀} ⋯ F_{tₙ}` of upward letters. -/
abbrev upWord (t : List I) : List (Letter I) := t.map up

variable (RD Λ₀) in
/-- The left region of `F_{t₀} ⋯ F_{tₙ} 1_{λ}` is the weight of the block `t`. -/
theorem wt_upWord (t : List I) :
    KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t) = blockWeight RD Λ₀ (t : Multiset I) := by
  induction t with
  | nil => rfl
  | cons i t ih =>
    change KL3.Diagram.wt RD _ (up i :: upWord t) = _
    have hsh : sh RD (up i) = RD.iX i := by simp [sh]
    rw [wt_cons, ih, hsh, show ((i :: t : List I) : Multiset I) = {i} + (t : Multiset I) by
      rw [Multiset.singleton_add, Multiset.cons_coe], blockWeight_cons, add_comm]

/-- The sequence `tₙ ⋯ t₀`, the order in which `F_{t₀} ⋯ F_{tₙ}` adds strands. -/
def listSeq (t : List I) : Seq (t : Multiset I) := Seq.ofList t.reverse (Multiset.coe_reverse t)

theorem cons_coe_eq (i : I) (t : List I) :
    ({i} : Multiset I) + (t : Multiset I) = ((i :: t : List I) : Multiset I) := by
  rw [Multiset.singleton_add, Multiset.cons_coe]

theorem appendSeq_listSeq (i : I) (t : List I) :
    appendSeq i (cons_coe_eq i t) (listSeq t) = listSeq (i :: t) := by
  apply Subtype.ext
  funext a
  have hlen : Multiset.card (t : Multiset I) = t.length := Multiset.coe_card t
  change ((listSeq t).append (default : Seq ({i} : Multiset I))).1 (Fin.cast _ a) =
    (Seq.ofList (i :: t).reverse (Multiset.coe_reverse (i :: t))).lbl a
  rw [Seq.ofList_lbl]
  have h2 : Multiset.card ((i :: t : List I) : Multiset I) = t.length + 1 := by simp
  have h1 := a.2
  by_cases ha : (a : ℕ) < t.length
  · rw [Seq.append_apply_lt _ _ _ (by rw [hlen]; exact ha)]
    change (Seq.ofList t.reverse (Multiset.coe_reverse t)).lbl _ = _
    rw [Seq.ofList_lbl]
    simp only [List.reverse_cons]
    rw [List.getElem_append_left]
    rfl
  · rw [Seq.append_apply_ge _ _ _ (by rw [hlen]; exact Nat.le_of_not_lt ha)]
    rw [Multiset.mem_singleton.mp (Seq.mem (default : Seq ({i} : Multiset I)) _)]
    simp only [List.reverse_cons]
    have ha' : (a : ℕ) = t.reverse.length := by
      rw [List.length_reverse]
      omega
    simp only [ha', List.getElem_concat_length]

/-- A list whose multiset is `ν`, read off a sequence (in reverse, so that `listSeq` of it is
the sequence). -/
def seqWord {ν : Multiset I} (s : Seq ν) : List I := (List.ofFn s.lbl).reverse

theorem coe_seqWord {ν : Multiset I} (s : Seq ν) : ((seqWord s : List I) : Multiset I) = ν := by
  rw [seqWord, Multiset.coe_reverse]
  have := s.2
  rwa [Fin.univ_val_map] at this

theorem listSeq_seqWord {ν : Multiset I} (s : Seq ν) :
    Seq.cast (coe_seqWord s) (listSeq (seqWord s)) = s := by
  apply Subtype.ext
  funext a
  rw [Seq.cast_apply]
  change (Seq.ofList (seqWord s).reverse (Multiset.coe_reverse _)).lbl _ = _
  rw [Seq.ofList_lbl]
  simp only [seqWord, List.reverse_reverse, Fin.val_cast, List.getElem_ofFn]

/-! ### The blocks of `F_𝐢 T^λ_∅` -/

variable {hQ : IsRouquierQ C Q}
  {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 :
      I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin 1, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

set_option hygiene false in
local notation "𝕊" β => (DerivedCategory.singleFunctor
  (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ) 0)

/-- The right regular module `T` is the left ideal `Tᵐᵒᵖ · 1` of `Tᵐᵒᵖ`. -/
def regularOpLinearEquiv (T : Type) [Ring T] {e : Tᵐᵒᵖ} (he : e = 1) :
    T ≃ₗ[Tᵐᵒᵖ] idemLeftIdeal e where
  toFun x := ⟨op x, by rw [mem_idemLeftIdeal, he, mul_one]⟩
  invFun y := unop y.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [∀ β : Multiset I,
    _root_.HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)] in
theorem redFirstIdem_zero (s : Seq (0 : Multiset I)) : redFirstIdem Q Λ 0 s = 1 := by
  have : Subsingleton (Seq (0 : Multiset I)) :=
    ⟨fun _ _ => Subtype.ext (funext fun a => (a : Fin 0).elim0)⟩
  rw [← sum_redFirstIdem Q Λ 0, Fintype.sum_subsingleton _ s]

theorem blackRegularVacuum_zero (p : blockWeight RD Λ₀ (0 : Multiset I) = blockWeight RD Λ₀ 0) :
    blackRegularVacuum Q Λ RD Λ₀ ⟨0, p⟩ = (𝕊 0).obj
      (ModuleCat.of (TensorProductAlgebra k Q Λ 0)ᵐᵒᵖ (TensorProductAlgebra k Q Λ 0)) := by
  unfold blackRegularVacuum
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- **The block `t` of `F_{t₀} ⋯ F_{tₙ} T^λ_∅` is `e(tₙ ⋯ t₀) T^λ` in degree `0`** (Webster,
arXiv:1309.3796v3, §4.6 and proof of Proposition 7.22 (b), one red strand), for the word
`upWord t` out of the vacuum region into any region `c` equal to its left region. -/
def upWordBlockIso : (t : List I) → {c : X} →
    (hc : KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t) = c) →
    (p : blockWeight RD Λ₀ (t : Multiset I) = c) →
    (blackBlockEval hP hwf hΛ₀ hsym (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
        ⟨(t : Multiset I), p⟩).obj
        (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map
          (vacHom (k := k) hQ RD Λ₀ (upWord t) hc)).obj.obj
          (blackRegularVacuum Q Λ RD Λ₀)) ≅
      (𝕊 (t : Multiset I)).obj (ModuleCat.of _
        (idemLeftIdeal (redFirstIdem Q Λ (t : Multiset I) (listSeq t))))
  | [], _, hc, p => by
    subst hc
    refine eqToIso ?_ ≪≫ (𝕊 0).mapIso
      (regularOpLinearEquiv _ (redFirstIdem_zero (Q := Q) (Λ := Λ) (listSeq []))).toModuleIso
    exact blackRegularVacuum_zero (Q := Q) (Λ := Λ) (RD := RD) p
  | i :: t, c, hc, p => by
    let x := vacHom (k := k) hQ RD Λ₀ (upWord (i :: t)) hc
    let c₁ : Col I X := ⟨up i, KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t)⟩
    have hw : (LinearCat.revHom x).obj.word = c₁ :: wd RD (vacWt RD Λ₀) (upWord t) := rfl
    let tl : vacRegion hQ RD Λ₀ ⟶
        (⟨⟨(KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t) : X)⟩⟩ :
          RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :=
      (CL.presCL RD k (univScalars hQ RD)).tailHom (LinearCat.revHom x) c₁ _ hw
    let hd : (⟨⟨(KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t) : X)⟩⟩ :
        RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) ⟶ ⟨⟨c⟩⟩ :=
      (CL.presCL RD k (univScalars hQ RD)).headHom (LinearCat.revHom x) c₁ _ hw
    have hxy : x = tl ≫ hd :=
      ((CL.presCL RD k (univScalars hQ RD)).headHom_comp_tailHom (LinearCat.revHom x) c₁ _ hw).symm
    have htl : tl = vacHom (k := k) hQ RD Λ₀ (upWord t) rfl := rfl
    have hβ : ({i} : Multiset I) + (t : Multiset I) = ((i :: t : List I) : Multiset I) :=
      cons_coe_eq i t
    refine eqToIso (congrArg (fun y : vacRegion hQ RD Λ₀ ⟶
        (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) =>
          (blackBlockEval hP hwf hΛ₀ hsym _ _).obj
        (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map y).obj.obj
          (blackRegularVacuum Q Λ RD Λ₀))) hxy) ≪≫
      (blackBlockEval hP hwf hΛ₀ hsym _ _).mapIso
        (((ObjectProperty.ι _).mapIso
          ((Stendhal.blackPresCL hP hwf hΛ₀ hsym).mapComp tl hd)).app _) ≪≫
      blackPresCLMapUpBlockIso hP hwf hΛ₀ hsym hd i _ rfl _
        ⟨(t : Multiset I), (wt_upWord RD Λ₀ t).symm⟩ ⟨_, p⟩ hβ ≪≫
      (derivedFOfEq Λ hQ i hβ).mapIso
        (upWordBlockIso t rfl (wt_upWord RD Λ₀ t).symm) ≪≫
      derivedFOfEqSingleRedFirstIdealIso Q Λ hQ i hβ (listSeq t) ≪≫
      (𝕊 _).mapIso (eqToIso (by rw [appendSeq_listSeq]))

/-- `upWordBlockIso` at the block `ν`, for a word `t` of content `ν`. -/
def upWordBlockIsoOfEq (t : List I) {ν : Multiset I} (h : (t : Multiset I) = ν)
    (hc : KL3.Diagram.wt RD (vacWt RD Λ₀) (upWord t) = blockWeight RD Λ₀ ν) :
    (blackBlockEval hP hwf hΛ₀ hsym (⟨⟨(blockWeight RD Λ₀ ν : X)⟩⟩ :
          RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) ⟨ν, rfl⟩).obj
        (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map
          (vacHom (k := k) hQ RD Λ₀ (upWord t) hc)).obj.obj (blackRegularVacuum Q Λ RD Λ₀)) ≅
      (𝕊 ν).obj (ModuleCat.of _ (idemLeftIdeal (redFirstIdem Q Λ ν (Seq.cast h (listSeq t))))) := by
  subst h
  exact upWordBlockIso hP hwf hΛ₀ hsym t hc rfl

variable (hQ RD Λ₀) in
/-- **`F_𝐢` out of the vacuum region**, for a sequence `𝐢` of content `ν`: the word
`F_{iₙ} ⋯ F_{i₁}` (the strand `i₁` is added first, on the left). -/
def vacuumSeqHom {ν : Multiset I} (s : Seq ν) :
    vacRegion hQ RD Λ₀ ⟶ (⟨⟨(blockWeight RD Λ₀ ν : X)⟩⟩ :
      RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :=
  vacHom (k := k) hQ RD Λ₀ (upWord (seqWord s)) (by rw [wt_upWord, coe_seqWord])

/-- **`(F_𝐢 T^λ_∅)_ν ≅ e(𝐢) T^λ_ν`** in degree `0` (Webster, arXiv:1309.3796v3, §4.6 and proof
of Proposition 7.22 (b), one red strand): the input `W` of
`SingleRed.blackVacuumDerivedTensorIsoId` for the vacuum `C₀ = T^λ_∅`. -/
def vacuumSeqBlockIso {ν : Multiset I} (s : Seq ν) :
    (blackBlockEval hP hwf hΛ₀ hsym (⟨⟨(blockWeight RD Λ₀ ν : X)⟩⟩ :
          RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) ⟨ν, rfl⟩).obj
        (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map
          (vacuumSeqHom (k := k) (hQ := hQ) (RD := RD) (Λ₀ := Λ₀) s)).obj.obj
            (blackRegularVacuum Q Λ RD Λ₀)) ≅
      (𝕊 ν).obj (ModuleCat.of _ (idemLeftIdeal (redFirstIdem Q Λ ν s))) :=
  upWordBlockIsoOfEq hP hwf hΛ₀ hsym (seqWord s) (coe_seqWord s) _ ≪≫
    (𝕊 ν).mapIso (eqToIso (congrArg
      (fun s' => ModuleCat.of (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
        (idemLeftIdeal (redFirstIdem Q Λ ν s'))) (listSeq_seqWord s)))

section Assembly

open DG.DegreeZero
open scoped DG.DegreeZero

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

variable {ν : Multiset I} [DG.HasDerivedCategory.{0, 0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  {Xb : Type} [AddCommGroup Xb] [DG.DGAddCommGroup Xb] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ Xb]
  [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖᵐᵒᵖ Xb]
  [DG.DGBimodule (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ Xb]

/-- **Webster, arXiv:1309.3796v3, proof of Proposition 7.22 (b), one red strand, with the
vacuum `T^λ_∅`**: `SingleRed.blackVacuumDerivedTensorIsoId` with `C₀ = T^λ_∅`, `u_𝐢 = F_𝐢`
(`vacuumSeqHom`) and `W` computed (`vacuumSeqBlockIso`). The remaining inputs are `cS` (the
S-move is a derived tensor product), `σ, eσ, hσ` (it is the block `ν` component of a strongly
equivariant endofunctor fixing `T^λ_∅`) and `hgen` (the dots and crossings act on `F_𝐢 T^λ_∅`
as the 2-morphisms of the derived action). The route hypothesis `hΛ₀` is that of
`blackRouqFamily`. -/
def blackRegularVacuumDerivedTensorIsoId
    (S' : DerivedCategory (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) ⥤
      DerivedCategory (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ)) [S'.Additive]
    (cS : dgDerivedTensor.{0} _ _ Xb ⋙ derivedComparison (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ≅
      derivedComparison (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ⋙ S')
    (σ : Stendhal.blackPresCL hP hwf hΛ₀ hsym ⟶ Stendhal.blackPresCL hP hwf hΛ₀ hsym)
    (eσ : (σ.app (vacRegion hQ RD Λ₀)).obj.obj (blackRegularVacuum Q Λ RD Λ₀) ≅
      blackRegularVacuum Q Λ RD Λ₀)
    (hσ : (σ.app (⟨⟨(blockWeight RD Λ₀ ν : X)⟩⟩ :
          RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)).obj ⋙
        blackBlockEval hP hwf hΛ₀ hsym _ ⟨ν, rfl⟩ ≅
      blackBlockEval hP hwf hΛ₀ hsym _ ⟨ν, rfl⟩ ⋙ S')
    (hgen : ∀ y ∈ redFirstKLRGenerators Q Λ ν, ∀ a b,
      ∃ η : vacuumSeqHom (k := k) (hQ := hQ) (RD := RD) (Λ₀ := Λ₀) a ⟶
        vacuumSeqHom (k := k) (hQ := hQ) (RD := RD) (Λ₀ := Λ₀) b,
        (blackBlockEval hP hwf hΛ₀ hsym _ ⟨ν, rfl⟩).map
            (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map₂ η).hom.app
              (blackRegularVacuum Q Λ RD Λ₀)) =
          (vacuumSeqBlockIso hP hwf hΛ₀ hsym a).hom ≫
            (𝕊 ν).map (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ ν a)
              (redFirstIdem Q Λ ν b) y (redFirstIdem_isIdempotentElem Q Λ ν b))) ≫
            (vacuumSeqBlockIso hP hwf hΛ₀ hsym b).inv) :
    S' ≅ 𝟭 _ :=
  blackVacuumDerivedTensorIsoId hP hwf hΛ₀ hsym (blackRegularVacuum Q Λ RD Λ₀)
    (isZero_blackRegularVacuum (Q := Q) (Λ := Λ) (RD := RD) (Λ₀ := Λ₀)) S' cS σ eσ hσ
    (vacuumSeqHom (k := k) (hQ := hQ) (RD := RD) (Λ₀ := Λ₀))
    (vacuumSeqBlockIso hP hwf hΛ₀ hsym) hgen

end Assembly

end Categorification.Stendhal.SingleRed
