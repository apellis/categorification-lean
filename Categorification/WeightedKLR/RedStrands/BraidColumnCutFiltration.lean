/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnDiagramFiltration
import Categorification.WeightedKLR.RedStrands.BraidColumnStandardDimension
import Categorification.WeightedKLR.RedStrands.BraidRightSequenceCut

/-!
# The standard filtration of a braided sequence projective from its column

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11, step `p_n → f_n`. The braid `𝔅_w (e(t) T^λ)` of a sequence projective is the cut
`e(t) V e_{wλ}` (`braidRightSequenceCutEquiv`), which the images of the eligible diagrams filter
with surjections from loading standards (`hasFiltration_braidColumn`). The eligible indices are
distinct admissible choices of the loading with the same words (`blockChoice_injective`,
`choiceRows_blockChoice`), so the standards have total dimension at most that of the braid
(`finrank_braidF_rightSequence`), and the surjections are isomorphisms. This proves
`hasCornerStandardFiltration_braidF_rightSequence` without a filtration hypothesis.
-/

noncomputable section

namespace Categorification.ModuleFiltration.HasFiltration

universe v

variable {ι A : Type*} [Ring A] {L : ι → ModuleCat.{v} A}

/-- A filtration whose labels satisfy `p` is a filtration with labels in the subtype. -/
theorem pmap {p : ι → Prop} {m : List ι} {Y : ModuleCat.{v} A} (h : HasFiltration L m Y)
    (hp : ∀ c ∈ m, p c) :
    HasFiltration (fun c : {c // p c} => L c.1) (m.pmap Subtype.mk hp) Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons f g m c hf hfg hg _ hZ ih =>
    exact .cons f g _ ⟨c, hp c List.mem_cons_self⟩ hf hfg hg
      (ih fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')) hZ

end Categorification.ModuleFiltration.HasFiltration

namespace Categorification.ModuleFiltration

universe v

/-- Restricting back along the inverse of a ring isomorphism. -/
def restrictScalarsSymmEquiv {A B : Type*} [Ring A] [Ring B] (g : A ≃+* B)
    {X : ModuleCat.{v} B} {Y : ModuleCat.{v} A}
    (e : (ModuleCat.restrictScalars (g : A →+* B)).obj X ≃ₗ[A] Y) :
    X ≃ₗ[B] (ModuleCat.restrictScalars (g.symm : B →+* A)).obj Y where
  toFun x := e x
  invFun y := e.symm y
  left_inv x := e.left_inv x
  right_inv y := e.right_inv y
  map_add' x y := e.map_add x y
  map_smul' b x := by
    have h := e.map_smul (g.symm b) x
    change e (g (g.symm b) • x) = _ at h
    rw [RingEquiv.apply_symm_apply] at h
    exact h

/-- A sum over a nodup list, against a sum over another through a relation that is functional
on the second list, is at most the second sum. -/
theorem sum_le_of_rel {α β : Type*} {E : List α} {M : List β} (hE : E.Nodup)
    (R : α → β → Prop) (G : α → ℕ) (H : β → ℕ)
    (hR : ∀ a ∈ E, ∃ b ∈ M, R a b ∧ G a = H b)
    (huniq : ∀ a ∈ E, ∀ a' ∈ E, ∀ b, R a b → R a' b → a = a') :
    (E.map G).sum ≤ (M.map H).sum := by
  classical
  choose F hFM hFR hFG using hR
  have h1 : (E.map G).sum = ((E.attach.map fun a => F a.1 a.2).map H).sum := by
    rw [List.map_map]
    conv_lhs => rw [← List.attach_map_val (l := E)]
    congr 1
    exact List.map_congr_left fun a _ => hFG a.1 a.2
  have hnd : (E.attach.map fun a => F a.1 a.2).Nodup := by
    refine hE.attach.map_on fun a _ a' _ h => Subtype.ext ?_
    exact huniq a.1 a.2 a'.1 a'.2 _ (hFR a.1 a.2) (h ▸ hFR a'.1 a'.2)
  have hsub : (E.attach.map fun a => F a.1 a.2) ⊆ M := fun b hb => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hb
    exact hFM a.1 a.2
  obtain ⟨l, hp, hs⟩ := List.subperm_of_subset hnd hsub
  rw [h1, ← (hp.map H).sum_eq]
  exact (hs.map H).sum_le_sum fun _ _ => Nat.zero_le _

end Categorification.ModuleFiltration

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (σ : Perm (Fin ℓ))

local notation "μ" => stendhalWeight ℓ ν
local notation "C'" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- **Relabelling a surjection from a loading standard**: a surjection from the standard of
`V^λ` at `σ s'` onto `P` gives one from the standard of `V^{λ ∘ σ}` at `s'` onto `P`
restricted back along the relabelling of the corners. -/
theorem exists_surjective_loadingStandard_relabel {b s' : Seq μ} (h : Seq.redPerm σ s' = b)
    {κ : List (Fin ℓ)} (hκ : redWord s' = κ) {P : ModuleCat.{0} (C (κ.map σ))ᵐᵒᵖ}
    (d : ModuleCat.of (C (κ.map σ))ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) b
      (κ.map σ)) →ₗ[(C (κ.map σ))ᵐᵒᵖ] P) (hd : Function.Surjective d) :
    ∃ d' : ModuleCat.of (C' κ)ᵐᵒᵖ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s' κ)
        →ₗ[(C' κ)ᵐᵒᵖ] (ModuleCat.restrictScalars
          ((cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ).symm :
            (C' κ)ᵐᵒᵖ →+* (C (κ.map σ))ᵐᵒᵖ)).obj P,
      Function.Surjective d' := by
  subst h
  let e := restrictScalarsSymmEquiv (cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ)
    (loadingStandardRelabelEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ hκ)
  let d' := ((ModuleCat.restrictScalars
    ((cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) σ κ).symm :
      (C' κ)ᵐᵒᵖ →+* (C (κ.map σ))ᵐᵒᵖ)).map (ModuleCat.ofHom d)).hom
  refine ⟨d'.comp e.toLinearMap, ?_⟩
  exact (show Function.Surjective d' from hd).comp e.surjective

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF ModuleFiltration
open BraidedStendhalAlgebra BraidColumn Equiv
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "𝕂" => RatFunc ℚ

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
include C wt in
/-- **An eligible index of a braid column**, through its wiring: the relabelled bottom is the
row loading of the block words reordered by `w`, and these words come from an admissible choice
of the loading. -/
theorem exists_rowSeq_of_mem_braidColumnIndexList (w : Perm (Fin ℓ)) {ν : Multiset I}
    {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) {W : Perm (Fin (Multiset.card
      (stendhalWeight ℓ ν)))} (hW : W ∈ braidColumnIndexList t w) :
    ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = Multiset.card (stendhalWeight ℓ ν))
      (φ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν)))),
      ProjectiveBlockIndex t φ ∧
      (∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r) ∧
      W = braidColumnBottomBlockIndex n hn w φ ∧
      ∃ hν : blockContent (blockRow t n hn φ ∘ w) = ν,
        Seq.redPerm w⁻¹ (W⁻¹ • t) = (rowSeq (blockRow t n hn φ ∘ w) hν).1 := by
  obtain ⟨n, hn, φ, hφ, hred, rfl⟩ := mem_braidColumnIndexList.1 hW
  have hc := mem_loadingChoices_ofFn_of_eq _ _ (isAdmissibleChoice_blockChoice hφ hred ht)
    (countP_ofFn_lbl t)
  have hrows : choiceRows (List.ofFn t.lbl) (List.ofFn (blockChoice n hn φ)).reverse ℓ =
      blockRow t n hn φ := funext (choiceRows_blockChoice hφ hred ht)
  have hmem : blockRow t n hn φ ∈ (loadingMono wt (Seq.toList t)).map Prod.snd := by
    rw [loadingMono_map_snd, ← hrows]
    exact List.mem_map_of_mem hc
  obtain ⟨p, hp, hp2⟩ := List.mem_map.1 hmem
  have hν := blockContent_comp_of_mem_loadingMono C wt w t hp
  rw [hp2] at hν
  exact ⟨n, hn, φ, hφ, hred, rfl, hν, eq_rowSeq_of_ofFn _ _ hν (ofFn_relabel_bottom hred w)⟩

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
/-- **The standards of a braid column have total dimension at most that of the braid**
(Webster, arXiv:1309.3796v2, proof of Lemma 6.11): the eligible indices are distinct admissible
choices of the loading, and the standard at an index has the dimension of the row standard at
the words of its choice. -/
theorem sum_finrank_braidColumn_le (w : Perm (Fin ℓ)) {ν : Multiset I}
    {t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) :
    ((braidColumnIndexList t w).map fun W => Module.finrank k (ViolLoadingStandard (k := k)
      (Q := Q) (Λ := Λ ∘ w) (Seq.redPerm w⁻¹ (W⁻¹ • t)) (List.finRange ℓ))).sum ≤
      ((loadingMono wt (Seq.toList t)).map fun p =>
        Module.finrank k (rightRowStandard C hQ (Λ ∘ w) (p.2 ∘ w)).carrier).sum := by
  let H : (Fin ℓ → List I) → ℕ := fun u =>
    Module.finrank k (rightRowStandard C hQ (Λ ∘ w) (u ∘ w)).carrier
  rw [show (fun p : ℤ × (Fin ℓ → List I) =>
      Module.finrank k (rightRowStandard C hQ (Λ ∘ w) (p.2 ∘ w)).carrier) = H ∘ Prod.snd from rfl,
    ← List.map_map, loadingMono_map_snd, List.map_map]
  refine sum_le_of_rel (nodup_braidColumnIndexList t w)
    (fun W c => ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = Multiset.card (stendhalWeight ℓ ν))
      (φ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν)))), ProjectiveBlockIndex t φ ∧
      (∀ r : Fin ℓ, (φ⁻¹ • t).lbl (braidBlockPositions n hn ⟨r, 0⟩) = Sum.inr r) ∧
      W = braidColumnBottomBlockIndex n hn w φ ∧ c = (List.ofFn (blockChoice n hn φ)).reverse)
    _ _ (fun W hW => ?_) ?_
  · obtain ⟨n, hn, φ, hφ, hred, rfl, hν, heq⟩ :=
      exists_rowSeq_of_mem_braidColumnIndexList C wt w ht hW
    refine ⟨_, mem_loadingChoices_ofFn_of_eq _ _ (isAdmissibleChoice_blockChoice hφ hred ht)
      (countP_ofFn_lbl t), ⟨n, hn, φ, hφ, hred, rfl, rfl⟩, ?_⟩
    have hrows : choiceRows (List.ofFn t.lbl) (List.ofFn (blockChoice n hn φ)).reverse ℓ =
        blockRow t n hn φ := funext (choiceRows_blockChoice hφ hred ht)
    simp only [Function.comp_apply]
    rw [heq, finrank_rowSeq C hQ (Λ ∘ w) _ hν]
    change _ = H (choiceRows (List.ofFn t.lbl) (List.ofFn (blockChoice n hn φ)).reverse ℓ)
    rw [hrows]
  · rintro W - W' - c ⟨n, hn, φ, hφ, hred, rfl, rfl⟩ ⟨n', hn', φ', hφ', hred', rfl, hc⟩
    obtain ⟨rfl, rfl⟩ := blockChoice_injective hφ hred hφ' hred'
      (List.ofFn_injective (List.reverse_injective hc))
    rfl

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
theorem finiteDimensional_loadingStandard_of_eq {ν : Multiset I}
    {s s' : Seq (stendhalWeight ℓ ν)} (h : s = s') (κ : List (Fin ℓ))
    [FiniteDimensional k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s κ)] :
    FiniteDimensional k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s' κ) := by
  subst h
  assumption

/-- **`f_n` from the class map** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11, step
`p_n → f_n`): if the class map of `𝔅_w` is `x ↦ B(f x, -)` with `f` congruent at `v = 1` to the
permutation of the tensor factors by `w`, then `𝔅_w (e(t) T^λ)` has a standard filtration. The
images of the eligible diagrams filter the cut `e(t) V e_{wλ}` (`hasFiltration_braidColumn`),
each piece a quotient of a loading standard; the class map gives the dimension of the braid
(`finrank_braidF_rightSequence`), which bounds the total dimension of these standards
(`sum_finrank_braidColumn_le`), so every quotient map is an isomorphism. -/
theorem hasCornerStandardFiltration_braidF_rightSequence (w : Equiv.Perm (Fin ℓ))
    (f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ w))
    (hf : VOneCongr f (tensorPermute wt w).toLinearMap)
    (hcls : braidClass C hQ hR Λ wt hwt w = (formDual hR (wt ∘ w)).comp f)
    {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    HasCornerStandardFiltration (Λ ∘ w) ν (isReducedChoice_canChoice ν) hQ.klrSymm hQ
      (braidF C hQ Λ w ν (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
        (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht).toGFin) := by
  set N := braidF C hQ Λ w ν (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
    (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht).toGFin
  set L := braidColumnIndexList t w
  obtain ⟨hfilt, hsurj⟩ := hasFiltration_braidColumn (k := k) (Q := Q) (Λ := Λ) t ht w
    (canChoice ℓ ν) (isReducedChoice_canChoice ν)
  have hp : ∀ i ∈ (List.range L.length).reverse, i < L.length := fun i hi => by
    simpa using hi
  let g := cornerRelabelOp (k := k) (Q := Q) (Λ := Λ) (ν := ν) w (List.finRange ℓ)
  have e0 := braidRightSequenceCutEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht
  let e := restrictScalarsSymmEquiv g e0
  have h0 := (hfilt.pmap hp).restrictScalars (g.symm : (ViolOrderCorner (k := k) (Q := Q)
    (Λ := Λ ∘ w) (ν := ν) (List.finRange ℓ))ᵐᵒᵖ →+* (ViolOrderCorner (k := k) (Q := Q)
      (Λ := Λ) (ν := ν) ((List.finRange ℓ).map w))ᵐᵒᵖ)
  have h1 := h0.of_equiv e.symm
  let X := ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ w) (ν := ν)
    (List.finRange ℓ))ᵐᵒᵖ (braidRightSequenceCut (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht)
  let sP : ℕ → Seq (stendhalWeight ℓ ν) := fun i =>
    Seq.redPerm w⁻¹ ((braidColumnIndexAt t w i)⁻¹ • t)
  have hrow (i : {i // i < L.length}) : ∃ (u : Fin ℓ → List I) (hν : blockContent u = ν),
      sP i.1 = (rowSeq u hν).1 ∧ Module.finrank k (rightRowStandard C hQ (Λ ∘ w) u).carrier =
        Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w) (sP i.1)
          (List.finRange ℓ)) := by
    obtain ⟨n, hn, φ, -, -, -, hν, heq⟩ :=
      exists_rowSeq_of_mem_braidColumnIndexList C wt w ht (braidColumnIndexAt_mem i.2)
    exact ⟨_, hν, heq, (finrank_rowSeq C hQ (Λ ∘ w) _ hν).symm.trans (congrArg (fun s =>
      Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w) s
        (List.finRange ℓ))) heq).symm⟩
  choose u hν hu hfin using hrow
  let sel : {i // i < L.length} →
      {s : Seq (stendhalWeight ℓ ν) // redWord s = List.finRange ℓ ∧ ¬ IsViolated s} :=
    fun i => ⟨sP i.1, (hu i) ▸ (rowSeq (u i) (hν i)).2⟩
  let S : {i // i < L.length} → ModuleCat.{0} (ViolOrderCorner (k := k) (Q := Q)
      (Λ := Λ ∘ w) (ν := ν) (List.finRange ℓ))ᵐᵒᵖ := fun i =>
    ModuleCat.of _ (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w) (sel i).1
      (List.finRange ℓ))
  have hd : ∀ i : {i // i < L.length}, ∃ d' : S i →ₗ[(ViolOrderCorner (k := k) (Q := Q)
      (Λ := Λ ∘ w) (ν := ν) (List.finRange ℓ))ᵐᵒᵖ] (ModuleCat.restrictScalars (g.symm :
        (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ w) (ν := ν) (List.finRange ℓ))ᵐᵒᵖ →+*
          (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) ((List.finRange ℓ).map w))ᵐᵒᵖ)).obj
        (ModuleCat.of _ (diagramPiece (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) t w
          (canChoice ℓ ν) (isReducedChoice_canChoice ν)) i.1)), Function.Surjective d' := by
    intro i
    obtain ⟨d, hd⟩ := hsurj i.1 i.2
    exact exists_surjective_loadingStandard_relabel w
      (b := (braidColumnIndexAt t w i.1)⁻¹ • t) (s' := sP i.1)
      (by simp only [sP]; rw [Seq.redPerm_redPerm, mul_inv_cancel, Seq.redPerm_one])
      (sel i).2.1 (P := ModuleCat.of _ (diagramPiece (diagramColumnMaps (k := k) (Q := Q)
        (Λ := Λ) t w (canChoice ℓ ν) (isReducedChoice_canChoice ν)) i.1)) d hd
  choose d hd using hd
  have hN : ∀ (c : k) (x : braidRightSequenceCut (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht),
      algebraMap k (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ w) (ν := ν)
        (List.finRange ℓ))ᵐᵒᵖ c • x = c • x := fun c x => by
    rw [MulOpposite.algebraMap_apply]
    exact CornerRes.op_algebraMap_smul (isReducedChoice_canChoice ν) hQ.klrSymm _ c x
  have : FiniteDimensional k (braidRightSequenceCut (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (isReducedChoice_canChoice ν) hQ.klrSymm hQ w t ht) :=
    (braidFunctor (Λ := Λ) (ν := ν) (isReducedChoice_canChoice ν) hQ.klrSymm w hQ
      (rightSequenceProj (rouquierGrading Q hQ Λ) t ht).toGFin).finiteDimensional
  have := finiteDimensional_algebraModule (Y := X) (AddEquiv.refl _) hN
  have hS := fun (i : {i // i < L.length}) (a : k)
      (x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w) (sel i).1 (List.finRange ℓ)) =>
    algebraMap_smul_loadingStandard (sel i).1 (List.finRange ℓ) a x
  have h2 := h1.of_surjective_factors_of_le (k := k) (S := S) d (fun i => by
      have := finiteDimensional_rowSeq C hQ (Λ ∘ w) (u i) (hν i)
      have := finiteDimensional_loadingStandard_of_eq (k := k) (Q := Q) (Λ ∘ w) (hu i).symm
        (List.finRange ℓ)
      exact finiteDimensional_algebraModule (Y := S i) (AddEquiv.refl _) (hS i)) hd (by
    rw [finrank_algebraModule (Y := X) (AddEquiv.refl _) hN]
    change _ ≤ Module.finrank k N.carrier
    rw [finrank_braidF_rightSequence C hQ hR Λ wt hwt w f hf hcls t ht]
    refine le_trans (le_of_eq ?_) (sum_finrank_braidColumn_le C hQ Λ wt w ht)
    rw [List.map_pmap]
    refine (congrArg List.sum ((List.pmap_congr_left _ (g := fun a _ =>
      Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w) (sP a)
        (List.finRange ℓ))) (H₂ := hp) fun a _ h₁ _ =>
          finrank_algebraModule (Y := S ⟨a, h₁⟩) (AddEquiv.refl _) (hS _)).trans
            (List.pmap_eq_map _))).trans ?_
    rw [List.map_reverse, List.sum_reverse]
    congr 1
    refine List.ext_getElem (by simp [L]) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    exact congrArg (fun W : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) =>
      Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ w)
        (Seq.redPerm w⁻¹ (W⁻¹ • t)) (List.finRange ℓ)))
      (List.getD_eq_getElem _ _ (by simpa [L] using h1)))
  have h3 : HasFiltration (fun s : {s : Seq (stendhalWeight ℓ ν) //
      redWord s = List.finRange ℓ ∧ ¬ IsViolated s} => ModuleCat.of (ViolOrderCorner (k := k)
        (Q := Q) (Λ := Λ ∘ w) (ν := ν) (List.finRange ℓ))ᵐᵒᵖ (ViolLoadingStandard (k := k)
          (Q := Q) (Λ := Λ ∘ w) s.1 (List.finRange ℓ)))
      (((List.range L.length).reverse.pmap Subtype.mk hp).flatMap fun i => [sel i]) X :=
    HasFiltration.bind (M := fun i => [sel i])
      (fun i => HasFiltration.single (c := sel i) (LinearEquiv.refl _ (S i))) h2
  exact ⟨_, h3⟩

end Categorification.Stendhal.FirstWeight
