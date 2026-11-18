/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackDownSpanning
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffix
import Categorification.WeightedKLR.RedStrands.DoubleRedPrefixBubble
import Categorification.WeightedKLR.RedStrands.DoubleSpanningQuotient

/-!
# Black rectangles after an initial word of dominant red strands

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. In a rectangle with
only black strands, KL III straightening puts the bubble algebra in the
outermost region, immediately after the red prefix in physical word order.
Its positive generators vanish in the violating quotient. Throughout the
reduction the signed strands to the right of the rectangle remain fixed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w w'
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {k : Type w} [CommRing k]
    {ℓ : ℕ} (weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})
    (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
    (base : Presentation.{w, max u v} (signature RD (Subtype.val ∘ weights)) k)

local notation "labels" => (Subtype.val ∘ weights)
local notation "K" => pres RD k
local notation "B₀" => addBlackKLRelations RD labels base

/-- The signed presentation for the local black straightening in Webster v2, Lemma 4.28. -/
abbrev redPrefixSpanningPresentation :=
  addDownRelations RD labels (affineCoverQ Q exponents)
    (addRedUpRelations RD labels k (addRedCapRelations RD labels (addRedCupRelations RD labels B₀)))

local notation "B" => redPrefixSpanningPresentation RD weights Q exponents base

private theorem rectangleKL_eqs (r : (K).Rel) :
    (B).lin (blackMirrorLinear RD labels ((K).rel r)) = 0 :=
  (B).lin_rel_self (.inl (.inl (.inl (.inl (.inr r)))))

variable (rs : List (Fin ℓ)) (v : List (DoubleStrand I ℓ))
    (hr : rs ++ v.filterMap DoubleStrand.redLabel = List.finRange ℓ) {right : X}

local notation "red" => rs.map (Sum.inr (α := Letter I))
local notation "η" => endWeight RD labels 0 red
local notation "rectEnd" => (fun (s : List (Letter I)) => endWeight RD labels 0 (red ++ blackWord s ++ v))
local notation "rectCut" => right - List.sum (List.map (DoubleStrand.weight RD labels) v)

/-- Boundary with a black rectangle between an initial red word and a fixed signed suffix. -/
def redPrefixBlackTriple (s : List (Letter I)) (hs : rectEnd s = right) :
    DoubleStendhalTriple RD weights 0 right :=
  ⟨⟨red ++ blackWord s ++ v, by
    simpa [blackWord, List.filterMap_append, List.filterMap_map, Function.comp_def, DoubleStrand.redLabel] using hr⟩, hs⟩

local notation "bd" => redPrefixBlackTriple RD weights rs v hr
local notation "V" => violatingFunctor B right

private theorem rectangleCut (s : List (Letter I)) (hs : rectEnd s = right) :
    endWeight RD labels 0 (red ++ blackWord s) = rectCut := by
  apply eq_sub_of_add_eq
  exact (endWeight_append RD labels 0 (red ++ blackWord s) v).symm.trans hs

/-- Projection of a linear combination of black diagrams drawn in the rectangle. -/
def redPrefixBlackEntry (P : Presentation.{w, w'} (signature RD labels) k)
    (s t : List (Letter I)) (hs : rectEnd s = right) (ht : rectEnd t = right) :
    LinDiagram k (ob RD η s) (ob RD η t) →ₗ[k]
      ((violatingFunctor P right).obj (bd s hs) ⟶ (violatingFunctor P right).obj (bd t ht)) :=
  (violatingEntry P (bd s hs) (bd t ht)).comp (blackLinear RD labels k 0 red v)

private def rectangleKLHom (s t : List (Letter I)) (hs : rectEnd s = right) (ht : rectEnd t = right) :
    ((K).obj (ob RD η s) ⟶ (K).obj (ob RD η t)) →ₗ[k] ((V).obj (bd s hs) ⟶ (V).obj (bd t ht)) :=
  ((V).mapLinearMap k (X := bd s hs) (Y := bd t ht)).comp
    ((InducedCategory.homLinearEquiv (R := k) (F := tripleObj B (right := right))
      (X := bd s hs) (Y := bd t ht)).symm.toLinearMap.comp
      (blackRectangleHom RD labels 0 red v s B (rectangleKL_eqs RD weights Q exponents base) t
        (rectangleCut RD weights rs v s hs) (rectangleCut RD weights rs v t ht)))

local notation "F" => rectangleKLHom RD weights Q exponents base rs v hr
local notation "entry" => redPrefixBlackEntry RD weights rs v hr B

private theorem rectangleKLHom_lin (s t : List (Letter I)) (hs : rectEnd s = right) (ht : rectEnd t = right)
    (f : LinDiagram k (ob RD η s) (ob RD η t)) :
    F s t hs ht ((K).lin f) = entry s t hs ht f := by
  exact congrArg (fun m => (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd t ht) m))
    (blackRectangleHom_lin RD labels 0 red v s B (rectangleKL_eqs RD weights Q exponents base) t
      (rectangleCut RD weights rs v s hs) (rectangleCut RD weights rs v t ht) f)

private theorem rectangleKLHom_comp (s t z : List (Letter I))
    (hs : rectEnd s = right) (ht : rectEnd t = right) (hz : rectEnd z = right)
    (f : (K).obj (ob RD η s) ⟶ (K).obj (ob RD η t)) (g : (K).obj (ob RD η t) ⟶ (K).obj (ob RD η z)) :
    F s z hs hz (f ≫ g) = F s t hs ht f ≫ F t z ht hz g := by
  let M := blackRectangleHom (k := k) RD labels 0 red v (τ := rectCut)
  let eqs := rectangleKL_eqs RD weights Q exponents base
  let hc := rectangleCut (right := right) RD weights rs v
  change (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd z hz)
    (M s B eqs z (hc s hs) (hc z hz) (f ≫ g))) = _
  rw [show M s B eqs z (hc s hs) (hc z hz) (f ≫ g) = _ from
    blackRectangleHom_comp RD labels 0 red v s B eqs t z (hc s hs) (hc t ht) (hc z hz) f g]
  exact (V).map_comp (InducedCategory.homMk (X := bd s hs) (Y := bd t ht) _)
    (InducedCategory.homMk (X := bd t ht) (Y := bd z hz) _)

private theorem rectangleKLHom_id (s : List (Letter I)) (hs : rectEnd s = right) :
    F s s hs hs (𝟙 ((K).obj (ob RD η s))) = 𝟙 _ := by
  refine (congrArg (fun m => (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd s hs) m))
    (blackRectangleHom_id RD labels 0 red v s B (rectangleKL_eqs RD weights Q exponents base)
      (rectangleCut RD weights rs v s hs))).trans ?_
  exact (V).map_id (bd s hs)

variable (he : ∀ r i, (exponents r i : ℤ) = RD.pair (RD.iY i) (weights r).val)
local notation "redDegree" => (fun i => List.sum (List.map (fun r => exponents r i) rs))

include he in
private theorem rectangle_realGenerator (i : I) (n : ℕ) :
    bubGen RD k η i (n + 1) = (K).lin (LinDiagram.of (cwReal RD η i (n + redDegree i))) := by
  have h : ip RD i η = (redDegree i : ℤ) := by
    simp [ip, endWeight, List.map_map, Function.comp_def, DoubleStrand.weight, map_list_sum, ← he]
  rw [bubGen, h, ite_eq_left (Int.natCast_nonneg _), cwU]
  have hm : (redDegree i : ℤ) - 1 + ((n + 1 : ℕ) : ℤ) = ((n + redDegree i : ℕ) : ℤ) := by omega
  rw [hm, cwL_of_nonneg _ _ _ _ (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem rectangleKLHom_realBubble (s : List (Letter I)) (hs : rectEnd s = right) (i : I) (m : ℕ) :
    F s s hs hs (bubAt RD k η s ((K).lin (LinDiagram.of (cwReal RD η i m)))) =
      (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd s hs)
        ((B).diag (ccwBubbleAt RD labels 0 i red (blackWord s ++ v) (by simp [redPrefixBlackTriple, List.append_assoc]) m))) := by
  obtain ⟨ls, hc, hd⟩ := exists_mkD RD η (cwReal RD η i m)
  have hw : SChain s (ls.map (whL s [])) s := by simpa using hc.whisk s []
  have hl : (K).lin (LinDiagram.of (cwReal RD η i m)) = dg RD k η [] [] ls := by
    rw [hd, dg_of hc]
    rfl
  rw [hl, bubAt_dg, dg_of hw, ← Presentation.lin_of, rectangleKLHom_lin]
  have hd' : blackDiagram RD labels 0 red v (mkD RD η (ls.map (whL s [])) hw) =
      ccwBubbleAt RD labels 0 i red (blackWord s ++ v)
        (w := red ++ blackWord s ++ v) (by simp [List.append_assoc]) m := by
    apply Diagram.ext
    rw [ccwBubbleAt, Diagram.layers_cast, hd, layers_blackDiagram_mkD, layers_blackDiagram_mkD]
    simp [whL, blackWord, List.map_map]
  change (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd s hs)
    ((B).lin (blackLinear RD labels k 0 red v (LinDiagram.of _)))) = _
  rw [blackLinear_of, Presentation.lin_of, hd']

include he in
private theorem rectangle_bubbleGen_zero (s : List (Letter I)) (hs : rectEnd s = right) (i : I) (n : ℕ) :
    F s s hs hs (bubAt RD k η s (bubGen RD k η i (n+1))) = 0 := by
  rw [rectangle_realGenerator RD weights exponents rs he, rectangleKLHom_realBubble]
  have hz := ccwBubble_afterRedPrefix_zero RD i Q exponents weights B₀ (bd s hs)
    rs (blackWord s ++ v) (by simp [redPrefixBlackTriple, List.append_assoc]) n
  exact hz

include he in
private theorem rectangle_bubbles_scalar (s : List (Letter I)) (hs : rectEnd s = right) (p : PiLam I k) :
    ∃ c : k, F s s hs hs (bubAt RD k η s (bubMap RD k η p).val) = c • 𝟙 _ := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨r, ?_⟩
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, EndOne.val_algebraMap,
      map_smul, map_smul, bubAt_id, rectangleKLHom_id]
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b, by rw [map_add, EndOne.val_add, map_add, map_add, ha, hb, add_smul]⟩
  | mul_X p j _ =>
    obtain ⟨i,n⟩ := j
    refine ⟨0, ?_⟩
    have hb : (bubMap RD k η (MvPolynomial.X (i,n))).val = bubGen RD k η i (n+1) := by simp [bubMap]
    rw [map_mul, EndOne.val_mul, bubAt_comp, rectangleKLHom_comp _ _ _ _ _ _ _ _ s s s hs hs hs, hb,
      rectangle_bubbleGen_zero RD weights Q exponents base rs v hr he, Limits.zero_comp, zero_smul]

include he in
/-- Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28, using KL III Lemma 3.9.
A black diagram between an initial red word and any fixed signed suffix, with downward black
endpoints, projects into the span of downward black dots and crossings in that rectangle. -/
theorem redPrefixBlackEntry_mem_span (s t : List I)
    (hs : rectEnd (dns s) = right) (ht : rectEnd (dns t) = right)
    (d : LinDiagram k (ob RD η (dns s)) (ob RD η (dns t))) :
    entry (dns s) (dns t) hs ht d ∈ Submodule.span k {g | ∃ (A : List (LayerData I)) (hA : SChain (dns s) A (dns t)),
      DownBlackLayers A ∧ g = entry (dns s) (dns t) hs ht (LinDiagram.of (mkD RD η A hA))} := by
  classical
  rw [← rectangleKLHom_lin]
  have H : (K).lin d ∈ downwardBlackBubbleSpan RD k η (dns s) (dns t) := by
    rw [downwardBlackBubbleSpan_eq_top]; exact Submodule.mem_top
  generalize (K).lin d = z at H ⊢
  induction H using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A,γ,hA,hch,⟨p,hp⟩,rfl⟩ := hz
    have hv := congrArg EndOne.val hp
    change (bubMap RD k η p).val = γ at hv
    obtain ⟨c,hc⟩ := rectangle_bubbles_scalar RD weights Q exponents base rs v hr he (dns t) ht p
    rw [rectangleKLHom_comp _ _ _ _ _ _ _ _ _ _ _ hs ht ht, ← hv, hc, Linear.comp_smul,
      Category.comp_id, dg_of hch, ← Presentation.lin_of, rectangleKLHom_lin]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨A,hch,hA,rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz

include he in
/-- The local straightening of Webster v2, Lemma 4.28, persists after adjoining
further relations to the signed presentation. -/
theorem redPrefixBlackEntry_mem_span_of_ideal_le
    (P : Presentation.{w, w'} (signature RD labels) k)
    (hP : ∀ a b, (B).ideal a b ≤ P.ideal a b)
    (s t : List I) (hs : rectEnd (dns s) = right) (ht : rectEnd (dns t) = right)
    (d : LinDiagram k (ob RD η (dns s)) (ob RD η (dns t))) :
    redPrefixBlackEntry RD weights rs v hr P (dns s) (dns t) hs ht d ∈ Submodule.span k
      {g | ∃ (A : List (LayerData I)) (hA : SChain (dns s) A (dns t)), DownBlackLayers A ∧
        g = redPrefixBlackEntry RD weights rs v hr P (dns s) (dns t) hs ht (LinDiagram.of (mkD RD η A hA))} := by
  let liftMap := (violatingExtension B P hP).mapLinearMap k
    (X := (V).obj (bd (dns s) hs)) (Y := (V).obj (bd (dns t) ht))
  have hmap (e : LinDiagram k (ob RD η (dns s)) (ob RD η (dns t))) :
      liftMap (entry (dns s) (dns t) hs ht e) = redPrefixBlackEntry RD weights rs v hr P (dns s) (dns t) hs ht e := rfl
  rw [← hmap]
  have h := redPrefixBlackEntry_mem_span RD weights Q exponents base rs v hr he s t hs ht d
  generalize entry (dns s) (dns t) hs ht d = f at h ⊢
  induction h using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨A, hA, hdown, rfl⟩ := hx
    exact Submodule.subset_span ⟨A, hA, hdown, hmap _⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

end Categorification.Stendhal.DoubleDiagram
