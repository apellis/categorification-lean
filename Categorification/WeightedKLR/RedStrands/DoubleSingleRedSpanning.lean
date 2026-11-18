/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackDownSpanning
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedReduction
import Categorification.WeightedKLR.RedStrands.DoubleRedPrefixBubble

/-!
# Downward spanning for one dominant red strand

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, and Khovanov–Lauda
III, arXiv:0807.3250v1, Lemma 3.9. Every surviving diagram has its single
red strand first. Black straightening moves all bubble factors next to that
strand. At a dominant red weight the positive-degree generators of the
bubble algebra are real bubbles, and the red-prefix relation kills them.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {k : Type w} [CommRing k]
    (weights : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})
    (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin 1 → I →₀ ℕ)
    (base : Presentation.{w, max u v} (signature RD (Subtype.val ∘ weights)) k)

local notation "labels" => (Subtype.val ∘ weights)
private abbrev firstRed : List (DoubleStrand I 1) := [.inr 0]
local notation "η" => endWeight RD labels 0 firstRed
local notation "K" => pres RD k
local notation "B₀" => addBlackKLRelations RD labels base

/-- A one-red presentation containing the reflected KL black relations
and the red slides used in Webster v3, Lemma 4.29. -/
abbrev singleRedSpanningPresentation :=
  addDownRelations RD labels (affineCoverQ Q exponents)
    (addRedUpRelations RD labels k (addRedCapRelations RD labels (addRedCupRelations RD labels B₀)))

local notation "B" => singleRedSpanningPresentation RD weights Q exponents base

private theorem singleRedKL_eqs (r : (K).Rel) :
    (B).lin (blackMirrorLinear RD labels ((K).rel r)) = 0 :=
  (B).lin_rel_self (.inl (.inl (.inl (.inl (.inr r)))))

variable {right : X}
local notation "redEnd" => (fun (s : List (Letter I)) => endWeight RD labels 0 (firstRed ++ blackWord s ++ []))
local notation "bd" => singleRedTriple (Λd := weights) RD
local notation "V" => violatingFunctor B right

/-- Reflection and projection of a presented black Hom with the single red on its left. -/
def singleRedKLHom (s t : List (Letter I)) (hs : redEnd s = right) (ht : redEnd t = right) :
    ((K).obj (ob RD η s) ⟶ (K).obj (ob RD η t)) →ₗ[k] ((V).obj (bd s hs) ⟶ (V).obj (bd t ht)) :=
  (singleRedProjection B s t hs ht).comp
    (blackPrefixHom RD labels 0 firstRed B (singleRedKL_eqs RD weights Q exponents base))

local notation "F" => singleRedKLHom RD weights Q exponents base

private theorem singleRedKLHom_lin (s t : List (Letter I)) (hs : redEnd s = right) (ht : redEnd t = right)
    (f : LinDiagram k (ob RD η s) (ob RD η t)) :
    F s t hs ht ((K).lin f) = singleRedBlackEntry B s t hs ht f := by
  unfold singleRedKLHom
  rw [LinearMap.comp_apply, blackPrefixHom_lin]
  rfl

private theorem singleRedKLHom_comp (s t z : List (Letter I))
    (hs : redEnd s = right) (ht : redEnd t = right) (hz : redEnd z = right)
    (f : (K).obj (ob RD η s) ⟶ (K).obj (ob RD η t)) (g : (K).obj (ob RD η t) ⟶ (K).obj (ob RD η z)) :
    F s z hs hz (f ≫ g) = F s t hs ht f ≫ F t z ht hz g := by
  unfold singleRedKLHom
  simp only [LinearMap.comp_apply]
  rw [blackPrefixHom_comp, singleRedProjection_comp B s t z hs ht hz]

private theorem singleRedKLHom_id (s : List (Letter I)) (hs : redEnd s = right) :
    F s s hs hs (𝟙 ((K).obj (ob RD η s))) = 𝟙 _ := by
  unfold singleRedKLHom
  rw [LinearMap.comp_apply, blackPrefixHom_id, singleRedProjection_id]

variable (he : ∀ i, (exponents 0 i : ℤ) = RD.pair (RD.iY i) (weights 0).val)

include he in
private theorem singleRed_realGenerator (i : I) (n : ℕ) :
    bubGen RD k η i (n + 1) = (K).lin (LinDiagram.of (cwReal RD η i (n + exponents 0 i))) := by
  have h : ip RD i η = (exponents 0 i : ℤ) := by
    simpa [endWeight, firstRed, DoubleStrand.weight, ip] using (he i).symm
  rw [bubGen, h, ite_eq_left (Int.natCast_nonneg _), cwU]
  have hm : (exponents 0 i : ℤ) - 1 + ((n + 1 : ℕ) : ℤ) = ((n + exponents 0 i : ℕ) : ℤ) := by omega
  rw [hm, cwL_of_nonneg _ _ _ _ (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem singleRedKLHom_realBubble (s : List (Letter I)) (hs : redEnd s = right) (i : I) (m : ℕ) :
    F s s hs hs (bubAt RD k η s ((K).lin (LinDiagram.of (cwReal RD η i m)))) =
      (V).map (InducedCategory.homMk (X := bd s hs) (Y := bd s hs)
        ((B).diag (ccwBubbleAt RD labels 0 i firstRed (blackWord s ++ []) (by simp [singleRedTriple]) m))) := by
  obtain ⟨ls, hc, hd⟩ := exists_mkD RD η (cwReal RD η i m)
  have hw : SChain s (ls.map (whL s [])) s := by simpa using hc.whisk s []
  have hl : (K).lin (LinDiagram.of (cwReal RD η i m)) = dg RD k η [] [] ls := by
    rw [hd, dg_of hc]
    rfl
  rw [hl, bubAt_dg, dg_of hw, ← Presentation.lin_of, singleRedKLHom_lin]
  have hd' : blackDiagram RD labels 0 firstRed [] (mkD RD η (ls.map (whL s [])) hw) =
      ccwBubbleAt RD labels 0 i firstRed (blackWord s ++ [])
        (w := firstRed ++ blackWord s ++ []) (by simp) m := by
    apply Diagram.ext
    rw [ccwBubbleAt, Diagram.layers_cast, hd, layers_blackDiagram_mkD, layers_blackDiagram_mkD]
    simp [whL, blackWord, List.map_map]
  change (singleRedProjection B s s hs hs) ((B).lin (blackLinear RD labels k 0 firstRed [] _)) = _
  rw [blackLinear_of, Presentation.lin_of, hd']
  rfl

include he in
private theorem singleRed_bubbleGen_zero (s : List (Letter I)) (hs : redEnd s = right) (i : I) (n : ℕ) :
    F s s hs hs (bubAt RD k η s (bubGen RD k η i (n+1))) = 0 := by
  rw [singleRed_realGenerator RD weights exponents he, singleRedKLHom_realBubble]
  have hz := ccwBubble_afterRedPrefix_zero RD i Q exponents weights B₀ (bd s hs)
    [0] (blackWord s ++ []) (by simp [singleRedTriple]) n
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hz

include he in
private theorem singleRed_bubbles_scalar (s : List (Letter I)) (hs : redEnd s = right) (p : PiLam I k) :
    ∃ c : k, F s s hs hs (bubAt RD k η s (bubMap RD k η p).val) = c • 𝟙 _ := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨r, ?_⟩
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, EndOne.val_algebraMap,
      map_smul, map_smul, bubAt_id, singleRedKLHom_id]
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b, by rw [map_add, EndOne.val_add, map_add, map_add, ha, hb, add_smul]⟩
  | mul_X p j _ =>
    obtain ⟨i,n⟩ := j
    refine ⟨0, ?_⟩
    have hb : (bubMap RD k η (MvPolynomial.X (i,n))).val = bubGen RD k η i (n+1) := by simp [bubMap]
    rw [map_mul, EndOne.val_mul, bubAt_comp, singleRedKLHom_comp _ _ _ _ _ s s s hs hs hs, hb,
      singleRed_bubbleGen_zero RD weights Q exponents base he, Limits.zero_comp, zero_smul]

include he in
/-- Webster, arXiv:1309.3796v3, §4.6, Lemma 4.29, for the entries with
one dominant red and arbitrary all-down black words. Every morphism in
the violating quotient is a linear combination of downward diagrams. -/
theorem singleRed_span_downwardBlack (s t : List I)
    (hs : redEnd (dns s) = right) (ht : redEnd (dns t) = right)
    (f : (V).obj (bd (dns s) hs) ⟶ (V).obj (bd (dns t) ht)) :
    f ∈ Submodule.span k {g | ∃ (A : List (LayerData I)) (hA : SChain (dns s) A (dns t)),
      DownBlackLayers A ∧ g = singleRedBlackEntry B (dns s) (dns t) hs ht
        (LinDiagram.of (mkD RD η A hA))} := by
  classical
  obtain ⟨d,rfl⟩ := singleRedBlackEntry_surjective B (dns s) (dns t) hs ht f
  rw [← singleRedKLHom_lin]
  have H : (K).lin d ∈ downwardBlackBubbleSpan RD k η (dns s) (dns t) := by
    rw [downwardBlackBubbleSpan_eq_top]; exact Submodule.mem_top
  generalize (K).lin d = z at H ⊢
  induction H using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A,γ,hA,hch,⟨p,hp⟩,rfl⟩ := hz
    have hv := congrArg EndOne.val hp
    change (bubMap RD k η p).val = γ at hv
    obtain ⟨c,hc⟩ := singleRed_bubbles_scalar RD weights Q exponents base he (dns t) ht p
    rw [singleRedKLHom_comp _ _ _ _ _ _ _ _ hs ht ht, ← hv, hc, Linear.comp_smul,
      Category.comp_id, dg_of hch, ← Presentation.lin_of, singleRedKLHom_lin]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨A,hch,hA,rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz

end Categorification.Stendhal.DoubleDiagram
