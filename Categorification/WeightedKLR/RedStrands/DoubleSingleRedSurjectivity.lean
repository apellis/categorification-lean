/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.DoubleSingleBlackSpan
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedReduction
import Categorification.WeightedKLR.RedStrands.DoubleRedPrefixBubble
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary

/-!
# Spanning the fundamental one-red, one-black endomorphisms by downward dots

Webster, arXiv:1309.3796v3, proof of Lemma 4.29. In this rank-one block one
red stays at the far left of a nonviolating diagram. Black KL straightening
then leaves only downward dots and bubbles next to the red. The generators
of the bubble algebra at weight one have strictly positive degree and are
real counterclockwise bubbles in physical order. They vanish after the
red slide, leaving only downward dots.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w

private abbrev fundWeights :
    Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, fun _ => by decide +revert⟩

local notation "RD" => sl2RootDatum
local notation "redVal" => Subtype.val ∘ fundWeights
local notation "S" => signature RD redVal

private abbrev leftRed : List (DoubleStrand Unit 1) := [.inr 0]
private abbrev strandWord : List (Letter Unit) := [dn ()]
private abbrev rightBlack : List (DoubleStrand Unit 1) := [.inl (dn ())]

private theorem exteriorWeight : endWeight RD redVal 0 (leftRed ++ blackWord strandWord ++ []) = -1 := rfl
private abbrev cut := singleRedTriple (Λd := fundWeights) RD strandWord exteriorWeight

variable {k : Type w} [CommRing k]

private abbrev Q₁ : Unit → Unit → MvPolynomial (Fin 2) k := fun _ _ => 0
private abbrev d₁ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

/-- The signed rank-one presentation used here, built over an arbitrary
additional base. The black relations are the reflected KL III ones. -/
def fundamentalSingleRedPresentation (P : Presentation.{w, 0} S k) : Presentation.{w, 0} S k :=
  addDownRelations RD redVal (affineCoverQ Q₁ d₁)
    (addRedUpRelations RD redVal k
      (addRedCapRelations RD redVal (addRedCupRelations RD redVal (addBlackKLRelations RD redVal P))))

variable (P : Presentation.{w, 0} (signature sl2RootDatum (Subtype.val ∘ fundWeights)) k)

local notation "B" => fundamentalSingleRedPresentation P
local notation "K" => pres RD k
local notation "F" => ob RD 1 strandWord
local notation "vac" => ob RD 1 []
/-- The red-first one-black object in the fundamental rank-one signed quotient. -/
abbrev fundamentalSingleRedObj : ViolatingCategory B (-1) := (violatingFunctor B (-1)).obj cut

local notation "target" => fundamentalSingleRedObj P

private theorem black_eqs (r : (K).Rel) : (B).lin (blackMirrorLinear RD redVal ((K).rel r)) = 0 :=
  (B).lin_rel_self (.inl (.inl (.inl (.inl (.inr r)))))

private abbrev signedProjection :=
  singleRedProjection B strandWord strandWord exteriorWeight exteriorWeight

/-- The black presented End map into the fundamental red-first signed
endomorphism algebra. -/
def fundamentalBlackEnd :
    End ((K).obj F) →ₗ[k] End target :=
  (signedProjection P).comp (blackPrefixHom RD redVal 0 leftRed B (black_eqs P))

private theorem fund_map_lin (f : LinDiagram k F F) :
    fundamentalBlackEnd P ((K).lin f) =
      singleRedBlackEntry B strandWord strandWord exteriorWeight exteriorWeight f := by
  change (signedProjection P) (blackPrefixHom RD redVal 0 leftRed B (black_eqs P) ((K).lin f)) = _
  rw [blackPrefixHom_lin]
  rfl

private theorem fund_map_comp (f g : End ((K).obj F)) :
    fundamentalBlackEnd P (f ≫ g) = fundamentalBlackEnd P f ≫ fundamentalBlackEnd P g := by
  change (signedProjection P) (blackPrefixHom RD redVal 0 leftRed B (black_eqs P) (f ≫ g)) = _
  rw [blackPrefixHom_comp, singleRedProjection_comp]
  rfl

private theorem fund_map_id : fundamentalBlackEnd P (𝟙 ((K).obj F)) = 𝟙 target := by
  change (signedProjection P) (blackPrefixHom RD redVal 0 leftRed B (black_eqs P) (𝟙 ((K).obj F))) = _
  have h := blackPrefixHom_id RD redVal 0 leftRed B (black_eqs P) strandWord
  change blackPrefixHom RD redVal 0 leftRed B (black_eqs P) (𝟙 ((K).obj F)) = _ at h
  rw [h, singleRedProjection_id]

private theorem bubgen_real (n : ℕ) :
    bubGen RD k 1 () (n + 1) = (K).lin (LinDiagram.of (cwReal RD 1 () (n + 1))) := by
  have h : ip RD () 1 = 1 := rfl
  rw [bubGen, h, ite_eq_left (by decide), cwU]
  have hm : (1 : ℤ) - 1 + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := by simp
  rw [hm, cwL_of_nonneg _ _ _ _ (Int.natCast_nonneg _), Int.toNat_natCast]

private def bubRightRaw (m : ℕ) : End F :=
  Diagram.cast (Diagram.whisker (cwReal RD 1 () m) (ob RD 1 strandWord) []
    (whiskerOK_right RD 1 strandWord)) (whisker_right_eq RD 1 strandWord)
      (whisker_right_eq RD 1 strandWord)

private theorem bubRightRaw_lin (m : ℕ) :
    (K).lin (LinDiagram.of (bubRightRaw m)) =
      bubRU RD k 1 (dn ()) ((K).lin (LinDiagram.of (cwReal RD 1 () m))) := by
  change (K).lin (LinDiagram.of (bubRightRaw m)) = plcL RD k 1 [dn ()] [] [] []
    ((K).lin (LinDiagram.of (cwReal RD 1 () m)))
  rw [← lin_bubR RD k 1 (dn ()) (LinDiagram.of (cwReal RD 1 () m))]
  congr 1
  rw [bubR, LinDiagram.whisker_of, LinDiagram.cast_of]
  rfl

private theorem rightBubble_reflect (m : ℕ) :
    blackDiagram RD redVal 0 leftRed [] (bubRightRaw m) =
      ccwBubbleAt RD redVal 0 () leftRed rightBlack rfl m := by
  let η := endWeight RD redVal 0 leftRed
  obtain ⟨ls, h, hd⟩ := exists_mkD RD η (cwReal RD η () m)
  have hs : SChain strandWord (ls.map (whL strandWord [])) strandWord := by
    simpa only [List.append_nil] using h.whisk strandWord []
  have hb : bubRightRaw m = mkD RD η (ls.map (whL strandWord [])) hs := by
    apply Diagram.ext
    unfold bubRightRaw
    rw [Diagram.layers_cast, Diagram.layers_whisker]
    change (Diagram.layers (cwReal RD η () m)).map _ = Diagram.layers (mkD RD η _ hs)
    rw [hd, layers_mkD, layers_mkD]
    exact layList_whisker RD η strandWord [] h
  apply Diagram.ext
  rw [hb, layers_blackDiagram_mkD, ccwBubbleAt, Diagram.layers_cast, hd, layers_blackDiagram_mkD]
  simp [whL, blackWord, List.map_map]

private theorem fund_bubbleGen_zero (n : ℕ) :
    fundamentalBlackEnd P (bubRU RD k 1 (dn ()) (bubGen RD k 1 () (n + 1))) = 0 := by
  rw [bubgen_real, ← bubRightRaw_lin, fund_map_lin]
  have hvan := ccwBubble_afterRedPrefix_zero RD () Q₁ d₁ fundWeights (addBlackKLRelations RD redVal P)
    cut [0] rightBlack rfl n
  change (signedProjection P) ((B).lin (blackLinear RD redVal k 0 leftRed []
    (LinDiagram.of (bubRightRaw (n + 1))))) = 0
  rw [blackLinear_of, Presentation.lin_of, rightBubble_reflect]
  have hdegree : (d₁ : Fin 1 → Unit →₀ ℕ) 0 () = 1 := by simp [d₁]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hdegree] at hvan
  change (violatingFunctor B (-1)).map (InducedCategory.homMk (X := cut) (Y := cut)
    ((B).diag (ccwBubbleAt RD redVal 0 () leftRed rightBlack rfl (n + 1)))) = 0
  exact hvan

private theorem fund_bubbles_scalar (p : PiLam Unit k) :
    ∃ c : k, fundamentalBlackEnd P (bubRU RD k 1 (dn ()) ((bubMap RD k 1 p).val)) = c • 𝟙 target := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨r, ?_⟩
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, EndOne.val_algebraMap]
    change fundamentalBlackEnd P
      (plcL RD k 1 [dn ()] [] [] [] (r • 𝟙 ((K).obj vac))) = _
    rw [map_smul, map_smul]
    change r • fundamentalBlackEnd P (bubRU RD k 1 (dn ()) (𝟙 _)) = _
    rw [bubRU_id, fund_map_id]
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    rw [map_add, EndOne.val_add]
    change fundamentalBlackEnd P (plcL RD k 1 [dn ()] [] [] []
      ((bubMap RD k 1 p).val + (bubMap RD k 1 q).val)) = _
    rw [map_add, map_add, ha, hb, add_smul]
  | mul_X p i _ =>
    obtain ⟨i, n⟩ := i
    cases i
    refine ⟨0, ?_⟩
    rw [map_mul, EndOne.val_mul, bubRU_comp, fund_map_comp]
    have hg : (bubMap RD k 1 (MvPolynomial.X ((), n))).val = bubGen RD k 1 () (n + 1) := by
      simp [bubMap]
    rw [hg, fund_bubbleGen_zero, Limits.zero_comp, zero_smul]

/-- Webster v3, Lemma 4.29, for the rank-one fundamental red-first one-black
Hom. Every endomorphism is in the span of powers of the downward dot. -/
theorem fundamentalSingleRed_span_downwardDots (f : End target) :
    f ∈ Submodule.span k (Set.range fun n => fundamentalBlackEnd P (dotsU RD k 1 (dn ()) n)) := by
  obtain ⟨d, rfl⟩ := singleRedBlackEntry_surjective B strandWord strandWord exteriorWeight exteriorWeight f
  rw [← fund_map_lin]
  have hs := fundamental_down_mem_slideSetR k ((K).lin d)
  generalize (K).lin d = g at hs ⊢
  induction hs using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, β, ⟨p, hp⟩, rfl⟩ := hg
    have hval := congrArg EndOne.val hp
    change (bubMap RD k 1 p).val = β at hval
    obtain ⟨c, hc⟩ := fund_bubbles_scalar P p
    rw [fund_map_comp, ← hval, hc, Linear.comp_smul, Category.comp_id]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add g h _ _ hg hh => rw [map_add]; exact Submodule.add_mem _ hg hh
  | smul r g _ hg => rw [map_smul]; exact Submodule.smul_mem _ r hg

private theorem fund_dot_zero : fundamentalBlackEnd P (dotsU RD k 1 (dn ()) 1) = 0 := by
  rw [← dotsU_eq, ← Presentation.lin_of, fund_map_lin]
  let dot := redDownDotRedLeft RD redVal 0 [] 0 () []
  have hd : blackDiagram RD redVal 0 leftRed [] (dots RD 1 [] (dn ()) [] 1) = dot := by
    apply Diagram.ext
    rw [dots]
    change Diagram.layers (blackDiagram RD redVal 0 leftRed []
      (mkD RD (endWeight RD redVal 0 leftRed) [([], .dot (dn ()), [])] (by schain))) = _
    rw [layers_blackDiagram_mkD]
    rfl
  let A := addRedUpRelations RD redVal k
    (addRedCapRelations RD redVal (addRedCupRelations RD redVal (addBlackKLRelations RD redVal P)))
  let f := moveDiagram RD redVal 0 [] (.redBlack 0 (dn ())) []
  let g := moveDiagram RD redVal 0 [] (.blackRed (dn ()) 0) []
  have he : (B).diag (f ≫ g) = (B).diag dot := by
    have hb := redDown_bigon_redLeft RD redVal Q₁ d₁ A 0 [] 0 () []
    rw [show (d₁ : Fin 1 → Unit →₀ ℕ) 0 () = 1 by simp [d₁], pow_one] at hb
    exact hb
  change (signedProjection P) ((B).lin (blackLinear RD redVal k 0 leftRed []
    (LinDiagram.of (dots RD 1 [] (dn ()) [] 1)))) = 0
  rw [blackLinear_of, Presentation.lin_of, hd, ← he]
  change (violatingFunctor B (-1)).map (InducedCategory.homMk (X := cut) (Y := cut)
    ((B).diag (f ≫ g))) = 0
  apply diagram_eq_zero_of_black_at_cut
  exact ⟨dn (), rfl⟩

/-- In the fundamental rank-one, one-red block the algebra map of scalars
is onto the red-first corner. A positive power of the dot factors through
the violated black-first boundary, and the rank-one straightening removes
all other diagrams. -/
theorem fundamentalSingleRed_algebraMap_surjective :
    Function.Surjective (algebraMap k (End target)) := by
  intro f
  have hs := fundamentalSingleRed_span_downwardDots P f
  change ∃ z, (Algebra.linearMap k (End target)) z = f
  refine LinearMap.mem_range.mp ((Submodule.span_le.mpr ?_) hs)
  rintro _ ⟨n, rfl⟩
  cases n with
  | zero =>
    refine ⟨1, ?_⟩
    change algebraMap k (End target) 1 = fundamentalBlackEnd P (dotsU RD k 1 (dn ()) 0)
    rw [dotsU_zero, fund_map_id, map_one]
    rfl
  | succ n =>
    have hz : fundamentalBlackEnd P (dotsU RD k 1 (dn ()) (n + 1)) = 0 := by
      rw [Nat.add_comm, ← dotsU_add, fund_map_comp, fund_dot_zero, Limits.zero_comp]
    change fundamentalBlackEnd P (dotsU RD k 1 (dn ()) (n + 1)) ∈ _
    rw [hz]
    exact Submodule.zero_mem _

/-- Every unital diagram comparison into the fundamental red-first corner is
surjective, by scalar generation. -/
theorem fundamentalSingleRed_algHom_surjective {A : Type*} [Semiring A] [Algebra k A]
    (f : A →ₐ[k] End target) : Function.Surjective f := by
  intro g
  obtain ⟨r, rfl⟩ := fundamentalSingleRed_algebraMap_surjective P g
  exact ⟨algebraMap k A r, f.commutes r⟩

section Comparison

open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "D" => addDownRelations RD redVal (affineCoverQ Q₁ d₁) B
local notation "M" => addMixedBlackRelations RD redVal k (fun _ _ => 1) D
local notation "T" => addRedUpRelations RD redVal k M
local notation "blackContent" => ({()} : Multiset Unit)
local notation "Ord" => {s : KLR.Seq (stendhalWeight 1 blackContent) // IsRedOrdered s}

local instance : DecidableEq Unit := Classical.decEq _
local instance : Fintype Ord := Subtype.fintype IsRedOrdered

private theorem additional_ideal_le (a b : Obj S) : (B).ideal a b ≤ (T).ideal a b := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨r, u, v, h, pre, post⟩
  apply Submodule.subset_span
  cases r with
  | user r =>
    exact Presentation.IdealGen.intro (P := T) (.user (.inl (.inl (.inl r)))) u v h pre post
  | interchange r hr =>
    exact Presentation.IdealGen.intro (P := T) (.interchange r hr) u v h pre post

private def additionalFunctor : (B).Presented ⥤ (T).Presented :=
  CategoryTheory.Quotient.lift (B).homRel (T).linFunctor fun _ _ f g h =>
    ((T).lin_eq_iff f g).mpr (additional_ideal_le P _ _ h)

private theorem additionalFunctor_lin :
    (B).linFunctor ⋙ additionalFunctor P = (T).linFunctor := rfl

private instance : (additionalFunctor P).Additive := by
  have : (B).linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : ((B).linFunctor ⋙ additionalFunctor P).Additive := by
    rw [additionalFunctor_lin]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp (B).linFunctor _

private instance : (additionalFunctor P).Linear k := by
  have : (B).linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : ((B).linFunctor ⋙ additionalFunctor P).Linear k := by
    rw [additionalFunctor_lin]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (B).linFunctor _

private def additionalBoundaryFunctor : BoundaryCategory (Λ := fundWeights) B (-1) ⥤
    BoundaryCategory (Λ := fundWeights) T (-1) where
  obj a := a
  map f := InducedCategory.homMk ((additionalFunctor P).map f.hom)
  map_id _ := InducedCategory.hom_ext ((additionalFunctor P).map_id _)
  map_comp f g := InducedCategory.hom_ext ((additionalFunctor P).map_comp f.hom g.hom)

private instance : (additionalBoundaryFunctor P).Additive where
  map_add {_X _Y} {f g} := InducedCategory.hom_ext
    ((additionalFunctor P).map_add (f := f.hom) (g := g.hom))

private instance : (additionalBoundaryFunctor P).Linear k where
  map_smul {_X _Y} f r := InducedCategory.hom_ext ((additionalFunctor P).map_smul r f.hom)

private def additionalViolatingFunctor : ViolatingCategory (Λ := fundWeights) B (-1) ⥤
    ViolatingCategory (Λ := fundWeights) T (-1) :=
  DoubleViolatingQuotient.lift k (tripleObj (Λ := fundWeights) B (right := -1))
    (additionalBoundaryFunctor P ⋙ violatingFunctor T (-1)) fun _ h =>
      DoubleViolatingQuotient.id_eq_zero k (tripleObj (Λ := fundWeights) T) h

private instance : (additionalViolatingFunctor P).Linear k := by
  unfold additionalViolatingFunctor
  infer_instance

private theorem additionalViolatingFunctor_surjective
    (f : End ((violatingFunctor T (-1)).obj cut)) :
    ∃ g : End target, (additionalViolatingFunctor P).map g = f := by
  obtain ⟨⟨f⟩, rfl⟩ := (violatingFunctor T (-1)).map_surjective f
  obtain ⟨g, rfl⟩ := (T).lin_surjective f
  exact ⟨(violatingFunctor B (-1)).map (InducedCategory.homMk (X := cut) (Y := cut) ((B).lin g)), rfl⟩

private theorem extra_end_scalar (f : End ((violatingFunctor T (-1)).obj cut)) :
    ∃ c : k, c • 𝟙 _ = f := by
  obtain ⟨g, rfl⟩ := additionalViolatingFunctor_surjective P f
  obtain ⟨c, hc⟩ := fundamentalSingleRed_algebraMap_surjective P g
  change c • 𝟙 target = g at hc
  refine ⟨c, ?_⟩
  change c • 𝟙 ((additionalViolatingFunctor P).obj target) = (additionalViolatingFunctor P).map g
  rw [← hc, Functor.map_smul]
  exact congrArg (fun f : End ((additionalViolatingFunctor P).obj target) => c • f)
    ((additionalViolatingFunctor P).map_id target).symm

private abbrev redFirst : Ord := ⟨(FirstWeight.boundaryAt () 1 0).val,
  (FirstWeight.boundaryAt () 1 0).property.1⟩

private theorem eq_redFirst (s : Ord) (hs : ¬ IsViolated s.val) : s = redFirst := by
  obtain ⟨r, hr⟩ := (FirstWeight.boundaryEquiv () 1).surjective ⟨s.val, s.property, hs⟩
  obtain rfl : r = 0 := Fin.fin_one_eq_zero r
  exact Subtype.ext (congrArg Subtype.val hr).symm

private theorem redFirst_end_scalar (f : End (downObj (Λ := fundWeights) T redFirst)) :
    ∃ c : k, c • 𝟙 _ = f := by
  have hf := extra_end_scalar P
  change ∀ f : End ((violatingFunctor T (downRightWeight RD fundWeights blackContent)).obj
    (downTriple RD fundWeights redFirst)), ∃ c : k, c • 𝟙 _ = f at hf
  exact hf f

private theorem matrix_entry_zero {i j : Ord} (h : IsViolated i.val ∨ IsViolated j.val)
    (f : downObj (Λ := fundWeights) T i ⟶ downObj (Λ := fundWeights) T j) : f = 0 := by
  rcases h with h | h
  · rw [← Category.id_comp f, downObj_id_eq_zero T i h, Limits.zero_comp]
  · rw [← Category.comp_id f, downObj_id_eq_zero T j h, Limits.comp_zero]

/-- Webster v3, Lemma 4.29, surjectivity for one fundamental red strand and
one downward black strand in type A₁. The natural comparison is the existing
ordinary diagram map. The red-first matrix entry is generated by scalars,
and an entry at the other loading vanishes by the left violating ideal. -/
theorem fundamentalSingleRed_ordinaryToDownwardMatrix_surjective :
    Function.Surjective (ordinaryToDownwardMatrix (Λ := fundWeights) B Q₁ d₁
      (fun _ _ => 1) (ν := blackContent)) := by
  intro f
  obtain ⟨c, hc⟩ := redFirst_end_scalar P (f redFirst redFirst)
  let G := ordinaryToDownwardMatrix (Λ := fundWeights) B Q₁ d₁ (fun _ _ => 1) (ν := blackContent)
  refine ⟨_, (G.commutes c).trans ?_⟩
  apply KLR.Diagram.MatEnd.ext
  intro i j
  by_cases hi : IsViolated i.val
  · exact (matrix_entry_zero P (.inl hi) _).trans (matrix_entry_zero P (.inl hi) _).symm
  by_cases hj : IsViolated j.val
  · exact (matrix_entry_zero P (.inr hj) _).trans (matrix_entry_zero P (.inr hj) _).symm
  obtain rfl := eq_redFirst i hi
  obtain rfl := eq_redFirst j hj
  change c • (1 : downwardMatrix (Λ := fundWeights) T blackContent) redFirst redFirst = _
  rw [KLR.Diagram.MatEnd.one_apply_self]
  exact hc

end Comparison

end Categorification.Stendhal.DoubleDiagram
