/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownMatrix
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations

/-!
# The ordinary diagram map to the all-down block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Lemma 4.28. Adjoin the downward, mixed black, and red/up relations to a
signed diagram presentation. The ordinary Stendhal diagram map sends each
generator to the same diagram with its black strands pointing downward, and
descends to the violating quotient used by the all-down inclusion in Theorem 4.29.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram TypeA
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (scalars : I → I → kˣ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "labels" => (Subtype.val ∘ Λ)
local notation "R" => affineCoverQ Q exponents
local notation "P↓" => addDownRelations RD labels R P
local notation "P₁" => addRedUpRelations RD labels k (addMixedBlackRelations RD labels k scalars (P↓))
local notation "W" => fun s : Seq μ => Presentation.obj (KLR.Diagram.pres k R) (ob (word s))

private theorem downIdeal_le (a b : Obj (signature RD labels)) : (P↓).ideal a b ≤ (P₁).ideal a b := by
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨rel, l, r, h, pre, post⟩ := hf
  apply Submodule.subset_span
  cases rel with
  | user i =>
    exact Presentation.IdealGen.intro (P := P₁) (.user (Sum.inl (Sum.inl i))) l r h pre post
  | interchange x hx =>
    exact Presentation.IdealGen.intro (P := P₁) (.interchange x hx) l r h pre post

private def signedQuotientFunctor : (P↓).Presented ⥤ (P₁).Presented :=
  CategoryTheory.Quotient.lift (P↓).homRel (P₁).linFunctor fun _ _ f g h =>
    ((P₁).lin_eq_iff f g).mpr (downIdeal_le P Q exponents scalars _ _ h)

private theorem lin_comp_signedQuotient :
    (P↓).linFunctor ⋙ signedQuotientFunctor P Q exponents scalars = (P₁).linFunctor := rfl

instance : (signedQuotientFunctor P Q exponents scalars).Additive := by
  have : (P↓).linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : ((P↓).linFunctor ⋙ signedQuotientFunctor P Q exponents scalars).Additive := by
    rw [lin_comp_signedQuotient]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp (P↓).linFunctor _

instance : (signedQuotientFunctor P Q exponents scalars).Linear k := by
  have : (P↓).linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : ((P↓).linFunctor ⋙ signedQuotientFunctor P Q exponents scalars).Linear k := by
    rw [lin_comp_signedQuotient]
    infer_instance
  exact Functor.linear_of_full_essSurj_comp (P↓).linFunctor _

private theorem signedQuotient_map_diag {a b : Obj (signature RD labels)} (d : a ⟶ b) :
    (signedQuotientFunctor P Q exponents scalars).map ((P↓).diag d) = (P₁).diag d := rfl

local notation "F" => downPresentedFunctor RD labels R P 0 [] [] ⋙
  signedQuotientFunctor P Q exponents scalars

private theorem downContextObj_word (s : Seq μ) :
    downContextObj RD labels 0 [] [] (ob (word s)) =
      obj RD labels 0 ((word s).map DoubleStrand.down) := by
  simp [downContextObj, ob]

private theorem diagramObj (s : Seq μ) : (F).obj (W s) = signedSeqObj (P₁) s :=
  congrArg (P₁).obj (downContextObj_word (RD := RD) (Λ := Λ) s)

local notation "G" => downMatrixOfFunctor (P₁) R (F) (diagramObj P Q exponents scalars (ν := ν))

private theorem signed_diag_cast {a b a' b' : Obj (signature RD labels)}
    (d : a ⟶ b) (ha : a = a') (hb : b = b') :
    (P₁).diag (Diagram.cast d ha hb) =
      eqToHom (congrArg (P₁).obj ha).symm ≫ (P₁).diag d ≫ eqToHom (congrArg (P₁).obj hb) := by
  subst ha hb
  simp

private theorem translate_layer (s t : Ord) (l r : List (I ⊕ Fin ℓ))
    (g : KLR.Diagram.Gen (I ⊕ Fin ℓ))
    (hs : l ++ g.dom ++ r = word s.val) (ht : l ++ g.cod ++ r = word t.val)
    {g' : Move I ℓ} (hg : downMove g = some g') :
    downFunctorEntry (P₁) R (F) (diagramObj P Q exponents scalars) s t
      ((KLR.Diagram.pres k R).diag (dl l g r hs ht)) =
      downLayer (P₁) s t (l.map DoubleStrand.down) g' (r.map DoubleStrand.down)
        (by simpa only [(downMove_words hg).1, ← List.map_append] using
          congrArg (List.map DoubleStrand.down) hs)
        (by simpa only [(downMove_words hg).2, ← List.map_append] using
          congrArg (List.map DoubleStrand.down) ht) := by
  have hg' : downMove (lay l g r).gen = some g' := hg
  have he := downPresentedFunctor_layer RD labels R P 0 [] []
    (a := ob (word s.val)) (b := ob (word t.val)) (lay l g r) (lay_valid ..)
    (obj_ext hs) (obj_ext ht) (g := g') hg'
  have he' := (congrArg (signedQuotientFunctor P Q exponents scalars).map he).trans
    (signedQuotient_map_diag P Q exponents scalars _)
  unfold downFunctorEntry dl
  rw [Functor.comp_map, he']
  change signedDownEntry (P₁) s t
    (eqToHom (congrArg (P₁).obj (downContextObj_word s.val)).symm ≫ _ ≫
      eqToHom (congrArg (P₁).obj (downContextObj_word t.val))) = _
  rw [← signed_diag_cast P Q exponents scalars _ (downContextObj_word s.val) (downContextObj_word t.val)]
  refine congrArg (fun d : obj RD labels 0 ((word s.val).map DoubleStrand.down) ⟶
      obj RD labels 0 ((word t.val).map DoubleStrand.down) =>
    signedDownEntry (P₁) s t ((P₁).diag d)) ?_
  apply Diagram.ext
  simp only [Diagram.layers_cast]
  calc
    _ = [layer RD labels 0 (l.map DoubleStrand.down) g' (r.map DoubleStrand.down)] := by
      simpa only [lay_left, lay_right, List.nil_append, List.append_nil] using
        layers_downLayerDiagram RD labels 0 [] [] (lay l g r) hg'
    _ = _ := rfl

private theorem translate_layer_zero (s t : Ord) (l r : List (I ⊕ Fin ℓ))
    (g : KLR.Diagram.Gen (I ⊕ Fin ℓ))
    (hs : l ++ g.dom ++ r = word s.val) (ht : l ++ g.cod ++ r = word t.val)
    (hg : downMove g = none) :
    downFunctorEntry (P₁) R (F) (diagramObj P Q exponents scalars) s t
      ((KLR.Diagram.pres k R).diag (dl l g r hs ht)) = 0 := by
  have he := downPresentedFunctor_layer_zero RD labels R P 0 [] []
    (a := ob (word s.val)) (b := ob (word t.val)) (lay l g r) (lay_valid ..)
    (obj_ext hs) (obj_ext ht) hg
  unfold downFunctorEntry dl
  rw [Functor.comp_map, he, Functor.map_zero, Limits.zero_comp, Limits.comp_zero, map_zero]

private theorem translate_dot (s : Ord) (a : Fin m) :
    downFunctorEntry (P₁) R (F) (diagramObj P Q exponents scalars) s s (dotE k R s.val a) =
      downDot (P₁) s a := by
  cases h : s.val.lbl a with
  | inl i =>
    rw [downDot_of_black (P₁) s a i h]
    exact translate_layer P Q exponents scalars s s ((word s.val).take a) ((word s.val).drop (a + 1))
      (.dot (s.val.lbl a)) (word_split s.val a) (word_split s.val a) (g' := .black (.dot (false, i)))
      (by rw [h]; rfl)
  | inr r =>
    rw [downDot_eq_zero_of_red (P₁) s a (by simp [h])]
    exact translate_layer_zero P Q exponents scalars s s ((word s.val).take a) ((word s.val).drop (a + 1))
      (.dot (s.val.lbl a)) (word_split s.val a) (word_split s.val a) (by rw [h]; rfl)

private theorem translate_cross (j : ℕ) (s t : Ord) (ht : t.val = sadj m j • s.val) :
    downFunctorEntry (P₁) R (F) (diagramObj P Q exponents scalars) s t
      (crossE k R s.val j ≫ eqToHom (congrArg W ht.symm)) = downCross (P₁) s t j := by
  by_cases hj : j + 1 < m
  · let l := (word s.val).take j
    let r := (word s.val).drop (j + 2)
    let g : KLR.Diagram.Gen (I ⊕ Fin ℓ) := .cross (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩)
    have hs : l ++ g.dom ++ r = word s.val := word_split₂ s.val hj
    have htop : l ++ g.cod ++ r = word t.val := by rw [ht, word_sadj s.val hj]; rfl
    have hd : crossE k R s.val j ≫ eqToHom (congrArg W ht.symm) =
        (KLR.Diagram.pres k R).diag (dl l g r hs htop) := by
      rw [crossE_def _ hj, diag_comp_eqToHom _ (congrArg (fun x => ob (word x)) ht.symm)]
      congr 1
    rw [hd]
    cases hg : downMove g with
    | none =>
      rw [translate_layer_zero P Q exponents scalars s t l r g hs htop hg]
      symm
      unfold downCross
      rw [dite_eq_left hj, dite_eq_left ht]
      split
      · rfl
      · rename_i g' hg'
        have hoc : downMove g = some g' := hg'
        rw [hg] at hoc
        contradiction
    | some g' =>
      rw [downCross_of_move (P₁) s t j hj ht g' hg]
      exact translate_layer P Q exponents scalars s t l r g hs htop hg
  · rw [crossE_of_le _ (Nat.le_of_not_lt hj), Limits.zero_comp, downFunctorEntry_zero]
    change 0 = downΨ (P₁) j s t
    rw [downΨ_eq_zero (P₁) (Nat.le_of_not_lt hj), MatEnd.zero_apply]

/-- The map of Webster, arXiv:1309.3796v2, Lemma 4.28, sending ordinary
Stendhal diagrams to the same diagrams in the all-down block after adjoining
the downward, mixed black, and red/up local relations. For Webster's diagram
algebra the exponents are the coroot pairings in Definition 4.5. -/
def ordinaryToDownwardMatrix : TensorProductAlgebra k Q exponents ν →ₐ[k] downwardMatrix (P₁) ν :=
  allDownMap (P₁) Q exponents (G)
    (fun s => downMatrixOfFunctor_e (P₁) R (F) (diagramObj P Q exponents scalars) s)
    (fun a => downMatrixOfFunctor_x (P₁) R (F) (diagramObj P Q exponents scalars) a
      (fun s => translate_dot P Q exponents scalars s a))

private theorem ordinaryToDownwardMatrix_comp : (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)).comp
    (affineTensorProjection exponents ν) = G :=
  allDownMap_comp_affine ..

/-- The ordinary comparison sends boundary identities to diagonal matrix units. -/
theorem ordinaryToDownwardMatrix_e (s : Seq μ) :
    ordinaryToDownwardMatrix P Q exponents scalars (affineTensorProjection exponents ν (KLRAlgebra.e s)) =
      downE (P₁) s :=
  (DFunLike.congr_fun (ordinaryToDownwardMatrix_comp P Q exponents scalars) _).trans
    (downMatrixOfFunctor_e ..)

/-- The ordinary comparison sends a dot to the diagonal sum of signed black dots. -/
theorem ordinaryToDownwardMatrix_x (a : Fin m) :
    ordinaryToDownwardMatrix P Q exponents scalars (affineTensorProjection exponents ν (KLRAlgebra.x a)) =
      downX (P₁) a :=
  (DFunLike.congr_fun (ordinaryToDownwardMatrix_comp P Q exponents scalars) _).trans
    (downMatrixOfFunctor_x (P₁) R (F) (diagramObj P Q exponents scalars) a
      (fun s => translate_dot P Q exponents scalars s a))

/-- The ordinary comparison sends each crossing to its signed all-down crossing. -/
theorem ordinaryToDownwardMatrix_ψ (j : ℕ) :
    ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)
      (affineTensorProjection exponents ν (KLRAlgebra.ψ j)) = downΨ (P₁) j :=
  (DFunLike.congr_fun (ordinaryToDownwardMatrix_comp P Q exponents scalars) _).trans
    (downMatrixOfFunctor_ψ (P₁) R (F) (diagramObj P Q exponents scalars) j
      (translate_cross P Q exponents scalars j))

/-- The red exponents in Webster's bigon relation (arXiv:1309.3796v2,
Definition 4.5, equation (4.2)), when the coroot pairings have finite support. -/
def corootExponents
    (finiteSupport : ∀ r : Fin ℓ, (Function.support (fun i =>
      (RD.pair (RD.iY i) (Λ r).val).toNat)).Finite) : Fin ℓ → I →₀ ℕ :=
  fun r => Finsupp.ofSupportFinite _ (finiteSupport r)

@[simp] theorem corootExponents_pair
    (finiteSupport : ∀ r : Fin ℓ, (Function.support (fun i =>
      (RD.pair (RD.iY i) (Λ r).val).toNat)).Finite) (r : Fin ℓ) (i : I) :
    (corootExponents (Λ := Λ) finiteSupport r i : ℤ) = RD.pair (RD.iY i) (Λ r).val :=
  Int.toNat_of_nonneg ((Λ r).property i)

/-- For a finite set of simple roots the red exponents of the ordinary
comparison are the coroot pairings of the signed weights. -/
abbrev ordinaryToDownwardMatrix_ofWeights [Finite I] :=
  ordinaryToDownwardMatrix P Q (corootExponents (Λ := Λ) (fun _ => Set.toFinite _)) scalars (ν := ν)

end Categorification.Stendhal.DoubleDiagram
