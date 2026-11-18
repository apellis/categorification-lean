/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleVacuum
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations
import Categorification.WeightedKLR.RedStrands.DoubleRedUp
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations

/-!
# The scalar character of the empty double Stendhal boundary

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, for the empty red family
and the vacuum. Assign the coefficient module to the empty boundary, the
zero module to every nonempty boundary, and zero to every layer. This
detects scalars after imposing the violating quotient and the implemented
mixed, red/up and all-down relations on a free base.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
    [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
    {Λ : Fin 0 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
    {k : Type w} [CommRing k]
local notation "labels" => Subtype.val ∘ Λ

private def vacuumInterpretation (S : Signature) (k : Type w) [CommRing k] :
    Interpretation S (ModuleCat.{w} k) where
  obj a := ModuleCat.of k (PLift (a.word = []) → k)
  layer _ _ := 0

private theorem map_from_nonempty (S : Signature) (k : Type w) [CommRing k]
    {a : Obj S} (h : a.word ≠ []) {N : ModuleCat.{w} k}
    (f : (vacuumInterpretation S k).obj a ⟶ N) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : z = 0 := funext fun e => (h e.down).elim
  rw [hz, map_zero, map_zero]

private theorem map_with_layer (S : Signature) (k : Type w) [CommRing k]
    {a b : Obj S} (d : a ⟶ b) (h : Diagram.layers d ≠ []) :
    (vacuumInterpretation S k).functor.map d = 0 := by
  obtain ⟨ls, hc⟩ := d
  cases ls with
  | nil => exact (h rfl).elim
  | cons L ls =>
    change (vacuumInterpretation S k).functor.map (Diagram.mk (L :: ls) hc) = 0
    rw [Interpretation.functor_map_mk_cons (vacuumInterpretation S k) L ls hc]
    change _ ≫ (0 : (vacuumInterpretation S k).obj L.dom ⟶ _) ≫ _ = _
    simp

local notation "S" => signature RD (Subtype.val ∘ Λ)

variable (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)

private theorem vacuum_respects (hp : ∀ i, (P.dom i).word ≠ []) :
    P.Respects (vacuumInterpretation S k).functor where
  rel i u v hw := map_from_nonempty S k (a := (P.dom i).whisker u v)
    (by simp [hp i]) _
  interchange x hx u v hw := by
    rw [InterchangeData.rel, LinDiagram.whisker_sub, LinDiagram.whisker_smul,
      Functor.map_sub, Functor.map_smul, freeLift_map_whisker_of, freeLift_map_whisker_of]
    rw [map_with_layer S k _ (by exact List.cons_ne_nil _ _),
      map_with_layer S k _ (by exact List.cons_ne_nil _ _)]
    let H := (vacuumInterpretation S k).obj (x.dom.whisker u v) ⟶
      (vacuumInterpretation S k).obj (x.cod.whisker u v)
    change (0 : H) - (x.sign : k) • (0 : H) = 0
    simp

private def vacuumAction (hp : ∀ i, (P.dom i).word ≠ []) :
    ViolatingCategory P (0 : X) ⥤ ModuleCat.{w} k :=
  DoubleViolatingQuotient.lift k (tripleObj P)
    (inducedFunctor (tripleObj P (right := (0 : X))) ⋙ P.lift (vacuum_respects P hp)) (fun b hb =>
    map_from_nonempty S k (a := obj RD labels 0 b.val.word) (by
      intro h
      have hw := congrArg (List.map Prod.snd) h
      change (colours RD labels 0 b.val.word).map Prod.snd = [] at hw
      rw [forget_colours] at hw
      obtain ⟨l,hl⟩ := hb
      rw [hw] at hl; contradiction) _)

private instance (hp : ∀ i, (P.dom i).word ≠ []) : (vacuumAction P hp).Additive := by
  unfold vacuumAction
  infer_instance

private instance (hp : ∀ i, (P.dom i).word ≠ []) : (vacuumAction P hp).Linear k := by
  unfold vacuumAction
  infer_instance

private theorem scalar_injective (hp : ∀ i, (P.dom i).word ≠ []) :
    Function.Injective (algebraMap k (End (vacuumObj P))) := by
  let G := vacuumAction P hp
  intro r s h
  change r • 𝟙 (vacuumObj P) = s • 𝟙 (vacuumObj P) at h
  have hm := congrArg G.map h
  rw [G.map_smul, G.map_smul, G.map_id] at hm
  have hv := congrArg (fun f : End (G.obj (vacuumObj P)) =>
    (f.hom (fun _ => (1 : k))) ⟨rfl⟩) hm
  change r * 1 = s * 1 at hv
  simpa using hv

private theorem word_nonempty (μ : X) (l : List (DoubleStrand I 0)) (h : l ≠ []) :
    (obj RD labels μ l).word ≠ [] := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a l => exact List.cons_ne_nil _ _

section LocalRelations

variable (base : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
    (t : I → I → kˣ) (Q : I ⊕ Fin 0 → I ⊕ Fin 0 → MvPolynomial (Fin 2) k)

local notation "down" => addDownRelations RD labels Q base
local notation "mixed" => addMixedBlackRelations RD labels k t down
local notation "signed" => addRedUpRelations RD labels k mixed

private theorem local_relation_domains [IsEmpty base.Rel] (i : (signed).Rel) : ((signed).dom i).word ≠ [] := by
  rcases i with ((i | d) | m) | r
  · exact isEmptyElim i
  · rcases d with ⟨μ,L,R,rel,left,right⟩
    have hrel : rel.dom.word ≠ [] := by
      cases rel <;> exact List.cons_ne_nil _ _
    apply word_nonempty
    change L ++ ((left.word ++ rel.dom.word ++ right).map DoubleStrand.down) ++ R ≠ []
    simp [hrel]
  · cases m with
    | distinct μ L R a b hn =>
      apply word_nonempty
      simp [blackWord]
    | equal μ L R a =>
      apply word_nonempty
      simp [blackWord]
  · exact Fin.elim0 r.red

/-- In the empty-red, empty-black block of Webster's Lemma 4.28
(arXiv:1309.3796v2), scalar multiplication gives the whole endomorphism
algebra for the signed presentation with the mixed black, red/up and
all-down relations over a free base. -/
theorem vacuum_algebraMap_bijective [IsEmpty base.Rel] :
    Function.Bijective (algebraMap k (End (vacuumObj signed))) :=
  ⟨scalar_injective signed (local_relation_domains base t Q), vacuum_algebraMap_surjective signed⟩

end LocalRelations

end Categorification.Stendhal.DoubleDiagram
