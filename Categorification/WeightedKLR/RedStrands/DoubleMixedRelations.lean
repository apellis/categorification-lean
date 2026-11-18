/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackDiagram
import Categorification.WeightedKLR.RedStrands.DoubleRedUp
import Categorification.Diagrams.CL.Presentation

/-!
# The mixed black identities of Webster's fullness argument

Webster, arXiv:1309.3796v2, §2.2, (2.3c) and (2.4a), included in the double
diagram relations of §4.5, Definition 4.24. In the order used by the proof
of Theorem 4.29, a downward strand is on the left and an upward strand is on
the right. These are the reflections of the CL relations on `E_i F_j`.
For distinct colours only the leading unit `t_{ji}` occurs. For equal
colours Webster sets `r_i = 1`; the additional summands pass through a cap,
a possibly fake bubble and a cup.

We adjoin these two local identities in every surrounding word to an
arbitrary presentation. This isolates precisely the black relations used
in the movement of upwards strands. A comparison of the polynomials in the
all-down KLR algebra with CL's dual parameters is a separate calculation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams CategoryTheory

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) (k : Type w) [CommRing k]

/-- The distinct- and equal-colour instances of (2.4a) and (2.3c) in a word. -/
inductive MixedBlackRelation (X : Type v) (I : Type u) (ℓ : ℕ)
  | distinct (μ : X) (L R : List (DoubleStrand I ℓ)) (i j : I) (ne : i ≠ j)
  | equal (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I)

private def mixedObj (μ : X) (L R : List (DoubleStrand I ℓ)) (i j : I) :=
  obj RD Λ μ (L ++ blackWord [up i, dn j] ++ R)

private def MixedBlackRelation.boundary : MixedBlackRelation X I ℓ → Obj (signature RD Λ)
  | .distinct μ L R i j _ => mixedObj RD Λ μ L R i j
  | .equal μ L R i => mixedObj RD Λ μ L R i i

/-- The linear combinations of raw diagrams imposed by (2.4a) and (2.3c).
The map `blackLinear` reflects them into the Webster convention. -/
def mixedBlackRelation (t : I → I → kˣ) (a : MixedBlackRelation X I ℓ) :
    LinDiagram k (a.boundary RD Λ) (a.boundary RD Λ) :=
  match a with
  | .distinct μ L R i j _ =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (LinDiagram.of (crossl RD i j η ≫ crossr RD i j η) -
      (t j i : k) • LinDiagram.of (𝟙 _))
  | .equal μ L R i =>
    let η := endWeight RD Λ μ L
    blackLinear RD Λ k μ L R (LinDiagram.of (𝟙 _) +
      LinDiagram.of (crossl RD i i η ≫ crossr RD i i η) - decompEFSum RD k i η)

/-- The distinct-colour relation is exactly the reflected CL relation for
`t_{ji}`. -/
theorem mixedBlackRelation_distinct_CL (S : CL.CLScalars C k) (μ : X)
    (L R : List (DoubleStrand I ℓ)) (i j : I) (h : i ≠ j) :
    mixedBlackRelation RD Λ k S.t (.distinct μ L R i j h) =
      blackLinear RD Λ k μ L R
        (CL.relationCL RD k S (.downupEF i j h (endWeight RD Λ μ L))) := rfl

/-- With Webster's `r_i=1`, the equal-colour relation is the reflection of
the CL decomposition on `E_i F_i`. -/
theorem mixedBlackRelation_equal_CL (S : CL.CLScalars C k) (μ : X)
    (L R : List (DoubleStrand I ℓ)) (i : I) (hi : S.r i = 1) :
    mixedBlackRelation RD Λ k S.t (.equal μ L R i) =
      blackLinear RD Λ k μ L R (s := [up i, dn i]) (t := [up i, dn i]) (CL.relationCL RD k S (.decompEF i (endWeight RD Λ μ L))) := by
  let η := endWeight RD Λ μ L
  let dbl := LinDiagram.of (crossl RD i i η ≫ crossr RD i i η) (R := k)
  have hs : (((S.r i)⁻¹ : kˣ) : k) ^ 2 • dbl = dbl := by rw [hi]; simp
  exact congrArg (fun x => blackLinear RD Λ k μ L R
    (LinDiagram.of (𝟙 _) + x - decompEFSum RD k i η)) hs.symm

/-- Adjoin the two families of mixed black identities to an arbitrary
presentation on the double Stendhal signature. -/
def addMixedBlackRelations (t : I → I → kˣ) (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels _ (MixedBlackRelation.boundary RD Λ) (MixedBlackRelation.boundary RD Λ)
    (mixedBlackRelation RD Λ k t)

variable {k}

/-- The morphism induced in a double presentation by a linear combination
of black diagrams in the specified context. -/
def blackMorphism (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    (L R : List (DoubleStrand I ℓ)) {s z : List (Letter I)} :
    LinDiagram k (ob RD (endWeight RD Λ μ L) s) (ob RD (endWeight RD Λ μ L) z) →ₗ[k]
      (P.obj (obj RD Λ μ (L ++ blackWord s ++ R)) ⟶ P.obj (obj RD Λ μ (L ++ blackWord z ++ R))) :=
  (P.linFunctor.mapLinearMap k).comp (blackLinear RD Λ k μ L R)

private theorem blackMorphism_comp (P : Presentation.{w, max u v} (signature RD Λ) k)
    (μ : X) (L R : List (DoubleStrand I ℓ)) {s z w : List (Letter I)}
    (f : LinDiagram k (ob RD (endWeight RD Λ μ L) s) (ob RD (endWeight RD Λ μ L) z))
    (g : LinDiagram k (ob RD (endWeight RD Λ μ L) z) (ob RD (endWeight RD Λ μ L) w)) :
    blackMorphism RD Λ P μ L R (f ≫ g) =
      blackMorphism RD Λ P μ L R f ≫ blackMorphism RD Λ P μ L R g := by
  change P.lin (blackLinear RD Λ k μ L R (f ≫ g)) = _
  rw [blackLinear_comp, Presentation.lin_comp]
  rfl

private theorem blackMorphism_id (P : Presentation.{w, max u v} (signature RD Λ) k)
    (μ : X) (L R : List (DoubleStrand I ℓ)) (s : List (Letter I)) :
    blackMorphism RD Λ P μ L R (LinDiagram.of (𝟙 (ob RD (endWeight RD Λ μ L) s))) = 𝟙 _ := by
  change P.lin (blackLinear RD Λ k μ L R (LinDiagram.of (𝟙 _))) = _
  rw [blackLinear_of, Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

variable (t : I → I → kˣ) (P : Presentation.{w, max u v} (signature RD Λ) k)
local notation "Q" => addRedUpRelations RD Λ k (addMixedBlackRelations RD Λ k t P)
local notation "B" => blackMorphism RD Λ Q

/-- The two actual mixed crossings on different colours compose to the
leading unit times the identity, as in Webster (2.4a). -/
theorem mixedBlack_ne (μ : X) (L R : List (DoubleStrand I ℓ)) (i j : I) (hij : i ≠ j) :
    let η := endWeight RD Λ μ L
    B μ L R (LinDiagram.of (crossl RD i j η)) ≫ B μ L R (LinDiagram.of (crossr RD i j η)) =
      (t j i : k) • 𝟙 _ := by
  let η := endWeight RD Λ μ L
  have h := (Q).lin_rel_self (.inl (.inr (.distinct μ L R i j hij)))
  change B μ L R (LinDiagram.of (crossl RD i j η ≫ crossr RD i j η) -
      (t j i : k) • LinDiagram.of (𝟙 _)) = 0 at h
  rw [map_sub, map_smul, sub_eq_zero, LinDiagram.of_comp, blackMorphism_comp, blackMorphism_id] at h
  exact h

/-- For equal colours the identity is the negative double crossing plus
the cap–bubble–cup terms of Webster (2.3c), all in the given word. -/
theorem mixedBlack_eq (μ : X) (L R : List (DoubleStrand I ℓ)) (i : I) :
    let η := endWeight RD Λ μ L
    𝟙 ((Q).obj (obj RD Λ μ (L ++ blackWord [up i, dn i] ++ R))) =
      -(B μ L R (LinDiagram.of (crossl RD i i η)) ≫ B μ L R (LinDiagram.of (crossr RD i i η))) +
      ∑ f ∈ Finset.range (ip RD i η).toNat, ∑ g ∈ Finset.range (f + 1),
        B μ L R (LinDiagram.of (dotCapEF RD η i (f - g))) ≫
        B μ L R (ccwL RD k η i (-ip RD i η - 1 + g)) ≫
        B μ L R (LinDiagram.of (cupDotEF RD η i ((ip RD i η).toNat - 1 - f))) := by
  let η := endWeight RD Λ μ L
  have h := (Q).lin_rel_self (.inl (.inr (.equal μ L R i)))
  change B μ L R (LinDiagram.of (𝟙 _) + LinDiagram.of (crossl RD i i η ≫ crossr RD i i η) -
    decompEFSum RD k i η) = 0 at h
  rw [map_sub, map_add, sub_eq_zero, blackMorphism_id, LinDiagram.of_comp, blackMorphism_comp] at h
  simp only [decompEFSum, map_sum, blackMorphism_comp] at h
  dsimp only
  rw [← h]
  abel

end Categorification.Stendhal.DoubleDiagram
