/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleNormalizedRedBubbleQ
import Categorification.WeightedKLR.RedStrands.DoubleRedBubbleRangeQ
import Categorification.WeightedKLR.RedStrands.DoubleSignedBubbleSweepQ
import Categorification.WeightedKLR.RedStrands.DoublePresentationUnion

/-! # Transport of arbitrary bubble polynomials past red

In the bubble-elimination step of Webster, arXiv:1309.3796v2, §4.5,
Lemma 4.28, the image of the empty black word endomorphism algebra is
independent of the choice of the adjacent cut at red.

This is the version of `DoubleRedCutBubbles` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (P : Presentation.{w,max u v} (signature RD Λ) k) (μ : X)
  (L R w : List (DoubleStrand I ℓ)) (hw : L ++ R = w)

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (r : Fin ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "Pr" => addRedUpSlideRelations RD Λ P
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents)
  (addRedUpRelations RD Λ k (addRedCapRelations RD Λ (addRedCupRelations RD Λ (addBlackKLRelationsQ RD Λ sc Pr))))
local notation "W" => L ++ [red] ++ R

private theorem signedKLRelationsQ (z : (CLQ.pres RD k sc).Rel) :
    (Pd).lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel z)) = 0 :=
  (Pd).lin_rel_self (.inl (.inl (.inl (.inl (.inr z)))))

local notation "hKL" => signedKLRelationsQ RD Λ sc P Q exponents

/-- Across a red strand the images of the two black bubble algebras coincide,
including when the coroot pairing changes sign. The red exponents agree
with the shift for every simple root. -/
theorem blackCutAlgHom_range_eq_across_redQ
    (hδ : ∀ i, ip RD i (endWeight RD Λ μ (L ++ [red])) =
      ip RD i (endWeight RD Λ μ L) + (exponents r i : ℤ)) :
    (blackCutAlgHomQ RD Λ sc (Pd) hKL μ L (red :: R) (W) (by simp [List.append_assoc])).range =
    (blackCutAlgHomQ RD Λ sc (Pd) hKL μ (L ++ [red]) R (W) rfl).range := by
  apply normalizedBubble_range_eqQ
  intro i o d
  change blackCutHomQ RD Λ sc (Pd) hKL μ L (red :: R) W (by simp [List.append_assoc])
      ((CLQ.pres RD k sc).lin _) = blackCutHomQ RD Λ sc (Pd) hKL μ (L ++ [red]) R W rfl ((CLQ.pres RD k sc).lin _)
  rw [blackCutHom_linQ, blackCutHom_linQ, Presentation.lin_cast, Presentation.lin_cast]
  exact normalizedBubble_slideQ RD Λ sc Q exponents P μ L i r R (hδ i) o d

/-- Further relations preserve insertion at every cut. -/
theorem extension_map_blackCutHomQ (J : Presentation.{w,max u v} (signature RD Λ) k)
    (inc : ∀ a b, P.ideal a b ≤ J.ideal a b)
    (hP : ∀ z : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel z)) = 0)
    (hJ : ∀ z : (CLQ.pres RD k sc).Rel, J.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel z)) = 0)
    (β : End ((CLQ.pres RD k sc).obj (ob RD (endWeight RD Λ μ L) []))) :
    (P.extension J inc).map (blackCutHomQ RD Λ sc P hP μ L R w hw β) =
      blackCutHomQ RD Λ sc J hJ μ L R w hw β := by
  obtain ⟨f,rfl⟩ := (CLQ.pres RD k sc).lin_surjective β
  rw [blackCutHom_linQ, blackCutHom_linQ, Presentation.extension_map_lin]

/-- Every black bubble polynomial to the right of red has a representative
on the left in any presentation containing the signed bubble relations.
The exponent condition is imposed in every colour. -/
theorem redBubbleSlidesLeft_of_ideal_leQ (J : Presentation.{w,max u v} (signature RD Λ) k)
    (inc : ∀ a b, (Pd).ideal a b ≤ J.ideal a b)
    (hJ : ∀ z : (CLQ.pres RD k sc).Rel, J.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel z)) = 0)
    (hshift : ∀ r i, (exponents r i : ℤ) = ip RD i (Λ r)) :
    RedBubbleSlidesLeftQ RD Λ sc J hJ μ w := by
  intro L R r hw
  dsimp only
  intro β _
  subst w
  have hδ (i : I) : ip RD i (endWeight RD Λ μ (L ++ [Sum.inr r])) =
      ip RD i (endWeight RD Λ μ L) + (exponents r i : ℤ) := by
    rw [endWeight_append, hshift]
    simp [ip, endWeight, DoubleStrand.weight]
  let ha : L ++ [Sum.inr r] ++ R = L ++ [Sum.inr r] ++ R := rfl
  let hb : L ++ (Sum.inr r :: R) = L ++ [Sum.inr r] ++ R := by simp [List.append_assoc]
  let FR := blackCutAlgHomQ RD Λ sc (Pd) hKL μ (L ++ [Sum.inr r]) R _ ha
  let FL := blackCutAlgHomQ RD Λ sc (Pd) hKL μ L (Sum.inr r :: R) _ hb
  have he : FL.range = FR.range := blackCutAlgHom_range_eq_across_redQ RD Λ sc P μ L R Q exponents r hδ
  obtain ⟨γ,hγ⟩ := (he.ge (show FR (CLQ.EndOne.of β) ∈ FR.range from ⟨_,rfl⟩))
  refine ⟨γ.val, CLQ.isBub_of_prop36 (RD := RD) _ (CLQ.prop36 _) _, ?_⟩
  have hc : blackCutHomQ RD Λ sc (Pd) hKL μ (L ++ [Sum.inr r]) R _ ha β =
      blackCutHomQ RD Λ sc (Pd) hKL μ L (Sum.inr r :: R) _ hb γ.val := hγ.symm
  have lift := congrArg (fun f => ((Pd).extension J inc).map f) hc
  exact (extension_map_blackCutHomQ RD Λ sc (Pd) μ (L ++ [Sum.inr r]) R _ ha J inc hKL hJ β).symm.trans
    (lift.trans (extension_map_blackCutHomQ RD Λ sc (Pd) μ L (Sum.inr r :: R) _ hb J inc hKL hJ γ.val))

end Categorification.Stendhal.DoubleDiagram
