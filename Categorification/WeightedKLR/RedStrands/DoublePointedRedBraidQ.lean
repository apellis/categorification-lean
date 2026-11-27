/-
Copyright (rightReal) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoublePointedRedBraid
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidBubblesQ
import Categorification.WeightedKLR.RedStrands.DoublePointedBlackClosure
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality

/-!
# The correction of the pointed red braid

Webster, arXiv:1309.3796v2, Definitions 4.5 and 4.24. Closing the braid
with extra dots on the left black leg shifts exactly that bubble's dot
count. In a sign-changing region the real bubble thresholds turn the
closed correction into the mixed coefficient of the two inverse series.

This is the version of `DoublePointedRedBraid` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ) (R : List (DoubleStrand I ℓ))
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "rS" => (Sum.inr r : DoubleStrand I ℓ)
local notation "initial" => (L ++ [rS] ++ R)
local notation "Qₐ" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "Pb" => addBlackKLRelationsQ RD Λ sc P
local notation "Pcup" => addRedCupRelations RD Λ (Pb)
local notation "Pcap" => addRedCapRelations RD Λ (Pcup)
local notation "Pup" => addRedUpRelations RD Λ k (Pcap)
local notation "Pd" => addDownRelations RD Λ Qₐ (Pup)
local notation "dL" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "BObj" => (Presentation.obj (Pd) (obj RD Λ μ initial))
local notation "oid" => (KLR.Diagram.ob [dL, rL, dL])
local notation "ellDot" => (End.of (Presentation.diag (P₀) (KLR.Diagram.E0 dL rL dL)))
local notation "rDot" => (End.of (Presentation.diag (P₀) (KLR.Diagram.E2 dL rL dL)))
local notation "close" => closeRedBraid RD Λ μ L i r R Q exponents (Pup)

/-- Close the braid with extra dots below the braid on its left inner leg. -/
def closePointedRedBraidQ (N : ℕ) : End ((P₀).obj oid) →ₗ[k] End BObj :=
  (close).comp (LinearMap.mulRight k (ellDot ^ N))

local notation "pointed" => closePointedRedBraidQ RD Λ sc μ L i r R Q exponents P

variable [DecidableEq I]

local notation "leftReal" => (fun a : ℕ => End.of (Presentation.diag (Pd) (cwBubbleBeforeRed RD Λ μ L i r R a)))
local notation "rightReal" => (fun b : ℕ => End.of (Presentation.diag (Pd) (ccwBubbleAfterRed RD Λ μ L i r R b)))
local notation "nL" => (ip RD i (endWeight RD Λ μ L))
local notation "nR" => (ip RD i (endWeight RD Λ μ (L ++ [rS])))
local notation "degreeZeroBefore" => (Int.toNat (-nL - 1))
local notation "degreeZeroAfter" => (Int.toNat (nR - 1))

omit [DecidableEq I] in
private theorem bubbleRealZeroQ {u v : List (DoubleStrand I ℓ)}
    (e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ initial)
    (f : End (ob RD (endWeight RD Λ μ u) [])) (hf : (CLQ.pres RD k sc).diag f = 0) :
    (Pd).diag (Diagram.cast (blackDiagram RD Λ μ u v f) e e) = 0 := by
  have h : (CLQ.pres RD k sc).lin (LinDiagram.of f) = (CLQ.pres RD k sc).lin 0 := by
    rw [Presentation.lin_of, Presentation.lin_zero, hf]
  have hkl := blackContext_lin_eq_of_KL_eq_suffixQ RD Λ sc μ u v [] P (LinDiagram.of f) 0 h
  have hq : (Pd).lin (blackLinear RD Λ k μ u v (LinDiagram.of f)) =
      (Pd).lin (blackLinear RD Λ k μ u v (0 : LEnd RD k (ob RD (endWeight RD Λ μ u) []))) :=
    lin_eq_addRels (Pup) (lin_eq_addRels (Pcap)
      (lin_eq_addRels (Pcup) (lin_eq_addRels (Pb) hkl)))
  rw [blackLinear_of, Presentation.lin_of, map_zero, Presentation.lin_zero] at hq
  rw [Presentation.diag, ← LinDiagram.cast_of, Presentation.lin_cast, Presentation.lin_of, hq]
  simp

omit [DecidableEq I] in
private theorem clockwiseReal_before_zeroQ (a : ℕ) (ha : a < degreeZeroBefore) :
    (leftReal) a = 0 := by
  unfold cwBubbleBeforeRed
  apply bubbleRealZeroQ RD Λ sc μ L r R Q exponents P
  rw [← Presentation.lin_of, NF.lin_ccwReal]
  exact CLQ.dg_ccwNeg RD k sc _ _ _ (by omega)

omit [DecidableEq I] in
private theorem counterclockwiseReal_after_zeroQ (b : ℕ) (hb : b < degreeZeroAfter) :
    (rightReal) b = 0 := by
  unfold ccwBubbleAfterRed
  apply bubbleRealZeroQ RD Λ sc μ L r R Q exponents P
  rw [← Presentation.lin_of, NF.lin_cwReal]
  exact CLQ.dg_cwNeg RD k sc _ _ _ (by omega)

omit [DecidableEq I] in
private theorem redBraidDots_commute : Commute rDot ellDot := by
  let τ : Multiset (I ⊕ Fin ℓ) := ([dL, rL, dL] : List (I ⊕ Fin ℓ))
  let s := KLR.KLRAlgebra.Seq.ofList [dL, rL, dL] (ν := τ) rfl
  exact KLR.Diagram.DiagR.dotE_comm (k := k) (Q := Qₐ) s ⟨0, by simp [τ]⟩ ⟨2, by simp [τ]⟩

/-- The difference of the pointed braid closures is the mixed bubble
convolution in degree `N + 1`. This identifies the correction before
evaluating the two pointed braid diagrams. -/
theorem pointedRedBraid_sub_eq_convolutionQ (N : ℕ) (hN : N ≤ degreeZeroBefore)
    (hneg : nL ≤ -1) (hpos : 1 ≤ nR) (hδ : nR = nL + (exponents r i : ℤ)) :
    (pointed) N ((P₀).diag (KLR.Diagram.braidL dL rL dL)) -
      (pointed) N ((P₀).diag (KLR.Diagram.braidR dL rL dL)) =
    sconv (fun a => (leftReal) (degreeZeroBefore + a)) (fun b => (rightReal) (degreeZeroAfter + b)) (N + 1) := by
  -- Apply the pointed closure to the underlying downward braid relation.
  have hb := KLR.Diagram.braidQ_at Qₐ (u := []) (v := []) (c := dL) (d := rL)
    Sum.inl_ne_inr (KLR.Diagram.braidL dL rL dL) (KLR.Diagram.braidR dL rL dL)
    (KLR.Diagram.E0 dL rL dL) (KLR.Diagram.E1 dL rL dL) (KLR.Diagram.E2 dL rL dL)
    rfl rfl rfl rfl rfl
  rw [qbar_affineCoverQ_black_red, KL3.Diagram.ncEval_sum_aux] at hb
  simp only [KL3.Diagram.ncEval_X0_pow_mul_X2_pow, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hb
  have hn := congrArg ((pointed) N) hb
  simp only [map_sub, map_sum] at hn
  rw [hn]
  have hδ' : exponents r i = degreeZeroBefore + degreeZeroAfter + 2 := by omega
  calc
    _ = ∑ a ∈ Finset.range (exponents r i),
        (leftReal) (N + a) * (rightReal) (exponents r i - 1 - a) := by
      apply Finset.sum_congr rfl
      intro a _
      change (close) ((ellDot ^ a * rDot ^ (exponents r i - 1 - a)) * ellDot ^ N) = _
      rw [mul_assoc, ((redBraidDots_commute i r Q exponents).pow_pow _ _).eq,
        ← mul_assoc, ← pow_add, add_comm a N, closedDotMonomial_eq_bubblesQ]
      rfl
    _ = _ := by
      rw [hδ', show degreeZeroBefore + degreeZeroAfter + 2 - 1 =
        degreeZeroBefore + degreeZeroAfter + 1 by omega]
      exact closedRedBraidCorrection_eq_sconv (leftReal) (rightReal) degreeZeroBefore degreeZeroAfter N hN
        (clockwiseReal_before_zeroQ RD Λ sc μ L i r R Q exponents P)
        (counterclockwiseReal_after_zeroQ RD Λ sc μ L i r R Q exponents P)


section MarkedMoves

variable (A : Presentation.{w, max u v} (signature RD Λ) k)

omit [DecidableEq I] in
private theorem markedPower_layers {s : List (DoubleStrand I ℓ)} {x : SignedLayer I ℓ}
    (hx : signedChain s [x] s) (N : ℕ) :
    (End.of (signedDg RD Λ A μ s s [x]) ^ N : End (A.obj (obj RD Λ μ s))) =
      signedDg RD Λ A μ s s (List.replicate N x) := by
  induction N with
  | zero => exact (signedDg_nil RD Λ A μ s).symm
  | succ N ih =>
    rw [pow_succ, End.mul_def]
    change signedDg RD Λ A μ s s [x] ≫
      (End.of (signedDg RD Λ A μ s s [x]) ^ N : End _) = _
    rw [ih, signedDg_comp RD Λ A μ hx (markedReplicate_chain hx N)]
    rfl

private theorem markedMove_power {D : Type*} [Category* D] {s t : D}
    (f : s ⟶ t) (x : End s) (y : End t) (h : f ≫ y = x ≫ f) (N : ℕ) :
    f ≫ (y ^ N : End t) = (x ^ N : End s) ≫ f := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, End.mul_def, ← Category.assoc, h, Category.assoc, ih]
    rw [← Category.assoc, ← End.mul_def, ← pow_succ]

omit [DecidableEq I] in
/-- Moving one mark past a layer moves any power of that mark past the layer. -/
theorem signedDg_markedMoveQ {s t : List (DoubleStrand I ℓ)} {x y f : SignedLayer I ℓ}
    (hx : signedChain s [x] s) (hy : signedChain t [y] t) (hf : signedChain s [f] t)
    (h : signedDg RD Λ A μ s t [f, y] = signedDg RD Λ A μ s t [x, f])
    (N : ℕ) :
    signedDg RD Λ A μ s t ([f] ++ List.replicate N y) =
      signedDg RD Λ A μ s t (List.replicate N x ++ [f]) := by
  change signedDg RD Λ A μ s t ([f] ++ [y]) = signedDg RD Λ A μ s t ([x] ++ [f]) at h
  rw [← signedDg_comp RD Λ A μ hf hy, ← signedDg_comp RD Λ A μ hx hf] at h
  have hp := markedMove_power (signedDg RD Λ A μ s t [f])
    (End.of (signedDg RD Λ A μ s s [x])) (End.of (signedDg RD Λ A μ t t [y])) h N
  rw [← signedDg_comp RD Λ A μ hf (markedReplicate_chain hy N),
    ← signedDg_comp RD Λ A μ (markedReplicate_chain hx N) hf,
    ← markedPower_layers RD Λ μ A hx, ← markedPower_layers RD Λ μ A hy]
  exact hp

end MarkedMoves

local notation "uS" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "dS" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "cupL" => (Move.black (ℓ := ℓ) (Shape.cup (true, i)))
local notation "cupR" => (Move.black (ℓ := ℓ) (Shape.cup (false, i)))
local notation "capL" => (Move.black (ℓ := ℓ) (Shape.cap (false, i)))
local notation "capR" => (Move.black (ℓ := ℓ) (Shape.cap (true, i)))
local notation "dotU" => (Move.black (ℓ := ℓ) (Shape.dot (true, i)))
local notation "dotD" => (Move.black (ℓ := ℓ) (Shape.dot (false, i)))
local notation "crossFF" => (Move.black (ℓ := ℓ) (Shape.cross false i i))

omit [DecidableEq I] in
private theorem signedPointedBlackClosure_chain (u v : List (DoubleStrand I ℓ)) (N : ℕ) :
    signedChain (u ++ v) (signedPointedBlackClosureLayers u v i N) (u ++ v) := by
  let middle := u ++ [uS, dS, dS, uS] ++ v
  have hpre : signedChain (u ++ v) [(u, cupL, v), (u ++ [uS, dS], cupR, v)] middle := by
    simp [middle, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  have hd : signedChain middle [(u, dotU, dS :: dS :: uS :: v)] middle := by
    simp [middle, signedChain, Move.bottom, Move.top]
  have hpost : signedChain middle
      [(u ++ [uS], crossFF, uS :: v), (u, capL, dS :: uS :: v), (u, capR, v)] (u ++ v) := by
    simp [middle, signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]
  simpa [signedPointedBlackClosureLayers, pointedBlackClosureLayers, blackWord, Sig.shape,
    List.map_replicate] using (hpre.append (markedReplicate_chain hd N)).append hpost

omit [DecidableEq I] in
/-- Vanishing in the black presentation remains true for the marked closed crossing
inside arbitrary signed words. -/
theorem signedPointedBlackClosure_eq_zeroQ (u v : List (DoubleStrand I ℓ)) (N : ℕ)
    (h : NF.dg (CLQ.pres RD k sc) (endWeight RD Λ μ u) [] [] (pointedBlackClosureLayers i N) = 0) :
    signedDg RD Λ (Pd) μ (u ++ v) (u ++ v) (signedPointedBlackClosureLayers u v i N) = 0 := by
  let η := endWeight RD Λ μ u
  have hs : SChain [] (pointedBlackClosureLayers i N) [] := by unfold pointedBlackClosureLayers; schain
  let d := mkD RD η (pointedBlackClosureLayers i N) hs
  have he : (CLQ.pres RD k sc).diag d = 0 := (NF.dg_of hs).symm.trans h
  let e : obj RD Λ μ (u ++ blackWord [] ++ v) = obj RD Λ μ (u ++ v) := by simp [blackWord]
  let f := Diagram.cast (blackDiagram RD Λ μ u v d) e e
  rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (signedPointedBlackClosure_chain i u v N) f (by
      unfold f d
      rw [Diagram.layers_cast, layers_blackDiagram_mkD]
      simp only [signedLayers, signedPointedBlackClosureLayers, List.map_map]
      rfl)]
  have hh : (CLQ.pres RD k sc).lin (LinDiagram.of d) = (CLQ.pres RD k sc).lin 0 := by
    rw [Presentation.lin_of, Presentation.lin_zero, he]
  have hq := blackContext_lin_eq_of_KL_eq_suffixQ RD Λ sc μ u v [] P (LinDiagram.of d) 0 hh
  have hfinal : (Pd).lin (blackLinear RD Λ k μ u v (LinDiagram.of d)) =
      (Pd).lin (blackLinear RD Λ k μ u v (0 : LEnd RD k (ob RD η []))) :=
    lin_eq_addRels (Pup) (lin_eq_addRels (Pcap)
      (lin_eq_addRels (Pcup) (lin_eq_addRels (Pb) hq)))
  unfold f
  rw [Presentation.diag, ← LinDiagram.cast_of, Presentation.lin_cast, ← blackLinear_of, hfinal,
    map_zero, Presentation.lin_zero]
  simp

end Categorification.Stendhal.DoubleDiagram
