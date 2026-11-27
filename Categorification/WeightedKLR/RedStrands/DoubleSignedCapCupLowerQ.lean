/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCupCurlQ

/-!
# The crossing-lowering cup placements of a signed sweep

Webster v2, §4.5, proof of Lemma 4.28. A cup at the first or last
interior strand forms a curl. A cup whose two legs lie inside the interval
meets the moving cap leg twice. Interchange puts these local reductions
between the two remaining signed sweeps, preserving the strict decrease
in the total crossing number.

This is the version of `DoubleSignedCapCupLower` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)
  (P : Presentation.{w,max u v} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X)
local notation "B" => DoubleStrand I ℓ
local notation "bl(" l ")" => (Sum.inl l : B)
local notation "D" => signedDg RD Λ P μ
local notation "F" => signedCrossingSpan RD Λ P μ

private theorem signedDg_mem_reindex {a b a' b' : List B} (ha : a=a') (hb : b=b')
    {ls : List (SignedLayer I ℓ)} {n : ℕ} (h : D a b ls ∈ F a b n) : D a' b' ls ∈ F a' b' n := by
  cases ha; cases hb; exact h

private theorem signedDg_mem_in_context {s a b t : List B} {pre A post : List (SignedLayer I ℓ)}
    (hp : signedChain s pre a) (ha : signedChain a A b) (ht : signedChain b post t) {n : ℕ}
    (h : D a b A ∈ F a b n) : D s t (pre ++ A ++ post) ∈ F s t (signedCrossings pre + n + signedCrossings post) := by
  let p := Diagram.mk _ (chain_signedLayers RD Λ μ hp)
  let q := Diagram.mk _ (chain_signedLayers RD Λ μ ht)
  have H := signedCrossingSpan_comp RD Λ P μ p q h
  rw [crossingNumber_of_signedLayers RD Λ μ p pre rfl, crossingNumber_of_signedLayers RD Λ μ q post rfl,
    ← signedDg_of RD Λ P μ hp,← signedDg_of RD Λ P μ ht,← Category.assoc,
    signedDg_comp RD Λ P μ hp ha,signedDg_comp RD Λ P μ (hp.append ha) ht] at H
  exact H

private theorem cup_past_sweep (L V : List B) (x l : Letter I) (R : List B) :
    let s := L ++ V ++ [bl(l)] ++ R
    let t := (L ++ [bl(x),bl(x.dual)]) ++ [bl(l)] ++ V ++ R
    D s t ([(L,.black (.cup x),V ++ [bl(l)] ++ R)] ++ sweepBlackLeft (L ++ [bl(x),bl(x.dual)]) V l R) =
      D s t (sweepBlackLeft L V l R ++ [(L,.black (.cup x),bl(l) :: (V ++ R))]) := by
  dsimp only
  have hc : signedChain (ℓ := ℓ) [] [([], .black (.cup x), [])] [bl(x),bl(x.dual)] := by
    simp [signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod]
  have h := signedDg_interchange RD Λ P μ L R hc (sweepBlackLeft_chain [] V l [])
  have e₁ : L ++ [] ++ ([] ++ V ++ [bl(l)] ++ []) ++ R = L ++ V ++ [bl(l)] ++ R :=
    by simp [List.append_assoc]
  have e₂ : L ++ [bl(x),bl(x.dual)] ++ ([] ++ [bl(l)] ++ V ++ []) ++ R =
      (L ++ [bl(x),bl(x.dual)]) ++ [bl(l)] ++ V ++ R := by simp [List.append_assoc]
  rw [e₁,e₂] at h
  simp only [sweepBlackLeft_whisk] at h
  simpa only [signedWhisk,List.map_cons,List.map_nil,List.nil_append,List.append_nil,List.append_assoc,
    List.cons_append] using h

private theorem cup_sweep_lower (L V : List B) (x l : Letter I) (R z : List B) (tail : List (SignedLayer I ℓ))
    (ht : signedChain ((L ++ [bl(x),bl(x.dual)]) ++ [bl(l)] ++ V ++ R) tail z) {n : ℕ}
    (hm : D (L ++ [bl(l)] ++ V ++ R) z ([(L,.black (.cup x),bl(l) :: (V ++ R))] ++ tail) ∈
      F (L ++ [bl(l)] ++ V ++ R) z n) :
    D (L ++ V ++ [bl(l)] ++ R) z
      (([(L,.black (.cup x),V ++ [bl(l)] ++ R)] ++ sweepBlackLeft (L ++ [bl(x),bl(x.dual)]) V l R) ++ tail) ∈
      F (L ++ V ++ [bl(l)] ++ R) z (V.length + n) := by
  let a := L ++ V ++ [bl(l)] ++ R
  let b := L ++ [bl(l)] ++ V ++ R
  let t := (L ++ [bl(x),bl(x.dual)]) ++ [bl(l)] ++ V ++ R
  let g : SignedLayer I ℓ := (L,.black (.cup x),V ++ [bl(l)] ++ R)
  let f : SignedLayer I ℓ := (L,.black (.cup x),bl(l) :: (V ++ R))
  have hswap := cup_past_sweep RD Λ P μ L V x l R
  have hcu : signedChain b [f] t := by simp [b,t,f,signedChain,Move.bottom,Move.top,List.append_assoc]
  have hs := sweepBlackLeft_chain L V l R
  have hs' := sweepBlackLeft_chain (L ++ [bl(x),bl(x.dual)]) V l R
  have hcu' : signedChain a [g] ((L ++ [bl(x),bl(x.dual)]) ++ V ++ [bl(l)] ++ R) := by
    simp [a,g,signedChain,Move.bottom,Move.top,List.append_assoc]
  have eqv := congrArg (fun h => h ≫ D t z tail) hswap
  rw [signedDg_comp RD Λ P μ (hcu'.append hs') ht, signedDg_comp RD Λ P μ (hs.append hcu) ht] at eqv
  rw [eqv,List.append_assoc (sweepBlackLeft L V l R) [f] tail]
  have m := signedDg_mem_in_context RD Λ P μ hs (hcu.append ht) (show signedChain z [] z from rfl) hm
  simpa only [List.append_nil,sweepBlackLeft_crossings,
    show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl,Nat.add_zero] using m

include hP

/-- The cup creating the last interior strand and moving cap endpoint can be
replaced by terms with at most the number of other interior strands in crossings. -/
theorem signedCapBlock_cupLastQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    let p := L ++ [bl(l.dual)] ++ U
    let s := p ++ R
    let t := L ++ (U ++ [bl(l.dual)]) ++ R
    D s t ((p,.black (.cup l.dual),R) :: signedCapBlock L (U ++ [bl(l.dual)]) l R d) ∈
      F s t U.length := by
  let p := L ++ [bl(l.dual)] ++ U
  let mid := p ++ [bl(l),bl(l.dual)] ++ R
  let t := L ++ (U ++ [bl(l.dual)]) ++ R
  let sub := [(p,Move.black (ℓ := ℓ) (.cup l.dual),R)] ++ crossBlackLeft p (bl(l.dual)) l R
  let tail := signedCapBlock L U l (bl(l.dual) :: R) d
  have ht : signedChain mid tail t := by simpa only [tail,mid,t,p,List.append_assoc,List.cons_append,
    List.nil_append] using signedCapBlock_chain L U l (bl(l.dual) :: R) d
  have hs : signedChain (p ++ R) sub mid := by
    simpa only [sub,mid,List.singleton_append,signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,
      Letter.dual_dual,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append,true_and] using
      crossBlackLeft_chain p (bl(l.dual)) l R
  have lower := signedCupCurl_blackQ p R RD Λ sc P hP μ l.dual
  have m : D (p ++ R) mid sub ∈ F (p ++ R) mid 0 := by
    obtain ⟨_ | _,i⟩ := l <;> exact lower
  have h := signedDg_mem_in_context RD Λ P μ (show signedChain (p ++ R) [] (p ++ R) from rfl) hs ht m
  rw [signedCapBlock_crossings] at h
  simpa only [signedCapBlock_append,sweepBlackLeft,sub,tail,mid,t,p,List.append_assoc,List.nil_append,
    List.cons_append,show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl,Nat.zero_add] using h


/-- Creating the stationary cap leg and the adjacent interior black leg gives
strictly fewer crossings, for any remaining signed interval and any dot count. -/
theorem signedCapBlock_cupFirstQ (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    D (L ++ U ++ [bl(l)] ++ R) (L ++ (bl(l) :: U) ++ R)
      ((L,.black (.cup l.dual),U ++ [bl(l)] ++ R) :: signedCapBlock L (bl(l) :: U) l R d) ∈
      F (L ++ U ++ [bl(l)] ++ R) (L ++ (bl(l) :: U) ++ R) U.length := by
  let z := L ++ (bl(l) :: U) ++ R
  let tail := signedCapBlock L [bl(l)] l (U ++ R) d
  have ht : signedChain ((L ++ [bl(l.dual),bl(l.dual.dual)]) ++ [bl(l)] ++ U ++ R) tail z := by
    simpa only [tail,z,Letter.dual_dual,List.append_assoc,List.cons_append,List.nil_append] using
      signedCapBlock_chain L [bl(l)] l (U ++ R) d
  have h := signedCapBlock_firstCup_singleQ L (U ++ R) RD Λ sc P hP μ l d
  have small : D (L ++ [bl(l)] ++ U ++ R) z ([(L,.black (.cup l.dual),bl(l) :: (U ++ R))] ++ tail) ∈
      F (L ++ [bl(l)] ++ U ++ R) z 0 := by
    have a : L ++ [bl(l)] ++ (U ++ R) = L ++ [bl(l)] ++ U ++ R := by simp [List.append_assoc]
    have b : L ++ [bl(l)] ++ (U ++ R) = z := by simp [z,List.append_assoc]
    exact signedDg_mem_reindex RD Λ P μ a b h
  have m := cup_sweep_lower RD Λ P μ L U l.dual l R z tail ht small
  have split : signedCapBlock L (bl(l) :: U) l R d =
      sweepBlackLeft (L ++ [bl(l.dual),bl(l.dual.dual)]) U l R ++ tail := by
    rw [show bl(l) :: U = [bl(l)] ++ U from rfl,signedCapBlock_append]
    simp [tail,List.append_assoc]
  rw [split]
  simpa only [z,List.cons_append,List.nil_append,Nat.add_zero] using m


/-- A cup creating two interior strands costs at most one crossing with
the moving cap leg, instead of the two crossings in the original sweep.
The signed words between the cup and the cap legs are arbitrary. -/
theorem signedCapBlock_cupInsideQ (L U V : List B) (x l : Letter I) (R : List B) (d : ℕ) :
    let p := L ++ [bl(l.dual)] ++ U
    let s := p ++ V ++ [bl(l)] ++ R
    let t := L ++ (U ++ [bl(x),bl(x.dual)] ++ V) ++ R
    D s t ((p,.black (.cup x),V ++ [bl(l)] ++ R) ::
      signedCapBlock L (U ++ [bl(x),bl(x.dual)] ++ V) l R d) ∈ F s t (U.length+V.length+1) := by
  let p := L ++ [bl(l.dual)] ++ U
  let z := L ++ (U ++ [bl(x),bl(x.dual)] ++ V) ++ R
  let a := p ++ [bl(l)] ++ V ++ R
  let b := p ++ [bl(l),bl(x),bl(x.dual)] ++ (V ++ R)
  let c := (p ++ [bl(x),bl(x.dual)]) ++ [bl(l)] ++ V ++ R
  let f := crossBlackLeft (p ++ [bl(x)]) (bl(x.dual)) l (V ++ R)
  let g := crossBlackLeft p (bl(x)) l (bl(x.dual) :: (V ++ R))
  let above := signedCapBlock L U l (bl(x) :: bl(x.dual) :: (V ++ R)) d
  let tail := (f ++ g) ++ above
  have h₁ := crossBlackLeft_chain (p ++ [bl(x)]) (bl(x.dual)) l (V ++ R)
  have h₂ := crossBlackLeft_chain p (bl(x)) l (bl(x.dual) :: (V ++ R))
  have ht : signedChain b above z := by
    simpa only [above,b,z,p,List.append_assoc,List.nil_append,List.cons_append] using
      signedCapBlock_chain L U l (bl(x) :: bl(x.dual) :: (V ++ R)) d
  have hf : signedChain c (f ++ g) b := by
    simp only [List.append_assoc,List.nil_append,List.cons_append] at h₁ h₂
    simpa only [c,f,g,b,List.append_assoc,List.nil_append,List.cons_append] using h₁.append h₂
  have hcup : signedChain a [(p,.black (.cup x),bl(l) :: (V ++ R))] c := by
    simp [a,c,signedChain,Move.bottom,Move.top,List.append_assoc]
  have small₀ := signedCupTwoLegs_blackQ p (V ++ R) RD Λ sc P hP μ x l
  have small₁ : D a b ([(p,.black (.cup x),bl(l) :: (V ++ R))] ++ (f ++ g)) ∈ F a b 1 := by
    have eqv := signedDg_mem_reindex RD Λ P μ
      (show p ++ [bl(l)] ++ (V ++ R) = a by simp [a,List.append_assoc]) (show _ = b from rfl) small₀
    simpa only [f,g,List.append_assoc] using eqv
  have small₂ := signedDg_mem_in_context RD Λ P μ (show signedChain a [] a from rfl) (hcup.append hf) ht small₁
  have small : D a z ([(p,.black (.cup x),bl(l) :: (V ++ R))] ++ tail) ∈ F a z (1+U.length) := by
    simpa only [tail,above,List.append_assoc,List.nil_append,signedCapBlock_crossings,
      show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl,Nat.zero_add] using small₂
  have m := cup_sweep_lower RD Λ P μ p V x l R z tail (hf.append ht) small
  have split : signedCapBlock L (U ++ [bl(x),bl(x.dual)] ++ V) l R d =
      sweepBlackLeft (p ++ [bl(x),bl(x.dual)]) V l R ++ tail := by
    rw [List.append_assoc U [bl(x),bl(x.dual)] V,signedCapBlock_append,sweepBlackLeft_append]
    simp only [sweepBlackLeft,tail,f,g,above,p,List.append_assoc,List.nil_append,List.cons_append]
  dsimp only
  rw [split,show U.length+V.length+1 = V.length+(1+U.length) by omega]
  simpa only [p,z,List.cons_append,List.nil_append] using m

end Categorification.Stendhal.DoubleDiagram
