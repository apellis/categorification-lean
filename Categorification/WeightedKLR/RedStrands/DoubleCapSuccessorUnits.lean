/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapRightCup
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorTransfer

/-!
# Cap successors up to a unit

Webster, arXiv:1309.3796v3, §4.5, proof of Lemma 4.29. For black strands with the
relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1), the cup
pitchfork holds only up to a unit of `k` (the scalars `t_{ij}`). The cap successor
statements are memberships in spans, so a unit factor on the forward diagram is harmless.
This file gives the unit forms of the replacement, right-cup and successor lemmas used
in the signed cap induction.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

section Replace

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

/-- Insert a filtration-bounded difference, up to a scalar, at a level of a signed diagram. -/
theorem signedDg_replace_span_smul (P : Presentation.{w,max u v} (signature RD Λ) k) (μ : X)
    {s a b t : List (DoubleStrand I ℓ)} {pre F G post : List (SignedLayer I ℓ)}
    (hp : signedChain s pre a) (hf : signedChain a F b) (hg : signedChain a G b)
    (ht : signedChain b post t) {n : ℕ} (c : k)
    (he : signedDg RD Λ P μ a b F - c • signedDg RD Λ P μ a b G ∈
      signedCrossingSpan RD Λ P μ a b n) :
    signedDg RD Λ P μ s t (pre ++ F ++ post) - c • signedDg RD Λ P μ s t (pre ++ G ++ post) ∈
      signedCrossingSpan RD Λ P μ s t (signedCrossings pre + n + signedCrossings post) := by
  let d := Diagram.mk _ (chain_signedLayers RD Λ μ hp)
  let e := Diagram.mk _ (chain_signedLayers RD Λ μ ht)
  have h := signedCrossingSpan_comp RD Λ P μ d e he
  rw [crossingNumber_of_signedLayers RD Λ μ d pre rfl,
    crossingNumber_of_signedLayers RD Λ μ e post rfl] at h
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
    ← Category.assoc, ← Category.assoc,
    ← signedDg_of RD Λ P μ hp, ← signedDg_of RD Λ P μ ht,
    signedDg_comp RD Λ P μ hp hf, signedDg_comp RD Λ P μ hp hg,
    signedDg_comp RD Λ P μ (hp.append hf) ht, signedDg_comp RD Λ P μ (hp.append hg) ht] at h
  exact h

end Replace

section RightCup

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L U : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))
local notation "bl(" b ")" => (Sum.inl b : DoubleStrand I ℓ)
local notation "Str" => DoubleStrand I ℓ

variable (x : DoubleStrand I ℓ)
include x
local notation "pre" => L ++ [bl(l.dual)] ++ U
local notation "src" => pre ++ [x] ++ R
local notation "dst" => (L ++ U) ++ [x,bl(l.dual)] ++ R
local notation "between" => pre ++ [bl(l),x,bl(l.dual)] ++ R
local notation "ev" => signedDg RD Λ P μ
local notation "cross" => signedCrossLayers (L ++ U) (bl(l.dual)) x R

private theorem rightCup_cross_chain_smul :
    signedChain ((L ++ U) ++ [bl(l.dual),x] ++ R) cross dst :=
  signedCrossLayers_chain (L ++ U) (by cases x <;> trivial) R

private theorem rightCup_pull_cross_smul (d : ℕ) :
    ev src dst (signedCupFromLeft pre x l R ++ signedCapBlock L U l (x :: bl(l.dual) :: R) d) =
      ev src dst (cupRightCapBlock L U l (x :: R) d ++ cross) := by
  let a := pre ++ [bl(l),bl(l.dual),x] ++ R
  let c : SignedLayer I ℓ := (pre,.black (.cup l),x :: R)
  have hx : CanCross (bl(l.dual)) x := by cases x <;> trivial
  have h₀ := signedCrossLayers_chain ([] : List Str) hx []
  have h := signedCapBlock_disjointRight RD Λ P μ L U l R h₀ d
  have e₁ : _ = a := show L ++ ([bl(l.dual)] ++ U ++ [bl(l)]) ++
      ([] ++ [bl(l.dual),x] ++ []) ++ R = a by simp [a,List.append_assoc]
  have e₂ : _ = dst := show L ++ U ++ ([] ++ [x,bl(l.dual)] ++ []) ++ R = dst by
    simp [List.append_assoc]
  rw [e₁,e₂] at h
  let B := signedCrossLayers (pre ++ [bl(l)]) (bl(l.dual)) x R ++
    signedCapBlock L U l (x :: bl(l.dual) :: R) d
  let G := signedCapBlock L U l (bl(l.dual) :: x :: R) d ++ cross
  have eqv : ev a dst B = ev a dst G := by
    simpa only [B,G,signedCrossLayers_whisk,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using h
  have hc : signedChain src [c] a := by
    simp [c,a,signedChain,Move.bottom,Move.top,Shape.cod,List.append_assoc]
  have hb : signedChain a B dst := by
    have u := signedCrossLayers_chain (pre ++ [bl(l)]) hx R
    have v := signedCapBlock_chain L U l (x :: bl(l.dual) :: R) d
    simp only [List.append_assoc,List.cons_append,List.nil_append] at u v
    simpa only [a,B,List.append_assoc,List.cons_append,List.nil_append] using u.append v
  have hg : signedChain a G dst := by
    have u := signedCapBlock_chain L U l (bl(l.dual) :: x :: R) d
    have v := rightCup_cross_chain_smul L U l R x
    simp only [List.append_assoc,List.cons_append,List.nil_append] at u v
    simpa only [a,G,List.append_assoc,List.cons_append,List.nil_append] using u.append v
  have e := congrArg (fun f => ev src a [c] ≫ f) eqv
  rw [signedDg_comp RD Λ P μ hc hb,signedDg_comp RD Λ P μ hc hg] at e
  simpa only [signedCupFromLeft,cupRightCapBlock,c,B,G,List.append_assoc,List.cons_append,
    List.nil_append] using e

/-- Removing the last letter from the right-hand cup zigzag, when the pitchfork at that
letter holds up to a scalar `c`: the scalar passes to the remaining cup zigzag. -/
theorem signedCapBlock_cupRight_last_smul (d : ℕ) (c : k)
    (hp : ev src between (signedCupFromRight pre x l R) -
        c • ev src between (signedCupFromLeft pre x l R) ∈
      signedCrossingSpan RD Λ P μ src between 0) :
    ev src dst (cupRightCapBlock L (U ++ [x]) l R d) -
        c • ev src dst (cupRightCapBlock L U l (x :: R) d ++ cross) ∈
      signedCrossingSpan RD Λ P μ src dst U.length := by
  have hb : signedChain between (signedCapBlock L U l (x :: bl(l.dual) :: R) d) dst := by
    simpa only [List.append_assoc,List.nil_append,List.cons_append] using
      signedCapBlock_chain L U l (x :: bl(l.dual) :: R) d
  have h := signedDg_replace_span_smul RD Λ P μ (show signedChain src [] src from rfl)
    (signedCupFromRight_chain pre x l R) (signedCupFromLeft_chain pre x l R) hb c hp
  change _ ∈ signedCrossingSpan RD Λ P μ src dst (0 + 0 + signedCrossings _) at h
  rw [signedCapBlock_crossings, Nat.zero_add] at h
  have cut : cupRightCapBlock L (U ++ [x]) l R d =
      signedCupFromRight pre x l R ++ signedCapBlock L U l (x :: bl(l.dual) :: R) d := by
    simp only [cupRightCapBlock,signedCapBlock_append,sweepBlackLeft,signedCupFromRight,
      List.append_assoc,List.nil_append,List.cons_append]
  rw [cut,← rightCup_pull_cross_smul RD Λ P μ L U l R x d]
  simpa only [List.nil_append] using h

end RightCup

section Successor

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
local notation "B" => DoubleStrand I ℓ

variable {a t : Obj (signature RD Λ)} {M : Type*} [AddCommGroup M] [Module k M]
  (π : (P.obj a ⟶ P.obj t) →ₗ[k] M)

/-- A cup-cap zigzag resolving to a forward sweep up to a unit, modulo the strictly
smaller crossing filtration. -/
theorem capSuccessorAt_of_forward_smul (m : CapPredecessor I ℓ) (u v L U : List B)
    (l : Letter I) (R : List B)
    (align : u ++ m.top ++ v = L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R)
    (out : ℕ → List (SignedLayer I ℓ))
    (chain : ∀ d, signedChain (u ++ m.bottom ++ v) (out d) (L ++ U ++ R))
    (forward : ∀ d, AppendsForward (RD := RD) (Λ := Λ) (out d))
    (budget : ∀ d, signedCrossings (out d) ≤ m.cost + U.length)
    (rewriteBlock : ∀ (μ : X) (d : ℕ), ∃ c : k,
      let diff := signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R)
          (m.rows u v ++ signedCapBlock L U l R d) -
        c • signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (out d)
      diff = 0 ∨
        ∃ n < m.cost + U.length, diff ∈ signedCrossingSpan RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) n) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u v L U l R := by
  apply capSuccessorAt_of_projected P π m u v L U l R align
  intro μ p hp _ d tail
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ (chain d))
  have hf := forward d p hp f rfl
  have hc := crossingNumber_of_signedLayers RD Λ μ f (out d) rfl
  have hi := budget d
  obtain ⟨c, hrw⟩ := rewriteBlock μ d
  have hmain : π (P.diag p ≫ (c • P.diag f) ≫ P.diag tail) ∈
      forwardSpan k (fun g => π (P.diag g)) tail (crossingNumber p + m.cost + U.length) := by
    rw [Linear.smul_comp, Linear.comp_smul, map_smul]
    exact Submodule.smul_mem _ c
      (Submodule.subset_span ⟨p ≫ f, hf, by rw [crossingNumber_comp,hc]; omega, by simp [P.diag_comp]⟩)
  have eqv : signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (out d) = P.diag f :=
    signedDg_of RD Λ P μ (chain d)
  rcases hrw with he | ⟨n,hn,hs⟩
  · rw [sub_eq_zero] at he
    rw [he,eqv]
    exact Submodule.mem_sup_left hmain
  · rw [eqv] at hs
    have h0 : crossingNumber (𝟙 (obj RD Λ μ (L ++ U ++ R))) = 0 := rfl
    have H := signedCrossingSpan_in_fewerCrossings RD Λ P μ p (𝟙 _) tail π hs
      (m := crossingNumber p + m.cost + U.length) (by omega)
    simp only [Category.id_comp,Preadditive.sub_comp,Preadditive.comp_sub,map_sub] at H
    apply (Submodule.sub_mem_iff_left _ (Submodule.mem_sup_left hmain)).mp
    exact Submodule.mem_sup_right H

end Successor

end Categorification.Stendhal.DoubleDiagram
