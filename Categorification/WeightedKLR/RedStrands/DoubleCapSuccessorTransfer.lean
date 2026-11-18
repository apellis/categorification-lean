/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPositions

/-!
# Applying signed word reductions to the physical cap induction

For Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, a local diagram calculation
on unlabelled signed words gives the matching physical successor case after
any linear projection. Corrections strictly below the original crossing count
enter the smaller-degree induction directly.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
local notation "S" => signature RD Λ
local notation "B" => DoubleStrand I ℓ

/-- The single crossing of either an actual crossing or a three-layer mate;
a cup or dot contributes zero. -/
def CapPredecessor.cost : CapPredecessor I ℓ → ℕ
  | .cross .. => 1
  | _ => 0

theorem CapPredecessor.signedCrossings_rows (m : CapPredecessor I ℓ) (u v : List B) :
    signedCrossings (m.rows u v) = m.cost := by
  cases m with
  | dot | cup => rfl
  | cross x y h => exact signedCrossLayers_crossings u h v

private theorem capBlock_nonempty (L U : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedCapBlock L U l R d ≠ [] := by simp [signedCapBlock]

variable {a t : Obj (signature RD Λ)} {M : Type*} [AddCommGroup M] [Module k M]
  (π : (P.obj a ⟶ P.obj t) →ₗ[k] M)

/-- Use word-labelled projected calculations in the raw successor statement.
Both projected exterior contexts remain arbitrary. -/
theorem capSuccessorAt_of_projected (m : CapPredecessor I ℓ) (u v L U : List B) (l : Letter I) (R : List B)
    (align : u ++ m.top ++ v = L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R)
    (h : ∀ (μ : X) (p : a ⟶ obj RD Λ μ (u ++ m.bottom ++ v)), ForwardPath a p →
      ResolvesSignedCapBlocks k (fun f => π (P.diag f)) p → ∀ (d : ℕ) (tail : obj RD Λ μ (L ++ U ++ R) ⟶ t),
      π (P.diag p ≫ signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R)
        (m.rows u v ++ signedCapBlock L U l R d) ≫ P.diag tail) ∈
        forwardSpan k (fun f => π (P.diag f)) tail (crossingNumber p + m.cost + U.length) ⊔
          fewerCrossings k (fun f => π (P.diag f)) tail (crossingNumber p + m.cost + U.length)) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u v L U l R := by
  intro μ p hp ih g hg e block d tail hb
  have chainB : signedChain (u ++ m.top ++ v) (signedCapBlock L U l R d) (L ++ U ++ R) := by
    rw [align]
    exact signedCapBlock_chain ..
  have ⟨_,he⟩ := boundaries_of_signedLayers block μ chainB (capBlock_nonempty L U l R d) hb
  subst e
  have eqv : signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (m.rows u v ++ signedCapBlock L U l R d) =
      P.diag (g ≫ block) := by
    apply signedDg_eq_diag_of_layers RD Λ P μ ((m.chain u v).append chainB)
    rw [Diagram.layers_comp, hg, hb]
    simp [signedLayers]
  have hc := (crossingNumber_of_signedLayers RD Λ μ g _ hg).trans (m.signedCrossings_rows u v)
  have H := h μ p hp ih d tail
  rw [eqv, P.diag_comp, Category.assoc] at H
  simpa only [P.diag_comp, Category.assoc, crossingNumber_comp, hc] using H

/-- A strictly smaller local span resolves the whole position, for example
in the curl, bigon and cup-inside cases. -/
theorem capSuccessorAt_of_lower (m : CapPredecessor I ℓ) (u v L U : List B) (l : Letter I) (R : List B)
    (align : u ++ m.top ++ v = L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R) (n : ℕ)
    (hn : n < m.cost + U.length)
    (lower : ∀ (μ : X) (d : ℕ), signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R)
      (m.rows u v ++ signedCapBlock L U l R d) ∈ signedCrossingSpan RD Λ P μ
        (u ++ m.bottom ++ v) (L ++ U ++ R) n) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u v L U l R := by
  apply capSuccessorAt_of_projected P π m u v L U l R align
  intro μ p hp ih d tail
  apply Submodule.mem_sup_right
  have h0 : crossingNumber (𝟙 (obj RD Λ μ (L ++ U ++ R))) = 0 := rfl
  have H := signedCrossingSpan_in_fewerCrossings RD Λ P μ p (𝟙 _) tail π (lower μ d)
    (m := crossingNumber p + m.cost + U.length) (by omega)
  simpa using H

/-- A signed sequence of layers that can be appended to any forward prefix. -/
def AppendsForward (ls : List (SignedLayer I ℓ)) : Prop :=
  ∀ {a b c : Obj (signature RD Λ)} (f : a ⟶ b), ForwardPath a f → ∀ g : b ⟶ c,
    Diagram.layers g = signedLayers RD Λ b.start ls → ForwardPath a (f ≫ g)

theorem appendsForward_nil : AppendsForward (RD := RD) (Λ := Λ) ([] : List (SignedLayer I ℓ)) := by
  intro a b c f hf g hg
  have h := Diagram.chain g
  rw [hg] at h
  subst c
  have e : g = 𝟙 b := Diagram.ext hg
  simpa [e] using hf

theorem CapPredecessor.appendsForward (m : CapPredecessor I ℓ) (u v : List B) :
    AppendsForward (RD := RD) (Λ := Λ) (m.rows u v) := by
  intro a b c f hf g hg
  cases m with
  | dot s | cup s => exact .single hf g _ hg (fun h => h)
  | cross x y h =>
    cases y with
    | inl l => exact hf.crossBlackLeft g u x l v hg
    | inr r =>
      cases x with
      | inl l => exact .single hf g _ hg (fun h => h)
      | inr => exact False.elim h

/-- Transport a projected local rewrite in which a modified cap is followed
by forward moves. An exact equation is allowed even at crossing degree zero.
This handles disjoint moves, dots carried onto the cap, and cap-leg entries. -/
theorem capSuccessorAt_of_slide (m : CapPredecessor I ℓ) (u v L U : List B) (l : Letter I) (R : List B)
    (align : u ++ m.top ++ v = L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R)
    (L' U' : List B) (l' : Letter I) (R' : List B)
    (src : u ++ m.bottom ++ v = L' ++ [.inl l'.dual] ++ U' ++ [.inl l'] ++ R')
    (marks : ℕ → ℕ) (above : List (SignedLayer I ℓ))
    (ha : signedChain (L' ++ U' ++ R') above (L ++ U ++ R)) (hf : AppendsForward (RD := RD) (Λ := Λ) above)
    (hbudget : U'.length + signedCrossings above ≤ m.cost + U.length)
    (rewriteBlock : ∀ (μ : X) (d : ℕ),
      let diff := signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (m.rows u v ++ signedCapBlock L U l R d) -
        signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (signedCapBlock L' U' l' R' (marks d) ++ above)
      diff = 0 ∨ ∃ n < m.cost + U.length, diff ∈ signedCrossingSpan RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) n) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u v L U l R := by
  apply capSuccessorAt_of_projected P π m u v L U l R align
  intro μ p hp ih d tail
  let blk := signedCapBlock L' U' l' R' (marks d)
  have hb : signedChain (u ++ m.bottom ++ v) blk (L' ++ U' ++ R') := by rw [src]; exact signedCapBlock_chain ..
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ hb)
  let g := Diagram.mk _ (chain_signedLayers RD Λ μ ha)
  have eqv : signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (blk ++ above) = P.diag (f ≫ g) := by
    rw [← signedDg_comp RD Λ P μ hb ha, signedDg_of RD Λ P μ hb, signedDg_of RD Λ P μ ha, P.diag_comp]
  have hn : crossingNumber g = signedCrossings above := crossingNumber_of_signedLayers RD Λ μ g above rfl
  apply capBlock_push_of_exchange k (fun z => π (P.diag z)) p ih f L' U' l' R' (marks d)
    (congrArg (obj RD Λ μ) src) rfl g (fun q hq => hf q hq g rfl) tail _ (by omega)
  rcases rewriteBlock μ d with he | ⟨n,hn',hs⟩
  · rw [sub_eq_zero] at he
    rw [he, eqv]
    simp [P.diag_comp, Category.assoc]
  · rw [eqv] at hs
    have h0 : crossingNumber (𝟙 (obj RD Λ μ (L ++ U ++ R))) = 0 := rfl
    have H := signedCrossingSpan_in_fewerCrossings RD Λ P μ p (𝟙 _) tail π hs
      (m := crossingNumber p + m.cost + U.length) (by omega)
    simpa only [Category.id_comp, Preadditive.sub_comp, Preadditive.comp_sub, map_sub, P.diag_comp,
      Category.assoc] using H

/-- A cup-cap zigzag can resolve directly to a forward sweep, modulo the
strictly smaller crossing filtration. At zero crossings the equation is exact. -/
theorem capSuccessorAt_of_forward (m : CapPredecessor I ℓ) (u v L U : List B) (l : Letter I) (R : List B)
    (align : u ++ m.top ++ v = L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R)
    (out : ℕ → List (SignedLayer I ℓ))
    (chain : ∀ d, signedChain (u ++ m.bottom ++ v) (out d) (L ++ U ++ R))
    (forward : ∀ d, AppendsForward (RD := RD) (Λ := Λ) (out d))
    (budget : ∀ d, signedCrossings (out d) ≤ m.cost + U.length)
    (rewriteBlock : ∀ (μ : X) (d : ℕ),
      let diff := signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (m.rows u v ++ signedCapBlock L U l R d) -
        signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (out d)
      diff = 0 ∨ ∃ n < m.cost + U.length, diff ∈ signedCrossingSpan RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) n) :
    CapSuccessorAt k (fun f => π (P.diag f)) m u v L U l R := by
  apply capSuccessorAt_of_projected P π m u v L U l R align
  intro μ p hp _ d tail
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ (chain d))
  have hf := forward d p hp f rfl
  have hc := crossingNumber_of_signedLayers RD Λ μ f (out d) rfl
  have hi := budget d
  have hmain : π (P.diag p ≫ P.diag f ≫ P.diag tail) ∈
      forwardSpan k (fun g => π (P.diag g)) tail (crossingNumber p + m.cost + U.length) :=
    Submodule.subset_span ⟨p ≫ f, hf, by rw [crossingNumber_comp,hc]; omega, by simp [P.diag_comp]⟩
  have eqv : signedDg RD Λ P μ (u ++ m.bottom ++ v) (L ++ U ++ R) (out d) = P.diag f :=
    signedDg_of RD Λ P μ (chain d)
  rcases rewriteBlock μ d with he | ⟨n,hn,hs⟩
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

end Categorification.Stendhal.DoubleDiagram
