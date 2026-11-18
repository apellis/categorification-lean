/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.WeightedKLR.RedStrands.DoubleRedBubbleCoefficients
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations

/-!
# Downward red triple points in a signed cap sweep

Webster, arXiv:1309.3796v2, Definition 4.5, (4.1a), and §4.5, Lemma 4.28.
The affine cover supplies the downward braid relations in any signed
context. In the middle-red repeated-black case the correction is a sum of
dot monomials, each of crossing number zero.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (μ : X) (L R : List (DoubleStrand I ℓ))

local notation "J" => I ⊕ Fin ℓ
local notation "δ" => (DoubleStrand.down : J → DoubleStrand I ℓ)
local notation "Qₐ" => affineCoverQ Q exponents
local notation "P₀" => KLR.Diagram.pres k Qₐ
local notation "P₁" => addDownRelations RD Λ Qₐ P
local notation "F" => downPresentedFunctor RD Λ Qₐ P μ L R
local notation "wrd" => fun s : List J => (L ++ List.map δ s ++ R)
local notation "D" => fun s t : List J => signedDg RD Λ (P₁) μ ((wrd) s) ((wrd) t)

private theorem down_inl (j : I) : δ (Sum.inl j) = Sum.inl (false,j) := rfl

private theorem map_cross (a b : List J) (c d : J) (h : CanCross (δ c) (δ d)) :
    (F).map ((P₀).diag (dl a (.cross c d) b (a := ob (a ++ [c,d] ++ b))
        (b := ob (a ++ [d,c] ++ b)) rfl rfl)) =
      (D) (a ++ [c,d] ++ b) (a ++ [d,c] ++ b)
        (signedCrossLayers (L ++ a.map δ) (δ c) (δ d) (b.map δ ++ R)) := by
  have hc : signedChain ((wrd) (a ++ [c,d] ++ b))
      (signedCrossLayers (L ++ a.map δ) (δ c) (δ d) (b.map δ ++ R))
      ((wrd) (a ++ [d,c] ++ b)) := by
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using
      signedCrossLayers_chain (L ++ a.map δ) h (b.map δ ++ R)
  cases c <;> cases d
  all_goals first | exact h.elim | skip
  all_goals
    refine (downPresentedFunctor_layer RD Λ Qₐ P μ L R (lay a (.cross _ _) b)
      (lay_valid ..) rfl rfl rfl).trans ?_
    symm
    exact signedDg_eq_diag_of_layers RD Λ (P₁) μ hc _ (by
      simp [signedLayers, signedCrossLayers, crossBlackLeft, downLayerDiagram, moveDiagram, lay, DoubleStrand.down])

private theorem map_braidL (a b : J) (j : I) (h : CanCross (δ a) (δ b)) :
    (F).map ((P₀).diag (braidL a b (.inl j))) =
      (D) [a,b,.inl j] [.inl j,b,a] (signedCapBraidLeft L (δ a) (δ b) (false,j) R) := by
  change (F).map ((P₀).diag (XL a b (.inl j) ≫ XR b a (.inl j) ≫ XL b (.inl j) a)) = _
  simp only [Presentation.diag_comp, Functor.map_comp]
  change (F).map ((P₀).diag (dl [] (.cross a b) [.inl j] rfl rfl)) ≫
    (F).map ((P₀).diag (dl [b] (.cross a (.inl j)) [] rfl rfl)) ≫
    (F).map ((P₀).diag (dl [] (.cross b (.inl j)) [a] rfl rfl)) = _
  have h₁ : CanCross (δ a) (δ (.inl j)) := by cases a <;> trivial
  have h₂ : CanCross (δ b) (δ (.inl j)) := by cases b <;> trivial
  rw [map_cross RD Λ P Q exponents μ L R [] [.inl j] a b h,
    map_cross RD Λ P Q exponents μ L R [b] [] a (.inl j) h₁,
    map_cross RD Λ P Q exponents μ L R [] [a] b (.inl j) h₂]
  have c₁ : signedChain ((wrd) [a,b,.inl j]) (signedCrossLayers L (δ a) (δ b) (δ (.inl j) :: R))
      ((wrd) [b,a,.inl j]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
      signedCrossLayers_chain L h (δ (.inl j) :: R)
  have c₂ : signedChain ((wrd) [b,a,.inl j]) (crossBlackLeft (L ++ [δ b]) (δ a) (false,j) R)
      ((wrd) [b,.inl j,a]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append, down_inl] using
      crossBlackLeft_chain (L ++ [δ b]) (δ a) (false,j) R
  have c₃ : signedChain ((wrd) [b,.inl j,a]) (crossBlackLeft L (δ b) (false,j) (δ a :: R))
      ((wrd) [.inl j,b,a]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append, down_inl] using
      crossBlackLeft_chain L (δ b) (false,j) (δ a :: R)
  have e₁ := signedDg_comp RD Λ (P₁) μ c₂ c₃
  have e₂ := signedDg_comp RD Λ (P₁) μ c₁ (c₂.append c₃)
  rw [← e₁] at e₂
  simpa only [signedCapBraidLeft, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil, List.map_cons, List.map_nil, down_inl, signedCrossLayers] using e₂

private theorem map_braidR (a b : J) (j : I) (h : CanCross (δ a) (δ b)) :
    (F).map ((P₀).diag (braidR a b (.inl j))) =
      (D) [a,b,.inl j] [.inl j,b,a] (signedCapBraidRight L (δ a) (δ b) (false,j) R) := by
  change (F).map ((P₀).diag (XR a b (.inl j) ≫ XL a (.inl j) b ≫ XR (.inl j) a b)) = _
  simp only [Presentation.diag_comp, Functor.map_comp]
  change (F).map ((P₀).diag (dl [a] (.cross b (.inl j)) [] rfl rfl)) ≫
    (F).map ((P₀).diag (dl [] (.cross a (.inl j)) [b] rfl rfl)) ≫
    (F).map ((P₀).diag (dl [.inl j] (.cross a b) [] rfl rfl)) = _
  have h₁ : CanCross (δ a) (δ (.inl j)) := by cases a <;> trivial
  have h₂ : CanCross (δ b) (δ (.inl j)) := by cases b <;> trivial
  rw [map_cross RD Λ P Q exponents μ L R [a] [] b (.inl j) h₂,
    map_cross RD Λ P Q exponents μ L R [] [b] a (.inl j) h₁,
    map_cross RD Λ P Q exponents μ L R [.inl j] [] a b h]
  have c₁ : signedChain ((wrd) [a,b,.inl j]) (crossBlackLeft (L ++ [δ a]) (δ b) (false,j) R)
      ((wrd) [a,.inl j,b]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append, down_inl] using
      crossBlackLeft_chain (L ++ [δ a]) (δ b) (false,j) R
  have c₂ : signedChain ((wrd) [a,.inl j,b]) (crossBlackLeft L (δ a) (false,j) (δ b :: R))
      ((wrd) [.inl j,a,b]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append, down_inl] using
      crossBlackLeft_chain L (δ a) (false,j) (δ b :: R)
  have c₃ : signedChain ((wrd) [.inl j,a,b]) (signedCrossLayers (L ++ [δ (.inl j)]) (δ a) (δ b) R)
      ((wrd) [.inl j,b,a]) := by
    simpa only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
      signedCrossLayers_chain (L ++ [δ (.inl j)]) h R
  have e₁ := signedDg_comp RD Λ (P₁) μ c₂ c₃
  have e₂ := signedDg_comp RD Λ (P₁) μ c₁ (c₂.append c₃)
  rw [← e₁] at e₂
  simpa only [signedCapBraidRight, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil, List.map_cons, List.map_nil, down_inl, signedCrossLayers] using e₂

private theorem down_braid_eq (a b : J) (j : I) (h : CanCross (δ a) (δ b))
    (hbraid : ¬ (a = .inl j ∧ a ≠ b)) :
    (D) [a,b,.inl j] [.inl j,b,a] (signedCapBraidLeft L (δ a) (δ b) (false,j) R) =
      (D) [a,b,.inl j] [.inl j,b,a] (signedCapBraidRight L (δ a) (δ b) (false,j) R) := by
  rw [← map_braidL RD Λ P Q exponents μ L R a b j h,
    ← map_braidR RD Λ P Q exponents μ L R a b j h]
  apply congrArg (F).map
  exact braid_at Qₐ (u := []) (v := []) hbraid (braidL a b (.inl j)) (braidR a b (.inl j)) rfl rfl

private theorem diagram_pow_count {a : Obj (signature RD Λ)} (d : End a)
    (h : crossingNumber d = 0) (n : ℕ) : crossingNumber (d ^ n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, End.mul_def, crossingNumber_comp, h, ih]

private theorem diag_pow {a : Obj (signature RD Λ)} (d : End a) (n : ℕ) :
    (P₁).diag (d ^ n) = End.of ((P₁).diag d) ^ n := by
  induction n with
  | zero => exact (P₁).diag_id _
  | succ n ih => rw [pow_succ, End.mul_def, Presentation.diag_comp, ih, pow_succ, End.mul_def]

private theorem down_dot_monomial (i : I) (r : Fin ℓ) (m n : ℕ) :
    let black : J := .inl i
    let red : J := .inr r
    (F).map (End.of ((P₀).diag (E0 black red black)) ^ m *
      End.of ((P₀).diag (E2 black red black)) ^ n) ∈
        signedCrossingSpan RD Λ (P₁) μ ((wrd) [black,red,black]) ((wrd) [black,red,black]) 2 := by
  let black : J := .inl i
  let red : J := .inr r
  let dot : Move I ℓ := .black (.dot (false,i))
  let d₀ : End (obj RD Λ μ ((wrd) [black,red,black])) :=
    downLayerDiagram RD Λ μ L R (lay [] (.dot black) [red,black]) (g := dot) rfl
  let d₂ : End (obj RD Λ μ ((wrd) [black,red,black])) :=
    downLayerDiagram RD Λ μ L R (lay [black,red] (.dot black) []) (g := dot) rfl
  have h₀ : (F).map ((P₀).diag (E0 black red black)) = (P₁).diag d₀ :=
    downPresentedFunctor_layer RD Λ Qₐ P μ L R (lay [] (.dot black) [red,black]) (lay_valid ..) rfl rfl rfl
  have h₂ : (F).map ((P₀).diag (E2 black red black)) = (P₁).diag d₂ :=
    downPresentedFunctor_layer RD Λ Qₐ P μ L R (lay [black,red] (.dot black) []) (lay_valid ..) rfl rfl rfl
  change ((F).mapEnd (X := (P₀).obj (ob [black,red,black])))
    (End.of ((P₀).diag (E0 black red black)) ^ m *
      End.of ((P₀).diag (E2 black red black)) ^ n) ∈ _
  rw [map_mul, map_pow, map_pow]
  change End.of ((F).map ((P₀).diag (E0 black red black))) ^ m *
    End.of ((F).map ((P₀).diag (E2 black red black))) ^ n ∈ _
  rw [h₀, h₂, ← diag_pow RD Λ P Q exponents d₀ m, ← diag_pow RD Λ P Q exponents d₂ n,
    End.mul_def, ← Presentation.diag_comp]
  let raw := (d₂ ^ n) ≫ (d₀ ^ m)
  change (P₁).diag raw ∈ _
  refine Submodule.subset_span ⟨raw, ?_, rfl⟩
  dsimp only [raw]
  rw [crossingNumber_comp, diagram_pow_count RD Λ d₂ rfl n, diagram_pow_count RD Λ d₀ rfl m]
  decide

local notation "leftBraid" => fun (a b : J) (j : I) =>
  (D) [a,b,Sum.inl j] [Sum.inl j,b,a] (signedCapBraidLeft L (δ a) (δ b) (false,j) R)
local notation "rightBraid" => fun (a b : J) (j : I) =>
  (D) [a,b,Sum.inl j] [Sum.inl j,b,a] (signedCapBraidRight L (δ a) (δ b) (false,j) R)
local notation "braidSpan" => fun (a b : J) (j : I) =>
  signedCrossingSpan RD Λ (P₁) μ ((wrd) [a,b,Sum.inl j]) ((wrd) [Sum.inl j,b,a]) 2

/-- With an outside red and two downward strands the affine-cover braid is exact. -/
theorem signedCapBraid_redBlack_down (r : Fin ℓ) (i j : I) :
    (leftBraid) (.inr r) (.inl i) j - (rightBraid) (.inr r) (.inl i) j ∈
      (braidSpan) (.inr r) (.inl i) j := by
  rw [down_braid_eq RD Λ P Q exponents μ L R (.inr r) (.inl i) j trivial
    (fun h => Sum.inr_ne_inl h.1), sub_self]
  exact Submodule.zero_mem _

open scoped Matrix in
/-- With red between two downward strands the affine-cover braid correction
has zero crossings, including when the black colours agree. -/
theorem signedCapBraid_blackRed_down (r : Fin ℓ) (i j : I) :
    (leftBraid) (.inl i) (.inr r) j - (rightBraid) (.inl i) (.inr r) j ∈
      (braidSpan) (.inl i) (.inr r) j := by
  classical
  by_cases hij : i = j
  · subst j
    let b : J := .inl i
    let r' : J := .inr r
    have h := braidQ_at Qₐ (u := []) (v := []) (c := b) (d := r') Sum.inl_ne_inr
      (braidL b r' b) (braidR b r' b) (E0 b r' b) (E1 b r' b) (E2 b r' b) rfl rfl rfl rfl rfl
    rw [qbar_affineCoverQ_black_red, KL3.Diagram.ncEval_sum_aux] at h
    simp only [KL3.Diagram.ncEval_X0_pow_mul_X2_pow, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    change (leftBraid) b r' i - (rightBraid) b r' i ∈ (braidSpan) b r' i
    rw [← map_braidL RD Λ P Q exponents μ L R b r' i trivial,
      ← map_braidR RD Λ P Q exponents μ L R b r' i trivial]
    let Fₗ := (F).mapLinearMap k (X := (P₀).obj (ob [b,r',b])) (Y := (P₀).obj (ob [b,r',b]))
    change Fₗ ((P₀).diag (braidL b r' b)) - Fₗ ((P₀).diag (braidR b r' b)) ∈ _
    rw [← map_sub, h, map_sum]
    exact Submodule.sum_mem _ (fun m _ => down_dot_monomial RD Λ P Q exponents μ L R i r m
      (exponents r i - 1 - m))
  · rw [down_braid_eq RD Λ P Q exponents μ L R (.inl i) (.inr r) j trivial
      (fun h => hij (Sum.inl.inj h.1)), sub_self]
    exact Submodule.zero_mem _

end Categorification.Stendhal.DoubleDiagram
