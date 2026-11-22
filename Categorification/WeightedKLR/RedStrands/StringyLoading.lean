/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaximalLoading
import Categorification.KLR.CyclotomicStringParametrization
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition

/-!
# Stringy loadings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Definition 5.16 and Proposition 5.17. The black blocks of a loading are compared with the string
parametrizations of simple modules over the cyclotomic quotients of the KLR algebra.

## Main results

* `cycKLR_x_isNilpotent`: the dots act nilpotently in the cyclotomic quotient
  `R^{λ}(β)` for monomial cyclotomic polynomials `X^{λ_i}`.
* `blackBlocks`, `LoadLT`: the black blocks of a loading and the order of Proposition 5.17,
  dominance on black counts with ties broken by the string keys of the blocks.
* `IsStringy`: Definition 5.16.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra
variable {I k : Type*} [DecidableEq I] [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C Q) (μ : I →₀ ℕ) (β : Multiset I)

include hQ in
/-- The dots are nilpotent in the cyclotomic quotient with monomial cyclotomic polynomials,
through the identification with the tensor product algebra of one red strand. -/
theorem cycKLR_x_isNilpotent (a : Fin (Multiset.card β)) :
    IsNilpotent (CycKLR.mk k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i) β (x a)) := by
  obtain ⟨N, hN⟩ := tensorProjection_dot_nilpotent (fun _ : Fin 1 => μ) β hQ
    (SingleRed.blackPos β a)
  refine ⟨N, (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => μ) β).injective ?_⟩
  rw [map_pow, map_zero, ← hN]
  congr 1
  change SingleRed.cyclotomicProjection Q (fun _ : Fin 1 => μ) β (CycKLR.mk _ _ _ _ (x a)) = _
  rw [SingleRed.cyclotomicProjection, CycKLR.lift_mk, SingleRed.insertRed_x]
  change TensorProductAlgebra.mk Q _ β _ = TensorProductAlgebra.mk Q _ β
    (orderProjection Q _ β (affineCover Q _ β (x _)))
  rw [affineCover_x]
  congr 1
  apply Subtype.ext
  change _ = _ * StendhalAlgebraAllOrders.redOrderedIdem k Q _ β
  have h1 := SingleRed.redOrderedIdem_eq_one Q (fun _ : Fin 1 => μ) β
  have h2 : StendhalAlgebraAllOrders.x (SingleRed.blackPos β a) *
      StendhalAlgebraAllOrders.redOrderedIdem k Q (fun _ : Fin 1 => μ) β =
      StendhalAlgebraAllOrders.x (SingleRed.blackPos β a) := by
    rw [h1, mul_one]
  rw [h2]
  rfl
end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra

section Blocks

variable {I R : Type*}

/-- The maximal blocks of black strands of a word, read left to right between red strands. -/
def blackBlocks : List (I ⊕ R) → List (List I)
  | [] => [[]]
  | .inl i :: l => (blackBlocks l).modifyHead (i :: ·)
  | .inr _ :: l => [] :: blackBlocks l

theorem blackBlocks_ne_nil (l : List (I ⊕ R)) : blackBlocks l ≠ [] := by
  induction l with
  | nil => simp [blackBlocks]
  | cons x l ih =>
    rcases x with i | r
    · obtain ⟨a, l', h⟩ := List.exists_cons_of_ne_nil ih
      simp [blackBlocks, h]
    · simp [blackBlocks]

theorem blackBlocks_map {R' : Type*} (f : R → R') (l : List (I ⊕ R)) :
    blackBlocks (l.map (Sum.map id f)) = blackBlocks l := by
  induction l with
  | nil => rfl
  | cons x l ih => rcases x with i | r <;> simp [blackBlocks, ih]

theorem blackBlocks_append_inr (l m : List (I ⊕ R)) (r : R) :
    blackBlocks (l ++ .inr r :: m) = blackBlocks l ++ blackBlocks m := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rcases x with i | r'
    · obtain ⟨a, l', h⟩ := List.exists_cons_of_ne_nil (blackBlocks_ne_nil l)
      simp [blackBlocks, ih, h]
    · simp [blackBlocks, ih]

theorem blackBlocks_map_inl (w : List I) :
    blackBlocks (w.map (Sum.inl : I → I ⊕ R)) = [w] := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [blackBlocks, ih]

end Blocks

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {θ β : Multiset I}

omit [DecidableEq I] in
theorem blackBlocks_twoPieceLoading (t : Seq (stendhalWeight ℓ θ)) (w : Seq β) :
    blackBlocks (List.ofFn (twoPieceLoading θ β t w).lbl) =
      blackBlocks (List.ofFn t.lbl) ++ [List.ofFn w.1] := by
  rw [ofFn_twoPieceLoading, blackBlocks_append_inr, blackBlocks_map_inl]
  congr 1
  exact blackBlocks_map _ _

section Order

/-- Lists of keys compared entrywise. -/
theorem forall₂_le_trans {α : Type*} [Preorder α] {a b c : List α}
    (h₁ : List.Forall₂ (· ≤ ·) a b) (h₂ : List.Forall₂ (· ≤ ·) b c) :
    List.Forall₂ (· ≤ ·) a c := by
  induction h₁ generalizing c with
  | nil => exact h₂
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc h => exact .cons (le_trans hab hbc) (ih h)

theorem forall₂_le_antisymm {α : Type*} [PartialOrder α] {a b : List α}
    (h₁ : List.Forall₂ (· ≤ ·) a b) (h₂ : List.Forall₂ (· ≤ ·) b a) : a = b := by
  induction h₁ with
  | nil => rfl
  | cons hab _ ih =>
    cases h₂ with
    | cons hba h => rw [le_antisymm hab hba, ih h]

variable {μ : Multiset (I ⊕ Fin ℓ)}

/-- The string keys of the black blocks of a loading. -/
def blockKeys (σ : ℕ → I) (p : Seq μ) : List (Lex (ℕ → ℕ)) :=
  (blackBlocks (List.ofFn p.lbl)).map (KLR.strKey σ)

/-- The order on loadings used in Proposition 5.17: Webster's dominance order on the black
counts, with ties broken by comparing the string keys of the black blocks entrywise. -/
def LoadLT (σ : ℕ → I) (p q : Seq μ) : Prop :=
  StendhalLT p q ∨ (StendhalLE p q ∧ StendhalLE q p ∧
    List.Forall₂ (· ≤ ·) (blockKeys σ p) (blockKeys σ q) ∧ blockKeys σ p ≠ blockKeys σ q)

theorem loadLT_irrefl (σ : ℕ → I) (p : Seq μ) : ¬ LoadLT σ p p := by
  rintro (h | ⟨-, -, -, h⟩)
  · exact h.2 h.1
  · exact h rfl

theorem loadLT_trans {σ : ℕ → I} {p q r : Seq μ} (h₁ : LoadLT σ p q) (h₂ : LoadLT σ q r) :
    LoadLT σ p r := by
  rcases h₁ with h₁ | ⟨a₁, b₁, c₁, d₁⟩ <;> rcases h₂ with h₂ | ⟨a₂, b₂, c₂, d₂⟩
  · exact .inl ⟨stendhalLE_trans h₁.1 h₂.1, fun h => h₁.2 (stendhalLE_trans h₂.1 h)⟩
  · exact .inl ⟨stendhalLE_trans h₁.1 a₂, fun h => h₁.2 (stendhalLE_trans a₂ h)⟩
  · exact .inl ⟨stendhalLE_trans a₁ h₂.1, fun h => h₂.2 (stendhalLE_trans h a₁)⟩
  · refine .inr ⟨stendhalLE_trans a₁ a₂, stendhalLE_trans b₂ b₁, forall₂_le_trans c₁ c₂,
      fun h => d₁ (forall₂_le_antisymm c₁ ?_)⟩
    rw [h]
    exact c₂

theorem stendhalLT.loadLT {σ : ℕ → I} {p q : Seq μ} (h : StendhalLT p q) : LoadLT σ p q :=
  .inl h

end Order

theorem forall₂_append_singleton_iff {α β : Type*} {R : α → β → Prop} {a : List α} {b : List β}
    {x : α} {y : β} : List.Forall₂ R (a ++ [x]) (b ++ [y]) ↔ List.Forall₂ R a b ∧ R x y := by
  rw [← List.forall₂_reverse_iff, List.reverse_append, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.forall₂_cons,
    List.forall₂_reverse_iff]
  exact and_comm

section TwoPiece

variable {θ β : Multiset I}

theorem stendhalLE_twoPiece_iff (t t' : Seq (stendhalWeight ℓ θ)) (w w' : Seq β) :
    StendhalLE (twoPieceLoading θ β t w) (twoPieceLoading θ β t' w') ↔ StendhalLE t t' := by
  constructor
  · intro h r i
    have := h r.castSucc i
    rwa [blackCount_twoPieceLoading_castSucc, blackCount_twoPieceLoading_castSucc] at this
  · intro h R i
    rcases Fin.eq_castSucc_or_eq_last R with ⟨r, rfl⟩ | rfl
    · rw [blackCount_twoPieceLoading_castSucc, blackCount_twoPieceLoading_castSucc]
      exact h r i
    · rw [blackCount_twoPieceLoading_last, blackCount_twoPieceLoading_last]

theorem blockKeys_twoPiece (σ : ℕ → I) (t : Seq (stendhalWeight ℓ θ)) (w : Seq β) :
    blockKeys σ (twoPieceLoading θ β t w) = blockKeys σ t ++ [KLR.strKey σ (List.ofFn w.1)] := by
  rw [blockKeys, blackBlocks_twoPieceLoading, List.map_append]
  rfl

theorem loadLT_twoPiece_left {σ : ℕ → I} {t t' : Seq (stendhalWeight ℓ θ)} (h : LoadLT σ t t')
    (w : Seq β) : LoadLT σ (twoPieceLoading θ β t w) (twoPieceLoading θ β t' w) := by
  rcases h with h | ⟨a, b, c, d⟩
  · exact .inl ⟨(stendhalLE_twoPiece_iff _ _ _ _).2 h.1,
      fun h' => h.2 ((stendhalLE_twoPiece_iff _ _ _ _).1 h')⟩
  · refine .inr ⟨(stendhalLE_twoPiece_iff _ _ _ _).2 a, (stendhalLE_twoPiece_iff _ _ _ _).2 b,
      ?_, ?_⟩
    · rw [blockKeys_twoPiece, blockKeys_twoPiece]
      exact forall₂_append_singleton_iff.2 ⟨c, le_rfl⟩
    · rw [blockKeys_twoPiece, blockKeys_twoPiece]
      exact fun h' => d (List.append_inj_left' h' rfl)

theorem loadLT_twoPiece_right {σ : ℕ → I} (t : Seq (stendhalWeight ℓ θ)) {w w' : Seq β}
    (h : KLR.strKey σ (List.ofFn w.1) < KLR.strKey σ (List.ofFn w'.1)) :
    LoadLT σ (twoPieceLoading θ β t w) (twoPieceLoading θ β t w') := by
  refine .inr ⟨(stendhalLE_twoPiece_iff _ _ _ _).2 fun _ _ => le_rfl,
    (stendhalLE_twoPiece_iff _ _ _ _).2 fun _ _ => le_rfl, ?_, ?_⟩
  · rw [blockKeys_twoPiece, blockKeys_twoPiece]
    exact forall₂_append_singleton_iff.2 ⟨List.forall₂_refl _, h.le⟩
  · rw [blockKeys_twoPiece, blockKeys_twoPiece]
    exact fun h' => h.ne (List.append_inj_right' h' rfl |> List.singleton_inj.1)

theorem loadLT_twoPiece_cases {σ : ℕ → I} {t t' : Seq (stendhalWeight ℓ θ)} {w w' : Seq β}
    (h : LoadLT σ (twoPieceLoading θ β t w) (twoPieceLoading θ β t' w')) :
    LoadLT σ t t' ∨ (StendhalLE t t' ∧ StendhalLE t' t ∧ blockKeys σ t = blockKeys σ t' ∧
      KLR.strKey σ (List.ofFn w.1) < KLR.strKey σ (List.ofFn w'.1)) := by
  rcases h with h | ⟨a, b, c, d⟩
  · exact .inl (.inl ⟨(stendhalLE_twoPiece_iff _ _ _ _).1 h.1,
      fun h' => h.2 ((stendhalLE_twoPiece_iff _ _ _ _).2 h')⟩)
  · rw [stendhalLE_twoPiece_iff] at a b
    rw [blockKeys_twoPiece, blockKeys_twoPiece] at c d
    obtain ⟨c₁, c₂⟩ := forall₂_append_singleton_iff.1 c
    by_cases hk : blockKeys σ t = blockKeys σ t'
    · refine .inr ⟨a, b, hk, lt_of_le_of_ne c₂ fun he => d ?_⟩
      rw [hk, he]
    · exact .inl (.inr ⟨a, b, c₁, hk⟩)

end TwoPiece

section Support

open Categorification.Graded GProj

variable {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

/-- The red-ordered loadings whose idempotents act nonzero on the top of a shift class. -/
def loadSupp (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I} {G : KLR.GradingDatum (stendhalQ Q Λ)}
    (c : IndecClass (tensorProductGrade G ν)) : Set (Seq (stendhalWeight ℓ ν)) :=
  {p | ∃ hp : IsRedOrdered p, ∃ x : c.top, seqIdem Q Λ p hp • x ≠ 0}

/-- `p` acts nonzero on the top of `c`, and no loading above it in `LoadLT` does. -/
def IsMaxLoad (σ : ℕ → I) (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}
    {G : KLR.GradingDatum (stendhalQ Q Λ)} (c : IndecClass (tensorProductGrade G ν))
    (p : Seq (stendhalWeight ℓ ν)) : Prop :=
  p ∈ loadSupp Λ c ∧ ∀ q ∈ loadSupp Λ c, ¬ LoadLT σ p q

variable (k Q) in
/-- **Webster, arXiv:1309.3796v2, Definition 5.16.** A loading is stringy when no black strand
lies left of the first red strand and the black block right of the `j`-th red strand is the
string parametrization of a simple module of the cyclotomic quotient `R^{λ_j}`. -/
def IsStringy (σ : ℕ → I) : (ℓ : ℕ) → (Λ : Fin ℓ → I →₀ ℕ) → (ν : Multiset I) →
    Seq (stendhalWeight ℓ ν) → Prop
  | 0, _, ν, _ => ν = 0
  | ℓ + 1, Λ, ν, p => ∃ (θ β : Multiset I) (h : θ + β = ν) (t : Seq (stendhalWeight ℓ θ))
      (w : Seq β), IsRedOrdered t ∧
      Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h) (twoPieceLoading θ β t w) = p ∧
      IsStringy σ ℓ (Λ ∘ Fin.castSucc) θ t ∧
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module k M)
        (_ : Module (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β) M)
        (_ : IsScalarTower k
          (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β) M)
        (_ : FiniteDimensional k M)
        (_ : IsSimpleModule
          (CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β) M),
        CycKLR.IsStrMax Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β M σ w

end Support

end Categorification.Stendhal
