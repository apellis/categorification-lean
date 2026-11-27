/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraidQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlackDownBraid
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlackDownBraidQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedRepeat

/-!
# All downward KLR relations in a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25: the 2-category `𝒯` imposes the KLR
relations of Definition 4.5 on downward strands (Definition 4.24). For a Rouquier family with
red lines and red/up crossings, the generator images `genImg` kill every downward KLR relation
in every signed context (`admissibleMap_downRelation`, from the empty context,
`admissibleMap_downRelation_empty`), provided

* the family satisfies the mixed KLR relations for the black polynomials (`RouqUpKLR`);
* the red/down crossings satisfy the bigon relation (`DownBigon`), are natural for downward
  dots (`UpIsoDotNatural`) and for downward black crossings (`DownDotCrossNatural`,
  `DownQuotCrossNatural`, `DownMidCrossNatural`), and satisfy the triple point `[i, r, i]`
  (`DownMidSame`);
* words with a red label twice vanish (`RepeatedRedZero`);

and the polynomials are those of Webster's §2.2: `Q_{ir} = x₀^{n_{ri}}`, `Q_{ri} = x₁^{n_{ri}}`,
and the red/red polynomials have no constant term. These hypotheses are properties of the
generator images; they are discharged for the cyclotomic region model in the assembly of
Theorem 4.25.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} [DecidableEq I] {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  {S : RouqFamily (B := B) RD}
  {red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x)}
  {upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁)}
  (Sc : CL.CLScalars C k)

/-- **The bare downward KLR relations.** Every KLR relation on downward strands in the empty
signed context is killed by the generator images. -/
theorem admissibleMap_downRelation_empty {Qb : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Qb) (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (hdot : UpIsoDotNatural S red upIso) (hrbb : DownDotCrossNatural S red upIso)
    (hbbr : DownQuotCrossNatural S red upIso) (hbrb : DownMidCrossNatural S red upIso)
    (hmid : DownMidSame S red upIso n) (hrep : RepeatedRedZero S red)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hQb : ∀ i j : I, Q (.inl i) (.inl j) = Qb i j)
    (hQir : ∀ (i : I) (r : Fin ℓ), Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i)
    (hQri : ∀ (i : I) (r : Fin ℓ), Q (.inr r) (.inl i) = MvPolynomial.X 1 ^ n r i)
    (hQrr : ∀ s t : Fin ℓ, MvPolynomial.constantCoeff (Q (.inr s) (.inr t)) = 0)
    (m : X) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] r.dom))
    (hb : Cond x y (downContextObj RD Λ m [] [] r.cod)) :
    admissibleMap (genImg S red upIso Sc) ha hb
      (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r)) = 0 := by
  have two : 2 ≤ r.dom.word.countP (fun c => c.isRight) →
      admissibleMap (genImg S red upIso Sc) ha hb
        (downLinear RD Λ k m [] [] (KLR.Diagram.relation k Q r)) = 0 :=
    fun h2 => admissibleMap_downRelation_of_two_red hrep _ Q hQrr m r h2 ha hb
  cases r with
  | sqEq c =>
    rcases c with i | s
    · exact admissibleMap_sqEq_ii (S := S) (red := red) (upIso := upIso) (Sc := Sc) (Q := Q)
        i m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | sqNe c d h =>
    rcases c with i | s <;> rcases d with j | t
    · exact admissibleMap_sqNe_ij Sc Q H hQb i j (fun e => h (congrArg _ e)) m ha hb
    · exact admissibleMap_sqNe_ir (S := S) (red := red) (upIso := upIso) (Sc := Sc) n hB Q i t
        (hQir i t) m ha hb
    · exact admissibleMap_sqNe_ri (S := S) (red := red) (upIso := upIso) (Sc := Sc) n hB Q j s
        (hQri j s) m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | slideLEq c =>
    rcases c with i | s
    · exact admissibleMap_slideLEq_ii (S := S) (red := red) (upIso := upIso) (Sc := Sc)
        (Q := Q) i m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | slideLNe c d h =>
    rcases c with i | s <;> rcases d with j | t
    · exact admissibleMap_slideLNe_ij Sc Q H i j (fun e => h (congrArg _ e)) m ha hb
    · rw [downLinear_slideLNe_ir (Q := Q) m i t, map_zero]
    · exact admissibleMap_slideLNe_ri (S := S) (red := red) (upIso := upIso) (Sc := Sc)
        (Q := Q) hdot j s m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | slideREq c =>
    rcases c with i | s
    · exact admissibleMap_slideREq_ii (S := S) (red := red) (upIso := upIso) (Sc := Sc)
        (Q := Q) i m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | slideRNe c d h =>
    rcases c with i | s <;> rcases d with j | t
    · exact admissibleMap_slideRNe_ij Sc Q H i j (fun e => h (congrArg _ e)) m ha hb
    · exact admissibleMap_slideRNe_ir (S := S) (red := red) (upIso := upIso) (Sc := Sc)
        (Q := Q) hdot i t m ha hb
    · rw [downLinear_slideRNe_ri (Q := Q) m j s, map_zero]
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | braid c d e h =>
    rcases c with i | s <;> rcases d with j | t <;> rcases e with c | t'
    · by_cases hic : i = c
      · subst hic
        have hij : i = j := by
          by_contra hij
          exact h ⟨rfl, fun e => hij (Sum.inl_injective e)⟩
        subst hij
        exact admissibleMap_braid_bbb Sc i i i (downBlackBraid_self S i) Q h m ha hb
      · exact admissibleMap_braid_bbb Sc i j c (downBlackBraid_of_ne S H i j c hic) Q h m ha hb
    · exact admissibleMap_braid_bbr Sc hbbr Q i j t' h m ha hb
    · exact admissibleMap_braid_brb Sc hbrb Q i t c h m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
    · exact admissibleMap_braid_rbb Sc hrbb Q s j c h m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])
    · exact two (by simp [KLR.Diagram.Rel.dom])
    · exact two (by simp [KLR.Diagram.Rel.dom])
  | braidQ c d h =>
    rcases c with i | s
    · rcases d with j | t
      · exact admissibleMap_braidQ_iji (S := S) (red := red) (upIso := upIso) (Sc := Sc) H Q i j (fun e => h (congrArg _ e)) (hQb i j) m ha hb
      · exact admissibleMap_braidQ_iri Sc n hmid Q i t (hQir i t) m ha hb
    · exact two (by simp [KLR.Diagram.Rel.dom])

/-- **The downward KLR relations in every signed context** (Webster, arXiv:1309.3796v3,
Definition 4.24) are killed by the generator images. -/
theorem admissibleMap_downRelation {Qb : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Qb) (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (hdot : UpIsoDotNatural S red upIso) (hrbb : DownDotCrossNatural S red upIso)
    (hbbr : DownQuotCrossNatural S red upIso) (hbrb : DownMidCrossNatural S red upIso)
    (hmid : DownMidSame S red upIso n) (hrep : RepeatedRedZero S red)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hQb : ∀ i j : I, Q (.inl i) (.inl j) = Qb i j)
    (hQir : ∀ (i : I) (r : Fin ℓ), Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i)
    (hQri : ∀ (i : I) (r : Fin ℓ), Q (.inr r) (.inl i) = MvPolynomial.X 1 ^ n r i)
    (hQrr : ∀ s t : Fin ℓ, MvPolynomial.constantCoeff (Q (.inr s) (.inr t)) = 0)
    [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
    [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
    (P : Presentation.{w, max u v} (signature RD Λ) k) (a : DownRelation X I ℓ) {x y : X}
    (ha : Cond x y ((addDownRelations RD Λ Q P).dom (.inr a)))
    (hb : Cond x y ((addDownRelations RD Λ Q P).cod (.inr a))) :
    admissibleMap (genImg S red upIso Sc) ha hb ((addDownRelations RD Λ Q P).rel (.inr a)) = 0 :=
  admissibleMap_downRelation_of_bare (genImg S red upIso Sc) Q P a
    (fun m _ _ ha' hb' => admissibleMap_downRelation_empty Sc H n hB hdot hrbb hbbr hbrb hmid
      hrep Q hQb hQir hQri hQrr m a.rel ha' hb') ha hb

end Categorification.Stendhal.DoubleDiagram
