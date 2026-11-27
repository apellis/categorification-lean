/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownBraid

/-!
# The downward triple point `[i, r, i]` in a Rouquier family

Webster, arXiv:1309.3796v3, (4.1) read downward, with the red strand between two black strands
of the same colour, in the proof of Theorem 4.25. The two ways of moving the strands of
`[i, r, i]` past each other differ by the divided difference of the polynomial
`Q_{i r}(u, v) = u^{n}` of the bigon (4.2), that is, by `∑_{t < n} y₀^t y₂^{n-1-t}` in the dots
on the two black strands. The downward translation of this relation is killed by the generator
images `genImg` as soon as the corresponding identity holds in the target bicategory
(`DownMidSame`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp MvPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

section Poly

variable {k : Type w} [CommRing k] {A : Type*} [Ring A] [Algebra k A]

omit [AddCommGroup X] in
theorem ncEval_X_zero_pow_mul_X_two_pow (y : Fin 3 → A) (t s : ℕ) :
    KLR.ncEval y (MvPolynomial.X 0 ^ t * MvPolynomial.X 2 ^ s : MvPolynomial (Fin 3) k) =
      y 0 ^ t * y 2 ^ s := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  unfold KLR.ncEval
  change (Finsupp.single _ _).sum _ = _
  rw [Finsupp.sum_single_index (by simp), map_one, one_mul]
  simp [List.ofFn_succ, Finsupp.single_apply]

omit [AddCommGroup X] in
theorem ncEval_finset_sum {n : ℕ} (y : Fin n → A) {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) k) :
    KLR.ncEval y (∑ x ∈ s, p x) = ∑ x ∈ s, KLR.ncEval y (p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [KLR.ncEval]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, KLR.ncEval_add, ih]

end Poly

theorem relation_braidQ {k : Type w} [CommRing k] {J : Type*}
    (Q : J → J → MvPolynomial (Fin 2) k) (c d : J) (h : c ≠ d) :
    KLR.Diagram.relation k Q (.braidQ c d h) = (LinDiagram.of (KLR.Diagram.braidL c d c) -
      LinDiagram.of (KLR.Diagram.braidR c d c) -
      KLR.Diagram.lpoly k ![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c]
        (KLR.qbar (Q c d)) : LinDiagram k (KLR.Diagram.ob [c, d, c]) (KLR.Diagram.ob [c, d, c])) :=
  rfl

local notation "fwT" => fw (S := signature RD Λ)
local notation "wD" i => DoubleStrand.weight RD Λ (Sum.inl (false, i))

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

theorem downLinear_E0_iri (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of
        (KLR.Diagram.E0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [] (.black (.dot (false, i)))
        [.inr r, .inl (false, i)]) rfl rfl) := by
  rw [KLR.Diagram.E0, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

theorem downLinear_E2_iri (s : X) (i : I) (r : Fin ℓ) :
    downLinear RD Λ k s [] [] (LinDiagram.of
        (KLR.Diagram.E2 (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i))) =
      LinDiagram.of (Diagram.cast (moveDiagram RD Λ s [.inl (false, i), .inr r]
        (.black (.dot (false, i))) []) rfl rfl) := by
  rw [KLR.Diagram.E2, KLR.Diagram.dl, downLinear_layer,
    downLinearLayer_of_move (g := .black (.dot (false, i))) RD Λ k s [] [] _ rfl,
    LinDiagram.cast_of]
  congr 1

/-- The image of the dot on the left black strand of the downward word `[i, r, i]`. -/
theorem downEndAlg_E0_iri (m : X) (i : I) (r : Fin ℓ)
    (hc : Cond m (((m + (wD i)) + Λ r) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])))
    (h₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + Λ r) + (wD i)) + RD.iX i = (m + (wD i)) + Λ r)
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) hc.1 hc.2.1 ⟶
      (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) m [.inl i, .inr r, .inl i] hc
        (LinDiagram.of (KLR.Diagram.E0 (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ ((S.E i q ≫ red r rfl) ◁ S.dot i h₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  rw [downEndAlg_apply, downLinear_E0_iri, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ m []
      (.black (.dot (false, i))) [.inr r, .inl (false, i)]) rfl rfl) =
      [layer RD Λ m [] (.black (.dot (false, i))) [.inr r, .inl (false, i)]] by
        simp [moveDiagram])]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
    (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := Uj ≫ Ui) (q₁ := 𝟙 _) (x₁ := R0)
    (y₁ := R0) (S.dot i h₁) (N ≫ (Uj ≫ Ui) ◁ (ρ_ R0).inv) ((Uj ≫ Ui) ◁ (ρ_ R0).hom ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_rightUnitor_hom, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
      Category.assoc, lift_map₂_rightUnitor_inv]
    congr 2
    change (ρ_ _).inv ≫ S.dot i h₁ ▷ 𝟙 _ ≫ (ρ_ _).hom = _
    rw [whiskerRight_id]
    simp
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) h₁
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_pair
  case hl => intro _ _; double_nil
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

/-- The image of the dot on the right black strand of the downward word `[i, r, i]`. -/
theorem downEndAlg_E2_iri (m : X) (i : I) (r : Fin ℓ)
    (hc : Cond m (((m + (wD i)) + Λ r) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])))
    (h₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + Λ r) + (wD i)) + RD.iX i = (m + (wD i)) + Λ r)
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) hc.1 hc.2.1 ⟶
      (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) hc.1 hc.2.1) :
    downEndAlg (k := k) (genImg S red upIso Sc) m [.inl i, .inr r, .inl i] hc
        (LinDiagram.of (KLR.Diagram.E2 (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i))) =
      (doubleModel S red).lift.map₂ N ≫ ((S.dot i q ▷ red r rfl) ▷ S.E i h₁) ≫
        (doubleModel S red).lift.map₂ N' := by
  rw [downEndAlg_apply, downLinear_E2_iri, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  rw [admissibleChain_congr _ (show Diagram.layers (Diagram.cast (moveDiagram RD Λ m
      [.inl (false, i), .inr r] (.black (.dot (false, i))) []) rfl rfl) =
      [layer RD Λ m [.inl (false, i), .inr r] (.black (.dot (false, i))) []] by
        simp [moveDiagram])]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
    (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  rw [admissibleChain₁_conj (doubleModel S red) _ _ _ _ (p₁ := 𝟙 _) (q₁ := Ui ≫ R0) (x₁ := Uj)
    (y₁ := Uj) (S.dot i q) (N ≫ (α_ Uj Ui R0).hom ≫ (λ_ _).inv)
    ((λ_ _).hom ≫ (α_ Uj Ui R0).inv ≫ N')
    ?hn ?hm ?hr ?hl ?hd ?he ?hg]
  · simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_associator_hom,
      lift_map₂_associator_inv, lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv,
      Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    change (α_ _ _ _).hom ≫ (λ_ _).inv ≫ 𝟙 _ ◁ (S.dot i q ▷ _) ≫ (λ_ _).hom ≫
      (α_ _ _ _).inv = _
    simp
    rfl
  case hg =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact blackImg_dot_dn' S red Sc _ i _ _ _ _ _ _ (by double_regions) (by double_regions) q
  case hn => double_regions
  case hm => double_regions
  case hr => intro _ _; double_nil
  case hl => intro _ _; double_pair
  case hd => intro _ _; double_single
  case he => intro _ _; double_single

/-- **A red strand between two downward strands of the same colour** (Webster,
arXiv:1309.3796v3, (4.1) read downward, with the red strand in the middle): the two ways of
moving the strands of `[i, r, i]` past each other differ by `∑_{t < n} y₀^t y₂^{n-1-t}`, where
`y₀` and `y₂` are the dots on the right and on the left black strand of the composite and `n`
is the exponent of the bigon (4.2). -/
def DownMidSame (n : Fin ℓ → I → ℕ) : Prop :=
  ∀ (r : Fin ℓ) (i : I) {μ μi μij ρ ρi T : X} (f₁ : μi + RD.iX i = μ)
    (f₂ : μij + RD.iX i = μi) (hR : μi + Λ r = ρi) (e₁ : μij + Λ r = T) (q : T + RD.iX i = ρi)
    (hr : μ + Λ r = ρ) (q₃ : ρi + RD.iX i = ρ),
    S.E i q ◁ redDownQuot S red upIso r i f₁ hR hr q₃ ≫ (α_ _ _ _).inv ≫
        S.cross i i q q₃ q q₃ ▷ red r hr ≫ (α_ _ _ _).hom ≫
        S.E i q ◁ redDownDot S red upIso r i f₁ hR hr q₃ =
      (α_ _ _ _).inv ≫ redDownDot S red upIso r i f₂ e₁ hR q ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        red r e₁ ◁ S.cross i i f₂ f₁ f₂ f₁ ≫ (α_ _ _ _).inv ≫
        redDownQuot S red upIso r i f₂ e₁ hR q ▷ S.E i f₁ ≫ (α_ _ _ _).hom +
      (α_ (S.E i q) (red r hR) (S.E i f₁)).inv ≫
        (∑ t ∈ Finset.range (n r i),
          (show End ((S.E i q ≫ red r hR) ≫ S.E i f₁) from
            (S.E i q ≫ red r hR) ◁ S.dot i f₁) ^ t *
          (show End ((S.E i q ≫ red r hR) ≫ S.E i f₁) from
            (S.dot i q ▷ red r hR) ▷ S.E i f₁) ^ (n r i - 1 - t)) ≫
        (α_ (S.E i q) (red r hR) (S.E i f₁)).hom

variable {S red upIso}

/-- The image of the downward braid `ψ₀ψ₁ψ₀` on `[i, r, i]`, read through free 2-morphisms. -/
theorem admissibleMap_braidL_iri (m : X) (i : I) (r : Fin ℓ)
    (ha hb : Cond m (((m + (wD i)) + Λ r) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + Λ r) + (wD i)) + RD.iX i = (m + (wD i)) + Λ r)
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) ha.1 ha.2.1 ⟶
      (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) ha.1 ha.2.1)
    (q₃ : ((m + (wD i)) + Λ r) + RD.iX i = m + Λ r) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.braidL (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i)))) =
      (doubleModel S red).lift.map₂ N ≫ (α_ (S.E i q) (red r rfl) (S.E i f₁)).hom ≫
        (S.E i q ◁ redDownQuot S red upIso r i f₁ rfl rfl q₃ ≫ (α_ _ _ _).inv ≫
        S.cross i i q q₃ q q₃ ▷ red r rfl ≫ (α_ _ _ _).hom ≫
        S.E i q ◁ redDownDot S red upIso r i f₁ rfl rfl q₃) ≫
        (α_ (S.E i q) (red r rfl) (S.E i f₁)).inv ≫ (doubleModel S red).lift.map₂ N' := by
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [] [.inl i] [.inr r] []
    [] [.inl i] (.cross (.inl i) (.inr r)) (.cross (.inl i) (.inl i)) (.cross (.inr r) (.inl i))
    rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inr r, .inl i])
    (b := KLR.Diagram.ob [.inr r, .inl i, .inl i]) (c := KLR.Diagram.ob [.inr r, .inl i, .inl i])
    (d := KLR.Diagram.ob [.inl i, .inr r, .inl i]) rfl rfl rfl rfl rfl rfl
  erw [eD, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD
  rw [admissibleChain_congr _ hD]
  have e₄ : (m + Λ r) + (wD i) = (m + (wD i)) + Λ r := by double_regions
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
    (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui5 := fwT m [(m, .inr r)] (m + Λ r) ⟨rfl, trivial⟩ rfl
  let R5 := fwT (m + Λ r) [(m + Λ r, .inl (false, i))] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ e₄
  erw [admissibleChain₃_conj (doubleModel S red) (genImg S red upIso Sc) _ ha hb
      (p₁ := Uj) (q₁ := 𝟙 _) (x₁ := Ui ≫ R0) (y₁ := R5 ≫ Ui5)
      (p₂ := 𝟙 _) (q₂ := Ui5) (x₂ := Uj ≫ R5) (y₂ := Uj ≫ R5)
      (p₃ := Uj) (q₃ := 𝟙 _) (x₃ := R5 ≫ Ui5) (y₃ := Ui ≫ R0)
      (redDownQuot S red upIso r i f₁ rfl rfl q₃) (S.cross i i q q₃ q q₃)
      (redDownDot S red upIso r i f₁ rfl rfl q₃)
      (N ≫ (α_ Uj Ui R0).hom ≫ Uj ◁ (ρ_ _).inv) (Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv)
      ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Uj ◁ (ρ_ _).inv) ((Uj ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv) ≫ N')
      ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3]
  · simp only [midK, PrelaxFunctor.map₂_comp,
      lift_map₂_whiskerLeft, lift_map₂_associator_hom, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map₂_rightUnitor_inv, lift_map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    bicategory
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_single
  case hl1 => intro _ _; double_nil
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_nil
  case hl2 => intro _ _; double_single
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_single
  case hl3 => intro _ _; double_nil
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hg1 =>
    intro _ _ _ _
    exact redDownQuot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg2 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg3 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _

/-- The image of the downward braid `ψ₁ψ₀ψ₁` on `[i, r, i]`, read through free 2-morphisms. -/
theorem admissibleMap_braidR_iri (m : X) (i : I) (r : Fin ℓ)
    (ha hb : Cond m (((m + (wD i)) + Λ r) + (wD i))
      (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])))
    (f₁ : (m + (wD i)) + RD.iX i = m)
    (q : (((m + (wD i)) + Λ r) + (wD i)) + RD.iX i = (m + (wD i)) + Λ r)
    (N : fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) ha.1 ha.2.1 ⟶
      (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl)
    (N' : (fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
          (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl ≫
        fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl) ≫
        fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl ⟶
      fwT m (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])).word
        (((m + (wD i)) + Λ r) + (wD i)) ha.1 ha.2.1)
    (f₂ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i))
    (e₁ : ((m + (wD i)) + (wD i)) + Λ r = ((m + (wD i)) + Λ r) + (wD i)) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (LinDiagram.of (KLR.Diagram.braidR (Sum.inl i : I ⊕ Fin ℓ) (.inr r) (.inl i)))) =
      (doubleModel S red).lift.map₂ N ≫ (α_ (S.E i q) (red r rfl) (S.E i f₁)).hom ≫
        ((α_ _ _ _).inv ≫ redDownDot S red upIso r i f₂ e₁ rfl q ▷ S.E i f₁ ≫ (α_ _ _ _).hom ≫
        red r e₁ ◁ S.cross i i f₂ f₁ f₂ f₁ ≫ (α_ _ _ _).inv ≫
        redDownQuot S red upIso r i f₂ e₁ rfl q ▷ S.E i f₁ ≫ (α_ _ _ _).hom) ≫
        (α_ (S.E i q) (red r rfl) (S.E i f₁)).inv ≫ (doubleModel S red).lift.map₂ N' := by
  obtain ⟨D, hD, eD⟩ := downLinear_dl3 (RD := RD) (Λ := Λ) (k := k) m [.inl i] [] [] [.inr r]
    [.inl i] [] (.cross (.inr r) (.inl i)) (.cross (.inl i) (.inl i)) (.cross (.inl i) (.inr r))
    rfl rfl rfl (a := KLR.Diagram.ob [.inl i, .inr r, .inl i])
    (b := KLR.Diagram.ob [.inl i, .inl i, .inr r]) (c := KLR.Diagram.ob [.inl i, .inl i, .inr r])
    (d := KLR.Diagram.ob [.inl i, .inr r, .inl i]) rfl rfl rfl rfl rfl rfl
  erw [eD, admissibleMap_of]
  change admissibleChain _ _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk]
  simp only [List.map_cons, List.map_nil, DoubleStrand.down, List.nil_append,
    List.append_nil] at hD
  rw [admissibleChain_congr _ hD]
  let R0 := fwT m [(m, .inl (false, i))] (m + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui := fwT (m + (wD i)) [(m + (wD i), .inr r)] ((m + (wD i)) + Λ r) ⟨rfl, trivial⟩ rfl
  let Uj := fwT ((m + (wD i)) + Λ r) [((m + (wD i)) + Λ r, .inl (false, i))]
    (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ rfl
  let Ui2 := fwT ((m + (wD i)) + (wD i)) [((m + (wD i)) + (wD i), .inr r)]
    (((m + (wD i)) + Λ r) + (wD i)) ⟨rfl, trivial⟩ e₁
  let Uj2 := fwT (m + (wD i)) [(m + (wD i), .inl (false, i))] ((m + (wD i)) + (wD i))
    ⟨rfl, trivial⟩ rfl
  erw [admissibleChain₃_conj (doubleModel S red) (genImg S red upIso Sc) _ ha hb
      (p₁ := 𝟙 _) (q₁ := R0) (x₁ := Uj ≫ Ui) (y₁ := Ui2 ≫ Uj2)
      (p₂ := Ui2) (q₂ := 𝟙 _) (x₂ := Uj2 ≫ R0) (y₂ := Uj2 ≫ R0)
      (p₃ := 𝟙 _) (q₃ := R0) (x₃ := Ui2 ≫ Uj2) (y₃ := Uj ≫ Ui)
      (redDownDot S red upIso r i f₂ e₁ rfl q) (S.cross i i f₂ f₁ f₂ f₁)
      (redDownQuot S red upIso r i f₂ e₁ rfl q)
      (N ≫ (λ_ _).inv) ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ Ui2 ◁ (ρ_ _).inv)
      (Ui2 ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ((λ_ _).hom ≫ N')
      ?hn1 ?hm1 ?hr1 ?hl1 ?hd1 ?he1 ?hg1 ?hn2 ?hm2 ?hr2 ?hl2 ?hd2 ?he2 ?hg2
      ?hn3 ?hm3 ?hr3 ?hl3 ?hd3 ?he3 ?hg3]
  · simp only [midK, PrelaxFunctor.map₂_comp,
      lift_map₂_whiskerLeft, lift_map₂_associator_hom, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map₂_rightUnitor_inv, lift_map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    bicategory
  case hn1 => double_regions
  case hm1 => double_regions
  case hr1 => intro _ _; double_nil
  case hl1 => intro _ _; double_single
  case hd1 => intro _ _; double_pair
  case he1 => intro _ _; double_pair
  case hn2 => double_regions
  case hm2 => double_regions
  case hr2 => intro _ _; double_single
  case hl2 => intro _ _; double_nil
  case hd2 => intro _ _; double_pair
  case he2 => intro _ _; double_pair
  case hn3 => double_regions
  case hm3 => double_regions
  case hr3 => intro _ _; double_nil
  case hl3 => intro _ _; double_single
  case hd3 => intro _ _; double_pair
  case he3 => intro _ _; double_pair
  case hg1 =>
    intro _ _ _ _
    exact redDownDot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _
  case hg2 =>
    intro _ _ _ _
    refine (heq_of_eq (genImg_blackOn S red upIso Sc _ _ _ _ _ _ _ _ _ _)).trans ?_
    exact cross_dn_heq S red Sc _ i i _ _ _ _ _ _ (by double_regions) (by double_regions) _ _ _ _
  case hg3 =>
    intro _ _ _ _
    exact redDownQuot_heq S red upIso r _ (by double_regions) (by double_regions)
      (by double_regions) (by double_regions) _ _ _ _ _ _ _ _

/-- **The downward braid `[i, r, i]`** with its correction term is killed by the generator
images, for the polynomial `Q_{i r}(u, v) = u^{n}` of the bigon (4.2). -/
theorem admissibleMap_braidQ_iri (n : Fin ℓ → I → ℕ) (hn : DownMidSame S red upIso n)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (i : I) (r : Fin ℓ)
    (hQ : Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i) (m : X) {x y : X}
    (ha : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i])))
    (hb : Cond x y (downContextObj RD Λ m [] [] (KLR.Diagram.ob [.inl i, .inr r, .inl i]))) :
    admissibleMap (genImg S red upIso Sc) ha hb (downLinear RD Λ k m [] []
      (KLR.Diagram.relation k Q (.braidQ (.inl i) (.inr r) Sum.inl_ne_inr))) = 0 := by
  obtain rfl : m = x := ha.2.2
  obtain rfl : ((m + (wD i)) + Λ r) + (wD i) = y := ha.2.1
  have f₁ : (m + (wD i)) + RD.iX i = m := by double_regions
  have f₂ : ((m + (wD i)) + (wD i)) + RD.iX i = m + (wD i) := by double_regions
  have e₁ : ((m + (wD i)) + (wD i)) + Λ r = ((m + (wD i)) + Λ r) + (wD i) := by
    double_regions
  have q : (((m + (wD i)) + Λ r) + (wD i)) + RD.iX i = (m + (wD i)) + Λ r := by double_regions
  have q₃ : ((m + (wD i)) + Λ r) + RD.iX i = m + Λ r := by double_regions
  rw [relation_braidQ, map_sub, map_sub, map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add']
  erw [admissibleMap_braidL_iri Sc m i r ha hb f₁ q (𝟙 _) (𝟙 _) q₃,
    admissibleMap_braidR_iri Sc m i r ha hb f₁ q (𝟙 _) (𝟙 _) f₂ e₁]
  change _ = _ + downEndAlg (genImg S red upIso Sc) m [.inl i, .inr r, .inl i] ha _
  rw [KLR.Diagram.lpoly, AlgHom.map_ncEval, hQ, StendhalAlgebraAllOrders.qbar_X_zero_pow,
    ncEval_finset_sum]
  simp only [ncEval_X_zero_pow_mul_X_two_pow]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [downEndAlg_E0_iri S red upIso Sc m i r ha f₁ q (𝟙 _) (𝟙 _),
    downEndAlg_E2_iri S red upIso Sc m i r ha f₁ q (𝟙 _) (𝟙 _)]
  simp only [PrelaxFunctor.map₂_id, Category.id_comp]
  erw [Category.comp_id, Category.comp_id, hn r i f₁ f₂ rfl e₁ q rfl q₃]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Iso.hom_inv_id,
    Iso.hom_inv_id_assoc, Category.comp_id]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  exact (Category.comp_id _).symm

end Categorification.Stendhal.DoubleDiagram
