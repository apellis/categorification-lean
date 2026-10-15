import Categorification.TwoRep.RouqMixedSource
import Categorification.Diagrams.CL.Brundan

/-!
# The nonpositive mixed cap pitchfork

Brundan, arXiv:1501.00350v1, Lemma 5.2 (5.2), for `h ≤ 0` and `h < dᵢⱼ`.
The crossing and caps are the actual `RouqFamily` maps, not morphisms of a
presented diagram category. We evaluate both components of the nonpositive
inversion map. The capped braid correction and dotted double crossing are
computed for the unrestricted rectangular polynomial `brundanQ`; the lower
terms vanish by the bubble bounds, without coefficient homogeneity.

`capTurn_nonpos` does not require mixed invertibility. The final pitchfork
uses `IsIso (S.mixedSigma ...)`, precisely the distinct-colour defining
inversion relation (1.7), independently of the relation being proved.
Horizontal composition is explicitly `k`-linear. No grading, field,
finite-dimensionality, or assumption on endomorphisms of the identity is used.
The positive-weight cases and all-weight mixed cyclicity are not asserted.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD)

omit [AdditiveWhiskering B] in
theorem mixedSigma_self (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    S.mixedSigma i i h₁ h₂ h₁ h₂ = (S.loc i h₁ h₂).sig := by
  exact (RightwardCrossing.sigma_eq_mateEquiv (S.adj i h₁) (S.adj i h₂) _).symm

theorem adjL_counit (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    (S.adjL i h₂).counit = (S.loc i h₁ h₂).capL := by
  rw [S.adjL_eq i h₁ h₂ rfl]
  rfl

def capTurn (i j : I) {a b c d : X} (hj : a + RD.iX j = b)
    (hi' : b + RD.iX i = d) (hi : a + RD.iX i = c)
    (hj' : c + RD.iX j = d) :
    (S.E i hi ≫ S.F i hi) ≫ S.E j hj ⟶ S.E j hj :=
  (α_ (S.E i hi) (S.F i hi) (S.E j hj)).hom ≫
    S.E i hi ◁ S.mixedSigma i j hj hi' hi hj' ≫
    (α_ (S.E i hi) (S.E j hj') (S.F i hi')).inv ≫
    S.cross j i hi hj' hj hi' ▷ S.F i hi' ≫
    (α_ (S.E j hj) (S.E i hi') (S.F i hi')).hom ≫
    S.E j hj ◁ (S.adjL i hi').counit ≫ (ρ_ (S.E j hj)).hom

end RouqFamily

section Ext
variable {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

theorem RouqLoc.nonpos_whisker_ext (hh : h ≤ 0) {d : B} (J : b ⟶ d)
    {T : b ⟶ d} (f g : (E₂ ≫ R₂) ≫ J ⟶ T)
    (hf : L.sig ▷ J ≫ f = L.sig ▷ J ≫ g)
    (hg : ∀ n : ℕ, n < (-h).toNat → L.cupD n ▷ J ≫ f = L.cupD n ▷ J ≫ g) :
    f = g := by
  have hs : (∑ n ∈ Finset.range (-h).toNat, (L.iN hh).g' n ≫ L.cupD n) ▷ J =
      ∑ n ∈ Finset.range (-h).toNat, ((L.iN hh).g' n ≫ L.cupD n) ▷ J :=
    map_sum (AdditiveWhiskering.whiskerRightAddHom _ _ J) _ _
  have H := congrArg (fun z => z ▷ J) (L.iN hh).total
  simp only [AdditiveWhiskering.add_whiskerRight, hs,
    comp_whiskerRight, id_whiskerRight] at H
  calc
    f = ((L.iN hh).f' ▷ J ≫ L.sig ▷ J +
      ∑ n ∈ Finset.range (-h).toNat, (L.iN hh).g' n ▷ J ≫ L.cupD n ▷ J) ≫ f := by rw [H, Category.id_comp]
    _ = ((L.iN hh).f' ▷ J ≫ L.sig ▷ J +
      ∑ n ∈ Finset.range (-h).toNat, (L.iN hh).g' n ▷ J ≫ L.cupD n ▷ J) ≫ g := by
      simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc]
      rw [hf]
      congr 1
      exact Finset.sum_congr rfl fun n hn => by rw [hg n (Finset.mem_range.mp hn)]
    _ = g := by rw [H, Category.id_comp]
end Ext

section Contraction
variable {a b c d : B} {E : a ⟶ b} {R : b ⟶ a} {F : c ⟶ d} {T : d ⟶ c}
  (A : E ⊣ R) (D : F ⊣ T) (J : b ⟶ c)

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem mate_associator :
    mateEquiv A D (α_ E J F).hom =
      (α_ R E J).inv ≫ A.counit ▷ J ≫ (λ_ J).hom ≫
      (ρ_ J).inv ≫ J ◁ D.unit ≫ (α_ J F T).inv := by
  rw [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ (((R ≫ E) ≫ J) ◁ D.unit ≫
      (A.counit ▷ J) ▷ (F ≫ T)) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem mate_monomial_cap (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cap : F ≫ T ⟶ 𝟙 c) :
    mateEquiv A D ((α_ E J F).hom ≫ x ▷ (J ≫ F) ≫
      E ◁ (y ▷ F) ≫ E ◁ (J ◁ z)) ≫
      (α_ J F T).hom ≫ J ◁ cap ≫ (ρ_ J).hom =
    (α_ R E J).inv ≫ (R ◁ x ≫ A.counit) ▷ J ≫ (λ_ J).hom ≫
      y ≫ (ρ_ J).inv ≫ J ◁ (D.unit ≫ z ▷ T ≫ cap) ≫ (ρ_ J).hom := by
  have hx : (α_ E J F).hom ≫ x ▷ (J ≫ F) ≫ E ◁ (y ▷ F) ≫ E ◁ (J ◁ z) =
      (x ▷ J) ▷ F ≫ (α_ E J F).hom ≫ E ◁ (y ▷ F ≫ J ◁ z) := by bicategory
  rw [hx, rightMate_pre, rightMate_post, mate_associator]
  calc
    _ = 𝟙 _ ⊗≫ (R ◁ x ≫ A.counit) ▷ J ⊗≫
      (J ◁ D.unit ≫ y ▷ (F ≫ T)) ⊗≫ J ◁ (z ▷ T ≫ cap) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory
end Contraction

section Polynomial
variable {a b c d : B} {E : a ⟶ b} {R : b ⟶ a} {F : c ⟶ d} {T : d ⟶ c}
  (A : E ⊣ R) (D : F ⊣ T) (J : b ⟶ c)

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem source_whiskerLeft_smul {a b c : B} (E : a ⟶ b) {f g : b ⟶ c}
    (s : k) (x : f ⟶ g) : E ◁ (s • x) = s • (E ◁ x) :=
  (precomp c E).map_smul s x

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem source_smul_whiskerRight {a b c : B} {f g : a ⟶ b}
    (s : k) (x : f ⟶ g) (F : b ⟶ c) : (s • x) ▷ F = s • (x ▷ F) :=
  (postcomp a F).map_smul s x

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem powComp_eq_end_pow {a b : B} {E : a ⟶ b} (x : E ⟶ E) (n : ℕ) :
    powComp x n = End.asHom (End.of x ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powComp_succ, ih, pow_succ']; rfl

theorem source_mate_add (f g : (E ≫ J) ≫ F ⟶ E ≫ (J ≫ F)) :
    mateEquiv A D (f + g) = mateEquiv A D f + mateEquiv A D g := by
  simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply, AdditiveWhiskering.add_whiskerRight,
    AdditiveWhiskering.whiskerLeft_add, Preadditive.comp_add, Preadditive.add_comp]

omit [AdditiveWhiskering B] in
theorem source_mate_smul (s : k) (f : (E ≫ J) ≫ F ⟶ E ≫ (J ≫ F)) :
    mateEquiv A D (s • f) = s • mateEquiv A D f := by
  simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
    Adjunction.homEquiv₂_apply, source_smul_whiskerRight,
    source_whiskerLeft_smul, Linear.comp_smul, Linear.smul_comp]

def capEval (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cap : F ≫ T ⟶ 𝟙 c) : MvPolynomial (Fin 3) k →ₗ[k] (R ≫ (E ≫ J) ⟶ J) where
  toFun p := mateEquiv A D ((α_ E J F).hom ≫
    KLR.ncEval (A := End (E ≫ (J ≫ F)))
      ![E ◁ (J ◁ z), E ◁ (y ▷ F), x ▷ (J ≫ F)] p) ≫
    (α_ J F T).hom ≫ J ◁ cap ≫ (ρ_ J).hom
  map_add' p q := by
    rw [CL.ncEvalB_add]
    change mateEquiv A D ((α_ E J F).hom ≫ (_ + _)) ≫ _ = _
    rw [Preadditive.comp_add, source_mate_add, Preadditive.add_comp]
  map_smul' s p := by
    rw [MvPolynomial.smul_eq_C_mul, CL.ncEval_C_mul', ← Algebra.smul_def]
    change mateEquiv A D ((α_ E J F).hom ≫ (s • _)) ≫ _ = _
    rw [Linear.comp_smul, source_mate_smul, Linear.smul_comp]
    rfl

theorem capEval_X3 (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cap : F ≫ T ⟶ 𝟙 c) (r q s : ℕ) :
    capEval (k := k) A D J x y z cap
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
      (α_ R E J).inv ≫ (R ◁ powComp x s ≫ A.counit) ▷ J ≫ (λ_ J).hom ≫
        powComp y q ≫ (ρ_ J).inv ≫
        J ◁ (D.unit ≫ powComp z r ▷ T ≫ cap) ≫ (ρ_ J).hom := by
  change mateEquiv A D ((α_ E J F).hom ≫ _) ≫ _ = _
  rw [CL.ncEval_X3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, End.mul_def,
    ← powComp_eq_end_pow, ← whiskerLeft_powComp, ← powComp_whiskerRight]
  exact mate_monomial_cap A D J (powComp x s) (powComp y q) (powComp z r) cap
end Polynomial

section Correction
variable {a b c d e : B} {E : a ⟶ b} {R : b ⟶ a} {F : c ⟶ d} {T : d ⟶ c}
  {G : e ⟶ c} {U : c ⟶ e} (A : E ⊣ R) {D : F ⊣ T} {D₀ : G ⊣ U}
  (J : b ⟶ c) (x : E ⟶ E) (y : J ⟶ J) {z : F ⟶ F} {w : G ⟶ G}
  {τ : G ≫ F ⟶ G ≫ F} {v : ℤ} (L : RouqLoc D₀ D w z τ v)

theorem capEval_X3_low (hv : v < 0) (r q s : ℕ) (hr : r < (-v).toNat) :
    capEval (k := k) A D J x y z L.capL
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
    if r = (-v-1).toNat then
      (α_ R E J).inv ≫ (R ◁ powComp x s ≫ A.counit) ▷ J ≫
        (λ_ J).hom ≫ powComp y q else 0 := by
  rw [capEval_X3]
  have hb : D.unit ≫ powComp z r ▷ T ≫ L.capL =
      if r = (-v-1).toNat then 𝟙 _ else 0 := by
    simpa only [RouqLoc.cupD, Category.assoc] using L.cupD_capL hv hr
  rw [hb]
  split_ifs <;> simp [AdditiveWhiskering.whiskerLeft_zero]

variable {I : Type*} {C : CartanDatum I} (P : CL.CLScalars C k) {i j : I}

/-- The capped divided difference: only the leading coefficient can survive.
The unrestricted rectangular terms vanish because their first exponents are smaller. -/
theorem capEval_brundan (hij : i ≠ j) (h : ℤ) (hh : h ≤ 0)
    (hd : h < C.dij i j) (hv : v = h - C.dij i j) :
    capEval A D J x y z L.capL (KLR.qbar (brundanQ P i j)) =
      if h = 0 then (P.t i j : k) •
        ((α_ R E J).inv ≫ A.counit ▷ J ≫ (λ_ J).hom) else 0 := by
  classical
  have hvneg : v < 0 := by omega
  by_cases hd0 : C.dot i j = 0
  · have hdij : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 hd0
    have hh0 : h ≠ 0 := by omega
    rw [brundanQ, ite_eq_left hd0, CL.qbar_C, map_zero, ite_eq_right hh0]
  have hdpos := C.dij_pos hij hd0
  let Ψ := capEval (k := k) A D J x y z L.capL
  change Ψ _ = _
  rw [brundanQ_qbar P hd0, map_add, MvPolynomial.C_mul', map_smul]
  simp only [map_sum]
  have hs : (∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      Ψ (MvPolynomial.C (P.s i j p q) * MvPolynomial.X 1 ^ q *
        ∑ r ∈ Finset.range p, MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (p-1-r))) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q _
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro r hr
    have he : (MvPolynomial.C (P.s i j p q) * MvPolynomial.X 1 ^ q *
        (MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (p-1-r)) : MvPolynomial (Fin 3) k) =
        (P.s i j p q) • (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q *
          MvPolynomial.X 2 ^ (p-1-r)) := by rw [MvPolynomial.smul_eq_C_mul]; ring
    rw [he, map_smul]
    have hp' := Finset.mem_range.mp hp
    have hr' := Finset.mem_range.mp hr
    have hz := capEval_X3_low (k := k) A J x y L hvneg r q (p-1-r) (by omega)
    rw [ite_eq_right (by omega)] at hz
    change P.s i j p q • capEval A D J x y z L.capL _ = 0
    rw [hz, smul_zero]
  rw [hs, add_zero]
  have he (r : ℕ) : (MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (C.dij i j-1-r) :
      MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ (C.dij i j-1-r) := by simp
  simp_rw [he]
  by_cases h0 : h = 0
  · rw [ite_eq_left h0, Finset.sum_eq_single (C.dij i j-1)]
    · have hlow := capEval_X3_low (k := k) A J x y L hvneg
        (C.dij i j-1) 0 (C.dij i j-1-(C.dij i j-1)) (by omega)
      rw [ite_eq_left (by omega)] at hlow
      simpa only [Ψ, hlow, Nat.sub_self, powComp_zero, whiskerLeft_id,
        Category.id_comp, Category.comp_id] using congrArg ((P.t i j : k) • ·) hlow
    · intro r hr hne
      have hr' := Finset.mem_range.mp hr
      change capEval A D J x y z L.capL _ = 0
      rw [capEval_X3_low A J x y L hvneg r 0 _ (by omega), ite_eq_right (by omega)]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right h0]
    have hz : (∑ r ∈ Finset.range (C.dij i j),
        Ψ (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ 0 *
          MvPolynomial.X 2 ^ (C.dij i j-1-r))) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr' := Finset.mem_range.mp hr
      change capEval A D J x y z L.capL _ = 0
      rw [capEval_X3_low A J x y L hvneg r 0 _ (by omega), ite_eq_right (by omega)]
    rw [hz, smul_zero]
end Correction

section CupPolynomial
variable {b c d : B} {F : c ⟶ d} {T : d ⟶ c} (D : F ⊣ T)
  (J : b ⟶ c) (y : J ⟶ J) (z : F ⟶ F) (cap : F ≫ T ⟶ 𝟙 c)

def cupEval (n : ℕ) : MvPolynomial (Fin 2) k →ₗ[k] (J ⟶ J) where
  toFun p := (ρ_ J).inv ≫ J ◁ D.unit ≫ (α_ J F T).inv ≫
    (KLR.ncEval (A := End (J ≫ F)) ![J ◁ z, y ▷ F] p) ▷ T ≫
    (α_ J F T).hom ≫ J ◁ (powComp z n ▷ T ≫ cap) ≫ (ρ_ J).hom
  map_add' p q := by
    rw [CL.ncEvalB_add]
    change _ ≫ _ ≫ _ ≫ ((_ : J ≫ F ⟶ J ≫ F) + (_ : J ≫ F ⟶ J ≫ F)) ▷ T ≫ _ = _
    simp only [AdditiveWhiskering.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' s p := by
    rw [MvPolynomial.smul_eq_C_mul, CL.ncEval_C_mul', ← Algebra.smul_def]
    change _ ≫ _ ≫ _ ≫ (s • (_ : J ≫ F ⟶ J ≫ F)) ▷ T ≫ _ = _
    simp only [source_smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem cupEval_X2 (n p q : ℕ) :
    cupEval (k := k) D J y z cap n (MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
    powComp y q ≫ (ρ_ J).inv ≫ J ◁ (D.unit ≫ powComp z (p+n) ▷ T ≫ cap) ≫ (ρ_ J).hom := by
  change _ ≫ _ ≫ _ ≫ (KLR.ncEval (A := End (J ≫ F)) _ _) ▷ T ≫ _ = _
  rw [CL.ncEval_X2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, End.mul_def,
    ← powComp_eq_end_pow, ← whiskerLeft_powComp, ← powComp_whiskerRight]
  calc
    _ = 𝟙 _ ⊗≫ (J ◁ D.unit ≫ powComp y q ▷ (F ≫ T)) ⊗≫
      J ◁ (powComp z p ▷ T ≫ powComp z n ▷ T ≫ cap) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by
      rw [whisker_exchange, ← comp_whiskerRight_assoc, powComp_comp_powComp]
      bicategory
end CupPolynomial

section CupEvaluation
variable {b c d e : B} {F : c ⟶ d} {T : d ⟶ c} {G : e ⟶ c} {U : c ⟶ e}
  {D : F ⊣ T} {D₀ : G ⊣ U} (J : b ⟶ c) (y : J ⟶ J)
  {z : F ⟶ F} {w : G ⟶ G} {τ : G ≫ F ⟶ G ≫ F} {v : ℤ}
  (L : RouqLoc D₀ D w z τ v)

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem cupEval_X2_low (hv : v < 0) (n p q : ℕ) (hp : p+n < (-v).toNat) :
    cupEval (k := k) D J y z L.capL n (MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
      if p+n = (-v-1).toNat then powComp y q else 0 := by
  rw [cupEval_X2]
  have hb : D.unit ≫ powComp z (p+n) ▷ T ≫ L.capL =
      if p+n = (-v-1).toNat then 𝟙 _ else 0 := by
    simpa only [RouqLoc.cupD, Category.assoc] using L.cupD_capL hv hp
  rw [hb]
  split_ifs <;> simp [AdditiveWhiskering.whiskerLeft_zero]

variable {I : Type*} {C : CartanDatum I} (P : CL.CLScalars C k) {i j : I}
omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
/-- The dotted double crossing at a nonpositive inversion component.
The surviving term has coefficient `tᵢⱼ`, including the disconnected case. -/
theorem cupEval_brundan (hij : i ≠ j) (h : ℤ) (hv : v = h - C.dij i j)
    (n : ℕ) (hn : (n : ℤ) < -h) :
    cupEval D J y z L.capL n (brundanQ P i j) =
      (P.t i j : k) • (if n = (-h-1).toNat then 𝟙 J else 0) := by
  classical
  have hvneg : v < 0 := by omega
  let Ψ := cupEval (k := k) D J y z L.capL n
  have he (s : k) (p q : ℕ) (hp : p ≤ C.dij i j) :
      Ψ (MvPolynomial.C s * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
        s • (if p+n = (-v-1).toNat then powComp y q else 0) := by
    rw [mul_assoc, MvPolynomial.C_mul', map_smul]
    change s • cupEval D J y z L.capL n _ = _
    rw [cupEval_X2_low J y L hvneg n p q (by omega)]
  change Ψ _ = _
  by_cases hd0 : C.dot i j = 0
  · have hdij : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 hd0
    rw [brundanQ, ite_eq_left hd0]
    have hconst : (MvPolynomial.C (P.t i j : k) : MvPolynomial (Fin 2) k) =
        MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 0 := by simp
    rw [hconst, he _ 0 0 (by omega)]
    simp only [zero_add, powComp_zero, show v = h by omega]
  have hdpos := C.dij_pos hij hd0
  rw [brundanQ, ite_eq_right hd0, map_add, map_add]
  have hX : (MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ C.dij i j : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ C.dij i j * MvPolynomial.X 1 ^ 0 := by simp
  have hY : (MvPolynomial.C (P.t j i : k) * MvPolynomial.X 1 ^ C.dij j i : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t j i : k) * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ C.dij j i := by simp
  rw [hX, hY, he _ _ _ le_rfl, he _ _ _ (by omega), ite_eq_right (show ¬ 0+n = (-v-1).toNat by omega), smul_zero, add_zero]
  have hrect : Ψ (∑ p ∈ Finset.range (C.dij i j), ∑ q ∈ Finset.range (C.dij j i),
      MvPolynomial.C (P.s i j p q) * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) = 0 := by
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q _
    have hp' := Finset.mem_range.mp hp
    rw [he _ p q (by omega), ite_eq_right (by omega), smul_zero]
  rw [hrect, add_zero, powComp_zero]
  have hiff : C.dij i j+n = (-v-1).toNat ↔ n = (-h-1).toNat := by omega
  simp only [hiff]
end CupEvaluation

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD)

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem powComp_slide {a b : B} {E F : a ⟶ b} (x : E ⟶ E) (y : F ⟶ F)
    (t : E ⟶ F) (ht : x ≫ t = t ≫ y) (n : ℕ) :
    powComp x n ≫ t = t ≫ powComp y n := by
  induction n with
  | zero => simp [powComp_zero]
  | succ n ih => rw [powComp_succ, powComp_succ, Category.assoc, ht, ← Category.assoc, ih, Category.assoc]

theorem capTurn_dot (i j : I) {a b c d : X} (hj : a + RD.iX j = b)
    (hi' : b + RD.iX i = d) (hi : a + RD.iX i = c) (hj' : c + RD.iX j = d)
    (x : S.E i hi ⟶ S.E i hi) (z : S.E i hi' ⟶ S.E i hi')
    (hs : x ▷ S.E j hj' ≫ S.cross j i hi hj' hj hi' =
      S.cross j i hi hj' hj hi' ≫ S.E j hj ◁ z) :
    (x ▷ S.F i hi) ▷ S.E j hj ≫ S.capTurn i j hj hi' hi hj' =
    (α_ (S.E i hi) (S.F i hi) (S.E j hj)).hom ≫
      S.E i hi ◁ S.mixedSigma i j hj hi' hi hj' ≫
      (α_ (S.E i hi) (S.E j hj') (S.F i hi')).inv ≫
      S.cross j i hi hj' hj hi' ▷ S.F i hi' ≫
      (α_ (S.E j hj) (S.E i hi') (S.F i hi')).hom ≫
      S.E j hj ◁ (z ▷ S.F i hi' ≫ (S.adjL i hi').counit) ≫ (ρ_ (S.E j hj)).hom := by
  unfold capTurn
  calc
    _ = 𝟙 _ ⊗≫ (x ▷ (S.F i hi ≫ S.E j hj) ≫
      S.E i hi ◁ S.mixedSigma i j hj hi' hi hj') ⊗≫
      S.cross j i hi hj' hj hi' ▷ S.F i hi' ⊗≫
      S.E j hj ◁ (S.adjL i hi').counit ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ S.E i hi ◁ S.mixedSigma i j hj hi' hi hj' ⊗≫
      (x ▷ S.E j hj' ≫ S.cross j i hi hj' hj hi') ▷ S.F i hi' ⊗≫
      S.E j hj ◁ (S.adjL i hi').counit ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = _ := by rw [hs]; bicategory

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem capTurn_cup {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Q) (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₇ : e + RD.iX i = c) (n : ℕ) :
    (λ_ (S.E j h₂)).inv ≫ (S.loc i h₁ h₄).cupD n ▷ S.E j h₂ ≫ S.capTurn i j h₂ h₃ h₄ h₅ =
    cupEval (S.adj i h₃) (S.E j h₂) (S.dot j h₂) (S.dot i h₃)
      (S.loc i h₇ h₃).capL n (Q i j) := by
  have hs : powComp (S.dot i h₄) n ▷ S.E j h₅ ≫ S.cross j i h₄ h₅ h₂ h₃ =
      S.cross j i h₄ h₅ h₂ h₃ ≫ S.E j h₂ ◁ powComp (S.dot i h₃) n := by
    simpa only [← powComp_whiskerRight, ← whiskerLeft_powComp] using
      powComp_slide _ _ _ (H.slide_right j i hij.symm h₄ h₅ h₂ h₃) n
  simp only [RouqLoc.cupD, comp_whiskerRight, Category.assoc]
  rw [S.capTurn_dot i j h₂ h₃ h₄ h₅ _ _ hs]
  rw [← Category.assoc _ _ ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫ _),
    ← Category.assoc _ _ ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫ _),
    ← Category.assoc _ _ ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫ _)]
  rw [S.mixedSigma_cup]
  change _ = cupEval _ _ _ _ _ _ _
  simp only [cupEval, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← H.square i j hij h₂ h₃ h₄ h₅]
  rw [S.adjL_counit i h₇ h₃]
  bicategory

theorem capTurn_sig {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Q) (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hc : RD.pair (RD.iY i) c < 0) :
    (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).inv ≫
      (S.loc i h₁ h₄).sig ▷ S.E j h₂ ≫ S.capTurn i j h₂ h₃ h₄ h₅ =
    capEval (S.adj i h₁) (S.adj i h₃) (S.E j h₂)
      (S.dot i h₁) (S.dot j h₂) (S.dot i h₃) (S.loc i h₇ h₃).capL (KLR.qbar (Q i j)) := by
  have hb := congrArg (fun z => z ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom ≫
      S.E j h₂ ◁ (S.loc i h₇ h₃).capL ≫ (ρ_ (S.E j h₂)).hom)
    (S.mixedSigma_braidQ H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
  rw [Preadditive.sub_comp] at hb
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hb
  rw [← whiskerLeft_comp_assoc, S.mixedSigma_self i h₇ h₃, (S.loc i h₇ h₃).sig_capL hc,
    AdditiveWhiskering.whiskerLeft_zero] at hb
  simp only [Limits.zero_comp, Limits.comp_zero, sub_zero] at hb
  simpa only [capTurn, S.adjL_counit i h₇ h₃, S.mixedSigma_self, capEval,
    LinearMap.coe_mk, AddHom.coe_mk, Category.assoc] using hb

theorem pair_step_ne (i j : I) (hij : i ≠ j) {a b : X} (hj : a + RD.iX j = b) :
    RD.pair (RD.iY i) b = RD.pair (RD.iY i) a - C.dij i j := by
  rw [← hj, map_add]
  have hp : RD.pair (RD.iY i) (RD.iX j) = -(C.dij i j : ℤ) := CL.ip_iX_ne hij
  rw [hp, sub_eq_add_neg]

/-- The scalar cap-turn relation before cancelling the mixed crossing,
proved on both components of the actual nonpositive inversion isomorphism. -/
theorem capTurn_nonpos (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hh : RD.pair (RD.iY i) b ≤ 0) (hd : RD.pair (RD.iY i) b < C.dij i j) :
    S.capTurn i j h₂ h₃ h₄ h₅ =
      (P.t i j : k) • ((S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  classical
  have hw := pair_step_ne i j hij h₂
  have hc : RD.pair (RD.iY i) c < 0 := by omega
  rw [S.adjL_counit i h₁ h₄]
  apply (S.loc i h₁ h₄).nonpos_whisker_ext hh
  · apply (cancel_epi (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).inv).mp
    rw [S.capTurn_sig H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hc,
      capEval_brundan _ _ _ _ _ P hij _ hh hd hw]
    have hs := (S.loc i h₁ h₄).sig_powComp_capL_of_le (n := 0) (by omega)
    simp only [powComp_zero, id_whiskerRight, Category.id_comp] at hs
    simp only [Linear.comp_smul, ← comp_whiskerRight_assoc]
    rw [hs]
    by_cases hz : RD.pair (RD.iY i) b = 0
    · simp [hz]
    · simp [hz, AdditiveWhiskering.zero_whiskerRight]
  · intro n hn
    apply (cancel_epi (λ_ (S.E j h₂)).inv).mp
    rw [S.capTurn_cup H i j hij h₁ h₂ h₃ h₄ h₅ h₇ n,
      cupEval_brundan _ _ _ P hij _ hw n (by omega)]
    simp only [Linear.comp_smul, ← comp_whiskerRight_assoc]
    rw [(S.loc i h₁ h₄).cupD_capL (by omega) hn]
    split_ifs <;> simp [AdditiveWhiskering.zero_whiskerRight]

theorem mixedCap_pitchfork_nonpos_of_steps (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₂ h₃ h₄ h₅)]
    (hh : RD.pair (RD.iY i) b ≤ 0) (hd : RD.pair (RD.iY i) b < C.dij i j) :
    S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom ≫
      S.E j h₂ ◁ (S.adjL i h₃).counit ≫ (ρ_ (S.E j h₂)).hom =
    (P.t i j : k) • ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).hom ≫
      S.E i h₄ ◁ inv (S.mixedSigma i j h₂ h₃ h₄ h₅) ≫
      (α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).inv ≫
      (S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  apply (cancel_epi ((α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).hom ≫
    S.E i h₄ ◁ S.mixedSigma i j h₂ h₃ h₄ h₅ ≫
    (α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv)).mp
  simp only [Linear.comp_smul, Category.assoc, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, IsIso.hom_inv_id, whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id_assoc]
  exact S.capTurn_nonpos P H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hh hd
/-- Brundan Lemma 5.2 (5.2) in the nonpositive band.
The only additional invertibility assumption is the original relation (1.7)
for the actual distinct-colour mate. The strict second bound excludes the
disconnected weight-zero boundary; the scalar is `tᵢⱼ`, not `tⱼᵢ`. -/
theorem mixedCap_pitchfork_nonpos (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {b c d f : X}
    (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    [IsIso (S.mixedSigma i j h₂ h₃ h₄ h₅)]
    (hh : RD.pair (RD.iY i) b ≤ 0) (hd : RD.pair (RD.iY i) b < C.dij i j) :
    S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom ≫
      S.E j h₂ ◁ (S.adjL i h₃).counit ≫ (ρ_ (S.E j h₂)).hom =
    (P.t i j : k) • ((α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).hom ≫
      S.E i h₄ ◁ inv (S.mixedSigma i j h₂ h₃ h₄ h₅) ≫
      (α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).inv ≫
      (S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  exact S.mixedCap_pitchfork_nonpos_of_steps P H i j hij
    (sub_add_cancel b (RD.iX i)) h₂ h₃ h₄ h₅
    (show b - RD.iX i + RD.iX j = c - RD.iX i by rw [← h₂]; abel)
    (sub_add_cancel c (RD.iX i)) hh hd
end RouqFamily

end Categorification.TwoRep
