import Categorification.TwoRep.RouqMixedPositive

/-!
# Brundan's upper-weight mixed cup pitchfork

`RouqFamily.mixedCup_pitchfork_of_ge` proves Lemma 5.2 (5.3) of Brundan,
*On the definition of Kac–Moody 2-category*, for `h ≥ dᵢⱼ`. Together with
`mixedCap_pitchfork_of_lt`, this supplies both weight ranges of Lemma 5.2.

The codomain is `Fᵢ ≫ (Eⱼ ≫ Eᵢ)`, not the cap equation with a changed inequality.
Both cups are the actual units of `RouqFamily.adjL`, and the coefficient is `tᵢⱼ`.
The proof postcomposes with the positive inversion at weight `h - dᵢⱼ`: its
crossing component is the mated braid correction and its remaining components
are the dotted caps indexed by `0 ≤ n < h - dᵢⱼ`. At equality there are no cap
components. The disconnected case `h = dᵢⱼ = 0` uses the constant square relation.

The parameters are the unrestricted rectangular `BrundanUpKLR` parameters over
a commutative ring, with linear hom categories and linear whiskering. No grading,
field, dimension, integrability, or extra nilpotence hypothesis is used. This is
not an all-weight CL cyclicity theorem or a verification of `presNM`.
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

section Ext
variable {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- The positive inversion components remain jointly monic after left whiskering. -/
theorem RouqLoc.nonneg_whisker_ext (hh : 0 ≤ h) {d : B} (J : d ⟶ b)
    {T : d ⟶ b} (f g : T ⟶ J ≫ (R₁ ≫ E₁))
    (hf : f ≫ J ◁ L.sig = g ≫ J ◁ L.sig)
    (hg : ∀ n : ℕ, n < h.toNat → f ≫ J ◁ L.capD n = g ≫ J ◁ L.capD n) :
    f = g := by
  have hs : J ◁ (∑ n ∈ Finset.range h.toNat, L.capD n ≫ (L.ip hh).g' n) =
      ∑ n ∈ Finset.range h.toNat, J ◁ (L.capD n ≫ (L.ip hh).g' n) :=
    map_sum (AdditiveWhiskering.whiskerLeftAddHom J _ _) _ _
  have H := congrArg (fun z => J ◁ z) (L.ip hh).total
  simp only [AdditiveWhiskering.whiskerLeft_add, hs, whiskerLeft_comp, whiskerLeft_id] at H
  calc
    f = f ≫ (J ◁ L.sig ≫ J ◁ (L.ip hh).f' +
      ∑ n ∈ Finset.range h.toNat, J ◁ L.capD n ≫ J ◁ (L.ip hh).g' n) := by rw [H, Category.comp_id]
    _ = g ≫ (J ◁ L.sig ≫ J ◁ (L.ip hh).f' +
      ∑ n ∈ Finset.range h.toNat, J ◁ L.capD n ≫ J ◁ (L.ip hh).g' n) := by
      simp only [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc]
      rw [hf]
      congr 1
      exact Finset.sum_congr rfl fun n hn => by rw [hg n (Finset.mem_range.mp hn)]
    _ = g := by rw [H, Category.comp_id]
end Ext

section Polynomial
variable {a b c d : B} {E : a ⟶ b} {R : b ⟶ a} {F : c ⟶ d} {T : d ⟶ c}
  (A : E ⊣ R) (D : F ⊣ T) (J : b ⟶ c)

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
/-- Contract a polynomial monomial after taking the two outer right mates. -/
theorem mate_monomial_cup (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cup : 𝟙 b ⟶ R ≫ E) :
    (λ_ J).inv ≫ cup ▷ J ≫ (α_ R E J).hom ≫
      mateEquiv A D ((α_ E J F).hom ≫ x ▷ (J ≫ F) ≫
        E ◁ (y ▷ F) ≫ E ◁ (J ◁ z)) ≫ (α_ J F T).hom =
    (λ_ J).inv ≫ (cup ≫ R ◁ x ≫ A.counit) ▷ J ≫ (λ_ J).hom ≫
      y ≫ (ρ_ J).inv ≫ J ◁ (D.unit ≫ z ▷ T) := by
  have hx : (α_ E J F).hom ≫ x ▷ (J ≫ F) ≫ E ◁ (y ▷ F) ≫ E ◁ (J ◁ z) =
      (x ▷ J) ▷ F ≫ (α_ E J F).hom ≫ E ◁ (y ▷ F ≫ J ◁ z) := by bicategory
  rw [hx, rightMate_pre, rightMate_post, mate_associator]
  calc
    _ = 𝟙 _ ⊗≫ (cup ≫ R ◁ x ≫ A.counit) ▷ J ⊗≫
      (J ◁ D.unit ≫ y ▷ (F ≫ T)) ⊗≫ J ◁ (z ▷ T) := by bicategory
    _ = _ := by rw [whisker_exchange]; bicategory

/-- Evaluate the braid correction between a derived cup and two right mates. -/
def upperCupEval (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cup : 𝟙 b ⟶ R ≫ E) : MvPolynomial (Fin 3) k →ₗ[k] (J ⟶ J ≫ (F ≫ T)) where
  toFun p := (λ_ J).inv ≫ cup ▷ J ≫ (α_ R E J).hom ≫
    mateEquiv A D ((α_ E J F).hom ≫
      KLR.ncEval (A := End (E ≫ (J ≫ F)))
        ![E ◁ (J ◁ z), E ◁ (y ▷ F), x ▷ (J ≫ F)] p) ≫ (α_ J F T).hom
  map_add' p q := by
    rw [CL.ncEvalB_add]
    change _ ≫ _ ≫ _ ≫ mateEquiv A D ((α_ E J F).hom ≫ (_ + _)) ≫ _ = _
    rw [Preadditive.comp_add, source_mate_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' s p := by
    rw [MvPolynomial.smul_eq_C_mul, CL.ncEval_C_mul', ← Algebra.smul_def]
    change _ ≫ _ ≫ _ ≫ mateEquiv A D ((α_ E J F).hom ≫ (s • _)) ≫ _ = _
    rw [Linear.comp_smul, source_mate_smul]
    simp only [Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

/-- Expand a three-variable monomial with its source variable order unchanged. -/
theorem upperCupEval_X3 (x : E ⟶ E) (y : J ⟶ J) (z : F ⟶ F)
    (cup : 𝟙 b ⟶ R ≫ E) (r q s : ℕ) :
    upperCupEval (k := k) A D J x y z cup
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
    (λ_ J).inv ≫ (cup ≫ R ◁ powComp x s ≫ A.counit) ▷ J ≫ (λ_ J).hom ≫
      powComp y q ≫ (ρ_ J).inv ≫ J ◁ (D.unit ≫ powComp z r ▷ T) := by
  change _ ≫ _ ≫ _ ≫ mateEquiv A D ((α_ E J F).hom ≫ _) ≫ _ = _
  rw [CL.ncEval_X3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, End.mul_def,
    ← powComp_eq_end_pow, ← whiskerLeft_powComp, ← powComp_whiskerRight]
  exact mate_monomial_cup A D J (powComp x s) (powComp y q) (powComp z r) cup
end Polynomial

section CapPolynomial
variable {a b c : B} {E : a ⟶ b} {R : b ⟶ a} (A : E ⊣ R)
  (J : b ⟶ c) (x : E ⟶ E) (y : J ⟶ J) (cup : 𝟙 b ⟶ R ≫ E)

/-- Contract a two-variable square polynomial against a cup and a dotted cap. -/
def upperCapEval (n : ℕ) : MvPolynomial (Fin 2) k →ₗ[k] (J ⟶ J) where
  toFun p := (λ_ J).inv ≫ cup ▷ J ≫ (α_ R E J).hom ≫
    R ◁ (KLR.ncEval (A := End (E ≫ J)) ![E ◁ y, x ▷ J] p) ≫
    (α_ R E J).inv ≫ (R ◁ powComp x n ≫ A.counit) ▷ J ≫ (λ_ J).hom
  map_add' p q := by
    rw [CL.ncEvalB_add]
    change _ ≫ _ ≫ _ ≫ R ◁ ((_ : E ≫ J ⟶ E ≫ J) + (_ : E ≫ J ⟶ E ≫ J)) ≫ _ = _
    simp only [AdditiveWhiskering.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' s p := by
    rw [MvPolynomial.smul_eq_C_mul, CL.ncEval_C_mul', ← Algebra.smul_def]
    change _ ≫ _ ≫ _ ≫ R ◁ (s • (_ : E ≫ J ⟶ E ≫ J)) ≫ _ = _
    simp only [source_whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply]

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The second variable counts dots on the colour of the cup. -/
theorem upperCapEval_X2 (n p q : ℕ) :
    upperCapEval (k := k) A J x y cup n (MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
    (λ_ J).inv ≫ (cup ≫ R ◁ powComp x (q+n) ≫ A.counit) ▷ J ≫ (λ_ J).hom ≫ powComp y p := by
  change _ ≫ _ ≫ _ ≫ R ◁ (KLR.ncEval (A := End (E ≫ J)) _ _) ≫ _ = _
  rw [CL.ncEval_X2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, End.mul_def,
    ← powComp_eq_end_pow, ← whiskerLeft_powComp, ← powComp_whiskerRight]
  calc
    _ = 𝟙 _ ⊗≫ cup ▷ J ⊗≫ (R ◁ powComp x q) ▷ J ⊗≫
      ((R ≫ E) ◁ powComp y p ≫ (R ◁ powComp x n ≫ A.counit) ▷ J) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by
      rw [whisker_exchange, ← powComp_comp_powComp, whiskerLeft_comp]
      bicategory
end CapPolynomial

section CapEvaluation
variable {a b c e : B} {E : a ⟶ b} {R : b ⟶ a} {G : b ⟶ e} {U : e ⟶ b}
  {A : E ⊣ R} {A' : G ⊣ U} (J : b ⟶ c) {x : E ⟶ E} {x' : G ⟶ G}
  (y : J ⟶ J) {τ : E ≫ G ⟶ E ≫ G} {h : ℤ} (L : RouqLoc A A' x x' τ h)

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- Low-degree contraction is the top positive inversion component. -/
theorem upperCapEval_X2_low (hh : 0 < h) (n p q : ℕ) (hq : q+n < h.toNat) :
    upperCapEval (k := k) A J x y L.cupL n (MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
    if q+n = (h-1).toNat then powComp y p else 0 := by
  rw [upperCapEval_X2]
  have hb : L.cupL ≫ R ◁ powComp x (q+n) ≫ A.counit =
      if q+n = (h-1).toNat then 𝟙 _ else 0 := by
    simpa only [RouqLoc.capD, eq_comm] using L.cupL_capD hh hq
  rw [hb]
  split_ifs <;> simp [AdditiveWhiskering.zero_whiskerRight]

variable {I : Type*} {C : CartanDatum I} (P : CL.CLScalars C k) {i j : I}

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- Only the `tᵢⱼ` leading term of the square survives the bounded contraction. -/
theorem upperCapEval_brundan (hij : i ≠ j) (n : ℕ) (hn : (n : ℤ) < h - C.dij i j) :
    upperCapEval A J x y L.cupL n (brundanQ P j i) =
      (P.t i j : k) • (if n = (h-C.dij i j-1).toNat then 𝟙 J else 0) := by
  classical
  have hh : 0 < h := by omega
  let Ψ := upperCapEval (k := k) A J x y L.cupL n
  have he (s : k) (p q : ℕ) (hq : q ≤ C.dij i j) :
      Ψ (MvPolynomial.C s * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) =
      s • (if q+n = (h-1).toNat then powComp y p else 0) := by
    rw [mul_assoc, MvPolynomial.C_mul', map_smul]
    change s • upperCapEval A J x y L.cupL n _ = _
    rw [upperCapEval_X2_low J y L hh n p q (by omega)]
  change Ψ _ = _
  by_cases hd0 : C.dot j i = 0
  · have hdij : C.dij i j = 0 := (C.dij_eq_zero_iff hij).2 (by simpa only [C.symm i j] using hd0)
    rw [brundanQ, ite_eq_left hd0]
    have hconst : (MvPolynomial.C (P.t j i : k) : MvPolynomial (Fin 2) k) =
        MvPolynomial.C (P.t j i : k) * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 0 := by simp
    rw [hconst, he _ 0 0 (by omega)]
    simp only [zero_add, powComp_zero, hdij, Nat.cast_zero, sub_zero]
    rw [P.t_symm j i hd0]
  have hdpos : 0 < C.dij i j := C.dij_pos hij (by simpa only [C.symm i j] using hd0)
  rw [brundanQ, ite_eq_right hd0, map_add, map_add]
  have hX : (MvPolynomial.C (P.t j i : k) * MvPolynomial.X 0 ^ C.dij j i : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t j i : k) * MvPolynomial.X 0 ^ C.dij j i * MvPolynomial.X 1 ^ 0 := by simp
  have hY : (MvPolynomial.C (P.t i j : k) * MvPolynomial.X 1 ^ C.dij i j : MvPolynomial (Fin 2) k) =
      MvPolynomial.C (P.t i j : k) * MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ C.dij i j := by simp
  rw [hX, hY, he _ _ _ (by omega), he _ _ _ le_rfl,
    ite_eq_right (show ¬ 0+n = (h-1).toNat by omega), smul_zero, zero_add]
  have hrect : Ψ (∑ p ∈ Finset.range (C.dij j i), ∑ q ∈ Finset.range (C.dij i j),
      MvPolynomial.C (P.s j i p q) * MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) = 0 := by
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro q hq
    have hq' := Finset.mem_range.mp hq
    rw [he _ p q (by omega), ite_eq_right (by omega), smul_zero]
  rw [hrect, add_zero, powComp_zero]
  have hiff : C.dij i j+n = (h-1).toNat ↔ n = (h-C.dij i j-1).toNat := by omega
  simp only [hiff]
end CapEvaluation

section Correction
variable {a b c d e : B} {E : a ⟶ b} {R : b ⟶ a} {G : b ⟶ e} {U : e ⟶ b}
  {F : c ⟶ d} {T : d ⟶ c} {A : E ⊣ R} {A' : G ⊣ U} (D : F ⊣ T)
  (J : b ⟶ c) {x : E ⟶ E} {x' : G ⟶ G} (y : J ⟶ J) (z : F ⟶ F)
  {τ : E ≫ G ⟶ E ≫ G} {h : ℤ} (L : RouqLoc A A' x x' τ h)

/-- Contract the low outer degree using the positive inversion. -/
theorem upperCupEval_X3_low (hh : 0 < h) (r q s : ℕ) (hs : s < h.toNat) :
    upperCupEval (k := k) A D J x y z L.cupL
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
    if s = (h-1).toNat then
      powComp y q ≫ (ρ_ J).inv ≫ J ◁ (D.unit ≫ powComp z r ▷ T) else 0 := by
  rw [upperCupEval_X3]
  have hb : L.cupL ≫ R ◁ powComp x s ≫ A.counit =
      if s = (h-1).toNat then 𝟙 _ else 0 := by
    simpa only [RouqLoc.capD, eq_comm] using L.cupL_capD hh hs
  rw [hb]
  split_ifs <;> simp [AdditiveWhiskering.zero_whiskerRight]

variable {I : Type*} {C : CartanDatum I} (P : CL.CLScalars C k) {i j : I}

/-- The divided-difference correction survives exactly at `h = dᵢⱼ`. -/
theorem upperCupEval_brundan (hij : i ≠ j) (hh : 0 < h) (hd : (C.dij i j : ℤ) ≤ h) :
    upperCupEval A D J x y z L.cupL (KLR.qbar (brundanQ P i j)) =
    if h = C.dij i j then (P.t i j : k) • ((ρ_ J).inv ≫ J ◁ D.unit) else 0 := by
  classical
  by_cases hd0 : C.dot i j = 0
  · have hz := (C.dij_eq_zero_iff hij).2 hd0
    rw [brundanQ, ite_eq_left hd0, CL.qbar_C, map_zero, ite_eq_right (by omega)]
  have hdpos := C.dij_pos hij hd0
  let Ψ := upperCupEval (k := k) A D J x y z L.cupL
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
    have hp' := Finset.mem_range.mp hp
    have hr' := Finset.mem_range.mp hr
    rw [he, map_smul]
    change P.s i j p q • upperCupEval A D J x y z L.cupL _ = 0
    rw [upperCupEval_X3_low D J y z L hh r q _ (by omega), ite_eq_right (by omega), smul_zero]
  rw [hs, add_zero]
  have he (r : ℕ) : (MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (C.dij i j-1-r) :
      MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ (C.dij i j-1-r) := by simp
  simp_rw [he]
  by_cases hb : h = C.dij i j
  · rw [ite_eq_left hb, Finset.sum_eq_single 0]
    · change (P.t i j : k) • upperCupEval A D J x y z L.cupL _ = _
      rw [upperCupEval_X3_low D J y z L hh _ _ _ (by omega), ite_eq_left (by omega)]
      simp
    · intro r hr hne
      have hr' := Finset.mem_range.mp hr
      change upperCupEval A D J x y z L.cupL _ = 0
      rw [upperCupEval_X3_low D J y z L hh _ _ _ (by omega), ite_eq_right (by omega)]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hdpos))
  · rw [ite_eq_right hb]
    have hz : (∑ r ∈ Finset.range (C.dij i j),
        Ψ (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ 0 *
          MvPolynomial.X 2 ^ (C.dij i j-1-r))) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr' := Finset.mem_range.mp hr
      change upperCupEval A D J x y z L.cupL _ = 0
      rw [upperCupEval_X3_low D J y z L hh _ _ _ (by omega), ite_eq_right (by omega)]
    rw [hz, smul_zero]
end Correction

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : RootDatum C X Y}
  (S : RouqFamily (B := B) RD)

/-- The derived left unit is the cup of the local inverse at its upper weight. -/
theorem adjL_unit (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    (S.adjL i h₁).unit = (S.loc i h₁ h₂).cupL := by
  rw [S.adjL_eq i (sub_add_cancel a (RD.iX i)) h₁ h₂]
  rfl

/-- The left side of the cup pitchfork postcomposed with the mixed crossing. -/
def cupTurn (i j : I) {a b c e : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX j = c) (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c) :
    S.E j h₂ ⟶ S.E j h₂ ≫ (S.F i h₇ ≫ S.E i h₇) :=
  (λ_ (S.E j h₂)).inv ≫ (S.adjL i h₁).unit ▷ S.E j h₂ ≫
    (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫
    S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ ≫
    (α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).inv ≫
    S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
    (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).hom

omit [AdditiveWhiskering B] in
/-- The counit identity for the original right mate, without a cyclicity premise. -/
theorem mixedSigma_cap (i j : I) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c) :
    (α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).inv ≫
      S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
      (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).hom ≫
      S.E j h₂ ◁ (S.adj i h₇).counit ≫ (ρ_ (S.E j h₂)).hom =
    S.F i h₁ ◁ S.cross i j h₆ h₇ h₁ h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).inv ≫
      (S.adj i h₁).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom := by
  have H := (mateEquiv_eq_iff_counit (S.adj i h₁) (S.adj i h₇)
    (S.cross i j h₆ h₇ h₁ h₂) (S.mixedSigma i j h₆ h₇ h₁ h₂)).mp rfl
  simpa only [Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_symm_apply,
    Category.assoc] using H.symm

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The dotted-cap component of the cup turn is the original upward square. -/
theorem cupTurn_cap {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Q) (i j : I) (hij : i ≠ j) {a b c d e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₄ : b + RD.iX i = d) (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (n : ℕ) :
    S.cupTurn i j h₁ h₂ h₆ h₇ ≫
      S.E j h₂ ◁ ((S.F i h₇ ◁ powComp (S.dot i h₇) n) ≫ (S.adj i h₇).counit) ≫
      (ρ_ (S.E j h₂)).hom =
    upperCapEval (S.adj i h₁) (S.E j h₂) (S.dot i h₁) (S.dot j h₂)
      (S.loc i h₁ h₄).cupL n (Q j i) := by
  have hs : S.E j h₆ ◁ powComp (S.dot i h₇) n ≫ S.cross i j h₆ h₇ h₁ h₂ =
      S.cross i j h₆ h₇ h₁ h₂ ≫ powComp (S.dot i h₁) n ▷ S.E j h₂ := by
    simpa only [← powComp_whiskerRight, ← whiskerLeft_powComp] using
      powComp_slide _ _ _ (H.slide_left i j hij h₆ h₇ h₁ h₂) n
  have hc := S.mixedSigma_cap i j h₁ h₂ h₆ h₇
  unfold cupTurn
  calc
    _ = (λ_ (S.E j h₂)).inv ≫ (S.adjL i h₁).unit ▷ S.E j h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫
      S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ ≫
      S.F i h₁ ◁ (S.E j h₆ ◁ powComp (S.dot i h₇) n) ≫
      ((α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).inv ≫
        S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
        (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).hom ≫
        S.E j h₂ ◁ (S.adj i h₇).counit ≫ (ρ_ (S.E j h₂)).hom) := by
        calc
          _ = 𝟙 _ ⊗≫ (S.adjL i h₁).unit ▷ S.E j h₂ ⊗≫
            S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ ⊗≫
            (S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
              (S.E j h₂ ≫ S.F i h₇) ◁ powComp (S.dot i h₇) n) ⊗≫
            S.E j h₂ ◁ (S.adj i h₇).counit ⊗≫ 𝟙 _ := by bicategory
          _ = _ := by rw [← whisker_exchange]; bicategory
    _ = _ := by
      rw [hc]
      have he : S.F i h₁ ◁ (S.E j h₆ ◁ powComp (S.dot i h₇) n) ≫
          S.F i h₁ ◁ S.cross i j h₆ h₇ h₁ h₂ =
          S.F i h₁ ◁ S.cross i j h₆ h₇ h₁ h₂ ≫
          S.F i h₁ ◁ (powComp (S.dot i h₁) n ▷ S.E j h₂) := by
        rw [← whiskerLeft_comp, hs, whiskerLeft_comp]
      rw [reassoc_of% he]
      rw [S.adjL_unit i h₁ h₄]
      unfold upperCapEval
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← H.square j i hij.symm h₁ h₂ h₆ h₇, whiskerLeft_comp]
      bicategory

/-- At positive weight the crossing component is minus the mated braid correction. -/
theorem cupTurn_sig_pos {Q : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Q) (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hh : 0 < RD.pair (RD.iY i) b) :
    S.cupTurn i j h₁ h₂ h₆ h₇ ≫ S.E j h₂ ◁ (S.loc i h₇ h₃).sig =
    -upperCupEval (S.adj i h₁) (S.adj i h₃) (S.E j h₂)
      (S.dot i h₁) (S.dot j h₂) (S.dot i h₃) (S.loc i h₁ h₄).cupL (KLR.qbar (Q i j)) := by
  have hb := congrArg (fun z => (λ_ (S.E j h₂)).inv ≫
      (S.loc i h₁ h₄).cupL ▷ S.E j h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫ z ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom)
    (S.mixedSigma_braidQ H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id, S.mixedSigma_self] at hb
  rw [← comp_whiskerRight_assoc, (S.loc i h₁ h₄).cupL_sig hh,
    AdditiveWhiskering.zero_whiskerRight] at hb
  simp only [Limits.zero_comp, Limits.comp_zero, zero_sub] at hb
  apply neg_injective
  simpa only [cupTurn, S.adjL_unit i h₁ h₄, upperCupEval,
    LinearMap.coe_mk, AddHom.coe_mk, Category.assoc, neg_neg] using hb

/-- Recover the cup turn from every positive-inversion component when `h > 0`. -/
theorem cupTurn_of_ge_pos (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hh : 0 < RD.pair (RD.iY i) b) (hd : (C.dij i j : ℤ) ≤ RD.pair (RD.iY i) b) :
    S.cupTurn i j h₁ h₂ h₆ h₇ =
      (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adjL i h₇).unit) := by
  classical
  have hw := pair_step_ne i j hij h₂
  have hc : 0 ≤ RD.pair (RD.iY i) c := by omega
  rw [S.adjL_unit i h₇ h₃]
  apply (S.loc i h₇ h₃).nonneg_whisker_ext hc
  · rw [S.cupTurn_sig_pos H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hh,
      upperCupEval_brundan _ _ _ _ _ P hij hh hd]
    have hs := (S.loc i h₇ h₃).cupL_powComp_sig_of_le (n := 0) hc
    simp only [powComp_zero, whiskerLeft_id, Category.id_comp] at hs
    simp only [Linear.smul_comp, Category.assoc, ← whiskerLeft_comp]
    rw [hs]
    by_cases hz : RD.pair (RD.iY i) b = C.dij i j
    · simp [hz, show RD.pair (RD.iY i) c = 0 by omega, AdditiveWhiskering.whiskerLeft_neg]
    · simp [hz, show ¬ (0 : ℤ) = RD.pair (RD.iY i) c by omega,
        AdditiveWhiskering.whiskerLeft_zero]
  · intro n hn
    apply (cancel_mono (ρ_ (S.E j h₂)).hom).mp
    have ht := S.cupTurn_cap H i j hij h₁ h₂ h₄ h₆ h₇ n
    change S.cupTurn i j h₁ h₂ h₆ h₇ ≫ S.E j h₂ ◁ (S.loc i h₇ h₃).capD n ≫
      (ρ_ (S.E j h₂)).hom = _ at ht
    rw [Category.assoc, ht, upperCapEval_brundan _ _ _ P hij n (by omega)]
    simp only [Linear.smul_comp, Category.assoc, ← whiskerLeft_comp_assoc]
    rw [(S.loc i h₇ h₃).cupL_capD (by omega) hn]
    have he : n = (RD.pair (RD.iY i) b - C.dij i j - 1).toNat ↔
        (RD.pair (RD.iY i) c - 1).toNat = n := by omega
    simp only [he]
    split_ifs <;> simp [AdditiveWhiskering.whiskerLeft_zero]

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
/-- For disconnected colours the original cup turn is the constant square `tᵢⱼ`. -/
theorem mixedSigma_cup_square_zero (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {b c d f : X}
    (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f) (hd : C.dot i j = 0) :
    (λ_ (S.E j h₂)).inv ≫ (S.adj i h₄).unit ▷ S.E j h₂ ≫
      (α_ (S.E i h₄) (S.F i h₄) (S.E j h₂)).hom ≫
      S.E i h₄ ◁ S.mixedSigma i j h₂ h₃ h₄ h₅ ≫
      (α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫
      S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom =
    (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adj i h₃).unit) := by
  have hs := H.square i j hij h₂ h₃ h₄ h₅
  rw [brundanQ, ite_eq_left hd, CL.ncEval_C'] at hs
  change S.cross i j h₂ h₃ h₄ h₅ ≫ S.cross j i h₄ h₅ h₂ h₃ =
    (P.t i j : k) • 𝟙 _ at hs
  have hp := congrArg (fun z => z ≫
      (α_ (S.E i h₄) (S.E j h₅) (S.F i h₃)).inv ≫
      S.cross j i h₄ h₅ h₂ h₃ ▷ S.F i h₃ ≫
      (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom)
    (S.mixedSigma_cup i j h₂ h₃ h₄ h₅)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc] at hp
  rw [hs, source_smul_whiskerRight, id_whiskerRight] at hp
  simpa only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id] using hp

/-- The empty-component boundary `h = dᵢⱼ = 0`, using the original unit and square. -/
theorem cupTurn_of_ge_zero (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hh : RD.pair (RD.iY i) b = 0) (hd : C.dij i j = 0) :
    S.cupTurn i j h₁ h₂ h₆ h₇ =
      (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adjL i h₇).unit) := by
  have hw := pair_step_ne i j hij h₂
  have hc : RD.pair (RD.iY i) c = 0 := by omega
  have hd0 := (C.dij_eq_zero_iff hij).1 hd
  rw [S.adjL_unit i h₇ h₃]
  apply (S.loc i h₇ h₃).nonneg_whisker_ext (by omega)
  · have hb := congrArg (fun z => (λ_ (S.E j h₂)).inv ≫
        (S.loc i h₁ h₄).cupL ▷ S.E j h₂ ≫
        (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫ z ≫
        (α_ (S.E j h₂) (S.E i h₃) (S.F i h₃)).hom)
      (S.mixedSigma_braidQ H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇)
    have hl := (S.loc i h₁ h₄).cupL_powComp_sig_of_le (n := 0) (by omega)
    have hr := (S.loc i h₇ h₃).cupL_powComp_sig_of_le (n := 0) (by omega)
    simp only [powComp_zero, whiskerLeft_id, Category.id_comp, hh, hc, Nat.cast_zero, ite_true] at hl hr
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id, S.mixedSigma_self] at hb
    rw [← comp_whiskerRight_assoc, hl, AdditiveWhiskering.neg_whiskerRight] at hb
    have hz : upperCupEval (S.adj i h₁) (S.adj i h₃) (S.E j h₂)
        (S.dot i h₁) (S.dot j h₂) (S.dot i h₃) (S.loc i h₁ h₄).cupL
        (KLR.qbar (brundanQ P i j)) = 0 := by
      rw [brundanQ, ite_eq_left hd0, CL.qbar_C, map_zero]
    change _ - _ = upperCupEval (S.adj i h₁) (S.adj i h₃) (S.E j h₂)
        (S.dot i h₁) (S.dot j h₂) (S.dot i h₃) (S.loc i h₁ h₄).cupL
        (KLR.qbar (brundanQ P i j)) at hb
    rw [hz] at hb
    have he := (sub_eq_zero.mp hb).symm
    simp only [Preadditive.comp_neg, Preadditive.neg_comp] at he
    rw [S.mixedSigma_cup_square_zero P H i j hij h₂ h₃ h₄ h₅ hd0] at he
    simp only [Linear.smul_comp, Category.assoc, ← whiskerLeft_comp, hr,
      AdditiveWhiskering.whiskerLeft_neg, Preadditive.comp_neg, smul_neg]
    simpa only [cupTurn, S.adjL_unit i h₁ h₄, Category.assoc] using he
  · intro n hn
    omega

/-- The cup turn from the positive inversion components, including weight zero. -/
theorem cupTurn_of_ge (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hd : (C.dij i j : ℤ) ≤ RD.pair (RD.iY i) b) :
    S.cupTurn i j h₁ h₂ h₆ h₇ =
      (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adjL i h₇).unit) := by
  by_cases hh : 0 < RD.pair (RD.iY i) b
  · exact S.cupTurn_of_ge_pos P H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hh hd
  · exact S.cupTurn_of_ge_zero P H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ (by omega) (by omega)

/-- Brundan Lemma 5.2 (5.3): the actual scalar cup pitchfork for every `h ≥ dᵢⱼ`.
The only mixed invertibility premise is the original relation (1.7) for the
actual right mate. Both cups are the units of the derived left adjunctions.
The boundary `h = dᵢⱼ`, including disconnected colours at weight zero, is included. -/
theorem mixedCup_pitchfork_of_ge (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c e : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    [IsIso (S.mixedSigma i j h₆ h₇ h₁ h₂)]
    (hd : (C.dij i j : ℤ) ≤ RD.pair (RD.iY i) b) :
    (λ_ (S.E j h₂)).inv ≫ (S.adjL i h₁).unit ▷ S.E j h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫
      S.F i h₁ ◁ S.cross j i h₁ h₂ h₆ h₇ =
    (P.t i j : k) • ((ρ_ (S.E j h₂)).inv ≫ S.E j h₂ ◁ (S.adjL i h₇).unit ≫
      (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).inv ≫
      inv (S.mixedSigma i j h₆ h₇ h₁ h₂) ▷ S.E i h₇ ≫
      (α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).hom) := by
  apply (cancel_mono ((α_ (S.F i h₁) (S.E j h₆) (S.E i h₇)).inv ≫
    S.mixedSigma i j h₆ h₇ h₁ h₂ ▷ S.E i h₇ ≫
    (α_ (S.E j h₂) (S.F i h₇) (S.E i h₇)).hom)).mp
  simp only [Linear.smul_comp, Category.assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  exact S.cupTurn_of_ge P H i j hij h₁ h₂ rfl rfl
    (show b + RD.iX i + RD.iX j = c + RD.iX i by rw [← h₂]; abel) h₆ h₇ hd

end RouqFamily
end Categorification.TwoRep
