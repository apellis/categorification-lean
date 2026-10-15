import Categorification.TwoRep.RouqMixedNonpositive

/-!
# The mixed cap pitchfork below the Cartan bound

Brundan, arXiv:1501.00350v1, Lemma 5.2 (5.2). The positive band `0 < h < dᵢⱼ`
is proved by evaluating the capped mixed braid on the actual positive inverse
component. Its two vanishing bounds leave only the monomial with exponents
`r = dᵢⱼ - h - 1` and `s = h`; the rectangular lower terms vanish without
homogeneity assumptions. The cap definition and the inverse identity account
for both minus signs.

`mixedCap_pitchfork_of_lt` combines this with the nonpositive result. It uses
actual upward crossings, their right mates, and the derived left adjunction
caps, with coefficient `tᵢⱼ`. Only the source mixed inversion relation (1.7)
is required beyond the ungraded Rouquier and upward KLR data. The scalar ring
is commutative and horizontal composition is explicitly linear. Equation (5.3)
and all-weight cyclicity are separate results.
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

section Evaluation
variable {a b c d e f : B} {E : a ⟶ b} {R : b ⟶ a}
  {G : b ⟶ e} {U : e ⟶ b} {F : c ⟶ d} {T : d ⟶ c}
  {G' : f ⟶ c} {U' : c ⟶ f}
  {A : E ⊣ R} {A' : G ⊣ U} {D : F ⊣ T} {D' : G' ⊣ U'}
  {x : E ⟶ E} {x' : G ⟶ G} {z : F ⟶ F} {z' : G' ⟶ G'}
  {τ : E ≫ G ⟶ E ≫ G} {τ' : G' ≫ F ⟶ G' ≫ F}
  {h v : ℤ} (L : RouqLoc A A' x x' τ h) (M : RouqLoc D' D z' z τ' v)
  (J : b ⟶ c) (y : J ⟶ J)

/-- The capped correction evaluated on the actual positive inverse component. -/
def posCapEval : MvPolynomial (Fin 3) k →ₗ[k] ((G ≫ U) ≫ J ⟶ J) where
  toFun p := L.sigL ▷ J ≫ (α_ R E J).hom ≫ capEval A D J x y z M.capL p
  map_add' p q := by rw [map_add]; simp only [Preadditive.comp_add]
  map_smul' s p := by rw [map_smul]; simp only [Linear.comp_smul]; rfl

theorem posCapEval_X3 (r q s : ℕ) :
    posCapEval (k := k) L M J y
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
      (L.sigL ≫ L.capD s) ▷ J ≫ (λ_ J).hom ≫ powComp y q ≫ (ρ_ J).inv ≫
        J ◁ (D.unit ≫ powComp z r ▷ T ≫ M.capL) ≫ (ρ_ J).hom := by
  simp only [posCapEval, LinearMap.coe_mk, AddHom.coe_mk, capEval_X3,
    Category.assoc, Iso.hom_inv_id_assoc, RouqLoc.capD, comp_whiskerRight]

theorem posCapEval_X3_of_lt (hh : 0 ≤ h) (r q s : ℕ) (hs : s < h.toNat) :
    posCapEval (k := k) L M J y
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) = 0 := by
  rw [posCapEval_X3, L.sigL_capD hh hs, AdditiveWhiskering.zero_whiskerRight]
  simp

theorem posCapEval_X3_low (hv : v < 0) (r q s : ℕ) (hr : r < (-v).toNat) :
    posCapEval (k := k) L M J y
      (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
      if r = (-v-1).toNat then
        (L.sigL ≫ L.capD s) ▷ J ≫ (λ_ J).hom ≫ powComp y q else 0 := by
  rw [posCapEval_X3]
  have hb : D.unit ≫ powComp z r ▷ T ≫ M.capL =
      if r = (-v-1).toNat then 𝟙 _ else 0 := by
    simpa only [RouqLoc.cupD, Category.assoc] using M.cupD_capL hv hr
  rw [hb]
  split_ifs <;> simp [AdditiveWhiskering.whiskerLeft_zero]

variable {I : Type*} {C : CartanDatum I} (P : CL.CLScalars C k) {i j : I}

/-- In the positive band the two inverse-component bounds leave one monomial. -/
theorem posCapEval_brundan (hij : i ≠ j) (hh : 0 < h)
    (hd : h < C.dij i j) (hv : v = h - C.dij i j) :
    posCapEval L M J y (KLR.qbar (brundanQ P i j)) =
      -(P.t i j : k) • (L.capL ▷ J ≫ (λ_ J).hom) := by
  classical
  have hvneg : v < 0 := by omega
  have hd0 : C.dot i j ≠ 0 := by
    intro hz
    have := (C.dij_eq_zero_iff hij).2 hz
    omega
  let Ψ := posCapEval (k := k) L M J y
  have he (r q s : ℕ) (hrs : r+s < C.dij i j) :
      Ψ (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q * MvPolynomial.X 2 ^ s) =
      if r = (-v-1).toNat ∧ s = h.toNat then
        -(L.capL ▷ J ≫ (λ_ J).hom ≫ powComp y q) else 0 := by
    by_cases hs : s < h.toNat
    · rw [posCapEval_X3_of_lt L M J y hh.le r q s hs, ite_eq_right (by omega)]
    · rw [posCapEval_X3_low L M J y hvneg r q s (by omega)]
      by_cases hr : r = (-v-1).toNat
      · have hs' : s = h.toNat := by omega
        rw [ite_eq_left hr, ite_eq_left ⟨hr, hs'⟩, hs']
        have hc : L.sigL ≫ L.capD h.toNat = -L.capL := by
          rw [L.capL_of_nonneg hh.le, neg_neg]
        rw [hc, AdditiveWhiskering.neg_whiskerRight, Preadditive.neg_comp]
      · rw [ite_eq_right hr, ite_eq_right (by omega)]
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
    have hm : (MvPolynomial.C (P.s i j p q) * MvPolynomial.X 1 ^ q *
        (MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (p-1-r)) : MvPolynomial (Fin 3) k) =
        (P.s i j p q) • (MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ q *
          MvPolynomial.X 2 ^ (p-1-r)) := by rw [MvPolynomial.smul_eq_C_mul]; ring
    have hp' := Finset.mem_range.mp hp
    have hr' := Finset.mem_range.mp hr
    rw [hm, map_smul, he r q (p-1-r) (by omega), ite_eq_right (by omega), smul_zero]
  rw [hs, add_zero]
  have hm (r : ℕ) : (MvPolynomial.X 0 ^ r * MvPolynomial.X 2 ^ (C.dij i j-1-r) :
      MvPolynomial (Fin 3) k) =
      MvPolynomial.X 0 ^ r * MvPolynomial.X 1 ^ 0 * MvPolynomial.X 2 ^ (C.dij i j-1-r) := by simp
  simp_rw [hm]
  rw [Finset.sum_eq_single (-v-1).toNat]
  · rw [he _ _ _ (by omega), ite_eq_left ⟨rfl, by omega⟩, powComp_zero,
      Category.comp_id, smul_neg, neg_smul]
  · intro r hr hne
    have hr' := Finset.mem_range.mp hr
    rw [he _ _ _ (by omega), ite_eq_right (by omega)]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))
end Evaluation

namespace RouqFamily
variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  (S : RouqFamily (B := B) RD)

/-- The positive-band cap turn, using the actual positive inverse component. -/
theorem capTurn_pos (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hh : 0 < RD.pair (RD.iY i) b) (hd : RD.pair (RD.iY i) b < C.dij i j) :
    S.capTurn i j h₂ h₃ h₄ h₅ =
      (P.t i j : k) • ((S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  have hw := pair_step_ne i j hij h₂
  have hc : RD.pair (RD.iY i) c < 0 := by omega
  have hb := congrArg (fun z => (S.loc i h₁ h₄).sigL ▷ S.E j h₂ ≫
      (α_ (S.F i h₁) (S.E i h₁) (S.E j h₂)).hom ≫ z)
    (S.capTurn_sig H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hc)
  have he := posCapEval_brundan (S.loc i h₁ h₄) (S.loc i h₇ h₃)
    (S.E j h₂) (S.dot j h₂) P hij hh hd hw
  change _ = posCapEval (S.loc i h₁ h₄) (S.loc i h₇ h₃)
    (S.E j h₂) (S.dot j h₂) _ at hb
  rw [he] at hb
  simp only [Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc] at hb
  rw [(S.loc i h₁ h₄).sigL_sig_of_nonneg hh.le,
    AdditiveWhiskering.neg_whiskerRight, id_whiskerRight,
    Preadditive.neg_comp, Category.id_comp, neg_smul] at hb
  rw [S.adjL_counit i h₁ h₄]
  exact neg_injective hb

/-- The cap turn for every weight strictly below `dᵢⱼ`. -/
theorem capTurn_of_lt (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c)
    (hd : RD.pair (RD.iY i) b < C.dij i j) :
    S.capTurn i j h₂ h₃ h₄ h₅ =
      (P.t i j : k) • ((S.adjL i h₄).counit ▷ S.E j h₂ ≫ (λ_ (S.E j h₂)).hom) := by
  by_cases hh : RD.pair (RD.iY i) b ≤ 0
  · exact S.capTurn_nonpos P H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ hh hd
  · exact S.capTurn_pos P H i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇ (by omega) hd

/-- Brundan Lemma 5.2 (5.2): the scalar cap pitchfork for all `h < dᵢⱼ`.
The only mixed invertibility assumption is the original defining relation (1.7)
for the actual mate. The caps come from the derived left adjunctions, and the
coefficient is `tᵢⱼ`. No restriction to nonpositive weights remains. -/
theorem mixedCap_pitchfork_of_lt (P : CL.CLScalars C k) (H : BrundanUpKLR S P)
    (i j : I) (hij : i ≠ j) {b c d f : X}
    (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    [IsIso (S.mixedSigma i j h₂ h₃ h₄ h₅)]
    (hd : RD.pair (RD.iY i) b < C.dij i j) :
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
  exact S.capTurn_of_lt P H i j hij
    (sub_add_cancel b (RD.iX i)) h₂ h₃ h₄ h₅
    (show b - RD.iX i + RD.iX j = c - RD.iX i by rw [← h₂]; abel)
    (sub_add_cancel c (RD.iX i)) hd
end RouqFamily
end Categorification.TwoRep
