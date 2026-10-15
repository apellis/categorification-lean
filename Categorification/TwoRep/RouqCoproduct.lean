/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCoproductBubbles
import Categorification.TwoRep.RouqCoproductTeleporter
import Categorification.TwoRep.CoproductGauss

/-!
# The `sl₂` coproduct: the block of Rouquier's map through the identity

Let finitely many labels `a ∈ A` each carry Rouquier's `sl₂` data at a common object `b`
(`RouqLoc`; J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
Definition 1.1) of weight `h a`, with nilpotent dots, in a `k`-linear bicategory. Shift the dots
of label `a` by pairwise distinct scalars `u a ∈ k`. Rouquier's map for the direct sum
`E = ⊞ₐ Eₐ` at `b` has a block

  `⊞ₐ Eₐ Fₐ 1_b → ⊞ₐ Fₐ Eₐ 1_b ⊕ 1_b^{⊕ N}`,   `N = ∑ₐ h a ≥ 0`,

whose entries are
* `(a, a)`: the rightward crossing `σₐ` of label `a`;
* `(a, c)`, `a ≠ c`: the rightward crossing of the position-preserving component `δ a c` of the
  summed crossing on `Eₐ E_c`, which is an inverse of the dumbbell `(u_c + y_c) - (u_a + x_a)`;
* `(a, t)`, `t < N`: the cap of label `a` with `t` shifted dots `(u_a + x_a)ᵗ`.

This is the block-`(2)` part of KM3 for the coproduct of `sl₂` data (B. Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, Theorem `th:coproduct` and Lemma
`lem:many-sl2`; J. Brundan, A. Savage, B. Webster, arXiv:1812.03255v3, §5, Theorem 5.4). The
remaining blocks `Eₐ F_c → F_c Eₐ` (`a ≠ c`) only involve the mixed crossings.

**Proof.** The statement is the same as in the sources; the proof is a matrix argument. In the
additive envelope `Mat_ (b ⟶ b)`, the labelwise inverses of Rouquier's maps assemble to an
isomorphism `Φ`; composing with `Φ⁻¹` and Gaussian elimination (`CoproductGauss`) reduce the
block to a square matrix over the commutative ring `End (𝟙 b)`. Modulo the nilradical this matrix
is the image of the partial-fraction matrix `crtMatrix` (`CoproductCRT`), which is invertible over
`k` since the `u a` are distinct. The nilpotent corrections are the closed diagrams of
`RouqCoproductBubbles` (Brundan's infinite Grassmannian relation, Theorem 3.2, and nilpotent dots).

## Main statements

* `RouqCoproduct.isIso_rouqMap_of_nonneg`: for `∑ₐ h a ≥ 0` the block is invertible in
  `Mat_ (b ⟶ b)`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Finset

universe w v u

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-! ## Matrices in the additive envelope -/

namespace RouqCoproduct

section MatHelpers

variable {D : Type*} [Category D] [Preadditive D]

/-- A diagonal morphism between objects of `Mat_ D` indexed by the same type. -/
def diagMat {A : Type} [Fintype A] [DecidableEq A] {F G : A → D} (f : ∀ a, F a ⟶ G a) :
    (⟨A, F⟩ : Mat_ D) ⟶ ⟨A, G⟩ :=
  fun a c => if hac : a = c then f a ≫ eqToHom (congrArg G hac) else 0

variable {A : Type} [Fintype A] [DecidableEq A] {F G : A → D}

theorem diagMat_comp_apply {M : Mat_ D} (f : ∀ a, F a ⟶ G a) (g : (⟨A, G⟩ : Mat_ D) ⟶ M)
    (a : A) (m : M.ι) : (diagMat f ≫ g) a m = f a ≫ g a m := by
  rw [Mat_.comp_apply, Finset.sum_eq_single a]
  · simp [diagMat]
  · intro c _ hc
    simp [diagMat, Ne.symm hc]
  · simp

theorem comp_diagMat_apply {M : Mat_ D} (f : ∀ a, F a ⟶ G a) (g : M ⟶ (⟨A, F⟩ : Mat_ D))
    (m : M.ι) (c : A) : (g ≫ diagMat f) m c = g m c ≫ f c := by
  rw [Mat_.comp_apply, Finset.sum_eq_single c]
  · simp [diagMat]
  · intro a _ hc
    simp [diagMat, hc]
  · simp

theorem diagMat_comp_diagMat {H : A → D} (f : ∀ a, F a ⟶ G a) (g : ∀ a, G a ⟶ H a) :
    diagMat f ≫ diagMat g = diagMat fun a => f a ≫ g a := by
  refine Mat_.hom_ext _ _ fun a c => ?_
  rw [diagMat_comp_apply]
  by_cases hac : a = c
  · subst hac; simp [diagMat]
  · simp [diagMat, hac]

theorem diagMat_id : diagMat (fun a => 𝟙 (F a)) = 𝟙 (⟨A, F⟩ : Mat_ D) := by
  refine Mat_.hom_ext _ _ fun a c => ?_
  by_cases hac : a = c
  · subst hac; simp [diagMat, Mat_.id_apply_self]
  · simp only [diagMat, dite_eq_right hac]
    exact (Mat_.id_apply_of_ne _ a c hac).symm

theorem diagMat_neg (f : ∀ a, F a ⟶ G a) : diagMat (fun a => -f a) = -diagMat f := by
  refine Mat_.hom_ext _ _ fun a c => ?_
  change _ = -(diagMat f a c)
  by_cases hac : a = c <;> simp [diagMat, hac]

end MatHelpers

/-! ## Matrices over a commutative ring modulo the nilradical -/

section MatNil

variable {R : Type*} [CommRing R] {ι κ μ : Type*} [Fintype κ]

/-- A matrix all of whose entries are nilpotent. -/
def MatNil {ι κ : Type*} (M : Matrix ι κ R) : Prop := ∀ i j, M i j ∈ nilradical R

omit [Fintype κ] in
theorem MatNil.add {M M' : Matrix ι κ R} (h : MatNil M) (h' : MatNil M') : MatNil (M + M') :=
  fun i j => Ideal.add_mem _ (h i j) (h' i j)

omit [Fintype κ] in
theorem MatNil.neg {M : Matrix ι κ R} (h : MatNil M) : MatNil (-M) :=
  fun i j => (Ideal.neg_mem_iff _).mpr (h i j)

omit [Fintype κ] in
theorem MatNil.sub {M M' : Matrix ι κ R} (h : MatNil M) (h' : MatNil M') : MatNil (M - M') :=
  fun i j => Ideal.sub_mem _ (h i j) (h' i j)

omit [Fintype κ] in
theorem MatNil.zero : MatNil (0 : Matrix ι κ R) := fun _ _ => Ideal.zero_mem _

theorem MatNil.mul_left (M : Matrix ι κ R) {M' : Matrix κ μ R} (h : MatNil M') :
    MatNil (M * M') :=
  fun _ j => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h l j)

theorem MatNil.mul_right {M : Matrix ι κ R} (h : MatNil M) (M' : Matrix κ μ R) :
    MatNil (M * M') :=
  fun i _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (h i l)

/-- Congruence modulo matrices with nilpotent entries. -/
def NilEq {ι κ : Type*} (M M' : Matrix ι κ R) : Prop := MatNil (M - M')

omit [Fintype κ] in
theorem NilEq.refl (M : Matrix ι κ R) : NilEq M M := by
  simpa [NilEq] using (MatNil.zero : MatNil (0 : Matrix ι κ R))

omit [Fintype κ] in
theorem NilEq.add {M₁ M₂ M₁' M₂' : Matrix ι κ R} (h₁ : NilEq M₁ M₁') (h₂ : NilEq M₂ M₂') :
    NilEq (M₁ + M₂) (M₁' + M₂') := by
  have := MatNil.add h₁ h₂
  unfold NilEq
  convert this using 1
  abel

omit [Fintype κ] in
theorem NilEq.sub {M₁ M₂ M₁' M₂' : Matrix ι κ R} (h₁ : NilEq M₁ M₁') (h₂ : NilEq M₂ M₂') :
    NilEq (M₁ - M₂) (M₁' - M₂') := by
  have := MatNil.sub h₁ h₂
  unfold NilEq
  convert this using 1
  abel

theorem NilEq.mul {M₁ M₁' : Matrix ι κ R} {M₂ M₂' : Matrix κ μ R} (h₁ : NilEq M₁ M₁')
    (h₂ : NilEq M₂ M₂') : NilEq (M₁ * M₂) (M₁' * M₂') := by
  have := MatNil.add (MatNil.mul_right h₁ M₂) (MatNil.mul_left M₁' h₂)
  unfold NilEq
  convert this using 1
  rw [Matrix.sub_mul, Matrix.mul_sub]
  abel

end MatNil

section Sums

variable {A : Type} [Fintype A] [DecidableEq A] {M : Type*} [AddCommMonoid M]

theorem sum_sigma_ite {g : A → ℕ} (a : A) (f : (Σ a, Fin (g a)) → M) :
    ∑ p : Σ a, Fin (g a), (if a = p.1 then f p else 0) = ∑ m : Fin (g a), f ⟨a, m⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro c _ hca; simp [Ne.symm hca]
  · simp

theorem sum_sigma_ite' {g : A → ℕ} (a : A) (f : (Σ a, Fin (g a)) → M) :
    ∑ p : Σ a, Fin (g a), (if p.1 = a then f p else 0) = ∑ m : Fin (g a), f ⟨a, m⟩ := by
  simp_rw [eq_comm (b := a)]
  exact sum_sigma_ite a f

end Sums

theorem Biprod.ofComponents_id {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (X Y : D) : Biprod.ofComponents (𝟙 X) 0 0 (𝟙 Y) = 𝟙 (X ⊞ Y) := by
  ext <;> simp [Biprod.ofComponents]

theorem oMat_id_apply {D : Type*} [Category D] [Preadditive D] (o : D) {ι : Type} [Fintype ι]
    [DecidableEq ι] (i j : ι) : (𝟙 (oMat o ι) : oMat o ι ⟶ oMat o ι) i j =
      if i = j then 𝟙 o else 0 := by
  by_cases hij : i = j
  · subst hij; rw [Mat_.id_apply_self, ite_eq_left rfl]
  · rw [Mat_.id_apply_of_ne _ _ _ hij, ite_eq_right hij]

/-! ## Labelwise relations, for either sign of the weight -/

section Uniform

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

omit [AdditiveWhiskering C] in
/-- Brundan (3.5) for either sign of `h`. -/
theorem sig_sigL_eq : L.sig ≫ L.sigL = ∑ m ∈ range h.toNat, L.capD m ≫ L.cupN m - 𝟙 _ := by
  by_cases hh : 0 ≤ h
  · exact L.sig_sigL_of_nonneg hh
  · rw [L.sig_sigL_of_nonpos (by omega), show h.toNat = 0 by omega]; simp

omit [AdditiveWhiskering C] in
/-- Brundan (3.5) for either sign of `h`. -/
theorem sigL_sig_eq : L.sigL ≫ L.sig = ∑ m ∈ range (-h).toNat, L.capN m ≫ L.cupD m - 𝟙 _ := by
  by_cases hh : h ≤ 0
  · exact L.sigL_sig_of_nonpos hh
  · rw [L.sigL_sig_of_nonneg (by omega), show (-h).toNat = 0 by omega]; simp

end Uniform

/-! ## Morphisms between powers of one object as matrices -/

section OMatExtra

variable {D : Type*} [Category D] [Preadditive D] {o : D} {ι κ : Type} [Fintype ι] [Fintype κ]

/-- A matrix over `End o` as a morphism `o^{⊕ ι} ⟶ o^{⊕ κ}`. -/
def ofMatrix (M : Matrix ι κ (End o)) : oMat o ι ⟶ oMat o κ := fun i j => M i j

@[simp] theorem toMatrix_ofMatrix (M : Matrix ι κ (End o)) :
    oMat.toMatrix (ofMatrix M) = M := rfl

theorem hom_ext_toMatrix {f g : oMat o ι ⟶ oMat o κ}
    (h : oMat.toMatrix f = oMat.toMatrix g) : f = g :=
  Mat_.hom_ext _ _ fun i j => congrFun (congrFun h i) j

theorem toMatrix_add (f g : oMat o ι ⟶ oMat o κ) :
    oMat.toMatrix (f + g) = oMat.toMatrix f + oMat.toMatrix g := rfl

theorem toMatrix_sub (f g : oMat o ι ⟶ oMat o κ) :
    oMat.toMatrix (f - g) = oMat.toMatrix f - oMat.toMatrix g := rfl

theorem toMatrix_zero : oMat.toMatrix (0 : oMat o ι ⟶ oMat o κ) = 0 := rfl

theorem toMatrix_id [DecidableEq ι] : oMat.toMatrix (𝟙 (oMat o ι)) = 1 := by
  ext i j
  rw [oMat.toMatrix, oMat_id_apply, Matrix.one_apply]
  rfl

/-- If `g ≫ f` is nilpotent, so is `f ≫ g`. -/
theorem isNilpotent_comp_swap {X Y : D} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsNilpotent (R := End Y) (g ≫ f)) : IsNilpotent (R := End X) (f ≫ g) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K + 1, ?_⟩
  have key : ∀ m, powComp (f ≫ g) (m + 1) = f ≫ powComp (g ≫ f) m ≫ g := by
    intro m
    induction m with
    | zero => simp [powComp_succ]
    | succ m ih => rw [powComp_succ, ih, powComp_succ]; simp only [Category.assoc]
  have hK' : powComp (g ≫ f) K = 0 := by rw [powComp_eq_pow']; exact hK
  rw [← powComp_eq_pow', key, hK', Limits.zero_comp, Limits.comp_zero]

end OMatExtra

/-! ## The setting -/

section Setting

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]
  {A : Type} [Fintype A] [DecidableEq A] {b : B} {src tgt : A → B}
  {E₁ : ∀ a, src a ⟶ b} {R₁ : ∀ a, b ⟶ src a} {E₂ : ∀ a, b ⟶ tgt a} {R₂ : ∀ a, tgt a ⟶ b}
  {adj₁ : ∀ a, E₁ a ⊣ R₁ a} {adj₂ : ∀ a, E₂ a ⊣ R₂ a}
  {x₁ : ∀ a, E₁ a ⟶ E₁ a} {x₂ : ∀ a, E₂ a ⟶ E₂ a}
  {τ : ∀ a, E₁ a ≫ E₂ a ⟶ E₁ a ≫ E₂ a} {h : A → ℤ}
  (L : ∀ a, RouqLoc (adj₁ a) (adj₂ a) (x₁ a) (x₂ a) (τ a) (h a))

/-- `⊞ₐ Eₐ Fₐ 1_b` in the additive envelope. -/
abbrev objEF (_L : ∀ a, RouqLoc (adj₁ a) (adj₂ a) (x₁ a) (x₂ a) (τ a) (h a)) : Mat_ (b ⟶ b) :=
  ⟨A, fun a => R₁ a ≫ E₁ a⟩

/-- `⊞ₐ Fₐ Eₐ 1_b` in the additive envelope. -/
abbrev objFE (_L : ∀ a, RouqLoc (adj₁ a) (adj₂ a) (x₁ a) (x₂ a) (τ a) (h a)) : Mat_ (b ⟶ b) :=
  ⟨A, fun a => E₂ a ≫ R₂ a⟩

/-- The index set `{(a, m) : m < h a}` of the caps in the labelwise inverses (`h a ≥ 0`). -/
abbrev Pos (h : A → ℤ) : Type := Σ a, Fin (h a).toNat

/-- The index set `{(a, m) : m < -h a}` of the cups in the labelwise inverses (`h a ≤ 0`). -/
abbrev Neg (h : A → ℤ) : Type := Σ a, Fin (-h a).toNat

/-- The labelwise rightward crossings. -/
def sigD : objEF L ⟶ objFE L := diagMat fun a => (L a).sig

/-- The labelwise leftward crossings. -/
def sigLD : objFE L ⟶ objEF L := diagMat fun a => (L a).sigL

/-- The labelwise caps `capD m`, `m < h a`. -/
def capP : objEF L ⟶ oMat (𝟙 b) (Pos h) :=
  fun a p => if a = p.1 then (L a).capD p.2 else 0

/-- The labelwise cups `cupD m`, `m < -h a`. -/
def cupM : oMat (𝟙 b) (Neg h) ⟶ objFE L :=
  fun q c => if q.1 = c then (L c).cupD q.2 else 0

/-- The labelwise `♠`-cups `cupN m`, `m < h a`. -/
def cupNP : oMat (𝟙 b) (Pos h) ⟶ objEF L :=
  fun p a => if p.1 = a then (L a).cupN p.2 else 0

/-- The labelwise `♣`-caps `capN m`, `m < -h a`. -/
def capNM : objFE L ⟶ oMat (𝟙 b) (Neg h) :=
  fun c q => if c = q.1 then (L c).capN q.2 else 0

/-- All caps `capD i`, `i < n`, of all labels. -/
def capAll (n : ℕ) : objEF L ⟶ oMat (𝟙 b) (A × Fin n) :=
  fun a q => if a = q.1 then (L a).capD q.2 else 0

/-- All cups `cupD j`, `j < n`, of all labels. -/
def cupAll (n : ℕ) : oMat (𝟙 b) (A × Fin n) ⟶ objFE L :=
  fun q c => if q.1 = c then (L c).cupD q.2 else 0

variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

variable (b) in
/-- The teleporter coefficients: `-telCoeff (u a - u c) i j` from the cap of label `a` with `i`
dots to the cup of label `c ≠ a` with `j` dots. -/
def tel (u : A → k) (n : ℕ) : oMat (𝟙 b) (A × Fin n) ⟶ oMat (𝟙 b) (A × Fin n) :=
  fun q q' => if q.1 = q'.1 then 0 else (-telCoeff (u q.1 - u q'.1) q.2 q'.2) • 𝟙 (𝟙 b)

variable (b) in
/-- The binomial coefficients `[xⁱ] (u_a + x)ᵗ`. -/
def wMat (u : A → k) (n N : ℕ) : oMat (𝟙 b) (A × Fin n) ⟶ oMat (𝟙 b) (Fin N) :=
  fun q t => (((t : ℕ).choose q.2 : k) * u q.1 ^ ((t : ℕ) - q.2)) • 𝟙 (𝟙 b)

/-- **The rightward crossing of the summed crossing**, restricted to `⊞ₐ Eₐ Fₐ → ⊞_c F_c E_c`:
the labelwise rightward crossings on the diagonal, and off the diagonal the rightward crossing of
the position-preserving component `δ a c` of the summed upward crossing on `Eₐ E_c`. -/
def rouqSig (δ : ∀ a c, E₁ a ≫ E₂ c ⟶ E₁ a ≫ E₂ c) : objEF L ⟶ objFE L :=
  sigD L + (show objEF L ⟶ objFE L from fun a c => if a = c then 0 else
    RightwardCrossing.sigma (adj₂ c).unit (δ a c) (adj₁ a).counit)

/-- **The caps with shifted dots** `(u_a + x_a)ᵗ`, `t < N`. -/
def rouqCaps (u : A → k) (N : ℕ) : objEF L ⟶ oMat (𝟙 b) (Fin N) :=
  fun a t => R₁ a ◁ powComp (u a • 𝟙 (E₁ a) + x₁ a) t ≫ (adj₁ a).counit

/-! ### The Rouquier map through the teleporters -/

section Bridge

theorem sum_prod_ite_fst {M : Type*} [AddCommMonoid M] {n : ℕ} (c : A) (f : A × Fin n → M) :
    ∑ q : A × Fin n, (if q.1 = c then f q else 0) = ∑ j : Fin n, f (c, j) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp
  · intro a _ hac; simp [hac]
  · simp

theorem sum_prod_ite_fst' {M : Type*} [AddCommMonoid M] {n : ℕ} (c : A) (f : A × Fin n → M) :
    ∑ q : A × Fin n, (if c = q.1 then f q else 0) = ∑ j : Fin n, f (c, j) := by
  simp_rw [eq_comm (a := c)]
  exact sum_prod_ite_fst c f

omit [AdditiveWhiskering B] in
theorem capAll_comp_apply {n : ℕ} {M : Mat_ (b ⟶ b)} (g : oMat (𝟙 b) (A × Fin n) ⟶ M) (a : A)
    (m : M.ι) : (capAll L n ≫ g) a m = ∑ i : Fin n, (L a).capD i ≫ g (a, i) m := by
  rw [Mat_.comp_apply]
  simp only [capAll, ite_comp, zero_comp]
  exact sum_prod_ite_fst' a _

omit [AdditiveWhiskering B] in
theorem comp_cupAll_apply {n : ℕ} {M : Mat_ (b ⟶ b)} (g : M ⟶ oMat (𝟙 b) (A × Fin n))
    (m : M.ι) (c : A) : (g ≫ cupAll L n) m c = ∑ j : Fin n, g m (c, j) ≫ (L c).cupD j := by
  rw [Mat_.comp_apply]
  simp only [cupAll, comp_ite, comp_zero]
  exact sum_prod_ite_fst c _

variable {n : ℕ} (hx₁ : ∀ a, powComp (x₁ a) n = 0) (hx₂ : ∀ a, powComp (x₂ a) n = 0)
  {u : A → k} (hu : Function.Injective u)

include hx₁ hx₂ hu in
/-- The off-diagonal entries of the Rouquier map are the teleporters. -/
theorem rouqSig_eq (δ : ∀ a c, E₁ a ≫ E₂ c ⟶ E₁ a ≫ E₂ c)
    (hδ : ∀ a c, a ≠ c →
      δ a c ≫ ((u c - u a) • 𝟙 _ + E₁ a ◁ x₂ c - x₁ a ▷ E₂ c) = 𝟙 _) :
    rouqSig L δ = sigD L + capAll L n ≫ tel b u n ≫ cupAll L n := by
  rw [rouqSig]
  congr 1
  refine Mat_.hom_ext _ _ fun a c => ?_
  rw [capAll_comp_apply]
  simp_rw [comp_cupAll_apply]
  by_cases hac : a = c
  · subst hac; simp [tel]
  · have he : u a - u c ≠ 0 := sub_ne_zero.mpr fun h' => hac (hu h')
    rw [ite_eq_right hac, sigma_eq_teleporter (adj₁ a) (adj₂ c) (x₁ a) (x₂ c) (hx₁ a) (hx₂ c) he
      (δ a c) (by rw [neg_sub]; exact hδ a c hac)]
    simp only [tel, hac, ite_false, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      Preadditive.comp_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, _) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => _) n]
    rfl

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The caps with shifted dots in terms of the dotted caps, for `N ≤ n`. -/
theorem rouqCaps_eq {N : ℕ} (hN : N ≤ n) (u : A → k) :
    rouqCaps L u N = capAll L n ≫ wMat b u n N := by
  refine Mat_.hom_ext _ _ fun a t => ?_
  rw [capAll_comp_apply]
  simp only [wMat, Linear.comp_smul, Category.comp_id]
  change R₁ a ◁ powComp (u a • 𝟙 (E₁ a) + x₁ a) t ≫ (adj₁ a).counit = _
  rw [whiskerLeft_powComp_shift, Fin.sum_univ_eq_sum_range
    (fun i => (((t : ℕ).choose i : k) * u a ^ ((t : ℕ) - i)) • (L a).capD i) n]
  refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
  · simp only [Finset.mem_range] at hi ⊢; omega
  · simp only [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_smul]

end Bridge

/-! ### The labelwise inverses -/

section Phi

omit [AdditiveWhiskering B] in
theorem capP_comp_apply {M : Mat_ (b ⟶ b)} (g : oMat (𝟙 b) (Pos h) ⟶ M) (a : A) (m : M.ι) :
    (capP L ≫ g) a m = ∑ i : Fin (h a).toNat, (L a).capD i ≫ g ⟨a, i⟩ m := by
  rw [Mat_.comp_apply]
  simp only [capP, ite_comp, zero_comp]
  exact sum_sigma_ite a _

omit [AdditiveWhiskering B] in
theorem comp_cupM_apply {M : Mat_ (b ⟶ b)} (g : M ⟶ oMat (𝟙 b) (Neg h)) (m : M.ι) (c : A) :
    (g ≫ cupM L) m c = ∑ j : Fin (-h c).toNat, g m ⟨c, j⟩ ≫ (L c).cupD j := by
  rw [Mat_.comp_apply]
  simp only [cupM, comp_ite, comp_zero]
  exact sum_sigma_ite' c _

omit [AdditiveWhiskering B] in
theorem capNM_comp_apply {M : Mat_ (b ⟶ b)} (g : oMat (𝟙 b) (Neg h) ⟶ M) (c : A) (m : M.ι) :
    (capNM L ≫ g) c m = ∑ i : Fin (-h c).toNat, (L c).capN i ≫ g ⟨c, i⟩ m := by
  rw [Mat_.comp_apply]
  simp only [capNM, ite_comp, zero_comp]
  exact sum_sigma_ite c _

omit [AdditiveWhiskering B] in
theorem comp_cupNP_apply {M : Mat_ (b ⟶ b)} (g : M ⟶ oMat (𝟙 b) (Pos h)) (m : M.ι) (a : A) :
    (g ≫ cupNP L) m a = ∑ j : Fin (h a).toNat, g m ⟨a, j⟩ ≫ (L a).cupN j := by
  rw [Mat_.comp_apply]
  simp only [cupNP, comp_ite, comp_zero]
  exact sum_sigma_ite' a _

/-- The labelwise Rouquier maps `(σ, caps) : ⊞ Eₐ Fₐ ⊕ 1^{Neg} → ⊞ Fₐ Eₐ ⊕ 1^{Pos}` (Brundan
(1.8), (1.9) at every label). -/
def phiHom : objEF L ⊞ oMat (𝟙 b) (Neg h) ⟶ objFE L ⊞ oMat (𝟙 b) (Pos h) :=
  Biprod.ofComponents (sigD L) (capP L) (cupM L) 0

/-- The labelwise inverses. -/
def phiInv : objFE L ⊞ oMat (𝟙 b) (Pos h) ⟶ objEF L ⊞ oMat (𝟙 b) (Neg h) :=
  Biprod.ofComponents (-sigLD L) (capNM L) (cupNP L) 0

omit [AdditiveWhiskering B] in
theorem cupM_comp_apply {M : Mat_ (b ⟶ b)} (g : objFE L ⟶ M) (q : Neg h) (m : M.ι) :
    (cupM L ≫ g) q m = (L q.1).cupD q.2 ≫ g q.1 m := by
  rw [Mat_.comp_apply, Finset.sum_eq_single q.1]
  · simp [cupM]
  · intro c _ hc; simp [cupM, Ne.symm hc]
  · simp

omit [AdditiveWhiskering B] in
theorem cupNP_comp_apply {M : Mat_ (b ⟶ b)} (g : objEF L ⟶ M) (p : Pos h) (m : M.ι) :
    (cupNP L ≫ g) p m = (L p.1).cupN p.2 ≫ g p.1 m := by
  rw [Mat_.comp_apply, Finset.sum_eq_single p.1]
  · simp [cupNP]
  · intro c _ hc; simp [cupNP, Ne.symm hc]
  · simp

theorem mat_zero_apply {D : Type*} [Category D] [Preadditive D] {M N : Mat_ D} (i : M.ι)
    (j : N.ι) : (0 : M ⟶ N) i j = 0 := rfl

theorem mat_neg_apply {D : Type*} [Category D] [Preadditive D] {M N : Mat_ D} (f : M ⟶ N)
    (i : M.ι) (j : N.ι) : (-f) i j = -(f i j) := rfl

omit [AdditiveWhiskering B] in
theorem phiHom_phiInv : phiHom L ≫ phiInv L = 𝟙 _ := by
  rw [phiHom, phiInv, Biprod.ofComponents_comp, ← Biprod.ofComponents_id]
  congr 1
  · rw [Preadditive.comp_neg, sigD, sigLD, diagMat_comp_diagMat, ← diagMat_neg]
    refine Mat_.hom_ext _ _ fun a c => ?_
    rw [Mat_.add_apply, capP_comp_apply]
    simp only [cupNP, diagMat]
    by_cases hac : a = c
    · subst hac
      simp only [dite_true, eqToHom_refl, Category.comp_id, ite_true, Mat_.id_apply_self,
        sig_sigL_eq (L a), Fin.sum_univ_eq_sum_range (fun m => (L a).capD m ≫ (L a).cupN m)]
      abel
    · simp [hac, Mat_.id_apply_of_ne _ _ _ hac]
  · rw [Limits.comp_zero, add_zero]
    refine Mat_.hom_ext _ _ fun a q => ?_
    rw [sigD, diagMat_comp_apply, mat_zero_apply]
    simp only [capNM]
    split_ifs with haq
    · subst haq
      exact (L q.1).sig_capN (by have := q.2.2; omega) q.2.2
    · exact Limits.comp_zero
  · rw [Limits.zero_comp, add_zero, Preadditive.comp_neg]
    refine Mat_.hom_ext _ _ fun q c => ?_
    rw [mat_neg_apply, sigLD, comp_diagMat_apply, mat_zero_apply]
    simp only [cupM]
    split_ifs with hqc
    · subst hqc
      rw [(L q.1).cupD_sigL (by have := q.2.2; omega) q.2.2, neg_zero]
    · rw [Limits.zero_comp, neg_zero]
  · rw [Limits.zero_comp, add_zero]
    refine Mat_.hom_ext _ _ fun q q' => ?_
    rw [cupM_comp_apply, oMat_id_apply]
    obtain ⟨a, m⟩ := q
    obtain ⟨a', m'⟩ := q'
    simp only [capNM]
    by_cases haa : a = a'
    · subst haa
      rw [ite_eq_left rfl, (L a).cupD_capN (by have := m.2; omega) m.2 m'.2]
      simp [Fin.val_inj]
    · simp [haa]

omit [AdditiveWhiskering B] in
theorem sigLD_sigD : (-sigLD L) ≫ sigD L + capNM L ≫ cupM L = 𝟙 _ := by
  rw [Preadditive.neg_comp, sigD, sigLD, diagMat_comp_diagMat, ← diagMat_neg]
  refine Mat_.hom_ext _ _ fun a c => ?_
  rw [Mat_.add_apply, capNM_comp_apply]
  simp only [cupM, diagMat]
  by_cases hac : a = c
  · subst hac
    simp only [dite_true, eqToHom_refl, Category.comp_id, ite_true, Mat_.id_apply_self,
      sigL_sig_eq (L a), Fin.sum_univ_eq_sum_range (fun m => (L a).capN m ≫ (L a).cupD m)]
    abel
  · simp [hac, Mat_.id_apply_of_ne _ _ _ hac]

omit [AdditiveWhiskering B] in
theorem cupNP_sigD : cupNP L ≫ sigD L = 0 := by
  refine Mat_.hom_ext _ _ fun p c => ?_
  rw [sigD, comp_diagMat_apply, mat_zero_apply]
  simp only [cupNP]
  split_ifs with hpc
  · subst hpc
    exact (L p.1).cupN_sig (by have := p.2.2; omega) p.2.2
  · exact Limits.zero_comp

omit [AdditiveWhiskering B] in
theorem phiInv_phiHom : phiInv L ≫ phiHom L = 𝟙 _ := by
  rw [phiHom, phiInv, Biprod.ofComponents_comp, ← Biprod.ofComponents_id]
  congr 1
  · exact sigLD_sigD L
  · rw [Limits.comp_zero, add_zero, Preadditive.neg_comp]
    refine Mat_.hom_ext _ _ fun c p => ?_
    rw [mat_neg_apply, sigLD, diagMat_comp_apply, mat_zero_apply]
    simp only [capP]
    split_ifs with hcp
    · subst hcp
      rw [(L p.1).sigL_capD (by have := p.2.2; omega) p.2.2, neg_zero]
    · rw [Limits.comp_zero, neg_zero]
  · rw [Limits.zero_comp, add_zero]
    exact cupNP_sigD L
  · rw [Limits.zero_comp, add_zero]
    refine Mat_.hom_ext _ _ fun p p' => ?_
    rw [cupNP_comp_apply, oMat_id_apply]
    obtain ⟨a, m⟩ := p
    obtain ⟨a', m'⟩ := p'
    simp only [capP]
    by_cases haa : a = a'
    · subst haa
      rw [ite_eq_left rfl, (L a).cupN_capD (by have := m.2; omega) m.2 m'.2]
      simp [Fin.val_inj]
    · simp [haa]

instance isIso_phiInv : IsIso (phiInv L) := ⟨⟨phiHom L, phiInv_phiHom L, phiHom_phiInv L⟩⟩

end Phi

/-! ### Gaussian elimination -/

section Main

attribute [local instance] endIdCommRing

omit [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B] in
theorem endId_hcomm (f g : (𝟙 b : b ⟶ b) ⟶ 𝟙 b) : f ≫ g = g ≫ f := Bicategory.endId_comm f g

omit [AdditiveWhiskering B] in
theorem cupAll_comp_apply {n : ℕ} {M : Mat_ (b ⟶ b)} (g : objFE L ⟶ M) (q : A × Fin n)
    (m : M.ι) : (cupAll L n ≫ g) q m = (L q.1).cupD q.2 ≫ g q.1 m := by
  rw [Mat_.comp_apply, Finset.sum_eq_single q.1]
  · simp [cupAll]
  · intro c _ hc; simp [cupAll, Ne.symm hc]
  · simp

/-- The closed diagrams `cupD j ∘ σ' ∘ capD i` of one label. -/
def gam (n : ℕ) : oMat (𝟙 b) (A × Fin n) ⟶ oMat (𝟙 b) (A × Fin n) :=
  cupAll L n ≫ (-sigLD L) ≫ capAll L n

/-- The closed diagrams `cupN m ∘ capD i` of one label. -/
def bet (n : ℕ) : oMat (𝟙 b) (Pos h) ⟶ oMat (𝟙 b) (A × Fin n) :=
  cupNP L ≫ capAll L n

/-- The closed diagrams `cupD j ∘ capN m` of one label. -/
def gamM (n : ℕ) : oMat (𝟙 b) (A × Fin n) ⟶ oMat (𝟙 b) (Neg h) :=
  cupAll L n ≫ capNM L

variable {n : ℕ} (hx₁ : ∀ a, powComp (x₁ a) n = 0) (hx₂ : ∀ a, powComp (x₂ a) n = 0)

include hx₁ hx₂ in
theorem matNil_gam : MatNil (oMat.toMatrix (gam L n)) := by
  intro q q'
  rw [mem_nilradical]
  change IsNilpotent (R := End (𝟙 b)) ((cupAll L n ≫ (-sigLD L) ≫ capAll L n) q q')
  rw [cupAll_comp_apply, Preadditive.neg_comp, mat_neg_apply, sigLD, diagMat_comp_apply]
  simp only [capAll]
  split_ifs with hq
  · rw [Preadditive.comp_neg]
    exact ((L q.1).cupD_sigL_capD_isNilpotent (hx₁ _) (hx₂ _) q.2 q'.2).neg
  · simp only [Limits.comp_zero, neg_zero]
    exact IsNilpotent.zero

variable (hn : ∀ a, (h a).natAbs ≤ n)

/-- `(a, m) ↦ (a, m)`, from the caps of the labelwise inverses to all caps. -/
def embP (p : Pos h) : A × Fin n :=
  (p.1, ⟨p.2, by have := p.2.2; have := hn p.1; omega⟩)

/-- `(a, m) ↦ (a, m)`, from the cups of the labelwise inverses to all cups. -/
def embN (r : Neg h) : A × Fin n :=
  (r.1, ⟨r.2, by have := r.2.2; have := hn r.1; omega⟩)

variable (b) in
/-- The Kronecker matrix of `embP`. -/
def matB0 : Matrix (Pos h) (A × Fin n) (End (𝟙 b)) :=
  Matrix.of fun p q => if q = embP hn p then 1 else 0

variable (b) in
/-- The Kronecker matrix of `embN`. -/
def matE0 : Matrix (A × Fin n) (Neg h) (End (𝟙 b)) :=
  Matrix.of fun q r => if q = embN hn r then 1 else 0

include hx₁ hx₂ in
theorem nilEq_bet : NilEq (oMat.toMatrix (bet L n)) (matB0 b hn) := by
  intro p q
  rw [mem_nilradical]
  change IsNilpotent (R := End (𝟙 b)) ((show End (𝟙 b) from (cupNP L ≫ capAll L n) p q) - _)
  rw [cupNP_comp_apply]
  obtain ⟨a, m⟩ := p
  obtain ⟨a', i⟩ := q
  simp only [capAll, matB0, Matrix.of_apply]
  by_cases haa : a = a'
  · subst haa
    have hc : ((a, i) = embP hn ⟨a, m⟩) ↔ (m : ℕ) = i := by
      simp [embP, Prod.ext_iff, Fin.ext_iff, eq_comm]
    simp only [ite_true, hc]
    exact (L a).cupN_capD_sub_isNilpotent (hx₁ _) (hx₂ _) m.2 i
  · have hc : ¬((a', i) = embP hn ⟨a, m⟩) := fun h' => haa (congrArg Prod.fst h').symm
    simp only [haa, hc, ite_false, sub_zero, Limits.comp_zero]
    exact (IsNilpotent.zero : IsNilpotent (0 : End (𝟙 b)))

include hx₁ hx₂ in
theorem nilEq_gamM : NilEq (oMat.toMatrix (gamM L n)) (matE0 b hn) := by
  intro q r
  rw [mem_nilradical]
  change IsNilpotent (R := End (𝟙 b)) ((show End (𝟙 b) from (cupAll L n ≫ capNM L) q r) - _)
  rw [cupAll_comp_apply]
  obtain ⟨a, j⟩ := q
  obtain ⟨a', m⟩ := r
  simp only [capNM, matE0, Matrix.of_apply]
  by_cases haa : a = a'
  · subst haa
    have hc : ((a, j) = embN hn ⟨a, m⟩) ↔ (j : ℕ) = m := by
      simp [embN, Prod.ext_iff, Fin.ext_iff]
    simp only [ite_true, hc]
    exact (L a).cupD_capN_sub_isNilpotent (hx₁ _) (hx₂ _) m.2 j
  · have hc : ¬((a, j) = embN hn ⟨a', m⟩) := fun h' => haa (congrArg Prod.fst h')
    simp only [haa, hc, ite_false, sub_zero, Limits.comp_zero]
    exact (IsNilpotent.zero : IsNilpotent (0 : End (𝟙 b)))

omit [AdditiveWhiskering B] in
theorem ofMatrix_comp_ofMatrix {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι κ (End (𝟙 b))) (M' : Matrix κ μ (End (𝟙 b))) :
    ofMatrix M ≫ ofMatrix M' = ofMatrix (M * M') :=
  hom_ext_toMatrix (by rw [oMat_comp_toMatrix endId_hcomm]; rfl)

omit [AdditiveWhiskering B] in
theorem ofMatrix_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    ofMatrix (1 : Matrix ι ι (End (𝟙 b))) = 𝟙 (oMat (𝟙 b) ι) :=
  hom_ext_toMatrix (by rw [toMatrix_id]; rfl)

omit [AdditiveWhiskering B] in
theorem ofMatrix_add {ι κ : Type} [Fintype ι] [Fintype κ] (M M' : Matrix ι κ (End (𝟙 b))) :
    ofMatrix (M + M') = ofMatrix M + ofMatrix M' := rfl

omit [AdditiveWhiskering B] in
theorem ofMatrix_zero {ι κ : Type} [Fintype ι] [Fintype κ] :
    ofMatrix (0 : Matrix ι κ (End (𝟙 b))) = 0 := rfl

omit [AdditiveWhiskering B] in
theorem isNilpotent_of_matNil {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : oMat (𝟙 b) ι ⟶ oMat (𝟙 b) ι) (hf : MatNil (oMat.toMatrix f)) :
    IsNilpotent (R := End (oMat (𝟙 b) ι)) f :=
  oMat_isNilpotent_of_entries endId_hcomm f fun i j => mem_nilradical.mp (hf i j)

omit [AdditiveWhiskering B] in
/-- A morphism congruent, modulo matrices with nilpotent entries, to an invertible matrix is
invertible. -/
theorem isIso_of_nilEq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : oMat (𝟙 b) ι ⟶ oMat (𝟙 b) κ) {C : Matrix ι κ (End (𝟙 b))}
    {Dm : Matrix κ ι (End (𝟙 b))} (hCD : C * Dm = 1) (hDC : Dm * C = 1)
    (hf : NilEq (oMat.toMatrix f) C) : IsIso f := by
  have hcd : ofMatrix C ≫ ofMatrix Dm = 𝟙 _ := by rw [ofMatrix_comp_ofMatrix, hCD, ofMatrix_one]
  have hdc : ofMatrix Dm ≫ ofMatrix C = 𝟙 _ := by rw [ofMatrix_comp_ofMatrix, hDC, ofMatrix_one]
  have : IsIso (ofMatrix C) := ⟨⟨ofMatrix Dm, hcd, hdc⟩⟩
  have hnil : IsNilpotent (R := End (oMat (𝟙 b) ι)) ((f - ofMatrix C) ≫ ofMatrix Dm) :=
    isNilpotent_of_matNil _ (by
      rw [oMat_comp_toMatrix endId_hcomm, toMatrix_sub, toMatrix_ofMatrix, toMatrix_ofMatrix]
      exact MatNil.mul_right hf _)
  have := isIso_id_add_of_isNilpotent _ hnil
  have e : f = (𝟙 _ + (f - ofMatrix C) ≫ ofMatrix Dm) ≫ ofMatrix C := by
    rw [Preadditive.add_comp, Category.id_comp, Category.assoc, hdc, Category.comp_id,
      add_sub_cancel]
  rw [e]
  infer_instance

variable (b) in
/-- `o^{⊕ ι} ⊞ o^{⊕ κ} ≅ o^{⊕ (ι ⊕ κ)}`. -/
def sumIso (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    oMat (𝟙 b) ι ⊞ oMat (𝟙 b) κ ≅ oMat (𝟙 b) (ι ⊕ κ) where
  hom := biprod.desc (ofMatrix (Matrix.fromCols 1 0)) (ofMatrix (Matrix.fromCols 0 1))
  inv := biprod.lift (ofMatrix (Matrix.fromRows 1 0)) (ofMatrix (Matrix.fromRows 0 1))
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [ofMatrix_comp_ofMatrix, Matrix.fromCols_mul_fromRows, ofMatrix_one,
      ofMatrix_zero]
  inv_hom_id := by
    rw [biprod.lift_desc, ofMatrix_comp_ofMatrix, ofMatrix_comp_ofMatrix, ← ofMatrix_add,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add]
    simp [Matrix.fromBlocks_one, ofMatrix_one]

omit [AdditiveWhiskering B] in
theorem matB0_mul_apply {μ : Type*} (X : Matrix (A × Fin n) μ (End (𝟙 b))) (p : Pos h) (y : μ) :
    (matB0 b hn * X : Matrix (Pos h) μ (End (𝟙 b))) p y = X (embP hn p) y := by
  simp [Matrix.mul_apply, matB0]

omit [AdditiveWhiskering B] in
theorem mul_matE0_apply {μ : Type*} [Fintype μ] (X : Matrix μ (A × Fin n) (End (𝟙 b))) (x : μ)
    (r : Neg h) : (X * matE0 b hn : Matrix μ (Neg h) (End (𝟙 b))) x r = X x (embN hn r) := by
  simp [Matrix.mul_apply, matE0]

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The constant part of the Schur complement is the partial-fraction matrix. -/
theorem schur_const_eq {N : ℕ} (u : A → k) :
    (matB0 b hn * (oMat.toMatrix (wMat b u n N) *
        (Matrix.fromCols 1 0 : Matrix (Fin N) (Fin N ⊕ Neg h) (End (𝟙 b)))) -
      matB0 b hn * (oMat.toMatrix (tel b u n) * ((1 : Matrix (A × Fin n) (A × Fin n) (End (𝟙 b))) *
        ((0 : Matrix (A × Fin n) (A × Fin n) (End (𝟙 b))) * (oMat.toMatrix (wMat b u n N) *
          (Matrix.fromCols 1 0 : Matrix (Fin N) (Fin N ⊕ Neg h) (End (𝟙 b)))) +
          matE0 b hn * (Matrix.fromCols 0 1 : Matrix (Neg h) (Fin N ⊕ Neg h) (End (𝟙 b)))))) :
        Matrix (Pos h) (Fin N ⊕ Neg h) (End (𝟙 b))) =
      (crtMatrix u (fun a => (h a).toNat) (fun a => (-h a).toNat) N).map
        (algebraMap k (End (𝟙 b))) := by
  simp only [Matrix.one_mul, Matrix.zero_mul, zero_add, Matrix.mul_fromCols, Matrix.mul_one,
    Matrix.mul_zero]
  ext p y
  rcases y with t | r
  · simp only [Matrix.sub_apply, Matrix.fromCols_apply_inl, Matrix.zero_apply, sub_zero,
      matB0_mul_apply, Matrix.map_apply, crtMatrix, Matrix.of_apply, Sum.elim_inl,
      Algebra.algebraMap_eq_smul_one]
    rfl
  · simp only [Matrix.sub_apply, Matrix.fromCols_apply_inr, Matrix.zero_apply, zero_sub,
      matB0_mul_apply, mul_matE0_apply, Matrix.map_apply, crtMatrix, Matrix.of_apply,
      Sum.elim_inr, Algebra.algebraMap_eq_smul_one]
    have hpr : p.1 ≠ r.1 := by
      obtain ⟨a, m⟩ := p
      obtain ⟨c, m'⟩ := r
      rintro (rfl : a = c)
      have := m.2
      have := m'.2
      omega
    change -(if p.1 = r.1 then 0 else _) = _
    rw [ite_eq_right hpr, neg_smul, neg_neg]
    rfl

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
include hx₁ hx₂ hn in
/-- **Block `(2)`, with teleporters**: for `∑ₐ h a ≥ 0`, the map
`(σ + cap ∘ teleporter ∘ cup, cap ∘ binomials) : ⊞ Eₐ Fₐ → ⊞ Fₐ Eₐ ⊕ 1^{⊕ N}` is invertible. -/
theorem isIso_lift_teleporter {u : A → k} (hu : Function.Injective u) (hN : 0 ≤ ∑ a, h a) :
    IsIso (biprod.lift (sigD L + capAll L n ≫ tel b u n ≫ cupAll L n)
      (capAll L n ≫ wMat b u n (∑ a, h a).toNat)) := by
  set N := (∑ a, h a).toNat with hNdef
  set T := tel b u n
  set W := wMat b u n N
  refine isIso_lift_of_isIso_ofComponents _ _ (cupM L) ?_
  suffices hΨ : IsIso (phiInv L ≫ Biprod.ofComponents (sigD L + capAll L n ≫ T ≫ cupAll L n)
      ((capAll L n ≫ W) ≫ biprod.inl) (cupM L) biprod.inr) from
    IsIso.of_isIso_comp_left (phiInv L) _
  have e11 : (-sigLD L) ≫ (sigD L + capAll L n ≫ T ≫ cupAll L n) + capNM L ≫ cupM L =
      𝟙 _ + ((-sigLD L) ≫ capAll L n) ≫ T ≫ cupAll L n := by
    rw [Preadditive.comp_add, add_right_comm, sigLD_sigD L, Category.assoc]
  have e12 : (-sigLD L) ≫ (capAll L n ≫ W) ≫ biprod.inl + capNM L ≫ biprod.inr =
      ((-sigLD L) ≫ capAll L n) ≫ W ≫ biprod.inl + capNM L ≫ biprod.inr := by
    simp only [Category.assoc]
  have e21 : cupNP L ≫ (sigD L + capAll L n ≫ T ≫ cupAll L n) + 0 ≫ cupM L =
      bet L n ≫ T ≫ cupAll L n := by
    rw [Limits.zero_comp, add_zero, Preadditive.comp_add, cupNP_sigD, zero_add, bet,
      Category.assoc]
  have e22 : cupNP L ≫ (capAll L n ≫ W) ≫ biprod.inl +
      (0 : oMat (𝟙 b) (Pos h) ⟶ oMat (𝟙 b) (Neg h)) ≫ biprod.inr =
      bet L n ≫ W ≫ biprod.inl := by
    rw [Limits.zero_comp, add_zero, bet]
    simp only [Category.assoc]
  rw [phiInv, Biprod.ofComponents_comp, e11, e12, e21, e22]
  -- the `(1,1)` block is unipotent
  have hgam := matNil_gam L hx₁ hx₂
  have hTgam : IsNilpotent (R := End (oMat (𝟙 b) (A × Fin n))) (T ≫ gam L n) :=
    isNilpotent_of_matNil _ (by
      rw [oMat_comp_toMatrix endId_hcomm]; exact MatNil.mul_left _ hgam)
  have hgamT : IsNilpotent (R := End (oMat (𝟙 b) (A × Fin n))) (gam L n ≫ T) :=
    isNilpotent_of_matNil _ (by
      rw [oMat_comp_toMatrix endId_hcomm]; exact MatNil.mul_right hgam _)
  have hΨ₁₁ : IsIso (𝟙 (objFE L) + ((-sigLD L) ≫ capAll L n) ≫ T ≫ cupAll L n) :=
    isIso_id_add_of_isNilpotent _ (isNilpotent_comp_swap _ (T ≫ cupAll L n) (by
      simpa only [gam, Category.assoc] using hTgam))
  have hG : IsIso (𝟙 _ + gam L n ≫ T) := isIso_id_add_of_isNilpotent _ hgamT
  refine isIso_ofComponents_of_isIso_schur _ _ _ _ ?_
  -- push the inverse of the `(1,1)` block through the cups
  have hpush : cupAll L n ≫ inv (𝟙 (objFE L) + ((-sigLD L) ≫ capAll L n) ≫ T ≫ cupAll L n) =
      inv (𝟙 _ + gam L n ≫ T) ≫ cupAll L n := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      gam, Category.assoc]
  have hS : bet L n ≫ W ≫ biprod.inl - (bet L n ≫ T ≫ cupAll L n) ≫
      inv (𝟙 (objFE L) + ((-sigLD L) ≫ capAll L n) ≫ T ≫ cupAll L n) ≫
        (((-sigLD L) ≫ capAll L n) ≫ W ≫ biprod.inl + capNM L ≫ biprod.inr) =
      bet L n ≫ W ≫ biprod.inl - bet L n ≫ T ≫ inv (𝟙 _ + gam L n ≫ T) ≫
        (gam L n ≫ W ≫ biprod.inl + gamM L n ≫ biprod.inr) := by
    simp only [Category.assoc]
    rw [reassoc_of% hpush]
    simp only [Preadditive.comp_add, gam, gamM, Category.assoc]
  rw [hS]
  -- pass to matrices
  rw [← isIso_comp_right_iff _ (sumIso b (Fin N) (Neg h)).hom]
  -- the inverse of the partial-fraction matrix
  have hdisj : ∀ a, (h a).toNat = 0 ∨ (-h a).toNat = 0 := fun a => by omega
  have hN' : ∑ a, (h a).toNat = N + ∑ a, (-h a).toNat := by
    have e : ∀ a, ((h a).toNat : ℤ) = h a + ((-h a).toNat : ℤ) := fun a => by omega
    zify
    rw [hNdef, Int.toNat_of_nonneg hN]
    simp only [e, Finset.sum_add_distrib]
  obtain ⟨Dk, hCD, hDC⟩ := crtMatrix_exists_inv (k := k) (u := u)
    (hp := fun a => (h a).toNat) (hn := fun a => (-h a).toNat) (N := N) hu hdisj hN'
  let φ := algebraMap k (End (𝟙 b))
  refine isIso_of_nilEq _ (C := (crtMatrix u (fun a => (h a).toNat) (fun a => (-h a).toNat) N).map φ)
    (Dm := Dk.map φ) (by rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero φ) (map_one φ)])
    (by rw [← Matrix.map_mul, hDC, Matrix.map_one _ (map_zero φ) (map_one φ)]) ?_
  rw [← schur_const_eq hn u]
  simp only [sumIso, Preadditive.sub_comp, Preadditive.add_comp, Category.assoc, biprod.inl_desc,
    biprod.inr_desc, toMatrix_sub, toMatrix_add, oMat_comp_toMatrix endId_hcomm, toMatrix_ofMatrix]
  -- the inverse of the unipotent block is congruent to `1`
  have hGi : NilEq (oMat.toMatrix (inv (𝟙 _ + gam L n ≫ T))) 1 := by
    have h1 := congrArg oMat.toMatrix (IsIso.inv_hom_id (𝟙 _ + gam L n ≫ T))
    rw [oMat_comp_toMatrix endId_hcomm, toMatrix_add, toMatrix_id,
      oMat_comp_toMatrix endId_hcomm] at h1
    rw [Matrix.mul_add, Matrix.mul_one] at h1
    have h2 : oMat.toMatrix (inv (𝟙 _ + gam L n ≫ T)) - 1 =
        -(oMat.toMatrix (inv (𝟙 _ + gam L n ≫ T)) *
          (oMat.toMatrix (gam L n) * oMat.toMatrix T)) :=
      eq_neg_of_add_eq_zero_left (by rw [sub_add_eq_add_sub, h1, sub_self])
    unfold NilEq
    rw [h2]
    exact MatNil.neg (MatNil.mul_left _ (MatNil.mul_right hgam _))
  have hgam0 : NilEq (oMat.toMatrix (gam L n)) 0 := by
    unfold NilEq; rw [sub_zero]; exact hgam
  have hB := nilEq_bet L hx₁ hx₂ hn
  have hE := nilEq_gamM L hx₁ hx₂ hn
  exact NilEq.sub (NilEq.mul hB (NilEq.refl _))
    (NilEq.mul hB (NilEq.mul (NilEq.refl _) (NilEq.mul hGi
      (NilEq.add (NilEq.mul hgam0 (NilEq.refl _)) (NilEq.mul hE (NilEq.refl _))))))

end Main


/-! ### The main theorem -/

section Theorem

theorem powComp_add_eq {D : Type*} [Category D] {X : D} (f : X ⟶ X) (i : ℕ) :
    ∀ j : ℕ, powComp f (i + j) = powComp f i ≫ powComp f j
  | 0 => by simp
  | j + 1 => by rw [← add_assoc, powComp_succ, powComp_add_eq f i j, powComp_succ, Category.assoc]

/-- **The block of Rouquier's map through the identity, `∑ₐ h a ≥ 0`** (the block-`(2)` part of KM3
for the coproduct of `sl₂` data: B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, Theorem `th:coproduct`; J. Brundan, A. Savage, B. Webster, arXiv:1812.03255v3,
§5, Theorem 5.4). Labels `a` carry Rouquier's data `L a` of weight `h a` at a common object `b`, with
nilpotent dots; the dots of label `a` are shifted by `u a`, the `u a` pairwise distinct; `δ a c`
(`a ≠ c`) is any inverse of the dumbbell `(u_c + y_c) - (u_a + x_a)` on `Eₐ E_c` (the
position-preserving component of the summed crossing). Then

  `(rouqSig, rouqCaps) : ⊞ₐ Eₐ Fₐ 1_b → ⊞ₐ Fₐ Eₐ 1_b ⊕ 1_b^{⊕ N}`,   `N = ∑ₐ h a`,

is invertible in the additive envelope `Mat_ (b ⟶ b)`. Proved by a matrix argument: Gaussian
elimination against the labelwise inverses reduces it to the partial-fraction matrix
`crtMatrix` modulo nilpotent closed diagrams. -/
theorem isIso_rouqMap_of_nonneg {n : ℕ} (hx₁ : ∀ a, powComp (x₁ a) n = 0)
    (hx₂ : ∀ a, powComp (x₂ a) n = 0) {u : A → k} (hu : Function.Injective u)
    (δ : ∀ a c, E₁ a ≫ E₂ c ⟶ E₁ a ≫ E₂ c)
    (hδ : ∀ a c, a ≠ c →
      δ a c ≫ ((u c - u a) • 𝟙 _ + E₁ a ◁ x₂ c - x₁ a ▷ E₂ c) = 𝟙 _)
    (hN : 0 ≤ ∑ a, h a) :
    IsIso (biprod.lift (rouqSig L δ) (rouqCaps L u (∑ a, h a).toNat)) := by
  set n' := n + ∑ a, (h a).natAbs
  have hx₁' : ∀ a, powComp (x₁ a) n' = 0 := fun a => by
    rw [powComp_add_eq, hx₁ a, Limits.zero_comp]
  have hx₂' : ∀ a, powComp (x₂ a) n' = 0 := fun a => by
    rw [powComp_add_eq, hx₂ a, Limits.zero_comp]
  have hn' : ∀ a, (h a).natAbs ≤ n' := fun a =>
    le_add_left (Finset.single_le_sum (f := fun a => (h a).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a))
  have hNn : (∑ a, h a).toNat ≤ n' := by
    have : ∑ a, h a ≤ ∑ a, ((h a).natAbs : ℤ) :=
      Finset.sum_le_sum fun a _ => Int.le_natAbs
    have h2 : ((∑ a, (h a).natAbs : ℕ) : ℤ) = ∑ a, ((h a).natAbs : ℤ) := by push_cast; rfl
    omega
  rw [rouqSig_eq L hx₁' hx₂' hu δ hδ, rouqCaps_eq L hNn u]
  exact isIso_lift_teleporter L hx₁' hx₂' hn' hu hN

end Theorem

end Setting

end RouqCoproduct

end Categorification.TwoRep
