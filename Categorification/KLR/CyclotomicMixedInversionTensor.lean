import Categorification.KLR.CyclotomicMixedInversionAffine
import Categorification.KLR.CyclotomicLower
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.Examples.Small

/-!
# Rectangular affine crossing over the actual lower coefficient algebra

The source is `R(γ+j)e(γ,j) ⊗_{R(γ)} e(γ,i)R(γ+i)`, with different
left and right coefficient algebras. Coefficient absorption removes the
redundant singleton and empty factors from the Mackey tensor; both inverse
identities are proved. The resulting full-corner equivalence has elementary
formula `x ⊗ y ↦ ι(x) ψ_{|γ|} ι(y)` and both coefficient linearities.
`tauEquiv` is the signed map with the source convention `τ = -ψ`.

Affine injectivity retains the integral-domain and nonzero factorization
hypotheses of the PBW theorem. The tensor comparison itself needs only a
commutative base. Cyclotomic quotient descent and comparison with the
adjunction-defined mixed mate are not established in this module.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.MixedAffine.Lower
open MulOpposite
open scoped TensorProduct
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (γ : Multiset I) (i j : I)

/-- First-factor inclusion in the actual lower coefficient algebra. -/
def inc (c : I) : KLRAlgebra k Q γ →ₙₐ[k] KLRAlgebra k Q (γ + {c}) where
  toFun a := concat Q γ {c} (a ⊗ₜ 1)
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.add_tmul]
  map_mul' a b := by rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_smul' a b := by simp [TensorProduct.smul_tmul]

abbrev Left := CornerTensor.Left (inc Q γ j)
abbrev Right := CornerTensor.Right (inc Q γ i) (AlgHom.id k _)
abbrev Source := BalancedTensor k (KLRAlgebra k Q (γ + {j}))
  (KLRAlgebra k Q γ) (Left Q γ j) (Right Q γ i)

theorem quadTop_one : quadTop (Q := Q) (crossingQuad γ i j) 1 =
    (inc Q γ j 1 : KLRAlgebra k Q (γ + {j})) ⊗ₜ (1 : KLRAlgebra k Q {i}) := by
  change quadTop (crossingQuad γ i j) ((1 ⊗ₜ 1) ⊗ₜ (1 ⊗ₜ 1)) = _
  rw [quadTop_tmul]
  change concat Q γ {j} (1 ⊗ₜ 1) ⊗ₜ
    castKLR Q (add_zero ({i} : Multiset I)) (concat Q {i} 0 (1 ⊗ₜ 1)) = _
  rw [concat_one_right]
  rfl

theorem quadBot_one : quadBot (Q := Q) (crossingQuad γ i j) 1 =
    (inc Q γ i 1 : KLRAlgebra k Q (γ + {i})) ⊗ₜ (1 : KLRAlgebra k Q {j}) := by
  change quadBot (crossingQuad γ i j) ((1 ⊗ₜ 1) ⊗ₜ (1 ⊗ₜ 1)) = _
  rw [quadBot_tmul]
  change concat Q γ {i} (1 ⊗ₜ 1) ⊗ₜ
    castKLR Q (add_zero ({j} : Multiset I)) (concat Q {j} 0 (1 ⊗ₜ 1)) = _
  rw [concat_one_right]
  rfl

/-- A genuine coefficient tensor, before adjoining the other singleton variable. -/
def topPure (x : Left Q γ j) (u : KLRAlgebra k Q {i}) :
    MackeyTop Q (crossingQuad γ i j) :=
  ⟨(x : KLRAlgebra k Q (γ + {j})) ⊗ₜ u, by
    change (_ ⊗ₜ _) * quadTop (crossingQuad γ i j) 1 = _
    rw [quadTop_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, CornerTensor.left_mem]⟩

def botPure (y : Right Q γ i) (v : KLRAlgebra k Q {j}) :
    MackeyBot Q (crossingQuad γ i j) :=
  ⟨(y : KLRAlgebra k Q (γ + {i})) ⊗ₜ v, by
    change quadBot (crossingQuad γ i j) 1 * (_ ⊗ₜ _) = _
    rw [quadBot_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (AlgHom.id k _ (inc Q γ i 1) * (y : KLRAlgebra k Q (γ + {i}))) ⊗ₜ _ = _
    rw [CornerTensor.right_mem]⟩

/-- The lower-rank balanced tensor maps into the four-block tensor. -/
def embedBil : Left Q γ j →ₗ[k] Right Q γ i →ₗ[k] MackeyX Q (crossingQuad γ i j) :=
  LinearMap.mk₂ k (fun x y => BalancedTensor.tmul (topPure Q γ i j x 1) (botPure Q γ i j y 1))
    (fun x x' y => by
      have ht : topPure Q γ i j (x + x') 1 = topPure Q γ i j x 1 + topPure Q γ i j x' 1 :=
        Subtype.ext (TensorProduct.add_tmul _ _ _)
      rw [ht, BalancedTensor.add_tmul])
    (fun c x y => by
      have ht : topPure Q γ i j (c • x) 1 = c • topPure Q γ i j x 1 :=
        Subtype.ext (TensorProduct.smul_tmul' _ _ _)
      rw [ht, BalancedTensor.smul_tmul])
    (fun x y y' => by
      have ht : botPure Q γ i j (y + y') 1 = botPure Q γ i j y 1 + botPure Q γ i j y' 1 :=
        Subtype.ext (TensorProduct.add_tmul _ _ _)
      rw [ht, BalancedTensor.tmul_add])
    (fun c x y => by
      have ht : botPure Q γ i j (c • y) 1 = c • botPure Q γ i j y 1 :=
        Subtype.ext (TensorProduct.smul_tmul' _ _ _)
      rw [ht, BalancedTensor.tmul_smul])

def quadElt (a : KLRAlgebra k Q γ) (v : KLRAlgebra k Q {j})
    (u : KLRAlgebra k Q {i}) : QuadAlg Q (crossingQuad γ i j) :=
  (a ⊗ₜ v) ⊗ₜ (u ⊗ₜ 1)

theorem quadTop_elt (a : KLRAlgebra k Q γ) (v : KLRAlgebra k Q {j})
    (u : KLRAlgebra k Q {i}) : quadTop (crossingQuad γ i j) (quadElt Q γ i j a v u) =
      concat Q γ {j} (a ⊗ₜ v) ⊗ₜ u := by
  change concat Q γ {j} (a ⊗ₜ v) ⊗ₜ
    castKLR Q (add_zero ({i} : Multiset I)) (concat Q {i} 0 (u ⊗ₜ 1)) = _
  rw [concat_one_right]

theorem quadBot_elt (a : KLRAlgebra k Q γ) (v : KLRAlgebra k Q {j})
    (u : KLRAlgebra k Q {i}) : quadBot (crossingQuad γ i j) (quadElt Q γ i j a v u) =
      concat Q γ {i} (a ⊗ₜ u) ⊗ₜ v := by
  change concat Q γ {i} (a ⊗ₜ u) ⊗ₜ
    castKLR Q (add_zero ({j} : Multiset I)) (concat Q {j} 0 (v ⊗ₜ 1)) = _
  rw [concat_one_right]

theorem embedBil_balanced (x : Left Q γ j) (a : KLRAlgebra k Q γ) (y : Right Q γ i) :
    embedBil Q γ i j (op a • x) y = embedBil Q γ i j x (a • y) := by
  have ht : topPure Q γ i j (op a • x) 1 =
      op (quadElt Q γ i j a 1 1) • topPure Q γ i j x 1 := by
    apply Subtype.ext
    change ((x : KLRAlgebra k Q (γ + {j})) * inc Q γ j a) ⊗ₜ 1 =
      (_ ⊗ₜ _) * quadTop (crossingQuad γ i j) (quadElt Q γ i j a 1 1)
    rw [quadTop_elt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  have hb : botPure Q γ i j (a • y) 1 =
      quadElt Q γ i j a 1 1 • botPure Q γ i j y 1 := by
    apply Subtype.ext
    change (inc Q γ i a * (y : KLRAlgebra k Q (γ + {i}))) ⊗ₜ 1 =
      quadBot (crossingQuad γ i j) (quadElt Q γ i j a 1 1) * (_ ⊗ₜ _)
    rw [quadBot_elt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  change BalancedTensor.tmul _ _ = BalancedTensor.tmul _ _
  rw [ht, hb, BalancedTensor.op_smul_tmul]

def embed : Source Q γ i j →ₗ[k] MackeyX Q (crossingQuad γ i j) :=
  BalancedTensor.lift (embedBil Q γ i j) (embedBil_balanced Q γ i j)

/-- Absorb the last singleton variable into the left coefficient factor. -/
def leftInsert : KLRAlgebra k Q (γ + {j}) →ₗ[k] KLRAlgebra k Q {j} →ₗ[k] Left Q γ j :=
  LinearMap.mk₂ k (fun x v => ⟨x * concat Q γ {j} (1 ⊗ₜ v), by
      change (x * concat Q γ {j} (1 ⊗ₜ v)) * concat Q γ {j} (1 ⊗ₜ 1) = _
      rw [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]⟩)
    (fun x x' v => Subtype.ext (add_mul _ _ _))
    (fun c x v => Subtype.ext (smul_mul_assoc _ _ _))
    (fun x v v' => Subtype.ext (by simp only [TensorProduct.tmul_add, map_add, mul_add]; rfl))
    (fun c x v => Subtype.ext (by simp only [TensorProduct.tmul_smul, map_smul, mul_smul_comm]; rfl))

/-- Absorb the other singleton variable into the right coefficient factor. -/
def rightInsert : KLRAlgebra k Q (γ + {i}) →ₗ[k] KLRAlgebra k Q {i} →ₗ[k] Right Q γ i :=
  LinearMap.mk₂ k (fun y u => ⟨concat Q γ {i} (1 ⊗ₜ u) * y, by
      change concat Q γ {i} (1 ⊗ₜ 1) * (concat Q γ {i} (1 ⊗ₜ u) * y) = _
      rw [← mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]⟩)
    (fun y y' u => Subtype.ext (mul_add _ _ _))
    (fun c y u => Subtype.ext (mul_smul_comm _ _ _))
    (fun y u u' => Subtype.ext (by simp only [TensorProduct.tmul_add, map_add, add_mul]; rfl))
    (fun c y u => Subtype.ext (by simp only [TensorProduct.tmul_smul, map_smul, smul_mul_assoc]; rfl))

local notation "A" => KLRAlgebra k Q (γ + Multiset.cons j 0)
local notation "C" => KLRAlgebra k Q (γ + Multiset.cons i 0)
local notation "Ji" => KLRAlgebra k Q (Multiset.cons i 0)
local notation "Jj" => KLRAlgebra k Q (Multiset.cons j 0)

/-- Coefficient absorption on the ambient tensor factors. -/
def absorbTensor : (A ⊗[k] Ji) ⊗[k] (C ⊗[k] Jj) →ₗ[k] Source Q γ i j :=
  ((BalancedTensor.mk k A (KLRAlgebra k Q γ) (Left Q γ j) (Right Q γ i)).restrictScalars k) ∘ₗ
    TensorProduct.map (TensorProduct.lift (leftInsert Q γ j))
      (TensorProduct.lift (rightInsert Q γ i)) ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.comm k Ji C).toLinearMap ∘ₗ
    (TensorProduct.tensorTensorTensorComm k A Ji Jj C).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.comm k C Jj).toLinearMap

def absorbBil : (A ⊗[k] Ji) →ₗ[k] (C ⊗[k] Jj) →ₗ[k] Source Q γ i j :=
  TensorProduct.curry (absorbTensor Q γ i j)

theorem absorbBil_tmul (x : A) (u : Ji) (y : C) (v : Jj) :
    absorbBil Q γ i j (x ⊗ₜ u) (y ⊗ₜ v) =
      BalancedTensor.tmul (leftInsert Q γ j x v) (rightInsert Q γ i y u) := rfl

theorem absorbBil_balance_pure (x : A) (u : Ji) (y : C) (v : Jj)
    (a : KLRAlgebra k Q γ) (b : Jj) (c : Ji) :
    absorbBil Q γ i j ((x ⊗ₜ u) * quadTop (crossingQuad γ i j) (quadElt Q γ i j a b c))
      (y ⊗ₜ v) =
    absorbBil Q γ i j (x ⊗ₜ u)
      (quadBot (crossingQuad γ i j) (quadElt Q γ i j a b c) * (y ⊗ₜ v)) := by
  rw [quadTop_elt, quadBot_elt, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, absorbBil_tmul, absorbBil_tmul]
  have hl : leftInsert Q γ j (x * concat Q γ {j} (a ⊗ₜ b)) v =
      op a • leftInsert Q γ j x (b * v) := by
    apply Subtype.ext
    change (x * concat Q γ {j} (a ⊗ₜ b)) * concat Q γ {j} (1 ⊗ₜ v) =
      (x * concat Q γ {j} (1 ⊗ₜ (b * v))) * concat Q γ {j} (a ⊗ₜ 1)
    simp only [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hr : rightInsert Q γ i (concat Q γ {i} (a ⊗ₜ c) * y) u =
      a • rightInsert Q γ i y (u * c) := by
    apply Subtype.ext
    change concat Q γ {i} (1 ⊗ₜ u) * (concat Q γ {i} (a ⊗ₜ c) * y) =
      concat Q γ {i} (a ⊗ₜ 1) * (concat Q γ {i} (1 ⊗ₜ (u * c)) * y)
    simp only [← mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hl, hr, BalancedTensor.op_smul_tmul]

theorem absorbBil_balance_elt (t : A ⊗[k] Ji) (s : C ⊗[k] Jj)
    (a : KLRAlgebra k Q γ) (b : Jj) (c : Ji) :
    absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) (quadElt Q γ i j a b c)) s =
    absorbBil Q γ i j t (quadBot (crossingQuad γ i j) (quadElt Q γ i j a b c) * s) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [add_mul, map_add, LinearMap.add_apply, ht, ht']
  | tmul x u =>
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [mul_add, map_add, hs, hs']
    | tmul y v => exact absorbBil_balance_pure Q γ i j x u y v a b c

theorem absorbBil_balanced (t : A ⊗[k] Ji) (r : QuadAlg Q (crossingQuad γ i j))
    (s : C ⊗[k] Jj) :
    absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) r) s =
    absorbBil Q γ i j t (quadBot (crossingQuad γ i j) r * s) := by
  have hadd (r r' : QuadAlg Q (crossingQuad γ i j))
      (hr : absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) r) s =
        absorbBil Q γ i j t (quadBot (crossingQuad γ i j) r * s))
      (hr' : absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) r') s =
        absorbBil Q γ i j t (quadBot (crossingQuad γ i j) r' * s)) :
      absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) (r + r')) s =
        absorbBil Q γ i j t (quadBot (crossingQuad γ i j) (r + r') * s) := by
    simp only [map_add, mul_add, add_mul, LinearMap.add_apply, hr, hr']
  have hsmul (e : k) (r : QuadAlg Q (crossingQuad γ i j))
      (hr : absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) r) s =
        absorbBil Q γ i j t (quadBot (crossingQuad γ i j) r * s)) :
      absorbBil Q γ i j (t * quadTop (crossingQuad γ i j) (e • r)) s =
        absorbBil Q γ i j t (quadBot (crossingQuad γ i j) (e • r) * s) := by
    simpa only [map_smul, mul_smul_comm, smul_mul_assoc, LinearMap.smul_apply] using congrArg (e • ·) hr
  dsimp only [crossingQuad] at r ⊢
  induction r using TensorProduct.inductionOn with
  | add r r' hr hr' => exact hadd r r' hr hr'
  | tmul ab cd =>
    induction ab using TensorProduct.inductionOn with
    | add ab ab' hb hb' =>
      rw [TensorProduct.add_tmul]
      exact hadd _ _ hb hb'
    | tmul a b =>
      induction cd using TensorProduct.inductionOn with
      | add cd cd' hd hd' =>
        rw [TensorProduct.tmul_add]
        exact hadd _ _ hd hd'
      | tmul c d =>
        obtain ⟨e, rfl⟩ := (zeroEquiv (Q := Q)).symm.surjective d
        rw [zeroEquiv_symm_apply, Algebra.algebraMap_eq_smul_one]
        have he : (a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] (e • (1 : KLRAlgebra k Q 0))) =
            e • ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] (1 : KLRAlgebra k Q 0))) := by
          rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
        rw [he]
        exact hsmul e (quadElt Q γ i j a b c) (absorbBil_balance_elt Q γ i j t s a b c)

def absorb : MackeyX Q (crossingQuad γ i j) →ₗ[k] Source Q γ i j :=
  BalancedTensor.lift
    ((absorbBil Q γ i j).comp
      ((Graded.leftIdeal (quadTop (Q := Q) (crossingQuad γ i j) 1)).subtype.restrictScalars k)
      |>.compl₂ (quadBotSub Q (crossingQuad γ i j)).subtype)
    (fun t r b => absorbBil_balanced Q γ i j t r b)

theorem absorb_tmul (t : MackeyTop Q (crossingQuad γ i j))
    (b : MackeyBot Q (crossingQuad γ i j)) :
    absorb Q γ i j (BalancedTensor.tmul t b) = absorbBil Q γ i j t b := rfl

theorem absorb_embed (z : Source Q γ i j) : absorb Q γ i j (embed Q γ i j z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    change absorbBil Q γ i j ((x : A) ⊗ₜ 1) ((y : C) ⊗ₜ 1) = _
    rw [absorbBil_tmul]
    have hx : leftInsert Q γ j x 1 = x := Subtype.ext (CornerTensor.left_mem _ x)
    have hy : rightInsert Q γ i y 1 = y := Subtype.ext (CornerTensor.right_mem _ _ y)
    rw [hx, hy]

theorem pure_absorption (x : Left Q γ j) (u : Ji) (y : Right Q γ i) (v : Jj) :
    BalancedTensor.tmul (topPure Q γ i j x u) (botPure Q γ i j y v) =
      embed Q γ i j (BalancedTensor.tmul (leftInsert Q γ j x v) (rightInsert Q γ i y u)) := by
  have ht : topPure Q γ i j x u =
      op (quadElt Q γ i j 1 1 u) • topPure Q γ i j x 1 := by
    apply Subtype.ext
    change (x : A) ⊗ₜ u = (_ ⊗ₜ _) * quadTop (crossingQuad γ i j) (quadElt Q γ i j 1 1 u)
    rw [quadTop_elt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (x : A) ⊗ₜ u = ((x : A) * inc Q γ j 1) ⊗ₜ u
    rw [CornerTensor.left_mem]
  have hb : quadElt Q γ i j 1 1 u • botPure Q γ i j y v =
      quadElt Q γ i j 1 v 1 • botPure Q γ i j (rightInsert Q γ i y u) 1 := by
    apply Subtype.ext
    change quadBot (crossingQuad γ i j) (quadElt Q γ i j 1 1 u) * (_ ⊗ₜ _) =
      quadBot (crossingQuad γ i j) (quadElt Q γ i j 1 v 1) * (_ ⊗ₜ _)
    rw [quadBot_elt, quadBot_elt, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    change (rightInsert Q γ i y u : C) ⊗ₜ v =
      (AlgHom.id k C (inc Q γ i 1) * (rightInsert Q γ i y u : C)) ⊗ₜ v
    rw [CornerTensor.right_mem]
  have hv : op (quadElt Q γ i j 1 v 1) • topPure Q γ i j x 1 =
      topPure Q γ i j (leftInsert Q γ j x v) 1 := by
    apply Subtype.ext
    change (_ ⊗ₜ _) * quadTop (crossingQuad γ i j) (quadElt Q γ i j 1 v 1) = _
    rw [quadTop_elt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  rw [ht, BalancedTensor.op_smul_tmul, hb, ← BalancedTensor.op_smul_tmul, hv]
  rfl

def topProj : A ⊗[k] Ji →ₗ[k] MackeyTop Q (crossingQuad γ i j) where
  toFun t := ⟨t * quadTop (crossingQuad γ i j) 1, by
    change (_ * _) * _ = _
    rw [mul_assoc, quadTop_mul_one]⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

def botProj : C ⊗[k] Jj →ₗ[k] MackeyBot Q (crossingQuad γ i j) where
  toFun b := ⟨quadBot (crossingQuad γ i j) 1 * b, by
    change _ * (_ * _) = _
    rw [← mul_assoc, quadBot_one_mul]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

theorem topProj_tmul (x : A) (u : Ji) : topProj Q γ i j (x ⊗ₜ u) =
    topPure Q γ i j (leftInsert Q γ j x 1) u := by
  apply Subtype.ext
  change (x ⊗ₜ u) * quadTop (crossingQuad γ i j) 1 =
    (x * concat Q γ {j} (1 ⊗ₜ 1)) ⊗ₜ u
  rw [quadTop_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

theorem botProj_tmul (y : C) (v : Jj) : botProj Q γ i j (y ⊗ₜ v) =
    botPure Q γ i j (rightInsert Q γ i y 1) v := by
  apply Subtype.ext
  change quadBot (crossingQuad γ i j) 1 * (_ ⊗ₜ _) = _
  rw [quadBot_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem embed_absorb (z : MackeyX Q (crossingQuad γ i j)) : embed Q γ i j (absorb Q γ i j z) = z := by
  have hproj (t : A ⊗[k] Ji) (b : C ⊗[k] Jj) :
      embed Q γ i j (absorb Q γ i j
        (BalancedTensor.tmul (topProj Q γ i j t) (botProj Q γ i j b))) =
      BalancedTensor.tmul (topProj Q γ i j t) (botProj Q γ i j b) := by
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, BalancedTensor.add_tmul, ht, ht']
    | tmul x u =>
      induction b using TensorProduct.inductionOn with
      | add b b' hb hb' => simp only [map_add, BalancedTensor.tmul_add, hb, hb']
      | tmul y v =>
        rw [topProj_tmul, botProj_tmul, absorb_tmul]
        change embed Q γ i j (absorbBil Q γ i j (_ ⊗ₜ u) (_ ⊗ₜ v)) = _
        rw [absorbBil_tmul]
        exact (pure_absorption Q γ i j _ u _ v).symm
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul t b =>
    have ht : topProj Q γ i j t = t := Subtype.ext t.2
    have hb : botProj Q γ i j b = b := Subtype.ext b.2
    simpa only [ht, hb] using hproj t b

/-- Removal of the redundant singleton and empty factors, with both inverses proved. -/
def sourceEquiv : Source Q γ i j ≃ₗ[k] MackeyX Q (crossingQuad γ i j) :=
  { embed Q γ i j with
    invFun := absorb Q γ i j
    left_inv := absorb_embed Q γ i j
    right_inv := embed_absorb Q γ i j }

theorem embed_left (a : A) (z : Source Q γ i j) :
    embed Q γ i j (a • z) = (a ⊗ₜ 1 : TensorKLR Q (γ + {j}) {i}) • embed Q γ i j z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
  | tmul x y =>
    rw [BalancedTensor.smul_tmul']
    change BalancedTensor.tmul (topPure Q γ i j (a • x) 1) _ =
      (a ⊗ₜ 1 : TensorKLR Q (γ + {j}) {i}) • BalancedTensor.tmul (topPure Q γ i j x 1) _
    rw [BalancedTensor.smul_tmul']
    congr 1
    apply Subtype.ext
    change (a * (x : A)) ⊗ₜ 1 = (a ⊗ₜ 1) * ((x : A) ⊗ₜ 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def rightMul (a : C) : Right Q γ i →ₗ[KLRAlgebra k Q γ] Right Q γ i where
  toFun y := ⟨y * a, by
    change inc Q γ i 1 * ((y : C) * a) = _
    rw [← mul_assoc]
    exact congrArg (· * a) (CornerTensor.right_mem (inc Q γ i) (AlgHom.id k C) y)⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _)

def rightAct (a : C) : Source Q γ i j →ₗ[A] Source Q γ i j :=
  BalancedTensor.mapRight (rightMul Q γ i a)

theorem embed_right (a : C) (z : Source Q γ i j) :
    embed Q γ i j (rightAct Q γ i j a z) =
      MackeyX.rightAct (q := crossingQuad γ i j) (a ⊗ₜ 1) (embed Q γ i j z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    change BalancedTensor.tmul (topPure Q γ i j x 1) (botPure Q γ i j (rightMul Q γ i a y) 1) =
      BalancedTensor.tmul (topPure Q γ i j x 1) (botRMul (q := crossingQuad γ i j) (a ⊗ₜ 1)
        (botPure Q γ i j y 1))
    congr 1
    apply Subtype.ext
    change ((y : C) * a) ⊗ₜ 1 = ((y : C) ⊗ₜ 1) * (a ⊗ₜ 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- The actual rectangular affine Mackey equivalence, balanced over `R(γ)` alone. -/
def affineEquiv (hij : i ≠ j) : Source Q γ i j ≃ₗ[k] bimod Q (weightSquare γ i j) :=
  (sourceEquiv Q γ i j).trans (crossingEquiv γ i j hPQ hP hij)

theorem affineEquiv_tmul (hij : i ≠ j) (x : Left Q γ j) (y : Right Q γ i) :
    (affineEquiv Q γ i j hPQ hP hij (BalancedTensor.tmul x y) : KLRAlgebra k Q ((γ + {j}) + {i})) =
      concat Q (γ + {j}) {i} ((x : A) ⊗ₜ 1) * ψ (Multiset.card γ) *
        botConcat Q (weightSquare γ i j) ((y : C) ⊗ₜ 1) :=
  crossingEquiv_tmul γ i j hPQ hP hij _ _

theorem affineEquiv_left (hij : i ≠ j) (a : A) (z : Source Q γ i j) :
    (affineEquiv Q γ i j hPQ hP hij (a • z) : KLRAlgebra k Q ((γ + {j}) + {i})) =
      concat Q (γ + {j}) {i} (a ⊗ₜ 1) * affineEquiv Q γ i j hPQ hP hij z := by
  change (crossingEquiv γ i j hPQ hP hij (embed Q γ i j (a • z)) : KLRAlgebra k Q ((γ + {j}) + {i})) = _
  rw [embed_left, crossingEquiv_left]
  rfl

theorem affineEquiv_right (hij : i ≠ j) (a : C) (z : Source Q γ i j) :
    (affineEquiv Q γ i j hPQ hP hij (rightAct Q γ i j a z) : KLRAlgebra k Q ((γ + {j}) + {i})) =
      affineEquiv Q γ i j hPQ hP hij z * botConcat Q (weightSquare γ i j) (a ⊗ₜ 1) := by
  change (crossingEquiv γ i j hPQ hP hij (embed Q γ i j (rightAct Q γ i j a z)) : KLRAlgebra k Q ((γ + {j}) + {i})) = _
  rw [embed_right, crossingEquiv_right]
  rfl

/-- The source convention `τ = -ψ`, not an unspecified isomorphism. -/
def tauEquiv (hij : i ≠ j) : Source Q γ i j ≃ₗ[k] bimod Q (weightSquare γ i j) :=
  (affineEquiv Q γ i j hPQ hP hij).trans (LinearEquiv.neg k)

theorem tauEquiv_tmul (hij : i ≠ j) (x : Left Q γ j) (y : Right Q γ i) :
    (tauEquiv Q γ i j hPQ hP hij (BalancedTensor.tmul x y) : KLRAlgebra k Q ((γ + {j}) + {i})) =
      concat Q (γ + {j}) {i} ((x : A) ⊗ₜ 1) * (-ψ (Multiset.card γ)) *
        botConcat Q (weightSquare γ i j) ((y : C) ⊗ₜ 1) := by
  change -(affineEquiv Q γ i j hPQ hP hij (BalancedTensor.tmul x y) : KLRAlgebra k Q ((γ + {j}) + {i})) = _
  rw [affineEquiv_tmul, mul_neg, neg_mul]

/-- Left multiplication by the actual left coefficient algebra on the corner. -/
def cornerLeft (a : A) (z : bimod Q (weightSquare γ i j)) : bimod Q (weightSquare γ i j) :=
  ⟨concat Q (γ + {j}) {i} (a ⊗ₜ 1) * z,
    concat_mul_mem_bimod (weightSquare γ i j) (a ⊗ₜ 1) z.2⟩

/-- Right multiplication by the different right coefficient algebra on the corner. -/
def cornerRight (a : C) (z : bimod Q (weightSquare γ i j)) : bimod Q (weightSquare γ i j) :=
  ⟨z * botConcat Q (weightSquare γ i j) (a ⊗ₜ 1),
    mul_botConcat_mem_bimod (weightSquare γ i j) (a ⊗ₜ 1) z.2⟩

theorem affineEquiv_symm_left (hij : i ≠ j) (a : A) (z : bimod Q (weightSquare γ i j)) :
    (affineEquiv Q γ i j hPQ hP hij).symm (cornerLeft Q γ i j a z) =
      a • (affineEquiv Q γ i j hPQ hP hij).symm z := by
  apply (affineEquiv Q γ i j hPQ hP hij).injective
  apply Subtype.ext
  simp only [LinearEquiv.apply_symm_apply, affineEquiv_left]
  rfl

theorem affineEquiv_symm_right (hij : i ≠ j) (a : C) (z : bimod Q (weightSquare γ i j)) :
    (affineEquiv Q γ i j hPQ hP hij).symm (cornerRight Q γ i j a z) =
      rightAct Q γ i j a ((affineEquiv Q γ i j hPQ hP hij).symm z) := by
  apply (affineEquiv Q γ i j hPQ hP hij).injective
  apply Subtype.ext
  simp only [LinearEquiv.apply_symm_apply, affineEquiv_right]
  rfl

@[simp] theorem affineEquiv_inverse_forward (hij : i ≠ j) (z : Source Q γ i j) :
    (affineEquiv Q γ i j hPQ hP hij).symm (affineEquiv Q γ i j hPQ hP hij z) = z :=
  (affineEquiv Q γ i j hPQ hP hij).symm_apply_apply z

@[simp] theorem affineEquiv_forward_inverse (hij : i ≠ j) (z : bimod Q (weightSquare γ i j)) :
    affineEquiv Q γ i j hPQ hP hij ((affineEquiv Q γ i j hPQ hP hij).symm z) = z :=
  (affineEquiv Q γ i j hPQ hP hij).apply_symm_apply z

end Categorification.KLR.KLRAlgebra.MixedAffine.Lower
