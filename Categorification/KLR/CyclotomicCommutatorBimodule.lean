import Categorification.KLR.CyclotomicNegativeCommutator

/-!
# Present-colour cyclotomic commutator bimodule equivalences

The positive and negative decompositions of Kang–Kashiwara, §5.2, have canonical
outer actions over `RΛ(β)`, for `β = {i} + γ`. On the lower tensor the actions are
multiplication on its first and second factors. On the middle corner they are
multiplication by the last-strand inclusion, descended through the
cyclotomic ideal. On the finite correction they are pointwise regular actions.

`cyclotomicCommutatorBimoduleEquiv` and `cyclotomicNegativeCommutatorBimoduleEquiv`
are linear equivalences over `RΛ(β)` with explicit right compatibility, including
for the inverse. Their forward and inverse functions are definitionally the
previously constructed equivalences. These are usable as ungraded bimodule
isomorphisms; no module action is transported through a commutator equivalence.

The action and map-compatibility statements require only a commutative ground
ring. Bijectivity assumes `KLRSymm Q`, unit constant leading coefficients of the
`Q_{jl}`, monic `a_j` and the Cartan-degree condition. Unlike the graded
source, these statements forget grading. They cover only present colour; no
functor, naturality or adjunction packaging is asserted.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "Rb" => KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "S" => CycKLR k Q a (Si + β)
local notation "N" => LowerCoefficient Q i γ a

/-- Last-strand concatenation descends through the actual cyclotomic ideal. -/
def cyclotomicLastLinear : Rl →ₗ[k] S :=
  (LinearMap.ker (CycKLR.mk k Q a β).toLinearMap).liftQ
    ((CycKLR.mk k Q a (Si + β)).toLinearMap.comp
      ({ toFun := cL Q i β
         map_add' := cL_add i β
         map_smul' := fun c r => cL_smul i β c r } : Rb →ₗ[k] KLRAlgebra k Q (Si + β)))
    (by
      intro r hr
      exact (CycKLR.mk_eq_zero_iff _).2
        (cL_mem_cycIdeal i β a ((CycKLR.mk_eq_zero_iff r).1 hr))) ∘ₗ
    ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
      CycKLR.mk_surjective).symm.toLinearMap

theorem cyclotomicLastLinear_mk (r : Rb) :
    cyclotomicLastLinear Q i γ a (CycKLR.mk k Q a β r) =
      CycKLR.mk k Q a (Si + β) (cL Q i β r) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (CycKLR.mk k Q a β).toLinearMap CycKLR.mk_surjective r
  change ((CycKLR.mk k Q a β).toLinearMap.quotKerEquivOfSurjective
    CycKLR.mk_surjective).symm (CycKLR.mk k Q a β r) = _ at he
  rw [cyclotomicLastLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
  rfl

/-- The nonunital inclusion has the actual colour-cut idempotent as unit image. -/
def cyclotomicLast : Rl →ₙₐ[k] S where
  toFun := cyclotomicLastLinear Q i γ a
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' r s := by
    obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
    obtain ⟨s, rfl⟩ := CycKLR.mk_surjective s
    rw [← map_mul, cyclotomicLastLinear_mk, cL_mul, map_mul,
      cyclotomicLastLinear_mk, cyclotomicLastLinear_mk]

@[simp] theorem cyclotomicLast_mk (r : Rb) :
    cyclotomicLast Q i γ a (CycKLR.mk k Q a β r) =
      CycKLR.mk k Q a (Si + β) (cL Q i β r) := cyclotomicLastLinear_mk Q i γ a r

theorem cyclotomicLast_one : cyclotomicLast Q i γ a 1 =
    CycKLR.mk k Q a (Si + β) (cL Q i β 1) := by
  rw [← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk]

instance middleCyclotomicModule : Module Rl (MiddleCyclotomic Q i γ a) where
  smul r z := ⟨cyclotomicLast Q i γ a r * z.1, by
    constructor
    · rw [← cyclotomicLast_one, ← mul_assoc, ← map_mul, one_mul]
    · rw [mul_assoc, z.2.2]⟩
  one_smul z := Subtype.ext (by
    change cyclotomicLast Q i γ a 1 * z.1 = z.1
    rw [cyclotomicLast_one]
    exact z.2.1)
  mul_smul r s z := Subtype.ext (by
    change cyclotomicLast Q i γ a (r * s) * z.1 =
      cyclotomicLast Q i γ a r * (cyclotomicLast Q i γ a s * z.1)
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (mul_zero _)
  smul_add r z w := Subtype.ext (mul_add _ _ _)
  add_smul r s z := Subtype.ext (by
    change cyclotomicLast Q i γ a (r + s) * z.1 =
      cyclotomicLast Q i γ a r * z.1 + cyclotomicLast Q i γ a s * z.1
    rw [map_add, add_mul])
  zero_smul z := Subtype.ext (by change cyclotomicLast Q i γ a 0*z.1 = 0; rw [map_zero, zero_mul])

instance middleCyclotomicOpModule : Module Rlᵐᵒᵖ (MiddleCyclotomic Q i γ a) where
  smul r z := ⟨z.1 * cyclotomicLast Q i γ a r.unop, by
    constructor
    · rw [← mul_assoc, z.2.1]
    · rw [← cyclotomicLast_one, mul_assoc, ← map_mul, mul_one]⟩
  one_smul z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i γ a 1 = z.1
    rw [cyclotomicLast_one]
    exact z.2.2)
  mul_smul r s z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i γ a (s.unop * r.unop) =
      (z.1 * cyclotomicLast Q i γ a s.unop) * cyclotomicLast Q i γ a r.unop
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (zero_mul _)
  smul_add r z w := Subtype.ext (add_mul _ _ _)
  add_smul r s z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i γ a (r.unop + s.unop) =
      z.1 * cyclotomicLast Q i γ a r.unop + z.1 * cyclotomicLast Q i γ a s.unop
    rw [map_add, mul_add])
  zero_smul z := Subtype.ext (by change z.1*cyclotomicLast Q i γ a 0 = 0; rw [map_zero, mul_zero])

instance middleCyclotomicComm : SMulCommClass Rl Rlᵐᵒᵖ (MiddleCyclotomic Q i γ a) where
  smul_comm r s z := Subtype.ext (mul_assoc (cyclotomicLast Q i γ a r) z.1 (cyclotomicLast Q i γ a s.unop)).symm

instance middleCyclotomicTower : IsScalarTower k Rl (MiddleCyclotomic Q i γ a) where
  smul_assoc c r z := Subtype.ext (by
    change cyclotomicLast Q i γ a (c • r) * z.1 = c • (cyclotomicLast Q i γ a r * z.1)
    rw [map_smul, smul_mul_assoc])

instance middleCyclotomicOpTower : IsScalarTower k Rlᵐᵒᵖ (MiddleCyclotomic Q i γ a) where
  smul_assoc c r z := Subtype.ext (by
    change z.1 * cyclotomicLast Q i γ a (c • r.unop) = c • (z.1 * cyclotomicLast Q i γ a r.unop)
    rw [map_smul, mul_smul_comm])

/-- The left action is actual multiplication by the descended last-strand inclusion. -/
theorem middleCyclotomic_smul_val (r : Rl) (z : MiddleCyclotomic Q i γ a) :
    ((r • z : MiddleCyclotomic Q i γ a) : S) = cyclotomicLast Q i γ a r * (z : S) := rfl

/-- The right action is actual right multiplication, not transport along a decomposition. -/
theorem middleCyclotomic_op_smul_val (r : Rlᵐᵒᵖ) (z : MiddleCyclotomic Q i γ a) :
    ((r • z : MiddleCyclotomic Q i γ a) : S) = (z : S) * cyclotomicLast Q i γ a r.unop := rfl

/-- Right multiplication on the actual second tensor factor, linear over the balancing algebra. -/
def lowerCoefficientRight (r : Rl) : N →ₗ[KLRAlgebra k Q γ] N where
  toFun y := ⟨y.1 * r, by change _ * (y.1 * r) = y.1 * r; rw [← mul_assoc, CornerTensor.right_mem]⟩
  map_add' y z := Subtype.ext (add_mul _ _ _)
  map_smul' s y := Subtype.ext (mul_assoc _ _ _)

/-- The canonical right action descends through the balanced tensor relations. -/
def lowerCyclotomicRight (r : Rl) : LowerCyclotomic Q i γ a →ₗ[Rl] LowerCyclotomic Q i γ a :=
  BalancedTensor.mapRight (lowerCoefficientRight Q i γ a r)

instance lowerCyclotomicOpModule : Module Rlᵐᵒᵖ (LowerCyclotomic Q i γ a) where
  smul r z := lowerCyclotomicRight Q i γ a r.unop z
  one_smul z := by
    change lowerCyclotomicRight Q i γ a 1 z = z
    induction z using BalancedTensor.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy]
    | tmul x y =>
      change BalancedTensor.tmul x (lowerCoefficientRight Q i γ a 1 y) = _
      congr 1
      exact Subtype.ext (mul_one _)
  mul_smul r s z := by
    change lowerCyclotomicRight Q i γ a (s.unop * r.unop) z =
      lowerCyclotomicRight Q i γ a r.unop (lowerCyclotomicRight Q i γ a s.unop z)
    induction z using BalancedTensor.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      change BalancedTensor.tmul x (lowerCoefficientRight Q i γ a (s.unop * r.unop) y) = _
      congr 1
      exact Subtype.ext (mul_assoc _ _ _).symm
  smul_zero r := map_zero _
  smul_add r x y := map_add _ _ _
  add_smul r s z := by
    change lowerCyclotomicRight Q i γ a (r.unop + s.unop) z =
      lowerCyclotomicRight Q i γ a r.unop z + lowerCyclotomicRight Q i γ a s.unop z
    induction z using BalancedTensor.induction_on with
    | zero => simp only [map_zero, add_zero]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | tmul x y =>
      change BalancedTensor.tmul x (lowerCoefficientRight Q i γ a (r.unop+s.unop) y) = _
      rw [show lowerCoefficientRight Q i γ a (r.unop+s.unop) y =
        lowerCoefficientRight Q i γ a r.unop y + lowerCoefficientRight Q i γ a s.unop y
          from Subtype.ext (mul_add _ _ _), BalancedTensor.tmul_add]
      rfl
  zero_smul z := by
    change lowerCyclotomicRight Q i γ a 0 z = 0
    induction z using BalancedTensor.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul x y =>
      change BalancedTensor.tmul x (lowerCoefficientRight Q i γ a 0 y) = _
      rw [show lowerCoefficientRight Q i γ a 0 y = 0 from Subtype.ext (mul_zero _), BalancedTensor.tmul_zero]

instance lowerCyclotomicComm : SMulCommClass Rl Rlᵐᵒᵖ (LowerCyclotomic Q i γ a) where
  smul_comm r s z := (map_smul (lowerCyclotomicRight Q i γ a s.unop) r z).symm

theorem lowerCyclotomic_op_smul_tmul (r : Rl)
    (x : CornerTensor.Left (lowerLastCyc Q i γ a)) (y : N) :
    op r • (BalancedTensor.tmul x y : LowerCyclotomic Q i γ a) =
      BalancedTensor.tmul x (lowerCoefficientRight Q i γ a r y) := rfl

/-- The crossing formula on arbitrary quotient coefficients. -/
theorem cyclotomicSigma_tmul_canonical
    (x : CornerTensor.Left (lowerLastCyc Q i γ a)) (y : N) :
    (cyclotomicSigma Q i γ a (BalancedTensor.tmul x y) : S) =
      cyclotomicLast Q i γ a (x : Rl) *
        CycKLR.mk k Q a (Si + β) (-ψ (Multiset.card γ)) *
          cyclotomicLast Q i γ a (y : Rl) := by
  obtain ⟨x, rfl⟩ := lowerLeftQuotient_surjective Q i γ a x
  obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
  rw [cyclotomicSigma_tmul Q i γ a x y b hb.symm]
  change _ = cyclotomicLast Q i γ a (CycKLR.mk k Q a β (x : Rb)) * _ * _
  rw [← hb, cyclotomicLast_mk, cyclotomicLast_mk, map_mul, map_mul]

/-- Left equivariance uses multiplication on the first factor and the actual corner inclusion. -/
theorem cyclotomicSigma_smul (r : Rl) (z : LowerCyclotomic Q i γ a) :
    cyclotomicSigma Q i γ a (r • z) = r • cyclotomicSigma Q i γ a z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x y =>
    rw [BalancedTensor.smul_tmul']
    apply Subtype.ext
    change (cyclotomicSigma Q i γ a (BalancedTensor.tmul (r • x) y) : S) =
      cyclotomicLast Q i γ a r * (cyclotomicSigma Q i γ a (BalancedTensor.tmul x y) : S)
    rw [cyclotomicSigma_tmul_canonical, cyclotomicSigma_tmul_canonical]
    change cyclotomicLast Q i γ a (r * (x : Rl)) * _ * _ = _
    rw [map_mul]
    simp only [mul_assoc]

/-- Right equivariance uses multiplication on the second tensor factor. -/
theorem cyclotomicSigma_op_smul (r : Rlᵐᵒᵖ) (z : LowerCyclotomic Q i γ a) :
    cyclotomicSigma Q i γ a (r • z) = r • cyclotomicSigma Q i γ a z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x y =>
    rw [← op_unop r, lowerCyclotomic_op_smul_tmul]
    apply Subtype.ext
    change (cyclotomicSigma Q i γ a (BalancedTensor.tmul x (lowerCoefficientRight Q i γ a r.unop y)) : S) =
      (cyclotomicSigma Q i γ a (BalancedTensor.tmul x y) : S) * cyclotomicLast Q i γ a r.unop
    rw [cyclotomicSigma_tmul_canonical, cyclotomicSigma_tmul_canonical]
    change _ * _ * cyclotomicLast Q i γ a ((y : Rl) * r.unop) = _
    rw [map_mul]
    simp only [mul_assoc]

/-- Dotted multiplication is left equivariant for every exponent. -/
theorem cyclotomicDotCounit_smul (d : ℕ) (r : Rl) (z : LowerCyclotomic Q i γ a) :
    cyclotomicDotCounit Q i γ a d (r • z) = r * cyclotomicDotCounit Q i γ a d z := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero, mul_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]
  | tmul x y =>
    rw [BalancedTensor.smul_tmul']
    change (r * (x : Rl)) * _ * (y : Rl) = r * ((x : Rl) * _ * (y : Rl))
    simp only [mul_assoc]

/-- Dotted multiplication is right equivariant for every exponent. -/
theorem cyclotomicDotCounit_op_smul (d : ℕ) (r : Rlᵐᵒᵖ) (z : LowerCyclotomic Q i γ a) :
    cyclotomicDotCounit Q i γ a d (r • z) = cyclotomicDotCounit Q i γ a d z * r.unop := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero, zero_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, add_mul]
  | tmul x y =>
    rw [← op_unop r, lowerCyclotomic_op_smul_tmul]
    change (x : Rl) * _ * ((y : Rl) * r.unop) = ((x : Rl) * _ * (y : Rl)) * r.unop
    simp only [mul_assoc]

/-- The canonical dot-unit formula, with arbitrary cyclotomic coefficients. -/
theorem cyclotomicDotUnit_monomial_canonical (r : Rl) (d : ℕ) :
    (cyclotomicDotUnit Q i γ a (Polynomial.monomial d r) : S) =
      cyclotomicLast Q i γ a r *
        CycKLR.mk k Q a (Si + β) ((x ⟨Multiset.card β, lastPos_lt i β⟩)^d) *
          cyclotomicLast Q i γ a 1 := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [cyclotomicDotUnit_monomial, cyclotomicLast_mk, cyclotomicLast_one, map_mul, map_mul]

theorem cyclotomicDotUnit_monomial_mul_left (r s : Rl) (d : ℕ) :
    cyclotomicDotUnit Q i γ a (Polynomial.monomial d (r*s)) =
      r • cyclotomicDotUnit Q i γ a (Polynomial.monomial d s) := by
  apply Subtype.ext
  change (cyclotomicDotUnit Q i γ a (Polynomial.monomial d (r*s)) : S) =
    cyclotomicLast Q i γ a r * (cyclotomicDotUnit Q i γ a (Polynomial.monomial d s) : S)
  rw [cyclotomicDotUnit_monomial_canonical, cyclotomicDotUnit_monomial_canonical, map_mul]
  simp only [mul_assoc]

theorem cyclotomicDotUnit_monomial_mul_right (r s : Rl) (d : ℕ) :
    cyclotomicDotUnit Q i γ a (Polynomial.monomial d (r*s)) =
      op s • cyclotomicDotUnit Q i γ a (Polynomial.monomial d r) := by
  apply Subtype.ext
  change (cyclotomicDotUnit Q i γ a (Polynomial.monomial d (r*s)) : S) =
    (cyclotomicDotUnit Q i γ a (Polynomial.monomial d r) : S) * cyclotomicLast Q i γ a s
  rw [cyclotomicDotUnit_monomial_canonical, cyclotomicDotUnit_monomial_canonical, map_mul]
  obtain ⟨b, rfl⟩ := CycKLR.mk_surjective s
  have hc := ((commute_x_last_cL (Q := Q) i β b).pow_left d).map (CycKLR.mk k Q a (Si + β))
  rw [cyclotomicLast_mk] at *
  rw [mul_assoc (cyclotomicLast Q i γ a r), ← hc.eq]
  simp only [mul_assoc]
  rw [← cyclotomicLast_mk, ← map_mul, mul_one, ← map_mul, one_mul]

/-- The dot-unit is left equivariant on all coefficient polynomials. -/
theorem cyclotomicDotUnit_smul (r : Rl) (p : Polynomial Rl) :
    cyclotomicDotUnit Q i γ a (r • p) = r • cyclotomicDotUnit Q i γ a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | monomial d s =>
    rw [Polynomial.smul_monomial]
    exact cyclotomicDotUnit_monomial_mul_left Q i γ a r s d

/-- The dot-unit is right equivariant on all coefficient polynomials. -/
theorem cyclotomicDotUnit_op_smul (r : Rlᵐᵒᵖ) (p : Polynomial Rl) :
    cyclotomicDotUnit Q i γ a (r • p) = r • cyclotomicDotUnit Q i γ a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | monomial d s =>
    rw [Polynomial.smul_monomial]
    exact cyclotomicDotUnit_monomial_mul_right Q i γ a s r.unop d

variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "pos" => cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg
local notation "neg" => cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg

theorem cyclotomicCommutatorFinEquiv_smul (hwt : 0 ≤ wt) (r : Rl)
    (z : LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) :
    pos hwt (r • z) = r • pos hwt z := by
  rcases z with ⟨l,v⟩
  rw [show r • (l,v) = (r • l, r • v) from rfl,
    cyclotomicCommutatorFinEquiv_apply, cyclotomicCommutatorFinEquiv_apply,
    cyclotomicSigma_smul, smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  exact cyclotomicDotUnit_monomial_mul_left Q i γ a r (v d) d

theorem cyclotomicCommutatorFinEquiv_op_smul (hwt : 0 ≤ wt) (r : Rlᵐᵒᵖ)
    (z : LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) :
    pos hwt (r • z) = r • pos hwt z := by
  rcases z with ⟨l,v⟩
  rw [show r • (l,v) = (r • l, r • v) from rfl,
    cyclotomicCommutatorFinEquiv_apply, cyclotomicCommutatorFinEquiv_apply,
    cyclotomicSigma_op_smul, smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  exact cyclotomicDotUnit_monomial_mul_right Q i γ a (v d) r.unop d

/-- The nonnegative decomposition is linear over the actual cyclotomic algebra.
Together with `cyclotomicCommutatorBimoduleEquiv_op_smul`, this is an ungraded
bimodule equivalence. Its forward and inverse functions are unchanged. -/
def cyclotomicCommutatorBimoduleEquiv (hwt : 0 ≤ wt) :
    (LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) ≃ₗ[Rl] MiddleCyclotomic Q i γ a where
  toEquiv := (pos hwt).toEquiv
  map_add' := map_add (pos hwt)
  map_smul' := cyclotomicCommutatorFinEquiv_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt

theorem cyclotomicCommutatorBimoduleEquiv_apply (hwt : 0 ≤ wt)
    (z : LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) :
    cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z = pos hwt z := rfl

theorem cyclotomicCommutatorBimoduleEquiv_symm_apply (hwt : 0 ≤ wt)
    (z : MiddleCyclotomic Q i γ a) :
    (cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z =
      (pos hwt).symm z := rfl

theorem cyclotomicCommutatorBimoduleEquiv_op_smul (hwt : 0 ≤ wt) (r : Rlᵐᵒᵖ)
    (z : LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) :
    cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt (r • z) =
      r • cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z :=
  cyclotomicCommutatorFinEquiv_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt r z

theorem cyclotomicCommutatorBimoduleEquiv_symm_op_smul (hwt : 0 ≤ wt) (r : Rlᵐᵒᵖ)
    (z : MiddleCyclotomic Q i γ a) :
    (cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm (r • z) =
      r • (cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z := by
  apply (cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply, cyclotomicCommutatorBimoduleEquiv_op_smul,
    LinearEquiv.apply_symm_apply]

theorem cyclotomicNegativeCommutatorEquiv_smul (hwt : wt ≤ 0) (r : Rl)
    (z : LowerCyclotomic Q i γ a) : neg hwt (r • z) = r • neg hwt z := by
  apply Prod.ext
  · exact cyclotomicSigma_smul Q i γ a r z
  · funext d
    exact cyclotomicDotCounit_smul Q i γ a d r z

theorem cyclotomicNegativeCommutatorEquiv_op_smul (hwt : wt ≤ 0) (r : Rlᵐᵒᵖ)
    (z : LowerCyclotomic Q i γ a) : neg hwt (r • z) = r • neg hwt z := by
  apply Prod.ext
  · exact cyclotomicSigma_op_smul Q i γ a r z
  · funext d
    exact cyclotomicDotCounit_op_smul Q i γ a d r z

/-- The nonpositive decomposition with the actual outer cyclotomic actions.
Right compatibility and right compatibility of its inverse are proved separately. -/
def cyclotomicNegativeCommutatorBimoduleEquiv (hwt : wt ≤ 0) :
    LowerCyclotomic Q i γ a ≃ₗ[Rl] MiddleCyclotomic Q i γ a × (Fin (-wt).toNat → Rl) where
  toEquiv := (neg hwt).toEquiv
  map_add' := map_add (neg hwt)
  map_smul' := cyclotomicNegativeCommutatorEquiv_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt

theorem cyclotomicNegativeCommutatorBimoduleEquiv_apply (hwt : wt ≤ 0)
    (z : LowerCyclotomic Q i γ a) :
    cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z = neg hwt z := rfl

theorem cyclotomicNegativeCommutatorBimoduleEquiv_symm_apply (hwt : wt ≤ 0)
    (z : MiddleCyclotomic Q i γ a × (Fin (-wt).toNat → Rl)) :
    (cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z =
      (neg hwt).symm z := rfl

theorem cyclotomicNegativeCommutatorBimoduleEquiv_op_smul (hwt : wt ≤ 0) (r : Rlᵐᵒᵖ)
    (z : LowerCyclotomic Q i γ a) :
    cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt (r • z) =
      r • cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z :=
  cyclotomicNegativeCommutatorEquiv_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt r z

theorem cyclotomicNegativeCommutatorBimoduleEquiv_symm_op_smul (hwt : wt ≤ 0) (r : Rlᵐᵒᵖ)
    (z : MiddleCyclotomic Q i γ a × (Fin (-wt).toNat → Rl)) :
    (cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm (r • z) =
      r • (cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z := by
  apply (cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply, cyclotomicNegativeCommutatorBimoduleEquiv_op_smul,
    LinearEquiv.apply_symm_apply]

end Categorification.KLR.KLRAlgebra
