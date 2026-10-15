/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentEquivalence
import Categorification.Algebra.IdempotentEquiv

/-!
# The absent-colour ungraded EF decomposition on modules

Induction is `(S e) ⊗_Rl N`, with ordinary multiplication on the one-sided
cyclotomic corner. Restriction is the actual fixed subspace `e M` with action
through the nonunital last-strand inclusion. `resIndEquiv` identifies their
composite with the two-cut corner tensor by left cutting actual tensors.

`absentEFEquiv` applies the accepted dot-unit bimodule equivalence to every
left cyclotomic module, naturally in arbitrary linear maps. The finite summands
are the original `e x_last^d e ⊗ n` in their original order. The coefficient
inverse uses noncommutative right balancing and the original module action.
No finiteness, projectivity, flatness or nontriviality of the module or quotient
is required; rank zero and zero weight are included under the same hypotheses.
This is the absent-colour ungraded module consequence of Kang–Kashiwara §5.2;
no graded shifts, present-colour commutators or adjunction are asserted.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "Rl" => CycKLR k Q a β
local notation "S" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + β)
local notation "ι" => cyclotomicLast Q i a β

/-- The last-colour idempotent in the actual cyclotomic quotient. -/
def lastIdem : S := ι 1

theorem lastIdem_mul : lastIdem Q i a β * lastIdem Q i a β = lastIdem Q i a β := by
  change ι 1 * ι 1 = ι 1
  rw [← map_mul, one_mul]

/-- The genuine one-sided induction bimodule `S e`. -/
abbrev IndCorner := ↥(lIdeal (lastIdem Q i a β))

instance indCornerOpModule : Module Rlᵐᵒᵖ (IndCorner Q i a β) where
  smul r z := ⟨z.1 * ι r.unop, by
    change z.1 * ι r.unop * ι 1 = z.1 * ι r.unop
    rw [mul_assoc, ← map_mul, mul_one]⟩
  one_smul z := Subtype.ext z.2
  mul_smul r s z := Subtype.ext (by
    change z.1 * ι (s.unop * r.unop) = (z.1 * ι s.unop) * ι r.unop
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (zero_mul _)
  smul_add r z w := Subtype.ext (add_mul _ _ _)
  add_smul r s z := Subtype.ext (by
    change z.1 * ι (r.unop + s.unop) = z.1 * ι r.unop + z.1 * ι s.unop
    rw [map_add, mul_add])
  zero_smul z := Subtype.ext (by change z.1 * ι 0 = 0; rw [map_zero, mul_zero])

instance indCornerComm : SMulCommClass S Rlᵐᵒᵖ (IndCorner Q i a β) where
  smul_comm r s z := Subtype.ext (mul_assoc r z.1 (ι s.unop)).symm

instance indCornerOpTower : IsScalarTower k Rlᵐᵒᵖ (IndCorner Q i a β) where
  smul_assoc c r z := Subtype.ext (by
    change z.1 * ι (c • r.unop) = c • (z.1 * ι r.unop)
    rw [map_smul, mul_smul_comm])

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (CycKLR k Q a β) N]

/-- Ungraded induction by the actual one-sided cyclotomic corner. -/
abbrev Ind := BalancedTensor k S Rl (IndCorner Q i a β) N

variable (M : Type*) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ({i} + β)) M] [IsScalarTower k (CycKLR k Q a ({i} + β)) M]

/-- Restriction is the actual idempotent-fixed subspace, not a tensor model. -/
abbrev Res := ↥(fixSub k M (lastIdem Q i a β))

instance resModule : Module Rl (Res Q i a β M) where
  smul r z := ⟨ι r • z.1, by
    change ι 1 • (ι r • z.1) = ι r • z.1
    rw [smul_smul, ← map_mul, one_mul]⟩
  one_smul z := Subtype.ext z.2
  mul_smul r s z := Subtype.ext (by
    change ι (r * s) • z.1 = ι r • (ι s • z.1)
    rw [map_mul, mul_smul])
  smul_zero r := Subtype.ext (smul_zero _)
  smul_add r z w := Subtype.ext (smul_add _ _ _)
  add_smul r s z := Subtype.ext (by
    change ι (r + s) • z.1 = ι r • z.1 + ι s • z.1
    rw [map_add, add_smul])
  zero_smul z := Subtype.ext (by change ι 0 • z.1 = 0; rw [map_zero, zero_smul])

instance resTower : IsScalarTower k Rl (Res Q i a β M) where
  smul_assoc c r z := Subtype.ext (by
    change ι (c • r) • z.1 = c • (ι r • z.1)
    rw [map_smul, smul_assoc])

/-- The actual composite of induction and idempotent restriction. -/
abbrev EF := Res Q i a β (Ind Q i a β N)

/-- Forget only the left cut. -/
def cornerToInd : Corner Q i a β →ₗ[k] IndCorner Q i a β where
  toFun z := ⟨z.1, by
    change z.1 * lastIdem Q i a β = z.1
    simpa only [lastIdem, cyclotomicLast_one] using z.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Put the left cut onto an actual one-sided element. -/
def leftCut : IndCorner Q i a β →ₗ[k] Corner Q i a β where
  toFun z := ⟨lastIdem Q i a β * z.1, by
    constructor
    · rw [← cyclotomicLast_one, ← mul_assoc]
      exact congrArg (· * z.1) (lastIdem_mul Q i a β)
    · rw [← cyclotomicLast_one, mul_assoc]
      exact congrArg (lastIdem Q i a β * ·) z.2⟩
  map_add' z w := Subtype.ext (mul_add _ _ _)
  map_smul' c z := Subtype.ext (mul_smul_comm _ _ _)

def cutTensor : Ind Q i a β N →ₗ[k] BalancedTensor k Rl Rl (Corner Q i a β) N :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k Rl Rl (Corner Q i a β) N).comp (leftCut Q i a β))
    (fun z r n => by
      change BalancedTensor.tmul (leftCut Q i a β (op r • z)) n = _
      have h : leftCut Q i a β (op r • z) = op r • leftCut Q i a β z :=
        Subtype.ext (mul_assoc _ _ _).symm
      rw [h, BalancedTensor.op_smul_tmul]
      rfl)

@[simp] theorem cutTensor_tmul (z : IndCorner Q i a β) (n : N) :
    cutTensor Q i a β N (BalancedTensor.tmul z n) =
      BalancedTensor.tmul (leftCut Q i a β z) n := rfl

/-- Inclusion of the two-cut tensor into genuine induction. -/
def includeTensor : BalancedTensor k Rl Rl (Corner Q i a β) N →ₗ[k] Ind Q i a β N :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k S Rl (IndCorner Q i a β) N).comp (cornerToInd Q i a β))
    (fun z r n => by
      change BalancedTensor.tmul (cornerToInd Q i a β (op r • z)) n = _
      change BalancedTensor.tmul (op r • cornerToInd Q i a β z) n = _
      rw [BalancedTensor.op_smul_tmul]
      rfl)

@[simp] theorem includeTensor_tmul (z : Corner Q i a β) (n : N) :
    includeTensor Q i a β N (BalancedTensor.tmul z n) =
      BalancedTensor.tmul (cornerToInd Q i a β z) n := rfl

theorem cut_include (t : BalancedTensor k Rl Rl (Corner Q i a β) N) :
    cutTensor Q i a β N (includeTensor Q i a β N t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul z n =>
    rw [includeTensor_tmul, cutTensor_tmul]
    have h : leftCut Q i a β (cornerToInd Q i a β z) = z :=
      Subtype.ext (by
        change lastIdem Q i a β * z.1 = z.1
        simpa only [lastIdem, cyclotomicLast_one] using z.2.1)
    rw [h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem include_cut (t : Ind Q i a β N) :
    includeTensor Q i a β N (cutTensor Q i a β N t) = lastIdem Q i a β • t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul z n => rw [cutTensor_tmul, includeTensor_tmul, BalancedTensor.smul_tmul']; rfl
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem includeTensor_fixed (t : BalancedTensor k Rl Rl (Corner Q i a β) N) :
    lastIdem Q i a β • includeTensor Q i a β N t = includeTensor Q i a β N t := by
  rw [← include_cut, cut_include]

/-- Identification by left cutting actual induction tensors. -/
def resIndEquiv : EF Q i a β N ≃ₗ[Rl] BalancedTensor k Rl Rl (Corner Q i a β) N where
  toFun z := cutTensor Q i a β N z.1
  invFun t := ⟨includeTensor Q i a β N t, includeTensor_fixed Q i a β N t⟩
  left_inv z := Subtype.ext ((include_cut Q i a β N z.1).trans z.2)
  right_inv t := cut_include Q i a β N t
  map_add' z w := map_add _ z.1 w.1
  map_smul' r z := by
    change cutTensor Q i a β N (ι r • z.1) = r • cutTensor Q i a β N z.1
    have h : ∀ t : Ind Q i a β N,
        cutTensor Q i a β N (ι r • t) = r • cutTensor Q i a β N t := by
      intro t
      induction t using BalancedTensor.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul v n =>
        rw [BalancedTensor.smul_tmul', cutTensor_tmul, cutTensor_tmul, BalancedTensor.smul_tmul']
        congr 1
        apply Subtype.ext
        change ι 1 * (ι r * v.1) = ι r * (ι 1 * v.1)
        rw [← mul_assoc, ← map_mul, one_mul, ← mul_assoc, ← map_mul, mul_one]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    exact h z.1


/-- Restriction of an actual map of cyclotomic modules. -/
def resMap {M' : Type*} [AddCommGroup M'] [Module k M'] [Module S M']
    [IsScalarTower k S M'] (f : M →ₗ[S] M') : Res Q i a β M →ₗ[Rl] Res Q i a β M' where
  toFun z := ⟨f z.1, by change lastIdem Q i a β • f z.1 = f z.1; rw [← map_smul, z.2]⟩
  map_add' z w := Subtype.ext (map_add f z.1 w.1)
  map_smul' r z := Subtype.ext (f.map_smul (ι r) z.1)

variable [IsScalarTower k (CycKLR k Q a β) N]
  {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (CycKLR k Q a β) N']
  [IsScalarTower k (CycKLR k Q a β) N']

/-- Induction on morphisms is tensoring the actual module map. -/
abbrev indMap (f : N →ₗ[Rl] N') : Ind Q i a β N →ₗ[S] Ind Q i a β N' :=
  BalancedTensor.mapRight f

/-- The genuine EF action on arbitrary cyclotomic module maps. -/
def efMap (f : N →ₗ[Rl] N') : EF Q i a β N →ₗ[Rl] EF Q i a β N' :=
  resMap Q i a β (Ind Q i a β N) (indMap Q i a β N f)

@[simp] theorem efMap_val (f : N →ₗ[Rl] N') (z : EF Q i a β N) :
    (efMap Q i a β N f z).1 = BalancedTensor.mapRight f z.1 := rfl

@[simp] theorem efMap_id : efMap Q i a β N (LinearMap.id : N →ₗ[Rl] N) = LinearMap.id := by
  ext z
  change BalancedTensor.mapRight (LinearMap.id : N →ₗ[Rl] N) z.1 = z.1
  rw [BalancedTensor.mapRight_id]
  rfl

theorem efMap_comp {N'' : Type*} [AddCommGroup N''] [Module k N''] [Module Rl N'']
    [IsScalarTower k Rl N''] (f : N →ₗ[Rl] N') (g : N' →ₗ[Rl] N'') :
    efMap Q i a β N (g.comp f) = (efMap Q i a β N' g).comp (efMap Q i a β N f) := by
  ext z
  change BalancedTensor.mapRight (g.comp f) z.1 = BalancedTensor.mapRight g (BalancedTensor.mapRight f z.1)
  rw [BalancedTensor.mapRight_comp]
  rfl

omit [IsScalarTower k Rl N] in
/-- The comparison cuts an elementary induction tensor on its left. -/
theorem resIndEquiv_cut_tmul (z : IndCorner Q i a β) (n : N) :
    resIndEquiv Q i a β N
      ⟨lastIdem Q i a β • BalancedTensor.tmul z n, by
        change lastIdem Q i a β • (lastIdem Q i a β • _) = _
        rw [smul_smul, lastIdem_mul]⟩ = BalancedTensor.tmul (leftCut Q i a β z) n := by
  change cutTensor Q i a β N (lastIdem Q i a β • BalancedTensor.tmul z n) = _
  rw [BalancedTensor.smul_tmul', cutTensor_tmul]
  congr 1
  apply Subtype.ext
  change lastIdem Q i a β * (lastIdem Q i a β * z.1) = lastIdem Q i a β * z.1
  rw [← mul_assoc, lastIdem_mul]

variable (hsym : KLRSymm Q)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hi : i ∉ β)
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "E" => finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi

/-- Coefficients of an actual two-cut tensor, acting on its module factor. -/
def tensorCoefficients : BalancedTensor k Rl Rl (Corner Q i a β) N →ₗ[Rl] (Fin (wt).toNat → N) :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun z n d => (E).symm z d • n)
      (fun z w n => by ext d; simp [add_smul])
      (fun c z n => by ext d; simp [smul_assoc])
      (fun z n m => by ext d; simp [smul_add])
      (fun c z n => by ext d; exact smul_comm _ c n))
    (fun z r n => by
      ext d
      change (E).symm (op r • z) d • n = (E).symm z d • (r • n)
      rw [finEquiv_symm_right, mul_smul])
    (fun r z n => by
      ext d
      change (E).symm (r • z) d • n = r • ((E).symm z d • n)
      rw [finEquiv_symm_left, mul_smul])

local notation "coeff" => tensorCoefficients Q i a β N hsym hQ ha RD Λ hΛ hdeg hi

/-- Finite dot-unit tensors, in the accepted original order. -/
def tensorDotSum : (Fin (wt).toNat → N) →ₗ[Rl] BalancedTensor k Rl Rl (Corner Q i a β) N where
  toFun v := ∑ d : Fin (wt).toNat, BalancedTensor.tmul (E (Pi.single d 1)) (v d)
  map_add' v w := by simp only [Pi.add_apply, BalancedTensor.tmul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [← BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul']
    congr 1
    rw [← finEquiv_right, ← finEquiv_left]
    congr 1
    ext j
    by_cases h : d = j
    · subst j; simp
    · simp [h]

local notation "dots" => tensorDotSum Q i a β N hsym hQ ha RD Λ hΛ hdeg hi

theorem coefficients_dotSum (v : Fin (wt).toNat → N) : coeff (dots v) = v := by
  change coeff (∑ d, BalancedTensor.tmul (E (Pi.single d 1)) (v d)) = v
  rw [map_sum]
  ext j
  simp only [Finset.sum_apply]
  change (∑ d, (E).symm (E (Pi.single d 1)) j • v d) = v j
  simp only [LinearEquiv.symm_apply_apply]
  classical
  simp [Pi.single_apply, ite_smul]

theorem dotSum_coefficients (t : BalancedTensor k Rl Rl (Corner Q i a β) N) :
    dots (coeff t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul z n =>
    change (∑ d, BalancedTensor.tmul (E (Pi.single d 1)) ((E).symm z d • n)) = _
    have hsum : ∑ d : Fin (wt).toNat, op ((E).symm z d) • E (Pi.single d 1) = z := by
      simp only [← finEquiv_right, ← map_sum]
      have h : (∑ d : Fin (wt).toNat, fun j => (Pi.single d (1 : Rl) : Fin (wt).toNat → Rl) j * (E).symm z d) = (E).symm z := by
        ext j
        classical
        simp [Pi.single_apply]
      rw [h, LinearEquiv.apply_symm_apply]
    have hadd : ∀ (s : Finset (Fin (wt).toNat)) (f : Fin (wt).toNat → Corner Q i a β),
        (BalancedTensor.tmul (∑ d ∈ s, f d) n : BalancedTensor k Rl Rl (Corner Q i a β) N) =
          ∑ d ∈ s, BalancedTensor.tmul (f d) n := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert d s hd hs => simp only [Finset.sum_insert hd, BalancedTensor.add_tmul, hs]
    simp only [← BalancedTensor.op_smul_tmul]
    rw [← hadd, hsum]

/-- The absent-colour ungraded decomposition on an arbitrary actual cyclotomic module. -/
def absentEFEquiv : (Fin (wt).toNat → N) ≃ₗ[Rl] EF Q i a β N :=
  let e : (Fin (wt).toNat → N) ≃ₗ[Rl] BalancedTensor k Rl Rl (Corner Q i a β) N :=
    { dots with
      invFun := coeff
      left_inv := coefficients_dotSum Q i a β N hsym hQ ha RD Λ hΛ hdeg hi
      right_inv := dotSum_coefficients Q i a β N hsym hQ ha RD Λ hΛ hdeg hi }
  e.trans (resIndEquiv Q i a β N).symm

local notation "EFiso" => absentEFEquiv Q i a β N hsym hQ ha RD Λ hΛ hdeg hi

/-- The finite map lands in genuine induction with its original dot-unit representatives. -/
theorem absentEFEquiv_val (v : Fin (wt).toNat → N) :
    (EFiso v).1 = ∑ d : Fin (wt).toNat,
      BalancedTensor.tmul (cornerToInd Q i a β (dotUnitTerm Q i a β d 1)) (v d) := by
  change includeTensor Q i a β N (∑ d, BalancedTensor.tmul (E (Pi.single d 1)) (v d)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [includeTensor_tmul]
  congr 2
  change dotUnitSum Q i a β (wt).toNat (Pi.single d 1) = _
  simp only [dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  classical
  simp [Pi.single_apply, apply_ite]

/-- The dot order in the genuine one-sided representative is `e x_last^d e`. -/
theorem absentEFEquiv_dot_val (d : Fin (wt).toNat) :
    (cornerToInd Q i a β (dotUnitTerm Q i a β d 1)).1 =
      lastIdem Q i a β *
        (CycKLR.mk k Q a ({i} + β) (x ⟨Multiset.card β, lastPos_lt i β⟩)) ^ (d : ℕ) *
          lastIdem Q i a β := rfl

/-- A single summand is the actual dotted unit tensor, not a transported action. -/
theorem absentEFEquiv_single (d : Fin (wt).toNat) (n : N) :
    (EFiso (Pi.single d n)).1 =
      BalancedTensor.tmul (cornerToInd Q i a β (dotUnitTerm Q i a β d 1)) n := by
  rw [absentEFEquiv_val]
  classical
  rw [Finset.sum_eq_single d]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, BalancedTensor.tmul_zero]
  · intro h
    exact (h (Finset.mem_univ d)).elim

theorem absentEFEquiv_inverse_forward (v : Fin (wt).toNat → N) :
    (EFiso).symm (EFiso v) = v := (EFiso).symm_apply_apply v

theorem absentEFEquiv_forward_inverse (z : EF Q i a β N) :
    EFiso ((EFiso).symm z) = z := (EFiso).apply_symm_apply z

/-- Naturality for every linear map of actual cyclotomic modules. -/
theorem absentEFEquiv_natural (f : N →ₗ[Rl] N') (v : Fin (wt).toNat → N) :
    efMap Q i a β N f (EFiso v) =
      absentEFEquiv Q i a β N' hsym hQ ha RD Λ hΛ hdeg hi (fun d => f (v d)) := by
  apply Subtype.ext
  rw [efMap_val, absentEFEquiv_val, absentEFEquiv_val, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact BalancedTensor.mapRight_tmul f _ _

theorem absentEFEquiv_symm_natural (f : N →ₗ[Rl] N') (z : EF Q i a β N) :
    (absentEFEquiv Q i a β N' hsym hQ ha RD Λ hΛ hdeg hi).symm (efMap Q i a β N f z) =
      fun d => f ((EFiso).symm z d) := by
  apply (absentEFEquiv Q i a β N' hsym hQ ha RD Λ hΛ hdeg hi).injective
  rw [LinearEquiv.apply_symm_apply, ← absentEFEquiv_natural, LinearEquiv.apply_symm_apply]

end Categorification.KLR.KLRAlgebra.AbsentColour
