import Categorification.KLR.CyclotomicAbsentModule
import Categorification.KLR.CyclotomicCommutatorBimodule

/-!
# Present-colour cyclotomic module commutators

For `β = {i} + γ`, the functors here are genuine induction `S e ⊗ N` and
idempotent restriction `e M`, with their multiplication actions. The comparison
`indResEquiv` balances over the cyclotomic lower algebra by quotient surjectivity;
it does not identify the raw and cyclotomic lower algebras.

The nonnegative and nonpositive equivalences use the original crossing,
dot-unit, and dot-counit bimodule maps of Kang–Kashiwara, Theorem 5.2 and its
proof (arXiv:1102.4677v4, §5). They are ungraded and natural in arbitrary modules.
No projectivity, flatness, finite generation, nonzero quotient, or positive
lower rank is required. Grading shifts, adjunctions, and a bundled categorical
action are not asserted.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.PresentColour
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I) (a : I → Polynomial k)
local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "Rl" => CycKLR k Q a β
local notation "Rg" => CycKLR k Q a γ
local notation "ι" => AbsentColour.cyclotomicLast Q i a γ
local notation "e" => AbsentColour.lastIdem Q i a γ
local notation "L" => CornerTensor.Left (lowerLastCyc Q i γ a)
local notation "C" => LowerCoefficient Q i γ a
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (CycKLR k Q a ({i} + γ)) N] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N]

/-- The actual composite: induce the idempotent restriction. -/
abbrev FE := AbsentColour.Ind Q i a γ (AbsentColour.Res Q i a γ N)
abbrev LowerTensor := BalancedTensor k Rl Rl (LowerCyclotomic Q i γ a) N

lemma idem_eq : e = lowerLastCyc Q i γ a 1 := AbsentColour.cyclotomicLast_one Q i a γ

def leftToInd : L ≃ₗ[Rl] AbsentColour.IndCorner Q i a γ where
  toFun x := ⟨x.1, by change x.1 * e = x.1; rw [idem_eq]; exact x.2⟩
  invFun x := ⟨x.1, by change x.1 * lowerLastCyc Q i γ a 1 = x.1; rw [← idem_eq]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coeffAct : C →ₗ[k] N →ₗ[k] AbsentColour.Res Q i a γ N :=
  LinearMap.mk₂ k (fun y n => ⟨y.1 • n, by
    change e • (y.1 • n) = y.1 • n
    rw [smul_smul, idem_eq]
    exact congrArg (· • n) y.2⟩)
    (fun y z n => Subtype.ext (add_smul _ _ _))
    (fun c y n => Subtype.ext (smul_assoc _ _ _))
    (fun y n m => Subtype.ext (smul_add _ _ _))
    (fun c y n => Subtype.ext (smul_comm _ c _))

def lowerAct (n : N) : LowerCyclotomic Q i γ a →ₗ[Rl] FE Q i γ a N :=
  BalancedTensor.liftB
    (((BalancedTensor.mkBil k Rl Rg (AbsentColour.IndCorner Q i a γ)
      (AbsentColour.Res Q i a γ N)).comp ((leftToInd Q i γ a).toLinearMap.restrictScalars k)).compl₂
      ((coeffAct Q i γ a N).flip n))
    (fun x r y => by
      change BalancedTensor.tmul (leftToInd Q i γ a (op r • x)) (coeffAct Q i γ a N y n) = _
      have hx : leftToInd Q i γ a (op r • x) = op (CycKLR.mk k Q a γ r) • leftToInd Q i γ a x := by
        apply Subtype.ext
        change x.1 * lowerLastCyc Q i γ a r = x.1 * ι (CycKLR.mk k Q a γ r)
        rw [AbsentColour.cyclotomicLast_mk]; rfl
      rw [hx, BalancedTensor.op_smul_tmul]
      congr 1
      apply Subtype.ext
      change ι (CycKLR.mk k Q a γ r) • (y.1 • n) = (lowerLastCyc Q i γ a r * y.1) • n
      rw [AbsentColour.cyclotomicLast_mk, smul_smul]; rfl)
    (fun r x y => by
      change BalancedTensor.tmul (leftToInd Q i γ a (r • x)) _ = r • BalancedTensor.tmul _ _
      rw [map_smul, BalancedTensor.smul_tmul']; rfl)

@[simp] theorem lowerAct_tmul (n : N) (x : L) (y : C) :
    lowerAct Q i γ a N n (BalancedTensor.tmul x y) =
      BalancedTensor.tmul (leftToInd Q i γ a x) (coeffAct Q i γ a N y n) := rfl

def lowerToFE : LowerTensor Q i γ a N →ₗ[Rl] FE Q i γ a N :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun t n => lowerAct Q i γ a N n t)
      (fun t u n => map_add _ t u)
      (fun c t n => (lowerAct Q i γ a N n).map_smul_of_tower c t)
      (fun t n m => by
        induction t using BalancedTensor.induction_on with
        | zero => simp only [map_zero, add_zero]
        | add t u ht hu => simp only [map_add, ht, hu]; abel
        | tmul x y => simp only [lowerAct_tmul, map_add, BalancedTensor.tmul_add])
      (fun c t n => by
        induction t using BalancedTensor.induction_on with
        | zero => simp only [map_zero, smul_zero]
        | add t u ht hu => simp only [map_add, ht, hu, smul_add]
        | tmul x y => rw [lowerAct_tmul, lowerAct_tmul, map_smul, BalancedTensor.tmul_smul]))
    (fun t r n => by
      change lowerAct Q i γ a N n (op r • t) = lowerAct Q i γ a N (r • n) t
      induction t using BalancedTensor.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add t u ht hu => simp only [smul_add, map_add, ht, hu]
      | tmul x y =>
        rw [lowerCyclotomic_op_smul_tmul, lowerAct_tmul, lowerAct_tmul]
        congr 1
        exact Subtype.ext (mul_smul y.1 r n))
    (fun r t n => (lowerAct Q i γ a N n).map_smul r t)

@[simp] theorem lowerToFE_tmul (x : L) (y : C) (n : N) :
    lowerToFE Q i γ a N (BalancedTensor.tmul (BalancedTensor.tmul x y) n) =
      BalancedTensor.tmul (leftToInd Q i γ a x) (coeffAct Q i γ a N y n) := rfl

def coeffIdem : C := ⟨e, by
  change lowerLastCyc Q i γ a 1 * e = e
  rw [← idem_eq, AbsentColour.lastIdem_mul]⟩

def insertIdem : AbsentColour.IndCorner Q i a γ →ₗ[Rl] LowerCyclotomic Q i γ a where
  toFun x := BalancedTensor.tmul ((leftToInd Q i γ a).symm x) (coeffIdem Q i γ a)
  map_add' x y := by rw [map_add, BalancedTensor.add_tmul]
  map_smul' r x := by rw [map_smul, BalancedTensor.smul_tmul']; rfl

theorem insertIdem_balance (x : AbsentColour.IndCorner Q i a γ) (r : Rg) :
    insertIdem Q i γ a (op r • x) = op (ι r) • insertIdem Q i γ a x := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  change BalancedTensor.tmul ((leftToInd Q i γ a).symm (op (CycKLR.mk k Q a γ r) • x)) _ = _
  have hx : (leftToInd Q i γ a).symm (op (CycKLR.mk k Q a γ r) • x) =
      op r • (leftToInd Q i γ a).symm x := by
    apply Subtype.ext
    change x.1 * ι (CycKLR.mk k Q a γ r) = x.1 * lowerLastCyc Q i γ a r
    rw [AbsentColour.cyclotomicLast_mk]; rfl
  change BalancedTensor.tmul _ _ = op (ι (CycKLR.mk k Q a γ r)) • BalancedTensor.tmul ((leftToInd Q i γ a).symm x) (coeffIdem Q i γ a)
  rw [hx, BalancedTensor.op_smul_tmul, lowerCyclotomic_op_smul_tmul]
  congr 1
  apply Subtype.ext
  change lowerLastCyc Q i γ a r * e = e * ι (CycKLR.mk k Q a γ r)
  rw [AbsentColour.cyclotomicLast_mk, idem_eq]
  change lowerLastCyc Q i γ a r * lowerLastCyc Q i γ a 1 =
    lowerLastCyc Q i γ a 1 * lowerLastCyc Q i γ a r
  rw [← map_mul, ← map_mul, mul_one, one_mul]

def feToLower : FE Q i γ a N →ₗ[Rl] LowerTensor Q i γ a N :=
  BalancedTensor.liftB
    (((BalancedTensor.mkBil k Rl Rl (LowerCyclotomic Q i γ a) N).comp
      ((insertIdem Q i γ a).restrictScalars k)).compl₂ (fixSub k N e).subtype)
    (fun x r n => by
      change BalancedTensor.tmul (insertIdem Q i γ a (op r • x)) n.1 = _
      rw [insertIdem_balance, BalancedTensor.op_smul_tmul]; rfl)
    (fun r x n => by
      change BalancedTensor.tmul (insertIdem Q i γ a (r • x)) n.1 = r • BalancedTensor.tmul (insertIdem Q i γ a x) n.1
      rw [map_smul, BalancedTensor.smul_tmul'])

@[simp] theorem feToLower_tmul (x : AbsentColour.IndCorner Q i a γ) (n : AbsentColour.Res Q i a γ N) :
    feToLower Q i γ a N (BalancedTensor.tmul x n) =
      BalancedTensor.tmul (insertIdem Q i γ a x) n.1 := rfl

theorem lowerToFE_feToLower (t : FE Q i γ a N) :
    lowerToFE Q i γ a N (feToLower Q i γ a N t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul x n =>
    rw [feToLower_tmul]
    change lowerToFE Q i γ a N (BalancedTensor.tmul
      (BalancedTensor.tmul ((leftToInd Q i γ a).symm x) (coeffIdem Q i γ a)) n.1) = _
    rw [lowerToFE_tmul, LinearEquiv.apply_symm_apply]
    congr 1
    exact Subtype.ext n.2

theorem feToLower_lowerToFE (t : LowerTensor Q i γ a N) :
    feToLower Q i γ a N (lowerToFE Q i γ a N t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul z n =>
    induction z using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.zero_tmul, map_zero]
    | add z w hz hw => simp only [BalancedTensor.add_tmul, map_add, hz, hw]
    | tmul x y =>
      rw [lowerToFE_tmul, feToLower_tmul]
      change BalancedTensor.tmul (BalancedTensor.tmul x (coeffIdem Q i γ a)) (y.1 • n) = _
      rw [← BalancedTensor.op_smul_tmul, lowerCyclotomic_op_smul_tmul]
      congr 2
      apply Subtype.ext
      change e * y.1 = y.1
      rw [idem_eq]; exact y.2

/-- Genuine induction after restriction, compared by multiplication, over the cyclotomic balancing algebra. -/
def indResEquiv : FE Q i γ a N ≃ₗ[Rl] LowerTensor Q i γ a N :=
  LinearEquiv.ofLinearMap (feToLower Q i γ a N) (lowerToFE Q i γ a N)
    (LinearMap.ext (feToLower_lowerToFE Q i γ a N))
    (LinearMap.ext (lowerToFE_feToLower Q i γ a N))

variable {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module (CycKLR k Q a ({i} + γ)) N'] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N']

abbrev feMap (f : N →ₗ[Rl] N') : FE Q i γ a N →ₗ[Rl] FE Q i γ a N' :=
  AbsentColour.indMap Q i a γ (AbsentColour.Res Q i a γ N) (AbsentColour.resMap Q i a γ N f)

theorem indResEquiv_natural (f : N →ₗ[Rl] N') (t : FE Q i γ a N) :
    indResEquiv Q i γ a N' (feMap Q i γ a N f t) =
      BalancedTensor.mapRight f (indResEquiv Q i γ a N t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul x n => rfl

def efMiddleEquiv : AbsentColour.EF Q i a β N ≃ₗ[Rl]
    BalancedTensor k Rl Rl (MiddleCyclotomic Q i γ a) N :=
  AbsentColour.resIndEquiv Q i a β N

end Categorification.KLR.KLRAlgebra.PresentColour

namespace Categorification.BalancedTensor
open MulOpposite
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
  {M M' : Type*} [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
  [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module R M'] [IsScalarTower k R M']
  [Module Rᵐᵒᵖ M'] [SMulCommClass R Rᵐᵒᵖ M']
  {N : Type*} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]

/-- Tensor a map preserving both actual outer actions. -/
def mapLeft (f : M →ₗ[R] M') (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) :
    BalancedTensor k R R M N →ₗ[R] BalancedTensor k R R M' N :=
  liftB ((mkBil k R R M' N).comp (f.restrictScalars k))
    (fun m r n => by change tmul (f (op r • m)) n = tmul (f m) (r • n); rw [hf, op_smul_tmul])
    (fun r m n => by change tmul (f (r • m)) n = r • tmul (f m) n; rw [map_smul, smul_tmul'])

omit [SMulCommClass R Rᵐᵒᵖ M'] [IsScalarTower k R N] in
@[simp] theorem mapLeft_tmul (f : M →ₗ[R] M') (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (m : M) (n : N) : mapLeft (k := k) f hf (tmul m n) = tmul (f m) n := rfl

def congrLeft (f : M ≃ₗ[R] M') (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) :
    BalancedTensor k R R M N ≃ₗ[R] BalancedTensor k R R M' N :=
  LinearEquiv.ofLinearMap (mapLeft f.toLinearMap hf)
    (mapLeft f.symm.toLinearMap (fun r m => by
      apply f.injective
      change f (f.symm (r • m)) = f (r • f.symm m)
      rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]))
    (extB fun m n => by change tmul (f (f.symm m)) n = tmul m n; rw [LinearEquiv.apply_symm_apply])
    (extB fun m n => by change tmul (f.symm (f m)) n = tmul m n; rw [LinearEquiv.symm_apply_apply])

variable (M N) (h : ℕ)

def prodFinTo : BalancedTensor k R R (M × (Fin h → R)) N →ₗ[R]
    BalancedTensor k R R M N × (Fin h → N) :=
  liftB (LinearMap.mk₂ k (fun z n => (tmul z.1 n, fun d => z.2 d • n))
    (fun z w n => by ext; exacts [add_tmul _ _ _, add_smul _ _ _])
    (fun c z n => by ext; exacts [smul_tmul _ _ _, smul_assoc _ _ _])
    (fun z n m => by ext; exacts [tmul_add _ _ _, smul_add _ _ _])
    (fun c z n => by ext; exacts [tmul_smul _ _ _, smul_comm _ _ _]))
    (fun z r n => by
      change (tmul (op r • z.1) n, fun d => (z.2 d * r) • n) = (tmul z.1 (r • n), fun d => z.2 d • (r • n))
      ext; exacts [op_smul_tmul _ _ _, mul_smul _ _ _])
    (fun r z n => by
      change (tmul (r • z.1) n, fun d => (r * z.2 d) • n) = r • (tmul z.1 n, fun d => z.2 d • n)
      ext; exacts [(smul_tmul' _ _ _).symm, mul_smul _ _ _])

def prodFinIn : BalancedTensor k R R M N →ₗ[R] BalancedTensor k R R (M × (Fin h → R)) N :=
  mapLeft (LinearMap.inl R M (Fin h → R)) (fun r m => by ext; rfl; simp)

def prodFinDots : (Fin h → N) →ₗ[R] BalancedTensor k R R (M × (Fin h → R)) N where
  toFun v := ∑ d : Fin h, tmul (0, Pi.single d 1) (v d)
  map_add' v w := by simp only [Pi.add_apply, tmul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [← op_smul_tmul, smul_tmul']
    congr 1
    ext j
    · simp
    · classical
      by_cases hd : d = j <;> simp [hd]

def prodFinFrom := (prodFinIn (k := k) (R := R) M N h).coprod (prodFinDots (k := k) (R := R) M N h)

theorem prodFinTo_from (z : BalancedTensor k R R M N × (Fin h → N)) :
    prodFinTo (k := k) (R := R) M N h (prodFinFrom M N h z) = z := by
  obtain ⟨t, v⟩ := z
  have ht : prodFinTo (k := k) (R := R) M N h (prodFinIn M N h t) = (t, 0) := by
    induction t using induction_on with
    | zero => simp only [map_zero]; rfl
    | add t u ht hu => simp only [map_add, ht, hu, Prod.mk_add_mk, add_zero]
    | tmul m n => change (tmul m n, fun d : Fin h => (0 : R) • n) = _; simp only [zero_smul]; rfl
  change prodFinTo (k := k) (R := R) M N h (prodFinIn M N h t + prodFinDots M N h v) = _
  rw [map_add, ht]
  have hv : prodFinTo (k := k) (R := R) M N h (prodFinDots M N h v) = (0, v) := by
    change prodFinTo (k := k) (R := R) M N h (∑ d, tmul (0, Pi.single d 1) (v d)) = _
    rw [map_sum]
    ext j
    · change (LinearMap.fst R (BalancedTensor k R R M N) (Fin h → N)) (∑ d : Fin h, (tmul (0 : M) (v d), fun j => (Pi.single d (1 : R) : Fin h → R) j • v d)) = 0
      rw [map_sum]
      simp
    · change ((LinearMap.proj j).comp (LinearMap.snd R (BalancedTensor k R R M N) (Fin h → N))) (∑ d : Fin h, (tmul (0 : M) (v d), fun j => (Pi.single d (1 : R) : Fin h → R) j • v d)) = v j
      rw [map_sum]
      change (∑ d : Fin h, (Pi.single d (1 : R) : Fin h → R) j • v d) = v j
      classical
      simp [Pi.single_apply, ite_smul]
  rw [hv]; simp

theorem prodFinFrom_to (t : BalancedTensor k R R (M × (Fin h → R)) N) :
    prodFinFrom M N h (prodFinTo (k := k) (R := R) M N h t) = t := by
  induction t using induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul z n =>
    change tmul (z.1, 0) n + (∑ d : Fin h, tmul (0, Pi.single d 1) (z.2 d • n)) = (tmul z n : BalancedTensor k R R (M × (Fin h → R)) N)
    simp only [← op_smul_tmul]
    have hs : (∑ d : Fin h, op (z.2 d) • ((0 : M), Pi.single d (1 : R))) = (0, z.2) := by
      ext j
      · change (LinearMap.fst R M (Fin h → R)) (∑ d : Fin h, op (z.2 d) • ((0 : M), Pi.single d (1 : R))) = 0
        rw [map_sum]
        simp
      · change ((LinearMap.proj j).comp (LinearMap.snd R M (Fin h → R))) (∑ d : Fin h, op (z.2 d) • ((0 : M), Pi.single d (1 : R))) = z.2 j
        rw [map_sum]
        change (∑ d : Fin h, (Pi.single d (1 : R) : Fin h → R) j * z.2 d) = z.2 j
        classical
        simp [Pi.single_apply]
    have hadd : ∀ (s : Finset (Fin h)) (f : Fin h → M × (Fin h → R)),
        tmul (∑ d ∈ s, f d) n = (∑ d ∈ s, tmul (f d) n : BalancedTensor k R R (M × (Fin h → R)) N) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | @insert d s hd hs => simp only [Finset.sum_insert hd, add_tmul, hs]
    rw [← hadd, hs, ← add_tmul]
    congr 1
    simp

def prodFin : BalancedTensor k R R (M × (Fin h → R)) N ≃ₗ[R]
    BalancedTensor k R R M N × (Fin h → N) :=
  LinearEquiv.ofLinearMap (prodFinTo (k := k) (R := R) M N h) (prodFinFrom M N h)
    (LinearMap.ext (prodFinTo_from M N h)) (LinearMap.ext (prodFinFrom_to M N h))

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

theorem mapLeft_natural (f : M →ₗ[R] M') (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (g : N →ₗ[R] N') (t : BalancedTensor k R R M N) :
    mapRight g (mapLeft f hf t) = mapLeft f hf (mapRight g t) := by
  induction t using induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul m n => rfl

theorem congrLeft_natural (f : M ≃ₗ[R] M') (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (g : N →ₗ[R] N') (t : BalancedTensor k R R M N) :
    mapRight g (congrLeft f hf t) = congrLeft f hf (mapRight g t) :=
  mapLeft_natural M N f.toLinearMap hf g t

theorem prodFin_natural (g : N →ₗ[R] N') (t : BalancedTensor k R R (M × (Fin h → R)) N) :
    prodFin M N' h (mapRight g t) =
      (mapRight g (prodFin M N h t).1, fun d => g ((prodFin M N h t).2 d)) := by
  induction t using induction_on with
  | zero => simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]; rfl
  | add t u ht hu =>
    simp only [map_add, ht, hu, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rfl
  | tmul z n =>
    change (tmul z.1 (g n), fun d => z.2 d • g n) = (tmul z.1 (g n), fun d => g (z.2 d • n))
    simp only [map_smul]

theorem prodFin_symm_natural (g : N →ₗ[R] N') (z : BalancedTensor k R R M N × (Fin h → N)) :
    mapRight g ((prodFin M N h).symm z) =
      (prodFin M N' h).symm (mapRight g z.1, fun d => g (z.2 d)) := by
  apply (prodFin M N' h).injective
  rw [prodFin_natural, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem prodFin_symm_tmul (m : M) (n : N) :
    (prodFin (k := k) (R := R) M N h).symm (tmul m n, 0) = tmul (m, 0) n := by
  apply (prodFin M N h).injective
  rw [LinearEquiv.apply_symm_apply]
  change (tmul m n, 0) = (tmul m n, fun d : Fin h => (0 : R) • n)
  simp only [zero_smul]; rfl

theorem prodFin_symm_zero (v : Fin h → N) :
    (prodFin (k := k) (R := R) M N h).symm (0, v) =
      ∑ d : Fin h, tmul ((0 : M), Pi.single d 1) (v d) := by
  change prodFinIn (k := k) (R := R) M N h 0 + prodFinDots M N h v = _
  rw [map_zero, zero_add]; rfl

end Categorification.BalancedTensor

namespace Categorification.KLR.KLRAlgebra.PresentColour
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I) (a : I → Polynomial k)
local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "Rl" => CycKLR k Q a β
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (CycKLR k Q a ({i} + γ)) N] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N]
  {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module (CycKLR k Q a ({i} + γ)) N'] [IsScalarTower k (CycKLR k Q a ({i} + γ)) N']

theorem efMiddleEquiv_symm_natural (f : N →ₗ[Rl] N')
    (t : BalancedTensor k Rl Rl (MiddleCyclotomic Q i γ a) N) :
    AbsentColour.efMap Q i a β N f ((efMiddleEquiv Q i γ a N).symm t) =
      (efMiddleEquiv Q i γ a N').symm (BalancedTensor.mapRight f t) := by
  change BalancedTensor k Rl Rl (AbsentColour.Corner Q i a β) N at t
  apply Subtype.ext
  change BalancedTensor.mapRight f (AbsentColour.includeTensor Q i a β N t) =
    AbsentColour.includeTensor Q i a β N' (BalancedTensor.mapRight f t)
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul z n => rfl

variable (hsym : KLRSymm Q)
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "pos" => cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg
local notation "neg" => cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg

/-- The nonnegative commutator on genuine induction/restriction composites. -/
def positiveEquiv (hwt : 0 ≤ wt) :
    (FE Q i γ a N × (Fin (wt).toNat → N)) ≃ₗ[Rl] AbsentColour.EF Q i a β N :=
  ((indResEquiv Q i γ a N).prodCongr (LinearEquiv.refl Rl _)).trans
    ((BalancedTensor.prodFin (LowerCyclotomic Q i γ a) N (wt).toNat).symm.trans
      ((BalancedTensor.congrLeft (pos hwt)
        (cyclotomicCommutatorBimoduleEquiv_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)).trans
        (efMiddleEquiv Q i γ a N).symm))

/-- The nonpositive commutator on genuine induction/restriction composites. -/
def negativeEquiv (hwt : wt ≤ 0) :
    FE Q i γ a N ≃ₗ[Rl] (AbsentColour.EF Q i a β N × (Fin (-wt).toNat → N)) :=
  (indResEquiv Q i γ a N).trans
    ((BalancedTensor.congrLeft (neg hwt)
      (cyclotomicNegativeCommutatorBimoduleEquiv_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)).trans
      ((BalancedTensor.prodFin (MiddleCyclotomic Q i γ a) N (-wt).toNat).trans
        ((efMiddleEquiv Q i γ a N).symm.prodCongr (LinearEquiv.refl Rl _))))

local notation "Pos" => positiveEquiv Q i γ a N hsym hQ ha RD Λ hΛ hdeg
local notation "Neg" => negativeEquiv Q i γ a N hsym hQ ha RD Λ hΛ hdeg

theorem positiveEquiv_natural (hwt : 0 ≤ wt) (f : N →ₗ[Rl] N')
    (z : FE Q i γ a N × (Fin (wt).toNat → N)) :
    AbsentColour.efMap Q i a β N f (Pos hwt z) =
      positiveEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt
        (feMap Q i γ a N f z.1, fun d => f (z.2 d)) := by
  unfold positiveEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [efMiddleEquiv_symm_natural]
  change (efMiddleEquiv Q i γ a N').symm (BalancedTensor.mapRight f
    (BalancedTensor.mapLeft (pos hwt).toLinearMap
      (cyclotomicCommutatorBimoduleEquiv_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt) _)) = _
  rw [BalancedTensor.mapLeft_natural, BalancedTensor.prodFin_symm_natural, indResEquiv_natural]
  rfl

theorem negativeEquiv_natural (hwt : wt ≤ 0) (f : N →ₗ[Rl] N') (z : FE Q i γ a N) :
    negativeEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt (feMap Q i γ a N f z) =
      (AbsentColour.efMap Q i a β N f (Neg hwt z).1, fun d => f ((Neg hwt z).2 d)) := by
  unfold negativeEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [indResEquiv_natural]
  rw [← BalancedTensor.congrLeft_natural, BalancedTensor.prodFin_natural, efMiddleEquiv_symm_natural]

/-- The positive crossing is the original bimodule crossing, applied to a module coefficient. -/
theorem positiveEquiv_crossing (hwt : 0 ≤ wt) (l : LowerCyclotomic Q i γ a) (n : N) :
    Pos hwt (lowerToFE Q i γ a N (BalancedTensor.tmul l n), 0) =
      (efMiddleEquiv Q i γ a N).symm (BalancedTensor.tmul (cyclotomicSigma Q i γ a l) n) := by
  unfold positiveEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  change (efMiddleEquiv Q i γ a N).symm
    (BalancedTensor.congrLeft (pos hwt) _ ((BalancedTensor.prodFin _ N _).symm
      (feToLower Q i γ a N (lowerToFE Q i γ a N (BalancedTensor.tmul l n)), 0))) = _
  rw [feToLower_lowerToFE, BalancedTensor.prodFin_symm_tmul]
  change (efMiddleEquiv Q i γ a N).symm (BalancedTensor.tmul (pos hwt (l, 0)) n) = _
  congr 2
  rw [cyclotomicCommutatorBimoduleEquiv_apply, cyclotomicCommutatorFinEquiv_apply]
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero]

/-- The positive finite summands are the original dotted units, with their original order. -/
theorem positiveEquiv_dots (hwt : 0 ≤ wt) (v : Fin (wt).toNat → N) :
    Pos hwt (0, v) = (efMiddleEquiv Q i γ a N).symm
      (∑ d : Fin (wt).toNat, BalancedTensor.tmul (pos hwt (0, Pi.single d 1)) (v d)) := by
  unfold positiveEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero]
  rw [BalancedTensor.prodFin_symm_zero, map_sum]
  rfl

/-- The coefficient in `positiveEquiv_dots` is the prescribed dot-unit monomial. -/
theorem positiveEquiv_dot_coefficient (hwt : 0 ≤ wt) (d : Fin (wt).toNat) :
    pos hwt (0, Pi.single d 1) = cyclotomicDotUnit Q i γ a (Polynomial.monomial d 1) := by
  rw [cyclotomicCommutatorBimoduleEquiv_apply, cyclotomicCommutatorFinEquiv_apply, map_zero, zero_add]
  classical
  rw [Finset.sum_eq_single d]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    simp only [Pi.single_eq_of_ne hb, map_zero]
  · exact fun hd => (hd (Finset.mem_univ d)).elim

/-- Both components in the nonpositive range are the original crossing and dotted counits. -/
theorem negativeEquiv_tmul (hwt : wt ≤ 0) (l : LowerCyclotomic Q i γ a) (n : N) :
    Neg hwt (lowerToFE Q i γ a N (BalancedTensor.tmul l n)) =
      ((efMiddleEquiv Q i γ a N).symm (BalancedTensor.tmul (cyclotomicSigma Q i γ a l) n),
        fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d l • n) := by
  unfold negativeEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  have hh : indResEquiv Q i γ a N (lowerToFE Q i γ a N (BalancedTensor.tmul l n)) = BalancedTensor.tmul l n :=
    feToLower_lowerToFE Q i γ a N _
  rw [hh]
  rfl

theorem positiveEquiv_inverse_forward (hwt : 0 ≤ wt) (z : FE Q i γ a N × (Fin (wt).toNat → N)) :
    (Pos hwt).symm (Pos hwt z) = z := (Pos hwt).symm_apply_apply z

theorem positiveEquiv_forward_inverse (hwt : 0 ≤ wt) (z : AbsentColour.EF Q i a β N) :
    Pos hwt ((Pos hwt).symm z) = z := (Pos hwt).apply_symm_apply z

theorem negativeEquiv_inverse_forward (hwt : wt ≤ 0) (z : FE Q i γ a N) :
    (Neg hwt).symm (Neg hwt z) = z := (Neg hwt).symm_apply_apply z

theorem negativeEquiv_forward_inverse (hwt : wt ≤ 0)
    (z : AbsentColour.EF Q i a β N × (Fin (-wt).toNat → N)) :
    Neg hwt ((Neg hwt).symm z) = z := (Neg hwt).apply_symm_apply z

theorem positiveEquiv_symm_natural (hwt : 0 ≤ wt) (f : N →ₗ[Rl] N') (z : AbsentColour.EF Q i a β N) :
    (positiveEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt).symm (AbsentColour.efMap Q i a β N f z) =
      (feMap Q i γ a N f ((Pos hwt).symm z).1, fun d => f (((Pos hwt).symm z).2 d)) := by
  apply (positiveEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply, ← positiveEquiv_natural, LinearEquiv.apply_symm_apply]

theorem negativeEquiv_symm_natural (hwt : wt ≤ 0) (f : N →ₗ[Rl] N')
    (z : AbsentColour.EF Q i a β N × (Fin (-wt).toNat → N)) :
    (negativeEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (AbsentColour.efMap Q i a β N f z.1, fun d => f (z.2 d)) = feMap Q i γ a N f ((Neg hwt).symm z) := by
  apply (negativeEquiv Q i γ a N' hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply, negativeEquiv_natural, LinearEquiv.apply_symm_apply]

end Categorification.KLR.KLRAlgebra.PresentColour
