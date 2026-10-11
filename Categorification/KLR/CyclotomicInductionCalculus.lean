import Categorification.KLR.CyclotomicAdjunction
import Categorification.KLR.CyclotomicPresentModule

/-!
# Dots, crossings, and the braid on cyclotomic induction

Right multiplication by the final dot and the source-normalized crossing `tau = -psi`
defines natural transformations of the original induction functors. The square,
both dot slides, and triple braid are proved from the local KLR relations on every
module, over any commutative ground ring and for arbitrary cyclotomic parameters.
The mixed mate under the original ordinary adjunctions is the existing
`cyclotomicSigma`, after the canonical tensor comparisons.

These are concrete inputs for a cyclotomic `RouqLoc` realization. The commutator
inversions, integer-weight packaging, and opposite-adjunction triangles are not
asserted here. The ordinary induction-left-adjoint-to-restriction orientation is
unchanged; induction is source E and Kang–Kashiwara F.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
open MulOpposite AbsentColour
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "R" => CycKLR k Q a β
local notation "S" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + β)
local notation "ι" => cyclotomicLast Q i a β

def dotElement : S := CycKLR.mk k Q a ({i} + β) (x ⟨Multiset.card β, lastPos_lt i β⟩)

theorem dot_commute (r : R) : Commute (dotElement Q i a β) (ι r) := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [cyclotomicLast_mk]
  exact (commute_x_last_cL (Q := Q) i β r).map (CycKLR.mk k Q a ({i} + β))

def dotCorner : IndCorner Q i a β →ₗ[S] IndCorner Q i a β where
  toFun z := ⟨z.1 * dotElement Q i a β, by
    change z.1 * dotElement Q i a β * ι 1 = z.1 * dotElement Q i a β
    rw [mul_assoc, (dot_commute Q i a β 1).eq, ← mul_assoc]
    exact congrArg (· * dotElement Q i a β) z.2⟩
  map_add' z t := Subtype.ext (add_mul _ _ _)
  map_smul' s z := Subtype.ext (mul_assoc _ _ _)

theorem dotCorner_balance (r : R) (z : IndCorner Q i a β) :
    dotCorner Q i a β (op r • z) = op r • dotCorner Q i a β z := by
  apply Subtype.ext
  change (z.1 * ι r) * dotElement Q i a β = (z.1 * dotElement Q i a β) * ι r
  rw [mul_assoc, ← (dot_commute Q i a β r).eq, ← mul_assoc]

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (CycKLR k Q a β) N]
  [IsScalarTower k (CycKLR k Q a β) N]

def dot : Ind Q i a β N →ₗ[S] Ind Q i a β N :=
  BalancedTensor.liftB
    ((BalancedTensor.mkBil k S R (IndCorner Q i a β) N).comp
      ((dotCorner Q i a β).restrictScalars k))
    (fun z r n => by
      change BalancedTensor.tmul (dotCorner Q i a β (op r • z)) n = _
      rw [dotCorner_balance, BalancedTensor.op_smul_tmul]
      rfl)
    (fun s z n => by
      change BalancedTensor.tmul (dotCorner Q i a β (s • z)) n = s • BalancedTensor.tmul (dotCorner Q i a β z) n
      rw [map_smul, BalancedTensor.smul_tmul'])

omit [IsScalarTower k R N] in
@[simp] theorem dot_tmul (z : IndCorner Q i a β) (n : N) :
    dot Q i a β N (BalancedTensor.tmul z n) = BalancedTensor.tmul (dotCorner Q i a β z) n := rfl

theorem dot_natural {N' : Type*} [AddCommGroup N'] [Module k N'] [Module R N']
    [IsScalarTower k R N'] (f : N →ₗ[R] N') :
    (indMap Q i a β N f).comp (dot Q i a β N) =
      (dot Q i a β N').comp (indMap Q i a β N f) :=
  BalancedTensor.extB fun _ _ => rfl

local notation "β₁" => ((Singleton.singleton i : Multiset I) + β)
local notation "T" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + β₁)
local notation "ι₁" => cyclotomicLast Q i a β₁
local notation "e₀" => indGenerator Q i a β
local notation "e₁" => lastIdem Q i a β₁
local notation "J" => Ind Q i a β₁ (Ind Q i a β N)

/-- Right multiplication by a double-corner centralizer, on original nested induction. -/
def doubleFactor (t : T) (ht : t * e₁ = t) : IndCorner Q i a β →ₗ[k] IndCorner Q i a β₁ where
  toFun y := ⟨ι₁ y.1 * t, by
    change (ι₁ y.1 * t) * e₁ = ι₁ y.1 * t
    rw [mul_assoc, ht]⟩
  map_add' y z := Subtype.ext (by simp only [Submodule.coe_add, map_add, add_mul])
  map_smul' c y := Subtype.ext (by
    change ι₁ (c • y.1) * t = c • (ι₁ y.1 * t)
    rw [map_smul, smul_mul_assoc])

def doubleInnerBil (t : T) (ht : t * e₁ = t) : IndCorner Q i a β →ₗ[k] N →ₗ[k] J :=
  ((BalancedTensor.mkBil k T S (IndCorner Q i a β₁) (Ind Q i a β N)).comp
    (doubleFactor Q i a β t ht)).compl₂
      ((BalancedTensor.mkBil k S R (IndCorner Q i a β) N) e₀)

omit [IsScalarTower k R N] in
theorem doubleInnerBil_balance (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t) (y : IndCorner Q i a β) (r : R) (n : N) :
    doubleInnerBil Q i a β N t ht (op r • y) n =
      doubleInnerBil Q i a β N t ht y (r • n) := by
  change BalancedTensor.tmul (doubleFactor Q i a β t ht (op r • y)) (BalancedTensor.tmul e₀ n) =
    BalancedTensor.tmul (doubleFactor Q i a β t ht y) (BalancedTensor.tmul e₀ (r • n))
  have hy : doubleFactor Q i a β t ht (op r • y) = op (ι r) • doubleFactor Q i a β t ht y := by
    apply Subtype.ext
    change ι₁ (y.1 * ι r) * t = (ι₁ y.1 * t) * ι₁ (ι r)
    rw [map_mul, mul_assoc, (hc r).eq, ← mul_assoc]
  rw [hy, BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul',
    ← indGenerator_balance, BalancedTensor.op_smul_tmul]

def doubleInner (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t) : Ind Q i a β N →ₗ[k] J :=
  BalancedTensor.lift (doubleInnerBil Q i a β N t ht)
    (doubleInnerBil_balance Q i a β N t ht hc)

omit [IsScalarTower k R N] in
@[simp] theorem doubleInner_tmul (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t) (y : IndCorner Q i a β) (n : N) :
    doubleInner Q i a β N t ht hc (BalancedTensor.tmul y n) =
      BalancedTensor.tmul (doubleFactor Q i a β t ht y) (BalancedTensor.tmul e₀ n) := rfl

omit [IsScalarTower k R N] in
theorem doubleInner_smul (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t) (s : S) (m : Ind Q i a β N) :
    doubleInner Q i a β N t ht hc (s • m) = ι₁ s • doubleInner Q i a β N t ht hc m := by
  induction m using BalancedTensor.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add m m' hm hm' => simp only [smul_add, map_add, hm, hm']
  | tmul y n =>
    rw [BalancedTensor.smul_tmul', doubleInner_tmul, doubleInner_tmul, BalancedTensor.smul_tmul']
    congr 1
    apply Subtype.ext
    change ι₁ (s * y.1) * t = ι₁ s * (ι₁ y.1 * t)
    rw [map_mul, mul_assoc]

def doubleEnd (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t) : J →ₗ[T] J :=
  BalancedTensor.liftB
    (LinearMap.mk₂ k (fun z m => z.1 • doubleInner Q i a β N t ht hc m)
      (fun z z' m => add_smul z.1 z'.1 _)
      (fun c z m => smul_assoc c z.1 _)
      (fun z m m' => by rw [map_add, smul_add])
      (fun c z m => by rw [map_smul, smul_comm]))
    (fun z s m => by
      change (z.1 * ι₁ s) • doubleInner Q i a β N t ht hc m =
        z.1 • doubleInner Q i a β N t ht hc (s • m)
      rw [doubleInner_smul, mul_smul])
    (fun s z m => mul_smul s z.1 _)

omit [IsScalarTower k R N] in
@[simp] theorem doubleEnd_tmul (t : T) (ht : t * e₁ = t)
    (hc : ∀ r : R, Commute (ι₁ (ι r)) t)
    (z : IndCorner Q i a β₁) (y : IndCorner Q i a β) (n : N) :
    doubleEnd Q i a β N t ht hc (BalancedTensor.tmul z (BalancedTensor.tmul y n)) =
      BalancedTensor.tmul (z.1 • doubleFactor Q i a β t ht y) (BalancedTensor.tmul e₀ n) := by
  change z.1 • doubleInner Q i a β N t ht hc (BalancedTensor.tmul y n) = _
  rw [doubleInner_tmul, BalancedTensor.smul_tmul']

def doubleIdem : T := ι₁ (ι 1)
def crossingElement : T := -(CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))) * doubleIdem Q i a β

theorem double_commute (r : R) :
    Commute (ι₁ (ι r)) (CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))) := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [cyclotomicLast_mk, cyclotomicLast_mk]
  exact (doubleLast_commute Q i β r).map (CycKLR.mk k Q a ({i} + β₁))

theorem doubleIdem_mul : doubleIdem Q i a β * doubleIdem Q i a β = doubleIdem Q i a β := by
  change ι₁ (ι 1) * ι₁ (ι 1) = ι₁ (ι 1)
  rw [← map_mul, ← map_mul, one_mul]

theorem doubleIdem_cut : doubleIdem Q i a β * e₁ = doubleIdem Q i a β := by
  change ι₁ (ι 1) * ι₁ 1 = ι₁ (ι 1)
  rw [← map_mul, mul_one]

theorem crossingElement_cut : crossingElement Q i a β * e₁ = crossingElement Q i a β := by
  rw [crossingElement, mul_assoc, doubleIdem_cut]

theorem crossingElement_commute (r : R) : Commute (ι₁ (ι r)) (crossingElement Q i a β) := by
  apply (double_commute Q i a β r).neg_right.mul_right
  change ι₁ (ι r) * ι₁ (ι 1) = ι₁ (ι 1) * ι₁ (ι r)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_one, one_mul]

omit [DecidableEq I] in
/-- Both appended labels really are the chosen colour. -/
theorem doubleLast_labels (s : Seq β) :
    (Seq.cast (add_comm β₁ {i}) ((Seq.cast (add_comm β {i}) (s.append default)).append default)).1
      ⟨Multiset.card β, by simp⟩ =
    (Seq.cast (add_comm β₁ {i}) ((Seq.cast (add_comm β {i}) (s.append default)).append default)).1
      ⟨Multiset.card β + 1, by simp⟩ := by
  simp only [Seq.cast_apply]
  rw [Seq.append_apply_lt _ _ _ (by change Multiset.card β < Multiset.card β₁; simp), Seq.cast_apply,
    Seq.append_apply_ge _ _ _ (by change Multiset.card β ≤ Multiset.card β; rfl),
    Seq.append_apply_ge _ _ _ (by change Multiset.card β₁ ≤ Multiset.card β + 1; simp)]
  exact (Multiset.mem_singleton.1 (Seq.mem _ _)).trans
    (Multiset.mem_singleton.1 (Seq.mem _ _)).symm

theorem doubleLast_square_raw :
    (ψ (Multiset.card β) * ψ (Multiset.card β) * cL Q i β₁ (cL Q i β 1) :
      KLRAlgebra k Q ({i} + β₁)) = 0 := by
  rw [← sum_e (k := k) (Q := Q) (ν := β)]
  change _ * ((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s) = 0
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s _
  change _ * cL Q i β₁ (cL Q i β (e s)) = 0
  rw [cL_e, cL_e, ψ_sq _ (by simp), ite_eq_left (doubleLast_labels i β s)]

theorem crossingElement_square : crossingElement Q i a β * crossingElement Q i a β = 0 := by
  let p : T := CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))
  have hd : Commute (doubleIdem Q i a β) p := double_commute Q i a β 1
  have hs : p * p * doubleIdem Q i a β = 0 := by
    change CycKLR.mk k Q a ({i} + β₁) _ * CycKLR.mk k Q a ({i} + β₁) _ * ι₁ (ι 1) = 0
    rw [← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk, cyclotomicLast_mk,
      ← map_mul, ← map_mul, doubleLast_square_raw, map_zero]
  change (-p * doubleIdem Q i a β) * (-p * doubleIdem Q i a β) = 0
  calc
    _ = (p * p) * (doubleIdem Q i a β * doubleIdem Q i a β) := by
      simp only [neg_mul, mul_neg, neg_neg]
      calc
        _ = p * (doubleIdem Q i a β * p) * doubleIdem Q i a β := by simp only [mul_assoc]
        _ = _ := by rw [hd.eq]; simp only [mul_assoc]
    _ = 0 := by rw [doubleIdem_mul, hs]

/-- The crossing acts on actual double induction, not on polynomial coordinates. -/
def crossing : J →ₗ[T] J :=
  doubleEnd Q i a β N (crossingElement Q i a β) (crossingElement_cut Q i a β)
    (crossingElement_commute Q i a β)

theorem crossingElement_right : crossingElement Q i a β * doubleIdem Q i a β = crossingElement Q i a β := by
  rw [crossingElement, mul_assoc, doubleIdem_mul]

def prevDot : T := CycKLR.mk k Q a ({i} + β₁) (x ⟨Multiset.card β, by simp⟩)

theorem prevDot_image : ι₁ (dotElement Q i a β) = prevDot Q i a β * e₁ := by
  rw [dotElement, cyclotomicLast_mk, cL_x, map_mul, lastIdem, cyclotomicLast_one]
  rfl

theorem crossingElement_leftCut : e₁ * crossingElement Q i a β = crossingElement Q i a β := by
  have hd := (double_commute Q i a β 1).neg_right.eq
  change doubleIdem Q i a β * -CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β)) =
    -CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β)) * doubleIdem Q i a β at hd
  have he : e₁ * doubleIdem Q i a β = doubleIdem Q i a β := by
    change ι₁ 1 * ι₁ (ι 1) = ι₁ (ι 1)
    rw [← map_mul, one_mul]
  rw [crossingElement, ← hd, ← mul_assoc, he, hd]

theorem doubleLast_slide_raw :
    ((x ⟨Multiset.card β, by simp⟩ * ψ (Multiset.card β) -
      ψ (Multiset.card β) * x ⟨Multiset.card β + 1, by simp⟩) * cL Q i β₁ (cL Q i β 1) :
      KLRAlgebra k Q ({i} + β₁)) = cL Q i β₁ (cL Q i β 1) := by
  rw [← sum_e (k := k) (Q := Q) (ν := β)]
  change _ * ((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s) =
    ((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s)
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change _ * cL Q i β₁ (cL Q i β (e s)) = cL Q i β₁ (cL Q i β (e s))
  rw [cL_e, cL_e, dot_cross_left _ (by simp), ite_eq_left (doubleLast_labels i β s)]

theorem crossingElement_slide :
    crossingElement Q i a β * dotElement Q i a β₁ =
      ι₁ (dotElement Q i a β) * crossingElement Q i a β + doubleIdem Q i a β := by
  let p : T := CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))
  have hs : (prevDot Q i a β * p - p * dotElement Q i a β₁) * doubleIdem Q i a β = doubleIdem Q i a β := by
    have h := congrArg (CycKLR.mk k Q a ({i} + β₁)) (doubleLast_slide_raw Q i β)
    simp only [map_mul, map_sub] at h
    have hd : CycKLR.mk k Q a ({i} + β₁) (cL Q i β₁ (cL Q i β 1)) = doubleIdem Q i a β := by
      rw [doubleIdem, ← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk, cyclotomicLast_mk]
    rw [hd] at h
    have hx : dotElement Q i a β₁ = CycKLR.mk k Q a ({i} + β₁) (x ⟨Multiset.card β + 1, by simp⟩) := by
      unfold dotElement
      congr 2
      apply Fin.ext
      simp
    simpa only [hx, prevDot, p] using h
  have hc : Commute (doubleIdem Q i a β) (dotElement Q i a β₁) :=
    (dot_commute Q i a β₁ (ι 1)).symm
  rw [prevDot_image, mul_assoc, crossingElement_leftCut]
  change (-p * doubleIdem Q i a β) * dotElement Q i a β₁ =
    prevDot Q i a β * (-p * doubleIdem Q i a β) + doubleIdem Q i a β
  calc
    _ = prevDot Q i a β * (-p * doubleIdem Q i a β) +
        (prevDot Q i a β * p - p * dotElement Q i a β₁) * doubleIdem Q i a β := by
      rw [mul_assoc, hc.eq]
      noncomm_ring
    _ = _ := by rw [hs]

theorem doubleLast_slide_raw' :
    ((ψ (Multiset.card β) * x ⟨Multiset.card β, by simp⟩ -
      x ⟨Multiset.card β + 1, by simp⟩ * ψ (Multiset.card β)) * cL Q i β₁ (cL Q i β 1) :
      KLRAlgebra k Q ({i} + β₁)) = cL Q i β₁ (cL Q i β 1) := by
  rw [← sum_e (k := k) (Q := Q) (ν := β)]
  change _ * ((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s) =
    ((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s)
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change _ * cL Q i β₁ (cL Q i β (e s)) = cL Q i β₁ (cL Q i β (e s))
  rw [cL_e, cL_e, dot_cross_right _ (by simp), ite_eq_left (doubleLast_labels i β s)]

theorem doubleIdem_prevDot : Commute (doubleIdem Q i a β) (prevDot Q i a β) := by
  have h : Commute (cL Q i β₁ (cL Q i β 1))
      (x ⟨Multiset.card β, by simp⟩ : KLRAlgebra k Q ({i} + β₁)) := by
    rw [← sum_e (k := k) (Q := Q) (ν := β)]
    change Commute (((cLLinear (Q := Q) i β₁).comp (cLLinear i β)) (∑ s : Seq β, e s)) _
    rw [map_sum]
    apply Commute.sum_left
    intro s _
    change Commute (cL Q i β₁ (cL Q i β (e s))) _
    rw [cL_e, cL_e]
    exact (x_mul_e _ _).symm
  have hd : CycKLR.mk k Q a ({i} + β₁) (cL Q i β₁ (cL Q i β 1)) = doubleIdem Q i a β := by
    rw [doubleIdem, ← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk, cyclotomicLast_mk]
  convert h.map (CycKLR.mk k Q a ({i} + β₁)) using 1
  · exact hd.symm
  · rfl

theorem crossingElement_slide' :
    dotElement Q i a β₁ * crossingElement Q i a β =
      crossingElement Q i a β * ι₁ (dotElement Q i a β) + doubleIdem Q i a β := by
  let p : T := CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))
  have hs : (p * prevDot Q i a β - dotElement Q i a β₁ * p) * doubleIdem Q i a β = doubleIdem Q i a β := by
    have h := congrArg (CycKLR.mk k Q a ({i} + β₁)) (doubleLast_slide_raw' Q i β)
    simp only [map_mul, map_sub] at h
    have hd : CycKLR.mk k Q a ({i} + β₁) (cL Q i β₁ (cL Q i β 1)) = doubleIdem Q i a β := by
      rw [doubleIdem, ← map_one (CycKLR.mk k Q a β), cyclotomicLast_mk, cyclotomicLast_mk]
    rw [hd] at h
    have hx : dotElement Q i a β₁ = CycKLR.mk k Q a ({i} + β₁) (x ⟨Multiset.card β + 1, by simp⟩) := by
      unfold dotElement
      congr 2
      apply Fin.ext
      simp
    simpa only [hx, prevDot, p] using h
  have ht : crossingElement Q i a β * ι₁ (dotElement Q i a β) =
      (-p * prevDot Q i a β) * doubleIdem Q i a β := by
    rw [prevDot_image]
    change (-p * doubleIdem Q i a β) * (prevDot Q i a β * e₁) = _
    calc
      _ = (-p * (doubleIdem Q i a β * prevDot Q i a β)) * e₁ := by simp only [mul_assoc]
      _ = _ := by rw [(doubleIdem_prevDot Q i a β).eq]; simp only [mul_assoc, doubleIdem_cut]
  rw [ht]
  change dotElement Q i a β₁ * (-p * doubleIdem Q i a β) = _
  calc
    _ = (-p * prevDot Q i a β) * doubleIdem Q i a β +
        (p * prevDot Q i a β - dotElement Q i a β₁ * p) * doubleIdem Q i a β := by noncomm_ring
    _ = _ := by rw [hs]

omit [IsScalarTower k R N] in
theorem crossing_square : (crossing Q i a β N).comp (crossing Q i a β N) = 0 := by
  apply BalancedTensor.extB
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm', LinearMap.zero_apply, add_zero]
  | tmul y n =>
    change doubleEnd Q i a β N _ _ _ (doubleEnd Q i a β N _ _ _
      (BalancedTensor.tmul z (BalancedTensor.tmul y n))) = 0
    rw [doubleEnd_tmul, doubleEnd_tmul]
    have h : ((z.1 • doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) y).1 •
        doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) e₀) = 0 := by
      apply Subtype.ext
      change (z.1 * (ι₁ y.1 * crossingElement Q i a β)) * (doubleIdem Q i a β * crossingElement Q i a β) = 0
      calc
        _ = (z.1 * ι₁ y.1) * ((crossingElement Q i a β * doubleIdem Q i a β) * crossingElement Q i a β) := by simp only [mul_assoc]
        _ = 0 := by rw [crossingElement_right, crossingElement_square, mul_zero]
    rw [h, BalancedTensor.zero_tmul]

omit [IsScalarTower k R N] in
theorem crossing_slide :
    (dot Q i a β₁ (Ind Q i a β N)).comp (crossing Q i a β N) =
      (crossing Q i a β N).comp (indMap Q i a β₁ _ (dot Q i a β N)) + LinearMap.id := by
  apply BalancedTensor.extB
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm']
  | tmul y n =>
    change dot Q i a β₁ _ (doubleEnd Q i a β N _ _ _ (BalancedTensor.tmul z (BalancedTensor.tmul y n))) =
      doubleEnd Q i a β N _ _ _ (BalancedTensor.tmul z (dot Q i a β N (BalancedTensor.tmul y n))) +
        BalancedTensor.tmul z (BalancedTensor.tmul y n)
    rw [doubleEnd_tmul, dot_tmul, dot_tmul, doubleEnd_tmul]
    have h : dotCorner Q i a β₁ (z.1 • doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) y) =
        z.1 • doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) (dotCorner Q i a β y) + op y.1 • z := by
      apply Subtype.ext
      change (z.1 * (ι₁ y.1 * crossingElement Q i a β)) * dotElement Q i a β₁ =
        z.1 * (ι₁ (y.1 * dotElement Q i a β) * crossingElement Q i a β) + z.1 * ι₁ y.1
      have hy : ι₁ y.1 * doubleIdem Q i a β = ι₁ y.1 := by
        change ι₁ y.1 * ι₁ (ι 1) = ι₁ y.1
        rw [← map_mul]
        exact congrArg ι₁ y.2
      rw [mul_assoc, mul_assoc, crossingElement_slide, mul_add, mul_add, hy, map_mul]
      simp only [mul_assoc]
    rw [h, BalancedTensor.add_tmul, BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul']
    have hy : y.1 • e₀ = y := Subtype.ext y.2
    rw [hy]

omit [IsScalarTower k R N] in
theorem crossing_slide' :
    (crossing Q i a β N).comp (dot Q i a β₁ (Ind Q i a β N)) =
      (indMap Q i a β₁ _ (dot Q i a β N)).comp (crossing Q i a β N) + LinearMap.id := by
  apply BalancedTensor.extB
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm']
  | tmul y n =>
    change doubleEnd Q i a β N _ _ _ (dot Q i a β₁ _ (BalancedTensor.tmul z (BalancedTensor.tmul y n))) =
      BalancedTensor.mapRight (dot Q i a β N)
        (doubleEnd Q i a β N _ _ _ (BalancedTensor.tmul z (BalancedTensor.tmul y n))) +
        BalancedTensor.tmul z (BalancedTensor.tmul y n)
    rw [dot_tmul, doubleEnd_tmul, doubleEnd_tmul, BalancedTensor.mapRight_tmul, dot_tmul]
    have he : dotCorner Q i a β e₀ = dotElement Q i a β • e₀ := by
      apply Subtype.ext
      exact (dot_commute Q i a β 1).eq.symm
    rw [he, ← BalancedTensor.smul_tmul' (dotElement Q i a β) e₀ n, ← BalancedTensor.op_smul_tmul]
    have h : (dotCorner Q i a β₁ z).1 •
        doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) y =
        op (dotElement Q i a β) • (z.1 • doubleFactor Q i a β (crossingElement Q i a β) (crossingElement_cut Q i a β) y) + op y.1 • z := by
      apply Subtype.ext
      change (z.1 * dotElement Q i a β₁) * (ι₁ y.1 * crossingElement Q i a β) =
        (z.1 * (ι₁ y.1 * crossingElement Q i a β)) * ι₁ (dotElement Q i a β) + z.1 * ι₁ y.1
      have hy : ι₁ y.1 * doubleIdem Q i a β = ι₁ y.1 := by
        change ι₁ y.1 * ι₁ (ι 1) = ι₁ y.1
        rw [← map_mul]
        exact congrArg ι₁ y.2
      calc
        _ = (z.1 * ι₁ y.1) * (dotElement Q i a β₁ * crossingElement Q i a β) := by
          rw [mul_assoc, ← mul_assoc (dotElement Q i a β₁), (dot_commute Q i a β₁ y.1).eq]
          simp only [mul_assoc]
        _ = _ := by
          rw [crossingElement_slide', mul_add]
          simp only [mul_assoc, hy]
    rw [h, BalancedTensor.add_tmul]
    congr 1
    have hy : y.1 • e₀ = y := Subtype.ext y.2
    rw [BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul', hy]

theorem crossing_natural {N' : Type*} [AddCommGroup N'] [Module k N'] [Module R N']
    [IsScalarTower k R N'] (f : N →ₗ[R] N') :
    (indMap Q i a β₁ _ (indMap Q i a β N f)).comp (crossing Q i a β N) =
      (crossing Q i a β N').comp (indMap Q i a β₁ _ (indMap Q i a β N f)) := by
  apply BalancedTensor.extB
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm']
  | tmul y n =>
    change BalancedTensor.mapRight (BalancedTensor.mapRight f)
      (doubleEnd Q i a β N _ _ _ (BalancedTensor.tmul z (BalancedTensor.tmul y n))) =
      doubleEnd Q i a β N' _ _ _
        (BalancedTensor.mapRight (BalancedTensor.mapRight f) (BalancedTensor.tmul z (BalancedTensor.tmul y n)))
    simp only [doubleEnd_tmul, BalancedTensor.mapRight_tmul]

open CategoryTheory
open CategoryTheory.Functor (whiskerLeft whiskerRight)
open scoped ModuleCat.Algebra

def dotNat : inductionFunctor.{u,v,w} Q i a β ⟶ inductionFunctor Q i a β where
  app N := ModuleCat.ofHom (dot Q i a β N)
  naturality _ _ f := ModuleCat.hom_ext (dot_natural Q i a β _ f.hom).symm

def crossingNat :
    inductionFunctor.{u,v,w} Q i a β ⋙ inductionFunctor Q i a β₁ ⟶
      inductionFunctor Q i a β ⋙ inductionFunctor Q i a β₁ where
  app N := ModuleCat.ofHom (crossing Q i a β N)
  naturality _ _ f := ModuleCat.hom_ext (crossing_natural Q i a β _ f.hom).symm

theorem crossingNat_square : crossingNat.{u,v,w} Q i a β ≫ crossingNat Q i a β = 0 := by
  ext N : 2
  exact ModuleCat.hom_ext (crossing_square Q i a β N)

theorem crossingNat_slide :
    crossingNat.{u,v,w} Q i a β ≫ whiskerLeft (inductionFunctor Q i a β) (dotNat Q i a β₁) =
      whiskerRight (dotNat Q i a β) (inductionFunctor Q i a β₁) ≫ crossingNat Q i a β + 𝟙 _ := by
  ext N : 2
  exact ModuleCat.hom_ext (crossing_slide Q i a β N)

theorem crossingNat_slide' :
    whiskerLeft (inductionFunctor.{u,v,w} Q i a β) (dotNat Q i a β₁) ≫ crossingNat Q i a β =
      crossingNat Q i a β ≫ whiskerRight (dotNat Q i a β) (inductionFunctor Q i a β₁) + 𝟙 _ := by
  ext N : 2
  exact ModuleCat.hom_ext (crossing_slide' Q i a β N)

/-- The mixed crossing obtained using the original ordinary adjunctions. -/
def mixedMate (M : ModuleCat.{max u v w} S) :
    ((restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M) ⟶
      ((inductionFunctor Q i a β₁ ⋙ restrictionFunctor Q i a β₁).obj M) :=
  ModuleCat.ofHom (homToRes Q i a β₁
    ((indMap Q i a β₁ _ (homFromRes Q i a β
      (N := (restrictionFunctor Q i a β).obj M)
      (LinearMap.id : Res Q i a β M →ₗ[R] Res Q i a β M))).comp
      (crossing Q i a β ((restrictionFunctor Q i a β).obj M))))

theorem mixedMate_tmul (M : ModuleCat.{max u v w} S)
    (y : IndCorner Q i a β) (m : Res Q i a β M) :
    (mixedMate Q i a β M (BalancedTensor.tmul y m)).1 =
      BalancedTensor.tmul
        ((lastIdem Q i a β₁) • doubleFactor Q i a β (crossingElement Q i a β)
          (crossingElement_cut Q i a β) y) m.1 := by
  change BalancedTensor.tmul
    ((lastIdem Q i a β₁) • doubleFactor Q i a β (crossingElement Q i a β)
      (crossingElement_cut Q i a β) y) (lastIdem Q i a β • m.1) = _
  rw [m.2]

theorem mixedMate_eq_adjunction (M : ModuleCat.{max u v w} S) :
    mixedMate Q i a β M =
      (cyclotomicAdjunction Q i a β₁).unit.app _ ≫
        (restrictionFunctor Q i a β₁).map
          ((crossingNat Q i a β).app ((restrictionFunctor Q i a β).obj M)) ≫
        (restrictionFunctor Q i a β₁).map
          ((inductionFunctor Q i a β₁).map ((cyclotomicAdjunction Q i a β).counit.app M)) := rfl

/-- The ordinary-adjunction mate is the existing cyclotomic crossing on all elementary tensors. -/
theorem mixedMate_sigma_tmul (M : ModuleCat.{max u v w} S)
    (x : CornerTensor.Left (lowerLastCyc Q i β a)) (y : LowerCoefficient Q i β a) (m : M) :
    PresentColour.efMiddleEquiv Q i β a M
      (mixedMate Q i a β M (BalancedTensor.tmul (PresentColour.leftToInd Q i β a x)
        (PresentColour.coeffAct Q i β a M y m))) =
      BalancedTensor.tmul (cyclotomicSigma Q i β a (BalancedTensor.tmul x y)) m := by
  change cutTensor Q i a β₁ M (mixedMate Q i a β M
    (BalancedTensor.tmul (PresentColour.leftToInd Q i β a x)
      (PresentColour.coeffAct Q i β a M y m))).1 = _
  rw [mixedMate_tmul, cutTensor_tmul]
  change BalancedTensor.tmul
    (leftCut Q i a β₁ (e₁ • doubleFactor Q i a β (crossingElement Q i a β)
      (crossingElement_cut Q i a β) (PresentColour.leftToInd Q i β a x))) (y.1 • m) = _
  rw [← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  rw [cyclotomicSigma_tmul_canonical]
  change (ι₁ 1 * (ι₁ 1 * (ι₁ x.1 * (-CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β)) * ι₁ (ι 1))))) * ι₁ y.1 = _
  have hy : ι₁ (ι 1) * ι₁ y.1 = ι₁ y.1 := by
    rw [← map_mul]
    congr 1
    rw [cyclotomicLast_one]
    exact y.2
  have hx : ι₁ 1 * ι₁ x.1 = ι₁ x.1 := by rw [← map_mul, one_mul]
  simp only [← mul_assoc] at hx ⊢
  rw [← map_mul, one_mul, hx]
  rw [mul_assoc (ι₁ x.1 * -CycKLR.mk k Q a ({i} + β₁) (ψ (Multiset.card β))), hy]
  rw [map_neg]
  rfl

/-- Change only the scalar-module presentation used by `ModuleCat`; the map is identity on generators. -/
def feRebase (M : ModuleCat.{max u v w} S) :
    PresentColour.FE Q i β a M →ₗ[S]
      (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M :=
  BalancedTensor.mapRight (N := Res Q i a β M) (N' := (restrictionFunctor Q i a β).obj M)
    (LinearMap.id : Res Q i a β M →ₗ[R] Res Q i a β M)

def feUnbase (M : ModuleCat.{max u v w} S) :
    (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M →ₗ[S]
      PresentColour.FE Q i β a M :=
  BalancedTensor.mapRight (N := (restrictionFunctor Q i a β).obj M) (N' := Res Q i a β M)
    (LinearMap.id : Res Q i a β M →ₗ[R] Res Q i a β M)

def feRebaseEquiv (M : ModuleCat.{max u v w} S) :
    PresentColour.FE Q i β a M ≃ₗ[S]
      (restrictionFunctor Q i a β ⋙ inductionFunctor Q i a β).obj M :=
  LinearEquiv.ofLinearMap (feRebase Q i a β M) (feUnbase Q i a β M)
    (BalancedTensor.extB fun _ _ => rfl) (BalancedTensor.extB fun _ _ => rfl)

def sigmaOuter : LowerCyclotomic Q i β a →ₗ[S] MiddleCyclotomic Q i β a where
  toFun := cyclotomicSigma Q i β a
  map_add' := map_add _
  map_smul' := cyclotomicSigma_smul Q i β a

theorem mixedMate_sigma (M : ModuleCat.{max u v w} S) :
    (PresentColour.efMiddleEquiv Q i β a M).toLinearMap.comp
      ((mixedMate Q i a β M).hom.comp
        ((feRebase Q i a β M).comp (PresentColour.lowerToFE Q i β a M))) =
    BalancedTensor.mapLeft (sigmaOuter Q i a β)
      (cyclotomicSigma_op_smul Q i β a) := by
  apply BalancedTensor.extB
  intro t m
  induction t using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.zero_tmul, map_zero]
  | add t t' ht ht' => simp only [BalancedTensor.add_tmul, map_add, ht, ht']
  | tmul x y =>
    change PresentColour.efMiddleEquiv Q i β a M
      (mixedMate Q i a β M (BalancedTensor.tmul (PresentColour.leftToInd Q i β a x)
        (PresentColour.coeffAct Q i β a M y m))) = _
    exact mixedMate_sigma_tmul Q i a β M x y m


local notation "β₂" => ((Singleton.singleton i : Multiset I) + β₁)
local notation "U" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + β₂)
local notation "ι₂" => cyclotomicLast Q i a β₂
local notation "e₂" => indGenerator Q i a β₂
local notation "g₁" => indGenerator Q i a β₁
local notation "K" => Ind Q i a β₂ (Ind Q i a β₁ (Ind Q i a β N))

omit [IsScalarTower k R N] in
theorem tmul_generator (z : IndCorner Q i a β) (n : N) :
    BalancedTensor.tmul z n = z.1 • (BalancedTensor.tmul e₀ n : Ind Q i a β N) := by
  rw [BalancedTensor.smul_tmul']
  congr 1
  exact Subtype.ext z.2.symm

omit [IsScalarTower k R N] in
theorem tmul_move (z : IndCorner Q i a β) (s : R) (n : N) :
    (BalancedTensor.tmul z (s • n) : Ind Q i a β N) =
      BalancedTensor.tmul (op s • z) n := (BalancedTensor.op_smul_tmul z s n).symm

omit [IsScalarTower k R N] in
theorem crossing_generator (n : N) :
    crossing Q i a β N (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) =
      crossingElement Q i a β • (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n) : J) := by
  change doubleEnd Q i a β N _ _ _ _ = _
  rw [doubleEnd_tmul, BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change ι₁ 1 * (doubleIdem Q i a β * crossingElement Q i a β) = crossingElement Q i a β * ι₁ 1
  change e₁ * (doubleIdem Q i a β * crossingElement Q i a β) = crossingElement Q i a β * e₁
  rw [crossingElement_cut]
  have h := (crossingElement_commute Q i a β 1).eq
  change doubleIdem Q i a β * crossingElement Q i a β = crossingElement Q i a β * doubleIdem Q i a β at h
  rw [h, crossingElement_right, crossingElement_leftCut]

omit [IsScalarTower k R N] in
theorem triple_tmul (z : IndCorner Q i a β₂) (y : IndCorner Q i a β₁)
    (x : IndCorner Q i a β) (n : N) :
    (BalancedTensor.tmul z (BalancedTensor.tmul y (BalancedTensor.tmul x n)) : K) =
      (z.1 * ι₂ (y.1 * ι₁ x.1)) •
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) : K) := by
  rw [tmul_generator Q i a β N x n, tmul_move]
  rw [tmul_generator Q i a β₁ _ (op x.1 • y), tmul_move]
  rw [tmul_generator Q i a β₂]
  rfl

def tripleIdem : U := ι₂ (doubleIdem Q i a β)
def lowerPsi : U := CycKLR.mk k Q a ({i} + β₂) (ψ (Multiset.card β))
def upperPsi : U := CycKLR.mk k Q a ({i} + β₂) (ψ (Multiset.card β + 1))

theorem tripleLast_braid_raw :
    ((ψ (Multiset.card β) * ψ (Multiset.card β + 1) * ψ (Multiset.card β) -
      ψ (Multiset.card β + 1) * ψ (Multiset.card β) * ψ (Multiset.card β + 1)) *
      cL Q i β₂ (cL Q i β₁ (cL Q i β 1)) : KLRAlgebra k Q ({i} + β₂)) = 0 := by
  rw [← sum_e (k := k) (Q := Q) (ν := β)]
  change _ * ((cLLinear (Q := Q) i β₂).comp
    ((cLLinear i β₁).comp (cLLinear i β))) (∑ s : Seq β, e s) = 0
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s _
  change _ * cL Q i β₂ (cL Q i β₁ (cL Q i β (e s))) = 0
  rw [cL_e, cL_e, cL_e, braid _ (by simp)]
  apply ite_eq_right
  intro h
  apply h.2
  simp only [Seq.cast_apply]
  rw [Seq.append_apply_lt _ _ _ (by change Multiset.card β < Multiset.card β₂; simp),
    Seq.append_apply_lt _ _ _ (by change Multiset.card β + 1 < Multiset.card β₂; simp)]
  exact doubleLast_labels i β s

theorem lowerPsi_image :
    ι₂ (CycKLR.mk k Q a β₂ (ψ (Multiset.card β))) =
      lowerPsi Q i a β * lastIdem Q i a β₂ := by
  rw [cyclotomicLast_mk, cL_ψ i β₂ (by simp), map_mul, lowerPsi,
    lastIdem, cyclotomicLast_one]

theorem tripleIdem_cut : lastIdem Q i a β₂ * tripleIdem Q i a β = tripleIdem Q i a β := by
  change ι₂ 1 * ι₂ _ = ι₂ _
  rw [← map_mul, one_mul]

theorem lowerCrossing_image : ι₂ (crossingElement Q i a β) =
    -lowerPsi Q i a β * tripleIdem Q i a β := by
  rw [crossingElement, map_mul, map_neg, lowerPsi_image, neg_mul, mul_assoc]
  change -(lowerPsi Q i a β * (lastIdem Q i a β₂ * tripleIdem Q i a β)) = _
  rw [tripleIdem_cut, neg_mul]

omit [IsScalarTower k R N] in
theorem tmul_generator_smul (s : R) (n : N) :
    (BalancedTensor.tmul e₀ (s • n) : Ind Q i a β N) =
      ι s • (BalancedTensor.tmul e₀ n : Ind Q i a β N) := by
  rw [tmul_move, BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change ι 1 * ι s = ι s * ι 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

omit [IsScalarTower k R N] in
theorem tripleIdem_generator (n : N) :
    tripleIdem Q i a β •
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) : K) =
      BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) := by
  change ι₂ (ι₁ (ι 1)) • _ = _
  rw [← tmul_generator_smul, ← tmul_generator_smul, ← tmul_generator_smul, one_smul]

omit [IsScalarTower k R N] in
theorem upper_generator (n : N) :
    crossing Q i a β₁ (Ind Q i a β N)
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n))) =
      -upperPsi Q i a β •
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) : K) := by
  rw [crossing_generator, crossingElement, mul_smul]
  have h : doubleIdem Q i a β₁ •
      (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) : K) =
      BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) := by
    change ι₂ (ι₁ 1) • _ = _
    rw [← tmul_generator_smul, ← tmul_generator_smul, one_smul]
  rw [h]
  congr 2
  simp [upperPsi]

omit [IsScalarTower k R N] in
theorem lower_generator (n : N) :
    indMap Q i a β₂ _ (crossing Q i a β N)
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n))) =
      -lowerPsi Q i a β •
        (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n)) : K) := by
  change BalancedTensor.tmul e₂
    (crossing Q i a β N (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n))) = _
  rw [crossing_generator, tmul_generator_smul, lowerCrossing_image, mul_smul, tripleIdem_generator]

theorem triple_braid_element :
    (lowerPsi Q i a β * upperPsi Q i a β * lowerPsi Q i a β) * tripleIdem Q i a β =
      (upperPsi Q i a β * lowerPsi Q i a β * upperPsi Q i a β) * tripleIdem Q i a β := by
  have h := congrArg (CycKLR.mk k Q a ({i} + β₂)) (tripleLast_braid_raw Q i β)
  have hd : CycKLR.mk k Q a ({i} + β₂) (cL Q i β₂ (cL Q i β₁ (cL Q i β 1))) =
      tripleIdem Q i a β := by
    rw [tripleIdem, doubleIdem, ← map_one (CycKLR.mk k Q a β),
      cyclotomicLast_mk, cyclotomicLast_mk, cyclotomicLast_mk]
  simp only [map_mul, map_sub, map_zero, hd, sub_mul, sub_eq_zero] at h
  exact h

omit [IsScalarTower k R N] in
theorem crossing_braid_generator (n : N) :
    (indMap Q i a β₂ _ (crossing Q i a β N))
      (crossing Q i a β₁ (Ind Q i a β N)
        ((indMap Q i a β₂ _ (crossing Q i a β N))
          (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n))))) =
    crossing Q i a β₁ (Ind Q i a β N)
      ((indMap Q i a β₂ _ (crossing Q i a β N))
        (crossing Q i a β₁ (Ind Q i a β N)
          (BalancedTensor.tmul e₂ (BalancedTensor.tmul g₁ (BalancedTensor.tmul e₀ n))))) := by
  simp only [lower_generator, upper_generator, map_smul]
  simp only [← mul_smul, neg_mul, mul_neg, neg_neg]
  rw [← tripleIdem_generator Q i a β N n, ← mul_smul, ← mul_smul,
    neg_mul, neg_mul]
  simp only [← mul_assoc]
  rw [triple_braid_element]


omit [IsScalarTower k R N] in
/-- The braid holds on the original triple induction of every module. -/
theorem crossing_braid :
    (indMap Q i a β₂ _ (crossing Q i a β N)).comp
      ((crossing Q i a β₁ (Ind Q i a β N)).comp
        (indMap Q i a β₂ _ (crossing Q i a β N))) =
    (crossing Q i a β₁ (Ind Q i a β N)).comp
      ((indMap Q i a β₂ _ (crossing Q i a β N)).comp
        (crossing Q i a β₁ (Ind Q i a β N))) := by
  apply BalancedTensor.extB
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm']
  | tmul y l =>
    induction l using BalancedTensor.induction_on with
    | zero => simp only [BalancedTensor.tmul_zero, map_zero]
    | add l l' hl hl' => simp only [BalancedTensor.tmul_add, map_add, hl, hl']
    | tmul x n =>
      rw [triple_tmul, map_smul, map_smul]
      exact congrArg (fun t => (z.1 * ι₂ (y.1 * ι₁ x.1)) • t)
        (crossing_braid_generator Q i a β N n)

/-- Natural braid, with the associator of the original induction functors explicit. -/
theorem crossingNat_braid :
    let F₀ := inductionFunctor.{u,v,w} Q i a β
    let F₁ := inductionFunctor.{u,v,w} Q i a β₁
    let F₂ := inductionFunctor.{u,v,w} Q i a β₂
    let l := whiskerRight (crossingNat Q i a β) F₂
    let r := (Functor.associator F₀ F₁ F₂).hom ≫
      whiskerLeft F₀ (crossingNat Q i a β₁) ≫ (Functor.associator F₀ F₁ F₂).inv
    l ≫ r ≫ l = r ≫ l ≫ r := by
  dsimp only
  apply NatTrans.ext
  funext N
  apply ModuleCat.hom_ext
  change (indMap Q i a β₂ _ (crossing Q i a β N)).comp
      ((crossing Q i a β₁ (Ind Q i a β N)).comp
        (indMap Q i a β₂ _ (crossing Q i a β N))) =
    (crossing Q i a β₁ (Ind Q i a β N)).comp
      ((indMap Q i a β₂ _ (crossing Q i a β N)).comp
        (crossing Q i a β₁ (Ind Q i a β N)))
  exact crossing_braid Q i a β N


end Categorification.KLR.KLRAlgebra.AbsentColour.InductionCalculus
