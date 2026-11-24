/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotMarkedExitJoints
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.Algebra.BalancedTensorFiniteFamily

/-!
# Kernel-column injectivity at the five-slot right tops

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and (6.21).
Group the lower factor of the balanced tensor by the four exit generators.
A tensor in the kernel then has a marked coefficient relation. The four
supported joint relations annihilate it by balancing.
-/
open scoped BigOperators

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "A" => BraidedStendhalAlgebra k Q Λ ν₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "raw" => ofKLR k Q Λ ν₀
local notation "mk" => violMk k Q Λ ν₀
local notation "π" => AlgHom.comp mk raw
local notation "p" => fun z : Seq μ₀ => π (e z)
variable (t : Seq μ₀)
  (order : redWord t = redWord (fixedTopFourExitCut 2))
local notation "s" => fixedTopFourExitBottom
local notation "v" => fixedTopFourExitCut
local notation "κ" => redWord t
local notation "E" => mk (redProj k Q Λ ν₀ κ)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν₀ κ
local notation "T" => IsIdempotentElem.Corner ord
local notation "C" => RedBlock.crossingSpace (k := k) E (p s)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t 1 2
local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) κ
local notation "inc" => blockKernelColumnInclusion Q Λ t 1 2 s
local notation "cross" => fun (w : List ℕ) (z : Seq μ₀) => π (ψw w*e z)

private theorem lid (v' : Seq μ₀) : p v'*p v'=p v' := by rw [← map_mul π,e_mul_self]
private theorem Eid : E*E=E := (ord).eq
private theorem cutIn (v' : Seq μ₀) (hv : redWord v'=κ) : E*p v'=p v' ∧ p v'*E=p v' :=
  ⟨(map_mul mk _ _).symm.trans (congrArg mk ((redProj_mul_e _ _).trans (ite_eq_left hv))),
   (map_mul mk _ _).symm.trans (congrArg mk ((e_mul_redProj _ _).trans (ite_eq_left hv)))⟩

private theorem crossSupport (w : List ℕ) (v' : Seq μ₀) :
    p (wordProd n₀ w • v')*cross w v'=cross w v' ∧ cross w v'*p v'=cross w v' := by
  constructor
  · rw [← map_mul π,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  · rw [← map_mul π,mul_assoc,e_mul_self]

private theorem exitCut (i : Fin 4) : wordProd n₀ (fiveSlotExitWord i) • s=v i := by
  fin_cases i <;> decide

include order in
private theorem exitOrder (i : Fin 4) : redWord (v i)=κ := by
  exact (show redWord (v i) = redWord (v 2) by fin_cases i <;> decide).trans order.symm

include order in
private def exitLeg (i : Fin 4) : C :=
  ⟨cross (fiveSlotExitWord i) s,⟨by
    have h := (crossSupport Q Λ (fiveSlotExitWord i) s).1
    rw [exitCut] at h
    change E*cross (fiveSlotExitWord i) s=cross (fiveSlotExitWord i) s
    rw [← h,← mul_assoc,(cutIn Q Λ t (v i) (exitOrder t order i)).1,h],
    (crossSupport Q Λ (fiveSlotExitWord i) s).2⟩⟩

private def cutCorner (x : V) : T :=
  ⟨E*x*E,(Subsemigroup.mem_corner_iff ord).2
    ⟨by rw [← mul_assoc E,← mul_assoc E,Eid],
     by rw [mul_assoc _ E,Eid]⟩⟩

include order in
private theorem exitLeg_generate (hQ : KLRSymm Q) (c : C) :
    ∃ d : Fin 4 → T, c=∑ i,d i • exitLeg Q Λ t order i := by
  classical
  obtain ⟨z,hz⟩ := violMk_surjective (Q := Q) (Λ := Λ) c.1
  let S := Finset.univ.filter (fun y : Seq μ₀ => redWord y=κ)
  let coeff (u : Seq μ₀) := if h : redWord u=κ then (fiveSlotExit_generate Q Λ hQ u (h.trans order) z).choose
    else fun _ => 0
  have hcoeff (u : Seq μ₀) (hu : u∈S) :
      raw (e u)*z*raw (e s) = ∑ i, coeff u i*raw (ψw (fiveSlotExitWord i)*e s) := by
    have he := (Finset.mem_filter.mp hu).2
    exact (by simpa only [coeff,dite_eq_left he] using (fiveSlotExit_generate Q Λ hQ u (he.trans order) z).choose_spec)
  have ha : redProj k Q Λ ν₀ κ*z*raw (e s) =
      ∑ i,(∑ u∈S, coeff u i)*raw (ψw (fiveSlotExitWord i)*e s) := by
    calc
      _ = ∑ u∈S, raw (e u)*z*raw (e s) := by
        simp only [S,redProj,redIdem,map_sum,Finset.sum_mul]
      _ = ∑ u∈S, ∑ i, coeff u i*raw (ψw (fiveSlotExitWord i)*e s) :=
        Finset.sum_congr rfl (fun u hu => hcoeff u hu)
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]
  let d (i : Fin 4) := mk (∑ u∈S, coeff u i)
  have hc : c.1=∑ i,d i*(exitLeg Q Λ t order i).1 := by
    have h := congrArg mk ha
    rw [map_mul,map_mul,hz] at h
    change E*c.1*p s=mk _ at h
    rw [c.2.1,c.2.2,map_sum] at h
    exact h.trans (Finset.sum_congr rfl (fun i _ => map_mul _ _ _))
  refine ⟨fun i => cutCorner Q Λ t (d i),?_⟩
  apply Subtype.ext
  change c.1 = (C).subtype (∑ i, cutCorner Q Λ t (d i) • exitLeg Q Λ t order i)
  rw [map_sum]
  change c.1=∑ i, (E*d i*E)*(exitLeg Q Λ t order i).1
  simp only [mul_assoc]
  have lk (i : Fin 4) : E*(exitLeg Q Λ t order i).1=(exitLeg Q Λ t order i).1 := (exitLeg Q Λ t order i).2.1
  simp only [lk,← Finset.mul_sum,← hc,c.2.1]


private def readP : P →ₗ[k] V :=
  (IsIdempotentElem.cornerVal («R» := k) ord).comp ((P).subtype.restrictScalars k)
private def readK : K →ₗ[k] V := (readP Q Λ t).comp ((K).subtype.restrictScalars k)

private theorem readK_injective : Function.Injective (readK Q Λ t) := by
  intro u w h
  exact Subtype.ext (Subtype.ext (Subtype.ext h))

private def loadingStack : BalancedTensor k k T P C →ₗ[k] V :=
  BalancedTensor.lift ((LinearMap.compl₂ (LinearMap.mul k V) (C).subtype).comp (readP Q Λ t))
    (fun x r y => mul_assoc x.1.1 r.1 y.1)

include order in
private theorem sum_exit_stack_zero (x : Fin 4 → K)
    (hz : inc (∑ i,BalancedTensor.tmul (x i) (exitLeg Q Λ t order i))=0) :
    ∑ i, readK Q Λ t (x i)*(exitLeg Q Λ t order i).1=0 := by
  let L := (loadingStack Q Λ t).comp inc
  have H : ∀ i, L (BalancedTensor.tmul (x i) (exitLeg Q Λ t order i)) =
      readK Q Λ t (x i)*(exitLeg Q Λ t order i).1 := fun _ => rfl
  have h := congrArg (loadingStack Q Λ t) hz
  change L (∑ i, BalancedTensor.tmul (x i) (exitLeg Q Λ t order i))=loadingStack Q Λ t 0 at h
  simpa only [map_sum,H,map_zero] using h

private def seam (w : List ℕ) (source : Seq μ₀)
    (hs : redWord source=κ) (ht : redWord (wordProd n₀ w • source)=κ) : T :=
  ⟨cross w source,(Subsemigroup.mem_corner_iff ord).2
    ⟨by
      have h := (crossSupport Q Λ w source).1
      calc E*cross w source = E*(p (wordProd n₀ w • source)*cross w source) :=
            congrArg (E*·) h.symm
        _ = _ := by rw [← mul_assoc,(cutIn Q Λ t _ ht).1,h],
     by
      have h := (crossSupport Q Λ w source).2
      calc cross w source*E = (cross w source*p source)*E := congrArg (·*E) h.symm
        _ = _ := by rw [mul_assoc,(cutIn Q Λ t _ hs).2,h]⟩⟩

include order in
private def exitProj (i : Fin 4) : T :=
  ⟨p (v i),(Subsemigroup.mem_corner_iff ord).2 (cutIn Q Λ t _ (exitOrder t order i))⟩

include order in
private theorem exitProj_fixes_leg (i : Fin 4) : exitProj Q Λ t order i • exitLeg Q Λ t order i=exitLeg Q Λ t order i := by
  apply Subtype.ext
  change p (v i)*cross (fiveSlotExitWord i) s=cross (fiveSlotExitWord i) s
  rw [← exitCut i]
  exact (crossSupport Q Λ _ _).1

private theorem loadingRep_value (u : Seq μ₀) (hu : redWord u=κ) (z : V)
    (cut : p t*z*p u=z) : (blockLoadingRep Q Λ t z).1.1=z := by
  rw [blockLoadingRep_val]
  calc p t*z*E = p t*(p t*z*p u)*E := congrArg (fun y => p t*y*E) cut.symm
    _ = z := by
      rw [← mul_assoc (p t),← mul_assoc (p t),lid,mul_assoc _ (p u),(cutIn Q Λ t _ hu).2,cut]

private def jointRep (u : Seq μ₀) (hu : redWord u=κ) (z : V)
    (cut : p t*z*p u=z) (marked : z ∈ J) : K :=
  ⟨blockLoadingRep Q Λ t z,by
    change (blockLoadingRep Q Λ t z).1.1 ∈ J
    rwa [loadingRep_value Q Λ t u hu z cut]⟩

private theorem jointRep_value (u : Seq μ₀) (hu : redWord u=κ) (z : V)
    (cut : p t*z*p u=z) (marked : z ∈ J) :
    readK Q Λ t (jointRep Q Λ t u hu z cut marked)=z := loadingRep_value Q Λ t u hu z cut

private theorem compose_cross (l w : List ℕ) (u : Seq μ₀)
    (hu : wordProd n₀ w • s=u) :
    cross l u*cross w s=cross (l++w) s := by
  change π (ψw l*e u)*π (ψw w*e s)=π (ψw (l++w)*e s)
  rw [← map_mul,ψw_append,← hu]
  have h : (e (wordProd n₀ w • s) : R)*(ψw w*e s)=ψw w*e s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  rw [mul_assoc,h,mul_assoc]


include order in
private def finiteSeam (w : List ℕ) (source : Seq μ₀)
    (hs : redWord source = redWord (v 2))
    (ht : redWord (wordProd n₀ w • source) = redWord (v 2)) : T :=
  seam Q Λ t w source (hs.trans order.symm) (ht.trans order.symm)

include order in
private def jointArms : Fin 4 → Fin 4 → T :=
  ![![finiteSeam Q Λ t order [2] (v 0) (by decide) (by decide),
      -finiteSeam Q Λ t order [3] (v 1) (by decide) (by decide),0,0],
    ![0,finiteSeam Q Λ t order [1] (v 1) (by decide) (by decide),
      -finiteSeam Q Λ t order [2] (v 2) (by decide) (by decide),0],
    ![finiteSeam Q Λ t order [2,1] (v 0) (by decide) (by decide),0,0,
      -finiteSeam Q Λ t order [3] (v 3) (by decide) (by decide)],
    ![0,0,finiteSeam Q Λ t order [2,3] (v 2) (by decide) (by decide),
      -finiteSeam Q Λ t order [1] (v 3) (by decide) (by decide)]]

include order in
private theorem jointArms_annihilate (j : Fin 4) :
    ∑ i, jointArms Q Λ t order j i • exitLeg Q Λ t order i = 0 := by
  have near := twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) s (by decide)
  have rev := twoBlackReversedMiddleExitWords (Q₀ := stendhalQ Q Λ) 1 (by decide) s
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl (by decide)
  have eA : cross [2] (v 0)*cross [3,2,1] s=cross [3] (v 1)*cross [2,3,1] s := by
    rw [compose_cross Q Λ _ _ _ (by decide),compose_cross Q Λ _ _ _ (by decide)]
    exact congrArg π near.1
  have eB : cross [1] (v 1)*cross [2,3,1] s=cross [2] (v 2)*cross [1,2,3] s := by
    rw [compose_cross Q Λ _ _ _ (by decide),compose_cross Q Λ _ _ _ (by decide)]
    exact congrArg π near.2
  have eC : cross [2,1] (v 0)*cross [3,2,1] s=cross [3] (v 3)*cross [2,3,1,2] s := by
    rw [compose_cross Q Λ _ _ _ (by decide),compose_cross Q Λ _ _ _ (by decide)]
    exact congrArg π rev.1
  have eD : cross [2,3] (v 2)*cross [1,2,3] s=cross [1] (v 3)*cross [2,3,1,2] s := by
    rw [compose_cross Q Λ _ _ _ (by decide),compose_cross Q Λ _ _ _ (by decide)]
    exact congrArg π rev.2
  apply Subtype.ext
  change (C).subtype (∑ i, jointArms Q Λ t order j i • exitLeg Q Λ t order i)=0
  rw [map_sum,Fin.sum_univ_four]
  fin_cases j
  · change cross [2] (v 0)*cross [3,2,1] s+(-cross [3] (v 1))*cross [2,3,1] s+
      (0:V)*cross [1,2,3] s+0*cross [2,3,1,2] s=0
    simp only [eA,neg_mul,zero_mul,add_zero,add_neg_cancel]
  · change (0:V)*cross [3,2,1] s+cross [1] (v 1)*cross [2,3,1] s+
      (-cross [2] (v 2))*cross [1,2,3] s+0*cross [2,3,1,2] s=0
    simp only [eB,neg_mul,zero_mul,zero_add,add_zero,add_neg_cancel]
  · change cross [2,1] (v 0)*cross [3,2,1] s+0*cross [2,3,1] s+
      0*cross [1,2,3] s+(-cross [3] (v 3))*cross [2,3,1,2] s=0
    simp only [eC,neg_mul,zero_mul,add_zero,add_neg_cancel]
  · change (0:V)*cross [3,2,1] s+0*cross [2,3,1] s+
      cross [2,3] (v 2)*cross [1,2,3] s+(-cross [1] (v 3))*cross [2,3,1,2] s=0
    simp only [eD,neg_mul,zero_mul,zero_add,add_neg_cancel]


private def rightOnKernel (d : T) (x : K) : K := op d • x

include order in
private def jointColumn (g : Fin 4 → K) (i : Fin 4) : K :=
  ∑ j, rightOnKernel Q Λ t (jointArms Q Λ t order j i) (g j)

private theorem read_rightOnKernel (d : T) (x : K) :
    readK Q Λ t (rightOnKernel Q Λ t d x)=readK Q Λ t x*d.1 := rfl

include order in
private theorem read_jointColumn (g : Fin 4 → K) (i : Fin 4) :
    readK Q Λ t (jointColumn Q Λ t order g i)=∑ j, readK Q Λ t (g j)*(jointArms Q Λ t order j i).1 := by
  rw [jointColumn,map_sum]
  simp only [read_rightOnKernel]

private def armValue : Fin 4 → Fin 4 → V :=
  ![![cross [2] (v 0),-cross [3] (v 1),0,0],
    ![0,cross [1] (v 1),-cross [2] (v 2),0],
    ![cross [2,1] (v 0),0,0,-cross [3] (v 3)],
    ![0,0,cross [2,3] (v 2),-cross [1] (v 3)]]

include order in
private theorem jointArms_value (j i : Fin 4) : (jointArms Q Λ t order j i).1=armValue Q Λ j i := by
  fin_cases j <;> fin_cases i <;> rfl

include order in
private theorem read_joint_coefficients (x g : Fin 4 → K) (zA zB zC zD : V)
    (gA : readK Q Λ t (g 0)=zA) (gB : readK Q Λ t (g 1)=zB)
    (gC : readK Q Λ t (g 2)=zC) (gD : readK Q Λ t (g 3)=zD)
    (h₀ : readK Q Λ t (x 0)*p (v 0)=zA*cross [2] (v 0)+zC*cross [2,1] (v 0))
    (h₁ : readK Q Λ t (x 1)*p (v 1)=zB*cross [1] (v 1)-zA*cross [3] (v 1))
    (h₂ : readK Q Λ t (x 2)*p (v 2)=zD*cross [2,3] (v 2)-zB*cross [2] (v 2))
    (h₃ : readK Q Λ t (x 3)*p (v 3)=-(zC*cross [3] (v 3)+zD*cross [1] (v 3)))
    (i : Fin 4) :
    rightOnKernel Q Λ t (exitProj Q Λ t order i) (x i) = jointColumn Q Λ t order g i := by
  let f (i : Fin 4) := readK Q Λ t (x i)*p (v i)
  apply readK_injective Q Λ t
  rw [read_rightOnKernel,read_jointColumn,Fin.sum_univ_four]
  simp only [jointArms_value]
  fin_cases i
  · change f 0=readK Q Λ t (g 0)*cross [2] (v 0)+readK Q Λ t (g 1)*0+
      readK Q Λ t (g 2)*cross [2,1] (v 0)+readK Q Λ t (g 3)*0
    simpa only [gA,gC,mul_zero,add_zero] using h₀
  · change f 1=readK Q Λ t (g 0)*(-cross [3] (v 1))+readK Q Λ t (g 1)*cross [1] (v 1)+
      readK Q Λ t (g 2)*0+readK Q Λ t (g 3)*0
    simp only [gA,gB,mul_neg,mul_zero,add_zero]
    exact h₁.trans ((sub_eq_add_neg _ _).trans (add_comm _ _))
  · change f 2=readK Q Λ t (g 0)*0+readK Q Λ t (g 1)*(-cross [2] (v 2))+
      readK Q Λ t (g 2)*0+readK Q Λ t (g 3)*cross [2,3] (v 2)
    simp only [gB,gD,mul_neg,mul_zero,zero_add,add_zero]
    exact h₂.trans ((sub_eq_add_neg _ _).trans (add_comm _ _))
  · change f 3=readK Q Λ t (g 0)*0+readK Q Λ t (g 1)*0+
      readK Q Λ t (g 2)*(-cross [3] (v 3))+readK Q Λ t (g 3)*(-cross [1] (v 3))
    simp only [gC,gD,mul_neg,mul_zero,zero_add]
    exact h₃.trans ((neg_add_rev _ _).trans (add_comm _ _))

private def cutCoeff (x : Fin 4 → K) (i : Fin 4) : V := readK Q Λ t (x i)*p (v i)

private theorem cutCoeff_supported (x : Fin 4 → K) (i : Fin 4) :
    p t*cutCoeff Q Λ t x i*p (wordProd n₀ (fiveSlotExitWord i) • s)=cutCoeff Q Λ t x i := by
  have top : p t*readK Q Λ t (x i)=readK Q Λ t (x i) :=
    congrArg (fun z : T => z.1) (x i).1.2
  change p t*(readK Q Λ t (x i)*p (v i))*p (wordProd n₀ (fiveSlotExitWord i) • s)=cutCoeff Q Λ t x i
  rw [exitCut i,← mul_assoc (p t),top,mul_assoc,lid]
  rfl

private theorem cutCoeff_marked (x : Fin 4 → K) (i : Fin 4) : cutCoeff Q Λ t x i ∈ J :=
  TwoSidedIdeal.mul_mem_right J _ _ (x i).2

include order in
private theorem cutCoeff_product (x : Fin 4 → K) (i : Fin 4) :
    cutCoeff Q Λ t x i*cross (fiveSlotExitWord i) s=readK Q Λ t (x i)*(exitLeg Q Λ t order i).1 := by
  change (readK Q Λ t (x i)*p (v i))*cross (fiveSlotExitWord i) s=readK Q Λ t (x i)*cross (fiveSlotExitWord i) s
  have h := congrArg Subtype.val (exitProj_fixes_leg Q Λ t order i)
  change p (v i)*cross (fiveSlotExitWord i) s=cross (fiveSlotExitWord i) s at h
  rw [mul_assoc,h]

include order in
private theorem cutCoeff_zero (x : Fin 4 → K)
    (hz : inc (∑ i,BalancedTensor.tmul (x i) (exitLeg Q Λ t order i))=0) :
    ∑ i, cutCoeff Q Λ t x i*cross (fiveSlotExitWord i) s=0 :=
  (Finset.sum_congr rfl (fun i _ => cutCoeff_product Q Λ t order x i)).trans (sum_exit_stack_zero Q Λ t order x hz)

include order in
private theorem marked_joint_representation (hQ : KLRSymm Q) (ht : FiveSlotRightTop t)
    (x : Fin 4 → K)
    (hz : inc (∑ i,BalancedTensor.tmul (x i) (exitLeg Q Λ t order i))=0) :
    ∃ g : Fin 4 → K, ∀ i,
      rightOnKernel Q Λ t (exitProj Q Λ t order i) (x i) = jointColumn Q Λ t order g i := by
  obtain ⟨zA,mA,zB,mB,zC,mC,zD,mD,h₀,h₁,h₂,h₃,cA,cB,cC,cD⟩ :=
    exists_fiveSlotRightTop_markedExitJoints Q Λ hQ t ht
      (cutCoeff Q Λ t x) (cutCoeff_supported Q Λ t x)
      (cutCoeff_marked Q Λ t x) (cutCoeff_zero Q Λ t order x hz)
  let jA := sadj n₀ 2 • v 0
  let jB := sadj n₀ 1 • v 1
  let jD := sadj n₀ 1 • v 3
  have ordA : redWord jA = κ :=
    (by decide : redWord jA = redWord (v 2)).trans order.symm
  have ordB : redWord jB = κ :=
    (by decide : redWord jB = redWord (v 2)).trans order.symm
  have ordD : redWord jD = κ :=
    (by decide : redWord jD = redWord (v 2)).trans order.symm
  let g : Fin 4 → K := ![jointRep Q Λ t jA ordA zA cA mA,
    jointRep Q Λ t jB ordB zB cB mB,
    jointRep Q Λ t jA ordA zC cC mC,
    jointRep Q Λ t jD ordD zD cD mD]
  have gA : readK Q Λ t (g 0)=zA :=
    jointRep_value Q Λ t jA ordA zA cA mA
  have gB : readK Q Λ t (g 1)=zB :=
    jointRep_value Q Λ t jB ordB zB cB mB
  have gC : readK Q Λ t (g 2)=zC :=
    jointRep_value Q Λ t jA ordA zC cC mC
  have gD : readK Q Λ t (g 3)=zD :=
    jointRep_value Q Λ t jD ordD zD cD mD
  exact ⟨g,read_joint_coefficients Q Λ t order x g zA zB zC zD gA gB gC gD h₀ h₁ h₂ h₃⟩

private abbrev SourceTensor := BalancedTensor k k T K C
private abbrev TargetTensor := BalancedTensor k k T P C

private def includeTensor : SourceTensor (k := k) Q Λ t →ₗ[k] TargetTensor (k := k) Q Λ t := inc

include order in
private theorem collect_tensor (hQ : KLRSymm Q) (z : SourceTensor (k := k) Q Λ t) :
    ∃ x : Fin 4 → K, z=∑ i,BalancedTensor.tmul (x i) (exitLeg Q Λ t order i) :=
  BalancedTensor.exists_sum_tmul_of_finite_generators (k := k) («T» := T)
    (M := K) (N := C) (exitLeg Q Λ t order) (exitLeg_generate Q Λ t order hQ) z

include order in
private theorem balance_tensor (x g : Fin 4 → K)
    (coeff : ∀ i, rightOnKernel Q Λ t (exitProj Q Λ t order i) (x i)=jointColumn Q Λ t order g i) :
    (∑ i,BalancedTensor.tmul (x i) (exitLeg Q Λ t order i) : SourceTensor (k := k) Q Λ t)=0 :=
  BalancedTensor.sum_tmul_eq_zero_of_jointRelations (k := k) («T» := T) (M := K) (N := C)
    (exitLeg Q Λ t order) x (exitProj Q Λ t order) g (jointArms Q Λ t order)
    (exitProj_fixes_leg Q Λ t order) coeff (jointArms_annihilate Q Λ t order)

include order in
private theorem tensor_kernel_zero (hQ : KLRSymm Q) (ht : FiveSlotRightTop t)
    (z : SourceTensor (k := k) Q Λ t)
    (hz : includeTensor Q Λ t z=0) : z=0 := by
  obtain ⟨x,rfl⟩ := collect_tensor Q Λ t order hQ z
  obtain ⟨g,coeff⟩ := marked_joint_representation Q Λ t order hQ ht x hz
  exact balance_tensor Q Λ t order x g coeff

/-- Webster's five-slot kernel-column inclusion is injective at every placement
of the last red among the two equal black strands to the right of the first
exchanged red. -/
theorem fiveSlotRightTop_blockKernelColumnInclusion_injective (hQ : KLRSymm Q)
    (ht : FiveSlotRightTop t) : Function.Injective inc := by
  change Function.Injective (includeTensor Q Λ t)
  exact (injective_iff_map_eq_zero (includeTensor Q Λ t)).mpr
    (tensor_kernel_zero Q Λ t (fiveSlotRightTop_redWord t ht) hQ ht)

/-- Webster's kernel-column inclusion (6.21) is injective at the five-slot
right-extreme top with one earlier red and two equal black strands. -/
theorem fiveSlot_blockKernelColumnInclusion_injective (hQ : KLRSymm Q) :
    Function.Injective (blockKernelColumnInclusion Q Λ (v 2) 1 2 s) :=
  fiveSlotRightTop_blockKernelColumnInclusion_injective Q Λ (v 2) hQ (Or.inl rfl)

end Categorification.Stendhal.BraidedStendhalAlgebra
