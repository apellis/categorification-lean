/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoBlackPivotObstruction
import Categorification.WeightedKLR.RedStrands.FixedTopFourExitJoints
import Categorification.WeightedKLR.RedStrands.FiniteExitAffineLift
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationSpan
import Categorification.KLR.InductionFree
import Categorification.TypeA.WeakOrder

/-!
# Marked exit joints at the three five-slot right tops

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and the cut after (6.21).
In the five-slot interval with one earlier red and two equal black strands,
all four supported marked exit coefficients come from marked neighboring
joints at the extreme, mixed, and full fixed tops. The joint correction is carried out
in the globally violated quotient and preserves each coefficient.
-/
open scoped BigOperators
namespace Categorification.TypeA
open Equiv

def fiveSlotExitWord : Fin 4 → List ℕ
  | 0 => [3,2,1]
  | 1 => [2,3,1]
  | 2 => [1,2,3]
  | _ => [2,3,1,2]

/-- The four interval-supported exits cover a crossing of the last red pair
in ambient size five, with the first position left available for a spectator. -/
theorem exists_fiveSlotExit_below :
    ∀ w : Perm (Fin 5), w 4 < w 1 →
      ∃ j : Fin 4, invSet 5 (wordProd 5 (fiveSlotExitWord j)) ⊆ invSet 5 w := by
  decide +kernel



/-- Each of the four five-slot exit words is reduced. -/
theorem fiveSlotExitWord_reduced (i : Fin 4) : IsReduced 5 (fiveSlotExitWord i) := by
  fin_cases i <;> constructor
  all_goals first | (simp [fiveSlotExitWord,ValidWord]; done) |
    (rw [length_eq_invCount]; decide +kernel)

theorem exists_fiveSlotExit_suffix {n : ℕ} (hn : n=5) (w : Perm (Fin n))
    (h : w ⟨4,by omega⟩<w ⟨1,by omega⟩) :
    ∃ i : Fin 4, IsReduced n (canWord n (w*(wordProd n (fiveSlotExitWord i))⁻¹)++fiveSlotExitWord i) ∧
      wordProd n (canWord n (w*(wordProd n (fiveSlotExitWord i))⁻¹)++fiveSlotExitWord i)=w := by
  subst n
  obtain ⟨i,hi⟩ := exists_fiveSlotExit_below w h
  let u := wordProd 5 (fiveSlotExitWord i)
  have prod : wordProd 5 (canWord 5 (w*u⁻¹)++fiveSlotExitWord i)=w := by
    rw [wordProd_append,wordProd_canWord]
    change w*u⁻¹*u=w
    rw [inv_mul_cancel_right]
  refine ⟨i,⟨validWord_append.2 ⟨validWord_canWord _ _,(fiveSlotExitWord_reduced i).1⟩,?_⟩,prod⟩
  rw [List.length_append,length_canWord,(fiveSlotExitWord_reduced i).2,prod]
  exact length_add_of_invSet_subset hi

end Categorification.TypeA

namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial KLR

variable {I k : Type*} [DecidableEq I] [CommRing k]
    {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
local notation "R" => KLRAlgebra k Q ν
local notation "m" => Multiset.card ν

/-- At ambient size five, the four consecutive-red exit words generate the column
under the endpoint crossing hypothesis. -/
theorem exists_fiveSlotExitColumn_coefficients (hQ : KLRSymm Q) (hm : m=5)
    (s t : Seq ν) (cross : ∀ w : Perm (Fin m), w • s=t →
      w ⟨4,by omega⟩<w ⟨1,by omega⟩) (z : R) :
    ∃ c : Fin 4 → R, e t*z*e s=∑ i,c i*(ψw (fiveSlotExitWord i)*e s) := by
  classical
  let exit (w : Perm (Fin m)) (hw : w • s=t) := (exists_fiveSlotExit_suffix hm w (cross w hw)).choose
  let ρ (w : Perm (Fin m)) := if hw : w • s=t then
    canWord m (w*(wordProd m (fiveSlotExitWord (exit w hw)))⁻¹)++fiveSlotExitWord (exit w hw)
    else canWord m w
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w)=w := by
    intro w
    dsimp only [ρ]
    split_ifs with hw
    · exact (exists_fiveSlotExit_suffix hm w (cross w hw)).choose_spec
    · exact ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩
  let B := lbasis (k := k) («μ» := ν) hQ ρ hρ
  induction B.mem_span z using Submodule.span_induction with
  | zero => exact ⟨fun _ => 0,by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨c,hc⟩ := hz
    obtain ⟨d,hd⟩ := hw
    refine ⟨fun i => c i+d i,?_⟩
    simp only [mul_add,add_mul,hc,hd,Finset.sum_add_distrib]
  | smul r z _ hz =>
    obtain ⟨c,hc⟩ := hz
    refine ⟨fun i => r • c i,?_⟩
    simp only [mul_smul_comm,smul_mul_assoc,hc,Finset.smul_sum]
  | mem _ hz =>
    obtain ⟨⟨v,w,d⟩,rfl⟩ := hz
    rw [show B (v,w,d)=_ from lbasis_apply ..,mul_assoc,mul_assoc _ (e v),e_mul_e]
    by_cases hv : v=s
    · subst v
      rw [ite_eq_left rfl]
      by_cases hw : w • s=t
      · let i := exit w hw
        refine ⟨fun j => if j=i then e t*pol (monomial d 1)*ψw
          (canWord m (w*(wordProd m (fiveSlotExitWord i))⁻¹)) else 0,?_⟩
        rw [Finset.sum_eq_single i]
        · simp only [ρ,dite_eq_left hw,ψw_append,mul_assoc,ite_true,i]
        · intro j _ hj
          simp only [ite_eq_right hj,zero_mul]
        · exact fun hi => (hi (Finset.mem_univ i)).elim
      · have cut := e_mul_pol_ψw_e (Q := Q) (monomial d (1:k)) (ρ w) s
        rw [(hρ w).2] at cut
        rw [← cut,← mul_assoc,e_mul_e,ite_eq_right (Ne.symm hw),zero_mul]
        exact ⟨fun _ => 0,by simp⟩
    · rw [ite_eq_right hv,mul_zero,mul_zero]
      exact ⟨fun _ => 0,by simp⟩

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "A" => BraidedStendhalAlgebra k Q Λ ν₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "raw" => ofKLR k Q Λ ν₀
local notation "mk" => violMk k Q Λ ν₀
local notation "p" => fun v : Seq μ₀ => raw (e v)
local notation "top" => fixedTopFourExitCut 2
local notation "bottom" => fixedTopFourExitBottom
local notation "q" => fun i : Fin 4 => wordProd n₀ (fiveSlotExitWord i) • bottom
local notation "leg" => fun i : Fin 4 => raw (ψw (fiveSlotExitWord i)*e bottom)

/-- Four exits generate every upper column in the exchanged red order with one
earlier red spectator and two equal black strands. -/
theorem fiveSlotExit_generate (hQ : KLRSymm Q) (v : Seq μ₀)
    (order : redWord v=redWord top) (z : A) :
    ∃ c : Fin 4 → A, p v*z*p bottom=∑ i, c i*leg i := by
  obtain ⟨x,rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) z
  have cross (w : Perm (Fin n₀)) (hw : w • bottom=v) :
      w ⟨4,by decide⟩<w ⟨1,by decide⟩ := by
    have hsub : [1,2].Sublist (redWord (w • bottom)) := by
      rw [hw,order]
      decide
    have lt : (1 : Fin 5)<4 := by decide
    exact (mem_invSet_pair.mp (mem_invSet_of_sublist_redWord hsub lt rfl rfl)).2
  obtain ⟨c,hc⟩ := exists_fiveSlotExitColumn_coefficients (stendhalQ_symm Q Λ hQ)
    (by decide) bottom v cross x
  exact ⟨fun i => raw (c i), by simpa only [map_mul,map_sum] using congrArg raw hc⟩

/-- The four supported coefficients of a five-slot relation lift through the
global violation while retaining the actual relation and all quotient projections. -/
theorem exists_fiveSlotExitRelation_affine_lift_at (hQ : KLRSymm Q)
    (upper : Seq μ₀) (order : redWord upper=redWord top) (x : Fin 4 → V)
    (support : ∀ i, mk (p upper)*x i*mk (p (q i))=x i)
    (hzero : ∑ i, x i*mk (leg i)=0) :
    ∃ c : Fin 4 → A, (∀ i, p upper*c i*p (q i)=c i) ∧
      (∀ i, mk (c i)=x i) ∧ (∑ i, c i*leg i)=0 := by
  obtain ⟨c,hc,he⟩ := exists_finiteExitRelation_affine_lift Q Λ bottom upper
    fiveSlotExitWord hQ (fun v hv => fiveSlotExit_generate Q Λ hQ v (hv.trans order)) x support hzero
  refine ⟨fun i => p upper*c i*p (q i),fun i => ?_,hc,he⟩
  have idem (v : Seq μ₀) : p v*p v=p v := by rw [← map_mul,e_mul_self]
  calc
    _ = (p upper*p upper)*c i*(p (q i)*p (q i)) := by simp only [mul_assoc]
    _ = _ := by rw [idem,idem]


/-- The four supported coefficients of a five-slot relation lift through the
global violation while retaining the actual relation and all quotient projections. -/
theorem exists_fiveSlotExitRelation_affine_lift (hQ : KLRSymm Q) (x : Fin 4 → V)
    (support : ∀ i, mk (p top)*x i*mk (p (q i))=x i)
    (hzero : ∑ i, x i*mk (leg i)=0) :
    ∃ c : Fin 4 → A, (∀ i, p top*c i*p (q i)=c i) ∧
      (∀ i, mk (c i)=x i) ∧ (∑ i, c i*leg i)=0 := by
  exact exists_fiveSlotExitRelation_affine_lift_at Q Λ hQ top rfl x support hzero

local notation "π" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 top) (redWord top)
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "v₃" => fixedTopFourExitCut 3
local notation "jA" => sadj n₀ 2 • v₀
local notation "jB" => sadj n₀ 1 • v₁
local notation "jD" => sadj n₀ 1 • v₃
local notation "C" => fun (w : List ℕ) (v : Seq μ₀) => π (ψw w*e v)

private theorem compose_viol_leg (l r : List ℕ) (v u : Seq μ₀)
    (hu : wordProd n₀ r • v=u) :
    C l u*C r v=C (l++r) v := by
  change π (ψw l*e u)*π (ψw r*e v)=π (ψw (l++r)*e v)
  rw [← map_mul,ψw_append,← hu]
  have cut : (e (wordProd n₀ r • v) : KLRAlgebra k (stendhalQ Q Λ) μ₀)*
      (ψw r*e v)=ψw r*e v := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  rw [mul_assoc,cut,mul_assoc]

/-- The extreme, mixed and full five-slot tops have the same red order. -/
theorem fiveSlotRightTop_redWord (upper : Seq μ₀) (ht : FiveSlotRightTop upper) :
    redWord upper=redWord top := by
  rcases ht with rfl|rfl|rfl <;> decide

/-- Moving the last red among its two black neighbors preserves the retained
cut counts, which ignore the cut between the two exchanged red strands. -/
theorem fiveSlotRightTop_blockRoot (upper : Seq μ₀) (ht : FiveSlotRightTop upper) :
    adjacentBlockRoot 1 2 upper=adjacentBlockRoot 1 2 top := by
  ext r i
  rcases ht with rfl|rfl|rfl <;> fin_cases r <;> cases i <;> decide

local notation "Jᵤ" => fun v : Seq μ₀ => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 v) (redWord v)

/-- At any of the three five-slot right tops, a relation whose four
coefficients lie in the higher ideal comes from four marked neighboring
joints. The correction preserves their individual upper and lower cuts. -/
theorem exists_fiveSlotRightTop_markedExitJoints (hQ : KLRSymm Q)
    (upper : Seq μ₀) (ht : FiveSlotRightTop upper)
    (x : Fin 4 → V) (support : ∀ i, mk (p upper)*x i*mk (p (q i))=x i)
    (mark : ∀ i, x i ∈ (Jᵤ upper)) (hzero : ∑ i, x i*mk (leg i)=0) :
    ∃ zA ∈ (Jᵤ upper), ∃ zB ∈ (Jᵤ upper), ∃ zC ∈ (Jᵤ upper), ∃ zD ∈ (Jᵤ upper),
      x 0=zA*C [2] v₀+zC*C [2,1] v₀ ∧
      x 1=zB*C [1] v₁-zA*C [3] v₁ ∧
      x 2=zD*C [2,3] top-zB*C [2] top ∧
      x 3=-(zC*C [3] v₃+zD*C [1] v₃) ∧
      π (e upper)*zA*π (e jA)=zA ∧ π (e upper)*zB*π (e jB)=zB ∧
      π (e upper)*zC*π (e jA)=zC ∧ π (e upper)*zD*π (e jD)=zD := by
  have order := fiveSlotRightTop_redWord upper ht
  obtain ⟨y,yCut,yEval,yZero⟩ := exists_fiveSlotExitRelation_affine_lift_at Q Λ hQ upper order x support hzero
  have exits (i : Fin 4) : q i=fixedTopFourExitCut i := by fin_cases i <;> decide
  have yCut' (i : Fin 4) : p upper*y i*p (fixedTopFourExitCut i)=y i := by
    rw [← exits i]
    exact yCut i
  have yRel : y 0*raw (ψw [3,2,1]*e bottom)+y 1*raw (ψw [2,3,1]*e bottom)+
      y 2*raw (ψw [1,2,3]*e bottom)+y 3*raw (ψw [2,3,1,2]*e bottom)=0 := by
    simpa only [Fin.sum_univ_four,fiveSlotExitWord,add_assoc] using yZero
  obtain ⟨u,v,w,uCut,vCut,wCut,h₀,h₁,h₂,h₃⟩ :=
    exists_fiveSlotRightTop_fourExitJointPresentation Q Λ hQ upper ht (y 0) (y 1) (y 2) (y 3)
      (yCut' 0) (yCut' 1) (yCut' 2) (yCut' 3) yRel
  let xA := mk u
  let xB := mk v
  let xD := mk w
  have hA : π (e upper)*xA*π (e jA)=xA := by
    change mk (p upper)*mk u*mk (p jA)=mk u
    simpa only [map_mul] using congrArg mk uCut
  have hB : π (e upper)*xB*π (e jB)=xB := by
    change mk (p upper)*mk v*mk (p jB)=mk v
    simpa only [map_mul] using congrArg mk vCut
  have hD : π (e upper)*xD*π (e jD)=xD := by
    change mk (p upper)*mk w*mk (p jD)=mk w
    simpa only [map_mul] using congrArg mk wCut
  have hx₀ : x 0=xA*C [2] v₀ := by
    rw [← yEval 0]
    exact (congrArg mk h₀).trans (map_mul mk _ _)
  have hx₁ : x 1=xB*C [1] v₁-xA*C [3] v₁ := by
    rw [← yEval 1]
    simpa only [map_sub,map_mul,AlgHom.comp_apply] using congrArg mk h₁
  have hx₂ : x 2=xD*C [2,3] top-xB*C [2] top := by
    rw [← yEval 2]
    simpa only [map_sub,map_mul,AlgHom.comp_apply] using congrArg mk h₂
  have hx₃ : x 3=-(xD*C [1] v₃) := by
    rw [← yEval 3]
    simpa only [map_mul,map_neg,AlgHom.comp_apply] using congrArg mk h₃
  have bCut : jB=sadj n₀ 2 • top := by decide
  have dCut : jD=sadj n₀ 2 • top := by decide
  have black (i : Fin n₀) (hi : ((top).lbl i).isLeft) :
      i=⟨3,by decide⟩ ∨ i=⟨4,by decide⟩ := by
    fin_cases i <;> first | decide | contradiction
  obtain ⟨z,zCut,zb,zd⟩ := exists_equalBlack_rightPair_markedCycle_at_three_tops Q Λ hQ
    top upper 2 (by decide) 1 2 () ht [0] (order.trans (by decide)) rfl rfl rfl black xB xD
    (bCut ▸ hB) (dCut ▸ hD) (hx₂ ▸ mark 2)
  have zLeft : π (e upper)*z=z := by
    have h := congrArg (fun r => π (e upper)*r) zCut
    change π (e upper)*(π (e upper)*z*π (e (sadj n₀ 3 • (sadj n₀ 2 • top))))=π (e upper)*z at h
    rw [← mul_assoc (π (e upper)),← mul_assoc (π (e upper)),← map_mul,e_mul_self,zCut] at h
    exact h.symm
  have cycle := twoBlackExitCycleWords (Q₀ := stendhalQ Q Λ) 1 (by decide) bottom
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl
  change (ψw [2,1,2]*e (q 0) : KLRAlgebra k (stendhalQ Q Λ) μ₀)=ψw [1,2,1]*e (q 0) ∧
    (ψw [2,1,3]*e (q 1) : KLRAlgebra k (stendhalQ Q Λ) μ₀)=ψw [2,3,1]*e (q 1) ∧
    (ψw [2,3,2]*e (q 2) : KLRAlgebra k (stendhalQ Q Λ) μ₀)=ψw [3,2,3]*e (q 2) ∧
    (ψw [1,3]*e (q 3) : KLRAlgebra k (stendhalQ Q Λ) μ₀)=ψw [3,1]*e (q 3) at cycle
  rw [exits 0,exits 1,exits 2,exits 3] at cycle
  have cyc₀ : C [2,1] jA*C [2] v₀=C [1] jA*C [2,1] v₀ := by
    rw [compose_viol_leg Q Λ _ _ _ _ (by decide),compose_viol_leg Q Λ _ _ _ _ (by decide)]
    exact congrArg π cycle.1
  have cyc₁ : C [2,1] jA*C [3] v₁=C [2,3] jB*C [1] v₁ := by
    rw [compose_viol_leg Q Λ _ _ _ _ (by decide),compose_viol_leg Q Λ _ _ _ _ (by decide)]
    exact congrArg π cycle.2.1
  have cyc₂ : C [2,3] jB*C [2] top=C [3] jD*C [2,3] top := by
    rw [compose_viol_leg Q Λ _ _ _ _ (by decide),compose_viol_leg Q Λ _ _ _ _ (by decide)]
    exact congrArg π cycle.2.2.1
  have cyc₃ : C [1] jA*C [3] v₃=C [3] jD*C [1] v₃ := by
    rw [compose_viol_leg Q Λ _ _ _ _ (by decide),compose_viol_leg Q Λ _ _ _ _ (by decide)]
    exact congrArg π cycle.2.2.2
  have cut (l : List ℕ) (v : Seq μ₀) : C l v*π (e v)=C l v := by
    simp only [← map_mul,mul_assoc,e_mul_self]
  have hmark₁ : xB*C [1] v₁-xA*C [3] v₁ ∈ (Jᵤ upper) := hx₁ ▸ mark 1
  have hmark₂ : xD*C [2,3] top-xB*C [2] top ∈ (Jᵤ upper) := hx₂ ▸ mark 2
  have hmark₃ : (0 : V)*C [3] v₃ + xD*C [1] v₃ ∈ (Jᵤ upper) := by
    simpa only [zero_mul,zero_add,hx₃,neg_neg] using TwoSidedIdeal.neg_mem (Jᵤ upper) (mark 3)
  have jAhigher : adjacentBlockRoot 1 2 upper < adjacentBlockRoot 1 2 jA := by
    rw [fiveSlotRightTop_blockRoot upper ht]
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro le
      exact (by decide : ¬ adjacentBlockRoot 1 2 jA 1 () ≤ adjacentBlockRoot 1 2 top 1 ())
        (le 1 ())
  have eMark : π (e jA) ∈ (Jᵤ upper) :=
    TwoSidedIdeal.subset_span ⟨jA,by rw [order]; decide,jAhigher,rfl⟩
  have reflect (z : V) (hz : π (e upper)*z*π (e jA)=z) (_ : z*C [3] v₁ ∈ (Jᵤ upper)) :
      z ∈ (Jᵤ upper) := hz ▸ TwoSidedIdeal.mul_mem_left (Jᵤ upper) _ _ eMark
  have s₁ : v₁=v₃ := by decide
  obtain ⟨r,rTop,mA,mB,mC,mD,r₀,r₁,r₂,r₃⟩ := exists_marked_fourExitCycle (Jᵤ upper)
    (π (e upper)) (π (e jA)) (π (e jA))
    (C [2] v₀) (C [3] v₁) (C [1] v₁) (C [2] top)
    (C [2,1] v₀) (C [3] v₃) (C [2,3] top) (C [1] v₃)
    (C [2,1] jA) (C [2,3] jB) (C [1] jA) (C [3] jD)
    cyc₀ cyc₁ cyc₂ cyc₃ (cut _ _) (cut _ _) reflect (s₁ ▸ reflect)
    xA xB 0 xD hA (by rw [mul_zero,zero_mul]) hmark₁ hmark₂ hmark₃
    (fun _ => ⟨z,zLeft,bCut.symm ▸ zb,dCut.symm ▸ zd⟩)
  have tailCut (l : List ℕ) (v : Seq μ₀) : π (e upper)*(r*C l v)*π (e v)=r*C l v := by
    rw [← mul_assoc (π (e upper)),rTop,mul_assoc,cut]
  refine ⟨_,mA,_,mB,_,mC,_,mD,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [r₀,zero_mul,add_zero,hx₀]
  · exact hx₁.trans r₁.symm
  · exact hx₂.trans r₂.symm
  · rw [r₃,zero_mul,zero_add,hx₃]
  · simp only [mul_sub,sub_mul,hA,tailCut]
  · simp only [mul_sub,sub_mul,hB,tailCut]
  · simpa only [zero_add] using tailCut [1] jA
  · simp only [mul_sub,sub_mul,hD,tailCut]

/-- At the fixed five-slot right extreme, every marked four-exit relation
comes from marked neighboring joints. The two remaining joints lie strictly
above the fixed top at the merged red cut. -/
theorem exists_fiveSlot_markedExitJoints (hQ : KLRSymm Q)
    (x : Fin 4 → V) (support : ∀ i, mk (p top)*x i*mk (p (q i))=x i)
    (mark : ∀ i, x i ∈ J) (hzero : ∑ i, x i*mk (leg i)=0) :
    ∃ zA ∈ J, ∃ zB ∈ J, ∃ zC ∈ J, ∃ zD ∈ J,
      x 0=zA*C [2] v₀+zC*C [2,1] v₀ ∧
      x 1=zB*C [1] v₁-zA*C [3] v₁ ∧
      x 2=zD*C [2,3] top-zB*C [2] top ∧
      x 3=-(zC*C [3] v₃+zD*C [1] v₃) ∧
      π (e top)*zA*π (e jA)=zA ∧ π (e top)*zB*π (e jB)=zB ∧
      π (e top)*zC*π (e jA)=zC ∧ π (e top)*zD*π (e jD)=zD := by
  exact exists_fiveSlotRightTop_markedExitJoints Q Λ hQ top (Or.inl rfl) x support mark hzero

end Categorification.Stendhal.BraidedStendhalAlgebra

