/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGrading
import Categorification.KLR.CyclotomicTerminal
import Categorification.KLR.CyclotomicSplit
import Categorification.Algebra.IdempotentEquiv

/-!
# The two-strand terminal projective

The weight-two terminal cyclotomic right ideal cut out by the nilHecke
divided-power projector is simple. This is the single-colour weight-two
case of Webster, arXiv:1309.3796v2, Proposition 7.2.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra MulOpposite

variable {k : Type*} [Field k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "ν" => Multiset.replicate 2 ()
local notation "powers" => fun _ : Unit => (Polynomial.X ^ 2 : Polynomial k)
local notation "π" => CycKLR.mk k Q powers ν
local notation "R" => CycKLR k Q powers ν
local notation "p" => π (x (⟨0, by decide⟩ : Fin (Multiset.card ν)))
local notation "q" => π (x (⟨1, by decide⟩ : Fin (Multiset.card ν)))
local notation "d" => π (ψ 0)

/-- The divided-power projector (x₀ ψ₀) in the weight-two terminal algebra. -/
def twoBlackTerminalIdem : R := p*d

/-- The affine lift of the terminal projector acts as the standard two-strand
nilHecke divided-power idempotent. -/
theorem toNH_twoBlackTerminalIdem_lift :
    toNH (i := ()) (fun j (_ : j ∈ ν) => Subsingleton.elim j ()) Q
      (x (⟨0, by decide⟩ : Fin (Multiset.card ν)) * ψ 0) =
      NilHecke.idemNH k 2 := by
  have hx : (NilHecke.xDelta (m := 2) 2 : MvPolynomial (Fin 2) k) =
      MvPolynomial.X 0 := by
    simp [NilHecke.xDelta, Fin.prod_univ_succ]
  rw [map_mul, toNH_x, toNH_ψ]
  change NilHecke.mulX k 2 0 * NilHecke.dd k 2 0 = _
  rw [NilHecke.idemNH, hx, show NilHecke.w0Word 2 = [0] from rfl,
    NilHecke.ddw_cons, NilHecke.ddw_nil, mul_one]
  rfl

local notation "E" => twoBlackTerminalIdem Q

private theorem terminalIdem_right_products :
    E*p=p ∧ p*E=0 ∧ E*d=0 ∧ E*E=E := by
  obtain ⟨pp,dd,_,rel⟩ := twoBlack_terminal_relations Q
  have pE : p*E=0 := by
    change p*(p*d)=0
    rw [← mul_assoc,pp,zero_mul]
  have ed : E*d=0 := by
    change (p*d)*d=0
    rw [mul_assoc,dd,mul_zero]
  have dp : d*p=1-E := eq_sub_of_add_eq rel
  have ep : E*p=p := by
    change (p*d)*p=p
    rw [mul_assoc,dp,mul_sub,mul_one,pE,sub_zero]
  exact ⟨ep,pE,ed,by change E*(p*d)=E; rw [← mul_assoc,ep]; rfl⟩

/-- The weight-two divided-power projector is idempotent. -/
theorem twoBlackTerminalIdem_idempotent : IsIdempotentElem E :=
  (terminalIdem_right_products Q).2.2.2

private theorem terminal_right_row (z : rIdeal E) :
    ∃ a b : k, a • E + b • p = z.val := by
  obtain ⟨pp,_,pq0,_⟩ := twoBlack_terminal_relations Q
  obtain ⟨ep,_,ed,_⟩ := terminalIdem_right_products Q
  have qNeg : q = -p := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm,pq0])
  let row : Submodule k R := Submodule.span k ({E,p} : Set R)
  have eMem : E ∈ row := Submodule.subset_span (Set.mem_insert _ _)
  have pMem : p ∈ row := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let Stable (y : R) : Prop := ∀ w ∈ row, w*y ∈ row
  have basis (y : R) (eMul : E*y ∈ row) (pMul : p*y ∈ row) : Stable y := by
    intro w hw
    obtain ⟨a,b,hw⟩ := Submodule.mem_span_pair.mp hw
    rw [← hw,add_mul,smul_mul_assoc,smul_mul_assoc]
    exact row.add_mem (row.smul_mem _ eMul) (row.smul_mem _ pMul)
  have stableP : Stable p := basis p (ep ▸ pMem) (pp ▸ row.zero_mem)
  have stableD : Stable d := basis d (ed ▸ row.zero_mem) eMem
  have all : ∀ y, Stable y := by
    intro y
    obtain ⟨y,rfl⟩ := CycKLR.mk_surjective y
    refine klr_induction («p» := fun r => Stable (π r)) ?_ ?_ ?_ ?_ ?_ ?_ y
    · intro u v hu hv w hw
      rw [map_add,mul_add]
      exact row.add_mem (hu w hw) (hv w hw)
    · intro u v hu hv w hw
      rw [map_mul,← mul_assoc]
      exact hv (w*π u) (hu w hw)
    · intro c w hw
      rw [AlgHom.commutes,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]
      exact row.smul_mem c hw
    · intro s w hw
      rw [e_eq_one_of_forall (fun j _ => Subsingleton.elim j ()) Q, map_one, mul_one]
      exact hw
    · intro a
      fin_cases a
      · exact stableP
      · change Stable q
        rw [qNeg]
        intro w hw
        rw [mul_neg]
        exact row.neg_mem (stableP w hw)
    · intro j
      cases j with
      | zero => exact stableD
      | succ j =>
        intro w hw
        rw [ψ_eq_zero _ (by simp), map_zero, mul_zero]
        exact row.zero_mem
  have hm := all z.val E eMem
  rw [mem_rIdeal.mp z.property] at hm
  exact Submodule.mem_span_pair.mp hm

/-- The two-black terminal projector is nonzero. -/
theorem twoBlackTerminalIdem_ne_zero : E ≠ 0 := by
  obtain ⟨_,_,_,rel⟩ := twoBlack_terminal_relations Q
  obtain ⟨ep,_,_,_⟩ := terminalIdem_right_products Q
  let _ : Nontrivial R :=
    (terminalCoinvAct («ν» := ν) (i := ()) (fun j _ => Subsingleton.elim j ()) Q).toRingHom.domain_nontrivial
  intro ez
  rw [ez,zero_mul] at ep
  rw [← ep,mul_zero,zero_mul,zero_add] at rel
  exact zero_ne_one rel

/-- Webster, arXiv:1309.3796v2, Proposition 7.2 for the terminal two-strand
one-colour block. The right ideal of the divided-power projector is simple. -/
theorem twoBlackTerminalProjective_simple :
    CategoryTheory.Simple (ModuleCat.of Rᵐᵒᵖ (rIdeal E)) := by
  obtain ⟨_,pe,ed,ee⟩ := terminalIdem_right_products Q
  have neE := twoBlackTerminalIdem_ne_zero Q
  apply simple_iff_isSimpleModule.mpr
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  let generator : rIdeal E := ⟨E,ee⟩
  refine ⟨⟨⟨generator,0,fun h => neE (congrArg Subtype.val h)⟩⟩,?_⟩
  intro r hr z
  obtain ⟨a,b,hu⟩ := terminal_right_row Q r
  have undo (c : k) (hc : c ≠ 0) (u : R) (hcE : r.val*u = c • E) :
      r.val*(u*algebraMap k R c⁻¹)=E := by
    rw [← mul_assoc,hcE,smul_mul_assoc,Algebra.algebraMap_eq_smul_one,
      mul_smul_comm,mul_one,smul_smul,mul_inv_cancel₀ hc,one_smul]
  have target : ∃ u : R, r.val*u=E := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        apply hr
        apply Subtype.ext
        change r.val = 0
        simpa only [ha,hb,zero_smul,zero_add] using hu.symm
      refine ⟨d*algebraMap k R b⁻¹,undo b hb d ?_⟩
      rw [← hu,add_mul,smul_mul_assoc,smul_mul_assoc,ed,smul_zero,zero_add]
      rfl
    · refine ⟨E*algebraMap k R a⁻¹,undo a ha E ?_⟩
      rw [← hu,add_mul,smul_mul_assoc,smul_mul_assoc,ee,pe,smul_zero,add_zero]
  obtain ⟨u,hu⟩ := target
  refine ⟨op (u*z.val),?_⟩
  apply Subtype.ext
  change r.val*(u*z.val)=z.val
  rw [← mul_assoc,hu]
  exact z.property

/-- The divided-power terminal corner is spanned by its idempotent.
This is the scalar corner for each outer factor in the label-two
calculation preceding Webster v2, §8.2, Proposition 8.4. -/
theorem twoBlackTerminal_corner_span (z : (twoBlackTerminalIdem_idempotent Q).Corner) :
    ∃ a : k, a • E = z.val := by
  obtain ⟨left,right⟩ := (Subsemigroup.mem_corner_iff (twoBlackTerminalIdem_idempotent Q)).mp z.property
  obtain ⟨a,b,h⟩ := terminal_right_row Q (⟨z.val,mem_rIdeal.mpr left⟩ : rIdeal E)
  obtain ⟨_,pe,_,ee⟩ := terminalIdem_right_products Q
  refine ⟨a,?_⟩
  have h' := congrArg (· * E) h
  change (a • E + b • p) * E = z.val * E at h'
  rwa [add_mul,smul_mul_assoc,smul_mul_assoc,ee,pe,smul_zero,add_zero,right] at h'


/-- Reversing the order of the first dot and crossing gives the complementary
weight-two terminal projector. -/
theorem twoBlackTerminal_reflected_projector : d * p = 1 - E := by
  obtain ⟨_,_,_,rel⟩ := twoBlack_terminal_relations Q
  exact eq_sub_of_add_eq rel

/-- The dot and crossing exhibit the terminal and reflected projectors as
equivalent idempotents. -/
theorem twoBlackTerminal_reflected_equivPair : IsEquivPair p d E (1 - E) := by
  obtain ⟨ep, _, ed, _⟩ := terminalIdem_right_products Q
  refine IsEquivPair.of_mul_left rfl (twoBlackTerminal_reflected_projector Q) ep ?_
  change d * (p * d) = d
  rw [← mul_assoc, twoBlackTerminal_reflected_projector Q, sub_mul, one_mul, ed, sub_zero]

/-- The off-diagonal corner from the complementary projector to the terminal
projector is the nonzero line spanned by the first dot. -/
theorem twoBlackTerminal_reflected_corner_span :
    p ≠ 0 ∧ E * p = p ∧ p * (1 - E) = p ∧
      ∀ z : R, E * z = z → z * (1 - E) = z → ∃ a : k, a • p = z := by
  have h := twoBlackTerminal_reflected_equivPair Q
  have pn : p ≠ 0 := by
    intro h
    apply twoBlackTerminalIdem_ne_zero Q
    change p * d = 0
    rw [h, zero_mul]
  have off : E * (1 - E) = 0 := by rw [mul_sub, mul_one, h.idem_left.eq, sub_self]
  refine ⟨pn, h.left_mul, h.mul_right, ?_⟩
  intro z hl hr
  obtain ⟨a,b,hspan⟩ := terminal_right_row Q (⟨z,mem_rIdeal.mpr hl⟩ : rIdeal E)
  refine ⟨b,?_⟩
  have h' := congrArg (· * (1 - E)) hspan
  change (a • E + b • p) * (1 - E) = z * (1 - E) at h'
  rwa [add_mul, smul_mul_assoc, smul_mul_assoc, off, h.mul_right, smul_zero, zero_add, hr] at h'


/-- The complementary cut is a line in the internal degree of the black dot. -/
theorem twoBlackTerminal_reflected_corner_mem_grade_iff (G : GradingDatum Q)
    {z : R} (hl : E * z = z) (hr : z * (1 - E) = z) (n : ℤ) :
    z ∈ grade G (fun _ => 2) ν n ↔ n = G.degX () ∨ z = 0 := by
  let D := grade G (fun _ => 2) ν
  let s : Seq ν := ⟨fun _ => (), by decide⟩
  have hs : (e s : KLRAlgebra k Q ν) = 1 :=
    e_eq_one_of_forall (fun j _ => Subsingleton.elim j ()) Q s
  have hx : p ∈ D (G.degX ()) := by
    apply Submodule.mem_map_of_mem
    simpa only [hs, mul_one, s] using G.x_mul_e_mem_grade ⟨0, by decide⟩ s
  obtain ⟨_, _, _, hspan⟩ := twoBlackTerminal_reflected_corner_span Q
  obtain ⟨a, rfl⟩ := hspan z hl hr
  have hzero : a • p ∈ D (G.degX ()) := Submodule.smul_mem _ _ hx
  constructor
  · intro hn
    by_cases he : n = G.degX ()
    · exact Or.inl he
    · let : GradedAlgebra D := gradedAlgebra G (fun _ => 2) ν
      exact Or.inr ((DirectSum.decompose_of_mem_same D hzero).symm.trans
        (DirectSum.decompose_of_mem_ne D hn he))
  · rintro (rfl | hz)
    · exact hzero
    · rw [hz]
      exact (D n).zero_mem

end Categorification.KLR.CycKLR
