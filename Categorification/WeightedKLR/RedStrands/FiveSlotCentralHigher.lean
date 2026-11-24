/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralCancellation
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.WeightedKLR.RedStrands.FiveSlotSpectatorWeight
import Categorification.WeightedKLR.RedStrands.OrdinaryRetainedCrossing

/-!
# The principal higher ideal at the central five-slot top

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
Every marked coefficient at the central top factors through the left extreme
by the same two red/black crossings. Cancellation on one supported bottom
column suffices to lift all four marked joint coefficients.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv MvPolynomial
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "t" => fixedTopFourExitCut 1
local notation "v₂" => fixedTopFourExitCut 2
local notation "bot" => fixedTopFourExitBottom
local notation "jA" => sadj N 2 • v₀
local notation "jB" => sadj N 1 • t
local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) (redWord t)
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "E" => fun w : Seq μ₀ => F (e w)
local notation "L" => fun (w : List ℕ) (v : Seq μ₀) => F (ψw w*e v)
local notation "C" => L [3,2] v₀
local notation "exitWord" => fun i : Fin 4 => L (fiveSlotExitWord i) bot
local notation "load" => fun i : Fin 4 => wordProd N (fiveSlotExitWord i) • bot

private theorem idem (w : Seq μ₀) : E w*E w=E w := by rw [← map_mul,e_mul_self]

private theorem split : F (ψ 3*e jA)*F (ψ 2*e v₀)=C := by
  have fixed : (e jA)*(ψ 2*e v₀ : KLRAlgebra k (stendhalQ Q Λ) μ₀)=ψ 2*e v₀ := by
    rw [← mul_assoc,← ψ_mul_e,mul_assoc,e_mul_self]
  rw [← map_mul,mul_assoc _ (e jA),fixed]
  simp only [ψw_cons,ψw_nil,mul_one,mul_assoc]

private theorem cutLeft {v w : Seq μ₀} {z : V} (hz : E v*z*E w=z) : E v*z=z := by
  have h := congrArg (E v * ·) hz
  change E v*(E v*z*E w)=E v*z at h
  rw [← mul_assoc (E v),← mul_assoc (E v),idem,hz] at h
  exact h.symm

private theorem cutRight {v w : Seq μ₀} {z : V} (hz : E v*z*E w=z) : z*E w=z := by
  have h := congrArg (· * E w) hz
  change E v*z*E w*E w=z*E w at h
  rw [mul_assoc _ (E w),idem,hz] at h
  exact h.symm

private theorem factor_bottom : C*E v₀=C := by rw [← map_mul,mul_assoc,e_mul_self]

private theorem factor_mem : C∈J := by
  rw [fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ t (Or.inl rfl)]
  exact factor_bottom Q Λ ▸ TwoSidedIdeal.mul_mem_left _ C _ (TwoSidedIdeal.subset_span (Set.mem_singleton _))

private theorem factor_top : E t*C=C := by
  have h : (e t : KLRAlgebra k (stendhalQ Q Λ) μ₀)*(ψw [3,2]*e v₀)=ψw [3,2]*e v₀ := by
    rw [← show wordProd N [3,2] • v₀=t by decide,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  exact (map_mul F _ _).symm.trans (congrArg F h)

/-- All higher-ideal elements with central left cut factor by the two
crossings from the extreme. The bottom loading is unrestricted. -/
theorem fiveSlotCentral_higher_exists_leftFactor (hQ : KLRSymm Q) (x : V)
    (hx : x∈J) (left : E t*x=x) : ∃ y : V, E v₀*y=y ∧ C*y=x := by
  rw [fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ t (Or.inl rfl)] at hx
  apply exists_factor_of_mem_principal_idempotent_ideal (idem Q Λ t) (idem Q Λ v₀) _ x hx left
  intro z cut
  have desc : ∀ w : Perm (Fin N), w • t=v₀ → w ⟨4,by decide⟩ < w ⟨3,by decide⟩ := by decide +kernel
  obtain ⟨w,hw,ew⟩ := exists_viol_leftFactor_of_descent Q Λ hQ t v₀ 3 (by decide) desc z cut
  change E (sadj N 3 • t)*w*E v₀=w at hw
  change F (ψ 3*e (sadj N 3 • t))*w=z at ew
  rw [show sadj N 3 • t=jA by decide] at hw ew
  have desc' : ∀ u : Perm (Fin N), u • jA=v₀ → u ⟨3,by decide⟩ < u ⟨2,by decide⟩ := by decide +kernel
  obtain ⟨y,hy,ey⟩ := exists_viol_leftFactor_of_descent Q Λ hQ jA v₀ 2 (by decide) desc' w hw
  change E (sadj N 2 • jA)*y*E v₀=y at hy
  change F (ψ 2*e (sadj N 2 • jA))*y=w at ey
  rw [sadj_smul_smul] at hy ey
  exact ⟨y,hy,by rw [← split,mul_assoc,ey,ew]⟩

/-- A spectator of pairing at most one kills the entire source corner of the
two-row map, so its zero relations are reflected. -/
theorem fiveSlotCentral_rowReflection_of_smallSpectator (hQ : KLRSymm Q)
    (h : Λ 0 ()≤1) : FiveSlotCentralRowReflection Q Λ := by
  apply (fiveSlotCentral_leftWord_cancel_iff Q Λ hQ).1
  intro y hy _
  rw [fiveSlotLeftExtreme_idem_zero_of_spectatorWeight_le_one Q Λ h,zero_mul,zero_mul] at hy
  exact hy.symm

/-- A single two-row reflection condition in the globally violated quotient
suffices to mark all four central joints on the fixed exchanged bottom. -/
theorem fiveSlotCentral_markedExitJoints_of_row_reflection (hQ : KLRSymm Q)
    (reflect : FiveSlotCentralRowReflection Q Λ)
    (x : Fin 4 → V) (support : ∀ i, E t*x i*E (load i)=x i)
    (mark : ∀ i, x i∈J) (rel : ∑ i, x i*exitWord i=0) :
    ∃ a ∈ J, ∃ b ∈ J, ∃ c ∈ J, ∃ d ∈ J,
      E t*a*E jA=a ∧ E t*b*E jB=b ∧ E t*c*E jA=c ∧ E t*d*E jB=d ∧
      x 0=a*L [2] v₀+c*L [2,1] v₀ ∧ x 1=b*L [1] t-a*L [3] t ∧
      x 2=d*L [2,3] v₂-b*L [2] v₂ ∧ x 3= -(c*L [3] t+d*L [1] t) := by
  classical
  have cancel := (fiveSlotCentral_leftWord_cancel_iff Q Λ hQ).2 reflect
  choose w hw he using fun i => fiveSlotCentral_higher_exists_leftFactor Q Λ hQ (x i)
    (mark i) (cutLeft Q Λ (support i))
  let y i := w i*E (load i)
  have ycut (i : Fin 4) : E v₀*y i*E (load i)=y i := by
    simp only [y,← mul_assoc (E v₀),hw,mul_assoc _ (E (load i)),idem]
  have factor (i : Fin 4) : C*y i=x i := by
    change C*(w i*E (load i))=x i
    rw [← mul_assoc,he,cutRight Q Λ (support i)]
  have last (i : Fin 4) : exitWord i*E bot=exitWord i := by
    rw [← map_mul,mul_assoc,e_mul_self]
  have sumCut : E v₀*(∑ i, y i*exitWord i)*E bot=∑ i, y i*exitWord i := by
    simp only [Finset.mul_sum,Finset.sum_mul,← mul_assoc (E v₀),cutLeft Q Λ (ycut _),mul_assoc _ (exitWord _),last]
  have sumZero : ∑ i, y i*exitWord i=0 := by
    apply cancel _ sumCut
    simpa only [Finset.mul_sum,← mul_assoc C,factor] using rel
  obtain ⟨a,b,c,d,ha,hb,hc,hd,r₀,r₁,r₂,r₃⟩ := exists_fiveSlot_violQuotient_fourExitJointPresentation
    Q Λ hQ v₀ rfl y ycut sumZero
  have fixed (u : Seq μ₀) (z : V) (hz : E v₀*z*E u=z) : E t*(C*z)*E u=C*z := by
    rw [← mul_assoc (E t),factor_top,mul_assoc,cutRight Q Λ hz]
  refine ⟨C*a,TwoSidedIdeal.mul_mem_right J _ _ (factor_mem Q Λ),C*b,TwoSidedIdeal.mul_mem_right J _ _ (factor_mem Q Λ),
    C*c,TwoSidedIdeal.mul_mem_right J _ _ (factor_mem Q Λ),C*d,TwoSidedIdeal.mul_mem_right J _ _ (factor_mem Q Λ),
    fixed _ _ ha,fixed _ _ hb,fixed _ _ hc,fixed _ _ hd,?_,?_,?_,?_⟩
  · rw [← factor 0,r₀,mul_add]
    simp only [mul_assoc,AlgHom.comp_apply]
  · rw [← factor 1,r₁,mul_sub]
    simp only [mul_assoc,AlgHom.comp_apply]
  · rw [← factor 2,r₂,mul_sub]
    simp only [mul_assoc,AlgHom.comp_apply]
  · rw [← factor 3,r₃,mul_neg,mul_add]
    simp only [mul_assoc,AlgHom.comp_apply]

/-- At every bottom, cancellation of the principal factor on the supported
left-extreme corner suffices for injectivity at the central top. -/
theorem fiveSlotCentral_columnInclusion_of_leftCancellation (hQ : KLRSymm Q) (s : Seq μ₀)
    (cancel : ∀ y : V, E v₀*y*E s=y → C*y=0 → y=0) :
    Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s) := by
  apply blockKernelColumnInclusion_injective_of_principal_factor Q Λ t 1 2 s v₀ (by decide) C
    (factor_mem Q Λ) (factor_top Q Λ) (factor_bottom Q Λ)
    (fiveSlotCentral_higher_exists_leftFactor Q Λ hQ)
  intro y yl yr hz
  exact cancel y ((congrArg (·*E s) yl).trans yr) hz

/-- Webster, Lemma 6.8 after (6.21), at the central five-slot upper loading.
For the fixed exchanged bottom, reflection of the two specified PBW rows
after global violation suffices for injectivity of the balanced column. -/
theorem fiveSlotCentral_columnInclusion_of_rowReflection (hQ : KLRSymm Q)
    (reflect : FiveSlotCentralRowReflection Q Λ) :
    Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 bot) :=
  fiveSlotCentral_columnInclusion_of_leftCancellation Q Λ hQ bot
    ((fiveSlotCentral_leftWord_cancel_iff Q Λ hQ).2 reflect)


/-- The two ordinary red-black tests give cancellation on the source corner
of the central principal coefficient. -/
theorem fiveSlotCentral_leftWord_cancel_source_of_tests (hQ : KLRSymm Q)
    (first : OrdinaryCutCrossingTest Q Λ t jA 3)
    (second : OrdinaryCutCrossingTest Q Λ jA v₀ 2)
    (y : V) (hl : E v₀ * y = y)
    (hr : y * violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord t)) = y)
    (hz : C * y = 0) : y = 0 := by
  have hword : redWord t = List.finRange 3 := by decide
  have h₁ : redWord jA = redWord t := by decide
  have h₂ : redWord v₀ = redWord jA := by decide
  have hstep₁ : sadj N 3 • t = jA := by decide
  have hstep₂ : sadj N 2 • jA = v₀ := sadj_smul_smul 2 v₀
  let A := violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (List.finRange 3))
  have hv : A * E v₀ = E v₀ := by
    change violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (List.finRange 3)) *
      violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (e v₀)) = _
    rw [← map_mul, redProj_mul_e, ite_eq_left (h₂.trans (h₁.trans hword))]
    rfl
  have hy : A * y = y ∧ y * A = y := ⟨by rw [← hl, ← mul_assoc, hv], by rwa [hword] at hr⟩
  have hz' : F ((ψ 3 * e jA) * (ψ 2 * e v₀)) * y = 0 := by
    rw [map_mul, split Q Λ]
    exact hz
  exact eq_zero_of_twoCrossings_mul_of_corner Q Λ hword h₁ h₂ 3 2 hstep₁ hstep₂ hQ
    first second y hy hl hz'

/-- The actual central five-slot higher kernel is projective whenever the
two constituent ordinary crossings cancel on their source cuts. -/
theorem fiveSlotCentral_kernel_projective_of_tests (hQ : KLRSymm Q)
    (first : OrdinaryCutCrossingTest Q Λ t jA 3)
    (second : OrdinaryCutCrossingTest Q Λ jA v₀ 2) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord t)).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ t 1 2) :=
  blockLoadingKernel_projective_of_principal_factor Q Λ t 1 2 v₀
    (by decide) C (factor_mem Q Λ) (factor_top Q Λ) (factor_bottom Q Λ)
    (fiveSlotCentral_higher_exists_leftFactor Q Λ hQ)
    (fiveSlotCentral_leftWord_cancel_source_of_tests Q Λ hQ first second)

end Categorification.Stendhal.BraidedStendhalAlgebra
