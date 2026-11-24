/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.WeightedKLR.RedStrands.OrdinaryRetainedCrossing


/-!
# Cancellation at the nearby left loading

The principal crossing is injective on the two-interior bottom corner
before the globally violated quotient. In that quotient, injectivity of the
same crossing is equivalent to one saturation condition on the violated ideal.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "s" => fixedTopFourExitBottom
local notation "v₀" => fixedTopFourExitCut 0
local notation "t" => sadj n₀ 2 • v₀
local notation "A" => BraidedStendhalAlgebra k Q Λ ν₀
local notation "R₀" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "F" => ofKLR k Q Λ ν₀
local notation "p" => fun v : Seq μ₀ => F (e v)

private theorem checked_word (l : List ℕ) (h : ValidWord n₀ l)
    (hlen : l.length=invCount n₀ (wordProd n₀ l)) : IsReduced n₀ l :=
  ⟨h,by rw [length_eq_invCount]; exact hlen⟩

/-- The principal crossing is left-cancellative before imposing global
violation. Its two matching PBW rows stay reduced and distinct. -/
theorem fiveSlot_jA_leftCancellation_braided (hQ : KLRSymm Q) (y : A)
    (ly : p v₀*y=y) (ry : y*p s=y) (hy : F (ψ 2*e v₀)*y=0) : y=0 := by
  let G := toKLR k Q Λ ν₀
  let z := G (flip y)
  have hq := stendhalQ_symm Q Λ hQ
  have zl : (e s : R₀)*z=z := by
    have h : p s*flip y=flip y := by
      simpa only [flip_mul,flip_e] using congrArg flip ry
    simpa only [z,G,map_mul,toKLR_ofKLR_e] using congrArg G h
  have zr : z*(e v₀ : R₀)=z := by
    have h : flip y*p v₀=flip y := by
      simpa only [flip_mul,flip_e] using congrArg flip ly
    simpa only [z,G,map_mul,toKLR_ofKLR_e] using congrArg G h
  have cFlip : flip (F (ψ 2*e v₀)) = F (ψ 2*e t) := by
    rw [flip_ofKLR,hflip_mul,hflip_e,hflip_ψ,e_mul_ψ]
  have hz : z*(ψ 2*e t : R₀)=0 := by
    have h : flip y*F (ψ 2*e t)=0 := by
      simpa only [flip_mul,flip_zero,cFlip] using congrArg flip hy
    simpa only [z,G,map_mul,map_zero,toKLR_ofKLR_ψ,toKLR_ofKLR_e] using congrArg G h
  have h1 : IsReduced n₀ [1,2,3] := checked_word _ (by simp [ValidWord,stendhalWeight]) (by decide)
  have h2 : IsReduced n₀ [1,2,3,1] := checked_word _ (by simp [ValidWord,stendhalWeight]) (by decide)
  obtain ⟨f,g,hfg⟩ := exists_two_corner_coefficients_of_words hq v₀ s
    [1,2,3] [1,2,3,1] h1 h2 (by decide) (by decide +kernel) z zl zr
  have support : (e v₀ : R₀)*(ψ 2*e t)=ψ 2*e t := by
    rw [ψ_mul_e (Q := stendhalQ Q Λ) 2 t, sadj_smul_smul, ← mul_assoc, e_mul_self]
  have zero : (pol f*(ψw [1,2,3,2]*e t) + pol g*(ψw [1,2,3,1,2]*e t) : R₀)=0 := by
    rw [hfg,add_mul] at hz
    simp only [mul_assoc,support] at hz
    simpa only [ψw_cons,ψw_nil,mul_one,mul_assoc] using hz
  have hf := (top_polynomial_pair_eq_zero_iff_of_words hq
    (checked_word [1,2,3,2] (by simp [ValidWord,stendhalWeight]) (by decide))
    (checked_word [1,2,3,1,2] (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide) t f g).mp zero
  have hz0 : z=0 := by rw [hfg,hf.1,hf.2,map_zero,zero_mul,zero_mul,add_zero]
  have hY := congrArg F hz0
  have flipzero : flip y=0 := by
    simpa only [z,G,ofKLR_toKLR (hQ := hQ),map_zero] using hY
  simpa only [flip_flip,flip_zero] using congrArg flip flipzero

local notation "V" => ViolQuotient k Q Λ ν₀
local notation "π" => violMk k Q Λ ν₀

/-- The same crossing surjects onto the nearby top's entire two-interior
bottom corner, already in the globally violated quotient. -/
theorem fiveSlot_jA_leftFactor_viol (hQ : KLRSymm Q) (x : V)
    (hx : π (p t)*x*π (p s)=x) :
    ∃ y : V, π (p v₀)*y*π (p s)=y ∧ π (F (ψ 2*e v₀))*y=x := by
  have desc : ∀ w : Perm (Fin n₀), w • t=s →
      w ⟨3,by decide⟩ < w ⟨2,by decide⟩ := by decide +kernel
  have source : sadj n₀ 2 • t = v₀ := sadj_smul_smul ..
  have h := exists_viol_leftFactor_of_descent Q Λ hQ t s 2 (by decide) desc x hx
  simpa only [source] using h

/-- Exact saturation condition for cancellation of the nearby left
crossing on the two-interior bottom column after global violation. -/
theorem fiveSlot_jA_leftCancellation_viol_iff :
    (∀ y : V, π (p v₀)*y=y → y*π (p s)=y → π (F (ψ 2*e v₀))*y=0 → y=0) ↔
      ∀ z : A, p v₀*z=z → z*p s=z →
        F (ψ 2*e v₀)*z ∈ violIdeal k Q Λ ν₀ → z ∈ violIdeal k Q Λ ν₀ := by
  constructor
  · intro cancel z zl zr hz
    apply (violMk_eq_zero_iff z).mp
    apply cancel (π z)
    · simpa only [map_mul] using congrArg π zl
    · simpa only [map_mul] using congrArg π zr
    · simpa only [map_mul] using (violMk_eq_zero_iff _).mpr hz
  · intro saturation y yl yr hy
    obtain ⟨w,hw⟩ := violMk_surjective (Q := Q) (Λ := Λ) y
    let z : A := p v₀*w*p s
    have sq (v : Seq μ₀) : p v*p v=p v := by rw [← map_mul,e_mul_self]
    have zl : p v₀*z=z := by
      change p v₀*(p v₀*w*p s)=p v₀*w*p s
      rw [← mul_assoc,← mul_assoc,sq]
    have zr : z*p s=z := by
      change (p v₀*w*p s)*p s=p v₀*w*p s
      rw [mul_assoc,sq]
    have hπ : π z=y := by
      change π (p v₀*w*p s)=y
      rw [map_mul,map_mul,hw,yl,yr]
    have hz : F (ψ 2*e v₀)*z ∈ violIdeal k Q Λ ν₀ := by
      apply (violMk_eq_zero_iff _).mp
      rw [map_mul,hπ,hy]
    exact hπ.symm.trans ((violMk_eq_zero_iff z).mpr (saturation z zl zr hz))

local notation "map₀" => AlgHom.comp π F
local notation "c" => map₀ (ψ 2*e v₀)
local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) (redWord t)

private theorem nearbyPrincipalSupport : c ∈ J ∧ map₀ (e t) * c = c ∧ c * map₀ (e v₀) = c := by
  have cl : map₀ (e t)*c=c := by
    rw [← map_mul, ψ_mul_e (Q := stendhalQ Q Λ) 2 v₀, ← mul_assoc, e_mul_self]
  have cr : c*map₀ (e v₀)=c := by rw [← map_mul,mul_assoc,e_mul_self]
  have hc : c ∈ J := by
    rw [fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ t (.inr rfl)]
    exact cr ▸ TwoSidedIdeal.mul_mem_left _ c _ (TwoSidedIdeal.subset_span (Set.mem_singleton _))
  exact ⟨hc, cl, cr⟩

/-- The source-corner cancellation test makes the nearby five-slot higher
kernel a loading projective. -/
theorem fiveSlot_jA_kernel_projective_of_test (hQ : KLRSymm Q)
    (test : OrdinaryCutCrossingTest Q Λ t v₀ 2) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord t)).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ t 1 2) := by
  obtain ⟨hc, cl, cr⟩ := nearbyPrincipalSupport Q Λ
  apply blockLoadingKernel_projective_of_principal_factor Q Λ t 1 2 v₀
    (by decide) c hc cl cr (fiveSlot_jA_higher_exists_leftFactor Q Λ hQ)
  intro y hl hr hz
  have word : redWord t = List.finRange 3 := by decide
  have order : redWord v₀ = redWord t := by decide
  have step : sadj n₀ 2 • t = v₀ := sadj_smul_smul 2 v₀
  let E₀ := violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (List.finRange 3))
  have hv : E₀ * map₀ (e v₀) = map₀ (e v₀) := by
    change violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (List.finRange 3)) *
      violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (e v₀)) = _
    rw [← map_mul, redProj_mul_e, ite_eq_left (order.trans word)]
    rfl
  have hy : E₀ * y = y ∧ y * E₀ = y := ⟨by rw [← hl, ← mul_assoc, hv], by rwa [word] at hr⟩
  exact eq_zero_of_crossing_mul_of_corner Q Λ word order 2 step hQ test y hy hl hz

/-- At the five-slot nearby left top, cancellation of the single crossing
from the left-extreme loading suffices for the marked tensor inclusion. -/
theorem fiveSlot_jA_blockKernelColumnInclusion_injective_of_leftCancellation
    (hQ : KLRSymm Q) (bottom : Seq μ₀)
    (cancel : ∀ y : V, map₀ (e v₀)*y=y → y*map₀ (e bottom)=y → c*y=0 → y=0) :
    Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 bottom) := by
  obtain ⟨hc, cl, cr⟩ := nearbyPrincipalSupport Q Λ
  exact blockKernelColumnInclusion_injective_of_principal_factor Q Λ t 1 2 bottom v₀ (by decide)
    c hc cl cr (fiveSlot_jA_higher_exists_leftFactor Q Λ hQ) cancel

/-- For the two-interior bottom column at the nearby left loading, a
single saturated corner of the global violated ideal completes the
injectivity test in Webster's (6.21). -/
theorem fiveSlot_jA_blockKernelColumnInclusion_injective_of_violated_saturation
    (hQ : KLRSymm Q)
    (saturates : ∀ z : A, p v₀*z=z → z*p s=z →
      F (ψ 2*e v₀)*z ∈ violIdeal k Q Λ ν₀ → z ∈ violIdeal k Q Λ ν₀) :
    Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s) :=
  fiveSlot_jA_blockKernelColumnInclusion_injective_of_leftCancellation Q Λ hQ s
    ((fiveSlot_jA_leftCancellation_viol_iff Q Λ).mpr saturates)

end Categorification.Stendhal.BraidedStendhalAlgebra
