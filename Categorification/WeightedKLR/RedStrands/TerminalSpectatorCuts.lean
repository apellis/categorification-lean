/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoSpectatorKernelLayer
import Categorification.WeightedKLR.RedStrands.BlockKernelCrossingGenerator
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.RightmostRedCrossingInjectivity

/-!
# Factoring higher one-black cuts through the terminal spectator

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
In the four-red loading, every reduced path from a strictly higher retained loading can
begin at the terminal crossing. The affine cut factorization also holds whenever the
permutation of the two loadings has the corresponding left descent.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA Equiv MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k]
variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν

private def withFirstCrossing (j : ℕ) (hj : j + 1 < m) (v : Perm (Fin m)) : List ℕ :=
  if v⁻¹ ⟨j + 1, hj⟩ < v⁻¹ ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩
    then j :: canWord m (sadj m j * v) else canWord m v

omit [DecidableEq I] in
private theorem withFirstCrossing_spec (j : ℕ) (hj : j + 1 < m) :
    IsReducedChoice (withFirstCrossing j hj) := by
  intro v
  unfold withFirstCrossing
  split_ifs with h
  · have hp : wordProd m (j :: canWord m (sadj m j * v)) = v := by
      rw [wordProd_cons, wordProd_canWord, ← mul_assoc, TypeA.sadj_mul_self, one_mul]
    refine ⟨⟨validWord_cons.2 ⟨hj, (isReduced_canWord _ _).validWord⟩, ?_⟩, hp⟩
    rw [hp, List.length_cons, (isReduced_canWord _ _).length_eq, wordProd_canWord]
    exact length_sadj_mul_of_gt hj h
  · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

/-- If every permutation carrying the bottom loading to the top has a left
descent at the crossing, every affine cut factors through that crossing. -/
theorem cut_factors_of_leftDescent (j : ℕ) (hj : j + 1 < m) (s w : Seq ν) (z : R)
    (hdesc : ∀ v : Perm (Fin m), v • w = s →
      v⁻¹ ⟨j + 1, hj⟩ < v⁻¹ ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩) :
    ∃ y : R, (ψ j * e (sadj m j • s)) * y = e s * z * e w := by
  let F : R →ₗ[k] R := (LinearMap.mulRight k (e w)).comp (LinearMap.mulLeft k (e s))
  let G : R →ₗ[k] R := LinearMap.mulLeft k (ψ j * e (sadj m j • s))
  change F z ∈ LinearMap.range G
  let ρ := withFirstCrossing j hj
  have hρ : IsReducedChoice ρ := withFirstCrossing_spec j hj
  have W : z ∈ Submodule.span k {b : R | ∃ (v : Perm (Fin m)) (d : Fin m →₀ ℕ) (t : Seq ν),
      ψw (ρ v) * pol (monomial d (1 : k)) * e t = b} := by rw [span_eq_top' ρ hρ]; trivial
  change z ∈ (LinearMap.range G).comap F
  refine (Submodule.span_le.2 ?_ : _ ≤ (LinearMap.range G).comap F) W
  rintro _ ⟨v,d,t,rfl⟩
  change e s * (ψw (ρ v) * pol (monomial d (1 : k)) * e t) * e w ∈ LinearMap.range G
  by_cases hi : t = w
  · subst t
    have hepoly : (e w * (pol (monomial d (1 : k)) * e w) : R) = pol (monomial d (1 : k)) * e w := by
      rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, e_mul_self]
    have hcut : (e s * (ψw (ρ v) * pol (monomial d (1 : k)) * e w) * e w : R) =
        (e s * ψw (ρ v)) * (pol (monomial d (1 : k)) * e w) := by
      simp only [mul_assoc, e_mul_self]
    by_cases ht : v • w = s
    · rw [hcut, show (e s * ψw (ρ v) : R) = ψw (ρ v) * e w by
        rw [e_mul_ψw, (hρ v).2, ← ht, inv_smul_smul],
        mul_assoc, hepoly]
      let σ := canWord m (sadj m j * v)
      have hword : ρ v = j :: σ := by
        change withFirstCrossing j hj v = _
        rw [withFirstCrossing, ite_eq_left (hdesc v ht)]
      have hσ : wordProd m σ • w = sadj m j • s := by
        change wordProd m (canWord m (sadj m j * v)) • w = _
        rw [wordProd_canWord, mul_smul, ht]
      refine ⟨ψw σ * (pol (monomial d (1 : k)) * e w), ?_⟩
      change (ψ j * e (sadj m j • s)) * (ψw σ * (pol (monomial d (1 : k)) * e w)) =
        ψw (ρ v) * (pol (monomial d (1 : k)) * e w)
      rw [hword, ψw_cons, mul_assoc (ψ j), ← mul_assoc (e (sadj m j • s))]
      rw [show (e (sadj m j • s) * ψw σ : R) = ψw σ * e w by
        rw [e_mul_ψw, ← hσ, inv_smul_smul]]
      simp only [mul_assoc, hepoly]
    · have h' : wordProd m (ρ v) • w ≠ s := by rw [(hρ v).2]; exact ht
      have hz : (e s * (ψw (ρ v) * pol (monomial d (1 : k)) * e w) * e w : R) = 0 := by
        calc
          _ = (e s * (ψw (ρ v) * e w)) * (pol (monomial d (1 : k)) * e w) := by
            rw [hcut]
            simp only [mul_assoc, hepoly]
          _ = _ := by
            rw [ψw_mul_e, ← mul_assoc (e s), e_mul_e, ite_eq_right (Ne.symm h'),
              zero_mul, zero_mul]
      rw [hz]
      exact Submodule.zero_mem _
  · rw [mul_assoc (e s), mul_assoc (ψw (ρ v) * pol (monomial d (1 : k))),
      e_mul_e, ite_eq_right hi, mul_zero, mul_zero]
    exact Submodule.zero_mem _

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA Equiv

private abbrev μ := stendhalWeight 4 ({()} : Multiset Unit)
private abbrev n := Multiset.card μ

private theorem terminalDescent (w : Seq μ) (ho : redWord w = redWord source)
    (hlt : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 w)
    (v : Perm (Fin n)) (hv : v • w = source) : v⁻¹ (4 : Fin 5) < v⁻¹ (3 : Fin 5) := by
  have hoff : redWord source = ([] : List (Fin 4)) ++ 0 :: 1 :: [2, 3] := by decide
  have hlabel (j : Fin n) : w.lbl (v⁻¹ j) = source.lbl j :=
    (congrArg (fun y : Seq μ => y.lbl j) hv)
  have hb : w.lbl (v⁻¹ (4 : Fin 5)) = .inl () := (hlabel _).trans rfl
  have ht : w.lbl (v⁻¹ (3 : Fin 5)) = .inr 3 := (hlabel _).trans rfl
  obtain ⟨_, r, ps, pt, hr, hps, hpt, hsep, hp⟩ :=
    (adjacentBlockRoot_oneBlack_lt_iff hoff (ho.trans hoff) ⟨4, by decide⟩
      (v⁻¹ (4 : Fin 5)) rfl hb).1 hlt
  by_cases hr3 : r = 3
  · subst r
    have heq := lbl_inj_of_inr w 3 hpt ht
    simpa only [heq] using hp
  have hpairs := redWord_pairwise_one w
  rw [ho, hoff] at hpairs
  have hpt' : pt < v⁻¹ (3 : Fin 5) := by
    fin_cases r
    · exact (List.pairwise_cons.mp hpairs).1 3 (by decide) _ _ hpt ht
    · exact (hr rfl).elim
    · exact (List.pairwise_cons.mp (List.pairwise_cons.mp
          (List.pairwise_cons.mp hpairs).2).2).1 3 (by decide) _ _ hpt ht
    · exact (hr3 rfl).elim
  exact hp.trans hpt'

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

/-- The loading obtained by moving the black immediately before the terminal red. -/
def terminalHigher : Seq μ :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inr 3] (by decide)

private theorem terminalStep : TypeA.sadj n 3 • source = terminalHigher := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

/-- All the affine higher cuts factor through the terminal crossing for four reds.
The proof uses the retained order and applies to arbitrary spectator weights. -/
theorem terminalCut_factors (w : Seq μ) (ho : redWord w = redWord source)
    (hlt : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 w)
    (z : KLRAlgebra k (stendhalQ Q Λ) μ) :
    ∃ y : KLRAlgebra k (stendhalQ Q Λ) μ,
      (ψ 3 * e terminalHigher) * y = e source * z * e w := by
  have h := cut_factors_of_leftDescent 3 (by decide) source w z (terminalDescent w ho hlt)
  rw [terminalStep] at h
  exact h

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA Equiv MulOpposite

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

private theorem terminalOrder : redWord terminalHigher = redWord source := by decide

private theorem terminalHigher_lt : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 terminalHigher := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad : (0 : ℕ) = 1 := congrFun (congrFun h (3 : Fin 4)) ()
    contradiction

private theorem swapTerminal : TypeA.sadj n 3 • terminalHigher = source := by
  apply Subtype.ext; funext j; fin_cases j <;> decide

noncomputable section
open MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev ν : Multiset Unit := {()}
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun w => π (KLRAlgebra.e w)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord source))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord source) terminalHigher terminalOrder
local notation "P" => rIdeal (orderedLoadingIdem Q Λ source)
local notation "K" => blockLoadingKernel Q Λ source 0 1
local notation "J" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 source) (redWord source)

/-- The red-black crossing from the terminalHigher loading into the source projective
is an element of the higher retained kernel. -/
def terminalCrossing : K := by
  let c := blockLoadingRep Q Λ source (π (ψ 3 * KLRAlgebra.e terminalHigher))
  refine ⟨c, ?_⟩
  have hd : p terminalHigher ∈ J := TwoSidedIdeal.subset_span ⟨terminalHigher, terminalOrder, terminalHigher_lt, rfl⟩
  change c.1.1 ∈ J
  rw [blockLoadingRep_val, map_mul]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hd))

theorem terminalCrossing_val : (terminalCrossing Q Λ).1.1.1 = π (ψ 3 * KLRAlgebra.e terminalHigher) := by
  change (blockLoadingRep Q Λ source (π (ψ 3 * KLRAlgebra.e terminalHigher))).1.1 = _
  have hx : (KLRAlgebra.e source * (ψ 3 * KLRAlgebra.e terminalHigher) : R) = ψ 3 * KLRAlgebra.e terminalHigher := by
    rw [ψ_mul_e, swapTerminal, ← mul_assoc, e_mul_self]
  have hE : p terminalHigher * E = p terminalHigher := by
    change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e terminalHigher))) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left terminalOrder]
    rfl
  rw [blockLoadingRep_val]
  change π (KLRAlgebra.e source) * π (ψ 3 * KLRAlgebra.e terminalHigher) * E = _
  rw [← map_mul, hx, map_mul, mul_assoc, hE]

/-- Left multiplication by the red-black crossing maps the intermediate loading projective to the kernel. -/
def terminalCrossingMap : rIdeal d →ₗ[Tᵐᵒᵖ] K where
  toFun y := op y.1 • terminalCrossing Q Λ
  map_add' y z := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 + z.1.1) = _ * y.1.1 + _ * z.1.1
    rw [mul_add]
  map_smul' a y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 * a.unop.1) = (_ * y.1.1) * a.unop.1
    rw [mul_assoc]

theorem terminalCrossingMap_val (y : rIdeal d) :
    (terminalCrossingMap Q Λ y).1.1.1 = π (ψ 3 * KLRAlgebra.e terminalHigher) * y.1.1 := by
  change (terminalCrossing Q Λ).1.1.1 * y.1.1 = _
  rw [terminalCrossing_val]

/-- The crossing onto the source loading generates its higher retained kernel.
This uses only the one-black reduced paths, with arbitrary red weights. -/
theorem terminalCrossingMap_surjective : Function.Surjective (terminalCrossingMap Q Λ) := by
  let F : rIdeal d →ₗ[Tᵐᵒᵖ] P := (K).subtype.comp (terminalCrossingMap Q Λ)
  suffices h : K ≤ LinearMap.range F by
    intro x
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨y, Subtype.ext hy⟩
  rw [blockLoadingKernel_eq_span]
  apply Submodule.span_le.2
  rintro _ ⟨w, ho, hlt, z, rfl⟩
  by_cases hv : IsViolated w
  · have hp : p w = 0 := violMk_e hv
    change blockLoadingRep Q Λ source (z * p w) ∈ LinearMap.range F
    rw [hp, mul_zero]
    convert (LinearMap.range F).zero_mem using 1
    apply Subtype.ext; apply Subtype.ext
    rw [blockLoadingRep_val, mul_zero, zero_mul]
    rfl
  · obtain ⟨z', rfl⟩ := (violMk_surjective.comp ofKLR_surjective : Function.Surjective π) z
    obtain ⟨y, hy⟩ := terminalCut_factors Q Λ w ho hlt z'
    let y' : T := ⟨E * π y * E, π y, rfl⟩
    have hidem : IsIdempotentElem d := by
      apply Subtype.ext
      exact congrArg Subtype.val (orderedLoadingIdem_idem Q Λ terminalHigher).eq
    refine ⟨rIdealProj hidem y', ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change (terminalCrossingMap Q Λ (rIdealProj hidem y')).1.1.1 =
      (blockLoadingRep Q Λ source (π z' * p w)).1.1
    have hE : p terminalHigher * E = p terminalHigher := by
      change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e terminalHigher))) * E = _
      rw [← map_mul, e_mul_redProj, ite_eq_left terminalOrder]
      rfl
    have hp : p terminalHigher * p terminalHigher = p terminalHigher := congrArg Subtype.val hidem.eq
    rw [terminalCrossingMap_val, blockLoadingRep_val]
    change π (ψ 3 * KLRAlgebra.e terminalHigher) * (p terminalHigher * (E * π y * E)) =
      p source * (π z' * p w) * E
    have hfix : π (ψ 3 * KLRAlgebra.e terminalHigher) * p terminalHigher = π (ψ 3 * KLRAlgebra.e terminalHigher) := by
      rw [map_mul, mul_assoc, hp]
    have hfix' : π (ψ 3 * KLRAlgebra.e terminalHigher) * E = π (ψ 3 * KLRAlgebra.e terminalHigher) := by
      rw [map_mul, mul_assoc, hE]
    calc
      _ = (π (ψ 3 * KLRAlgebra.e terminalHigher) * p terminalHigher * E) * π y * E := by
        simp only [mul_assoc]
      _ = π ((ψ 3 * KLRAlgebra.e terminalHigher) * y) * E := by
        rw [hfix, hfix']
        simp only [map_mul]
      _ = _ := by rw [hy, map_mul, map_mul, mul_assoc (p source)]

private theorem terminalPath (h2 : Λ 2 () = 0) :
    ZeroWeightSpectatorPath Λ terminalHigher higher := by
  have hs : TypeA.sadj n 2 • terminalHigher = higher := by
    apply Subtype.ext; funext j; fin_cases j <;> decide
  rw [← hs]
  exact ZeroWeightSpectatorPath.swap .nil 2 (by decide) 2 rfl rfl h2

private theorem beforeSpectators (r : Fin 4) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (q : Fin n) (hq : higher.lbl q = .inr r) : (⟨2, by decide⟩ : Fin n) < q := by
  fin_cases r
  · exact (hr0 rfl).elim
  · exact (hr1 rfl).elim
  · fin_cases q <;> revert hq <;> decide
  · fin_cases q <;> revert hq <;> decide

/-- Once the terminal crossing is injective, composing it with the zero-weight
spectator crossing gives the one higher partial-standard layer of the kernel. -/
theorem kernel_hasHigherFiltration_of_terminal_injective
    (h2 : Λ 2 () = 0) (hinj : Function.Injective (terminalCrossingMap Q Λ)) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of _ (blockLoadingKernel Q Λ source 0 1)) := by
  apply ModuleFiltration.HasFiltration.single
  let f := LinearEquiv.ofBijective (terminalCrossingMap Q Λ) ⟨hinj, terminalCrossingMap_surjective Q Λ⟩
  have he := ZeroWeightSpectatorPath.orderedIdemEquivAt Λ Q (terminalPath Λ h2) terminalOrder
  let g := (Classical.choose_spec (Classical.choose_spec he)).rIdealEquiv
  let h := blockPartialStandardAt_equiv_projective Q Λ higher 0 1 (redWord source) sameOrder
    (fun _ ho hlt => isViolated_of_strictly_higher_beforeSpectators (M := [2,3])
      (by decide) ho ⟨2, by decide⟩ rfl beforeSpectators hlt)
  exact f.symm.trans (g.trans h.symm)

end

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)
private abbrev νp : Multiset Unit := {()}
private abbrev μp := stendhalWeight 4 νp
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μp
local notation "V" => ViolQuotient k Q Λ νp
local notation "B" => BraidedStendhalAlgebra k Q Λ νp
local notation "π" => AlgHom.comp (violMk k Q Λ νp) (ofKLR k Q Λ νp)
local notation "E" => violMk k Q Λ νp (redProj k Q Λ νp (List.finRange 4))
local notation "p" => fun s => π (KLRAlgebra.e s)

private theorem word : redWord source = List.finRange 4 := by decide
private theorem highWord : redWord terminalHigher = List.finRange 4 := terminalOrder.trans word
private theorem step : sadj (Multiset.card μp) 3 • source = terminalHigher := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private def cornerImage (z : R) : (isIdempotentElem_violRedProj k Q Λ νp).Corner :=
  violCornerHom k Q Λ νp (cornerMk (ofKLR k Q Λ νp z))

private theorem cornerImage_idem :
    (cornerImage Q Λ (KLRAlgebra.e terminalHigher)).1 = p terminalHigher := by
  rw [cornerImage, violCornerHom_val, cornerMk_e_val highWord]
  rfl

private theorem cornerImage_cross :
    (cornerImage Q Λ (ψ 3 * KLRAlgebra.e source)).1 = π (ψ 3 * KLRAlgebra.e source) := by
  let eR := redProj k Q Λ νp (List.finRange 4)
  let c := ofKLR k Q Λ νp (ψ 3 * KLRAlgebra.e source)
  have hc : (ψ 3 * KLRAlgebra.e source : R) = KLRAlgebra.e terminalHigher * ψ 3 := by
    rw [e_mul_ψ, ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  have hleft : eR * c = c := by
    dsimp [eR, c]
    rw [hc, map_mul, redProj_mul_e_of_eq highWord]
  have hright : c * eR = c := by
    dsimp [eR, c]
    rw [map_mul, mul_assoc, e_mul_redProj, ite_eq_left word]
  change violMk k Q Λ νp (eR * c * eR) = _
  rw [hleft, hright]
  rfl

private theorem flipMul (x y : V) : violFlip (x * y) = violFlip y * violFlip x :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ νp) x y)

private theorem flipE : violFlip E = E := by
  rw [violFlip_violMk, flip_redProj]

private theorem flipHigh : violFlip (p terminalHigher) = p terminalHigher := by
  change violFlip (violMk k Q Λ νp (ofKLR k Q Λ νp (KLRAlgebra.e terminalHigher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_e]
  rfl

private theorem flipCross :
    violFlip (π (ψ 3 * KLRAlgebra.e terminalHigher)) = π (ψ 3 * KLRAlgebra.e source) := by
  change violFlip (violMk k Q Λ νp (ofKLR k Q Λ νp (ψ 3 * KLRAlgebra.e terminalHigher))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_mul, hflip_e, hflip_ψ, e_mul_ψ,
    ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  rfl

private theorem ordinaryImage (z : R) :
    identityCornerToTensor k Q Λ νp (cornerMk (ofKLR k Q Λ νp z)) = tensorOfKLR Q Λ νp z := by
  apply congrArg (TensorProductAlgebra.mk Q Λ νp)
  apply Subtype.ext
  rw [identityCornerHom_val, cornerMk_val, map_mul, map_mul,
    toAllOrders_ofKLR]
  change toAllOrders k Q Λ νp (ofKLR k Q Λ νp (redIdem k Q Λ (List.finRange 4))) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ νp z *
      toAllOrders k Q Λ νp (ofKLR k Q Λ νp (redIdem k Q Λ (List.finRange 4))) = _
  rw [toAllOrders_redIdem]
  let eR := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νp
  let a := StendhalAlgebraAllOrders.ofKLR k Q Λ νp z
  change eR * a * eR = a * eR
  rw [(redOrderedIdem_commute Q Λ νp a).eq, mul_assoc,
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq]

/-- A right multiplication test in the ordinary ordered algebra transports, by
the quotient corner equivalence and diagram flip, to the higher right-projective map. -/
theorem terminalCrossingMap_injective_of_ordinary_test (hQ : KLRSymm Q)
    (h : ∀ x : TensorProductAlgebra k Q Λ νp,
      x * tensorOfKLR Q Λ νp (KLRAlgebra.e terminalHigher) = x →
      x * tensorOfKLR Q Λ νp (ψ 3 * KLRAlgebra.e source) = 0 →
      x = 0) :
    Function.Injective (terminalCrossingMap Q Λ) := by
  let ρ := TypeA.canWord (Multiset.card μp)
  have hρ : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let q := violCornerEquiv (ν := νp) (Λ := Λ) hρ hQ
  let projective := rIdeal (orderedLoadingIdemAt Q Λ (redWord source) terminalHigher terminalOrder)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : AddCommGroup (blockLoadingKernel Q Λ source 0 1) := blockKernelAddGroup Q Λ source 0 1
  suffices hz : ∀ y : projective, terminalCrossingMap Q Λ y = 0 → y = 0 by
    intro y z hyz
    have hs : terminalCrossingMap Q Λ (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    exact sub_eq_zero.mp (hz (y - z) hs)
  intro y hy
  have hY : E * y.1.1 = y.1.1 ∧ y.1.1 * E = y.1.1 := by
    have inner := (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ νp (redWord source))).1 y.1.2
    have hEeq : violMk k Q Λ νp (redProj k Q Λ νp (redWord source)) = E :=
      congrArg (fun order => violMk k Q Λ νp (redProj k Q Λ νp order)) word
    exact ⟨(congrArg (fun z => z * y.1.1) hEeq).symm.trans inner.1,
      (congrArg (fun z => y.1.1 * z) hEeq).symm.trans inner.2⟩
  let fy : (isIdempotentElem_violRedProj k Q Λ νp).Corner := ⟨violFlip y.1.1,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violRedProj k Q Λ νp)).2
    ⟨by rw [← flipE Q Λ, ← flipMul Q Λ, hY.2],
     by rw [← flipE Q Λ, ← flipMul Q Λ, hY.1]⟩⟩
  have hf : fy * cornerImage Q Λ (KLRAlgebra.e terminalHigher) = fy := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (KLRAlgebra.e terminalHigher)).1 = violFlip y.1.1
    have hp : p terminalHigher * y.1.1 = y.1.1 := congrArg Subtype.val y.2
    rw [cornerImage_idem, ← flipHigh Q Λ, ← flipMul Q Λ, hp]
  have hh : fy * cornerImage Q Λ (ψ 3 * KLRAlgebra.e source) = 0 := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (ψ 3 * KLRAlgebra.e source)).1 = 0
    have hx : π (ψ 3 * KLRAlgebra.e terminalHigher) * y.1.1 = 0 := by
      rw [← terminalCrossingMap_val, hy]
      rfl
    rw [cornerImage_cross, ← flipCross Q Λ, ← flipMul Q Λ, hx]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ νp))
  have himg (z : R) : q (cornerImage Q Λ z) = tensorOfKLR Q Λ νp z :=
    (violCornerEquiv_violCornerHom hρ hQ (cornerMk (ofKLR k Q Λ νp z))).trans (ordinaryImage Q Λ z)
  have hq : q fy = 0 := h (q fy) (by rw [← himg, ← map_mul q, hf])
    (by rw [← himg, ← map_mul q, hh, map_zero])
  have hfy : fy = 0 := q.injective (hq.trans (map_zero q).symm)
  apply Subtype.ext; apply Subtype.ext
  have hhf : violFlip y.1.1 = 0 := congrArg Subtype.val hfy
  exact (violFlip_violFlip y.1.1).symm.trans (by
    rw [hhf]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ νp)))

private def prefixLoading : Seq (stendhalWeight 3 ((0 : Multiset Unit) + 0)) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2] (by decide)

private theorem prefix_ordered : IsRedOrdered prefixLoading := by unfold IsRedOrdered; decide

private theorem higher_append :
    appendRedLoading (appendBlackLoading () (0 + 0) prefixLoading) = terminalHigher := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private theorem source_append :
    appendBlackLoading () (0 + 0) (appendRedLoading prefixLoading) = source := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

/-- The rightmost crossing test on the three-red prefix transports to the terminal map. -/
private theorem terminalCrossingMap_of_exact_prefix (hQ : KLRSymm Q)
    (hLast : ∀ x : TensorProductAlgebra k Q Λ ({()} + ((0 : Multiset Unit) + 0)),
      x * tensorOfKLR Q Λ _ (KLRAlgebra.e (appendRedLoading (appendBlackLoading () (0 + 0) prefixLoading))) = x →
      x * tensorOfKLR Q Λ _ (ψ ((stendhalWeight 3 ((0 : Multiset Unit) + 0)).card) *
        KLRAlgebra.e (appendBlackLoading () (0 + 0) (appendRedLoading prefixLoading))) = 0 →
      x = 0) :
    Function.Injective (terminalCrossingMap Q Λ) := by
  apply terminalCrossingMap_injective_of_ordinary_test Q Λ hQ
  intro x hx hc
  have hedges : (stendhalWeight 3 ((0 : Multiset Unit) + 0)).card = 3 := by decide
  apply hLast x
  · rw [higher_append]
    exact hx
  · rw [hedges, source_append]
    exact hc

section Standard

open QuantumGroup KL3.Diagram

variable {F : Type*} [Field F] {C : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C F)

/-- The crossing into the loading kernel is injective at the standard
Khovanov–Lauda parameters, including positive spectator weight. -/
theorem terminalCrossingMap_standard_injective
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ) :
    Function.Injective (terminalCrossingMap QL weights) :=
  terminalCrossingMap_of_exact_prefix QL weights hQ
    (eq_zero_of_mul_rightmostRedCrossing hR hQ weights () 0 prefixLoading prefix_ordered)

/-- The kernel has the higher partial standard as a single layer for the standard
Khovanov–Lauda parameters and arbitrary spectator weight. -/
theorem mixedKernel_hasHigherFiltration_standard
    (hR : IsRouquierQ C QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ)
    (h2 : weights 2 () = 0) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt QL weights higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of _ (blockLoadingKernel QL weights source 0 1)) :=
  kernel_hasHigherFiltration_of_terminal_injective QL weights h2
    (terminalCrossingMap_standard_injective hR hQ weights)

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack
