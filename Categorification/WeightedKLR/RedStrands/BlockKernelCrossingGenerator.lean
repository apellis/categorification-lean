/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# Generating the one-black retained-boundary kernel

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21).
For the three-red, one-black example, the crossing at the spectator gives a
surjection from the higher loading projective onto the kernel. The proof uses
the reduced paths to each surviving higher loading and permits arbitrary red weights.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack

open KLR KLRAlgebra TypeA Equiv MvPolynomial

private abbrev μ := stendhalWeight 3 ({()} : Multiset Unit)
private abbrev n := Multiset.card μ
private def middle : Seq μ := KLRAlgebra.Seq.ofList [.inr 0, .inl (), .inr 1, .inr 2] (by decide)

private theorem source_shift : sadj n 2 • higher = source := by
  apply Subtype.ext; funext i
  fin_cases i <;> decide
private theorem higher_shift : sadj n 1 • middle = higher := by
  apply Subtype.ext; funext i
  fin_cases i <;> decide
private noncomputable def words (v : Perm (Fin n)) : List ℕ :=
  if v = sadj n 2 then [2] else if v = sadj n 2 * sadj n 1 then [2,1] else canWord n v

private theorem highWord : words (sadj n 2) = [2] := by simp [words]
private theorem middleWord : words (sadj n 2 * sadj n 1) = [2,1] := by
  rw [words, ite_eq_right (by decide), ite_eq_left rfl]

private theorem words_spec : IsReducedChoice words := by
  intro v
  by_cases h : v = sadj n 2
  · subst v
    rw [highWord]
    refine ⟨⟨by simp [ValidWord]; decide, ?_⟩, by simp [wordProd_cons]⟩
    simp [wordProd_cons, length_sadj (by decide : 2 + 1 < n)]
  by_cases h' : v = sadj n 2 * sadj n 1
  · subst v
    rw [middleWord]
    refine ⟨⟨by simp [ValidWord]; decide, ?_⟩, by simp [wordProd_cons]⟩
    have hl := length_sadj_mul (by decide : 2 + 1 < n) (sadj n 1)
    rw [length_sadj (by decide : 1 + 1 < n)] at hl
    have hz : length n (sadj n 2 * sadj n 1) ≠ 0 := fun hzero =>
      (show sadj n 2 * sadj n 1 ≠ 1 by decide) (length_eq_zero_iff.1 hzero)
    simp only [List.length_cons, List.length_nil, wordProd_cons, wordProd_nil, mul_one]
    omega
  · rw [words, ite_eq_right h, ite_eq_right h']
    exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private theorem perm_injective_at (s : Seq μ) : Function.Injective (fun v : Perm (Fin n) => v • s) := by
  have hf : Function.Injective s.lbl := by
    have hn : (Finset.univ.val.map s.lbl).Nodup := by
      rw [show Finset.univ.val.map s.lbl = μ from s.2]
      decide
    exact fun a b h => Multiset.inj_on_of_nodup_map hn a (by simp) b (by simp) h
  intro v w h
  apply inv_injective
  apply Equiv.ext
  intro i
  apply hf
  exact congrArg (fun t : Seq μ => t.lbl i) h

private theorem classify (w : Seq μ) (ho : redWord w = redWord source)
    (hlt : adjacentBlockRoot 0 1 source < adjacentBlockRoot 0 1 w) :
    IsViolated w ∨ w = higher ∨ w = middle := by
  suffices test : ∀ w : Seq μ, redWord w = redWord source → w ≠ source →
      (w.lbl ⟨0, by decide⟩).isLeft ∨ w = higher ∨ w = middle by
    have hne : w ≠ source := fun h => hlt.ne (congrArg (adjacentBlockRoot 0 1) h).symm
    rcases test w ho hne with hv | h'
    · exact .inl ⟨by decide, hv⟩
    · exact .inr h'
  let : Fintype (Seq μ) := inferInstanceAs (Fintype { f : Fin 4 → Unit ⊕ Fin 3 //
    Finset.univ.val.map f = μ })
  decide

variable {k : Type*} [CommRing k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ

private theorem cut_factors (w : Seq μ) (hw : w = higher ∨ w = middle) (z : R) :
    ∃ y : R, (ψ 2 * e higher) * y = e source * z * e w := by
  let F : R →ₗ[k] R := (LinearMap.mulRight k (e w)).comp (LinearMap.mulLeft k (e source))
  let G : R →ₗ[k] R := LinearMap.mulLeft k (ψ 2 * e higher)
  change F z ∈ LinearMap.range G
  let ρ := words
  have hρ : IsReducedChoice ρ := words_spec
  have W : z ∈ Submodule.span k {b : R | ∃ (v : Perm (Fin n)) (d : Fin n →₀ ℕ) (i : Seq μ),
      ψw (ρ v) * pol (monomial d (1 : k)) * e i = b} := by rw [span_eq_top' ρ hρ]; trivial
  change z ∈ (LinearMap.range G).comap F
  refine (Submodule.span_le.2 ?_ : _ ≤ (LinearMap.range G).comap F) W
  rintro _ ⟨v,d,i,rfl⟩
  change e source * (ψw (ρ v) * pol (monomial d (1 : k)) * e i) * e w ∈ LinearMap.range G
  by_cases hi : i = w
  · subst i
    have hepoly : (e w * (pol (monomial d (1 : k)) * e w) : R) = pol (monomial d (1 : k)) * e w := by
      rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, e_mul_self]
    have hcut : (e source * (ψw (ρ v) * pol (monomial d (1 : k)) * e w) * e w : R) =
        (e source * ψw (ρ v)) * (pol (monomial d (1 : k)) * e w) := by
      simp only [mul_assoc, e_mul_self]
    by_cases ht : v • w = source
    · have hleft : (e source * (ψw (ρ v) * pol (monomial d (1 : k)) * e w) * e w : R) =
          ψw (ρ v) * pol (monomial d (1 : k)) * e w := by
        rw [hcut, show (e source * ψw (ρ v) : R) = ψw (ρ v) * e w by
          rw [e_mul_ψw, (hρ v).2, ← ht, inv_smul_smul],
          mul_assoc, hepoly, ← mul_assoc]
      rw [hleft]
      rcases hw with rfl | rfl
      · have hv : v = sadj n 2 := perm_injective_at higher (ht.trans source_shift.symm)
        rw [hv, show ρ (sadj n 2) = [2] from highWord, ψw_cons, ψw_nil, mul_one]
        refine ⟨pol (monomial d (1 : k)) * e higher, ?_⟩
        change (ψ 2 * e higher) * (pol (monomial d (1 : k)) * e higher) =
          ψ 2 * pol (monomial d (1 : k)) * e higher
        rw [mul_assoc, ← mul_assoc (e higher) (pol (monomial d (1 : k))),
          (e_commute_pol _ _).eq, mul_assoc, e_mul_self, ← mul_assoc]
      · have hv : v = sadj n 2 * sadj n 1 := perm_injective_at middle
          (ht.trans (by
            change source = (sadj n 2 * sadj n 1) • middle
            rw [mul_smul, higher_shift, source_shift]))
        rw [hv, show ρ (sadj n 2 * sadj n 1) = [2,1] from middleWord, ψw_cons, ψw_cons,
          ψw_nil, mul_one]
        refine ⟨ψ 1 * pol (monomial d (1 : k)) * e middle, ?_⟩
        change (ψ 2 * e higher) * (ψ 1 * pol (monomial d (1 : k)) * e middle) =
          ψ 2 * ψ 1 * pol (monomial d (1 : k)) * e middle
        rw [mul_assoc (ψ 2), ← mul_assoc (e higher), ← mul_assoc (e higher),
          show (e higher * ψ 1 : R) = ψ 1 * e middle by
            rw [e_mul_ψ, ← higher_shift, ← mul_smul, TypeA.sadj_mul_self, one_smul]]
        simp only [mul_assoc, hepoly]
    · have h' : wordProd n (ρ v) • w ≠ source := by rw [(hρ v).2]; exact ht
      have hz : (e source * (ψw (ρ v) * pol (monomial d (1 : k)) * e w) * e w : R) = 0 := by
        calc
          _ = (e source * (ψw (ρ v) * e w)) * (pol (monomial d (1 : k)) * e w) := by
            rw [hcut]
            simp only [mul_assoc, hepoly]
          _ = _ := by
            rw [ψw_mul_e, ← mul_assoc (e source), e_mul_e, ite_eq_right (Ne.symm h'),
              zero_mul, zero_mul]
      rw [hz]
      exact Submodule.zero_mem _
  · rw [mul_assoc (e source), mul_assoc (ψw (ρ v) * pol (monomial d (1 : k))),
      e_mul_e, ite_eq_right hi, mul_zero, mul_zero]
    exact Submodule.zero_mem _

noncomputable section
open MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev ν : Multiset Unit := {()}
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun w => π (KLRAlgebra.e w)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord source))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord source))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord source) higher sameOrder
local notation "P" => rIdeal (orderedLoadingIdem Q Λ source)
local notation "K" => blockLoadingKernel Q Λ source 0 1
local notation "J" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 source) (redWord source)

/-- The red-black crossing from the higher loading into the source projective
is an element of the higher retained kernel. -/
def higherCrossing : K := by
  let c := blockLoadingRep Q Λ source (π (ψ 2 * KLRAlgebra.e higher))
  refine ⟨c, ?_⟩
  have hd : p higher ∈ J := TwoSidedIdeal.subset_span ⟨higher, sameOrder, source_lt_higher, rfl⟩
  change c.1.1 ∈ J
  rw [blockLoadingRep_val, map_mul]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hd))

theorem higherCrossing_val : (higherCrossing Q Λ).1.1.1 = π (ψ 2 * KLRAlgebra.e higher) := by
  change (blockLoadingRep Q Λ source (π (ψ 2 * KLRAlgebra.e higher))).1.1 = _
  have hx : (KLRAlgebra.e source * (ψ 2 * KLRAlgebra.e higher) : R) = ψ 2 * KLRAlgebra.e higher := by
    rw [ψ_mul_e, source_shift, ← mul_assoc, e_mul_self]
  have hE : p higher * E = p higher := by
    change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
    rfl
  rw [blockLoadingRep_val]
  change π (KLRAlgebra.e source) * π (ψ 2 * KLRAlgebra.e higher) * E = _
  rw [← map_mul, hx, map_mul, mul_assoc, hE]

/-- Left multiplication by the red-black crossing maps the higher loading projective to the kernel. -/
def higherCrossingMap : rIdeal d →ₗ[Tᵐᵒᵖ] K where
  toFun y := op y.1 • higherCrossing Q Λ
  map_add' y z := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 + z.1.1) = _ * y.1.1 + _ * z.1.1
    rw [mul_add]
  map_smul' a y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 * a.unop.1) = (_ * y.1.1) * a.unop.1
    rw [mul_assoc]

theorem higherCrossingMap_val (y : rIdeal d) :
    (higherCrossingMap Q Λ y).1.1.1 = π (ψ 2 * KLRAlgebra.e higher) * y.1.1 := by
  change (higherCrossing Q Λ).1.1.1 * y.1.1 = _
  rw [higherCrossing_val]

/-- The crossing onto the source loading generates its higher retained kernel.
This uses only the one-black reduced paths, with arbitrary red weights. -/
theorem higherCrossingMap_surjective : Function.Surjective (higherCrossingMap Q Λ) := by
  let F : rIdeal d →ₗ[Tᵐᵒᵖ] P := (K).subtype.comp (higherCrossingMap Q Λ)
  suffices h : K ≤ LinearMap.range F by
    intro x
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨y, Subtype.ext hy⟩
  rw [blockLoadingKernel_eq_span]
  apply Submodule.span_le.2
  rintro _ ⟨w, ho, hlt, z, rfl⟩
  obtain hv | hw := classify w ho hlt
  · have hp : p w = 0 := violMk_e hv
    change blockLoadingRep Q Λ source (z * p w) ∈ LinearMap.range F
    rw [hp, mul_zero]
    convert (LinearMap.range F).zero_mem using 1
    apply Subtype.ext; apply Subtype.ext
    rw [blockLoadingRep_val, mul_zero, zero_mul]
    rfl
  obtain ⟨z', rfl⟩ := (violMk_surjective.comp ofKLR_surjective : Function.Surjective π) z
  obtain ⟨y, hy⟩ := cut_factors Q Λ w hw z'
  let y' : T := ⟨E * π y * E, π y, rfl⟩
  have hidem : IsIdempotentElem d := by
    apply Subtype.ext
    exact congrArg Subtype.val (orderedLoadingIdem_idem Q Λ higher).eq
  refine ⟨rIdealProj hidem y', ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (higherCrossingMap Q Λ (rIdealProj hidem y')).1.1.1 =
    (blockLoadingRep Q Λ source (π z' * p w)).1.1
  have hE : p higher * E = p higher := by
    change (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e higher))) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left sameOrder]
    rfl
  have hp : p higher * p higher = p higher := congrArg Subtype.val hidem.eq
  rw [higherCrossingMap_val, blockLoadingRep_val]
  change π (ψ 2 * KLRAlgebra.e higher) * (p higher * (E * π y * E)) =
    p source * (π z' * p w) * E
  have hfix : π (ψ 2 * KLRAlgebra.e higher) * p higher = π (ψ 2 * KLRAlgebra.e higher) := by
    rw [map_mul, mul_assoc, hp]
  have hfix' : π (ψ 2 * KLRAlgebra.e higher) * E = π (ψ 2 * KLRAlgebra.e higher) := by
    rw [map_mul, mul_assoc, hE]
  calc
    _ = (π (ψ 2 * KLRAlgebra.e higher) * p higher * E) * π y * E := by
      simp only [mul_assoc]
    _ = π ((ψ 2 * KLRAlgebra.e higher) * y) * E := by
      rw [hfix, hfix']
      simp only [map_mul]
    _ = _ := by rw [hy, map_mul, map_mul, mul_assoc (p source)]

/-- If the crossing from the higher projective is injective, it identifies the kernel
with the one higher partial-standard layer. For positive spectator weight, injectivity
is an additional hypothesis and does not follow from the mixed bigon scalar. -/
theorem kernel_hasHigherFiltration_of_crossing_injective
    (hinj : Function.Injective (higherCrossingMap Q Λ)) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ higher 0 1 (redWord source) sameOrder)
      [()] (ModuleCat.of Tᵐᵒᵖ K) := by
  let φ := LinearEquiv.ofBijective (higherCrossingMap Q Λ)
    ⟨hinj, higherCrossingMap_surjective Q Λ⟩
  let η := blockPartialStandardAt_equiv_projective Q Λ higher 0 1 (redWord source)
    sameOrder higher_maximal
  exact ModuleFiltration.HasFiltration.single (φ.symm.trans η.symm)

end

end Categorification.Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack
