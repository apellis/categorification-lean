/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIso
import Categorification.KLR.MackeyFactor

/-!
# The Mackey subquotients are the balanced tensor products: injectivity

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18** (TeX lines 1784–1817).

For `c = |λ|` admissible, let `d` be the minimal double coset representative with `c` crossing
strands, and use the refined Mackey factorisation `w = (u₁ × u₂) · d · (Y × Y')`
(`TypeA.IsDoubleShuffle.exists_refinedFactor`, `refinedFactor_unique`) to choose reduced words
`ρ(w) = σ(u₁) (n + σ(u₂)) σ(d) σ(Y) (n'' + σ(Y'))` for the permutations `w` with `c` crossing
strands (`KLRAlgebra.mackeyRho`). The classes of the standard elements `ψ_{ρ(w)} x^u 1_s` form a
basis of `F_c / F_{c-1}` (`KLRAlgebra.subquotBasis`), on which we define, for each `λ`, a map
`KLRAlgebra.mackeyPsi : F_c / F_{c-1} → (… ⊗_{R'} …)_λ` which is a left inverse of
`mackeyMap` for `λ` and vanishes on the images of `mackeyMap` for `λ' ≠ λ`. This uses that the
balanced tensor product is spanned by the elements `(ψ_{u₁} ⊗ ψ_{u₂}) ⊗ (ψ_Y x^{v} 1_s ⊗ ψ_{Y'} x^{v'} 1_{s'})`
(`KLRAlgebra.span_genSet`; the right `R'`-module `_ν R_{ν-λ,λ} ⊗ …` is spanned by the
`ψ_{u₁} ⊗ ψ_{u₂}` over the minimal coset representatives, `mul_quadTop_one_mem_span`).

## Main results (under the hypotheses of the basis theorem: `k` a domain, `Q = P P'`)

* `KLRAlgebra.mackeyMap_injective` : `mackeyMap h q` is injective.
* `KLRAlgebra.mackeyMap_iSupIndep` : the images for the different `λ` with `|λ| = c` are
  independent; `KLRAlgebra.iSup_range_mackeyMap` : they span `F_c / F_{c-1}`.
* `KLRAlgebra.mackeySubquot_isInternal` : **KL I, Proposition 2.18**: `F_c / F_{c-1}` is the
  internal direct sum of the images of the injective bimodule maps
  `(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'} (_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''}) → F_c / F_{c-1}`,
  `|λ| = c`, which are homogeneous of degree `-λ·(ν'+λ-ν''')`
  (`KLRAlgebra.mackeyMap_mem_subquotGrading`). Refining the filtration `F_c` by any ordering of
  the `λ` with `|λ| = c` gives the paper's filtration indexed by `λ`.
* `KL1.mackeySubquot_isInternal`, `KL1.mackeyMap_injective` : the case of KL I (a simple graph,
  over `ℤ` or any integral domain).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')

/-! ### Admissible values of `|λ|` and the block sizes -/

section Adm

omit [DecidableEq I]

variable (ν ν'' ν''') in
/-- `c = |λ|` is admissible: there is a minimal double coset representative with `c` crossing
strands (`TypeA.exists_isDoubleShuffle_iff`). -/
def MackeyAdm (c : ℕ) : Prop :=
  Multiset.card ν ≤ c + Multiset.card ν'' ∧ c ≤ Multiset.card ν ∧ c ≤ Multiset.card ν'''

instance (c : ℕ) : Decidable (MackeyAdm ν ν'' ν''' c) := by
  unfold MackeyAdm; infer_instance

theorem mackeyAdm_of_quad (q : MackeyQuad ν ν' ν'' ν''') :
    MackeyAdm ν ν'' ν''' (Multiset.card q.β) := by
  obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
  refine ⟨?_, ?_, ?_⟩ <;> omega

variable {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c)

include hc in
theorem adm_hA : Multiset.card ν - c + c = Multiset.card ν := by
  have := hc.2.1; omega

include hc in
theorem adm_hAG : Multiset.card ν - c + (Multiset.card ν'' - (Multiset.card ν - c)) =
    Multiset.card ν'' := by
  have := hc.1; omega

include hc in
theorem adm_hCE : c + (Multiset.card ν''' - c) = Multiset.card ν''' := by
  have := hc.2.2; omega

include h hc in
theorem adm_hG : Multiset.card ν'' - (Multiset.card ν - c) + (Multiset.card ν''' - c) =
    Multiset.card ν' := by
  have := card_add_bot h
  have := hc.1; have := hc.2.1; have := hc.2.2
  rw [Multiset.card_add] at *
  omega

theorem card_q_α (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hq : Multiset.card q.β = c) :
    Multiset.card q.α = Multiset.card ν - c := by
  obtain ⟨e1, -, -, -⟩ := card_eqs q; omega

theorem card_q_γ (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hq : Multiset.card q.β = c) :
    Multiset.card q.γ = Multiset.card ν'' - (Multiset.card ν - c) := by
  obtain ⟨e1, -, e3, -⟩ := card_eqs q; omega

theorem card_q_δ (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hq : Multiset.card q.β = c) :
    Multiset.card q.δ = Multiset.card ν''' - c := by
  obtain ⟨-, -, -, e4⟩ := card_eqs q; omega

end Adm

/-! ### The minimal double coset representative and the refined factorisation -/

section Fac

omit [DecidableEq I]

/-- The minimal double coset representative with `c` crossing strands (`1` if `c` is not
admissible). -/
def mackeyD (c : ℕ) : Perm (Fin (Multiset.card (ν + ν'))) :=
  if hc : MackeyAdm ν ν'' ν''' c then
    Classical.choose ((exists_isDoubleShuffle_iff (Seq.card_add' ν ν') (card_add_bot h) c).2 hc)
  else 1

theorem mackeyD_spec {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) :
    IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) (mackeyD h c) ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') (mackeyD h c) = c := by
  rw [mackeyD, dif_pos hc]
  exact Classical.choose_spec ((exists_isDoubleShuffle_iff (Seq.card_add' ν ν')
    (card_add_bot h) c).2 hc)

theorem quadPerm_eq_mackeyD (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hq : Multiset.card q.β = c) : quadPerm h q = mackeyD h c := by
  have hc : MackeyAdm ν ν'' ν''' c := hq ▸ mackeyAdm_of_quad q
  exact (quadPerm_spec h q).1.eq_of_crossCount_eq _ _ (mackeyD_spec h hc).1
    (by rw [(quadPerm_spec h q).2, (mackeyD_spec h hc).2, hq])

/-- The data of the refined factorisation. -/
abbrev FacData (ν ν' ν'' ν''' : Multiset I) : Type :=
  Perm (Fin (Multiset.card ν)) × Perm (Fin (Multiset.card ν')) × Perm (Fin (Multiset.card ν'')) ×
    Perm (Fin (Multiset.card ν'''))

theorem exists_mackeyFac {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c)
    {w : Perm (Fin (Multiset.card (ν + ν')))}
    (hw : crossCount (Multiset.card ν) (Multiset.card ν'') w = c) :
    ∃ x : FacData ν ν' ν'' ν''', IsShuffle (adm_hA hc) x.1⁻¹ ∧ IsShuffle (adm_hG h hc) x.2.1⁻¹ ∧
      w = blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * mackeyD h c *
        blockPerm (card_add_bot h) x.2.2.1 x.2.2.2 ∧
      length _ w = length _ x.1 + length _ x.2.1 + length _ (mackeyD h c) +
        (length _ x.2.2.1 + length _ x.2.2.2) := by
  obtain ⟨u₁, u₂, Y, Y', h1, h2, h3, h4⟩ := (mackeyD_spec h hc).1.exists_refinedFactor
    (adm_hA hc) (adm_hG h hc) (adm_hAG hc) (adm_hCE hc) (mackeyD_spec h hc).2 w hw
  exact ⟨(u₁, u₂, Y, Y'), h1, h2, h3, h4⟩

/-- The refined Mackey factorisation `w = (u₁ × u₂) d (Y × Y')` of a permutation with `c`
crossing strands (junk otherwise). -/
def mackeyFac (c : ℕ) (w : Perm (Fin (Multiset.card (ν + ν')))) : FacData ν ν' ν'' ν''' :=
  if hw : MackeyAdm ν ν'' ν''' c ∧ crossCount (Multiset.card ν) (Multiset.card ν'') w = c then
    Classical.choose (exists_mackeyFac h hw.1 hw.2)
  else (1, 1, 1, 1)

theorem mackeyFac_spec {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c)
    {w : Perm (Fin (Multiset.card (ν + ν')))}
    (hw : crossCount (Multiset.card ν) (Multiset.card ν'') w = c) :
    IsShuffle (adm_hA hc) (mackeyFac h c w).1⁻¹ ∧ IsShuffle (adm_hG h hc) (mackeyFac h c w).2.1⁻¹ ∧
      w = blockPerm (Seq.card_add' ν ν') (mackeyFac h c w).1 (mackeyFac h c w).2.1 *
        mackeyD h c * blockPerm (card_add_bot h) (mackeyFac h c w).2.2.1 (mackeyFac h c w).2.2.2 ∧
      length _ w = length _ (mackeyFac h c w).1 + length _ (mackeyFac h c w).2.1 +
        length _ (mackeyD h c) +
        (length _ (mackeyFac h c w).2.2.1 + length _ (mackeyFac h c w).2.2.2) := by
  have hw' : MackeyAdm ν ν'' ν''' c ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') w = c := ⟨hc, hw⟩
  rw [mackeyFac, dif_pos hw']
  exact Classical.choose_spec (exists_mackeyFac h hw'.1 hw'.2)

theorem mackeyFac_eq {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) {u₁ : Perm (Fin (Multiset.card ν))}
    {u₂ : Perm (Fin (Multiset.card ν'))} {Y : Perm (Fin (Multiset.card ν''))}
    {Y' : Perm (Fin (Multiset.card ν'''))} (hu₁ : IsShuffle (adm_hA hc) u₁⁻¹)
    (hu₂ : IsShuffle (adm_hG h hc) u₂⁻¹) :
    mackeyFac h c (blockPerm (Seq.card_add' ν ν') u₁ u₂ * mackeyD h c *
      blockPerm (card_add_bot h) Y Y') = (u₁, u₂, Y, Y') := by
  have hw : crossCount (Multiset.card ν) (Multiset.card ν'') (blockPerm (Seq.card_add' ν ν') u₁ u₂ *
      mackeyD h c * blockPerm (card_add_bot h) Y Y') = c := by
    rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul, (mackeyD_spec h hc).2]
  obtain ⟨h1, h2, h3, -⟩ := mackeyFac_spec h hc hw
  obtain ⟨e1, e2, e3, e4⟩ := (mackeyD_spec h hc).1.refinedFactor_unique (adm_hA hc) (adm_hG h hc)
    (adm_hAG hc) (adm_hCE hc) (mackeyD_spec h hc).2 h1 h2 hu₁ hu₂ h3.symm
  ext1 <;> [exact e1; ext1 <;> [exact e2; ext1 <;> [exact e3; exact e4]]]

end Fac

/-! ### Mackey-adapted reduced words -/

section Rho

omit [DecidableEq I]

/-- **Mackey-adapted reduced words**: for `w` with `c` crossing strands,
`ρ(w) = σ(u₁) (n + σ(u₂)) σ(d) σ(Y) (n'' + σ(Y'))` where `w = (u₁ × u₂) d (Y × Y')` is the refined
factorisation; `σ = canWord` otherwise. -/
def mackeyRho (c : ℕ) (w : Perm (Fin (Multiset.card (ν + ν')))) : List ℕ :=
  if MackeyAdm ν ν'' ν''' c ∧ crossCount (Multiset.card ν) (Multiset.card ν'') w = c then
    canWord _ (mackeyFac h c w).1 ++ shiftWord (Multiset.card ν) (canWord _ (mackeyFac h c w).2.1) ++
      canWord _ (mackeyD h c) ++
      (canWord _ (mackeyFac h c w).2.2.1 ++
        shiftWord (Multiset.card ν'') (canWord _ (mackeyFac h c w).2.2.2))
  else canWord _ w

theorem mackeyRho_spec (c : ℕ) (w : Perm (Fin (Multiset.card (ν + ν')))) :
    IsReduced (Multiset.card (ν + ν')) (mackeyRho h c w) ∧
      wordProd (Multiset.card (ν + ν')) (mackeyRho h c w) = w := by
  unfold mackeyRho
  split_ifs with hw
  · obtain ⟨-, -, hwf, hl⟩ := mackeyFac_spec h hw.1 hw.2
    have hJ := Seq.card_add' ν ν'
    have hK := card_add_bot h
    have hv : ValidWord (Multiset.card (ν + ν')) (canWord _ (mackeyFac h c w).1 ++
        shiftWord (Multiset.card ν) (canWord _ (mackeyFac h c w).2.1) ++ canWord _ (mackeyD h c) ++
        (canWord _ (mackeyFac h c w).2.2.1 ++
          shiftWord (Multiset.card ν'') (canWord _ (mackeyFac h c w).2.2.2))) := by
      simp only [validWord_append]
      refine ⟨⟨⟨(validWord_canWord _ _).of_le (by omega), (validWord_canWord _ _).shiftWord hJ⟩,
        validWord_canWord _ _⟩, (validWord_canWord _ _).of_le (by omega),
        (validWord_canWord _ _).shiftWord hK⟩
    have hprod : wordProd (Multiset.card (ν + ν')) (canWord _ (mackeyFac h c w).1 ++
        shiftWord (Multiset.card ν) (canWord _ (mackeyFac h c w).2.1) ++ canWord _ (mackeyD h c) ++
        (canWord _ (mackeyFac h c w).2.2.1 ++
          shiftWord (Multiset.card ν'') (canWord _ (mackeyFac h c w).2.2.2))) = w := by
      simp only [wordProd_append]
      rw [← wordProd_append, wordProd_append_shiftWord hJ (validWord_canWord _ _)
          (validWord_canWord _ _), ← wordProd_append,
        wordProd_append_shiftWord hK (validWord_canWord _ _) (validWord_canWord _ _),
        wordProd_canWord, wordProd_canWord, wordProd_canWord, wordProd_canWord, wordProd_canWord,
        ← hwf]
    refine ⟨(isReduced_iff_length_le hv).2 ?_, hprod⟩
    rw [hprod, hl]
    simp only [List.length_append, length_shiftWord, length_canWord]
    omega
  · exact ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩

theorem mackeyRho_facPerm {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) {u₁ : Perm (Fin (Multiset.card ν))}
    {u₂ : Perm (Fin (Multiset.card ν'))} {Y : Perm (Fin (Multiset.card ν''))}
    {Y' : Perm (Fin (Multiset.card ν'''))} (hu₁ : IsShuffle (adm_hA hc) u₁⁻¹)
    (hu₂ : IsShuffle (adm_hG h hc) u₂⁻¹) :
    mackeyRho h c (blockPerm (Seq.card_add' ν ν') u₁ u₂ * mackeyD h c *
      blockPerm (card_add_bot h) Y Y') =
      canWord _ u₁ ++ shiftWord (Multiset.card ν) (canWord _ u₂) ++ canWord _ (mackeyD h c) ++
        (canWord _ Y ++ shiftWord (Multiset.card ν'') (canWord _ Y')) := by
  have hw : crossCount (Multiset.card ν) (Multiset.card ν'') (blockPerm (Seq.card_add' ν ν') u₁ u₂ *
      mackeyD h c * blockPerm (card_add_bot h) Y Y') = c := by
    rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul, (mackeyD_spec h hc).2]
  unfold mackeyRho
  rw [if_pos ⟨hc, hw⟩, mackeyFac_eq h hc hu₁ hu₂]

end Rho

/-! ### The Mackey-adapted basis of `F_c / F_{c-1}` -/

section Basis

/-- The indices of the basis of `F_{c-1}`. -/
def lowerIdx : ℕ → Set (StdIdx (ν + ν'))
  | 0 => ∅
  | c + 1 => mackeyIdx h c

theorem lowerIdx_subset (c : ℕ) : lowerIdx h c ⊆ mackeyIdx h c := by
  cases c with
  | zero => exact Set.empty_subset _
  | succ c => exact mackeyIdx_mono h (Nat.le_succ c)

theorem mackeyLowerBimod_eq_span (ρ : Perm (Fin (Multiset.card (ν + ν'))) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card (ν + ν')) (ρ w) ∧
      wordProd (Multiset.card (ν + ν')) (ρ w) = w) (c : ℕ) :
    mackeyLowerBimod Q h c = Submodule.span k (stdElt ρ '' lowerIdx h c) := by
  cases c with
  | zero => rw [mackeyLowerBimod_zero, lowerIdx, Set.image_empty, Submodule.span_empty]
  | succ c => rw [mackeyLowerBimod_succ, lowerIdx, mackeyBimodFilt_eq_span h ρ hρ]

theorem mem_mackeyIdx_diff_lower {c : ℕ} {b : StdIdx (ν + ν')} :
    b ∈ mackeyIdx h c \ lowerIdx h c ↔ b.1 ∈ botSet h ∧ b.2.1 • b.1 ∈ concatSet ν ν' ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') b.2.1 = c := by
  cases c with
  | zero =>
    simp only [lowerIdx, Set.diff_empty, mackeyIdx, Set.mem_setOf_eq, Nat.le_zero]
  | succ c => exact mem_mackeyIdx_diff h

theorem mem_botSet_iff {s : Seq (ν + ν')} :
    s ∈ botSet h ↔ ∃ (s₃ : Seq ν'') (s₄ : Seq ν'''), seqCast h (s₃.append s₄) = s := by
  simp only [botSet, Finset.mem_image, mem_concatSet]
  constructor
  · rintro ⟨_, ⟨s₃, s₄, rfl⟩, rfl⟩; exact ⟨s₃, s₄, rfl⟩
  · rintro ⟨s₃, s₄, rfl⟩; exact ⟨_, ⟨s₃, s₄, rfl⟩, rfl⟩

theorem stdElt_mem_mackeyBimodFilt {c : ℕ} (b : ↥(mackeyIdx h c \ lowerIdx h c)) :
    (stdElt (mackeyRho h c) b.1 : KLRAlgebra k Q (ν + ν')) ∈ mackeyBimodFilt Q h c := by
  rw [mackeyBimodFilt_eq_span h _ (mackeyRho_spec h c) c]
  exact Submodule.subset_span ⟨b.1, b.2.1, rfl⟩

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (Q) in
/-- **The Mackey-adapted basis of `F_c / F_{c-1}`**: the classes of the standard elements
`ψ_{ρ(w)} x^u 1_s` of `_{ν,ν'}R_{ν'',ν'''}` with exactly `c` crossing strands, for the
Mackey-adapted reduced words `ρ = mackeyRho h c`. -/
def subquotBasis (c : ℕ) : Basis ↥(mackeyIdx h c \ lowerIdx h c) k (MackeySubquot Q h c) :=
  quotBasis (linearIndependent_stdElt hPQ hP (mackeyRho h c) (mackeyRho_spec h c))
    (lowerIdx_subset h c) _ _ (mackeyBimodFilt_eq_span h _ (mackeyRho_spec h c) c)
    (mackeyLowerBimod_eq_span h _ (mackeyRho_spec h c) c)

theorem subquotBasis_apply {c : ℕ} (b : ↥(mackeyIdx h c \ lowerIdx h c)) :
    subquotBasis Q h hPQ hP c b =
      subquotOf h (stdElt (mackeyRho h c) b.1) (stdElt_mem_mackeyBimodFilt h b) :=
  quotBasis_apply' _ _ _ _ _ _ b

end Basis

/-! ### Transport of exponents and splitting of sequences -/

section Split

omit [DecidableEq I] in
/-- Exponent vectors along `ν'' + ν''' = ν + ν'`. -/
def uncastExp (E : Fin (Multiset.card (ν'' + ν''')) →₀ ℕ) : Fin (Multiset.card (ν + ν')) →₀ ℕ :=
  Finsupp.equivMapDomain (finCongr (congrArg Multiset.card h)) E

omit [DecidableEq I] in
/-- Split an exponent vector of `ν + ν'` along `ν'' + ν'''`. -/
def expSplit (u : Fin (Multiset.card (ν + ν')) →₀ ℕ) :
    (Fin (Multiset.card ν'') →₀ ℕ) × (Fin (Multiset.card ν''') →₀ ℕ) :=
  (expEquiv ν'' ν''').symm (Finsupp.equivMapDomain (finCongr (congrArg Multiset.card h)).symm u)

omit [DecidableEq I] in
theorem expSplit_uncastExp (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    expSplit h (uncastExp h (expEquiv ν'' ν''' (v₃, v₄))) = (v₃, v₄) := by
  rw [expSplit, uncastExp, ← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm,
    Finsupp.equivMapDomain_refl, Equiv.symm_apply_apply]

theorem castAlg_pol_monomial_eq (E : Fin (Multiset.card (ν'' + ν''')) →₀ ℕ) :
    castAlg Q h (pol (monomial E 1)) = pol (monomial (uncastExp h E) 1) := by
  rw [castAlg_pol_eq, rename_monomial, uncastExp, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

/-- The splitting `s = s₃ s₄` of a bottom sequence. -/
def botSplit (s : Seq (ν + ν')) (hs : s ∈ botSet h) : Seq ν'' × Seq ν''' :=
  (Classical.choose ((mem_botSet_iff h).1 hs),
    Classical.choose (Classical.choose_spec ((mem_botSet_iff h).1 hs)))

theorem botSplit_eq (s₃ : Seq ν'') (s₄ : Seq ν''') (hs : seqCast h (s₃.append s₄) ∈ botSet h) :
    botSplit h _ hs = (s₃, s₄) := by
  have := Classical.choose_spec (Classical.choose_spec ((mem_botSet_iff h).1 hs))
  obtain ⟨h1, h2⟩ := Seq.append_inj.1 (seqCast_injective h this)
  exact Prod.ext h1 h2

omit [DecidableEq I] in
theorem seqCast_blockPerm_smul {μ : Multiset I} (hμ : ν'' + ν''' = μ)
    (Y : Perm (Fin (Multiset.card ν''))) (Y' : Perm (Fin (Multiset.card ν''')))
    (hK : Multiset.card ν'' + Multiset.card ν''' = Multiset.card μ) (s₃ : Seq ν'') (s₄ : Seq ν''') :
    blockPerm hK Y Y' • seqCast hμ (s₃.append s₄) = seqCast hμ ((Y • s₃).append (Y' • s₄)) := by
  subst hμ
  exact Seq.blockPerm_smul_append Y Y' s₃ s₄

end Split

/-! ### The generators of the balanced tensor products -/

section Gen

variable (q : MackeyQuad ν ν' ν'' ν''')

/-- The sequences `i_α i_γ` of the first bottom block. -/
def quadSet₃ : Finset (Seq ν'') := (concatSet q.α q.γ).image (seqCast q.h₃)

/-- The sequences `i_β i_δ` of the second bottom block. -/
def quadSet₄ : Finset (Seq ν''') := (concatSet q.β q.δ).image (seqCast q.h₄)

theorem quadBot_one_eq : quadBot (Q := Q) q 1 = eSum Q (quadSet₃ q) ⊗ₜ eSum Q (quadSet₄ q) := by
  rw [quadBot_one, oneConcat, oneConcat, castAlg_eSum, castAlg_eSum]; rfl

omit [DecidableEq I] in
/-- The condition `Y • s₃ ∈ i_α i_γ`, `Y' • s₄ ∈ i_β i_δ`: the diagram `ψ_Y x^v 1_{s₃} ⊗ ψ_{Y'} x^{v'} 1_{s₄}`
lies in `(1_{α,γ} ⊗ 1_{β,δ}) (R(ν'') ⊗ R(ν'''))`. -/
def QuadCond (s₃ : Seq ν'') (s₄ : Seq ν''') (Y : Perm (Fin (Multiset.card ν'')))
    (Y' : Perm (Fin (Multiset.card ν'''))) : Prop :=
  Y • s₃ ∈ quadSet₃ q ∧ Y' • s₄ ∈ quadSet₄ q

instance (s₃ : Seq ν'') (s₄ : Seq ν''') (Y : Perm (Fin (Multiset.card ν'')))
    (Y' : Perm (Fin (Multiset.card ν'''))) : Decidable (QuadCond q s₃ s₄ Y Y') := by
  unfold QuadCond; infer_instance

variable (Q) in
/-- `(ψ_{u₁} ⊗ ψ_{u₂}) (1_{α,β} ⊗ 1_{γ,δ}) ∈ MackeyTop`. -/
def topElt (u₁ : Perm (Fin (Multiset.card ν))) (u₂ : Perm (Fin (Multiset.card ν'))) :
    MackeyTop Q q :=
  ⟨((ψw (canWord _ u₁) : KLRAlgebra k Q ν) ⊗ₜ (ψw (canWord _ u₂) : KLRAlgebra k Q ν')) *
      quadTop q 1, by rw [Graded.mem_leftIdeal, mul_assoc, quadTop_mul_one]⟩

theorem botElt_mem {s₃ : Seq ν''} {s₄ : Seq ν'''} {Y : Perm (Fin (Multiset.card ν''))}
    {Y' : Perm (Fin (Multiset.card ν'''))} (hb : QuadCond q s₃ s₄ Y Y')
    (v₃ : Fin (Multiset.card ν'') →₀ ℕ) (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    ((stdElt (canWord _) (s₃, Y, v₃) : KLRAlgebra k Q ν'') ⊗ₜ
      (stdElt (canWord _) (s₄, Y', v₄) : KLRAlgebra k Q ν''')) ∈ quadBotSub Q q := by
  rw [mem_quadBotSub, quadBot_one_eq, Algebra.TensorProduct.tmul_mul_tmul, eSum_mul_stdElt,
    eSum_mul_stdElt]
  simp only [wordProd_canWord]
  rw [if_pos hb.1, if_pos hb.2]

variable (Q) in
/-- **The generators of `MackeyX`**: `(ψ_{u₁} ⊗ ψ_{u₂}) ⊗ (ψ_Y x^{v₃} 1_{s₃} ⊗ ψ_{Y'} x^{v₄} 1_{s₄})`
(`0` unless `QuadCond`). -/
def gen (s₃ : Seq ν'') (s₄ : Seq ν''') (x : FacData ν ν' ν'' ν''')
    (v₃ : Fin (Multiset.card ν'') →₀ ℕ) (v₄ : Fin (Multiset.card ν''') →₀ ℕ) : MackeyX Q q :=
  if hb : QuadCond q s₃ s₄ x.2.2.1 x.2.2.2 then
    BalancedTensor.tmul (topElt Q q x.1 x.2.1) ⟨_, botElt_mem q hb v₃ v₄⟩
  else 0

omit [DecidableEq I] in
/-- The sub-quadruple of a sequence is unique. -/
theorem quadCond_unique {q q' : MackeyQuad ν ν' ν'' ν'''} {s₃ : Seq ν''} {s₄ : Seq ν'''}
    {Y : Perm (Fin (Multiset.card ν''))} {Y' : Perm (Fin (Multiset.card ν'''))}
    [DecidableEq I] (hb : QuadCond q s₃ s₄ Y Y') (hb' : QuadCond q' s₃ s₄ Y Y')
    (hqq : Multiset.card q.β = Multiset.card q'.β) : q = q' := by
  obtain ⟨-, hb⟩ := hb
  obtain ⟨-, hb'⟩ := hb'
  simp only [quadSet₄, Finset.mem_image, mem_concatSet] at hb hb'
  obtain ⟨_, ⟨i₂, i₄, rfl⟩, he⟩ := hb
  obtain ⟨_, ⟨i₂', i₄', rfl⟩, he'⟩ := hb'
  rw [← he'] at he
  refine MackeyQuad.ext_of_β (seq_weight_eq i₂ i₂' hqq fun t => ?_)
  have := congrArg (fun s : Seq ν''' => s.1 ⟨t.val, by
    have := t.2; obtain ⟨-, -, -, e4⟩ := card_eqs q; omega⟩) he
  simp only at this
  rw [seqCast_append_apply_lt _ _ _ _ (by simp), seqCast_append_apply_lt _ _ _ _ (by
    simp; omega)] at this
  exact this.trans (i₂'.apply_congr (by simp))

end Gen

/-! ### The inverse maps -/

section Psi

omit [DecidableEq I] in
theorem crossCount_facPerm {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) (x : FacData ν ν' ν'' ν''') :
    crossCount (Multiset.card ν) (Multiset.card ν'')
      (blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * mackeyD h c *
        blockPerm (card_add_bot h) x.2.2.1 x.2.2.2) = c := by
  rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul, (mackeyD_spec h hc).2]

variable (q : MackeyQuad ν ν' ν'' ν''')

theorem mem_idx_of_quadCond {c : ℕ} (hq : Multiset.card q.β = c) {s₃ : Seq ν''} {s₄ : Seq ν'''}
    {x : FacData ν ν' ν'' ν'''} (hb : QuadCond q s₃ s₄ x.2.2.1 x.2.2.2)
    (E : Fin (Multiset.card (ν + ν')) →₀ ℕ) :
    ((seqCast h (s₃.append s₄), blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * mackeyD h c *
        blockPerm (card_add_bot h) x.2.2.1 x.2.2.2, E) : StdIdx (ν + ν')) ∈
      mackeyIdx h c \ lowerIdx h c := by
  have hc : MackeyAdm ν ν'' ν''' c := hq ▸ mackeyAdm_of_quad q
  rw [mem_mackeyIdx_diff_lower]
  refine ⟨(mem_botSet_iff h).2 ⟨s₃, s₄, rfl⟩, ?_, crossCount_facPerm h hc x⟩
  obtain ⟨hb₃, hb₄⟩ := hb
  simp only [quadSet₃, quadSet₄, Finset.mem_image, mem_concatSet] at hb₃ hb₄
  obtain ⟨_, ⟨i₁, i₃, rfl⟩, e₃⟩ := hb₃
  obtain ⟨_, ⟨i₂, i₄, rfl⟩, e₄⟩ := hb₄
  simp only
  rw [mul_smul, mul_smul, seqCast_blockPerm_smul h, ← e₃, ← e₄, ← quadPerm_eq_mackeyD h q hq,
    quadPerm_smul, Seq.blockPerm_smul_append]
  exact append_mem_concatSet _ _

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (Q) in
/-- The value of the inverse map on a basis element. -/
def psiVal (c : ℕ) (b : ↥(mackeyIdx h c \ lowerIdx h c)) : MackeyX Q q :=
  gen Q q (botSplit h b.1.1 ((mem_mackeyIdx_diff_lower h).1 b.2).1).1
    (botSplit h b.1.1 ((mem_mackeyIdx_diff_lower h).1 b.2).1).2 (mackeyFac h c b.1.2.1)
    (expSplit h b.1.2.2).1 (expSplit h b.1.2.2).2

variable (Q) in
/-- **The projection `F_c / F_{c-1} → (… ⊗_{R'} …)` onto the summand of `λ = β`**, defined on the
Mackey-adapted basis. -/
def mackeyPsi (c : ℕ) : MackeySubquot Q h c →ₗ[k] MackeyX Q q :=
  (subquotBasis Q h hPQ hP c).constr k (psiVal Q h q c)

theorem mackeyPsi_basis {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) {s₃ : Seq ν''} {s₄ : Seq ν'''}
    {x : FacData ν ν' ν'' ν'''} (hx₁ : IsShuffle (adm_hA hc) x.1⁻¹)
    (hx₂ : IsShuffle (adm_hG h hc) x.2.1⁻¹) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ)
    (hmem : ((seqCast h (s₃.append s₄), blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * mackeyD h c *
        blockPerm (card_add_bot h) x.2.2.1 x.2.2.2, uncastExp h (expEquiv ν'' ν''' (v₃, v₄))) :
        StdIdx (ν + ν')) ∈ mackeyIdx h c \ lowerIdx h c) :
    mackeyPsi Q h q hPQ hP c (subquotBasis Q h hPQ hP c ⟨_, hmem⟩) = gen Q q s₃ s₄ x v₃ v₄ := by
  rw [mackeyPsi, Basis.constr_basis, psiVal]
  dsimp only
  obtain ⟨u₁, u₂, Y, Y'⟩ := x
  rw [botSplit_eq, mackeyFac_eq h hc hx₁ hx₂, expSplit_uncastExp]

end Psi

/-! ### `mackeyMap` on the generators -/

section MapGen

variable (q : MackeyQuad ν ν' ν'' ν''') [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

omit [IsDomain k] in
/-- `ι(ψ_{u₁} ⊗ ψ_{u₂}) ψ_d ι''(ψ_Y x^{v₃} 1_{s₃} ⊗ ψ_{Y'} x^{v₄} 1_{s₄})` is the standard element
`ψ_{ρ(w)} x^v 1_s` for the Mackey-adapted word of `w = (u₁ × u₂) d (Y × Y')`. -/
theorem mackeyRep_gen {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) (hq : Multiset.card q.β = c)
    {s₃ : Seq ν''} {s₄ : Seq ν'''} {x : FacData ν ν' ν'' ν'''}
    (hb : QuadCond q s₃ s₄ x.2.2.1 x.2.2.2) (hx₁ : IsShuffle (adm_hA hc) x.1⁻¹)
    (hx₂ : IsShuffle (adm_hG h hc) x.2.1⁻¹) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    concat Q ν ν' (topElt Q q x.1 x.2.1 : TensorKLR Q ν ν') *
        ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) *
        botConcat Q h ((stdElt (canWord _) (s₃, x.2.2.1, v₃) : KLRAlgebra k Q ν'') ⊗ₜ
          (stdElt (canWord _) (s₄, x.2.2.2, v₄) : KLRAlgebra k Q ν''')) =
      stdElt (mackeyRho h c) (seqCast h (s₃.append s₄),
        blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * mackeyD h c *
          blockPerm (card_add_bot h) x.2.2.1 x.2.2.2, uncastExp h (expEquiv ν'' ν''' (v₃, v₄))) := by
  obtain ⟨u₁, u₂, Y, Y'⟩ := x
  have hz := botElt_mem (Q := Q) q hb v₃ v₄
  rw [mem_quadBotSub] at hz
  show concat Q ν ν' (((ψw (canWord _ u₁) : KLRAlgebra k Q ν) ⊗ₜ
      (ψw (canWord _ u₂) : KLRAlgebra k Q ν')) * quadTop q 1) * _ * _ = _
  rw [concat_mul, concat_ψw_tmul_ψw (validWord_canWord _ _) (validWord_canWord _ _),
    mul_assoc (ψw _) (oneConcat Q ν ν'), oneConcat_mul_concat, mul_assoc (ψw _),
    concat_quadTop_one_mul_ψD, mul_assoc (ψw _), mul_assoc _ (botConcat Q h (quadBot q 1)),
    ← botConcat_mul, hz]
  simp only [stdElt]
  rw [botConcat_apply, concat_ψw_pol_e (validWord_canWord _ _) (validWord_canWord _ _),
    map_mul (castAlg Q h), map_mul (castAlg Q h), castAlg_ψw, castAlg_e, ← monomial_expEquiv,
    castAlg_pol_monomial_eq, mackeyRho_facPerm h hc hx₁ hx₂, quadPerm_eq_mackeyD h q hq]
  simp only [ψw_append, mul_assoc]

theorem mackeyMap_gen {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) (hq : Multiset.card q.β = c)
    {s₃ : Seq ν''} {s₄ : Seq ν'''} {x : FacData ν ν' ν'' ν'''}
    (hb : QuadCond q s₃ s₄ x.2.2.1 x.2.2.2) (hx₁ : IsShuffle (adm_hA hc) x.1⁻¹)
    (hx₂ : IsShuffle (adm_hG h hc) x.2.1⁻¹) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    mackeyMap h q hq (gen Q q s₃ s₄ x v₃ v₄) = subquotBasis Q h hPQ hP c
      ⟨_, mem_idx_of_quadCond h q hq hb (uncastExp h (expEquiv ν'' ν''' (v₃, v₄)))⟩ := by
  rw [gen, dif_pos hb, mackeyMap_tmul, subquotBasis_apply]
  exact subquotOf_congr h (mackeyRep_gen h q hc hq hb hx₁ hx₂ v₃ v₄) _ _

theorem mackeyPsi_mackeyMap_gen {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) (hq : Multiset.card q.β = c)
    {s₃ : Seq ν''} {s₄ : Seq ν'''} {x : FacData ν ν' ν'' ν'''}
    (hb : QuadCond q s₃ s₄ x.2.2.1 x.2.2.2) (hx₁ : IsShuffle (adm_hA hc) x.1⁻¹)
    (hx₂ : IsShuffle (adm_hG h hc) x.2.1⁻¹) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    mackeyPsi Q h q hPQ hP c (mackeyMap h q hq (gen Q q s₃ s₄ x v₃ v₄)) = gen Q q s₃ s₄ x v₃ v₄ := by
  rw [mackeyMap_gen h q hPQ hP hc hq hb hx₁ hx₂, mackeyPsi_basis h q hPQ hP hc hx₁ hx₂]

theorem mackeyPsi_mackeyMap_gen_ne {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c)
    (hq : Multiset.card q.β = c) {q' : MackeyQuad ν ν' ν'' ν'''} (hq' : Multiset.card q'.β = c)
    (hne : q ≠ q') {s₃ : Seq ν''} {s₄ : Seq ν'''} {x : FacData ν ν' ν'' ν'''}
    (hb : QuadCond q' s₃ s₄ x.2.2.1 x.2.2.2) (hx₁ : IsShuffle (adm_hA hc) x.1⁻¹)
    (hx₂ : IsShuffle (adm_hG h hc) x.2.1⁻¹) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ) :
    mackeyPsi Q h q hPQ hP c (mackeyMap h q' hq' (gen Q q' s₃ s₄ x v₃ v₄)) = 0 := by
  rw [mackeyMap_gen h q' hPQ hP hc hq' hb hx₁ hx₂, mackeyPsi_basis h q hPQ hP hc hx₁ hx₂, gen,
    dif_neg]
  intro hb'
  exact hne (quadCond_unique hb' hb (hq.trans hq'.symm))

end MapGen

/-! ### Spanning sets -/

section SpanStd

variable {μ₁ μ₂ : Multiset I}

theorem mem_span_std (ρ : Perm (Fin (Multiset.card μ₁)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card μ₁) (ρ w) ∧ wordProd (Multiset.card μ₁) (ρ w) = w)
    (a : KLRAlgebra k Q μ₁) : a ∈ Submodule.span k (Set.range (stdElt (Q := Q) ρ)) := by
  have h := span_eq_top' (k := k) (Q := Q) (ν := μ₁) ρ hρ
  have ha : a ∈ Submodule.span k {r : KLRAlgebra k Q μ₁ | ∃ (w : Perm (Fin (Multiset.card μ₁)))
      (u : Fin (Multiset.card μ₁) →₀ ℕ) (i : Seq μ₁),
      ψw (ρ w) * pol (monomial u 1) * e i = r} := by rw [h]; trivial
  refine Submodule.span_mono ?_ ha
  rintro _ ⟨w, u, i, rfl⟩
  exact ⟨(i, w, u), rfl⟩

/-- A `k`-linear map out of `R(μ₁) ⊗ R(μ₂)` lands in `F` as soon as the images of the tensors of
standard elements do. -/
theorem tensor_mem_of_std {M : Type*} [AddCommGroup M] [Module k M]
    (Φ : KLRAlgebra k Q μ₁ ⊗[k] KLRAlgebra k Q μ₂ →ₗ[k] M) (F : Submodule k M)
    (ρ : Perm (Fin (Multiset.card μ₁)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card μ₁) (ρ w) ∧ wordProd (Multiset.card μ₁) (ρ w) = w)
    (ρ' : Perm (Fin (Multiset.card μ₂)) → List ℕ)
    (hρ' : ∀ w, IsReduced (Multiset.card μ₂) (ρ' w) ∧ wordProd (Multiset.card μ₂) (ρ' w) = w)
    (hg : ∀ b b', Φ (stdElt ρ b ⊗ₜ stdElt ρ' b') ∈ F)
    (t : KLRAlgebra k Q μ₁ ⊗[k] KLRAlgebra k Q μ₂) : Φ t ∈ F := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add s t hs ht => rw [map_add]; exact add_mem hs ht
  | tmul a b =>
    induction mem_span_std (Q := Q) ρ hρ a using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨β, rfl⟩ := hx
      induction mem_span_std (Q := Q) ρ' hρ' b using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨β', rfl⟩ := hy
        exact hg β β'
      | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add]; exact add_mem hy hz
      | smul c y _ hy => rw [TensorProduct.tmul_smul, map_smul]; exact F.smul_mem c hy
    | zero => rw [TensorProduct.zero_tmul, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul, map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [← TensorProduct.smul_tmul', map_smul]; exact F.smul_mem c hx

end SpanStd

section BotSpan

variable (q : MackeyQuad ν ν' ν'' ν''')

variable (Q) in
/-- The generators `ψ_Y x^{v₃} 1_{s₃} ⊗ ψ_{Y'} x^{v₄} 1_{s₄}` of `MackeyBot`. -/
def botGens : Set (TensorKLR Q ν'' ν''') :=
  {z | ∃ (s₃ : Seq ν'') (s₄ : Seq ν''') (Y : Perm (Fin (Multiset.card ν'')))
    (Y' : Perm (Fin (Multiset.card ν'''))) (v₃ : Fin (Multiset.card ν'') →₀ ℕ)
    (v₄ : Fin (Multiset.card ν''') →₀ ℕ), QuadCond q s₃ s₄ Y Y' ∧
      (stdElt (canWord _) (s₃, Y, v₃) : KLRAlgebra k Q ν'') ⊗ₜ
        (stdElt (canWord _) (s₄, Y', v₄) : KLRAlgebra k Q ν''') = z}

theorem span_botGens_le : Submodule.span k (botGens Q q) ≤ quadBotSub Q q := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨s₃, s₄, Y, Y', v₃, v₄, hb, rfl⟩
  exact botElt_mem q hb v₃ v₄

theorem quadBot_one_mul_mem_span (z : TensorKLR Q ν'' ν''') :
    quadBot q 1 * z ∈ Submodule.span k (botGens Q q) := by
  refine tensor_mem_of_std (LinearMap.mulLeft k (quadBot q 1)) _ (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) (fun ⟨s₃, Y, v₃⟩ ⟨s₄, Y', v₄⟩ => ?_) z
  rw [LinearMap.mulLeft_apply, quadBot_one_eq, Algebra.TensorProduct.tmul_mul_tmul,
    eSum_mul_stdElt, eSum_mul_stdElt]
  simp only [wordProd_canWord]
  by_cases h₃ : Y • s₃ ∈ quadSet₃ q
  · by_cases h₄ : Y' • s₄ ∈ quadSet₄ q
    · rw [if_pos h₃, if_pos h₄]
      exact Submodule.subset_span ⟨s₃, s₄, Y, Y', v₃, v₄, ⟨h₃, h₄⟩, rfl⟩
    · rw [if_neg h₄, TensorProduct.tmul_zero]; exact zero_mem _
  · rw [if_neg h₃, TensorProduct.zero_tmul]; exact zero_mem _

theorem mem_span_botGens (b : MackeyBot Q q) :
    (b : TensorKLR Q ν'' ν''') ∈ Submodule.span k (botGens Q q) := by
  rw [← b.2]
  exact quadBot_one_mul_mem_span q _

end BotSpan

section TopSpan

omit [DecidableEq I] in
/-- Exponent vectors along an equality of weights. -/
def castExp {μ₁ μ₂ : Multiset I} (hμ : μ₁ = μ₂) (E : Fin (Multiset.card μ₁) →₀ ℕ) :
    Fin (Multiset.card μ₂) →₀ ℕ :=
  Finsupp.equivMapDomain (finCongr (congrArg Multiset.card hμ)) E

omit [DecidableEq I] in
@[simp] theorem castExp_rfl {μ₁ : Multiset I} (E : Fin (Multiset.card μ₁) →₀ ℕ) :
    castExp rfl E = E := by
  ext x; simp [castExp, Finsupp.equivMapDomain_apply]

omit [DecidableEq I] in
theorem castExp_castExp_symm {μ₁ μ₂ : Multiset I} (hμ : μ₁ = μ₂) (E : Fin (Multiset.card μ₂) →₀ ℕ) :
    castExp hμ (castExp hμ.symm E) = E := by
  subst hμ; simp

theorem castAlg_pol_monomial_eq' {μ₁ μ₂ : Multiset I} (hμ : μ₁ = μ₂)
    (E : Fin (Multiset.card μ₁) →₀ ℕ) :
    castAlg Q hμ (pol (monomial E 1)) = pol (monomial (castExp hμ E) 1) := by
  subst hμ; rw [castExp_rfl]; rfl

/-- **Right freeness, spanning half**: `x · 1_{α,β}` for a standard element `x` of `R(μ)` (for the
right parabolic words `σ(u) σ(y₁) (a + σ(y₂))`) is `0` or `ψ_u · ι_{α,β}(z)`. -/
theorem stdElt_rightWord_mul {α β μ : Multiset I} (hμ : α + β = μ) {a b : ℕ}
    (hab : a + b = Multiset.card μ) (ha : Multiset.card α = a)
    (w : Perm (Fin (Multiset.card μ))) (s : Seq μ) (p : Fin (Multiset.card μ) →₀ ℕ) :
    (stdElt (rightWord hab) (s, w, p) : KLRAlgebra k Q μ) * castAlg Q hμ (oneConcat Q α β) = 0 ∨
      ∃ z : TensorKLR Q α β,
        (stdElt (rightWord hab) (s, w, p) : KLRAlgebra k Q μ) * castAlg Q hμ (oneConcat Q α β) =
          ψw (canWord _ (rightFac hab w).1) * castAlg Q hμ (concat Q α β z) := by
  rw [oneConcat, castAlg_eSum, stdElt_mul_eSum]
  split_ifs with hs
  · right
    obtain ⟨_, hs', rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨i₁, i₂, rfl⟩ := mem_concatSet.1 hs'
    have hcard := congrArg Multiset.card hμ
    rw [Multiset.card_add] at hcard
    have hb : Multiset.card β = b := by omega
    set y := rightFac hab w
    set P := (expEquiv α β).symm (castExp hμ.symm p)
    refine ⟨((ψw (canWord a y.2.1) * pol (monomial P.1 1) * e i₁ : KLRAlgebra k Q α) ⊗ₜ
      (ψw (canWord b y.2.2) * pol (monomial P.2 1) * e i₂ : KLRAlgebra k Q β)), ?_⟩
    have hv1 : ValidWord (Multiset.card α) (canWord a y.2.1) :=
      (validWord_canWord _ _).of_le (by omega)
    have hv2 : ValidWord (Multiset.card β) (canWord b y.2.2) :=
      (validWord_canWord _ _).of_le (by omega)
    have hP : expEquiv α β (P.1, P.2) = castExp hμ.symm p := by
      rw [Prod.mk.eta, Equiv.apply_symm_apply]
    rw [concat_ψw_pol_e hv1 hv2, ← monomial_expEquiv, hP, map_mul, map_mul, castAlg_ψw,
      castAlg_pol_monomial_eq', castExp_castExp_symm, castAlg_e, stdElt, rightWord,
      show shiftWord (Multiset.card α) (canWord b y.2.2) = shiftWord a (canWord b y.2.2) by
        rw [ha]]
    simp only [ψw_append, mul_assoc]
    rfl
  · left; rfl

variable (q : MackeyQuad ν ν' ν'' ν''')

variable (Q) in
/-- The right `R'`-module generators `(ψ_{u₁} ⊗ ψ_{u₂}) ι_T(r)` of `MackeyTop`. -/
def topGens {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) : Set (TensorKLR Q ν ν') :=
  {z | ∃ (u₁ : Perm (Fin (Multiset.card ν))) (u₂ : Perm (Fin (Multiset.card ν')))
    (r : QuadAlg Q q), IsShuffle (adm_hA hc) u₁⁻¹ ∧ IsShuffle (adm_hG h hc) u₂⁻¹ ∧
      ((ψw (canWord _ u₁) : KLRAlgebra k Q ν) ⊗ₜ (ψw (canWord _ u₂) : KLRAlgebra k Q ν')) *
        quadTop q r = z}

/-- **`MackeyTop` is spanned, as a right `R'`-module, by the `(ψ_{u₁} ⊗ ψ_{u₂}) (1_{α,β} ⊗ 1_{γ,δ})`**
with `u₁`, `u₂` minimal coset representatives. -/
theorem mul_quadTop_one_mem_span {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c)
    (hq : Multiset.card q.β = c) (t : TensorKLR Q ν ν') :
    t * quadTop q 1 ∈ Submodule.span k (topGens Q h q hc) := by
  refine tensor_mem_of_std (LinearMap.mulRight k (quadTop q 1)) _ (rightWord (adm_hA hc))
    (rightWord_spec _) (rightWord (adm_hG h hc)) (rightWord_spec _)
    (fun ⟨s, w, p⟩ ⟨s', w', p'⟩ => ?_) t
  rw [LinearMap.mulRight_apply, quadTop_one, Algebra.TensorProduct.tmul_mul_tmul]
  rcases stdElt_rightWord_mul (Q := Q) q.h₁ (adm_hA hc) (card_q_α q hq) w s p with h1 | ⟨z₁, h1⟩
  · rw [h1, TensorProduct.zero_tmul]; exact zero_mem _
  rcases stdElt_rightWord_mul (Q := Q) q.h₂ (adm_hG h hc) (card_q_γ q hq) w' s' p' with
    h2 | ⟨z₂, h2⟩
  · rw [h2, TensorProduct.tmul_zero]; exact zero_mem _
  rw [h1, h2, ← Algebra.TensorProduct.tmul_mul_tmul]
  exact Submodule.subset_span ⟨_, _, z₁ ⊗ₜ z₂, (rightFac_spec _ w).1, (rightFac_spec _ w').1, rfl⟩

theorem span_topGens_le {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) :
    Submodule.span k (topGens Q h q hc) ≤
      (Graded.leftIdeal (quadTop (Q := Q) q 1)).restrictScalars k := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u₁, u₂, r, -, -, rfl⟩
  show _ * _ = _
  rw [mul_assoc, quadTop_mul_one]

variable (Q) in
/-- The generators `gen` of `MackeyX` with `u₁`, `u₂` minimal coset representatives. -/
def genSet {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) : Set (MackeyX Q q) :=
  {y | ∃ (s₃ : Seq ν'') (s₄ : Seq ν''') (x : FacData ν ν' ν'' ν''')
    (v₃ : Fin (Multiset.card ν'') →₀ ℕ) (v₄ : Fin (Multiset.card ν''') →₀ ℕ),
    QuadCond q s₃ s₄ x.2.2.1 x.2.2.2 ∧ IsShuffle (adm_hA hc) x.1⁻¹ ∧
      IsShuffle (adm_hG h hc) x.2.1⁻¹ ∧ gen Q q s₃ s₄ x v₃ v₄ = y}

set_option maxHeartbeats 1000000 in
/-- **The balanced tensor product is spanned by the generators `gen`.** -/
theorem span_genSet {c : ℕ} (hc : MackeyAdm ν ν'' ν''' c) (hq : Multiset.card q.β = c) :
    Submodule.span k (genSet Q h q hc) = ⊤ := by
  -- Step B: `(ψ_{u₁} ⊗ ψ_{u₂}) ⊗ b`
  have stepB : ∀ (u₁ : Perm (Fin (Multiset.card ν))) (u₂ : Perm (Fin (Multiset.card ν'))),
      IsShuffle (adm_hA hc) u₁⁻¹ → IsShuffle (adm_hG h hc) u₂⁻¹ → ∀ (b : MackeyBot Q q),
      (BalancedTensor.tmul (topElt Q q u₁ u₂) b : MackeyX Q q) ∈
        Submodule.span k (genSet Q h q hc) := by
    intro u₁ u₂ hu₁ hu₂ b
    have key : ∀ z ∈ Submodule.span k (botGens Q q), ∀ hz : z ∈ quadBotSub Q q,
        (BalancedTensor.tmul (topElt Q q u₁ u₂) ⟨z, hz⟩ : MackeyX Q q) ∈
          Submodule.span k (genSet Q h q hc) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨s₃, s₄, Y, Y', v₃, v₄, hb, rfl⟩ := hz
        intro hz'
        refine Submodule.subset_span ⟨s₃, s₄, (u₁, u₂, Y, Y'), v₃, v₄, hb, hu₁, hu₂, ?_⟩
        rw [gen, dif_pos hb]
      | zero =>
        intro hz'
        rw [show (⟨0, hz'⟩ : MackeyBot Q q) = 0 from rfl, BalancedTensor.tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro hz'
        rw [show (⟨x + y, hz'⟩ : MackeyBot Q q) = ⟨x, span_botGens_le q hx⟩ +
          ⟨y, span_botGens_le q hy⟩ from rfl, BalancedTensor.tmul_add]
        exact add_mem (ihx _) (ihy _)
      | smul a x hx ihx =>
        intro hz'
        rw [show (⟨a • x, hz'⟩ : MackeyBot Q q) = a • ⟨x, span_botGens_le q hx⟩ from rfl,
          BalancedTensor.tmul_smul]
        exact Submodule.smul_mem _ a (ihx _)
    exact key _ (mem_span_botGens q b) b.2
  -- Step A: reduce `t ∈ MackeyTop` to the generators
  rw [eq_top_iff]
  rintro y -
  induction y using BalancedTensor.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul t b =>
    have key : ∀ z ∈ Submodule.span k (topGens Q h q hc),
        ∀ hz : z ∈ Graded.leftIdeal (quadTop (Q := Q) q 1), ∀ b : MackeyBot Q q,
        (BalancedTensor.tmul (⟨z, hz⟩ : MackeyTop Q q) b : MackeyX Q q) ∈
          Submodule.span k (genSet Q h q hc) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u₁, u₂, r, hu₁, hu₂, rfl⟩ := hz
        intro hz' b
        have e : (⟨_, hz'⟩ : MackeyTop Q q) = op r • topElt Q q u₁ u₂ := by
          apply Subtype.ext
          rw [coe_op_smul_top]
          show _ = _ * quadTop q 1 * quadTop q r
          rw [mul_assoc, quadTop_one_mul]
        rw [e, BalancedTensor.op_smul_tmul]
        exact stepB u₁ u₂ hu₁ hu₂ _
      | zero =>
        intro hz' b
        rw [show (⟨0, hz'⟩ : MackeyTop Q q) = 0 from rfl, BalancedTensor.zero_tmul]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro hz' b
        rw [show (⟨x + y, hz'⟩ : MackeyTop Q q) = ⟨x, span_topGens_le h q hc hx⟩ +
          ⟨y, span_topGens_le h q hc hy⟩ from rfl, BalancedTensor.add_tmul]
        exact add_mem (ihx _ b) (ihy _ b)
      | smul a x hx ihx =>
        intro hz' b
        rw [show (⟨a • x, hz'⟩ : MackeyTop Q q) = a • ⟨x, span_topGens_le h q hc hx⟩ from rfl,
          BalancedTensor.smul_tmul]
        exact Submodule.smul_mem _ a (ihx _ b)
    have ht : (t : TensorKLR Q ν ν') = (t : TensorKLR Q ν ν') * quadTop q 1 := t.2.symm
    have := key _ (mul_quadTop_one_mem_span h q hc hq t) (by rw [← ht]; exact t.2) b
    convert this using 2
    exact Subtype.ext ht

end TopSpan

/-! ### Injectivity and independence -/

section Main

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- `mackeyPsi` is a left inverse of `mackeyMap`. -/
theorem mackeyPsi_comp_mackeyMap (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hq : Multiset.card q.β = c) :
    (mackeyPsi Q h q hPQ hP c).comp (mackeyMap h q hq) = LinearMap.id := by
  have hc : MackeyAdm ν ν'' ν''' c := hq ▸ mackeyAdm_of_quad q
  refine LinearMap.ext_on (span_genSet h q hc hq) ?_
  rintro _ ⟨s₃, s₄, x, v₃, v₄, hb, hx₁, hx₂, rfl⟩
  exact mackeyPsi_mackeyMap_gen h q hPQ hP hc hq hb hx₁ hx₂ v₃ v₄

/-- `mackeyPsi` for `λ` vanishes on the image of `mackeyMap` for `λ' ≠ λ`. -/
theorem mackeyPsi_comp_mackeyMap_ne {q q' : MackeyQuad ν ν' ν'' ν'''} {c : ℕ}
    (hq : Multiset.card q.β = c) (hq' : Multiset.card q'.β = c) (hne : q ≠ q') :
    (mackeyPsi Q h q hPQ hP c).comp (mackeyMap h q' hq') = 0 := by
  have hc : MackeyAdm ν ν'' ν''' c := hq ▸ mackeyAdm_of_quad q
  refine LinearMap.ext_on (span_genSet h q' hc hq') ?_
  rintro _ ⟨s₃, s₄, x, v₃, v₄, hb, hx₁, hx₂, rfl⟩
  exact mackeyPsi_mackeyMap_gen_ne h q hPQ hP hc hq hq' hne hb hx₁ hx₂ v₃ v₄

include hPQ hP in
/-- **KL I, Proposition 2.18 (injectivity)**: the map
`(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (…) → F_c / F_{c-1}` is injective. -/
theorem mackeyMap_injective (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hq : Multiset.card q.β = c) : Function.Injective (mackeyMap (Q := Q) h q hq) := by
  intro x y hxy
  have := congrArg (mackeyPsi Q h q hPQ hP c) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, mackeyPsi_comp_mackeyMap] at this

include hPQ hP in
/-- **KL I, Proposition 2.18 (independence)**: the images of the maps for the different `λ` with
`|λ| = c` are independent in `F_c / F_{c-1}`. -/
theorem mackeyMap_iSupIndep (c : ℕ) :
    iSupIndep fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} =>
      LinearMap.range (mackeyMap (Q := Q) h q.1 q.2) := by
  intro q
  rw [Submodule.disjoint_def]
  rintro x ⟨y, rfl⟩ hx
  have hker : (⨆ j ≠ q, LinearMap.range (mackeyMap (Q := Q) h j.1 j.2)) ≤
      LinearMap.ker (mackeyPsi Q h q.1 hPQ hP c) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
      mackeyPsi_comp_mackeyMap_ne h hPQ hP q.2 j.2 (fun e => hj (Subtype.ext e.symm)),
      LinearMap.zero_apply]
  have h0 := hker hx
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, mackeyPsi_comp_mackeyMap, LinearMap.id_apply]
    at h0
  rw [h0, map_zero]

omit [IsDomain k] in
/-- **KL I, Proposition 2.18 (the images span)**, indexed by the `λ` with `|λ| = c`. -/
theorem iSup_range_mackeyMap (c : ℕ) :
    (⨆ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
      LinearMap.range (mackeyMap (Q := Q) h q.1 q.2)) = ⊤ := by
  rw [← mackeyImage_eq_top h c, mackeyImage, iSup_subtype']

include hPQ hP in
open Classical in
/-- **KL I, Proposition 2.18.** The subquotient `F_c / F_{c-1}` of the Mackey filtration of the
`(R(ν) ⊗ R(ν'), R(ν'') ⊗ R(ν'''))`-bimodule `_{ν,ν'}R_{ν'',ν'''}` is the internal direct sum,
over the admissible `λ` with `|λ| = c`, of the images of the injective bimodule maps
`mackeyMap h q : (_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'}
  (_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''}) → F_c / F_{c-1}`,
which are homogeneous of degree `-λ·(ν'+λ-ν''')` (`mackeyMap_mem_subquotGrading`). -/
theorem mackeySubquot_isInternal (c : ℕ) :
    DirectSum.IsInternal fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} =>
      LinearMap.range (mackeyMap (Q := Q) h q.1 q.2) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨mackeyMap_iSupIndep h hPQ hP c, iSup_range_mackeyMap h c⟩

end Main

end KLRAlgebra

/-! ### The case of KL I -/

namespace KL1

open KLRAlgebra

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj] [IsDomain k] {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')

open Classical in
/-- **KL I, Proposition 2.18** for the rings `R(ν)` of a simple graph `Γ` (over `ℤ` or any
integral domain): `F_c / F_{c-1} ≅ ⊕_{|λ| = c} (_ν R_{ν-λ,λ} ⊗ _{ν'} R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'}
(_{ν-λ,ν''+λ-ν} R_{ν''} ⊗ _{λ,ν'''-λ} R_{ν'''}){-λ·(ν'+λ-ν''')}` as bimodules, via the injective
bimodule maps `mackeyMap` (`KLRAlgebra.mackeyMap_injective`, `mackeyMap_left`, `mackeyMap_right`)
of degree `-λ·(ν'+λ-ν''')` (`KLRAlgebra.mackeyMap_mem_subquotGrading`, `KL1.mackeyShift_eq`). -/
theorem mackeySubquot_isInternal (c : ℕ) :
    DirectSum.IsInternal fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} =>
      LinearMap.range (mackeyMap (Q := klQ (k := k) Γ) h q.1 q.2) :=
  KLRAlgebra.mackeySubquot_isInternal h (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) c

/-- **KL I, Proposition 2.18 (injectivity)** for the rings `R(ν)` of a simple graph. -/
theorem mackeyMap_injective (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hq : Multiset.card q.β = c) : Function.Injective (mackeyMap (Q := klQ (k := k) Γ) h q hq) :=
  KLRAlgebra.mackeyMap_injective h (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) q hq

end KL1

end Categorification.KLR

end
