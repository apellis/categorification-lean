/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorAlong
import Categorification.WeightedKLR.RedStrands.BraidedAppendFree

set_option backward.isDefEq.respectTransparency false

/-!
# The braided algebra with an extra black strand as a free module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.7. Write `e_κ` for the idempotent of the red order `κ`, and let the
append map `φ` add a black strand at the right. The elements `ψ_c x_{last}^n φ(e_κ)`, for `c`
increasing on the old strands, form a basis of `e_κ B̃(ν + i) φ(e_κ)` as a right module over the
image of `φ`: every element of `e_κ B̃(ν + i) φ(e)` is a sum `Σ ψ_c x_{last}^n φ(e_κ y_c e)`, and
such a sum vanishes only if every `e_κ y_c e` does.

## Main results

* `CosetIdx`: the pairs `(c, n)` with `c` increasing on the old strands.
* `cosetElt_mul_appendBlackValue_redProj`: `ψ_c x^n φ(e_κ) = e_κ ψ_c x^n φ(1)`.
* `exists_cosetGen_sum`: the spanning statement.
* `cosetGen_sum_eq_zero`: the independence statement.
* `mult_injective_append`, `mult_surjective_append`: multiplication from the tensor product
  along `φ` is injective, and onto the corner.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "last" => lastPos (BraidedStendhalAlgebra.appendCard i ν (ℓ := ℓ))

namespace BraidedStendhalAlgebra

omit [DecidableEq I] in
theorem appendBlackLoading_injective :
    Function.Injective (appendBlackLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  have := congrArg (fun s => s.lbl (appendPos i ν a)) h
  simpa only [appendBlackLoading_lbl_appendPos] using this

/-- The pairs `(c, n)` with `c` increasing on the old strands. -/
def CosetIdx : Type :=
  {p : Perm (Fin (Multiset.card (stendhalWeight ℓ νᵢ))) × ℕ //
    StrictMono fun x : Fin (Multiset.card (stendhalWeight ℓ ν)) =>
      p.1 (blockEquiv (appendCard i ν) (Sum.inl x))}

/-- The element `ψ_c x_{last}^n`. -/
def cosetElt (p : CosetIdx (ℓ := ℓ) i ν) : BraidedStendhalAlgebra k Q Λ νᵢ :=
  ofKLR k Q Λ νᵢ (ψw (canWord _ p.1.1) * KLRAlgebra.x last ^ p.1.2)

theorem redProj_mul_cosetElt_mul_e (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν)
    (s : Seq (stendhalWeight ℓ ν)) :
    redProj k Q Λ νᵢ κ * cosetElt Q Λ i ν p *
        ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) =
      if redWord s = κ then
        cosetElt Q Λ i ν p * ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s))
      else 0 := by
  have hp : (ψw (canWord _ p.1.1) * KLRAlgebra.x last ^ p.1.2 :
      KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ νᵢ)) =
      ψw (canWord _ p.1.1) * pol (X last ^ p.1.2) := by
    rw [map_pow, pol_X]
  have hX : (ψw (canWord _ p.1.1) * pol (X last ^ p.1.2) *
        KLRAlgebra.e (appendBlackLoading i ν s) :
      KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ νᵢ)) *
        redIdem k Q Λ (redWord (appendBlackLoading i ν s)) =
      ψw (canWord _ p.1.1) * pol (X last ^ p.1.2) * KLRAlgebra.e (appendBlackLoading i ν s) := by
    rw [mul_assoc _ (KLRAlgebra.e _), e_mul_redIdem]
    simp only [↓reduceIte]
  rw [cosetElt, redProj, ← map_mul, ← map_mul, hp, mul_assoc (redIdem k Q Λ κ), ← hX,
    ← mul_assoc, redIdem_mul_std, wordProd_canWord, redWord_smul_appendBlackLoading i ν p.2,
    redWord_appendBlackLoading, ← map_mul]
  simp only [and_true]
  split_ifs <;> simp only [map_zero]

/-- `ψ_c x^n φ(e_κ) = e_κ ψ_c x^n φ(1)`. -/
theorem cosetElt_mul_appendBlackValue_redProj (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν) :
    cosetElt Q Λ i ν p * appendBlackValue Q Λ i ν (redProj k Q Λ ν κ) =
      redProj k Q Λ νᵢ κ * cosetElt Q Λ i ν p * appendIdem Q Λ i ν := by
  rw [appendBlackValue_redProj, redProj_mul_appendIdem, appendIdem_eq_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun s _ => (redProj_mul_cosetElt_mul_e Q Λ i ν κ p s).symm

theorem appendIdem_mul_appendBlackValue (z : BraidedStendhalAlgebra k Q Λ ν) :
    appendIdem Q Λ i ν * appendBlackValue Q Λ i ν z = appendBlackValue Q Λ i ν z :=
  KLR.Corner.E_mul_val (appendBlack Q Λ i ν z)

/-- `ψ_c x^n φ(e_κ y) = e_κ ψ_c x^n φ(y)`. -/
theorem cosetElt_mul_appendBlackValue (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν)
    (y : BraidedStendhalAlgebra k Q Λ ν) :
    cosetElt Q Λ i ν p * appendBlackValue Q Λ i ν (redProj k Q Λ ν κ * y) =
      redProj k Q Λ νᵢ κ * cosetElt Q Λ i ν p * appendBlackValue Q Λ i ν y := by
  rw [map_mul, ← mul_assoc, cosetElt_mul_appendBlackValue_redProj, mul_assoc _ (appendIdem _ _ _ _),
    appendIdem_mul_appendBlackValue]

/-- The generators `ψ_c x^n φ(e_κ)`. -/
def cosetGen (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν) : BraidedStendhalAlgebra k Q Λ νᵢ :=
  cosetElt Q Λ i ν p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ)

theorem cosetGen_mul (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν)
    (y : BraidedStendhalAlgebra k Q Λ ν) :
    cosetGen Q Λ i ν κ p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y) =
      cosetElt Q Λ i ν p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y) := by
  rw [cosetGen, mul_assoc, ← map_mul, ← mul_assoc, (isIdempotentElem_redProj κ).eq]

theorem redProj_mul_cosetGen_mul (κ : List (Fin ℓ)) (p : CosetIdx (ℓ := ℓ) i ν) :
    redProj k Q Λ νᵢ κ * cosetGen Q Λ i ν κ p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ) =
      cosetGen Q Λ i ν κ p := by
  have h := cosetGen_mul Q Λ i ν κ p (redProj k Q Λ ν κ)
  rw [(isIdempotentElem_redProj κ).eq] at h
  rw [mul_assoc, h, appendBlackAlg_apply, cosetElt_mul_appendBlackValue_redProj, cosetGen,
    appendBlackAlg_apply, cosetElt_mul_appendBlackValue_redProj, ← mul_assoc, ← mul_assoc,
    (isIdempotentElem_redProj κ).eq]

variable (hQ : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ) (hρ : IsReducedChoice ρ)

omit [DecidableEq I] in
/-- Every standard diagram of `B̃(ν + i)` with bottom loading `s i` is `ψ_c x^n φ(b)`. -/
theorem exists_appendIdx_eq (β : BlackIdx (ℓ := ℓ) νᵢ) (s : Seq (stendhalWeight ℓ ν))
    (hs : β.1.1 = appendBlackLoading i ν s) :
    ∃ (p : CosetIdx (ℓ := ℓ) i ν) (b : BlackIdx (ℓ := ℓ) ν), appendIdx i ν p.1.1 p.1.2 b = β := by
  obtain ⟨⟨t, w, u⟩, hu⟩ := β
  dsimp only at hs
  subst hs
  set c := (lastCosetSplit (appendCard i ν) w).1
  set τ := (lastCosetSplit (appendCard i ν) w).2
  let u₀ : Fin (Multiset.card (stendhalWeight ℓ ν)) →₀ ℕ :=
    u.comapDomain (appendPos i ν) (appendPos_injective i ν).injOn
  have hu₀ : ∀ a, u₀ a = u (appendPos i ν a) := fun a => Finsupp.comapDomain_apply _ _ _ _
  refine ⟨⟨(c, u last), strictMono_lastCosetSplit _ w⟩, ⟨(s, τ, u₀), fun a ha => ?_⟩, ?_⟩
  · rw [hu₀]
    exact hu _ (by rw [appendBlackLoading_lbl_appendPos]; exact ha)
  · apply Subtype.ext
    refine Prod.ext rfl (Prod.ext (lastCosetSplit_mul _ w) ?_)
    ext a
    change appendDots i ν u₀ (u last) a = u a
    by_cases ha : a.val < Multiset.card (stendhalWeight ℓ ν)
    · rw [← appendPos_val_cast i ν a ha, appendDots_appendPos, hu₀]
    · have : a = last := Fin.ext (by
        have := a.isLt
        have := card_stendhalWeight_addBlack i ν (ℓ := ℓ)
        simp only [lastPos_val]
        omega)
      subst this
      rw [appendDots_last]

omit [DecidableEq I] in
theorem appendIdx_injective :
    Function.Injective fun q : CosetIdx (ℓ := ℓ) i ν × BlackIdx (ℓ := ℓ) ν =>
      appendIdx i ν q.1.1.1 q.1.1.2 q.2 := by
  rintro ⟨⟨⟨c, n⟩, hc⟩, ⟨⟨s, τ, u⟩, hu⟩⟩ ⟨⟨⟨c', n'⟩, hc'⟩, ⟨⟨s', τ', u'⟩, hu'⟩⟩ h
  have h' := congrArg Subtype.val h
  simp only [appendIdx, Prod.mk.injEq] at h'
  obtain ⟨hs, hw, hd⟩ := h'
  have hs' := appendBlackLoading_injective i ν hs
  have h1 := lastCosetSplit_eq (appendCard i ν) (τ := τ) hc
  have h2 := lastCosetSplit_eq (appendCard i ν) (τ := τ') hc'
  rw [hw, h2, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have hn : n = n' := by
    have := congrArg (fun d => d last) hd
    simpa only [appendDots_last] using this
  subst hs' hn
  have hu : u = u' := by
    ext a
    have := congrArg (fun d => d (appendPos i ν a)) hd
    simpa only [appendDots_appendPos] using this
  subst hu
  rfl

/-- The basis of `B̃(ν + i)` through the last coset. -/
abbrev appendBasis : Module.Basis (BlackIdx (ℓ := ℓ) νᵢ) k (BraidedStendhalAlgebra k Q Λ νᵢ) :=
  basis (Λ := Λ) (ν := νᵢ) hQ (lastCosetWord (appendCard i ν) ρ)
    (isReducedChoice_lastCosetWord hρ)

theorem appendBasis_appendIdx (p : CosetIdx (ℓ := ℓ) i ν) (b : BlackIdx (ℓ := ℓ) ν) :
    appendBasis Q Λ i ν hQ ρ hρ (appendIdx i ν p.1.1 p.1.2 b) =
      cosetElt Q Λ i ν p * appendBlackAlg Q Λ i ν (basis hQ ρ hρ b) :=
  (coset_mul_appendBlackValue_basis Q Λ i ν hQ ρ hρ p.2 p.1.2 b).symm

/-- A standard diagram whose bottom loading does not end in the new strand is killed by `φ`. -/
theorem appendBasis_mul_appendBlackAlg_eq_zero (β : BlackIdx (ℓ := ℓ) νᵢ)
    (hβ : ∀ s : Seq (stendhalWeight ℓ ν), β.1.1 ≠ appendBlackLoading i ν s)
    (y : BraidedStendhalAlgebra k Q Λ ν) :
    appendBasis Q Λ i ν hQ ρ hρ β * appendBlackAlg Q Λ i ν y = 0 := by
  rw [appendBlackAlg_apply, ← appendIdem_mul_appendBlackValue, ← mul_assoc, appendIdem_eq_sum,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [basis_apply, ← map_mul, mul_assoc, KLRAlgebra.e_mul_e]
  simp only [hβ s, ↓reduceIte, mul_zero, map_zero, zero_mul]

include hQ hρ in
/-- **Spanning** (Webster, proof of Proposition 6.7): every element of `e_κ B̃(ν + i) φ(e)` is
`Σ_c ψ_c x^n φ(e_κ) φ(e_κ y_c e)`. -/
theorem exists_cosetGen_sum (κ : List (Fin ℓ)) (e' : BraidedStendhalAlgebra k Q Λ ν)
    (z : BraidedStendhalAlgebra k Q Λ νᵢ) :
    ∃ t : CosetIdx (ℓ := ℓ) i ν →₀ BraidedStendhalAlgebra k Q Λ ν,
      redProj k Q Λ νᵢ κ * z * appendBlackAlg Q Λ i ν e' =
        t.sum fun p y => cosetGen Q Λ i ν κ p *
          appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e') := by
  have h0 : ∀ p, cosetGen Q Λ i ν κ p *
      appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * 0 * e') = 0 := fun p => by
    rw [mul_zero, zero_mul, map_zero, mul_zero]
  have hadd : ∀ p (y y' : BraidedStendhalAlgebra k Q Λ ν),
      cosetGen Q Λ i ν κ p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * (y + y') * e') =
        cosetGen Q Λ i ν κ p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e') +
          cosetGen Q Λ i ν κ p * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y' * e') :=
    fun p y y' => by rw [mul_add, add_mul, map_add, mul_add]
  refine Submodule.span_induction (p := fun z _ => ∃ t : CosetIdx (ℓ := ℓ) i ν →₀ _,
      redProj k Q Λ νᵢ κ * z * appendBlackAlg Q Λ i ν e' =
        t.sum fun p y => cosetGen Q Λ i ν κ p *
          appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e')) ?_ ?_ ?_ ?_
    ((appendBasis Q Λ i ν hQ ρ hρ).mem_span z)
  · rintro _ ⟨β, rfl⟩
    by_cases hβ : ∃ s, β.1.1 = appendBlackLoading i ν s
    · obtain ⟨s, hs⟩ := hβ
      obtain ⟨p, b, rfl⟩ := exists_appendIdx_eq i ν β s hs
      refine ⟨Finsupp.single p (basis hQ ρ hρ b), ?_⟩
      rw [Finsupp.sum_single_index (h0 p), appendBasis_appendIdx, mul_assoc (redProj k Q Λ ν κ),
        cosetGen_mul]
      simp only [appendBlackAlg_apply]
      rw [cosetElt_mul_appendBlackValue, map_mul]
      simp only [mul_assoc]
    · refine ⟨0, ?_⟩
      rw [Finsupp.sum_zero_index, mul_assoc,
        appendBasis_mul_appendBlackAlg_eq_zero Q Λ i ν hQ ρ hρ β (not_exists.1 hβ ·), mul_zero]
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨t, ht⟩ ⟨t', ht'⟩
    refine ⟨t + t', ?_⟩
    rw [Finsupp.sum_add_index' h0 hadd, ← ht, ← ht', mul_add, add_mul]
  · rintro r x _ ⟨t, ht⟩
    refine ⟨r • t, ?_⟩
    rw [Finsupp.sum_smul_index' h0, mul_smul_comm, smul_mul_assoc, ht, Finsupp.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only
    rw [mul_smul_comm, smul_mul_assoc, map_smul, mul_smul_comm]

omit [DecidableEq I] in
theorem appendIdx_eq_iff (p q : CosetIdx (ℓ := ℓ) i ν) (b b' : BlackIdx (ℓ := ℓ) ν) :
    appendIdx i ν q.1.1 q.1.2 b = appendIdx i ν p.1.1 p.1.2 b' ↔ q = p ∧ b = b' :=
  ⟨fun h => Prod.mk.inj (appendIdx_injective i ν (a₁ := (q, b)) (a₂ := (p, b')) h),
    fun ⟨h, h'⟩ => h ▸ h' ▸ rfl⟩

open Classical in
theorem repr_cosetElt_mul_appendBlackAlg (p q : CosetIdx (ℓ := ℓ) i ν) (b₀ : BlackIdx (ℓ := ℓ) ν)
    (y : BraidedStendhalAlgebra k Q Λ ν) :
    (appendBasis Q Λ i ν hQ ρ hρ).repr (cosetElt Q Λ i ν q * appendBlackAlg Q Λ i ν y)
        (appendIdx i ν p.1.1 p.1.2 b₀) =
      if q = p then (basis hQ ρ hρ).repr y b₀ else 0 := by
  let L₁ : BraidedStendhalAlgebra k Q Λ ν →ₗ[k] k :=
    (Finsupp.lapply (appendIdx i ν p.1.1 p.1.2 b₀)) ∘ₗ
      (appendBasis Q Λ i ν hQ ρ hρ).repr.toLinearMap ∘ₗ
        (LinearMap.mulLeft k (cosetElt Q Λ i ν q)) ∘ₗ
          LinearMap.ofClass (appendBlackAlg Q Λ i ν)
  let L₂ : BraidedStendhalAlgebra k Q Λ ν →ₗ[k] k :=
    if q = p then (Finsupp.lapply b₀) ∘ₗ (basis hQ ρ hρ).repr.toLinearMap else 0
  have h := (basis hQ ρ hρ).ext (f₁ := L₁) (f₂ := L₂) fun b => by
    simp only [L₁, L₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_ofClass,
      LinearMap.mulLeft_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply]
    rw [← appendBasis_appendIdx, Module.Basis.repr_self, Finsupp.single_apply,
      appendIdx_eq_iff]
    split_ifs with h₁ h₂ h₂
    · simp [h₁.2]
    · exact absurd h₁.1 h₂
    · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Finsupp.lapply_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hb
      exacts [absurd ⟨h₂, hb⟩ h₁, rfl]
    · exact (LinearMap.zero_apply _).symm
  have := LinearMap.congr_fun h y
  simp only [L₁, L₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_ofClass,
    LinearMap.mulLeft_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply] at this
  rw [this]
  split_ifs
  exacts [rfl, LinearMap.zero_apply _]

include hQ hρ in
/-- **Independence** (Webster, proof of Proposition 6.7): if
`Σ_c ψ_c x^n φ(e_κ) φ(e_κ y_c e) = 0` then every `e_κ y_c e` vanishes. -/
theorem cosetGen_sum_eq_zero (κ : List (Fin ℓ)) (e' : BraidedStendhalAlgebra k Q Λ ν)
    (Y : CosetIdx (ℓ := ℓ) i ν →₀ BraidedStendhalAlgebra k Q Λ ν)
    (hY : (Y.sum fun p y => cosetGen Q Λ i ν κ p *
      appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e')) = 0)
    (p : CosetIdx (ℓ := ℓ) i ν) : redProj k Q Λ ν κ * Y p * e' = 0 := by
  classical
  have hg : ∀ q (y : BraidedStendhalAlgebra k Q Λ ν), cosetGen Q Λ i ν κ q *
      appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e') =
        cosetElt Q Λ i ν q * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ * y * e') :=
    fun q y => by rw [mul_assoc (redProj _ _ _ _ _), cosetGen_mul]
  refine (basis hQ ρ hρ).repr.injective ?_
  ext b₀
  have h := congrArg (fun z => (appendBasis Q Λ i ν hQ ρ hρ).repr z
    (appendIdx i ν p.1.1 p.1.2 b₀)) hY
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, hg,
    repr_cosetElt_mul_appendBlackAlg, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [Finset.sum_ite_eq'] at h
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs at h with hp
  · exact h
  · rw [Finsupp.notMem_support_iff.1 hp, mul_zero, zero_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply]

theorem idemAppend (κ : List (Fin ℓ)) : IsIdempotentElem (redProj k Q Λ νᵢ κ) :=
  isIdempotentElem_redProj κ

theorem idemBase (κ : List (Fin ℓ)) : IsIdempotentElem (redProj k Q Λ ν κ) :=
  isIdempotentElem_redProj κ

include hQ hρ in
/-- Webster, proof of Proposition 6.7: multiplication
`e_κ' B̃(ν + i) φ(e_κ') ⊗ e_κ' B̃(ν) e_κ → B̃(ν + i)`, along the append map `φ`, is injective. -/
theorem mult_injective_append (κ' κ : List (Fin ℓ)) :
    Function.Injective (TensorAlong.mult (idemAppend Q Λ i ν κ')
      (idemBase Q Λ ν κ') (idemBase Q Λ ν κ) :
      TensorAlong k _ _ (appendBlackAlg Q Λ i ν) (redProj k Q Λ νᵢ κ') (redProj k Q Λ ν κ')
        (redProj k Q Λ ν κ) →ₗ[k] _) :=
  TensorAlong.mult_injective_of_basis _ _ _ (cosetGen Q Λ i ν κ')
    (redProj_mul_cosetGen_mul Q Λ i ν κ')
    (exists_cosetGen_sum Q Λ i ν hQ ρ hρ κ' (redProj k Q Λ ν κ'))
    (fun Y hY p => cosetGen_sum_eq_zero Q Λ i ν hQ ρ hρ κ' (redProj k Q Λ ν κ) Y hY p)

include hQ hρ in
/-- Webster, proof of Proposition 6.7: the image of multiplication along `φ` is the corner
`e_κ' B̃(ν + i) φ(e_κ)`. -/
theorem mult_surjective_append (κ' κ : List (Fin ℓ)) (z : BraidedStendhalAlgebra k Q Λ νᵢ) :
    ∃ t, TensorAlong.mult (idemAppend Q Λ i ν κ')
      (idemBase Q Λ ν κ') (idemBase Q Λ ν κ)
      (t : TensorAlong k _ _ (appendBlackAlg Q Λ i ν) (redProj k Q Λ νᵢ κ')
        (redProj k Q Λ ν κ') (redProj k Q Λ ν κ)) =
      redProj k Q Λ νᵢ κ' * z * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ) :=
  TensorAlong.mult_surjective_of_basis _ _ _ (cosetGen Q Λ i ν κ')
    (redProj_mul_cosetGen_mul Q Λ i ν κ')
    (exists_cosetGen_sum Q Λ i ν hQ ρ hρ κ' (redProj k Q Λ ν κ)) z

end BraidedStendhalAlgebra

end Categorification.Stendhal
