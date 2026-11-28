/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksStandardBasis

/-!
# Loading corners of a partial standardization at a cut

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22: the `Tor_0` term at the diagonal of the S-move is computed from the corner
`e(s) 𝕊(N)` of a partial standardization at a loading `s`. In the shuffle coordinates
`𝕊(N) ≅ ⊕_u ε_u N` (`cutStandardShuffleEquiv`), the loading idempotent `e(s)` acts on the
coordinate `u` by `1_{u s}` (`cutStandardShuffleEquiv_action_e`). When `1_{u s} = 0` for every
shuffle `u ≠ 1` (`IsUnshuffledLoading`), only the identity coordinate survives, and the fixed
vectors of `e(s)` on `𝕊(N)` are those of `1_s` on `N` (`cutStandardLoadingFixedEquiv`).

## Main definitions

* `Stendhal.IsUnshuffledLoading`: `1_{u s} = 0` for every shuffle `u ≠ 1`.
* `Stendhal.cutStandardLoadingFixedEquiv`: `e(s) 𝕊(N) ≅ 1_s N` for an unshuffled loading `s`.

## Main results

* `TypeA.shuffle_eq_one_of_fix_left`, `TypeA.shuffle_eq_one_of_fix_right`: a shuffle with a
  one-element block fixing that element is the identity.
* `KLR.shuffle_eq_one_of_smul_append_left`, `KLR.shuffle_eq_one_of_smul_append_right`.
* `Stendhal.isUnshuffledLoading_append_emptyLeft`, `Stendhal.isUnshuffledLoading_append_emptyRight`:
  for the cuts of the S-move with the outer block `P_∅` (one red strand, no black strand),
  every concatenation of loadings of the two blocks is unshuffled.
-/

noncomputable section

namespace Categorification.TypeA
open Equiv

/-- A strictly monotone permutation of `Fin m` is the identity. -/
theorem perm_eq_one_of_strictMono {m : ℕ} (σ : Perm (Fin m)) (hσ : StrictMono σ) : σ = 1 := by
  ext x
  have := congrArg (fun e : Fin m ≃o Fin m => (e x : Fin m))
    (Subsingleton.elim (StrictMono.orderIsoOfSurjective σ hσ σ.surjective) (OrderIso.refl _))
  simpa using congrArg Fin.val this

variable {n n' m : ℕ} {h : n + n' = m}

/-- A shuffle of a one-element first block fixing that element is the identity. -/
theorem shuffle_eq_one_of_fix_left (hn : n = 1) (u : Shuffle h) (x₀ : Fin n)
    (hu : u.1⁻¹ (blockEquiv h (Sum.inl x₀)) = blockEquiv h (Sum.inl x₀)) :
    u.1 = 1 := by
  have hsub : ∀ a a' : Fin n, a = a' := fun a a' => by
    subst hn; exact Subsingleton.elim a a'
  rw [← inv_eq_one]
  refine perm_eq_one_of_strictMono _ fun x x' hxx' => ?_
  obtain ⟨p, rfl⟩ := (blockEquiv h).surjective x
  obtain ⟨p', rfl⟩ := (blockEquiv h).surjective x'
  rcases p with a | y <;> rcases p' with a' | y'
  · exact absurd hxx' (by rw [hsub a a']; exact lt_irrefl _)
  · rw [hsub a x₀, hu]
    have hne : u.1⁻¹ (blockEquiv h (Sum.inr y')) ≠ blockEquiv h (Sum.inl x₀) := by
      rw [← hu]
      exact fun he => absurd ((blockEquiv h).injective (u.1⁻¹.injective he)) (by simp)
    rw [Fin.lt_def]
    have h0 : (blockEquiv h (Sum.inl x₀)).val = 0 := by
      rw [blockEquiv_inl_val]; have := x₀.2; omega
    rw [h0]
    exact Nat.pos_of_ne_zero fun hz => hne (Fin.ext (hz.trans h0.symm))
  · exfalso
    rw [Fin.lt_def, blockEquiv_inl_val, blockEquiv_inr_val] at hxx'
    have := a'.2; omega
  · exact u.2.2 ((blockEquiv_inr_lt_inr h).mp hxx')

/-- A shuffle of a one-element second block fixing that element is the identity. -/
theorem shuffle_eq_one_of_fix_right (hn' : n' = 1) (u : Shuffle h) (y₀ : Fin n')
    (hu : u.1⁻¹ (blockEquiv h (Sum.inr y₀)) = blockEquiv h (Sum.inr y₀)) :
    u.1 = 1 := by
  have hsub : ∀ b b' : Fin n', b = b' := fun b b' => by
    subst hn'; exact Subsingleton.elim b b'
  rw [← inv_eq_one]
  refine perm_eq_one_of_strictMono _ fun x x' hxx' => ?_
  obtain ⟨p, rfl⟩ := (blockEquiv h).surjective x
  obtain ⟨p', rfl⟩ := (blockEquiv h).surjective x'
  rcases p with a | y <;> rcases p' with a' | y'
  · exact u.2.1 hxx'
  · rw [hsub y' y₀, hu]
    have hne : u.1⁻¹ (blockEquiv h (Sum.inl a)) ≠ blockEquiv h (Sum.inr y₀) := by
      rw [← hu]
      exact fun he => absurd ((blockEquiv h).injective (u.1⁻¹.injective he)) (by simp)
    have htop : (blockEquiv h (Sum.inr y₀)).val + 1 = m := by
      rw [blockEquiv_inr_val]; have := y₀.2; omega
    rw [Fin.lt_def]
    have := (u.1⁻¹ (blockEquiv h (Sum.inl a))).2
    have hv : (u.1⁻¹ (blockEquiv h (Sum.inl a))).val ≠ (blockEquiv h (Sum.inr y₀)).val :=
      fun he => hne (Fin.ext he)
    omega
  · exfalso
    rw [Fin.lt_def, blockEquiv_inl_val, blockEquiv_inr_val] at hxx'
    have := a'.2; omega
  · exact absurd hxx' (by rw [hsub y y']; exact lt_irrefl _)

end Categorification.TypeA

namespace Categorification.KLR
open Equiv TypeA

variable {J : Type*} {ν ν' : Multiset J}

/-- If the first block is a single strand whose label does not occur in the second block, the
only shuffle carrying a concatenation to a concatenation is the identity. -/
theorem shuffle_eq_one_of_smul_append_left (hν : Multiset.card ν = 1)
    (hdisj : ∀ x ∈ ν, x ∉ ν') (i : Seq ν) (j : Seq ν') (u : Shuffle (Seq.card_add' ν ν'))
    {i' : Seq ν} {j' : Seq ν'} (he : u.1 • i.append j = i'.append j') : u.1 = 1 := by
  let x₀ : Fin (Multiset.card ν) := ⟨0, by omega⟩
  refine shuffle_eq_one_of_fix_left hν u x₀ ?_
  have hq : (i.append j).1 (u.1⁻¹ (Seq.posL ν' x₀)) = i'.1 x₀ := by
    have := congrArg (fun s : Seq (ν + ν') => s.1 (Seq.posL ν' x₀)) he
    simpa [Perm.inv_def] using this
  obtain ⟨w, hw⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective (u.1⁻¹ (Seq.posL ν' x₀))
  rcases w with a | b
  · rw [show a = x₀ from Fin.ext (by have := a.2; omega)] at hw
    exact hw.symm
  · exfalso
    have hb : (i.append j).1 (Seq.posR ν b) = j.1 b := Seq.append_posR i j b
    rw [show Seq.posR ν b = u.1⁻¹ (Seq.posL ν' x₀) from hw, hq] at hb
    exact hdisj _ (i'.mem x₀) (hb ▸ j.mem b)

/-- If the second block is a single strand whose label does not occur in the first block, the
only shuffle carrying a concatenation to a concatenation is the identity. -/
theorem shuffle_eq_one_of_smul_append_right (hν' : Multiset.card ν' = 1)
    (hdisj : ∀ x ∈ ν', x ∉ ν) (i : Seq ν) (j : Seq ν') (u : Shuffle (Seq.card_add' ν ν'))
    {i' : Seq ν} {j' : Seq ν'} (he : u.1 • i.append j = i'.append j') : u.1 = 1 := by
  let y₀ : Fin (Multiset.card ν') := ⟨0, by omega⟩
  refine shuffle_eq_one_of_fix_right hν' u y₀ ?_
  have hq : (i.append j).1 (u.1⁻¹ (Seq.posR ν y₀)) = j'.1 y₀ := by
    have := congrArg (fun s : Seq (ν + ν') => s.1 (Seq.posR ν y₀)) he
    simpa [Perm.inv_def] using this
  obtain ⟨w, hw⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective (u.1⁻¹ (Seq.posR ν y₀))
  rcases w with a | b
  · exfalso
    have ha : (i.append j).1 (Seq.posL ν' a) = i.1 a := Seq.append_posL i j a
    rw [show Seq.posL ν' a = u.1⁻¹ (Seq.posR ν y₀) from hw, hq] at ha
    exact hdisj _ (j'.mem y₀) (ha ▸ i.mem a)
  · rw [show b = y₀ from Fin.ext (by have := b.2; omega)] at hw
    exact hw.symm

end Categorification.KLR

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "V" => CutStandard Q Λ θ β N
local notation "N₀" => CutInput Q Λ θ β N

/-- The loading idempotent `e(s)` acting on the partial standardization `𝕊(N)`. -/
abbrev cutLoadingEnd (s : Seq (α + δ)) : Module.End k V :=
  cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e s))

/-- The idempotent `1_s` of the affine block algebra acting on the input `N`. -/
abbrev cutInputIdemEnd (s : Seq (α + δ)) : Module.End k N₀ :=
  DistribSMul.toLinearMap k N₀ (concatIdem (Q := S) s)

/-- A loading `s` of all strands is *unshuffled* if `1_{u s} = 0` for every shuffle `u ≠ 1`:
no nontrivial shuffle of `s` splits into a loading of the first block followed by one of the
second. -/
def IsUnshuffledLoading (s : Seq (α + δ)) : Prop :=
  ∀ u : Sh, u ≠ shufOne → concatIdem (Q := S) (u.1 • s) = 0

variable {Q Λ θ β}

/-- The fixed vectors of an endomorphism `f`. -/
theorem mem_ker_sub_one_iff {M : Type*} [AddCommGroup M] [Module k M] (f : Module.End k M)
    (x : M) : x ∈ LinearMap.ker (f - 1) ↔ f x = x := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

/-- A vector fixed by `e(s)` has no coordinate at a shuffle `u` with `1_{u s} = 0`. -/
theorem cutStandardShuffleEquiv_eq_zero_of_fixed {s : Seq (α + δ)} {w : V}
    (hw : cutLoadingEnd Q Λ θ β N hQ s w = w) {u : Sh}
    (hu : concatIdem (Q := S) (u.1 • s) = 0) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ w : Sh → N₀) u = 0 := by
  rw [← hw, cutStandardShuffleEquiv_action_e, hu, zero_smul]

/-- The loading idempotent on the identity-shuffle copy of `N`. -/
theorem cutLoadingEnd_unit (s : Seq (α + δ)) (n : N₀) :
    cutLoadingEnd Q Λ θ β N hQ s (cutStandardUnit Q Λ θ β N n) =
      cutStandardUnit Q Λ θ β N (cutInputIdemEnd Q Λ θ β N s n) := by
  apply (cutStandardShuffleEquiv Q Λ θ β N hQ).injective
  apply Subtype.ext
  funext u
  rw [cutStandardShuffleEquiv_action_e, cutStandardShuffleEquiv_unit,
    cutStandardShuffleEquiv_unit]
  by_cases hu : u = shufOne
  · subst hu
    simp only [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, smul_zero]

/-- A vector fixed by the loading idempotent of an unshuffled loading is the identity-shuffle
copy of its identity coordinate. -/
theorem eq_cutStandardUnit_of_fixed {s : Seq (α + δ)} (hs : IsUnshuffledLoading Q Λ θ β s)
    {w : V} (hw : cutLoadingEnd Q Λ θ β N hQ s w = w) :
    w = cutStandardUnit Q Λ θ β N
      ((cutStandardShuffleEquiv Q Λ θ β N hQ w : Sh → N₀) shufOne) := by
  apply (cutStandardShuffleEquiv Q Λ θ β N hQ).injective
  apply Subtype.ext
  funext u
  rw [cutStandardShuffleEquiv_unit]
  by_cases hu : u = shufOne
  · subst hu
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hu]
    exact cutStandardShuffleEquiv_eq_zero_of_fixed N hQ hw (hs u hu)

variable (Q Λ θ β)

/-- **The loading corner of a partial standardization** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, the corner at the diagonal): for an unshuffled loading `s`, the
vectors of `𝕊(N)` fixed by `e(s)` are the identity-shuffle copies of the vectors of `N` fixed
by `1_s`. -/
def cutStandardLoadingFixedEquiv {s : Seq (α + δ)} (hs : IsUnshuffledLoading Q Λ θ β s) :
    LinearMap.ker (cutLoadingEnd Q Λ θ β N hQ s - 1) ≃ₗ[k]
      LinearMap.ker (cutInputIdemEnd Q Λ θ β N s - 1) where
  toFun w := ⟨(cutStandardShuffleEquiv Q Λ θ β N hQ w.1 : Sh → N₀) shufOne, by
    rw [mem_ker_sub_one_iff]
    have hw := (mem_ker_sub_one_iff _ _).mp w.2
    conv_rhs => rw [← hw]
    rw [cutStandardShuffleEquiv_action_e]
    rfl⟩
  invFun n := ⟨cutStandardUnit Q Λ θ β N n.1, by
    rw [mem_ker_sub_one_iff, cutLoadingEnd_unit N hQ, (mem_ker_sub_one_iff _ _).mp n.2]⟩
  map_add' w w' := Subtype.ext (by
    simp only [Submodule.coe_add, map_add, Submodule.coe_add, Pi.add_apply])
  map_smul' c w := Subtype.ext (by
    simp only [Submodule.coe_smul, map_smul, Submodule.coe_smul, Pi.smul_apply,
      RingHom.id_apply])
  left_inv w := Subtype.ext (eq_cutStandardUnit_of_fixed N hQ hs
    ((mem_ker_sub_one_iff _ _).mp w.2)).symm
  right_inv n := Subtype.ext (by
    change (cutStandardShuffleEquiv Q Λ θ β N hQ (cutStandardUnit Q Λ θ β N n.1) : Sh → N₀)
      shufOne = n.1
    rw [cutStandardShuffleEquiv_unit, Pi.single_eq_same])

/-- **Unshuffled loadings for a one-strand first block**: if the first block of the cut is a
single strand whose label does not occur in the second block, every concatenation is
unshuffled. -/
theorem isUnshuffledLoading_append_of_left
    (hα : Multiset.card α = 1) (hdisj : ∀ x ∈ α, x ∉ δ) (i : Seq α) (j : Seq δ) :
    IsUnshuffledLoading Q Λ θ β (i.append j) := by
  intro u hu
  rw [concatIdem]
  refine Finset.sum_eq_zero fun p hp => absurd (Subtype.ext ?_) hu
  exact shuffle_eq_one_of_smul_append_left hα hdisj i j u (Finset.mem_filter.mp hp).2.symm

/-- **Unshuffled loadings for a one-strand second block**: if the second block of the cut is a
single strand whose label does not occur in the first block, every concatenation is
unshuffled. -/
theorem isUnshuffledLoading_append_of_right
    (hδ : Multiset.card δ = 1) (hdisj : ∀ x ∈ δ, x ∉ α) (i : Seq α) (j : Seq δ) :
    IsUnshuffledLoading Q Λ θ β (i.append j) := by
  intro u hu
  rw [concatIdem]
  refine Finset.sum_eq_zero fun p hp => absurd (Subtype.ext ?_) hu
  exact shuffle_eq_one_of_smul_append_right hδ hdisj i j u (Finset.mem_filter.mp hp).2.symm

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- For the cut `{1} | {2, …}` with no black strand in the first block (the outer block `P_∅`
of the S-move), every concatenation is unshuffled. -/
theorem isUnshuffledLoading_append_emptyLeft {r : ℕ} (Λ : Fin (1 + r) → I →₀ ℕ)
    (β : Multiset I)
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r))
      (stendhalWeight 1 (0 : Multiset I))))
    (j : Seq (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight r β))) :
    IsUnshuffledLoading Q Λ 0 β (i.append j) := by
  refine isUnshuffledLoading_append_of_left Q Λ 0 β (by simp [stendhalWeight]) ?_ i j
  intro x hx hx'
  simp [stendhalWeight] at hx hx'
  subst hx
  rcases hx' with ⟨c, -, hc⟩ | ⟨t, ht⟩
  · exact Sum.inl_ne_inr hc
  · have := congrArg Fin.val (Sum.inr_injective ht)
    simp at this

/-- For the cut `{1, …} | {last}` with no black strand in the last block (the outer block `P_∅`
of the mirror side of the S-move), every concatenation is unshuffled. -/
theorem isUnshuffledLoading_append_emptyRight {a : ℕ} (Λ : Fin (a + 1) → I →₀ ℕ)
    (θ : Multiset I)
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight a θ)))
    (j : Seq (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
      (stendhalWeight 1 (0 : Multiset I)))) :
    IsUnshuffledLoading Q Λ θ 0 (i.append j) := by
  refine isUnshuffledLoading_append_of_right Q Λ θ 0 (by simp [stendhalWeight]) ?_ i j
  intro x hx hx'
  simp [stendhalWeight] at hx hx'
  subst hx
  rcases hx' with ⟨c, -, hc⟩ | ⟨t, ht⟩
  · exact Sum.inl_ne_inr hc
  · have := congrArg Fin.val (Sum.inr_injective ht)
    simp at this
    omega

end Categorification.Stendhal
