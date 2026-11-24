/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicFinite
import Categorification.WeightedKLR.RedStrands.BraidColumnGeneration

/-!
# Projective cuts with a polynomial inside the upper word

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.11. A polynomial left by
a braid correction can lie inside the word of an earlier selected diagram.
When the crossings between the polynomial and that cut involve distinct
labels, exact dot slides put the polynomial below the cut.
-/

namespace Categorification.KLR.KLRAlgebra

open KLR TypeA MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- At each height the crossing exchanges distinct labels, read from the
bottom loading by applying the suffix below the crossing. -/
def DistinctCrossings : List ℕ → Seq ν → Prop
  | [], _ => True
  | j :: γ, s =>
      (∃ h : j + 1 < m, (wordProd m γ • s).lbl ⟨j, by omega⟩ ≠
        (wordProd m γ • s).lbl ⟨j + 1, h⟩) ∧ DistinctCrossings γ s

/-- A bottom idempotent with distinct labels permits a polynomial to slide to
the right of its crossing, permuting variables. -/
theorem pol_mul_ψ_mul_e_of_ne (j : ℕ) (h : j + 1 < m) (s : Seq ν)
    (hne : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, h⟩) (p : MvPolynomial (Fin m) k) :
    (pol p * ψ j * e s : A) = ψ j * pol (swapPol j h p) * e s := by
  have hswap : swapPol j h (swapPol j h p) = p := by
    simp only [swapPol, rename_rename]
    rw [show (⇑(Equiv.swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) ∘ ⇑(Equiv.swap
      (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩)) = id from
      funext fun a => Equiv.swap_apply_self _ _ a, rename_id_apply]
  have key := ψ_mul_pol_mul_e (Q := Q) j h s (swapPol j h p)
  rw [hswap, ite_eq_right hne, add_zero] at key
  exact key.symm

/-- A polynomial can be slid below a word of distinct-label crossings with
no correction terms. -/
theorem exists_pol_mul_ψw_mul_e_eq_of_distinctCrossings (γ : List ℕ) (s : Seq ν)
    (hγ : DistinctCrossings γ s) (p : MvPolynomial (Fin m) k) :
    ∃ p' : MvPolynomial (Fin m) k,
      (pol p * (ψw γ * e s) : A) = ψw γ * (pol p' * e s) := by
  induction γ generalizing p with
  | nil => exact ⟨p, by simp⟩
  | cons j γ ih =>
    obtain ⟨⟨hj, hne⟩, hγ⟩ := hγ
    let t := wordProd m γ • s
    let b : A := ψw γ * e s
    have hb : e t * b = b := by
      dsimp only [t, b]
      rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    have hs := congrArg (fun a : A => a * b) (pol_mul_ψ_mul_e_of_ne j hj t hne p)
    have hs' : (pol p * (ψ j * b) : A) = ψ j * (pol (swapPol j hj p) * b) := by
      simpa only [mul_assoc, hb] using hs
    obtain ⟨p', hp'⟩ := ih hγ (swapPol j hj p)
    change pol (swapPol j hj p) * b = _ at hp'
    refine ⟨p', ?_⟩
    simpa only [ψw_cons, mul_assoc, b] using hs'.trans (congrArg (fun a : A => ψ j * a) hp')

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν
local notation "E" => fun s : Seq μ => q (raw (e s))
local notation "C" => fun κ => q (redProj k Q Λ ν κ)

/-- Cut a dotted diagram through a selected loading. Dots inside the upper
diagram can be absorbed into the projective coefficient if the remaining
upper crossings have distinct labels at the cut loading. -/
theorem dottedCut_mem_columnProductsOn (ρ : Equiv.Perm (Fin m) → List ℕ)
    (s : Seq μ) (κ : List (Fin ℓ)) (S : Set (Equiv.Perm (Fin m)))
    {v w : Equiv.Perm (Fin m)} {α η β : List ℕ} (hv : v ∈ S)
    (hw : v * wordProd m β = w) (hk : redWord (v⁻¹ • s) = κ)
    (hρη : ρ v = α ++ η) (hη : DistinctCrossings η (v⁻¹ • s))
    (p : MvPolynomial (Fin m) k) (z : cornerBimodule (E (w⁻¹ • s)) (C κ)) :
    q (raw (ψw α * pol p * ψw (η ++ β) * e (w⁻¹ • s))) * z.val ∈
      columnProductsOn (Q := Q) (Λ := Λ) ρ s κ S := by
  let t := w⁻¹ • s
  let u := v⁻¹ • s
  let b : KLRAlgebra k (stendhalQ Q Λ) μ := ψw β * e t
  have ht : wordProd m β • t = u := by
    change wordProd m β • (w⁻¹ • s) = v⁻¹ • s
    rw [← hw, mul_inv_rev, mul_smul, smul_inv_smul]
  have hb : e u * b = b := by
    change e u * (ψw β * e t) = _
    rw [ψw_mul_e, ht, ← mul_assoc, e_mul_self]
    change e u * ψw β = ψw β * e t
    rw [ψw_mul_e, ht]
  obtain ⟨p', hp'⟩ := exists_pol_mul_ψw_mul_e_eq_of_distinctCrossings
    (Q := stendhalQ Q Λ) η u hη p
  have hp : (pol p * (ψw η * b) : KLRAlgebra k (stendhalQ Q Λ) μ) =
      ψw η * (pol p' * b) := by
    have hh := congrArg (fun x : KLRAlgebra k (stendhalQ Q Λ) μ => x * b) hp'
    simpa only [mul_assoc, hb] using hh
  have hdot : (e u * (pol p' * b) : KLRAlgebra k (stendhalQ Q Λ) μ) = pol p' * b := by
    rw [← mul_assoc, (e_commute_pol _ p').eq, mul_assoc, hb]
  let a : V := q (raw (pol p' * b))
  have ha : E u * a = a := by
    change q (raw (e u)) * q (raw (pol p' * b)) = a
    rw [← map_mul q, ← map_mul raw, hdot]
  refine ⟨v, a * z.val, hv, hk, ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, z.prop.2]⟩, ?_⟩
  change q (raw (ψw α * pol p * ψw (η ++ β) * e t)) * z.val =
    q (raw (ψw (ρ v) * e u)) * (a * z.val)
  have hf : (ψw α * pol p * ψw (η ++ β) * e t : KLRAlgebra k (stendhalQ Q Λ) μ) =
      (ψw (ρ v) * e u) * (pol p' * b) := by
    simp only [hρη, ψw_append, mul_assoc, b] at hp ⊢
    rw [hp, hdot]
  rw [hf, map_mul raw, map_mul q, mul_assoc]

end Categorification.Stendhal.BraidedStendhalAlgebra
