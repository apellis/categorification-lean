/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIntertwine
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.RedStrands.SubwordBruhatOrder

/-!
# Straightening in Bruhat form, for KLR algebras and Stendhal diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3: the spanning
argument for the basis of `T̃^λ` (Prop. 4.16) rewrites a diagram with local relations, each of
which either keeps the permutation of the strands or deletes crossings. This file records the
resulting bound in Bruhat form: rewriting a product of diagrams in terms of a chosen set of
standard diagrams `ψ_{ρ w} x^u e(i)` only produces permutations `w` that are subword products
of the concatenated words, and for a reduced word of `w` the correction terms are strictly
Bruhat below `w`.

The KLR statements hold for every commutative ring `k` and every `Q`. The Stendhal statements
follow by applying `Stendhal.StendhalAlgebraAllOrders.ofKLR`, which is surjective; the algebra
`T̃^λ` (`Stendhal.StendhalAlgebra`) is a corner of `StendhalAlgebraAllOrders`.

## Main definitions

* `Stendhal.tildeStdSpan ρ X`: the span in `StendhalAlgebraAllOrders` of the images of the
  standard diagrams `ψ_{ρ w} x^u e(i)` with `w ∈ X`.

## Main results

* `KLRAlgebra.mul_mem_subSpan_append`: a product of diagrams on subwords of `α` and `β` lies in
  the span of diagrams on subwords of `α ++ β`.
* `KLRAlgebra.mul_mem_stdSpan_subProds`: such a product is a combination of standard diagrams
  `ψ_{ρ w} x^u e(i)` with `w ∈ subProds (α ++ β)`, a Bruhat lower set
  (`TypeA.mem_subProds_of_bruhatLE`).
* `KLRAlgebra.lowSpan_le_stdSpan`, `KLRAlgebra.strictSpan_le_stdSpan`: diagrams on short words
  only involve short standard diagrams.
* `KLRAlgebra.reduced_sub_mem_stdSpan_bruhatLT`: for a reduced word `γ` of `w`,
  `ψ_γ x^p e(i) - ψ_{ρ w} x^p e(i)` is a combination of standard diagrams strictly Bruhat
  below `w`.
* `KLRAlgebra.x_mul_reduced_sub_mem_stdSpan_bruhatLT`: a dot slides through `ψ_γ`, `γ` reduced,
  up to standard diagrams strictly Bruhat below `w`.
* `KLRAlgebra.stdSpan_univ_eq_top`: the standard diagrams span.
* `Stendhal.ofKLR_mul_mem_tildeStdSpan`, `Stendhal.ofKLR_reduced_sub_mem_tildeStdSpan`,
  `Stendhal.ofKLR_x_mul_reduced_sub_mem_tildeStdSpan`, `Stendhal.tildeStdSpan_univ_eq_top`: the
  same statements for Stendhal diagrams.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

local notation "m" => Multiset.card μ

/-- A product of a diagram on a subword of `α` and a diagram on a subword of `β` lies in the
span of diagrams on subwords of `α ++ β`. -/
theorem mul_mem_subSpan_append {α β : List ℕ} {a b : KLRAlgebra k Q μ}
    (ha : a ∈ subSpan k Q μ α) (hb : b ∈ subSpan k Q μ β) :
    a * b ∈ subSpan k Q μ (α ++ β) := by
  have : subSpan k Q μ α ≤ (subSpan k Q μ (α ++ β)).comap (LinearMap.mulRight k b) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, p, i, hδ, rfl⟩
    show ψw δ * pol p * e i * b ∈ subSpan k Q μ (α ++ β)
    have h1 := ψw_mul_mem_subSpan δ (pol_mul_mem_subSpan p (e_mul_mem_subSpan i hb))
    rw [show ψw δ * pol p * e i * b = ψw δ * (pol p * (e i * b)) by simp only [mul_assoc]]
    exact subSpan_mono (hδ.append (List.Sublist.refl β)) h1
  exact this ha

variable (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

include hρ in
/-- **Straightening of products, Bruhat form.** A product of diagrams on subwords of `α` and of
`β` (with `α ++ β` valid) is a combination of standard diagrams `ψ_{ρ w} x^u e(i)` with
`w ∈ subProds (α ++ β)`; this set is a Bruhat lower set (`TypeA.mem_subProds_of_bruhatLE`). -/
theorem mul_mem_stdSpan_subProds {α β : List ℕ} (hv : ValidWord m (α ++ β))
    {a b : KLRAlgebra k Q μ} (ha : a ∈ subSpan k Q μ α) (hb : b ∈ subSpan k Q μ β) :
    a * b ∈ stdSpan Q ρ (subProds m (α ++ β)) :=
  subSpan_le_stdSpan ρ hρ hv (mul_mem_subSpan_append ha hb)

include hρ in
/-- Diagrams on short words with subword products in `S` only involve standard diagrams of
short permutations in `S`. -/
theorem lowSpan_le_stdSpan (S : Set (Perm (Fin m))) (L : ℕ) :
    lowSpan k Q μ S L ≤ stdSpan Q ρ {v | v ∈ S ∧ length m v < L} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨τ, p, i, hv, hS, hL, rfl⟩
  refine stdSpan_mono ρ ?_ (gen_mem_stdSpan ρ hρ τ hv p i)
  intro v hv'
  refine ⟨hS hv', ?_⟩
  obtain ⟨δ, hδ, rfl⟩ := hv'
  have h1 := length_wordProd_le (hv.sublist hδ)
  have h2 := hδ.length_le
  omega

include hρ in
/-- Diagrams on proper subwords of a valid word `γ` only involve standard diagrams of subword
products of `γ` shorter than `γ`. -/
theorem strictSpan_le_stdSpan {γ : List ℕ} (hγ : ValidWord m γ) :
    strictSpan k Q μ γ ≤ stdSpan Q ρ {v | v ∈ subProds m γ ∧ length m v < γ.length} :=
  (strictSpan_le_lowSpan hγ).trans (lowSpan_le_stdSpan ρ hρ _ _)

/-- Standard diagrams of short subword products of a reduced word `γ` are strictly Bruhat
below `wordProd m γ`. -/
private theorem stdSpan_short_le_bruhatLT {γ : List ℕ} (hγ : IsReduced m γ) {L : ℕ}
    (hL : L ≤ γ.length) :
    stdSpan Q ρ {v | v ∈ subProds m γ ∧ length m v < L} ≤
      stdSpan Q ρ {v | BruhatLE m v (wordProd m γ) ∧ v ≠ wordProd m γ} := by
  refine stdSpan_mono ρ fun v ⟨hv, hl⟩ => ⟨(mem_subProds_iff_bruhatLE hγ).1 hv, ?_⟩
  rintro rfl
  have := hγ.2
  omega

include hρ in
/-- **Leading term, Bruhat form.** For a reduced word `γ` of `w`, the diagram `ψ_γ x^p e(i)`
differs from the standard diagram `ψ_{ρ w} x^p e(i)` by standard diagrams of permutations
strictly Bruhat below `w`. -/
theorem reduced_sub_mem_stdSpan_bruhatLT {γ : List ℕ} (hγ : IsReduced m γ)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (ψw γ * pol p * e i : KLRAlgebra k Q μ) - ψw (ρ (wordProd m γ)) * pol p * e i ∈
      stdSpan Q ρ {v | BruhatLE m v (wordProd m γ) ∧ v ≠ wordProd m γ} := by
  have hE := braidEquiv_of_isReduced hγ (hρ (wordProd m γ)).1 (hρ _).2.symm
  have h := braidEquiv_sub_mem_lowSpan (Q := Q) hE hγ.1 p i
  exact stdSpan_short_le_bruhatLT ρ hγ (Nat.sub_le _ _) (lowSpan_le_stdSpan ρ hρ _ _ h)

include hρ in
/-- **Dots slide through a reduced word, Bruhat form.** For a reduced word `γ` of `w`,
`x_a ψ_γ x^p e(i) - ψ_γ x_{w⁻¹ a} x^p e(i)` is a combination of standard diagrams of
permutations strictly Bruhat below `w`. -/
theorem x_mul_reduced_sub_mem_stdSpan_bruhatLT {γ : List ℕ} (hγ : IsReduced m γ) (a : Fin m)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (x a * (ψw γ * pol p * e i) : KLRAlgebra k Q μ) -
        ψw γ * pol (X ((wordProd m γ)⁻¹ a) * p) * e i ∈
      stdSpan Q ρ {v | BruhatLE m v (wordProd m γ) ∧ v ≠ wordProd m γ} :=
  stdSpan_short_le_bruhatLT ρ hγ le_rfl
    (strictSpan_le_stdSpan ρ hρ hγ.1 (x_mul_gen_sub_mem_strictSpan γ a p i))

include hρ in
/-- The standard diagrams `ψ_{ρ w} x^u e(i)` span the KLR algebra. -/
theorem stdSpan_univ_eq_top : stdSpan Q ρ (Set.univ : Set (Perm (Fin m))) = ⊤ := by
  refine eq_top_iff.2 fun r _ => ?_
  obtain ⟨n, hn⟩ := exists_mem_filt r
  refine (Submodule.span_le.2 ?_) hn
  rintro _ ⟨γ, p, i, hv, -, rfl⟩
  exact stdSpan_mono ρ (Set.subset_univ _) (gen_mem_stdSpan ρ hρ γ hv p i)

end KLRAlgebra

end Categorification.KLR

namespace Categorification.Stendhal

open Equiv MvPolynomial TypeA KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Φ" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν

variable (Q Λ ν) in
/-- The span, in the algebra of Stendhal diagrams, of the images of the standard diagrams
`ψ_{ρ w} x^u e(i)` with `w ∈ X`. -/
noncomputable def tildeStdSpan (ρ : Perm (Fin m) → List ℕ) (X : Set (Perm (Fin m))) :
    Submodule k (StendhalAlgebraAllOrders k Q Λ ν) :=
  (stdSpan (stendhalQ Q Λ) ρ X).map (Φ).toLinearMap

theorem map_mem_tildeStdSpan (ρ : Perm (Fin m) → List ℕ) {X : Set (Perm (Fin m))}
    {r : KLRAlgebra k (stendhalQ Q Λ) μ} (hr : r ∈ stdSpan (stendhalQ Q Λ) ρ X) :
    Φ r ∈ tildeStdSpan Q Λ ν ρ X :=
  Submodule.mem_map_of_mem hr

theorem tildeStdSpan_mono (ρ : Perm (Fin m) → List ℕ) {X Y : Set (Perm (Fin m))}
    (h : X ⊆ Y) : tildeStdSpan Q Λ ν ρ X ≤ tildeStdSpan Q Λ ν ρ Y :=
  Submodule.map_mono (stdSpan_mono ρ h)

/-- **Straightening of products of Stendhal diagrams, Bruhat form.** The image of a product of
diagrams on subwords of `α` and `β` is a combination of the images of standard diagrams of
permutations in the Bruhat lower set `subProds (α ++ β)`. -/
theorem ofKLR_mul_mem_tildeStdSpan (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {α β : List ℕ} (hv : ValidWord m (α ++ β))
    {a b : KLRAlgebra k (stendhalQ Q Λ) μ} (ha : a ∈ subSpan k (stendhalQ Q Λ) μ α)
    (hb : b ∈ subSpan k (stendhalQ Q Λ) μ β) :
    Φ a * Φ b ∈ tildeStdSpan Q Λ ν ρ (subProds m (α ++ β)) := by
  rw [← map_mul]
  exact map_mem_tildeStdSpan ρ (mul_mem_stdSpan_subProds ρ hρ hv ha hb)

/-- **Leading term of a Stendhal diagram, Bruhat form.** For a reduced word `γ` of `w`, the
image of `ψ_γ x^p e(i)` differs from that of `ψ_{ρ w} x^p e(i)` by images of standard diagrams
of permutations strictly Bruhat below `w`. -/
theorem ofKLR_reduced_sub_mem_tildeStdSpan (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {γ : List ℕ} (hγ : TypeA.IsReduced m γ) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    Φ (ψw γ * pol p * e i) - Φ (ψw (ρ (wordProd m γ)) * pol p * e i) ∈
      tildeStdSpan Q Λ ν ρ {v | BruhatLE m v (wordProd m γ) ∧ v ≠ wordProd m γ} := by
  rw [← map_sub]
  exact map_mem_tildeStdSpan ρ (reduced_sub_mem_stdSpan_bruhatLT ρ hρ hγ p i)

/-- **Dots slide through a reduced Stendhal diagram, Bruhat form.** -/
theorem ofKLR_x_mul_reduced_sub_mem_tildeStdSpan (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {γ : List ℕ} (hγ : TypeA.IsReduced m γ) (a : Fin m)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    Φ (x a) * Φ (ψw γ * pol p * e i) -
        Φ (ψw γ * pol (X ((wordProd m γ)⁻¹ a) * p) * e i) ∈
      tildeStdSpan Q Λ ν ρ {v | BruhatLE m v (wordProd m γ) ∧ v ≠ wordProd m γ} := by
  rw [← map_mul, ← map_sub]
  exact map_mem_tildeStdSpan ρ (x_mul_reduced_sub_mem_stdSpan_bruhatLT ρ hρ hγ a p i)

/-- The images of the standard diagrams span the algebra of Stendhal diagrams. -/
theorem tildeStdSpan_univ_eq_top (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    tildeStdSpan Q Λ ν ρ Set.univ = ⊤ := by
  rw [tildeStdSpan, stdSpan_univ_eq_top ρ hρ, Submodule.map_top, LinearMap.range_eq_top]
  exact StendhalAlgebraAllOrders.ofKLR_surjective

end Categorification.Stendhal
