/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildePhiStraightening
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers
import Categorification.WeightedKLR.RedStrands.PrependRedStandardDegree

/-!
# The layers `P̃_{≥φ}/P̃_{>φ}` of the projective `T̃^λ e(s)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23 (the proof of Proposition 5.21 run in `T̃^λ`). For a red-ordered loading `s` and
a choice `ρ` of reduced words, the diagrams `x̃_φ` generate `P̃ = T̃^λ e(s)`
(`iSup_tildePhiSub_eq_top`). Put `P̃_{>φ} = Σ_{φ < φ'} T̃^λ x̃_{φ'}` and
`P̃_{≥φ} = P̃_{>φ} + T̃^λ x̃_φ`, the order being Webster's order on the bottoms `φ • s`. Then
`S̃_{φ • s} → P̃_{≥φ}/P̃_{>φ}`, `[e(φ • s)] ↦ [x̃_φ]`, is well defined and surjective
(`tildePhiLayerMap_surjective`), where `S̃_t = T̃^λ e(t) / Ũ_t` is the left standard module of
`T̃^λ`.

## Main definitions

* `tildePhiSub`, `tildePhiAbove`, `tildePhiAtLeast`, `tildePhiLayer`, `tildeStandard`.
* `tildePhiLayerMap`: the map `S̃_{φ • s} → P̃_{≥φ}/P̃_{>φ}`.

## Main results

* `iSup_tildePhiSub_eq_top`, `tildePhiLayerGen_annihilated`, `tildePhiLayerMap_surjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => StendhalAlgebra k Q Λ ν
local notation "E" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- A shortcut: instance search does not unfold `StendhalAlgebra` to find the additive group of
a submodule of a left ideal. -/
private abbrev addCommGroupSubmoduleLIdeal (x : B) (M : Submodule B (lIdeal x)) :
    AddCommGroup M :=
  Submodule.addCommGroup (R := B) M

attribute [local instance] addCommGroupSubmoduleLIdeal

variable {Q Λ}

theorem stendhalAlgebra_e_mul_e_self (s : Seq μ) (hs : IsRedOrdered s) :
    (StendhalAlgebra.e s hs * StendhalAlgebra.e s hs : B) = StendhalAlgebra.e s hs := by
  apply Subtype.ext
  change E s * E s = E s
  simp [StendhalAlgebraAllOrders.e_mul_e]

variable (ℓ ν Q Λ) in
/-- The idempotents of the red-ordered loadings sum to one in `T̃^λ_ν`. -/
theorem sum_stendhalAlgebra_e_eq_one :
    ∑ s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 =
      (1 : StendhalAlgebra k Q Λ ν) := by
  classical
  apply Subtype.ext
  rw [KLR.Corner.val_sum, KLR.Corner.val_one]
  change (∑ s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s},
    StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
  exact (Finset.sum_subtype _ (fun s => by simp) _).symm

theorem tildePhiElt_mul_e (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    tildePhiElt Q Λ ρ hs hg * StendhalAlgebra.e s hs = tildePhiElt Q Λ ρ hs hg := by
  apply Subtype.ext
  change E (phiBottom s g) * _ * E s * E s = E (phiBottom s g) * _ * E s
  simp [mul_assoc, StendhalAlgebraAllOrders.e_mul_e]

theorem e_mul_tildePhiElt (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    StendhalAlgebra.e (phiBottom s g) (isRedOrdered_phiBottom hs hg) * tildePhiElt Q Λ ρ hs hg =
      tildePhiElt Q Λ ρ hs hg := by
  apply Subtype.ext
  change E (phiBottom s g) * (E (phiBottom s g) * _ * E s) = E (phiBottom s g) * _ * E s
  simp [← mul_assoc, StendhalAlgebraAllOrders.e_mul_e]

theorem e_mul_mul_e_eq_phiCut {t s : Seq μ} (ht : IsRedOrdered t) (hs : IsRedOrdered s) (y : B) :
    StendhalAlgebra.e t ht * y * StendhalAlgebra.e s hs = phiCut Q Λ t s ht hs y.1 :=
  rfl

variable (Q Λ) in
/-- `x̃_φ` as an element of `P̃ = T̃^λ e(s)`. -/
def tildePhiVec (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) : lIdeal (StendhalAlgebra.e s hs : B) :=
  ⟨tildePhiElt Q Λ ρ hs g.mem, tildePhiElt_mul_e ρ hs g.mem⟩

variable (Q Λ) in
/-- The submodule `T̃^λ x̃_φ` of `P̃ = T̃^λ e(s)`. -/
def tildePhiSub (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    Submodule B (lIdeal (StendhalAlgebra.e s hs : B)) :=
  Submodule.span B {tildePhiVec Q Λ ρ hs g}

private theorem mem_of_val_mem_map' {M : Submodule B B} {S : Submodule B M} {x : M}
    (h : (x : B) ∈ S.map M.subtype) : x ∈ S := by
  obtain ⟨y, hy, he⟩ := h
  rwa [show y = x from Subtype.ext he] at hy

/-- An element of `P̃` lying in `e(t) T̃^λ e(s)` lies in the span of the `T̃^λ x̃_{φ'}` with
`t ≤ φ' • s`. -/
theorem mem_iSup_tildePhiSub_of_e (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {t : Seq μ}
    (ht : IsRedOrdered t) (y : lIdeal (StendhalAlgebra.e s hs : B))
    (hy : StendhalAlgebra.e t ht * (y : B) = (y : B)) :
    y ∈ ⨆ (g : PhiIndex s) (_ : StendhalLE t (phiBottom s g.1)), tildePhiSub Q Λ ρ hs g := by
  refine mem_of_val_mem_map' ?_
  have hmem := phiCut_mem_tildePhiSpan (Q := Q) (Λ := Λ) ρ hρ hs ht (y : B).1
  rw [← e_mul_mul_e_eq_phiCut, show (StendhalAlgebra.e t ht * (y : B) *
    StendhalAlgebra.e s hs : B) = y by rw [hy]; exact y.2] at hmem
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨g, hg, hle, rfl⟩
  refine ⟨tildePhiVec Q Λ ρ hs ⟨g, List.mem_toFinset.2 hg⟩, ?_, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨g, List.mem_toFinset.2 hg⟩
    (Submodule.mem_iSup_of_mem hle (Submodule.subset_span rfl))

/-- **The `x̃_φ` generate `P̃ = T̃^λ e(s)`.** -/
theorem iSup_tildePhiSub_eq_top (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    (⨆ g : PhiIndex s, tildePhiSub Q Λ ρ hs g) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ t : {t : Seq μ // IsRedOrdered t},
      (⟨StendhalAlgebra.e t.1 t.2 * (y : B), by
        change _ * _ * _ = _; rw [mul_assoc, y.2]⟩ : lIdeal (StendhalAlgebra.e s hs : B)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (y : B) = ∑ t : {t : Seq μ // IsRedOrdered t}, StendhalAlgebra.e t.1 t.2 * (y : B)
    rw [← Finset.sum_mul, sum_stendhalAlgebra_e_eq_one, one_mul]
  rw [hy]
  refine Submodule.sum_mem _ fun t _ => ?_
  have := mem_iSup_tildePhiSub_of_e ρ hs hρ t.2 ⟨StendhalAlgebra.e t.1 t.2 * (y : B), by
    change _ * _ * _ = _; rw [mul_assoc, y.2]⟩ (by
      change _ * (_ * _) = _ * _
      rw [← mul_assoc, stendhalAlgebra_e_mul_e_self])
  refine (iSup_mono (fun g => ?_) : _ ≤ ⨆ g, tildePhiSub Q Λ ρ hs g) this
  exact iSup_le fun _ => le_rfl

variable (Q Λ) in
/-- `P̃_{>φ}`: the sum of the `T̃^λ x̃_{φ'}` with `φ < φ'`. -/
abbrev tildePhiAbove (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) : Submodule B (lIdeal (StendhalAlgebra.e s hs : B)) :=
  Submodule.above PhiLT (tildePhiSub Q Λ ρ hs) g

variable (Q Λ) in
/-- `P̃_{≥φ} = T̃^λ x̃_φ + P̃_{>φ}`. -/
abbrev tildePhiAtLeast (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) : Submodule B (lIdeal (StendhalAlgebra.e s hs : B)) :=
  tildePhiSub Q Λ ρ hs g ⊔ tildePhiAbove Q Λ ρ hs g

variable (Q Λ) in
/-- The layer `P̃_{≥φ}/P̃_{>φ}`. -/
abbrev tildePhiLayer (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) : Type :=
  tildePhiAtLeast Q Λ ρ hs g ⧸
    (tildePhiAbove Q Λ ρ hs g).comap (tildePhiAtLeast Q Λ ρ hs g).subtype

variable (Q Λ) in
/-- The class `[x̃_φ]` in the layer. -/
def tildePhiLayerGen (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) : tildePhiLayer Q Λ ρ hs g :=
  Submodule.Quotient.mk
    ⟨tildePhiVec Q Λ ρ hs g, Submodule.mem_sup_left (Submodule.subset_span rfl)⟩

private theorem stendhalLT_of_lt_of_le' {a b c : Seq μ} (hab : StendhalLT a b)
    (hbc : StendhalLE b c) : StendhalLT a c :=
  ⟨fun r i => (hab.1 r i).trans (hbc r i), fun hca => hab.2 fun r i => (hbc r i).trans (hca r i)⟩

/-- `[x̃_φ]` is killed by `e(t) T̃^λ` for `t` strictly above `φ • s`. -/
theorem tildePhiLayerGen_annihilated (ρ : Perm (Fin m) → List ℕ) {s : Seq μ}
    (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s)
    (t : Seq μ) (ht : IsRedOrdered t) (a : B) (hlt : StendhalLT (phiBottom s g.1) t) :
    (StendhalAlgebra.e t ht * a) • tildePhiLayerGen Q Λ ρ hs g = 0 := by
  rw [tildePhiLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (StendhalAlgebra.e t ht * a) • tildePhiVec Q Λ ρ hs g ∈ tildePhiAbove Q Λ ρ hs g
  have h := mem_iSup_tildePhiSub_of_e ρ hs hρ ht
    ((StendhalAlgebra.e t ht * a) • tildePhiVec Q Λ ρ hs g) (by
      change StendhalAlgebra.e t ht * (StendhalAlgebra.e t ht * a * tildePhiElt Q Λ ρ hs g.mem) =
        StendhalAlgebra.e t ht * a * tildePhiElt Q Λ ρ hs g.mem
      rw [← mul_assoc, ← mul_assoc, stendhalAlgebra_e_mul_e_self])
  refine (iSup₂_le (fun g' hle => ?_) : _ ≤ tildePhiAbove Q Λ ρ hs g) h
  exact le_iSup₂_of_le (f := fun g' (_ : PhiLT g g') => tildePhiSub Q Λ ρ hs g') g'
    (stendhalLT_of_lt_of_le' hlt hle) le_rfl

variable (Q Λ) in
/-- **The left standard module `S̃_t = T̃^λ e(t) / Ũ_t` of `T̃^λ`** (Webster,
arXiv:1309.3796v3, Definition 5.1, left form). -/
abbrev tildeStandard (t : Seq μ) (ht : IsRedOrdered t) : Type :=
  lIdeal (StendhalAlgebra.e t ht : B) ⧸
    (tildeLeftUpper Q Λ ν t ht).comap (lIdeal (StendhalAlgebra.e t ht : B)).subtype

/-- An element `z` killed by every `e(t') T̃^λ` with `t'` above `t` is killed by `Ũ_t`. -/
theorem tildeLeftUpper_smul_eq_zero {Z : Type*} [AddCommGroup Z] [Module B Z] (t : Seq μ)
    (ht : IsRedOrdered t) (z : Z)
    (hz : ∀ (t' : Seq μ) (ht' : IsRedOrdered t') (a : B), StendhalLT t t' →
      (StendhalAlgebra.e t' ht' * a) • z = 0) {y : B} (hy : y ∈ tildeLeftUpper Q Λ ν t ht) :
    y • z = 0 := by
  have hle : tildeLeftUpper Q Λ ν t ht ≤ LinearMap.ker (LinearMap.toSpanSingleton B Z z) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨t', ht', a, hlt, rfl⟩
    change (StendhalAlgebra.e t' ht' * a * StendhalAlgebra.e t ht) • z = 0
    rw [mul_assoc, hz t' ht' _ hlt]
  exact hle hy

variable (Q Λ) in
/-- **The map `S̃_{φ • s} → P̃_{≥φ}/P̃_{>φ}`**, `[y] ↦ y [x̃_φ]`, so `[e(φ • s)] ↦ [x̃_φ]`. -/
def tildePhiLayerMap (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    tildeStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs) →ₗ[B] tildePhiLayer Q Λ ρ hs g :=
  ((tildeLeftUpper Q Λ ν (phiBottom s g.1) (g.isRedOrdered hs)).comap
    (lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)).subtype).liftQ
    ((LinearMap.toSpanSingleton B _ (tildePhiLayerGen Q Λ ρ hs g)).comp
      (lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)).subtype)
    fun _ hy => tildeLeftUpper_smul_eq_zero _ _ _
      (fun t ht a hlt => tildePhiLayerGen_annihilated ρ hs hρ g t ht a hlt) hy

theorem tildePhiLayerMap_mk (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s)
    (y : lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)) :
    tildePhiLayerMap Q Λ ρ hs hρ g (Submodule.Quotient.mk y) =
      (y : B) • tildePhiLayerGen Q Λ ρ hs g :=
  rfl

/-- **Webster, proof of Corollary 5.23**: `S̃_{φ • s} → P̃_{≥φ}/P̃_{>φ}` is surjective. -/
theorem tildePhiLayerMap_surjective (ρ : Perm (Fin m) → List ℕ) {s : Seq μ}
    (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    Function.Surjective (tildePhiLayerMap Q Λ ρ hs hρ g) := by
  intro v
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨n, hn, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
  set eb : B := StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs)
  refine ⟨Submodule.Quotient.mk ⟨c * eb, by
    change c * eb * eb = c * eb
    rw [mul_assoc, stendhalAlgebra_e_mul_e_self]⟩, ?_⟩
  rw [tildePhiLayerMap_mk, tildePhiLayerGen, ← Submodule.Quotient.mk_smul, eq_comm,
    Submodule.Quotient.eq]
  have hev : (c * eb) • tildePhiVec Q Λ ρ hs g = c • tildePhiVec Q Λ ρ hs g := by
    apply Subtype.ext
    change c * eb * tildePhiElt Q Λ ρ hs g.mem = c * tildePhiElt Q Λ ρ hs g.mem
    rw [mul_assoc, e_mul_tildePhiElt]
  change (⟨c • tildePhiVec Q Λ ρ hs g + b, hy⟩ - (c * eb) • ⟨tildePhiVec Q Λ ρ hs g, _⟩ :
    tildePhiAtLeast Q Λ ρ hs g) ∈ _
  rw [Submodule.mem_comap]
  convert hb using 1
  change c • tildePhiVec Q Λ ρ hs g + b - (c * eb) • tildePhiVec Q Λ ρ hs g = b
  rw [hev]
  abel

end Categorification.Stendhal
