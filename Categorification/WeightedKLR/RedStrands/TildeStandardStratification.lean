/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeLayerIso
import Categorification.WeightedKLR.RedStrands.TildeStratumIdeal
import Categorification.Algebra.TotalOrderFiltration
import Categorification.Algebra.OrderedProjectiveResolution

/-!
# Standard stratification of `T̃^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Corollary
5.23: `T̃^λ` is standardly stratified, with the left standard modules
`S̃_t = T̃^λ e(t) / Ũ_t` and Webster's preorder on loadings. In the form proved here:

* for every set `Γ` of loadings closed upwards, `P̃_Γ = Σ_{φ • s ∈ Γ} T̃^λ x̃_φ` has a finite
  filtration by standard modules `S̃_u` with `u ∈ Γ` (`exists_hasFiltration_phiStratumSub`).
  The filtration is taken along a linear extension of Webster's order with `Γ` on top
  (`stratumRel`), using the layer isomorphisms `tildeRelLayerEquiv`;
* the kernel `Ũ_t ∩ T̃^λ e(t)` of `T̃^λ e(t) → S̃_t` is `P̃_Γ` for `Γ = {u | t < u}`
  (`comap_tildeLeftUpper_eq_phiStratumSub`), so it has a finite filtration by standard modules
  `S̃_u` with `u` strictly above `t` (`exists_hasFiltration_tildeLeftUpper`);
* hence the projectives `T̃^λ e(t)` are ordered standard covers (`tildeOrderedStandardCovers`).

Hypotheses on the grading as for `tildeRelLayerEquiv`: the grading on `T̃^λ` with all red
orders is bounded below (`hc`), and black dots have positive degree (`hpos`); Webster's grading
satisfies both. Route hypothesis: `AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`.

## Main definitions

* `stratumRel`, `tildeOrderedStandardCovers`.

## Main results

* `exists_hasFiltration_phiStratumSub`, `comap_tildeLeftUpper_eq_phiStratumSub`,
  `exists_hasFiltration_tildeLeftUpper`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => StendhalAlgebra k Q Λ ν

/-- A shortcut: instance search does not unfold `StendhalAlgebra` to find the additive group of
a submodule of a left ideal. -/
private abbrev addCommGroupSubmoduleLIdeal'' (x : B) (M : Submodule B (lIdeal x)) :
    AddCommGroup M :=
  Submodule.addCommGroup (R := B) M

attribute [local instance] addCommGroupSubmoduleLIdeal''

section Order

open scoped Classical in
/-- The key of a block assignment for `stratumRel`: membership of the bottom in `Γ`, then the
number of assignments strictly below in Webster's order, then a fixed enumeration. -/
def stratumKey {s : Seq μ} (Γ : Set (Seq μ)) (g : PhiIndex s) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (if phiBottom s g.1 ∈ Γ then 1 else 0,
    toLex ((Finset.univ.filter fun g' : PhiIndex s => PhiLT g' g).card,
      (Fintype.equivFin (PhiIndex s) g : ℕ)))

/-- **A linear extension of Webster's order with `Γ` on top**: the strict order of the keys
`stratumKey`. -/
def stratumRel {s : Seq μ} (Γ : Set (Seq μ)) (a b : PhiIndex s) : Prop :=
  stratumKey Γ a < stratumKey Γ b

theorem stratumKey_injective {s : Seq μ} (Γ : Set (Seq μ)) :
    Function.Injective (stratumKey (s := s) Γ) := by
  intro a b h
  simp only [stratumKey, toLex_inj, Prod.mk.injEq] at h
  exact (Fintype.equivFin (PhiIndex s)).injective (Fin.ext h.2.2)

theorem stratumRel_irrefl {s : Seq μ} (Γ : Set (Seq μ)) (a : PhiIndex s) :
    ¬ stratumRel Γ a a :=
  lt_irrefl _

theorem stratumRel_trans {s : Seq μ} (Γ : Set (Seq μ)) (a b c : PhiIndex s) :
    stratumRel Γ a b → stratumRel Γ b c → stratumRel Γ a c :=
  lt_trans

theorem stratumRel_total {s : Seq μ} (Γ : Set (Seq μ)) (a b : PhiIndex s) (h : a ≠ b) :
    stratumRel Γ a b ∨ stratumRel Γ b a := by
  rcases lt_trichotomy (stratumKey Γ a) (stratumKey Γ b) with h' | h' | h'
  · exact Or.inl h'
  · exact absurd (stratumKey_injective Γ h') h
  · exact Or.inr h'

open scoped Classical in
theorem card_lt_of_phiLT {s : Seq μ} {a b : PhiIndex s} (hab : PhiLT a b) :
    (Finset.univ.filter fun g' : PhiIndex s => PhiLT g' a).card <
      (Finset.univ.filter fun g' : PhiIndex s => PhiLT g' b).card := by
  refine Finset.card_lt_card ⟨fun g hg => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact phiLT_trans _ _ _ hg hab
  · have := hsub (show a ∈ Finset.univ.filter fun g' : PhiIndex s => PhiLT g' b by simp [hab])
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact phiLT_irrefl a this

/-- `stratumRel` contains Webster's order when `Γ` is closed upwards. -/
theorem stratumRel_of_phiLT {s : Seq μ} {Γ : Set (Seq μ)} (hΓ : IsUpperLoadingSet Γ)
    {a b : PhiIndex s} (hab : PhiLT a b) : stratumRel Γ a b := by
  classical
  have hcard := card_lt_of_phiLT hab
  unfold stratumRel stratumKey
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hb : phiBottom s b.1 ∈ Γ
  · by_cases ha : phiBottom s a.1 ∈ Γ
    · refine Or.inr ⟨by simp [ha, hb], ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hcard
    · exact Or.inl (by simp [ha, hb])
  · have ha : phiBottom s a.1 ∉ Γ := fun ha => hb (hΓ ha hab.1)
    refine Or.inr ⟨by simp [ha, hb], ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hcard

/-- The assignments with bottom in `Γ` form an upward closed set for `stratumRel`. -/
theorem mem_of_stratumRel {s : Seq μ} {Γ : Set (Seq μ)} {a b : PhiIndex s}
    (ha : phiBottom s a.1 ∈ Γ) (hab : stratumRel Γ a b) : phiBottom s b.1 ∈ Γ := by
  classical
  by_contra hb
  unfold stratumRel stratumKey at hab
  rw [Prod.Lex.toLex_lt_toLex] at hab
  simp only [ha, hb, ↓reduceIte] at hab
  rcases hab with h | ⟨h, -⟩ <;> omega

end Order

variable {C : QuantumGroup.CartanDatum I}

/-- The layer of `stratumRel` at `φ` is the standard module at the bottom `φ • s`. -/
def stratumLayerEquiv
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) {s : Seq μ} (hs : IsRedOrdered s)
    {Γ : Set (Seq μ)} (hΓ : IsUpperLoadingSet Γ) (g : PhiIndex s) :
    Submodule.layer (stratumRel Γ) (tildePhiSub Q Λ ρ₀ hs) g ≃ₗ[B]
      tildeStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs) :=
  (tildeRelLayerEquiv hQ hR hall G' ρ₀ hρ₀ hc hpos s hs (stratumRel_irrefl Γ)
    (stratumRel_trans Γ) (fun _ _ h => stratumRel_of_phiLT hΓ h) g).symm

/-- **`P̃_Γ` has a standard filtration with labels in `Γ`** (Webster, arXiv:1309.3796v3,
Corollary 5.23, along a linear extension of Webster's order): for `Γ` closed upwards,
`Σ_{φ • s ∈ Γ} T̃^λ x̃_φ` has a finite filtration whose subquotients are standard modules
`S̃_u`, `u ∈ Γ`. Hypotheses on the grading as in `tildeRelLayerEquiv`. Route hypothesis:
`AllFiniteDeltaInjective`. -/
theorem exists_hasFiltration_phiStratumSub
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) {s : Seq μ} (hs : IsRedOrdered s)
    {Γ : Set (Seq μ)} (hΓ : IsUpperLoadingSet Γ) :
    ∃ l : List {t : Seq μ // IsRedOrdered t}, (∀ t ∈ l, t.1 ∈ Γ) ∧
      HasFiltration (fun t : {t : Seq μ // IsRedOrdered t} =>
        ModuleCat.of B (tildeStandard Q Λ t.1 t.2)) l
        (ModuleCat.of B (phiStratumSub Q Λ ρ₀ hs Γ)) := by
  classical
  let S : Finset (PhiIndex s) := Finset.univ.filter fun g => phiBottom s g.1 ∈ Γ
  have hup : ∀ φ ∈ S, ∀ φ', stratumRel Γ φ φ' → φ' ∈ S := by
    intro φ hφ φ' h
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
    exact mem_of_stratumRel hφ h
  obtain ⟨l, hl, hF⟩ := Submodule.hasFiltration_iSup_of_total (R := B)
    (N := tildePhiSub Q Λ ρ₀ hs) (stratumRel_irrefl Γ) (stratumRel_trans Γ)
    (stratumRel_total Γ) S hup
  have e : ∀ g : PhiIndex s, Nonempty ((ModuleCat.of B
      (Submodule.layer (stratumRel Γ) (tildePhiSub Q Λ ρ₀ hs) g)) ≃ₗ[B] ModuleCat.of B
      (tildeStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs))) :=
    fun g => ⟨stratumLayerEquiv hQ hR hall G' ρ₀ hρ₀ hc hpos hs hΓ g⟩
  have hF' : HasFiltration (fun g : PhiIndex s => ModuleCat.of B
      (tildeStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs))) l
      (ModuleCat.of B ↥(⨆ φ ∈ S, tildePhiSub Q Λ ρ₀ hs φ)) :=
    HasFiltration.mono_of_mem hF (fun g _ => e g)
  have heq : (⨆ φ ∈ S, tildePhiSub Q Λ ρ₀ hs φ) = phiStratumSub Q Λ ρ₀ hs Γ :=
    iSup_congr fun g => iSup_congr_Prop (by simp [S]) fun _ => rfl
  let f : PhiIndex s → {t : Seq μ // IsRedOrdered t} := fun g =>
    ⟨phiBottom s g.1, g.isRedOrdered hs⟩
  refine ⟨l.map f, fun t ht => ?_,
    (HasFiltration.relabel (L := fun t : {t : Seq μ // IsRedOrdered t} =>
      ModuleCat.of B (tildeStandard Q Λ t.1 t.2)) f hF').of_equiv (LinearEquiv.ofEq _ _ heq)⟩
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
  have := hl g hg
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

/-- The loadings strictly above `t` form an upward closed set. -/
theorem isUpperLoadingSet_stendhalLT (t : Seq μ) : IsUpperLoadingSet {u | StendhalLT t u} :=
  fun _ _ hu huv => ⟨fun r i => (hu.1 r i).trans (huv r i),
    fun hvt => hu.2 fun r i => (huv r i).trans (hvt r i)⟩

private theorem mem_of_val_mem_map''' {M : Submodule B B} {S : Submodule B M} {x : M}
    (h : (x : B) ∈ S.map M.subtype) : x ∈ S := by
  obtain ⟨y, hy, he⟩ := h
  rwa [show y = x from Subtype.ext he] at hy

/-- `Ũ_t ∩ T̃^λ e(t)` is `J_Γ e(t)` for `Γ = {u | t < u}`, hence `P̃_Γ`. -/
theorem comap_tildeLeftUpper_eq_phiStratumSub (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {t : Seq μ}
    (ht : IsRedOrdered t) :
    (tildeLeftUpper Q Λ ν t ht).comap (lIdeal (StendhalAlgebra.e t ht : B)).subtype =
      phiStratumSub Q Λ ρ ht {u | StendhalLT t u} := by
  rw [← comap_stratumIdeal_eq_phiStratumSub ρ hρ ht (isUpperLoadingSet_stendhalLT t)]
  ext y
  simp only [Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · intro hy
    refine (Submodule.span_le.2 ?_ : tildeLeftUpper Q Λ ν t ht ≤ _) hy
    rintro _ ⟨t', ht', a, hlt, rfl⟩
    rw [mul_assoc]
    exact e_mul_mem_stratumIdeal ht' hlt _
  · intro hy
    have hmul : ∀ z ∈ stratumIdeal Q Λ {u | StendhalLT t u},
        z * StendhalAlgebra.e t ht ∈ tildeLeftUpper Q Λ ν t ht := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, b, hlt, rfl⟩ := hx
        exact Submodule.subset_span ⟨u, hu, b, hlt, rfl⟩
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        rw [smul_eq_mul, mul_assoc]
        exact Submodule.smul_mem _ a hx
    have h := hmul (y : B) hy
    rwa [show ((y : B) * StendhalAlgebra.e t ht) = (y : B) from y.2] at h

/-- **Standard stratification of `T̃^λ`** (Webster, arXiv:1309.3796v3, Corollary 5.23,
condition on projectives): for every red-ordered loading `t`, the kernel `Ũ_t ∩ T̃^λ e(t)` of
`T̃^λ e(t) → S̃_t` has a finite filtration by standard modules `S̃_u` with `u` strictly above
`t`. Hypotheses on the grading as in `tildeRelLayerEquiv`. Route hypothesis:
`AllFiniteDeltaInjective`. -/
theorem exists_hasFiltration_tildeLeftUpper
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) {t : Seq μ} (ht : IsRedOrdered t) :
    ∃ l : List {u : Seq μ // IsRedOrdered u}, (∀ u ∈ l, StendhalLT t u.1) ∧
      HasFiltration (fun u : {u : Seq μ // IsRedOrdered u} =>
        ModuleCat.of B (tildeStandard Q Λ u.1 u.2)) l
        (ModuleCat.of B ((tildeLeftUpper Q Λ ν t ht).comap
          (lIdeal (StendhalAlgebra.e t ht : B)).subtype)) := by
  obtain ⟨l, hl, hF⟩ := exists_hasFiltration_phiStratumSub hQ hR hall G' ρ₀ hρ₀ hc hpos ht
    (isUpperLoadingSet_stendhalLT t)
  exact ⟨l, hl, hF.of_equiv (LinearEquiv.ofEq _ _
    (comap_tildeLeftUpper_eq_phiStratumSub ρ₀ hρ₀ ht).symm)⟩

/-- `T̃^λ e(t)` is projective. -/
theorem projective_lIdeal_e (t : Seq μ) (ht : IsRedOrdered t) :
    Module.Projective B (lIdeal (StendhalAlgebra.e t ht : B)) := by
  let p : B →ₗ[B] lIdeal (StendhalAlgebra.e t ht : B) :=
    { toFun := fun x => ⟨x * StendhalAlgebra.e t ht, by
        change _ * _ * _ = _
        rw [mul_assoc, stendhalAlgebra_e_mul_e_self]⟩
      map_add' := fun x y => Subtype.ext (add_mul x y _)
      map_smul' := fun a x => Subtype.ext (mul_assoc a x _) }
  exact Module.Projective.of_split (lIdeal (StendhalAlgebra.e t ht : B)).subtype p
    (LinearMap.ext fun x => Subtype.ext x.2)

/-- **The projectives `T̃^λ e(t)` are ordered standard covers** (Webster, arXiv:1309.3796v3,
Corollary 5.23): `T̃^λ e(t) → S̃_t` with kernel filtered by standards `S̃_u`, `u > t`.
Hypotheses as in `exists_hasFiltration_tildeLeftUpper`. -/
def tildeOrderedStandardCovers
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) :
    OrderedStandardCovers (fun t : {t : Seq μ // IsRedOrdered t} =>
        ModuleCat.of B (tildeStandard Q Λ t.1 t.2))
      (fun t => (StendhalAlgebra.e t.1 t.2 : B)) (fun s t => StendhalLT s.1 t.1) where
  quotient t := Submodule.mkQ _
  surjective t := Submodule.mkQ_surjective _
  projective t := projective_lIdeal_e t.1 t.2
  kernel t := by
    obtain ⟨l, hl, hF⟩ := exists_hasFiltration_tildeLeftUpper hQ hR hall G' ρ₀ hρ₀ hc hpos t.2
    exact ⟨l, hl, hF.of_equiv (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm)⟩

end Categorification.Stendhal
