/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverNegligible
import Categorification.KLR.CyclotomicAction.Global

/-!
# Red-negligible 2-morphisms of the cyclotomic family

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward
relations of the double calculus are checked on the cyclotomic family of the
extended datum, where red strands are cyclotomic inductions at red colours.
The image of a relation is a relation of the Cautis–Lauda calculus plus terms
carrying a dot on a red strand. This file isolates the ideal containing those
terms.

Fix a set `Rd` of red colours. A 2-morphism `α` between functors into the
weight space at `y` is *red-negligible* (`RedNegligible`) when, for every
object and every block of weight `y` in which each red colour occurs at most
once, its component factors through the central coloured-dot actions of the
red colours occurring exactly once. Red-negligible 2-morphisms form an ideal
under vertical composition, are stable under whiskering on the source side,
under whiskering by cyclotomic induction at any colour, and under whiskering
by cyclotomic restriction at non-red colours; the dot on a red strand is
red-negligible (`redNegligible_globalDot`). At the tensor-product block the
projection kills their components
(`cyclotomicCover_project_eq_zero_of_mem_negligible`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR KLRAlgebra KLR.CyclotomicAction TwoRep
  QuantumGroup Bicategory

universe u v w u₁ v₁ w₁ w₂ u₂ v₂

/-! ### Negligible morphisms and biproducts -/

section Biproduct

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] [Preadditive 𝒞] {E : Set (𝟭 𝒞 ⟶ 𝟭 𝒞)}

theorem negligible_mono {E' : Set (𝟭 𝒞 ⟶ 𝟭 𝒞)} (h : E ⊆ E') {M N : 𝒞} {f : M ⟶ N}
    (hf : f ∈ negligible E M N) : f ∈ negligible E' M N := by
  refine AddSubgroup.closure_mono ?_ hf
  rintro g ⟨η, hη, h', rfl⟩
  exact ⟨η, h hη, h', rfl⟩

/-- A biproduct of negligible maps is negligible. -/
theorem biproduct_map_mem_negligible [HasFiniteBiproducts 𝒞] {J : Type w₁} [Finite J]
    {f g : J → 𝒞} (φ : ∀ j, f j ⟶ g j) (hφ : ∀ j, φ j ∈ negligible E (f j) (g j)) :
    biproduct.map φ ∈ negligible E (⨁ f) (⨁ g) := by
  have := Fintype.ofFinite J
  have e : biproduct.map φ = ∑ j, biproduct.π f j ≫ φ j ≫ biproduct.ι g j := by
    conv_lhs => rw [← Category.id_comp (biproduct.map φ)]
    rw [show 𝟙 (⨁ f) = ∑ j, biproduct.π f j ≫ biproduct.ι f j from
      (IsBilimit.total (biproduct.isBilimit f)).symm, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Category.assoc, biproduct.ι_map]
  rw [e]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  exact negligible_comp_left _ (negligible_comp_right _ (hφ j))

end Biproduct

/-! ### Blockwise negligibility on products of categories -/

section Pi

variable {B : Type w₁} {𝒞 : B → Type u₁} [∀ β, Category.{v₁} (𝒞 β)]
  [∀ β, Preadditive (𝒞 β)] (P : B → Prop) (E : ∀ β, Set (𝟭 (𝒞 β) ⟶ 𝟭 (𝒞 β)))

/-- A morphism of a product of categories is negligible on the blocks
satisfying `P`. -/
def PiNegligible {M N : ∀ β, 𝒞 β} (f : M ⟶ N) : Prop :=
  ∀ β, P β → f β ∈ negligible (E β) (M β) (N β)

variable {P E}

namespace PiNegligible

theorem comp_left {L M N : ∀ β, 𝒞 β} (g : L ⟶ M) {f : M ⟶ N} (hf : PiNegligible P E f) :
    PiNegligible P E (g ≫ f) := fun β hβ => negligible_comp_left (g β) (hf β hβ)

theorem comp_right {L M N : ∀ β, 𝒞 β} {f : L ⟶ M} (g : M ⟶ N) (hf : PiNegligible P E f) :
    PiNegligible P E (f ≫ g) := fun β hβ => negligible_comp_right (g β) (hf β hβ)

theorem zero (M N : ∀ β, 𝒞 β) : PiNegligible P E (0 : M ⟶ N) := fun β _ =>
  (negligible (E β) (M β) (N β)).zero_mem

theorem add {M N : ∀ β, 𝒞 β} {f g : M ⟶ N} (hf : PiNegligible P E f)
    (hg : PiNegligible P E g) : PiNegligible P E (f + g) := fun β hβ =>
  (negligible (E β) (M β) (N β)).add_mem (hf β hβ) (hg β hβ)

theorem neg {M N : ∀ β, 𝒞 β} {f : M ⟶ N} (hf : PiNegligible P E f) :
    PiNegligible P E (-f) := fun β hβ => (negligible (E β) (M β) (N β)).neg_mem (hf β hβ)

theorem smul {K : Type*} [Semiring K] [∀ β, Linear K (𝒞 β)] (c : K) {M N : ∀ β, 𝒞 β}
    {f : M ⟶ N} (hf : PiNegligible P E f) : PiNegligible P E (c • f) := fun β hβ => by
  change c • f β ∈ _
  rw [← Category.comp_id (f β), ← Linear.comp_smul]
  exact negligible_comp_right _ (hf β hβ)

/-- Block-sum functors carry negligible maps to negligible maps when each
block functor does. -/
theorem blockSum {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
    {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] [∀ a, Preadditive (C a)]
    {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)] [∀ d, Preadditive (D d)]
    [∀ d, Finite {a // s a = d}] [∀ d, HasFiniteBiproducts (D d)]
    (L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d)
    {PC : A → Prop} {EC : ∀ a, Set (𝟭 (C a) ⟶ 𝟭 (C a))}
    {PD : Dd → Prop} {ED : ∀ d, Set (𝟭 (D d) ⟶ 𝟭 (D d))}
    (hP : ∀ a d, s a = d → PD d → PC a)
    (hL : ∀ a d (h : s a = d), PD d → ∀ {M N : C a} (f : M ⟶ N),
      f ∈ negligible (EC a) M N → (L a d h).map f ∈ negligible (ED d) _ _)
    {M N : ∀ a, C a} {f : M ⟶ N} (hf : PiNegligible PC EC f) :
    PiNegligible PD ED ((TwoRep.blockSum s L).map f) := fun d hd =>
  biproduct_map_mem_negligible _ fun (q : {a // s a = d}) =>
    hL q.1 d q.2 hd (f q.1) (hf q.1 (hP q.1 d q.2 hd))

/-- Block-restriction functors carry negligible maps to negligible maps when
each block functor does. -/
theorem blockRes {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
    {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] [∀ a, Preadditive (C a)]
    {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)] [∀ d, Preadditive (D d)]
    (R : ∀ (a : A) (d : Dd), s a = d → D d ⥤ C a)
    {PC : A → Prop} {EC : ∀ a, Set (𝟭 (C a) ⟶ 𝟭 (C a))}
    {PD : Dd → Prop} {ED : ∀ d, Set (𝟭 (D d) ⟶ 𝟭 (D d))}
    (hP : ∀ a, PC a → PD (s a))
    (hR : ∀ a, PC a → ∀ {M N : D (s a)} (f : M ⟶ N),
      f ∈ negligible (ED (s a)) M N → (R a (s a) rfl).map f ∈ negligible (EC a) _ _)
    {M N : ∀ d, D d} {f : M ⟶ N} (hf : PiNegligible PD ED f) :
    PiNegligible PC EC ((TwoRep.blockRes s R).map f) := fun a ha =>
  hR a ha (f (s a)) (hf (s a) (hP a ha))

/-- Blockwise natural transformations whose components are negligible
assemble to a block-sum transformation with negligible components. -/
theorem blockSumMap {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
    {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] [∀ a, Preadditive (C a)]
    {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)] [∀ d, Preadditive (D d)]
    [∀ d, Finite {a // s a = d}] [∀ d, HasFiniteBiproducts (D d)]
    {L L' : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
    (α : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⟶ L' a d h)
    {PD : Dd → Prop} {ED : ∀ d, Set (𝟭 (D d) ⟶ 𝟭 (D d))}
    (hα : ∀ a d (h : s a = d), PD d → ∀ M : C a,
      (α a d h).app M ∈ negligible (ED d) _ _)
    (M : ∀ a, C a) : PiNegligible PD ED ((TwoRep.blockSumMap s α).app M) := fun d hd =>
  biproduct_map_mem_negligible _ fun (q : {a // s a = d}) => hα q.1 d q.2 hd (M q.1)

end PiNegligible

end Pi

/-! ### Red-negligible maps of cyclotomic blocks -/

section Blocks

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (hc : ∀ δ c (z : CycKLR k Q a δ), Commute z (cyclotomicColourDot Q a δ c))
  (Rd : Set I)

/-- Each colour of `Rd` occurs at most once. -/
def RedBounded (β : Multiset I) : Prop := ∀ c ∈ Rd, β.count c ≤ 1

/-- The colours of `Rd` occurring exactly once. -/
def redOnce (β : Multiset I) : Set I := {c | c ∈ Rd ∧ β.count c = 1}

/-- The central coloured-dot actions of the red colours occurring once. -/
abbrev redDotActions (β : Multiset I) :=
  colourDotActions.{u, v, w} Q a hc (redOnce Rd β) β

variable {Q a hc Rd}

theorem RedBounded.of_cons {i : I} {β : Multiset I} (h : RedBounded Rd ({i} + β)) :
    RedBounded Rd β := fun c hc =>
  (Multiset.count_le_of_le c (Multiset.le_add_left β {i})).trans (h c hc)

theorem RedBounded.cons {i : I} (hi : i ∉ Rd) {β : Multiset I} (h : RedBounded Rd β) :
    RedBounded Rd ({i} + β) := fun c hc => by
  have hci : c ≠ i := fun e => hi (e ▸ hc)
  simpa [Multiset.count_singleton, hci] using h c hc

/-- Cyclotomic induction at any colour preserves red-negligible maps, when
the result is red-bounded. -/
theorem ind_map_mem_redNegligible (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (hδ : RedBounded Rd δ) {M N : ModuleCat.{max (max u v) w} (CycKLR k Q a β)}
    {f : M ⟶ N} (hf : f ∈ negligible (redDotActions Q a hc Rd β) M N) :
    (ind Q a i h).map f ∈ negligible (redDotActions Q a hc Rd δ) _ _ := by
  subst h
  have hi : i ∉ redOnce Rd β := fun ⟨hiR, hβ⟩ => by
    have := hδ i hiR
    simp [hβ] at this
  refine negligible_mono ?_ (ind_map_mem_negligible i hi (fun c hc => hc.2) hf)
  rintro η ⟨c, ⟨hcR, hcβ⟩, rfl⟩
  have hci : c ≠ i := fun e => hi (e ▸ ⟨hcR, hcβ⟩)
  exact ⟨c, ⟨hcR, by simpa [Multiset.count_singleton, hci] using hcβ⟩, rfl⟩

/-- Cyclotomic restriction at a non-red colour preserves red-negligible
maps. -/
theorem res_map_mem_redNegligible (i : I) (hiR : i ∉ Rd) {β δ : Multiset I}
    (h : {i} + β = δ) {M N : ModuleCat.{max (max u v) w} (CycKLR k Q a δ)}
    {f : M ⟶ N} (hf : f ∈ negligible (redDotActions Q a hc Rd δ) M N) :
    (res Q a i h).map f ∈ negligible (redDotActions Q a hc Rd β) _ _ := by
  subst h
  have hi : i ∉ redOnce Rd β := fun hi => hiR hi.1
  refine res_map_mem_negligible i hi (fun c hc => hc.2) (negligible_mono ?_ hf)
  rintro η ⟨c, ⟨hcR, hcβ⟩, rfl⟩
  have hci : c ≠ i := fun e => hiR (e ▸ hcR)
  exact ⟨c, ⟨hcR, by simpa [Multiset.count_singleton, hci] using hcβ⟩, rfl⟩

private theorem unique_position_of_count {c : I} {β : Multiset I} (hc : β.count c ≤ 1)
    (s : Seq β) (x y : Fin β.card) (hx : s.lbl x = c) (hy : s.lbl y = c) : x = y := by
  rw [← s.2, Multiset.count_map] at hc
  have hf : (Finset.univ.filter (fun x => c = s.lbl x)).card ≤ 1 := hc
  exact Finset.card_le_one_iff.mp hf (by simp [hx]) (by simp [hy])

/-- The dot on a red strand is red-negligible when the result is
red-bounded. -/
theorem dot_app_mem_redNegligible {i : I} (hiR : i ∈ Rd) {β δ : Multiset I}
    (h : {i} + β = δ) (hδ : RedBounded Rd δ)
    (M : ModuleCat.{max (max u v) w} (CycKLR k Q a β)) :
    (dot Q a i h).app M ∈ negligible (redDotActions Q a hc Rd δ) _ _ := by
  have hcount : δ.count i = 1 := by
    refine le_antisymm (hδ i hiR) ?_
    rw [← h]
    simp
  rw [dot_app_eq_centralModuleAction Q a i h
    (unique_position_of_count (hδ i hiR)) (hc δ i), ← Category.id_comp
      ((centralModuleAction _ (hc δ i)).app _)]
  exact comp_mem_negligible (E := redDotActions Q a hc Rd δ) _ ⟨i, ⟨hiR, hcount⟩, rfl⟩ _

end Blocks

/-! ### Red-negligible 2-morphisms of the cyclotomic family -/

section Global

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (hc : ∀ δ c (z : CycKLR k Q a δ), Commute z (cyclotomicColourDot Q a δ c))
  (Rd : Set I)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- **Red-negligible 2-morphisms.** On every object, the component at each
red-bounded block of the target weight space factors through the central
dot actions of the red colours occurring once. -/
def RedNegligible {Z : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k} {y : X}
    {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} (α : F ⟶ G) : Prop :=
  ∀ M, PiNegligible (fun β : WeightBlocks RD Λ y => RedBounded Rd β.1)
    (fun β => redDotActions.{u, v, w} Q a hc Rd β.1) (α.hom.app M)

variable {Q a hc Rd RD Λ}
variable {Z : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k}

namespace RedNegligible

variable {x y : X}

theorem comp_left {F G H : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} (θ : F ⟶ G) {α : G ⟶ H}
    (hα : RedNegligible Q a hc Rd RD Λ α) : RedNegligible Q a hc Rd RD Λ (θ ≫ α) :=
  fun M => (hα M).comp_left (θ.hom.app M)

theorem comp_right {F G H : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α : F ⟶ G} (θ : G ⟶ H)
    (hα : RedNegligible Q a hc Rd RD Λ α) : RedNegligible Q a hc Rd RD Λ (α ≫ θ) :=
  fun M => (hα M).comp_right (θ.hom.app M)

theorem zero (F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y) :
    RedNegligible Q a hc Rd RD Λ (0 : F ⟶ G) :=
  fun M => PiNegligible.zero (F.obj.obj M) (G.obj.obj M)

theorem add {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α β : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) (hβ : RedNegligible Q a hc Rd RD Λ β) :
    RedNegligible Q a hc Rd RD Λ (α + β) :=
  fun M => (hα M).add (hβ M)

theorem neg {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) : RedNegligible Q a hc Rd RD Λ (-α) :=
  fun M => (hα M).neg

theorem sub {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α β : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) (hβ : RedNegligible Q a hc Rd RD Λ β) :
    RedNegligible Q a hc Rd RD Λ (α - β) := by
  rw [sub_eq_add_neg]
  exact hα.add hβ.neg

theorem smul {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} (c : k) {α : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) : RedNegligible Q a hc Rd RD Λ (c • α) :=
  fun M => (hα M).smul c

theorem sum {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {ι : Type*} (s : Finset ι)
    {α : ι → (F ⟶ G)} (hα : ∀ i ∈ s, RedNegligible Q a hc Rd RD Λ (α i)) :
    RedNegligible Q a hc Rd RD Λ (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero F G
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hα j (Finset.mem_insert_self j s)).add
      (ih fun i hi => hα i (Finset.mem_insert_of_mem hi))

/-- Whiskering on the source side preserves red-negligibility. -/
theorem whiskerLeft {Z' : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k}
    (H : Z' ⟶ Z) {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) : RedNegligible Q a hc Rd RD Λ (H ◁ α) :=
  fun M β hβ => by
    have := hα (H.obj.obj M) β hβ
    exact this

/-- Whiskering by cyclotomic induction at any colour preserves
red-negligibility. -/
theorem whiskerRight_globalE {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ x} {α : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) (i : I) (h : x + RD.iX i = y) :
    RedNegligible Q a hc Rd RD Λ (α ▷ globalE Q a RD Λ i h) := fun M β hβ => by
  have := PiNegligible.blockSum (blockSucc RD Λ i h) (indBlock Q a RD Λ i h)
    (PC := fun β : WeightBlocks RD Λ x => RedBounded Rd β.1)
    (EC := fun β => redDotActions.{u, v, w} Q a hc Rd β.1)
    (PD := fun β : WeightBlocks RD Λ y => RedBounded Rd β.1)
    (ED := fun β => redDotActions.{u, v, w} Q a hc Rd β.1)
    (fun _ _ hβ hδ => RedBounded.of_cons (blockSucc_eq RD Λ i hβ ▸ hδ))
    (fun _ _ _ hδ _ _ _ hf => ind_map_mem_redNegligible i _ hδ hf) (hα M)
  exact this β hβ

/-- Whiskering by cyclotomic restriction at a non-red colour preserves
red-negligibility. -/
theorem whiskerRight_globalF {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} {α : F ⟶ G}
    (hα : RedNegligible Q a hc Rd RD Λ α) (i : I) (hi : i ∉ Rd) (h : x + RD.iX i = y) :
    RedNegligible Q a hc Rd RD Λ (α ▷ globalF Q a RD Λ i h) := fun M β hβ => by
  have := PiNegligible.blockRes (blockSucc RD Λ i h) (resBlock Q a RD Λ i h)
    (PC := fun β : WeightBlocks RD Λ x => RedBounded Rd β.1)
    (EC := fun β => redDotActions.{u, v, w} Q a hc Rd β.1)
    (PD := fun β : WeightBlocks RD Λ y => RedBounded Rd β.1)
    (ED := fun β => redDotActions.{u, v, w} Q a hc Rd β.1)
    (fun _ hβ => RedBounded.cons hi hβ)
    (fun _ _ _ _ _ hf => res_map_mem_redNegligible i hi _ hf) (hα M)
  exact this β hβ

end RedNegligible

/-- **The dot on a red strand is red-negligible.** -/
theorem redNegligible_globalDot {i : I} (hi : i ∈ Rd) {x y : X} (h : x + RD.iX i = y) :
    RedNegligible Q a hc Rd RD Λ (globalDot.{u, v, w} Q a RD Λ i h) := fun M β hβ => by
  have := PiNegligible.blockSumMap (blockSucc RD Λ i h)
    (fun _ _ hβ' => dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ'))
    (PD := fun β : WeightBlocks RD Λ y => RedBounded Rd β.1)
    (ED := fun β => redDotActions.{u, v, w} Q a hc Rd β.1)
    (fun _ _ _ hδ N => dot_app_mem_redNegligible hi _ hδ N) M
  exact this β hβ

end Global

end Categorification.Stendhal
