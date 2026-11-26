/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams
import Categorification.Algebra.FinrankCounting

/-!
# The layers `P_{≥φ}/P_{>φ}` of the projective `T^λ e(s)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. For a red-ordered loading `s` and a choice `ρ` of reduced words, the diagrams
`x_φ` (`phiElt`, one for each block assignment `φ` of `s`) generate `P = T^λ e(s)`. Put
`P_{>φ} = Σ_{φ < φ'} T^λ x_{φ'}` and `P_{≥φ} = P_{>φ} + T^λ x_φ`, the order being Webster's
order on the bottoms `φ • s`. Then `S_{φ • s} → P_{≥φ}/P_{>φ}`, `[e(φ • s)] ↦ [x_φ]`, is
surjective, and it is an isomorphism as soon as the dimensions of the `S_{φ • s}` add up to the
dimension of `P` (the dimension identity of Lemma 5.19).

## Main results

* `Stendhal.phiLayerMap_surjective`: the surjection `S_{φ • s} → P_{≥φ}/P_{>φ}`.
* `Stendhal.phiLayerMap_bijective_of_finrank_sum`: it is bijective, given the dimension
  identity and finite-dimensionality of `T^λ`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "E" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ) (ν := ν)

variable (ℓ ν) in
/-- The idempotents of the red-ordered loadings sum to one in `T^λ_ν`. -/
theorem sum_seqIdem_eq_one :
    ∑ s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}, seqIdem Q Λ s.1 s.2 = 1 := by
  classical
  have h : (∑ s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 :
      StendhalAlgebra k Q Λ ν) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s},
      StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  simpa only [map_sum, map_one] using congrArg (TensorProductAlgebra.mk Q Λ ν) h

variable {Q Λ}

/-- The block assignments of `s`, as a finite type. -/
abbrev PhiIndex (s : Seq μ) : Type :=
  {g : Fin m → ℕ // g ∈ (assignments s.lbl).toFinset}

omit [DecidableEq I] in
theorem PhiIndex.mem {s : Seq μ} (g : PhiIndex s) : g.1 ∈ assignments s.lbl :=
  List.mem_toFinset.1 g.2

omit [DecidableEq I] in
theorem PhiIndex.isRedOrdered {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    IsRedOrdered (phiBottom s g.1) :=
  isRedOrdered_phiBottom hs g.mem

private theorem e_mul_e_self (t : Seq μ) : E t * E t = E t := by
  simp [StendhalAlgebraAllOrders.e_mul_e]

theorem phiElt_mul_seqIdem (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    phiElt Q Λ ρ hs hg * seqIdem Q Λ s hs = phiElt Q Λ ρ hs hg := by
  rw [phiElt, seqIdem, ← map_mul]
  congr 1
  apply Subtype.ext
  change E _ * _ * E s * E s = E _ * _ * E s
  rw [mul_assoc _ (E s), e_mul_e_self]

theorem seqIdem_mul_phiElt (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    seqIdem Q Λ (phiBottom s g) (isRedOrdered_phiBottom hs hg) * phiElt Q Λ ρ hs hg =
      phiElt Q Λ ρ hs hg := by
  rw [phiElt, seqIdem, ← map_mul]
  congr 1
  apply Subtype.ext
  change E _ * (E _ * _ * E s) = E _ * _ * E s
  rw [← mul_assoc, ← mul_assoc, e_mul_e_self]

variable (Q Λ) in
/-- `x_φ` as an element of `P = T^λ e(s)`. -/
def phiVec (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    lIdeal (seqIdem Q Λ s hs) :=
  ⟨phiElt Q Λ ρ hs g.mem, phiElt_mul_seqIdem ρ hs g.mem⟩

variable (Q Λ) in
/-- The submodule `T^λ x_φ` of `P = T^λ e(s)`. -/
def phiSub (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  Submodule.span A {phiVec Q Λ ρ hs g}

/-- Webster's order on block assignments: the order on their bottoms `φ • s`. -/
def PhiLT {s : Seq μ} (g g' : PhiIndex s) : Prop :=
  StendhalLT (phiBottom s g.1) (phiBottom s g'.1)

theorem phiLT_irrefl {s : Seq μ} (g : PhiIndex s) : ¬ PhiLT g g := fun h => h.2 h.1

theorem phiLT_trans {s : Seq μ} (a b c : PhiIndex s) (hab : PhiLT a b) (hbc : PhiLT b c) :
    PhiLT a c :=
  ⟨fun r i => (hab.1 r i).trans (hbc.1 r i),
    fun hca => hab.2 fun r i => (hbc.1 r i).trans (hca r i)⟩

private theorem mem_of_val_mem_map {M : Submodule A A} {S : Submodule A M} {x : M}
    (h : (x : A) ∈ S.map M.subtype) : x ∈ S := by
  obtain ⟨y, hy, he⟩ := h
  rwa [show y = x from Subtype.ext he] at hy


/-- An element of `P` lying in `e(t) T^λ e(s)` lies in the span of the `T^λ x_{φ'}` with
`t ≤ φ' • s`. -/
theorem mem_iSup_phiSub_of_seqIdem
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {t : Seq μ} (ht : IsRedOrdered t) (y : lIdeal (seqIdem Q Λ s hs))
    (hy : seqIdem Q Λ t ht * (y : A) = (y : A)) :
    y ∈ ⨆ (g : PhiIndex s) (_ : StendhalLE t (phiBottom s g.1)), phiSub Q Λ ρ hs g := by
  refine mem_of_val_mem_map ?_
  have hmem := seqIdem_mul_mul_seqIdem_mem_span_phiElt (Q := Q) (Λ := Λ) ρ hρ hs ht (y : A)
  rw [mul_assoc, show (y : A) * _ = y from y.2, hy] at hmem
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨g, hg, hle, rfl⟩
  refine ⟨phiVec Q Λ ρ hs ⟨g, List.mem_toFinset.2 hg⟩, ?_, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨g, List.mem_toFinset.2 hg⟩
    (Submodule.mem_iSup_of_mem hle (Submodule.subset_span rfl))

/-- **The `x_φ` generate `P = T^λ e(s)`.** -/
theorem iSup_phiSub_eq_top
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) : (⨆ g : PhiIndex s, phiSub Q Λ ρ hs g) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ t : {t : Seq μ // IsRedOrdered t},
      (⟨seqIdem Q Λ t.1 t.2 * y, by
        change _ * _ * _ = _; rw [mul_assoc, y.2]⟩ : lIdeal (seqIdem Q Λ s hs)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (y : A) = ∑ t : {t : Seq μ // IsRedOrdered t}, seqIdem Q Λ t.1 t.2 * y
    rw [← Finset.sum_mul, sum_seqIdem_eq_one, one_mul]
  rw [hy]
  refine Submodule.sum_mem _ fun t _ => ?_
  have := mem_iSup_phiSub_of_seqIdem ρ hs hρ t.2 ⟨seqIdem Q Λ t.1 t.2 * (y : A), by
    change _ * _ * _ = _; rw [mul_assoc, y.2]⟩ (by
      change _ * (_ * _) = _ * _
      rw [← mul_assoc, seqIdem_mul_self])
  refine (iSup_mono (fun g => ?_) : _ ≤ ⨆ g, phiSub Q Λ ρ hs g) this
  exact iSup_le fun _ => le_rfl

variable (Q Λ) in
/-- `P_{>φ}`: the sum of the `T^λ x_{φ'}` with `φ < φ'`. -/
abbrev phiAbove
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) : Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  Submodule.above PhiLT (phiSub Q Λ ρ hs) g

variable (Q Λ) in
/-- `P_{≥φ} = T^λ x_φ + P_{>φ}`. -/
abbrev phiAtLeast
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) : Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  phiSub Q Λ ρ hs g ⊔ phiAbove Q Λ ρ hs g

variable (Q Λ) in
/-- The layer `P_{≥φ}/P_{>φ}`. -/
abbrev phiLayer
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) : Type :=
  phiAtLeast Q Λ ρ hs g ⧸ (phiAbove Q Λ ρ hs g).comap (phiAtLeast Q Λ ρ hs g).subtype

variable (Q Λ) in
/-- The class `[x_φ]` in the layer. -/
def phiLayerGen
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) : phiLayer Q Λ ρ hs g :=
  Submodule.Quotient.mk ⟨phiVec Q Λ ρ hs g, Submodule.mem_sup_left (Submodule.subset_span rfl)⟩

private theorem stendhalLT_of_lt_of_le'' {a b c : Seq μ} (hab : StendhalLT a b)
    (hbc : StendhalLE b c) : StendhalLT a c :=
  ⟨fun r i => (hab.1 r i).trans (hbc r i), fun hca => hab.2 fun r i => (hbc r i).trans (hca r i)⟩

theorem phiLayerGen_annihilated
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) (t : Seq μ) (ht : IsRedOrdered t) (a : A)
    (hlt : StendhalLT (phiBottom s g.1) t) :
    (seqIdem Q Λ t ht * a) • phiLayerGen Q Λ ρ hs g = 0 := by
  rw [phiLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (seqIdem Q Λ t ht * a) • phiVec Q Λ ρ hs g ∈ phiAbove Q Λ ρ hs g
  have h := mem_iSup_phiSub_of_seqIdem ρ hs hρ ht ((seqIdem Q Λ t ht * a) • phiVec Q Λ ρ hs g)
    (by
      change seqIdem Q Λ t ht * (seqIdem Q Λ t ht * a * phiElt Q Λ ρ hs g.mem) =
        seqIdem Q Λ t ht * a * phiElt Q Λ ρ hs g.mem
      rw [← mul_assoc, ← mul_assoc, seqIdem_mul_self])
  refine (iSup₂_le (fun g' hle => ?_) : _ ≤ phiAbove Q Λ ρ hs g) h
  exact le_iSup₂_of_le (f := fun g' (_ : PhiLT g g') => phiSub Q Λ ρ hs g') g'
    (stendhalLT_of_lt_of_le'' hlt hle) le_rfl

variable (Q Λ) in
/-- **The map `S_{φ • s} → P_{≥φ}/P_{>φ}`**, `[e(φ • s)] ↦ [x_φ]`. -/
def phiLayerMap
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    leftStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs) →ₗ[A] phiLayer Q Λ ρ hs g :=
  leftStandardLift _ _ (phiLayerGen Q Λ ρ hs g) fun t ht a hlt =>
    phiLayerGen_annihilated ρ hs hρ g t ht a hlt

theorem phiLayerMap_unit
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    phiLayerMap Q Λ ρ hs hρ g (leftStandardUnit Q Λ _ (g.isRedOrdered hs)) =
      phiLayerGen Q Λ ρ hs g := by
  refine leftStandardLift_unit (k := k) (Q := Q) (Λ := Λ) (ν := ν) _ _ _ ?_ _
  rw [phiLayerGen, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact seqIdem_mul_phiElt (Q := Q) (Λ := Λ) ρ hs g.mem

/-- **Webster, proof of Proposition 5.21**: `S_{φ • s} → P_{≥φ}/P_{>φ}` is surjective. -/
theorem phiLayerMap_surjective
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (g : PhiIndex s) :
    Function.Surjective (phiLayerMap Q Λ ρ hs hρ g) := by
  intro v
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨n, hn, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
  refine ⟨c • leftStandardUnit Q Λ _ (g.isRedOrdered hs), ?_⟩
  rw [map_smul, phiLayerMap_unit, phiLayerGen, ← Submodule.Quotient.mk_smul, eq_comm,
    Submodule.Quotient.eq]
  change (⟨c • phiVec Q Λ ρ hs g + b, hy⟩ - c • ⟨phiVec Q Λ ρ hs g, _⟩ :
    phiAtLeast Q Λ ρ hs g) ∈ _
  rw [Submodule.mem_comap]
  convert hb using 1
  change c • phiVec Q Λ ρ hs g + b - c • phiVec Q Λ ρ hs g = b
  abel

section Dimension

private instance finiteDimensional_sub [FiniteDimensional k A] (M : Submodule A A) : FiniteDimensional k M :=
  Module.Finite.of_injective (M.subtype.restrictScalars k) Subtype.val_injective

private instance finiteDimensional_subsub [FiniteDimensional k A] (M : Submodule A A) (S : Submodule A M) :
    FiniteDimensional k S :=
  Module.Finite.of_injective ((M.subtype.comp S.subtype).restrictScalars k)
    (Subtype.val_injective.comp Subtype.val_injective)

private instance finiteDimensional_quot {M : Type*} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] (S : Submodule A M) :
    FiniteDimensional k (M ⧸ S) :=
  Module.Finite.of_surjective (S.mkQ.restrictScalars k) (Submodule.mkQ_surjective S)

theorem finrank_phiLayer [FiniteDimensional k A]
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : PhiIndex s) :
    Module.finrank k (phiLayer Q Λ ρ hs g) =
      Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hs) g := by
  set p := (phiAbove Q Λ ρ hs g).comap (phiAtLeast Q Λ ρ hs g).subtype
  have hq : Module.finrank k (phiAtLeast Q Λ ρ hs g ⧸ p.restrictScalars k) +
      Module.finrank k (p.restrictScalars k) = Module.finrank k (phiAtLeast Q Λ ρ hs g) :=
    Submodule.finrank_quotient_add_finrank _
  have h1 : Module.finrank k (phiAtLeast Q Λ ρ hs g ⧸ p.restrictScalars k) =
      Module.finrank k (phiLayer Q Λ ρ hs g) :=
    (Submodule.Quotient.restrictScalarsEquiv k p).finrank_eq
  have h2 : Module.finrank k p = Module.finrank k (phiAbove Q Λ ρ hs g) :=
    ((Submodule.comapSubtypeEquivOfLe le_sup_right).restrictScalars k).finrank_eq
  change Module.finrank k _ + Module.finrank k p = _ at hq
  unfold Submodule.layerRank Submodule.finrankK
  change _ = Module.finrank k (phiAtLeast Q Λ ρ hs g) - Module.finrank k (phiAbove Q Λ ρ hs g)
  omega

/-- **Webster, proof of Proposition 5.21**: if the dimensions of the standard modules
`S_{φ • s}` add up to the dimension of `P = T^λ e(s)`, then `S_{φ • s} → P_{≥φ}/P_{>φ}` is an
isomorphism for every block assignment `φ`. -/
theorem phiLayerMap_bijective_of_finrank_sum [FiniteDimensional k A]
    (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hD : ∑ g : PhiIndex s, Module.finrank k (leftStandard Q Λ _ (g.isRedOrdered hs)) =
      Module.finrank k (lIdeal (seqIdem Q Λ s hs)))
    (g : PhiIndex s) : Function.Bijective (phiLayerMap Q Λ ρ hs hρ g) := by
  classical
  have hle : ∀ g' : PhiIndex s, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hs) g' ≤
      Module.finrank k (leftStandard Q Λ _ (g'.isRedOrdered hs)) := fun g' => by
    rw [← finrank_phiLayer]
    exact LinearMap.finrank_le_finrank_of_surjective (f := (phiLayerMap Q Λ ρ hs hρ g').restrictScalars k)
      (phiLayerMap_surjective (Q := Q) (Λ := Λ) ρ hs hρ g')
  have heq := Submodule.layerRank_eq_of_sum_eq (k := k) PhiLT (phiSub Q Λ ρ hs) phiLT_irrefl
    phiLT_trans (iSup_phiSub_eq_top (Q := Q) (Λ := Λ) ρ hs hρ) _ hle (by
      rw [hD]
      unfold Submodule.finrankK
      rw [Submodule.restrictScalars_top, finrank_top]) g
  rw [← finrank_phiLayer] at heq
  have hsurj := phiLayerMap_surjective (Q := Q) (Λ := Λ) ρ hs hρ g
  refine ⟨?_, hsurj⟩
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm
    (f := (phiLayerMap Q Λ ρ hs hρ g).restrictScalars k)).2 hsurj
  exact this

end Dimension

end Categorification.Stendhal

end
