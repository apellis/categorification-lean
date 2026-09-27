/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CisBub
import Categorification.TwoRep.UpDownCrossing
import Categorification.TwoRep.EndE

/-!
# CL Lemma 3.14: endomorphisms of `E 1_n` are dots times bubbles

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.14 (`lem:main`), the case `n ≥ -1`: "Suppose `m < 2|n+2|` and
`f ∈ Hom^m(E 1_n, E 1_n)`. If `n ≥ -1` then `f` is of the form `∑_i (f_i on 1_{n+2}) · (i dots)`
where `f_i ∈ Hom^{m-2i}(1_{n+2}, 1_{n+2})`" (eq. `eq:main1`).

**Formulation.** The existential form is exactly the surjectivity of the `k`-linear map

`Ψ : ⊕_{i<n+2} Hom(1_{n+2}, 1_{n+2}⟨m-2i⟩) → Hom(E 1_n, E 1_n⟨m⟩)`,
`(f_i)_i ↦ ∑_i dotsBub m i (f_i)`, `dotsBub m i g = (bubble g next to E 1_n) ∘ (i dots)`

(`Ψ`, `dotsBub`; the bubble `cisBub (E 1_n) g` is `g` placed on the `1_{n+2}`-side of the strand,
`CisBub.lean`). The theorem is `lemMain_surjective`. Indices `i ≥ n + 2` are not needed since
`Hom(1_{n+2}, 1_{n+2}⟨m-2i⟩) = 0` for `m - 2i < 0` (CL's sum is over all `i`).

**Proof.** The dimension count `EndE.lemMain_finrank` says both sides have the same dimension, so
it suffices to prove `Ψ` injective. Given `Ψ f = 0`, whisker with `F 1_n` and compose with the
cup `1_{n+2}⟨n+1⟩ → E F 1_{n+2}` and the projections onto the summands `1_{n+2}⟨n+1-2j⟩` of
`E F 1_{n+2}`: the "coefficient" of `dotsBub m i g` is `(g shifted) ∘ (cup ≫ dot^i ≫ π_j)`
(`coefSh_dotsBub`: the bubble moves through the cup by `cisBub_natural`, i.e. the interchange law,
and through the whiskering by `shWhiskerLeft_cisBub`, the associator coherence), and
`cup ≫ dot^i ≫ π_j` vanishes for `j > i` and is an isomorphism for `j = i` (`bubble_aux`, from
Lemma 3.6 at the weight `n + 2`). Descending induction on `i` gives `f_i = 0`.

CL's proof instead transports `f` by the left adjoint `(E 1_n)_L` (Proposition 3.9 at `n`); the
argument here needs the adjoint induction hypothesis (3.2) only at the weights `> n` (through
Lemma 3.6 at `n + 2` and the dimension count), and the two coherence mixins `ShiftInterchange`
and `ShiftAssoc`. The mirror statement for `n ≤ -1` (eq. `eq:main2`) is not formalized.

Indexing: `n = wt (r + 1)`, `E 1_n = E (r + 1)`, `1_{n+2} = 𝟙 (obj (r + 1 + 1))`,
`E F 1_{n+2} = F (r + 1) ≫ E (r + 1)` with `e : EFDecomp (r + 1)`.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B) (r : ℤ)

/-! ## Dots times bubbles -/

/-- **A dots-times-bubbles endomorphism of `E 1_n`**: the bubble `g : 1_{n+2} → 1_{n+2}⟨m-2i⟩`
placed on the `1_{n+2}`-side of the strand, followed by `i` dots (CL eq. `eq:main1`, one term). -/
def dotsBub (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * (i : ℤ)⟧) :
    S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧ :=
  (cisBubSh (S.E (r + 1)) g).comp (shPow (S.dot (r + 1)) i) (by ring)

/-- `dotsBub m i` as a `k`-linear map. -/
def dotsBubLin (m : ℤ) (i : ℕ) :
    (𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * (i : ℤ)⟧) →ₗ[k]
      (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) where
  toFun := S.dotsBub r m i
  map_add' g g' := by
    simp only [dotsBub, cisBubSh, cisBub_add]
    exact ShiftedHom.add_comp _ _ _ _
  map_smul' c g := by
    simp only [dotsBub, cisBubSh, cisBub_smul, RingHom.id_apply]
    exact ShiftedHom.smul_comp' _ _ _ _

/-- **CL's map** `Ψ : ⊕_{i<n+2} Hom(1_{n+2}, 1_{n+2}⟨m-2i⟩) → Hom(E 1_n, E 1_n⟨m⟩)`,
`(f_i) ↦ ∑_i (bubble f_i) ∘ (i dots)`; Lemma 3.14 is its surjectivity. -/
def Ψ (m : ℤ) :
    (∀ i : Fin (S.wt (r + 1 + 1)).toNat,
      (𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) →ₗ[k]
      (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :=
  ∑ i : Fin (S.wt (r + 1 + 1)).toNat, (S.dotsBubLin r m i).comp (LinearMap.proj i)

theorem Ψ_apply (m : ℤ)
    (f : ∀ i : Fin (S.wt (r + 1 + 1)).toNat,
      (𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) :
    S.Ψ r m f = ∑ i : Fin (S.wt (r + 1 + 1)).toNat, S.dotsBub r m i (f i) := by
  simp [Ψ, LinearMap.sum_apply, dotsBubLin]

/-! ## Coefficients along the cup and the summands of `E F 1_{n+2}` -/

variable {S r} (e : S.EFDecomp (r + 1))

/-- The coefficient of `φ : E 1_n → E 1_n⟨m⟩` in the summand `1_{n+2}⟨n+1-2j⟩`:
`cup ≫ (F ◁ φ) ≫ π_j`. -/
def coefSh (j : ℕ) {m : ℤ} (φ : S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :
    ShiftedHom (S.oneShift (r + 1) 0) (S.oneShift (r + 1) j) m :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (ι e 0)).comp
    ((shWhiskerLeft (S.F (r + 1)) (φ : ShiftedHom (S.E (r + 1)) (S.E (r + 1)) m)).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl (π e j)) (zero_add m)) (add_zero m)

omit [GradedBicategory.IsLinear B k] in
theorem coefSh_add (j : ℕ) {m : ℤ} (φ φ' : S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) :
    coefSh e j (φ + φ') = coefSh e j φ + coefSh e j φ' := by
  simp only [coefSh, shWhiskerLeft, ShiftedHom.map, ShiftedHom.comp, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

omit [GradedBicategory.IsLinear B k] in
theorem coefSh_zero (j : ℕ) {m : ℤ} : coefSh e j (0 : S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) = 0 := by
  simp only [coefSh, shWhiskerLeft, ShiftedHom.map, ShiftedHom.comp, Functor.map_zero, zero_comp,
    comp_zero]

/-- The coefficient map as an additive homomorphism. -/
def coefHom (j : ℕ) (m : ℤ) :
    (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) →+ ShiftedHom (S.oneShift (r + 1) 0) (S.oneShift (r + 1) j) m :=
  AddMonoidHom.mk' (coefSh e j) (coefSh_add e j)

/-- `cup ≫ dot^i ≫ π_j` as a shifted 2-morphism of degree `2i`. -/
def Cij (i j : ℕ) : ShiftedHom (S.oneShift (r + 1) 0) (S.oneShift (r + 1) j) ((i : ℤ) * 2) :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl (ι e 0)).comp
    ((shPow (S.dotEF (r + 1)) i).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (π e j)) (zero_add _))
    (add_zero _)

omit [GradedBicategory.IsLinear B k] in
theorem Cij_eq (i j : ℕ) :
    (Cij e i j : S.oneShift (r + 1) 0 ⟶ (S.oneShift (r + 1) j)⟦(i : ℤ) * 2⟧) =
      cupDots e i ≫ (π e j)⟦(i : ℤ) * 2⟧' := by
  rw [Cij, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  simp only [cupDots, Category.assoc]

variable [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssoc B]

omit [GradedBicategory.IsLinear B k] in
/-- **The coefficient of a dots-times-bubbles term**: the bubble passes through the cup and the
whiskering, leaving `(g shifted) ∘ (cup ≫ dot^i ≫ π_j)`. -/
theorem coefSh_dotsBub (j : ℕ) (m : ℤ) (i : ℕ)
    (g : 𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * (i : ℤ)⟧) :
    coefSh e j (S.dotsBub r m i g) =
      (cisBubSh (S.oneShift (r + 1) 0) g).comp (Cij e i j) (by ring) := by
  have hnat : (ShiftedHom.mk₀ (0 : ℤ) rfl (ι e 0)).comp
      (cisBubSh (S.F (r + 1) ≫ S.E (r + 1)) g) (add_zero _) =
      (cisBubSh (S.oneShift (r + 1) 0) g).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (ι e 0))
        (zero_add _) := by
    rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
    exact cisBub_natural (ι e 0) g
  rw [coefSh, dotsBub, Cij]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (ι e 0)).comp
    ((shWhiskerLeft (S.F (r + 1)) ((cisBubSh (S.E (r + 1)) g).comp
      (shPow (S.dot (r + 1)) i) (by ring))).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (π e j))
      (zero_add m)) (add_zero m) = _
  rw [shWhiskerLeft_comp, shWhiskerLeft_cisBub, shWhiskerLeft_shPow,
    ShiftedHom.comp_assoc _ _ _ (by ring : (i : ℤ) * 2 + (m - 2 * (i : ℤ)) = m)
      (by norm_num : (0 : ℤ) + (i : ℤ) * 2 = (i : ℤ) * 2) (by ring),
    ← ShiftedHom.comp_assoc _ _ _ (by ring : m - 2 * (i : ℤ) + 0 = m - 2 * (i : ℤ))
      (by ring : (i : ℤ) * 2 + (m - 2 * (i : ℤ)) = m) (by ring),
    hnat, ShiftedHom.comp_assoc _ _ _ (by ring : (0 : ℤ) + (m - 2 * (i : ℤ)) = m - 2 * (i : ℤ))
      (by ring : (i : ℤ) * 2 + 0 = (i : ℤ) * 2) (by ring)]
  rfl

/-! ## Lemma 3.14 -/

variable [∀ a b : B, HomFinite k (a ⟶ b)]

omit [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssoc B] in
/-- `cup ≫ dot^i ≫ π_j = 0` for `j > i`. -/
theorem Cij_eq_zero (hn : 0 ≤ S.wt (r + 1 + 1)) (hyp : ∀ r', r + 1 + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) {i j : ℕ} (hi : i < (S.wt (r + 1 + 1)).toNat) (hij : i < j) :
    Cij e i j = 0 := by
  rw [Cij_eq]
  exact (bubble_aux e hn hyp hd i hi).1 j hij

omit [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssoc B] in
/-- `cup ≫ dot^i ≫ π_i` is an isomorphism. -/
theorem isIso_Cij_self (hn : 0 ≤ S.wt (r + 1 + 1)) (hyp : ∀ r', r + 1 + 1 < r' → S.AdjHyp r')
    (hd : DotNondeg e) {i : ℕ} (hi : i < (S.wt (r + 1 + 1)).toNat) :
    IsIso (Cij e i i : S.oneShift (r + 1) 0 ⟶ (S.oneShift (r + 1) i)⟦(i : ℤ) * 2⟧) := by
  rw [Cij_eq]
  exact (bubble_aux e hn hyp hd i hi).2

/-- **CL Lemma 3.14** (`lem:main`, eq. `eq:main1`): for `n = wt (r + 1) ≥ -1` and
`m < 2(n + 2)`, assuming the adjoint induction hypothesis (3.2) for the weights `> n`, every
`f : E 1_n → E 1_n⟨m⟩` is a sum `∑_i (bubble f_i) ∘ (i dots)` with
`f_i : 1_{n+2} → 1_{n+2}⟨m-2i⟩`: the map `Ψ` is surjective. -/
theorem lemMain_surjective [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hr : -1 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {m : ℤ} (hm : m < 2 * (S.wt (r + 1) + 2)) :
    Function.Surjective (S.Ψ r m) := by
  have hw : S.wt (r + 1 + 1) = S.wt (r + 1) + 2 := S.wt_add_one _
  have hN : (((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1 + 1) := Int.toNat_of_nonneg (by omega)
  -- equal dimensions
  have hfin : finrank k (∀ i : Fin (S.wt (r + 1 + 1)).toNat,
      (𝟙 (S.obj (r + 1 + 1)) ⟶ (𝟙 (S.obj (r + 1 + 1)))⟦m - 2 * ((i : ℕ) : ℤ)⟧)) =
      finrank k (S.E (r + 1) ⟶ (S.E (r + 1))⟦m⟧) := by
    rw [Module.finrank_pi_fintype, S.lemMain_finrank (r := r + 1) hr hyp hm, Finset.sum_range]
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin]
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  by_cases h2 : IsZero (𝟙 (S.obj (r + 1 + 1)))
  · funext i
    exact h2.eq_of_src _ _
  obtain ⟨e⟩ := S.exists_EFDecomp (r := r + 1) (by omega)
  have hyp' : ∀ r', r + 1 + 1 < r' → S.AdjHyp r' := fun r' h => hyp r' (by omega)
  have hd : DotNondeg e := by
    by_cases hn : 0 ≤ S.wt (r + 1)
    · exact lemXind_of_adjHyp hn hyp' (hyp _ (by omega)) h2 e
    · intro i hi
      exfalso
      have : (S.wt (r + 1 + 1)).toNat = 1 := by omega
      omega
  -- the coefficients of `Ψ f = 0` vanish
  have hcoef : ∀ j : ℕ, ∑ i : Fin (S.wt (r + 1 + 1)).toNat,
      (cisBubSh (S.oneShift (r + 1) 0) (f i)).comp (Cij e i j) (by ring) = 0 := by
    intro j
    have := congrArg (coefHom e j m) hf
    rw [map_zero, Ψ_apply, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (coefSh_dotsBub e j m i (f i)).symm
  -- descending induction: `f i = 0` once `f i' = 0` for all `i' > i`
  have key : ∀ i : Fin (S.wt (r + 1 + 1)).toNat, (∀ i' : Fin _, i < i' → f i' = 0) → f i = 0 := by
    intro i hi'
    have h := hcoef i
    rw [Finset.sum_eq_single i] at h
    · haveI := isIso_Cij_self e (by omega) hyp' hd i.2
      have h' : cisBub (S.oneShift (r + 1) 0) (f i) ≫
          ((Cij e i i : S.oneShift (r + 1) 0 ⟶ _)⟦m - 2 * ((i : ℕ) : ℤ)⟧' ≫
            (shiftFunctorAdd' _ (((i : ℕ) : ℤ) * 2) (m - 2 * ((i : ℕ) : ℤ)) m
              (by ring)).inv.app _) = 0 := h
      have h'' := congrArg (fun φ => φ ≫ inv ((Cij e i i : S.oneShift (r + 1) 0 ⟶ _)⟦m -
        2 * ((i : ℕ) : ℤ)⟧' ≫ (shiftFunctorAdd' _ (((i : ℕ) : ℤ) * 2) (m - 2 * ((i : ℕ) : ℤ)) m
          (by ring)).inv.app _)) h'
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, zero_comp] at h''
      exact eq_zero_of_cisBub_eq_zero _ _ h''
    · intro i' _ hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [Cij_eq_zero e (by omega) hyp' hd i'.2 (Fin.lt_def.1 hlt), ShiftedHom.comp_zero]
      · rw [hi' i' hgt]
        rw [cisBubSh, cisBub_zero]
        apply ShiftedHom.zero_comp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hall : ∀ t : ℕ, ∀ i : Fin (S.wt (r + 1 + 1)).toNat,
      (S.wt (r + 1 + 1)).toNat - 1 - (i : ℕ) ≤ t → f i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hi
      refine key i fun i' hi' => ?_
      exfalso
      have := i'.2
      have := Fin.lt_def.1 hi'
      omega
    | succ t ih =>
      intro i hi
      refine key i fun i' hi' => ih i' ?_
      have := Fin.lt_def.1 hi'
      omega
  funext i
  exact hall _ i le_rfl

end Categorification.TwoRep.StrongSl2
