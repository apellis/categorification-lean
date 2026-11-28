/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFunctor
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers
import Categorification.Algebra.ModuleFiltrationIdempotents

/-!
# Standardizations of projectives have bounded projective dimension

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.28 (step for several red strands): standardization `S` from modules over the factor
algebra `D = T^{λ'}_θ ⊗ R^{λ_ℓ}_β` to modules over `T^λ_{θ+β}` sends finitely generated
projectives to modules of projective dimension below a bound depending only on `D`
(`exists_hasProjectiveDimensionLT_stdOf_projective`), for Rouquier parameters.

The regular module `D` splits along the idempotents `e(t) ⊗ e(u)` into the modules
`T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)`, whose standardizations are filtered by standard modules
(proof of Proposition 5.21), and standard modules have finite projective dimension
(Corollary 5.24). A finitely generated projective is a retract of `D^m`, and `S` is an exact
functor.

## Main definitions and results

* `parabolicFactorModuleOf`, `parabolicStdOf`, `parabolicStdOfMap`: standardization of modules over `D`.
* `hasFiltration_stdOf`: standardization preserves filtrations.
* `exists_hasProjectiveDimensionLT_stdOf_projective`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open CategoryTheory ModuleFiltration

section Generic

variable {A : Type} [Ring A]

/-- A uniform bound for the projective dimensions of the members of a list. -/
theorem exists_forall_mem_hasProjectiveDimensionLT {ι : Type*} (L : ι → ModuleCat.{0} A)
    (h : ∀ c, ∃ n, HasProjectiveDimensionLT (L c) n) (m : List ι) :
    ∃ n, ∀ c ∈ m, HasProjectiveDimensionLT (L c) n := by
  induction m with
  | nil => exact ⟨0, by simp⟩
  | cons c m ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨n', hn'⟩ := h c
    refine ⟨max n n', fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hasProjectiveDimensionLT_of_ge _ n' _ (le_max_right _ _)
    · have := hn c' hc'
      exact hasProjectiveDimensionLT_of_ge _ n _ (le_max_left _ _)

/-- Right multiplication by `f`, an endomorphism of the regular left module. -/
def rightMulEnd (f : A) : Module.End A A where
  toFun x := x * f
  map_add' x y := add_mul x y f
  map_smul' c x := mul_assoc c x f

theorem range_rightMulEnd {f : A} (hf : IsIdempotentElem f) :
    LinearMap.range (rightMulEnd f) = lIdeal f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change x * f * f = x * f
    rw [mul_assoc, hf.eq]
  · intro hy
    exact ⟨y, hy⟩

/-- **The regular module along orthogonal idempotents**: if `1 = Σ ε_b` is a decomposition into
orthogonal idempotents, `A` is filtered by the left ideals `A ε_b`. -/
theorem exists_hasFiltration_regular {β : Type*} [Fintype β] [DecidableEq β] (ε : β → A)
    (hidem : ∀ b, IsIdempotentElem (ε b)) (horth : ∀ b b', b ≠ b' → ε b * ε b' = 0)
    (hsum : ∑ b, ε b = 1) :
    ∃ m : List β, HasFiltration (fun b => ModuleCat.of A (lIdeal (ε b))) m (ModuleCat.of A A) := by
  refine exists_hasFiltration_of_orthogonal (M := ModuleCat.of A A)
    (fun b => rightMulEnd (ε b)) Finset.univ (fun b _ => ?_) (fun b _ b' _ hbb' => ?_) ?_
    (fun b _ => ⟨[b], HasFiltration.single (LinearEquiv.ofEq _ _ (range_rightMulEnd (hidem b)))⟩)
  · refine LinearMap.ext fun x => ?_
    change x * ε b * ε b = x * ε b
    rw [mul_assoc, (hidem b).eq]
  · refine LinearMap.ext fun x => ?_
    change x * ε b' * ε b = 0
    rw [mul_assoc, horth b' b (Ne.symm hbb'), mul_zero]
  · refine LinearMap.ext fun x => ?_
    change (∑ b ∈ Finset.univ, rightMulEnd (ε b)) x = x
    rw [LinearMap.sum_apply]
    change ∑ b, x * ε b = x
    rw [← Finset.mul_sum, hsum, mul_one]

/-- `A^m` is filtered by `m` copies of `A`. -/
theorem exists_hasFiltration_pi (m : ℕ) :
    ∃ l : List (Fin m), HasFiltration (fun _ => ModuleCat.of A A) l
      (ModuleCat.of A (Fin m → A)) := by
  classical
  refine exists_hasFiltration_of_orthogonal (M := ModuleCat.of A (Fin m → A))
    (fun i => LinearMap.single A (fun _ => A) i ∘ₗ LinearMap.proj i) Finset.univ
    (fun i _ => ?_) (fun i _ j _ hij => ?_) ?_ (fun i _ => ⟨[i], HasFiltration.single ?_⟩)
  · refine LinearMap.ext fun x => ?_
    simp
  · refine LinearMap.ext fun x => ?_
    simp [Ne.symm hij]
  · refine LinearMap.ext fun x => ?_
    change (∑ i ∈ Finset.univ, LinearMap.single A (fun _ => A) i ∘ₗ LinearMap.proj i) x = x
    rw [LinearMap.sum_apply]
    exact Finset.univ_sum_single x
  · have h : LinearMap.range (LinearMap.single A (fun _ : Fin m => A) i ∘ₗ LinearMap.proj i) =
        LinearMap.range (LinearMap.single A (fun _ : Fin m => A) i) :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun a =>
        ⟨(Pi.single i a : Fin m → A), by simp⟩)
    exact (LinearEquiv.ofEq _ _ h).trans
      (LinearEquiv.ofInjective _ fun a b hab => by simpa using congr_fun hab i).symm

/-- A finitely generated projective module is a retract of some `A^m`. -/
theorem exists_retract_pi (P : ModuleCat.{0} A) [Module.Projective A P] [Module.Finite A P] :
    ∃ m : ℕ, Nonempty (∃ (i : P →ₗ[A] (Fin m → A)) (r : (Fin m → A) →ₗ[A] P),
      r ∘ₗ i = LinearMap.id) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' A P
  obtain ⟨i, hi⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨m, ⟨i, f, hi⟩⟩

end Generic

namespace Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

open scoped Classical

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (θ β : Multiset I)

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

/-- A module over the factor algebra `D`, as a factor module of standardization. -/
def parabolicFactorModuleOf (X : ModuleCat.{0} D) : FactorModule Q Λ θ β := ⟨KMod (k := k) X⟩

/-- The standardization `S(X)` of a module over `D`, over `T^λ_{θ+β}`. -/
abbrev parabolicStdOf (X : ModuleCat.{0} D) : ModuleCat.{0} T :=
  stdLayerModule Q Λ hQ ⟨θ, β, rfl, parabolicFactorModuleOf Q Λ θ β X⟩

/-- The map of standardizations induced by a map of modules over `D`. -/
def parabolicStdOfMap {X Y : ModuleCat.{0} D} (f : X →ₗ[D] Y) : parabolicStdOf Q Λ hQ θ β X →ₗ[T] parabolicStdOf Q Λ hQ θ β Y :=
  stdLayerMap Q Λ hQ rfl (M := parabolicFactorModuleOf Q Λ θ β X) (M' := parabolicFactorModuleOf Q Λ θ β Y) (KMod.map f)

theorem stdOfMap_comp {X Y Z : ModuleCat.{0} D} (f : X →ₗ[D] Y) (g : Y →ₗ[D] Z) :
    parabolicStdOfMap Q Λ hQ θ β (g ∘ₗ f) = parabolicStdOfMap Q Λ hQ θ β g ∘ₗ parabolicStdOfMap Q Λ hQ θ β f :=
  LinearMap.ext fun z => LinearMap.congr_fun
    (parabolicStandardMap_comp Q Λ θ β (KMod.map (k := k) f) (KMod.map (k := k) g)) z

theorem stdOfMap_id (X : ModuleCat.{0} D) :
    parabolicStdOfMap Q Λ hQ θ β (LinearMap.id : X →ₗ[D] X) = LinearMap.id :=
  LinearMap.ext fun z => LinearMap.congr_fun
    (parabolicStandardMap_id Q Λ θ β (N := KMod (k := k) X)) z

/-- **Standardization preserves filtrations** (Webster, arXiv:1309.3796v3, Proposition 5.7). -/
theorem hasFiltration_stdOf {ι : Type*} {L : ι → ModuleCat.{0} D} {m : List ι}
    {Y : ModuleCat.{0} D} (h : HasFiltration L m Y) :
    HasFiltration (fun c => parabolicStdOf Q Λ hQ θ β (L c)) m (parabolicStdOf Q Λ hQ θ β Y) :=
  h.map _ (parabolicStdOfMap Q Λ hQ θ β)
    (fun f hf => parabolicStandardMap_injective Q Λ θ β hQ (KMod.map (k := k) f) hf)
    (fun f hf => parabolicStandardMap_surjective Q Λ θ β hQ (KMod.map (k := k) f) hf)
    (fun f g _ hfg _ => parabolicStandardMap_exact Q Λ θ β hQ (KMod.map (k := k) f)
      (KMod.map (k := k) g) hfg)

/-- The idempotent `e(t) ⊗ e(u)` of `D`. -/
abbrev pieceIdem (c : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β) : D :=
  seqIdem Q (old) c.1.1 c.1.2 ⊗ₜ[k] CycKLR.mk k Q (aΛ) β (e c.2)

theorem pieceIdem_idem (c : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β) :
    IsIdempotentElem (pieceIdem Q Λ θ β c) := by
  unfold IsIdempotentElem
  rw [Algebra.TensorProduct.tmul_mul_tmul, seqIdem_mul_self, ← map_mul, KLRAlgebra.e_mul_e,
    ite_eq_left_of_eq_true _ _ (eq_self c.2)]

theorem pieceIdem_orth (c c' : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β)
    (h : c ≠ c') : pieceIdem Q Λ θ β c * pieceIdem Q Λ θ β c' = 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul (CycKLR.mk k Q (aΛ) β), KLRAlgebra.e_mul_e]
  change TensorProductAlgebra.mk Q (old) θ (StendhalAlgebra.e c.1.1 c.1.2 *
    StendhalAlgebra.e c'.1.1 c'.1.2) ⊗ₜ[k] _ = _
  rw [StendhalAlgebra.e_mul_e]
  by_cases h₁ : c.1.1 = c'.1.1
  · have h₂ : c.2 ≠ c'.2 := fun h₂ => h (Prod.ext (Subtype.ext h₁) h₂)
    rw [ite_eq_right_of_eq_false _ _ (eq_false h₂), map_zero, TensorProduct.tmul_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), map_zero, TensorProduct.zero_tmul]

theorem sum_pieceIdem :
    ∑ c : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β, pieceIdem Q Λ θ β c = 1 := by
  rw [Fintype.sum_prod_type, Algebra.TensorProduct.one_def, ← sum_seqIdem_eq_one ℓ θ Q (old),
    ← map_one (CycKLR.mk k Q (aΛ) β), ← KLRAlgebra.sum_e, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [TensorProduct.tmul_sum]

/-- The factor module `D (e(t) ⊗ e(u))` is `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)`. -/
def pieceEquiv (c : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β) :
    (parabolicFactorModuleOf Q Λ θ β (ModuleCat.of D (lIdeal (pieceIdem Q Λ θ β c)))).carrier ≃ₗ[D]
      (tensorFactor Q Λ (oldProj Q Λ θ c.1.1 c.1.2) (cycProj Q Λ β c.2)).carrier :=
  (ExtTensor.lIdealEquiv k (seqIdem_mul_self Q (old) c.1.1 c.1.2)
      (show IsIdempotentElem (CycKLR.mk k Q (aΛ) β (e c.2)) by
        unfold IsIdempotentElem
        rw [← map_mul, KLRAlgebra.e_mul_e, ite_eq_left_of_eq_true _ _ (eq_self c.2)])).symm.trans
    (ExtTensor.congr (LinearEquiv.refl _ _) (LinearEquiv.refl _ _))

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
include hR

/-- The standardization of `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)` has finite projective dimension
(Webster, arXiv:1309.3796v3, proof of Proposition 5.21, and Corollary 5.24). -/
theorem exists_hasProjectiveDimensionLT_stdOf_piece
    (c : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β) :
    ∃ n, HasProjectiveDimensionLT
      (parabolicStdOf Q Λ hQ θ β (ModuleCat.of D (lIdeal (pieceIdem Q Λ θ β c)))) n := by
  obtain ⟨m', hm'⟩ := hasStandardFiltrations_of_rouquier hR hQ (old) θ c.1.1 c.1.2
  have h₂ : HasFiltration (fun d => stdModule Q Λ _ (twoPieceLabel (ℓ := ℓ) (rfl : θ + β = θ + β)
      c.2 d)) m' (stdLayerModule Q Λ hQ (tensorLayer Q Λ rfl (oldProj Q Λ θ c.1.1 c.1.2)
        (cycProj Q Λ β c.2))) :=
    (hasFiltration_tensorLayer Q Λ hQ rfl (cycProj Q Λ β c.2)
      (X := oldProj Q Λ θ c.1.1 c.1.2) hm').mono fun d =>
      nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ rfl d.2 c.2
  obtain ⟨n, hn⟩ := exists_forall_mem_hasProjectiveDimensionLT _
    (fun d => exists_hasProjectiveDimensionLT_stdModule_of_rouquier hR hQ Λ (θ + β)
      (twoPieceLabel (ℓ := ℓ) (rfl : θ + β = θ + β) c.2 d)) m'
  have : HasProjectiveDimensionLT (ModuleCat.of T (stdLayerModule Q Λ hQ (tensorLayer Q Λ rfl
      (oldProj Q Λ θ c.1.1 c.1.2) (cycProj Q Λ β c.2)))) n := h₂.hasProjectiveDimensionLT n hn
  exact ⟨n, @Retract.hasProjectiveDimensionLT _ _ _ _ _
    (stdLayerEquiv Q Λ hQ rfl (pieceEquiv Q Λ θ β c)).symm.toModuleIso.symm.retract n this⟩

/-- The standardization of the regular module `D` has finite projective dimension. -/
theorem exists_hasProjectiveDimensionLT_stdOf_regular :
    ∃ n, HasProjectiveDimensionLT (parabolicStdOf Q Λ hQ θ β (ModuleCat.of D D)) n := by
  classical
  obtain ⟨l, hl⟩ := exists_hasFiltration_regular (pieceIdem Q Λ θ β) (pieceIdem_idem Q Λ θ β)
    (pieceIdem_orth Q Λ θ β) (sum_pieceIdem Q Λ θ β)
  obtain ⟨n, hn⟩ := exists_forall_mem_hasProjectiveDimensionLT _
    (exists_hasProjectiveDimensionLT_stdOf_piece Q Λ hQ θ β hR) l
  exact ⟨n, (hasFiltration_stdOf Q Λ hQ θ β hl).hasProjectiveDimensionLT n hn⟩

/-- **Standardizations of projectives have bounded projective dimension** (Webster,
arXiv:1309.3796v3, proof of Theorem 5.28): there is `n` such that `S(P)` has projective dimension
`< n` for every finitely generated projective module `P` over `D`. -/
theorem exists_hasProjectiveDimensionLT_stdOf_projective :
    ∃ n, ∀ (P : ModuleCat.{0} D) [Module.Projective D P] [Module.Finite D P],
      HasProjectiveDimensionLT (parabolicStdOf Q Λ hQ θ β P) n := by
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLT_stdOf_regular Q Λ hQ θ β hR
  refine ⟨n, fun P _ _ => ?_⟩
  obtain ⟨m, ⟨i, r, hri⟩⟩ := exists_retract_pi P
  obtain ⟨l, hl⟩ := exists_hasFiltration_pi (A := D) m
  have : HasProjectiveDimensionLT (parabolicStdOf Q Λ hQ θ β (ModuleCat.of D (Fin m → D))) n :=
    (hasFiltration_stdOf Q Λ hQ θ β hl).hasProjectiveDimensionLT n fun _ _ => hn
  let i' : P →ₗ[D] ModuleCat.of D (Fin m → D) := i
  let r' : ModuleCat.of D (Fin m → D) →ₗ[D] P := r
  have hri' : r' ∘ₗ i' = LinearMap.id := hri
  let R : Retract (parabolicStdOf Q Λ hQ θ β P) (parabolicStdOf Q Λ hQ θ β (ModuleCat.of D (Fin m → D))) :=
    { i := ModuleCat.ofHom (X := parabolicStdOf Q Λ hQ θ β P)
          (Y := parabolicStdOf Q Λ hQ θ β (ModuleCat.of D (Fin m → D))) (parabolicStdOfMap Q Λ hQ θ β i')
      r := ModuleCat.ofHom (X := parabolicStdOf Q Λ hQ θ β (ModuleCat.of D (Fin m → D)))
          (Y := parabolicStdOf Q Λ hQ θ β P) (parabolicStdOfMap Q Λ hQ θ β r')
      retract := by
        ext z
        change parabolicStdOfMap Q Λ hQ θ β r' (parabolicStdOfMap Q Λ hQ θ β i' z) = z
        rw [← LinearMap.comp_apply, ← stdOfMap_comp, hri', stdOfMap_id]
        rfl }
  exact R.hasProjectiveDimensionLT n

end Stendhal

end Categorification
