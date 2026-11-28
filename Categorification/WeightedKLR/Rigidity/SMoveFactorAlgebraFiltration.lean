/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationProjTor
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationTor
import Categorification.Algebra.ModuleFiltrationIdempotents
import Categorification.WeightedKLR.RedStrands.StringyClassification

/-!
# The standard filtration of the standardized factor algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `E²` terms for resolutions by standardizations (Proposition 7.8). The
factor algebra `D_{θ,β} = T^{λ'}_θ ⊗ R^{λ_{ℓ+1}}_β` is the direct sum of the factor projectives
`T^{λ'} e(t) ⊠ R e(u)`, cut out by the orthogonal idempotents `e(t) ⊗ e(u)`. So its
standardization `S(D_{θ,β})` is filtered by the standardized factor projectives, hence
(Proposition 5.20) by the standard modules of the two-piece loadings `t' λ_{ℓ+1} u`. With the
dimension shift of `torAcyclic_stdLayer_of_finiteDimensional`, this gives Tor-acyclicity of
`S(M)` for every finite-dimensional factor module `M`, against a right module filtered by
right standards inequivalent to every two-piece loading.

## Main results

* `factorIdem`, `factorIdem_mul`, `sum_factorIdem`: the orthogonal idempotents `e(t) ⊗ e(u)`.
* `factorPieceEquiv`: `D (e(t) ⊗ e(u)) ≅ T^{λ'} e(t) ⊠ R e(u)`.
* `exists_hasFiltration_stdLayer_factorAlgebra`: the standard filtration of `S(D_{θ,β})`.
* `torAcyclic_stdLayer_factorAlgebra`, `torAcyclic_stdLayer_of_twoPieceInequivalent`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR KLRAlgebra ModuleFiltration Equiv
open BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero TensorProduct

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {θ β : Multiset I}

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "D" => parabolicFactorAlgebra Q Λ θ β

/-- The labels of the factor projectives: a red-ordered loading of the first `ℓ` red strands and
a black sequence on the last one. -/
abbrev FactorLabel (θ β : Multiset I) : Type :=
  {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t} × Seq β

/-- **The idempotent `e(t) ⊗ e(u)`** of the factor algebra. -/
abbrev factorIdem (p : FactorLabel (ℓ := ℓ) θ β) : D :=
  seqIdem Q (old) p.1.1 p.1.2 ⊗ₜ[k] CycKLR.mk k Q (aΛ) β (e p.2)

theorem factorIdem_mul (p q : FactorLabel (ℓ := ℓ) θ β) :
    factorIdem Q Λ p * factorIdem Q Λ q = if p = q then factorIdem Q Λ p else 0 := by
  obtain ⟨⟨t, ht⟩, u⟩ := p
  obtain ⟨⟨t', ht'⟩, u'⟩ := q
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, ← map_mul, StendhalAlgebra.e_mul_e,
    e_mul_e]
  dsimp only
  by_cases htt : t = t'
  · subst htt
    by_cases huu : u = u'
    · subst huu
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    · have : ((⟨t, ht⟩, u) : FactorLabel (ℓ := ℓ) θ β) ≠ (⟨t, ht'⟩, u') := fun h =>
        huu (congrArg Prod.snd h)
      rw [ite_eq_right huu, ite_eq_right this, map_zero, TensorProduct.tmul_zero]
  · have : ((⟨t, ht⟩, u) : FactorLabel (ℓ := ℓ) θ β) ≠ (⟨t', ht'⟩, u') := fun h =>
      htt (congrArg (fun p => p.1.1) h)
    rw [ite_eq_right htt, ite_eq_right this, map_zero, TensorProduct.zero_tmul]

theorem sum_factorIdem : ∑ p : FactorLabel (ℓ := ℓ) θ β, factorIdem Q Λ p = 1 := by
  rw [Fintype.sum_prod_type]
  change ∑ t : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}, ∑ u : Seq β,
    seqIdem Q (old) t.1 t.2 ⊗ₜ[k] CycKLR.mk k Q (aΛ) β (e u) = 1
  simp_rw [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul]
  rw [← map_sum (CycKLR.mk k Q (aΛ) β), sum_e, map_one, sum_seqIdem Q (old) θ,
    Algebra.TensorProduct.one_def]

/-- Right multiplication by `e(t) ⊗ e(u)`, an idempotent endomorphism of `D`. -/
abbrev factorRightMul (p : FactorLabel (ℓ := ℓ) θ β) :
    Module.End D (ModuleCat.of D D) :=
  LinearMap.toSpanSingleton D D (factorIdem Q Λ p)

/-- The inclusion of the projective `T^{λ'} e(t)` into `T^{λ'}`, over `k`. -/
def oldProjIncl (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) :
    KMod (k := k) (oldProj Q Λ θ t ht) →ₗ[k] TensorProductAlgebra k Q (old) θ where
  toFun x := (show lIdeal (seqIdem Q (old) t ht) from x).1
  map_add' _ _ := rfl
  map_smul' c x := by
    change algebraMap k _ c * (show lIdeal (seqIdem Q (old) t ht) from x).1 = _
    rw [← Algebra.smul_def]
    rfl

/-- The inclusion of the projective `R e(u)` into `R`, over `k`. -/
def cycProjIncl (u : Seq β) :
    KMod (k := k) (cycProj Q Λ β u) →ₗ[k] CycKLR k Q (aΛ) β where
  toFun y := (show lIdeal (CycKLR.mk k Q (aΛ) β (e u)) from y).1
  map_add' _ _ := rfl
  map_smul' c y := by
    change algebraMap k _ c * (show lIdeal (CycKLR.mk k Q (aΛ) β (e u)) from y).1 = _
    rw [← Algebra.smul_def]
    rfl

/-- The inclusion `T^{λ'} e(t) ⊠ R e(u) → D`, `x ⊠ y ↦ x ⊗ y`. -/
def factorPieceIncl (p : FactorLabel (ℓ := ℓ) θ β) :
    (tensorFactor Q Λ (oldProj Q Λ θ p.1.1 p.1.2) (cycProj Q Λ β p.2)).carrier →ₗ[D] D where
  toFun x := TensorProduct.map (oldProjIncl Q Λ p.1.1 p.1.2) (cycProjIncl Q Λ p.2)
    (ExtTensor.equivTensor x)
  map_add' x y := map_add _ _ _
  map_smul' c x := by
    refine ExtTensor.smul_eq_induction (F := fun x => TensorProduct.map
      (oldProjIncl Q Λ p.1.1 p.1.2) (cycProjIncl Q Λ p.2) (ExtTensor.equivTensor x))
      (fun x y => map_add _ _ _) (map_zero _) (fun a b x y => ?_) c x
    rw [ExtTensor.smul_tmul]
    change (a * (show lIdeal (seqIdem Q (old) p.1.1 p.1.2) from x).1) ⊗ₜ[k]
        (b * (show lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) from y).1) =
      (a ⊗ₜ[k] b) * ((show lIdeal (seqIdem Q (old) p.1.1 p.1.2) from x).1 ⊗ₜ[k]
        (show lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) from y).1)
    rw [Algebra.TensorProduct.tmul_mul_tmul]

theorem oldProjIncl_injective (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) :
    Function.Injective (oldProjIncl Q Λ t ht) := fun _ _ hxy =>
  Subtype.ext (p := fun z => z ∈ lIdeal (seqIdem Q (old) t ht)) hxy

theorem cycProjIncl_injective (u : Seq β) : Function.Injective (cycProjIncl Q Λ u) :=
  fun _ _ hxy => Subtype.ext (p := fun z => z ∈ lIdeal (CycKLR.mk k Q (aΛ) β (e u))) hxy

theorem factorPieceIncl_injective (p : FactorLabel (ℓ := ℓ) θ β) :
    Function.Injective (factorPieceIncl Q Λ p) :=
  (TensorProduct.map_injective_of_flat_flat _ _ (oldProjIncl_injective Q Λ p.1.1 p.1.2)
    (cycProjIncl_injective Q Λ p.2)).comp ExtTensor.equivTensor.injective

theorem range_factorPieceIncl (p : FactorLabel (ℓ := ℓ) θ β) :
    LinearMap.range (factorPieceIncl Q Λ p) = LinearMap.range (factorRightMul Q Λ p) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul x y =>
      refine ⟨(show lIdeal (seqIdem Q (old) p.1.1 p.1.2) from x).1 ⊗ₜ[k]
        (show lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) from y).1, ?_⟩
      change ((show lIdeal (seqIdem Q (old) p.1.1 p.1.2) from x).1 ⊗ₜ[k]
        (show lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) from y).1) * factorIdem Q Λ p = _
      rw [ Algebra.TensorProduct.tmul_mul_tmul,
        (show lIdeal (seqIdem Q (old) p.1.1 p.1.2) from x).2,
        (show lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) from y).2]
      rfl
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · rintro _ ⟨z, rfl⟩
    change z * factorIdem Q Λ p ∈ _
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have ha : a * seqIdem Q (old) p.1.1 p.1.2 ∈ lIdeal (seqIdem Q (old) p.1.1 p.1.2) := by
        rw [mem_lIdeal, mul_assoc, seqIdem_mul_self]
      have hb : b * CycKLR.mk k Q (aΛ) β (e p.2) ∈ lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) := by
        rw [mem_lIdeal, mul_assoc, ← map_mul, e_mul_self]
      exact ⟨ExtTensor.tmul (k := k) (show KMod (k := k) (oldProj Q Λ θ p.1.1 p.1.2) from
        ⟨_, ha⟩) (show KMod (k := k) (cycProj Q Λ β p.2) from ⟨_, hb⟩), rfl⟩
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy

/-- The summand `D (e(t) ⊗ e(u))` of the regular module. -/
abbrev factorPiece (p : FactorLabel (ℓ := ℓ) θ β) : ModuleCat.{0} D :=
  ModuleCat.of D (LinearMap.range (factorRightMul Q Λ p))

/-- **`D (e(t) ⊗ e(u)) ≅ T^{λ'} e(t) ⊠ R e(u)`** as modules over the factor algebra. -/
def factorPieceEquiv (p : FactorLabel (ℓ := ℓ) θ β) :
    KMod (k := k) (factorPiece Q Λ p) ≃ₗ[D]
      (tensorFactor Q Λ (oldProj Q Λ θ p.1.1 p.1.2) (cycProj Q Λ β p.2)).carrier :=
  ((LinearEquiv.ofInjective _ (factorPieceIncl_injective Q Λ p)).trans
    (LinearEquiv.ofEq _ _ (range_factorPieceIncl Q Λ p))).symm

/-- A module over the factor algebra, as a factor module. -/
abbrev factorModuleOf (X : ModuleCat.{0} D) : FactorModule Q Λ θ β :=
  ⟨KMod (k := k) X⟩

/-- Standardization of a module over the factor algebra, as an operation on `ModuleCat D`. -/
abbrev stdOfModule {ν : Multiset I} (h : θ + β = ν) (X : ModuleCat.{0} D) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  stdLayerModule Q Λ hQ ⟨θ, β, h, factorModuleOf Q Λ X⟩

/-- Standardization of a map of modules over the factor algebra. -/
abbrev stdOfModuleMap {ν : Multiset I} (h : θ + β = ν) {X Y : ModuleCat.{0} D}
    (f : X →ₗ[D] Y) : stdOfModule Q Λ hQ h X →ₗ[TensorProductAlgebra k Q Λ ν]
      stdOfModule Q Λ hQ h Y :=
  stdLayerMap Q Λ hQ h (M := factorModuleOf Q Λ X) (M' := factorModuleOf Q Λ Y) (KMod.map f)

theorem stdOfModuleMap_injective {ν : Multiset I} (h : θ + β = ν) {X Y : ModuleCat.{0} D}
    (f : X →ₗ[D] Y) (hf : Function.Injective f) :
    Function.Injective (stdOfModuleMap Q Λ hQ h f) :=
  parabolicStandardMap_injective Q Λ θ β hQ (N := (factorModuleOf Q Λ X).carrier)
    (N' := (factorModuleOf Q Λ Y).carrier) (KMod.map f) hf

theorem stdOfModuleMap_surjective {ν : Multiset I} (h : θ + β = ν) {X Y : ModuleCat.{0} D}
    (f : X →ₗ[D] Y) (hf : Function.Surjective f) :
    Function.Surjective (stdOfModuleMap Q Λ hQ h f) :=
  parabolicStandardMap_surjective Q Λ θ β hQ (N := (factorModuleOf Q Λ X).carrier)
    (N' := (factorModuleOf Q Λ Y).carrier) (KMod.map f) hf

theorem stdOfModuleMap_exact {ν : Multiset I} (h : θ + β = ν) {X Y Z : ModuleCat.{0} D}
    (f : X →ₗ[D] Y) (g : Y →ₗ[D] Z) (hfg : Function.Exact f g) :
    Function.Exact (stdOfModuleMap Q Λ hQ h f) (stdOfModuleMap Q Λ hQ h g) :=
  parabolicStandardMap_exact Q Λ θ β hQ (N := (factorModuleOf Q Λ X).carrier)
    (N' := (factorModuleOf Q Λ Y).carrier) (N'' := (factorModuleOf Q Λ Z).carrier)
    (KMod.map f) (KMod.map g) hfg

/-- The regular module of the factor algebra, as a factor module, is the factor algebra. -/
def factorRegularEquiv :
    (factorModuleOf Q Λ (ModuleCat.of D D)).carrier ≃ₗ[D]
      (factorOf Q Λ (θ := θ) (β := β) D).carrier :=
  LinearEquiv.refl D D

/-- Standardization transports filtrations of modules over the factor algebra. -/
theorem hasFiltration_stdOfModule {ν : Multiset I} (h : θ + β = ν) {ι : Type}
    {L : ι → ModuleCat.{0} D} {m : List ι} {X : ModuleCat.{0} D} (hX : HasFiltration L m X) :
    HasFiltration (fun c => stdOfModule Q Λ hQ h (L c)) m (stdOfModule Q Λ hQ h X) :=
  HasFiltration.map (stdOfModule Q Λ hQ h) (fun f => stdOfModuleMap Q Λ hQ h f)
    (fun f hf => stdOfModuleMap_injective Q Λ hQ h f hf)
    (fun f hf => stdOfModuleMap_surjective Q Λ hQ h f hf)
    (fun f g _ hfg _ => stdOfModuleMap_exact Q Λ hQ h f g hfg) hX

/-- **The standard filtration of the standardized factor algebra** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, with Proposition 5.20): `S(D_{θ,β})` is
filtered by the standard modules of the two-piece loadings `t' λ_{ℓ+1} u`. -/
theorem exists_hasFiltration_stdLayer_factorAlgebra {ν : Multiset I} (h : θ + β = ν)
    (hold : HasStandardFiltrations Q (old)) :
    ∃ l : List (Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d}),
      HasFiltration (fun p => stdModule Q Λ ν (twoPieceLabel h p.1 p.2)) l
        (stdOf Q Λ hQ h D) := by
  obtain ⟨m₁, h₁⟩ := exists_hasFiltration_of_orthogonal
    (L := factorPiece Q Λ)
    (M := ModuleCat.of D D) (factorRightMul Q Λ) Finset.univ
    (fun p _ => LinearMap.ext fun z => by
      change z * factorIdem Q Λ p * factorIdem Q Λ p = z * factorIdem Q Λ p
      rw [mul_assoc, factorIdem_mul, ite_eq_left rfl])
    (fun p _ q _ hpq => LinearMap.ext fun z => by
      change z * factorIdem Q Λ q * factorIdem Q Λ p = 0
      rw [mul_assoc, factorIdem_mul, ite_eq_right (Ne.symm hpq), mul_zero])
    (LinearMap.ext fun z => by
      change (∑ p ∈ Finset.univ, factorRightMul Q Λ p) z = z
      rw [LinearMap.sum_apply]
      change ∑ p, z * factorIdem Q Λ p = z
      rw [← Finset.mul_sum, sum_factorIdem, mul_one])
    (fun p _ => ⟨[p], HasFiltration.single (LinearEquiv.refl _ _)⟩)
  have h₂ := hasFiltration_stdOfModule Q Λ hQ h h₁
  have h₃ : HasFiltration (fun c => stdOfModule Q Λ hQ h (factorPiece Q Λ c)) m₁
      (stdOf Q Λ hQ h D) :=
    h₂.of_equiv (stdLayerEquiv Q Λ hQ h (factorRegularEquiv Q Λ (θ := θ) (β := β)))
  refine h₃.exists_refine fun p _ => ?_
  obtain ⟨m', hm'⟩ := hold θ p.1.1 p.1.2
  have h₄ := hasFiltration_tensorLayer Q Λ hQ h (cycProj Q Λ β p.2)
    (X := oldProj Q Λ θ p.1.1 p.1.2) hm'
  have h₅ : HasFiltration (fun d => stdModule Q Λ ν (twoPieceLabel h p.2 d)) m'
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h (oldProj Q Λ θ p.1.1 p.1.2)
        (cycProj Q Λ β p.2))) :=
    h₄.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ h d.2 p.2
  exact ⟨_, (HasFiltration.relabel
    (L := fun p : Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d} =>
      stdModule Q Λ ν (twoPieceLabel h p.1 p.2)) (fun d => (p.2, d)) h₅).of_equiv
    (stdLayerEquiv Q Λ hQ h (M := tensorFactor Q Λ _ _)
      (M' := factorModuleOf Q Λ (factorPiece Q Λ p))
      (factorPieceEquiv Q Λ p).symm)⟩

variable {ν : Multiset I} {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) (List.map (1 : Perm (Fin (ℓ + 1)))
      (List.finRange (ℓ + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **Tor against the standardized factor algebra** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, off-diagonal `E²` terms): if `N` is filtered by right standards whose
labels are inequivalent to every two-piece loading `t' λ_{ℓ+1} u`, then `N ⊗ᴸ S(D_{θ,β})` has
no cohomology (over `ℤ`). -/
theorem torAcyclic_stdLayer_factorAlgebra
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (old)) (h : θ + β = ν)
    {m : List {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s}}
    {N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    (hN : HasFiltration (fun t' : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ 1 t'.1) m N)
    (hlab : ∀ t' ∈ m, ∀ u d, ¬ (StendhalLE (twoPieceLabel h u d).1 t'.1 ∧
      StendhalLE t'.1 (twoPieceLabel h u d).1)) :
    TorAcyclic.{w} (k := ℤ) N (stdOf Q Λ hQ h D) := by
  obtain ⟨l, hl⟩ := exists_hasFiltration_stdLayer_factorAlgebra Q Λ hQ h hold
  let : HasDerivedCategory.{w, 0}
      (TensorProductAlgebra k Q (Λ ∘ ⇑(1 : Perm (Fin (ℓ + 1)))) ν) :=
    ‹HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)›
  have hY : HasFiltration (stdModule Q Λ ν)
      (l.map fun p : Seq β × {d : Seq (stendhalWeight ℓ θ) // IsRedOrdered d} =>
        twoPieceLabel h p.1 p.2) (stdOf Q Λ hQ h D) :=
    HasFiltration.relabel (L := stdModule Q Λ ν) _ hl
  intro n
  have key := isZero_derivedTensorHomology_tensor_of_standardFiltrations hρ hQ 1 DC hN hY
    (fun t' ht' s hs => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
      exact hlab t' ht' p.1 p.2) n
  exact key

include hρ in
/-- **Tor against standardizations of finite-dimensional factor modules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, off-diagonal `E²` terms for the
resolutions of Proposition 7.8): for Rouquier parameters, if `N` is filtered by right standards
whose labels are inequivalent to every two-piece loading `t' λ_{ℓ+1} u`, then `N ⊗ᴸ S(M)` has
no cohomology for every finite-dimensional module `M` over `D_{θ,β}`. -/
theorem torAcyclic_stdLayer_of_twoPieceInequivalent {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q)
    (DC : OrderedStandardCovers
      (fun s : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2))
      (fun s => seqIdem Q Λ s.1 s.2) (fun s t => StendhalLT s.1 t.1))
    (hold : HasStandardFiltrations Q (old)) (h : θ + β = ν)
    {m : List {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s}}
    {N : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}
    (hN : HasFiltration (fun t' : {s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s} =>
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ 1 t'.1) m N)
    (hlab : ∀ t' ∈ m, ∀ u d, ¬ (StendhalLE (twoPieceLabel h u d).1 t'.1 ∧
      StendhalLE t'.1 (twoPieceLabel h u d).1))
    (M : FactorModule Q Λ θ β) [FiniteDimensional k M.carrier] :
    TorAcyclic.{w} (k := ℤ) N (stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩) :=
  torAcyclic_stdLayer_of_finiteDimensional Q Λ hQ h N hR
    (torAcyclic_stdLayer_factorAlgebra Q Λ hQ hρ DC hold h hN hlab) M

end Categorification.Stendhal
