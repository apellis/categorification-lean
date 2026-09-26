/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Concat
import Categorification.KLR.GradedModules
import Categorification.Algebra.ExternalTensor

/-!
# Induction functors for KLR algebras

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6 "Induction and restriction" (TeX lines 1727–1870)
and §3.1, Proposition 3.1. For the non-unital inclusion `ι_{ν,ν'} = concat :
R(ν) ⊗ R(ν') → R(ν + ν')` with `ι(1) = 1_{ν,ν'}`, the induction functor is

`Ind_{ν,ν'} M = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} M`.

## Main definitions and results

* `GradingDatum.concat_mem_grade` : `ι` is degree-preserving,
  `ι (R(ν)_i ⊗ R(ν')_j) ⊆ R(ν + ν')_{i+j}`; this rests on the compatibility of the block
  embeddings with the coactions defining the gradings (`BlockEmb.coaction_valHom`).
* `KLRAlgebra.IndBimod Q ν ν' = R(ν + ν') 1_{ν,ν'}`, an `(R(ν + ν'), R(ν) ⊗ R(ν'))`-bimodule,
  finitely generated projective on the left.
* `KLRAlgebra.Ind Q ν ν' M` : the induced module (a `Categorification.BalancedTensor`).
* `GradingDatum.indProj G P P'` : `Ind_{ν,ν'} (P ⊠ P')` for finitely generated graded
  projective `P`, `P'`, as an object of `R(ν + ν')-pmod` (graded, finitely generated,
  projective).
* Functoriality and compatibility with the structure of `R-pmod`: `indProjCongr` (isomorphisms),
  `indProjProdLeft`, `indProjProdRight` (direct sums), `indProjShiftLeft`, `indProjShiftRight`
  (`Ind (P{a} ⊠ P') ≅ Ind (P ⊠ P'){a} ≅ Ind (P ⊠ P'{a})`).
* `GradingDatum.indIdemIso` : `Ind (R(ν) e ⊠ R(ν') e') ≅ R(ν + ν') ι(e ⊗ e')` for degree-zero
  idempotents, and `GradingDatum.indProjP` : `Ind (P_i ⊠ P_j) ≅ P_{ij}` (KL I, §2.6).
* `GradingDatum.indK0` : **the `ℤ[q, q⁻¹]`-bilinear map
  `[Ind] : K₀(R(ν)) × K₀(R(ν')) → K₀(R(ν + ν'))`**, `[P] ⊗ [P'] ↦ [Ind_{ν,ν'} (P ⊠ P')]`
  (KL I, §3.1), with `indK0_of`, `indK0_projP` (`[P_i] · [P_j] = [P_{ij}]`).
-/

noncomputable section

namespace Categorification

open scoped TensorProduct
open MulOpposite Graded

/-! ### Mapping coefficients of `AddMonoidAlgebra`s -/

/-- Applying a non-unital ring homomorphism to the coefficients of an `AddMonoidAlgebra`. -/
def AddMonoidAlgebra.mapCoeff {R S ι : Type*} [Semiring R] [Semiring S] (f : R →ₙ+* S) :
    AddMonoidAlgebra R ι →+ AddMonoidAlgebra S ι :=
  Finsupp.mapRange.addMonoidHom f.toAddMonoidHom

theorem AddMonoidAlgebra.mapCoeff_single {R S ι : Type*} [Semiring R] [Semiring S]
    (f : R →ₙ+* S) (a : ι) (r : R) :
    AddMonoidAlgebra.mapCoeff f (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single a (f r) :=
  Finsupp.mapRange_single (hf := map_zero _)

theorem AddMonoidAlgebra.mapCoeff_mul {R S ι : Type*} [Semiring R] [Semiring S] [AddMonoid ι]
    (f : R →ₙ+* S) (p q : AddMonoidAlgebra R ι) :
    AddMonoidAlgebra.mapCoeff f (p * q) =
      AddMonoidAlgebra.mapCoeff f p * AddMonoidAlgebra.mapCoeff f q := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_mul, map_add, map_add, add_mul, hp, hp']
  | single a r =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' => rw [mul_add, map_add, map_add, mul_add, hq, hq']
    | single b s =>
      show AddMonoidAlgebra.mapCoeff f
          (AddMonoidAlgebra.single a r * AddMonoidAlgebra.single b s) =
        AddMonoidAlgebra.mapCoeff f (AddMonoidAlgebra.single a r) *
          AddMonoidAlgebra.mapCoeff f (AddMonoidAlgebra.single b s)
      rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.mapCoeff_single,
        AddMonoidAlgebra.mapCoeff_single, AddMonoidAlgebra.mapCoeff_single,
        AddMonoidAlgebra.single_mul_single, map_mul]

namespace Graded.GProj

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-- The identity `P{a} → P` as a linear equivalence (of ungraded modules). -/
def shiftLinearEquiv (P : GProj 𝒜) (a : ℤ) : (P.shift a).carrier ≃ₗ[A] P.carrier :=
  LinearEquiv.refl _ _

theorem shiftLinearEquiv_preservesGrading (P : GProj 𝒜) (a : ℤ) :
    PreservesGrading (P.shift a).grading (Graded.shift P.grading a)
      (P.shiftLinearEquiv a).toLinearMap :=
  fun _ _ h => h

/-- Equal idempotents give isomorphic modules `A e = A e'`. -/
def ofIdempotentCongr [GradedAlgebra 𝒜] {e e' : A} (h : e = e') (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ 𝒜 0) :
    (ofIdempotent e he he0).Iso (ofIdempotent e' he' he0') := by
  subst h; exact GradedEquiv.refl _

end Graded.GProj

/-! ### Maps out of `K₀` -/

namespace Graded.K0

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  {k' A' : Type*} [CommRing k'] [Ring A'] [Algebra k' A'] {𝒜' : ℤ → Submodule k' A'}
  {G : Type*} [AddCommGroup G]

/-- The universal property of `K₀`: an isomorphism-invariant function on `A-pmod`, additive on
direct sums, induces an additive map on `K₀`. -/
def lift (f : GProj 𝒜 → G) (hiso : ∀ P Q : GProj 𝒜, P.Iso Q → f P = f Q)
    (hadd : ∀ P Q : GProj 𝒜, f (P.prod Q) = f P + f Q) : K0 𝒜 →+ G :=
  QuotientAddGroup.lift (relSubgroup 𝒜)
    (FreeAbelianGroup.lift (Quotient.lift f fun P Q ⟨e⟩ => hiso P Q e)) (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, Q, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift.of]
      show f (P.prod Q) - f P - f Q = 0
      rw [hadd]; abel)

@[simp] theorem lift_of (f : GProj 𝒜 → G) (hiso : ∀ P Q : GProj 𝒜, P.Iso Q → f P = f Q)
    (hadd : ∀ P Q : GProj 𝒜, f (P.prod Q) = f P + f Q) (P : GProj 𝒜) :
    lift f hiso hadd (of P) = f P := by
  show FreeAbelianGroup.lift _ (FreeAbelianGroup.of _) = _
  rw [FreeAbelianGroup.lift.of]
  rfl

/-- A biadditive map `K₀(A) × K₀(A') → G` from a function on pairs of objects which is
isomorphism-invariant and additive in each variable. -/
def lift₂ (f : GProj 𝒜 → GProj 𝒜' → G)
    (hiso₁ : ∀ (P₁ P₂ : GProj 𝒜) (Q : GProj 𝒜'), P₁.Iso P₂ → f P₁ Q = f P₂ Q)
    (hiso₂ : ∀ (P : GProj 𝒜) (Q₁ Q₂ : GProj 𝒜'), Q₁.Iso Q₂ → f P Q₁ = f P Q₂)
    (hadd₁ : ∀ (P₁ P₂ : GProj 𝒜) (Q : GProj 𝒜'), f (P₁.prod P₂) Q = f P₁ Q + f P₂ Q)
    (hadd₂ : ∀ (P : GProj 𝒜) (Q₁ Q₂ : GProj 𝒜'), f P (Q₁.prod Q₂) = f P Q₁ + f P Q₂) :
    K0 𝒜 →+ K0 𝒜' →+ G :=
  lift (fun P => lift (f P) (hiso₂ P) (hadd₂ P))
    (fun P₁ P₂ e => hom_ext fun Q => by rw [lift_of, lift_of, hiso₁ P₁ P₂ Q e])
    (fun P₁ P₂ => hom_ext fun Q => by rw [AddMonoidHom.add_apply, lift_of, lift_of, lift_of,
      hadd₁])

@[simp] theorem lift₂_of (f : GProj 𝒜 → GProj 𝒜' → G)
    (hiso₁ : ∀ (P₁ P₂ : GProj 𝒜) (Q : GProj 𝒜'), P₁.Iso P₂ → f P₁ Q = f P₂ Q)
    (hiso₂ : ∀ (P : GProj 𝒜) (Q₁ Q₂ : GProj 𝒜'), Q₁.Iso Q₂ → f P Q₁ = f P Q₂)
    (hadd₁ : ∀ (P₁ P₂ : GProj 𝒜) (Q : GProj 𝒜'), f (P₁.prod P₂) Q = f P₁ Q + f P₂ Q)
    (hadd₂ : ∀ (P : GProj 𝒜) (Q₁ Q₂ : GProj 𝒜'), f P (Q₁.prod Q₂) = f P Q₁ + f P Q₂)
    (P : GProj 𝒜) (Q : GProj 𝒜') :
    lift₂ f hiso₁ hiso₂ hadd₁ hadd₂ (of P) (of Q) = f P Q := by
  rw [lift₂, lift_of, lift_of]

/-- `c q^a` acts on `K₀` by `c` times the shift by `a`. -/
theorem C_mul_T_smul (a c : ℤ) (x : K0 𝒜) :
    (LaurentPolynomial.C c * LaurentPolynomial.T a : LaurentPolynomial ℤ) • x =
      c • shiftHom a x := by
  rw [mul_smul, T_smul, LaurentPolynomial.C_eq_algebraMap, algebraMap_smul]

/-- An additive map between `K₀` groups commuting with the grading shifts is
`ℤ[q, q⁻¹]`-linear. -/
theorem map_smul_of_shift (f : K0 𝒜 →+ K0 𝒜')
    (hf : ∀ (a : ℤ) (x : K0 𝒜), f (shiftHom a x) = shiftHom a (f x))
    (p : LaurentPolynomial ℤ) (x : K0 𝒜) : f (p • x) = p • f x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, add_smul, map_add, hp, hp']
  | C_mul_T a c => rw [C_mul_T_smul, C_mul_T_smul, map_zsmul, hf]

end Graded.K0

namespace KLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

open KLRAlgebra AddMonoidAlgebra

/-! ### The block embeddings are degree-preserving -/

namespace KLRAlgebra.BlockEmb

variable {μ ν : Multiset I} {T : Finset (Seq ν)} (B : BlockEmb μ ν T)

variable (Q) in
/-- The composite `R(μ) → e_T R(ν) e_T ⊆ R(ν)`, a non-unital ring homomorphism. -/
def valHom : KLRAlgebra k Q μ →ₙ+* KLRAlgebra k Q ν :=
  (cornerVal (eSum_idem (Q := Q) T)).comp (B.hom Q : KLRAlgebra k Q μ →+* _).toNonUnitalRingHom

@[simp] theorem valHom_apply (a : KLRAlgebra k Q μ) : B.valHom Q a = (B.hom Q a).val := rfl

variable (G : GradingDatum Q)

theorem eSum_mem_grade (S : Finset (Seq ν)) : (eSum Q S : KLRAlgebra k Q ν) ∈ G.grade ν 0 :=
  Submodule.sum_mem _ fun s _ => G.e_mem_grade s

/-- The set of elements on which `valHom` intertwines the coactions. -/
def goodSet : Set (KLRAlgebra k Q μ) :=
  {a | G.coaction (B.valHom Q a) = AddMonoidAlgebra.mapCoeff (B.valHom Q) (G.coaction a)}

theorem mem_goodSet_of_mem_grade {a : KLRAlgebra k Q μ} {d : ℤ} (ha : a ∈ G.grade μ d)
    (ha' : B.valHom Q a ∈ G.grade ν d) : a ∈ B.goodSet G := by
  show G.coaction (B.valHom Q a) = AddMonoidAlgebra.mapCoeff (B.valHom Q) (G.coaction a)
  rw [(G.mem_grade).1 ha, (G.mem_grade).1 ha', AddMonoidAlgebra.mapCoeff_single]

theorem add_mem_goodSet {a b : KLRAlgebra k Q μ} (ha : a ∈ B.goodSet G) (hb : b ∈ B.goodSet G) :
    a + b ∈ B.goodSet G := by
  have ha' : G.coaction (B.valHom Q a) = _ := ha
  have hb' : G.coaction (B.valHom Q b) = _ := hb
  show G.coaction (B.valHom Q (a + b)) = _
  rw [map_add, map_add, ha', hb', map_add (G.coaction), map_add]

theorem mul_mem_goodSet {a b : KLRAlgebra k Q μ} (ha : a ∈ B.goodSet G) (hb : b ∈ B.goodSet G) :
    a * b ∈ B.goodSet G := by
  have ha' : G.coaction (B.valHom Q a) = _ := ha
  have hb' : G.coaction (B.valHom Q b) = _ := hb
  show G.coaction (B.valHom Q (a * b)) = _
  rw [map_mul, map_mul, ha', hb', map_mul (G.coaction)]
  exact (AddMonoidAlgebra.mapCoeff_mul (B.valHom Q) _ _).symm

theorem sum_mem_goodSet {ι : Type*} (s : Finset ι) {f : ι → KLRAlgebra k Q μ}
    (hf : ∀ i ∈ s, f i ∈ B.goodSet G) : ∑ i ∈ s, f i ∈ B.goodSet G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact B.mem_goodSet_of_mem_grade G (zero_mem (G.grade μ 0))
      (by rw [map_zero]; exact zero_mem (G.grade ν 0))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact B.add_mem_goodSet G (hf j (Finset.mem_insert_self j s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem valHom_eF_mul {a : KLRAlgebra k Q μ} (i : Seq μ) :
    B.valHom Q (a * e i) = B.valHom Q a * B.eF Q i := by
  rw [map_mul, B.valHom_apply (e i), hom_e, val_gE]

omit [DecidableEq I] in
theorem card_le {j : ℕ} (hj : j + 1 < Multiset.card μ) : B.o + j + 1 < Multiset.card ν :=
  B.lt_card hj

/-- **The block embedding intertwines the coactions**, hence is degree-preserving. -/
theorem coaction_valHom (a : KLRAlgebra k Q μ) : a ∈ B.goodSet G := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes]
    refine B.mem_goodSet_of_mem_grade G (d := 0) ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (SetLike.GradedOne.one_mem)
    · rw [valHom_apply, AlgHom.commutes, Corner.val_algebraMap, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r (eSum_mem_grade G T)
  | grade1 g =>
    cases g with
    | idem i =>
      refine B.mem_goodSet_of_mem_grade G (G.e_mem_grade i) ?_
      show (B.hom Q (e i)).val ∈ _
      rw [hom_e, val_gE]
      exact eSum_mem_grade G _
    | dot a =>
      change x a ∈ B.goodSet G
      rw [← mul_one (x a), ← sum_e, Finset.mul_sum]
      refine B.sum_mem_goodSet G _ fun i _ => ?_
      refine B.mem_goodSet_of_mem_grade G (G.x_mul_e_mem_grade a i) ?_
      rw [valHom_eF_mul, valHom_apply, hom_x, val_polCorner, pol_X, mul_assoc, E_mul_eF]
      simp only [BlockEmb.eF, eSum, Finset.mul_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have := G.x_mul_e_mem_grade (B.pos a) s
      rwa [Seq.lbl, B.lbl i s hs a] at this
    | cross j =>
      change ψ j ∈ B.goodSet G
      by_cases hj : j + 1 < Multiset.card μ
      · rw [← mul_one (ψ j), ← sum_e, Finset.mul_sum]
        refine B.sum_mem_goodSet G _ fun i _ => ?_
        refine B.mem_goodSet_of_mem_grade G (G.ψ_mul_e_mem_grade hj i) ?_
        rw [valHom_eF_mul, valHom_apply, hom_ψ, B.val_gψ hj, mul_assoc, E_mul_eF]
        simp only [BlockEmb.eF, eSum, Finset.mul_sum]
        refine Submodule.sum_mem _ fun s hs => ?_
        have := G.ψ_mul_e_mem_grade (B.card_le hj) s
        rwa [Seq.lbl, Seq.lbl, B.lbl_of_mem hs (a := ⟨j, by omega⟩) rfl,
          B.lbl_of_mem hs (a := ⟨j + 1, hj⟩) (by simp; omega)] at this
      · rw [ψ_eq_zero j (by omega)]
        exact B.mem_goodSet_of_mem_grade G (zero_mem (G.grade μ 0))
          (by rw [map_zero]; exact zero_mem (G.grade ν 0))
  | mul u v hu hv => rw [map_mul]; exact B.mul_mem_goodSet G hu hv
  | add u v hu hv => rw [map_add]; exact B.add_mem_goodSet G hu hv

/-- The block embedding `R(μ) → R(ν)` is degree-preserving. -/
theorem valHom_mem_grade {a : KLRAlgebra k Q μ} {d : ℤ} (ha : a ∈ G.grade μ d) :
    B.valHom Q a ∈ G.grade ν d := by
  rw [GradingDatum.mem_grade]
  have h : G.coaction (B.valHom Q a) = _ := B.coaction_valHom G a
  rw [h, (G.mem_grade).1 ha, AddMonoidAlgebra.mapCoeff_single]

end KLRAlgebra.BlockEmb

namespace GradingDatum

variable (G : GradingDatum Q) {ν ν' : Multiset I}

/-- **`ι_{ν,ν'}` is degree-preserving**: `ι (R(ν)_i ⊗ R(ν')_j) ⊆ R(ν + ν')_{i+j}`. -/
theorem concat_tmul_mem_grade {a : KLRAlgebra k Q ν} {b : KLRAlgebra k Q ν'} {i j : ℤ}
    (ha : a ∈ G.grade ν i) (hb : b ∈ G.grade ν' j) :
    concat Q ν ν' (a ⊗ₜ b) ∈ G.grade (ν + ν') (i + j) := by
  rw [concat_tmul]
  exact SetLike.GradedMul.mul_mem ((blockL ν ν').valHom_mem_grade G ha)
    ((blockR ν ν').valHom_mem_grade G hb)

/-- `ι_{ν,ν'}` is degree-preserving for the tensor product grading of `R(ν) ⊗ R(ν')`. -/
theorem concat_mem_grade {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'} {d : ℤ}
    (ht : t ∈ tensorGrading (G.grade ν) (G.grade ν') d) :
    concat Q ν ν' t ∈ G.grade (ν + ν') d :=
  tensorGrading_map_mem _ _ _ (concat Q ν ν') (fun _ _ _ _ ha hb => G.concat_tmul_mem_grade ha hb)
    ht

theorem oneConcat_mem_grade : (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) ∈ G.grade (ν + ν') 0 :=
  Submodule.sum_mem _ fun s _ => G.e_mem_grade s

end GradingDatum

/-! ### The bimodule `R(ν + ν') 1_{ν,ν'}` and the induced modules -/

namespace KLRAlgebra

variable (Q) (ν ν' : Multiset I)

/-- The algebra `R(ν) ⊗ R(ν')`. -/
abbrev TensorKLR : Type _ := KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'

/-- The `(R(ν + ν'), R(ν) ⊗ R(ν'))`-bimodule `R(ν + ν') 1_{ν,ν'}`; the right action is through
`ι_{ν,ν'} = concat`. -/
abbrev IndBimod : Type _ := Graded.leftIdeal (oneConcat Q ν ν')

variable {Q ν ν'}

theorem mul_concat_mem (m : IndBimod Q ν ν') (t : TensorKLR Q ν ν') :
    (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' t ∈ Graded.leftIdeal (oneConcat Q ν ν') := by
  rw [Graded.mem_leftIdeal, mul_assoc, concat_mul_oneConcat]

instance : SMul (TensorKLR Q ν ν')ᵐᵒᵖ (IndBimod Q ν ν') :=
  ⟨fun t m => ⟨m * concat Q ν ν' t.unop, mul_concat_mem m _⟩⟩

theorem coe_op_smul (t : (TensorKLR Q ν ν')ᵐᵒᵖ) (m : IndBimod Q ν ν') :
    ((t • m : IndBimod Q ν ν') : KLRAlgebra k Q (ν + ν')) = m * concat Q ν ν' t.unop := rfl

instance : Module (TensorKLR Q ν ν')ᵐᵒᵖ (IndBimod Q ν ν') where
  one_smul m := Subtype.ext (by rw [coe_op_smul, unop_one, concat_one]; exact m.2)
  mul_smul s t m := Subtype.ext (by simp only [coe_op_smul, unop_mul, concat_mul, mul_assoc])
  smul_zero t := Subtype.ext (by simp [coe_op_smul])
  smul_add t m m' := Subtype.ext (by simp [coe_op_smul, add_mul])
  add_smul s t m := Subtype.ext (by simp [coe_op_smul, mul_add])
  zero_smul m := Subtype.ext (by simp [coe_op_smul])

instance : IsScalarTower k (TensorKLR Q ν ν')ᵐᵒᵖ (IndBimod Q ν ν') where
  smul_assoc c t m := Subtype.ext (by
    show (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (unop (c • t)) =
      c • ((m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' t.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν')ᵐᵒᵖ (IndBimod Q ν ν') where
  smul_comm r t m := Subtype.ext (by
    rw [coe_op_smul, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul, smul_eq_mul,
      smul_eq_mul, mul_assoc])

instance : Module.Finite (KLRAlgebra k Q (ν + ν')) (IndBimod Q ν ν') :=
  Module.Finite.of_surjective (Graded.leftIdealProj oneConcat_idem) fun b =>
    ⟨b, Subtype.ext (Graded.mem_leftIdeal.1 b.2)⟩

instance : Module.Projective (KLRAlgebra k Q (ν + ν')) (IndBimod Q ν ν') :=
  Module.Projective.of_split (Graded.leftIdeal _).subtype (Graded.leftIdealProj oneConcat_idem)
    (Graded.leftIdealProj_comp_subtype oneConcat_idem)

variable (Q ν ν') in
/-- **The induction functor** `Ind_{ν,ν'} N = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} N` (KL I,
§2.6). -/
abbrev Ind (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N] : Type _ :=
  BalancedTensor k (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν') (IndBimod Q ν ν') N

end KLRAlgebra

namespace GradingDatum

variable (G : GradingDatum Q) (ν ν' : Multiset I)

/-- The grading of `R(ν + ν') 1_{ν,ν'}`. -/
abbrev bimodGrading : ℤ → Submodule k (IndBimod Q ν ν') :=
  Graded.submodule (G.grade (ν + ν')) (Graded.leftIdeal (oneConcat Q ν ν'))

instance : DirectSum.Decomposition (G.bimodGrading ν ν') :=
  submoduleDecomposition _ (leftIdeal_isHomogeneous G.oneConcat_mem_grade)

variable {ν ν'}

/-- The right action of `R(ν) ⊗ R(ν')` on `R(ν + ν') 1_{ν,ν'}` is graded. -/
theorem op_smul_mem_bimodGrading {i l : ℤ} {m : IndBimod Q ν ν'} {t : TensorKLR Q ν ν'}
    (hm : m ∈ G.bimodGrading ν ν' i) (ht : t ∈ tensorGrading (G.grade ν) (G.grade ν') l) :
    op t • m ∈ G.bimodGrading ν ν' (i + l) :=
  SetLike.GradedMul.mul_mem (A := G.grade (ν + ν')) hm (G.concat_mem_grade ht)

variable (ν ν') in
/-- The grading of an induced module `Ind_{ν,ν'} N` of a graded `R(ν) ⊗ R(ν')`-module `N`. -/
abbrev indGrading {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
    (𝒩 : ℤ → Submodule k N) : ℤ → Submodule k (Ind Q ν ν' N) :=
  balancedGrading (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν') (G.bimodGrading ν ν') 𝒩

/-- **`Ind_{ν,ν'} (P ⊠ P')`** for finitely generated graded projective modules `P`, `P'`: a
finitely generated graded projective `R(ν + ν')`-module. -/
def indProj (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) : GProj (G.grade (ν + ν')) :=
  haveI := ExtTensor.finite (k := k) (A := KLRAlgebra k Q ν) (B := KLRAlgebra k Q ν')
    (P := P.carrier) (Q := P'.carrier)
  haveI := ExtTensor.projective (k := k) (A := KLRAlgebra k Q ν) (B := KLRAlgebra k Q ν')
    (P := P.carrier) (Q := P'.carrier)
  { carrier := Ind Q ν ν' (ExtTensor k P.carrier P'.carrier)
    grading := G.indGrading ν ν' (ExtTensor.grading P.grading P'.grading)
    decomposition := balancedDecomposition (tensorGrading (G.grade ν) (G.grade ν'))
      (fun _ _ _ _ hm ht => G.op_smul_mem_bimodGrading hm ht)
    gradedSMul := gradedSMul_balanced (G.grade (ν + ν'))
    finite := BalancedTensor.finite
    projective := BalancedTensor.projective }

theorem indProj_carrier (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) :
    (G.indProj P P').carrier = Ind Q ν ν' (ExtTensor k P.carrier P'.carrier) := rfl

theorem indProj_grading (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) :
    (G.indProj P P').grading = G.indGrading ν ν' (ExtTensor.grading P.grading P'.grading) := rfl

/-! ### Functoriality -/

/-- `Ind (P₁ ⊠ P₁') ≅ Ind (P₂ ⊠ P₂')` for `P₁ ≅ P₂`, `P₁' ≅ P₂'`. -/
def indProjCongr {P₁ P₂ : GProj (G.grade ν)} {P₁' P₂' : GProj (G.grade ν')} (e : P₁.Iso P₂)
    (e' : P₁'.Iso P₂') : (G.indProj P₁ P₁').Iso (G.indProj P₂ P₂') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr e.toLinearEquiv
    e'.toLinearEquiv)) fun _ y hy =>
      mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
        (ExtTensor.map_preservesGrading e.preservesGrading e'.preservesGrading) (y := y) hy

/-- `Ind ((P₁ ⊕ P₂) ⊠ P') ≅ Ind (P₁ ⊠ P') ⊕ Ind (P₂ ⊠ P')`. -/
def indProjProdLeft (P₁ P₂ : GProj (G.grade ν)) (P' : GProj (G.grade ν')) :
    (G.indProj (P₁.prod P₂) P').Iso ((G.indProj P₁ P').prod (G.indProj P₂ P')) :=
  let e := (BalancedTensor.congrRight (ExtTensor.prodLeft (k := k)
    (P := P₁.carrier) (P' := P₂.carrier) (Q := P'.carrier) (A := KLRAlgebra k Q ν)
    (B := KLRAlgebra k Q ν'))).trans
      (BalancedTensor.prodRight _ _ _ _ _ _)
  GradedEquiv.ofPreserves e fun _ y hy => balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν')
      (Graded.prod (G.indProj P₁ P').grading (G.indProj P₂ P').grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := Graded.prod P₁.grading P₂.grading)
          (𝒱 := P'.grading) (𝒰' := P₁.grading)
          (f := LinearMap.fst _ P₁.carrier P₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.1) (fun _ _ h => h) hn),
         tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := Graded.prod P₁.grading P₂.grading)
          (𝒱 := P'.grading) (𝒰' := P₂.grading)
          (f := LinearMap.snd _ P₁.carrier P₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.2) (fun _ _ h => h) hn)⟩) (y := y) hy

/-- `Ind (P ⊠ (P₁' ⊕ P₂')) ≅ Ind (P ⊠ P₁') ⊕ Ind (P ⊠ P₂')`. -/
def indProjProdRight (P : GProj (G.grade ν)) (P₁' P₂' : GProj (G.grade ν')) :
    (G.indProj P (P₁'.prod P₂')).Iso ((G.indProj P P₁').prod (G.indProj P P₂')) :=
  let e := (BalancedTensor.congrRight (ExtTensor.prodRight (k := k)
    (P := P.carrier) (Q := P₁'.carrier) (Q' := P₂'.carrier) (A := KLRAlgebra k Q ν)
    (B := KLRAlgebra k Q ν'))).trans
      (BalancedTensor.prodRight _ _ _ _ _ _)
  GradedEquiv.ofPreserves e fun _ y hy => balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν')
      (Graded.prod (G.indProj P P₁').grading (G.indProj P P₂').grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := P.grading)
          (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₁'.grading)
          (f := LinearMap.id) (g := LinearMap.fst _ P₁'.carrier P₂'.carrier)
          (fun _ _ h => h) (fun _ _ h => h.1) hn),
         tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading (𝒰 := P.grading)
          (𝒱 := Graded.prod P₁'.grading P₂'.grading) (𝒱' := P₂'.grading)
          (f := LinearMap.id) (g := LinearMap.snd _ P₁'.carrier P₂'.carrier)
          (fun _ _ h => h) (fun _ _ h => h.2) hn)⟩) (y := y) hy

/-- `Ind (P{a} ⊠ P') ≅ Ind (P ⊠ P'){a}`. -/
def indProjShiftLeft (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) (a : ℤ) :
    (G.indProj (P.shift a) P').Iso ((G.indProj P P').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr (P.shiftLinearEquiv a)
      (LinearEquiv.refl _ P'.carrier))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν') (𝒩' := ExtTensor.grading (shift P.grading a) P'.grading)
      (ExtTensor.map_preservesGrading (P.shiftLinearEquiv_preservesGrading a)
        (g := (LinearEquiv.refl (KLRAlgebra k Q ν') P'.carrier).toLinearMap)
        (fun _ _ h => h)) (y := y) hy
    rw [ExtTensor.grading_shift_left, balancedGrading_shift_right] at h
    exact h

/-- `Ind (P ⊠ P'{a}) ≅ Ind (P ⊠ P'){a}`. -/
def indProjShiftRight (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) (a : ℤ) :
    (G.indProj P (P'.shift a)).Iso ((G.indProj P P').shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr
      (LinearEquiv.refl _ P.carrier) (P'.shiftLinearEquiv a))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := KLRAlgebra k Q (ν + ν'))
      (ℳ := G.bimodGrading ν ν') (𝒩' := ExtTensor.grading P.grading (shift P'.grading a))
      (ExtTensor.map_preservesGrading
        (f := (LinearEquiv.refl (KLRAlgebra k Q ν) P.carrier).toLinearMap) (fun _ _ h => h)
        (P'.shiftLinearEquiv_preservesGrading a)) (y := y) hy
    rw [ExtTensor.grading_shift_right, balancedGrading_shift_right] at h
    exact h

/-! ### The product on Grothendieck groups (KL I, §3.1) -/

variable (ν ν') in
/-- The biadditive map `K₀(R(ν)) × K₀(R(ν')) → K₀(R(ν + ν'))`,
`([P], [P']) ↦ [Ind_{ν,ν'} (P ⊠ P')]`. -/
def indK0Add : K0 (G.grade ν) →+ K0 (G.grade ν') →+ K0 (G.grade (ν + ν')) :=
  K0.lift₂ (fun P P' => K0.of (G.indProj P P'))
    (fun _ _ _ e => K0.of_eq_of_iso (G.indProjCongr e (GradedEquiv.refl _)))
    (fun _ _ _ e => K0.of_eq_of_iso (G.indProjCongr (GradedEquiv.refl _) e))
    (fun P₁ P₂ P' => by
      beta_reduce; rw [K0.of_eq_of_iso (G.indProjProdLeft P₁ P₂ P'), K0.of_prod])
    (fun P P₁ P₂ => by
      beta_reduce; rw [K0.of_eq_of_iso (G.indProjProdRight P P₁ P₂), K0.of_prod])

@[simp] theorem indK0Add_of (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) :
    G.indK0Add ν ν' (K0.of P) (K0.of P') = K0.of (G.indProj P P') :=
  K0.lift₂_of _ _ _ _ _ P P'

theorem indK0Add_shift_left (a : ℤ) (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    G.indK0Add ν ν' (K0.shiftHom a x) y = K0.shiftHom a (G.indK0Add ν ν' x y) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      rw [K0.shiftHom_of, indK0Add_of, indK0Add_of, K0.shiftHom_of]
      exact K0.of_eq_of_iso (G.indProjShiftLeft P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

theorem indK0Add_shift_right (a : ℤ) (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    G.indK0Add ν ν' x (K0.shiftHom a y) = K0.shiftHom a (G.indK0Add ν ν' x y) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      rw [K0.shiftHom_of, indK0Add_of, indK0Add_of, K0.shiftHom_of]
      exact K0.of_eq_of_iso (G.indProjShiftRight P P' a)
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

variable (ν ν') in
/-- **The `ℤ[q, q⁻¹]`-bilinear map `[Ind] : K₀(R(ν)) × K₀(R(ν')) → K₀(R(ν + ν'))`** of KL I,
§3.1: `[P] ⊗ [P'] ↦ [Ind_{ν,ν'} (P ⊠ P')]`. -/
def indK0 : K0 (G.grade ν) →ₗ[LaurentPolynomial ℤ] K0 (G.grade ν') →ₗ[LaurentPolynomial ℤ]
    K0 (G.grade (ν + ν')) :=
  LinearMap.mk₂ (LaurentPolynomial ℤ) (fun x y => G.indK0Add ν ν' x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun p x y => K0.map_smul_of_shift ((G.indK0Add ν ν').flip y)
      (fun a x => G.indK0Add_shift_left a x y) p x)
    (fun x y y' => map_add _ y y')
    (fun p x y => K0.map_smul_of_shift (G.indK0Add ν ν' x)
      (fun a y => G.indK0Add_shift_right a x y) p y)

@[simp] theorem indK0_apply (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    G.indK0 ν ν' x y = G.indK0Add ν ν' x y := rfl

/-- `[P] · [P'] = [Ind_{ν,ν'} (P ⊠ P')]`. -/
theorem indK0_of (P : GProj (G.grade ν)) (P' : GProj (G.grade ν')) :
    G.indK0 ν ν' (K0.of P) (K0.of P') = K0.of (G.indProj P P') :=
  G.indK0Add_of P P'

/-! ### Induction of modules `R(ν) e` -/

section Idempotent

variable {e : KLRAlgebra k Q ν} {e' : KLRAlgebra k Q ν'}

theorem concat_idem (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    IsIdempotentElem (concat Q ν ν' (e ⊗ₜ e')) := by
  rw [IsIdempotentElem, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, he.eq, he'.eq]

theorem concat_mem_grade_zero (he0 : e ∈ G.grade ν 0) (he0' : e' ∈ G.grade ν' 0) :
    concat Q ν ν' (e ⊗ₜ e') ∈ G.grade (ν + ν') 0 := by
  simpa using G.concat_tmul_mem_grade he0 he0'

variable (e e') in
/-- The inclusion `R(ν) e ⊠ R(ν') e' → R(ν) ⊗ R(ν')`. -/
def idemIncl : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e') →ₗ[TensorKLR Q ν ν']
    TensorKLR Q ν ν' :=
  (ExtTensor.selfEquiv k (KLRAlgebra k Q ν) (KLRAlgebra k Q ν')).toLinearMap ∘ₗ
    ExtTensor.map (Graded.leftIdeal e).subtype (Graded.leftIdeal e').subtype

@[simp] theorem idemIncl_tmul (x : Graded.leftIdeal e) (y : Graded.leftIdeal e') :
    idemIncl e e' (ExtTensor.tmul x y) = (x : KLRAlgebra k Q ν) ⊗ₜ (y : KLRAlgebra k Q ν') :=
  rfl

theorem idemIncl_mul (n : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) :
    idemIncl e e' n * (e ⊗ₜ e') = idemIncl e e' n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_mul]
  | tmul x y =>
    rw [idemIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, Graded.mem_leftIdeal.1 x.2,
      Graded.mem_leftIdeal.1 y.2]
  | add n n' hn hn' => rw [map_add, add_mul, hn, hn']

theorem idemIncl_smul_unit (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (n : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) :
    idemIncl e e' n • ExtTensor.tmul (k := k) (⟨e, he.eq⟩ : Graded.leftIdeal e)
      (⟨e', he'.eq⟩ : Graded.leftIdeal e') = n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_smul]
  | tmul x y =>
    rw [idemIncl_tmul, ExtTensor.smul_tmul]
    congr 1
    · exact Subtype.ext (Graded.mem_leftIdeal.1 x.2)
    · exact Subtype.ext (Graded.mem_leftIdeal.1 y.2)
  | add n n' hn hn' => rw [map_add, add_smul, hn, hn']

variable (e e') in
/-- The bilinear map `(m, n) ↦ m ι(n)` inducing `Ind (R(ν) e ⊠ R(ν') e') → R(ν + ν') ι(e ⊗ e')`.
-/
def indIdemBil : IndBimod Q ν ν' →ₗ[k] ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e') →ₗ[k]
    Graded.leftIdeal (concat Q ν ν' (e ⊗ₜ e')) :=
  LinearMap.mk₂ k (fun m n => ⟨(m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n),
      by rw [Graded.mem_leftIdeal, mul_assoc, ← concat_mul, idemIncl_mul]⟩)
    (fun m m' n => Subtype.ext (add_mul _ _ _))
    (fun c m n => Subtype.ext (smul_mul_assoc _ _ _))
    (fun m n n' => Subtype.ext (by
      show (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' (n + n')) =
        (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n) +
          (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n')
      rw [map_add, map_add, mul_add]))
    (fun c m n => Subtype.ext (by
      show (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' (c • n)) =
        c • ((m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n))
      rw [LinearMap.map_smul_of_tower, map_smul, mul_smul_comm]))

variable (he : IsIdempotentElem e) (he' : IsIdempotentElem e')

theorem mul_oneConcat_of_mem {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ Graded.leftIdeal (concat Q ν ν' (e ⊗ₜ e'))) : r * oneConcat Q ν ν' = r := by
  have hr' : r * concat Q ν ν' (e ⊗ₜ e') = r := hr
  rw [← hr', mul_assoc, concat_mul_oneConcat]

variable (e e') in
/-- The linear isomorphism `Ind (R(ν) e ⊠ R(ν') e') ≅ R(ν + ν') ι(e ⊗ e')`. -/
def indIdemEquiv (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    Ind Q ν ν' (ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) ≃ₗ[KLRAlgebra k Q (ν + ν')]
      Graded.leftIdeal (concat Q ν ν' (e ⊗ₜ e')) :=
  LinearEquiv.ofLinear
    (BalancedTensor.liftB (indIdemBil e e')
      (fun m t n => Subtype.ext (by
        show (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' t * concat Q ν ν' (idemIncl e e' n) =
          (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' (t • n))
        rw [map_smul, smul_eq_mul, concat_mul, mul_assoc]))
      (fun r m n => Subtype.ext (by
        show r * (m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n) =
          r * ((m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n))
        rw [mul_assoc])))
    { toFun := fun r => BalancedTensor.tmul
        (⟨(r : KLRAlgebra k Q (ν + ν')), mul_oneConcat_of_mem r.2⟩ : IndBimod Q ν ν')
        (ExtTensor.tmul (k := k) (⟨e, he.eq⟩ : Graded.leftIdeal e)
          (⟨e', he'.eq⟩ : Graded.leftIdeal e'))
      map_add' := fun r r' => by
        rw [← BalancedTensor.add_tmul]
        exact congrArg (BalancedTensor.tmul · _) (Subtype.ext rfl)
      map_smul' := fun b r => by
        rw [RingHom.id_apply, BalancedTensor.smul_tmul']
        exact congrArg (BalancedTensor.tmul · _) (Subtype.ext rfl) }
    (LinearMap.ext fun r => Subtype.ext (by
      show (r : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (e ⊗ₜ e') = r
      exact r.2))
    (BalancedTensor.extB fun m n => by
      show BalancedTensor.tmul (⟨(m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n),
          _⟩ : IndBimod Q ν ν') _ = BalancedTensor.tmul m n
      rw [show (⟨(m : KLRAlgebra k Q (ν + ν')) * concat Q ν ν' (idemIncl e e' n),
          mul_concat_mem m _⟩ : IndBimod Q ν ν') = op (idemIncl e e' n) • m from rfl,
        BalancedTensor.op_smul_tmul, idemIncl_smul_unit he he'])

variable (he0 : e ∈ G.grade ν 0) (he0' : e' ∈ G.grade ν' 0)

/-- **`Ind (R(ν) e ⊠ R(ν') e') ≅ R(ν + ν') ι(e ⊗ e')`** for degree-zero idempotents `e`, `e'`. -/
def indIdemIso :
    (G.indProj (GProj.ofIdempotent e he he0) (GProj.ofIdempotent e' he' he0')).Iso
      (GProj.ofIdempotent (concat Q ν ν' (e ⊗ₜ e')) (concat_idem he he')
        (G.concat_mem_grade_zero he0 he0')) :=
  GradedEquiv.ofPreserves (indIdemEquiv e e' he he') fun _ y hy =>
    balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
      (Graded.submodule (G.grade (ν + ν')) (Graded.leftIdeal (concat Q ν ν' (e ⊗ₜ e'))))
      ((indIdemEquiv e e' he he').toLinearMap.restrictScalars k)
      (fun _ _ m n hm hn => by
        have hn' := ExtTensor.grading_map_mem _ _
          (tensorGrading (G.grade ν) (G.grade ν')) ((idemIncl e e').restrictScalars k)
          (fun _ _ x y hx hy => tmul_mem_tensorGrading hx hy) hn
        exact SetLike.GradedMul.mul_mem (A := G.grade (ν + ν')) hm (G.concat_mem_grade hn'))
      (y := y) hy

/-- `[Ind (R(ν) e ⊠ R(ν') e')] = [R(ν + ν') ι(e ⊗ e')]`. -/
theorem indK0_ofIdempotent :
    G.indK0 ν ν' (K0.of (GProj.ofIdempotent e he he0)) (K0.of (GProj.ofIdempotent e' he' he0')) =
      K0.of (GProj.ofIdempotent (concat Q ν ν' (e ⊗ₜ e')) (concat_idem he he')
        (G.concat_mem_grade_zero he0 he0')) := by
  rw [indK0_of]
  exact K0.of_eq_of_iso (G.indIdemIso he he' he0 he0')

end Idempotent

/-- **`Ind (P_i ⊠ P_j) ≅ P_{ij}`** (KL I, §2.6), with `P_i = R(ν) 1_i`. -/
def indProjE (i : Seq ν) (j : Seq ν') :
    (G.indProj (GProj.ofIdempotent (e i) (e_mul_self i) (G.e_mem_grade i))
      (GProj.ofIdempotent (e j) (e_mul_self j) (G.e_mem_grade j))).Iso
      (GProj.ofIdempotent (e (i.append j)) (e_mul_self _) (G.e_mem_grade _)) :=
  (G.indIdemIso (e_mul_self i) (e_mul_self j) (G.e_mem_grade i) (G.e_mem_grade j)).trans
    (GProj.ofIdempotentCongr (concat_e_tmul_e i j) _ _ _ _)

end GradingDatum

end KLR

namespace KLR.GradingDatum

open KLRAlgebra

variable {I : Type*} [DecidableEq I] {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  (G : GradingDatum Q) {ν ν' : Multiset I}

/-- **`Ind_{ν,ν'} (P_i ⊠ P_j) ≅ P_{ij}`** (KL I, §2.6). -/
def indProjP (i : Seq ν) (j : Seq ν') :
    (G.indProj (G.projP i) (G.projP j)).Iso (G.projP (i.append j)) :=
  G.indProjE i j

/-- `[P_i] · [P_j] = [P_{ij}]` in `K₀`. -/
theorem indK0_projP (i : Seq ν) (j : Seq ν') :
    G.indK0 ν ν' (K0.of (G.projP i)) (K0.of (G.projP j)) = K0.of (G.projP (i.append j)) := by
  rw [indK0_of]
  exact K0.of_eq_of_iso (G.indProjP i j)

end KLR.GradingDatum

end Categorification
