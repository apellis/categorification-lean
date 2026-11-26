/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeWordProjectives
import Categorification.WeightedKLR.RedStrands.NegativeTensorInjective
import Categorification.WeightedKLR.RedStrands.TensorModuleEquiv

/-!
# The Grothendieck group of `T̃^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 4.39: `K₀(T̃^λ) ≅ U_q^{-,ℤ} ⊗ V^ℤ_λ`, sending the class of the divided word
projective `[P̃_w]` to the vector `p̃_w`.

The proof follows Webster's, with one large weight in each black content instead of the
limit `N → ∞`. Fix a dominant `λ₀` with `⟨α_i^∨, λ₀⟩ ≥ 1` for all `i`, and a black content
`β`. For `N` large:

* extension of scalars along `prependRed : T̃^λ_β → T^{(Nλ₀, λ)}_β` (the functor `𝔯_N`) is
  bijective on `K₀` (`prependRedK0_bijective`) and sends `[P̃_w]` to `[P_{r(w)}]`
  (`prependRedK0_tildeWordClass`);
* Theorem 4.38 identifies `K₀(T^{(Nλ₀, λ)}_β)` with the weight `β` part of
  `V^ℤ_{Nλ₀} ⊗ V^ℤ_λ`, sending `[P_{r(w)}]` to `p_{r(w)}`;
* the map `𝔮_N (u ⊗ w) = u v_{Nλ₀} ⊗ w` sends `p̃_w` to `p_{r(w)}`
  (`negTensorMap_negWordVector`) and is injective on the vectors of content `β`
  (`negTensorMap_injective_below`).

So the classes `[P̃_w]` and the vectors `p̃_w` satisfy the same relations in each black
content, and both span. The contents assemble into a direct sum since `𝔮_N` separates them.

## Main definitions

* `negTensorLattice` : the `ℤ[q, q⁻¹]`-span of the vectors `p̃_w`.

## Main results

* `exists_tildeTensorEquiv` : **Webster, Proposition 4.39**.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Categorification.Graded GProj QuantumGroup LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom :=
  RingHomInvPair.of_ringEquiv invLP

/-- Two families spanning modules over `ℤ[q, q⁻¹]` correspond under a semilinear equivalence
for `q ↦ q⁻¹` as soon as they satisfy the same finite relations. -/
private theorem generatorEquiv_of_relations {J P V : Type*} [AddCommGroup P] [Module LP P]
    [AddCommGroup V] [Module LP V] (p : J → P) (v : J → V)
    (hp : Submodule.span LP (Set.range p) = ⊤) (hv : Submodule.span LP (Set.range v) = ⊤)
    (rel : ∀ a : J →₀ LP, a.sum (fun j c => c • p j) = 0 ↔ a.sum (fun j c => invLP c • v j) = 0) :
    ∃ e : P ≃ₛₗ[invLP.toRingHom] V, ∀ j, e (p j) = v j := by
  let A := Finsupp.linearCombination LP p
  let B := Finsupp.linearCombination LP v
  let σ : (J →₀ LP) ≃ₛₗ[invLP.toRingHom] (J →₀ LP) :=
    Finsupp.mapRange.linearEquiv invLP.toSemilinearEquiv
  let D : (J →₀ LP) →ₛₗ[invLP.toRingHom] V := B.comp σ.toLinearMap
  have hD (a : J →₀ LP) : D a = a.sum (fun j c => invLP c • v j) := by
    change (Finsupp.mapRange invLP (map_zero _) a).sum _ = _
    rw [Finsupp.sum_mapRange_index]
    · rfl
    · intro j; simp
  have genA (j : J) : A (Finsupp.single j 1) = p j := by simp [A]
  have genD (j : J) : D (Finsupp.single j 1) = v j := by
    rw [hD, Finsupp.sum_single_index]; all_goals simp
  have hker (a : J →₀ LP) : A a = 0 ↔ D a = 0 := by rw [hD]; exact rel a
  have surA : Function.Surjective A :=
    LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination (v := p) LP).trans hp)
  have surB : Function.Surjective B :=
    LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination (v := v) LP).trans hv)
  have hk : LinearMap.ker A ≤ LinearMap.ker D := fun a ha => (hker a).mp ha
  let f := ((LinearMap.ker A).liftQ D hk).comp
    (A.quotKerEquivOfSurjective surA).symm.toLinearMap
  have hf (a : J →₀ LP) : f (A a) = D a := by
    change (LinearMap.ker A).liftQ D hk ((A.quotKerEquivOfSurjective surA).symm (A a)) = D a
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have inj : Function.Injective f := by
    rintro x y h
    obtain ⟨a, rfl⟩ := surA x
    obtain ⟨b, rfl⟩ := surA y
    rw [hf, hf] at h
    have hz := (hker (a - b)).mpr (by rw [D.map_sub]; exact sub_eq_zero.mpr h)
    rw [A.map_sub] at hz
    exact sub_eq_zero.mp hz
  have sur : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := surB y
    refine ⟨A (σ.symm a), (hf _).trans ?_⟩
    change B (σ (σ.symm a)) = y
    rwa [σ.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective f ⟨inj, sur⟩, fun j => ?_⟩
  change f (p j) = v j
  rw [← genA j, hf, genD]

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

local notation "D" => C.toLusztig

/-! ### The lattice of the vectors `p̃_w` -/

instance negTensorLaurentModule (wt : Fin ℓ → Dom R) : Module LP (NegTensor D wt) :=
  Module.compHom _ integralLaurentEval

theorem negTensor_laurent_smul {wt : Fin ℓ → Dom R} (c : LP) (x : NegTensor D wt) :
    c • x = integralLaurentEval c • x := rfl

theorem negTensorMap_laurent_smul {n : ℕ} (wt : Fin (n + 1) → Dom R) (c : LP)
    (x : NegTensor D (fun j : Fin n => wt j.succ)) :
    negTensorMap D wt (c • x) = c • negTensorMap D wt x := by
  rw [negTensor_laurent_smul, tensor_laurent_smul, map_smul]

/-- `𝔮_N` for the labels `(λ₀, λ)`, with source `U⁻ ⊗ V^λ` stated directly. -/
def negTensorMapCons (ω₀ : Dom R) (wt : Fin ℓ → Dom R) :
    NegTensor D wt →ₗ[𝕂] TensorSpace (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) :=
  negTensorMap D (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R)

theorem negTensorMapCons_laurent_smul (ω₀ : Dom R) (wt : Fin ℓ → Dom R) (c : LP)
    (x : NegTensor D wt) : negTensorMapCons C ω₀ wt (c • x) = c • negTensorMapCons C ω₀ wt x :=
  negTensorMap_laurent_smul C (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) c x

theorem negTensorMapCons_negWordVector (ω₀ : Dom R) (wt : Fin ℓ → Dom R) (w : TensorWord I ℓ) :
    negTensorMapCons C ω₀ wt (negWordVector D w wt) =
      tensorWordVector w.prependRed (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) :=
  negTensorMap_negWordVector w (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R)

include hR in
theorem negTensorMapCons_eq_zero [Finite I] {ω₀ : Dom R} {wt : Fin ℓ → Dom R} {β : I →₀ ℕ}
    (hΛ : ∀ i, (β.degree : ℤ) ≤ ω₀.1 (R.coroot i)) {x : NegTensor D wt}
    (hx : x ∈ negTensorBelow D wt β) (h : negTensorMapCons C ω₀ wt x = 0) : x = 0 :=
  negTensorMap_injective_below hR (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hΛ hx
    (zero_mem _) (h.trans (map_zero _).symm)

/-- The `ℤ[q, q⁻¹]`-span of the vectors `p̃_w`. -/
def negTensorLattice (wt : Fin ℓ → Dom R) : Submodule LP (NegTensor D wt) :=
  Submodule.span LP (Set.range fun w : TensorWord I ℓ => negWordVector D w wt)

/-- The `ℤ[q, q⁻¹]`-span of the vectors `p̃_w` of black content `β`. -/
def negTensorLatticeAt (wt : Fin ℓ → Dom R) (β : Multiset I) : Submodule LP (NegTensor D wt) :=
  Submodule.span LP {x | ∃ w : TensorWord I ℓ, w.content.toMultiset = β ∧
    x = negWordVector D w wt}

/-- The vector `p̃_w` in the lattice of its black content. -/
def negWordVectorAt (wt : Fin ℓ → Dom R) (β : Multiset I) (w : TensorWordAt ℓ β) :
    negTensorLatticeAt (C := C) wt β :=
  ⟨negWordVector D w.1 wt, Submodule.subset_span ⟨w.1, w.2, rfl⟩⟩

theorem span_negWordVectorAt (wt : Fin ℓ → Dom R) (β : Multiset I) :
    Submodule.span LP (Set.range (negWordVectorAt C wt β)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).2
  congr 1
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem mem_negTensorBelow_of_mem_latticeAt {wt : Fin ℓ → Dom R} {β : Multiset I}
    {x : NegTensor D wt} (hx : x ∈ negTensorLatticeAt (C := C) wt β) :
    x ∈ negTensorBelow D wt β.toFinsupp := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have := negWordVector_mem_negTensorBelow w wt
    rw [← hw, Finsupp.toMultiset_toFinsupp]
    exact this
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => rw [negTensor_laurent_smul]; exact Submodule.smul_mem _ _ hx

/-! ### A large first label -/

section Labels

omit [DecidableEq I]
variable {C}

/-- A multiple of a dominant weight with positive coroot pairings, as large as needed. -/
private def largeWeight (ω : Dom R) (N : ℕ) : Dom R :=
  ⟨N • ω.1, fun i => by rw [AddMonoidHom.nsmul_apply]; exact nsmul_nonneg (ω.2 i) N⟩

private theorem largeWeight_coroot {ω : Dom R} (h₁ : ∀ i, 1 ≤ ω.1 (R.coroot i)) (N : ℕ)
    (i : I) : (N : ℤ) ≤ (largeWeight ω N).1 (R.coroot i) := by
  change (N : ℤ) ≤ (N • ω.1) (R.coroot i)
  rw [AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  nlinarith [h₁ i]

/-- The labels of a dominant weight, as a finitely supported function. -/
private def weightLabels [Finite I] (ω₀ : Dom R) : I →₀ ℕ :=
  let := Fintype.ofFinite I
  Finsupp.equivFunOnFinite.symm fun i => (ω₀.1 (R.coroot i)).toNat

private theorem weightLabels_apply [Finite I] (ω₀ : Dom R) (i : I) :
    ((weightLabels ω₀ i : ℕ) : ℤ) = ω₀.1 (R.coroot i) := by
  simp [weightLabels, Int.toNat_of_nonneg (ω₀.2 i)]

end Labels

local notation "moduleGrading" Λ' =>
  stendhalGradingDatum Λ' hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private theorem gradingDatum_ext {J : Type*} {Q' : J → J → MvPolynomial (Fin 2) k}
    {G₁ G₂ : GradingDatum Q'} (h1 : G₁.degX = G₂.degX) (h2 : G₁.degΨ = G₂.degΨ) : G₁ = G₂ := by
  cases G₁; cases G₂
  simp only at h1 h2
  subst h1; subst h2
  rfl

omit [DecidableEq I] in
/-- Omitting the first red colour of the grading of `T^{(λ₀, λ)}` gives the grading of
`T^λ`. -/
theorem restrictFirstRedGrading_cons (Λ₀ : I →₀ ℕ) (Λ : Fin ℓ → I →₀ ℕ) :
    restrictFirstRedGrading Q (Fin.cons Λ₀ Λ : Fin (ℓ + 1) → I →₀ ℕ)
      (moduleGrading (Fin.cons Λ₀ Λ : Fin (ℓ + 1) → I →₀ ℕ)) = moduleGrading Λ := by
  apply gradingDatum_ext
  · funext a; rcases a with i | r <;> rfl
  · funext a b; rcases a with i | r <;> rcases b with j | s <;> rfl

/-- Transport of `K₀(T̃^λ)` along an equality of gradings. -/
private def gradingTransport {Λ' : Fin ℓ → I →₀ ℕ} {G₁ G₂ : GradingDatum (stendhalQ Q Λ')}
    (h : G₁ = G₂) (ν : Multiset I) :
    K0 (stendhalGrade G₁ ν) ≃ₗ[LP] K0 (stendhalGrade G₂ ν) := by
  subst h; exact LinearEquiv.refl _ _

private theorem gradingTransport_tildeWordClass {Λ' : Fin ℓ → I →₀ ℕ}
    {G₁ G₂ : GradingDatum (stendhalQ Q Λ')} (h : G₁ = G₂) (hs₁ hs₂) (w : TensorWord I ℓ) :
    gradingTransport h _ (tildeWordClass Λ' C G₁ hs₁ w) = tildeWordClass Λ' C G₂ hs₂ w := by
  subst h; rfl

/-- `h ▸` on a divided sequence projective only changes its black content. -/
private theorem K0_of_dividedSequenceProj_cast (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (d : List ((I ⊕ Fin (ℓ + 1)) × ℕ)) (hw hw') :
    h ▸ K0.of (dividedSequenceProj Λ' C hQ ν d hw) = K0.of (dividedSequenceProj Λ' C hQ ν' d hw') := by
  subst h; rfl

/-! ### One black content -/

section Content

variable (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)

omit [DecidableEq I] in
theorem moduleGrading_cross_symm :
    ∀ a b, (moduleGrading Λ).degΨ a b = (moduleGrading Λ).degΨ b a := fun a b => by
  have h := restrictFirstRedGrading_cross_symm (Fin.cons 0 Λ : Fin (ℓ + 1) → I →₀ ℕ) C hQ a b
  rwa [restrictFirstRedGrading_cons] at h

omit [DecidableEq I] in
theorem moduleGrading_degX_pos {m : ℕ} (Λ' : Fin m → I →₀ ℕ) :
    ∀ a, 0 < (moduleGrading Λ').degX a := by
  rintro (i | r)
  · exact C.dot_self_pos i
  · change (0 : ℤ) < 2
    norm_num

/-- **The divided word projective `[P̃_w]`** of `T̃^λ` (Webster, arXiv:1309.3796v3, before
Proposition 4.39). -/
def tildeClass (w : TensorWord I ℓ) : K0 (stendhalGrade (moduleGrading Λ) w.content.toMultiset) :=
  tildeWordClass Λ C (moduleGrading Λ) (moduleGrading_cross_symm C hQ Λ) w

/-- `[P̃_w]` at its specified black content. -/
def tildeClassAt (β : Multiset I) (w : TensorWordAt ℓ β) :
    K0 (stendhalGrade (moduleGrading Λ) β) :=
  w.2 ▸ tildeClass C hQ Λ w.1

/-- Adding a red strand on the left, on words of a fixed black content. -/
def TensorWordAt.prependRed {β : Multiset I} (w : TensorWordAt ℓ β) : TensorWordAt (ℓ + 1) β :=
  ⟨w.1.prependRed, by rw [w.1.content_prependRed]; exact w.2⟩

omit [DecidableEq I] in
theorem TensorWordAt.prependRed_injective {β : Multiset I} :
    Function.Injective (TensorWordAt.prependRed (ℓ := ℓ) (β := β)) := by
  intro w w' h
  apply Subtype.ext
  have := congrArg (fun x : TensorWordAt (ℓ + 1) β => x.1.eraseFirstRed) h
  simpa only [TensorWordAt.prependRed, TensorWord.eraseFirstRed_prependRed] using this

include hR in
/-- The comparison with `T^{(λ₀, λ)}` for a large first label `λ₀` (Webster,
arXiv:1309.3796v3, proof of Proposition 4.39): `𝔯_N` is bijective on `K₀` in black content
`β` and sends `[P̃_w]` to `[P_{r(w)}]`, and Theorem 4.38 holds for `(λ₀, λ)`. -/
private theorem exists_firstRedComparison [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (β : Multiset I) (M : ℕ) :
    ∃ ω₀ : Dom R, (∀ i, (M : ℤ) ≤ ω₀.1 (R.coroot i)) ∧
      ∃ Φ : K0 (stendhalGrade (moduleGrading Λ) β) →ₗ[LP]
          K0 (tensorProductGrade (moduleGrading
            (Fin.cons (weightLabels ω₀) Λ : Fin (ℓ + 1) → I →₀ ℕ)) β),
        Function.Bijective Φ ∧
        SameWordRelations (Fin.cons (weightLabels ω₀) Λ) C hQ (Fin.cons ω₀ wt) hR β ∧
        ∀ w, Φ (tildeClassAt C hQ Λ β w) =
          projectiveWordAt (Fin.cons (weightLabels ω₀) Λ) C hQ β w.prependRed := by
  classical
  obtain ⟨ω, h₁⟩ := hρ
  obtain ⟨c, hc⟩ := exists_allOrdersGrade_eq_bot (moduleGrading Λ) β
    (stendhalQ_symm Q Λ hQ.klrSymm) (moduleGrading_degX_pos C hQ Λ)
  set N : ℕ := M + 2 * c.toNat + 1 with hN
  set ω₀ := largeWeight ω N
  set Λf : Fin (ℓ + 1) → I →₀ ℕ := Fin.cons (weightLabels ω₀) Λ
  set wtf : Fin (ℓ + 1) → Dom R := Fin.cons ω₀ wt
  have hwtf : ∀ r i, (Λf r i : ℤ) = (wtf r).1 (R.coroot i) := by
    intro r i
    refine Fin.cases ?_ (fun r => ?_) r
    · simp only [Λf, wtf, Fin.cons_zero]
      exact weightLabels_apply ω₀ i
    · simp only [Λf, wtf, Fin.cons_succ]
      exact hwt r i
  have hrel := (exists_tensorWordEquiv_iff Λf C hQ wtf hR).mp
    (exists_tensorWordEquiv C hQ hR Λf wtf hwtf) β
  have hG := restrictFirstRedGrading_cons C hQ (weightLabels ω₀) Λ
  let Φ := (prependRedK0 Q Λf β (moduleGrading Λf)).comp (gradingTransport hG.symm β).toLinearMap
  have hNc : 2 * c < (N : ℤ) := by
    have := Int.self_le_toNat c
    rw [hN]; push_cast; omega
  have hΦ : Function.Bijective Φ := by
    refine (prependRedK0_bijective Q Λf β (moduleGrading Λf) hQ.klrSymm
      (moduleGrading_degX_pos C hQ Λf) (c := c) (fun n hn => ?_) (fun i _ => ?_)).comp
      (gradingTransport hG.symm β).bijective
    · rw [hG]; exact hc n hn
    · have h1 := largeWeight_coroot h₁ N i
      have h2 := weightLabels_apply ω₀ i
      have h3 := moduleGrading_degX_pos C hQ Λf (.inl i)
      change 2 * c < ((weightLabels ω₀ i : ℕ) : ℤ) * (moduleGrading Λf).degX (.inl i)
      nlinarith
  have hΦw (w : TensorWordAt ℓ β) :
      Φ (tildeClassAt C hQ Λ β w) = projectiveWordAt Λf C hQ β w.prependRed := by
    obtain ⟨w, rfl⟩ := w
    change prependRedK0 Q Λf _ (moduleGrading Λf) (gradingTransport hG.symm _
      (tildeWordClass Λ C (moduleGrading Λ) (moduleGrading_cross_symm C hQ Λ) w)) = _
    rw [gradingTransport_tildeWordClass C hG.symm _ (restrictFirstRedGrading_cross_symm Λf C hQ)]
    refine (prependRedK0_tildeWordClass Λf C hQ w).trans ?_
    exact (K0_of_dividedSequenceProj_cast C hQ Λf _ _ _ _).symm
  refine ⟨ω₀, fun i => le_trans (by rw [hN]; push_cast; omega) (largeWeight_coroot h₁ N i),
    Φ, hΦ, hrel, hΦw⟩

include hR in
/-- **The classes `[P̃_w]` and the vectors `p̃_w` satisfy the same relations** in each
black content (Webster, arXiv:1309.3796v3, proof of Proposition 4.39). Route hypothesis:
a dominant weight `λ₁` with `⟨α_i^∨, λ₁⟩ ≥ 1` for all `i`, used to build the large first
label `λ₀ = Nλ₁`. -/
theorem tildeRelations [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (β : Multiset I)
    (a : TensorWordAt ℓ β →₀ LP) :
    a.sum (fun w c => c • tildeClassAt C hQ Λ β w) = 0 ↔
      a.sum (fun w c => LaurentPolynomial.invert c • negWordVectorAt C wt β w) = 0 := by
  classical
  obtain ⟨ω₀, hdeg, rN, hr, hrel, hrw⟩ :=
    exists_firstRedComparison C hQ hR Λ wt hρ hwt β β.toFinsupp.degree
  let Λf : Fin (ℓ + 1) → I →₀ ℕ := Fin.cons (weightLabels ω₀) Λ
  let wtf : Fin (ℓ + 1) → Dom R := Fin.cons ω₀ wt
  have hmemw (w : TensorWordAt ℓ β) :
      negWordVector D w.1 (fun j => wtf j.succ) ∈ negTensorBelow D _ β.toFinsupp := by
    have h := negWordVector_mem_negTensorBelow w.1 (fun j => wtf j.succ)
    rwa [show w.1.content = β.toFinsupp from (congrArg Multiset.toFinsupp w.2).symm.trans
      (Finsupp.toMultiset_toFinsupp _) |>.symm] at h
  set x : NegTensor D (fun j : Fin ℓ => wtf j.succ) :=
    a.sum (fun w c => LaurentPolynomial.invert c • negWordVector D w.1 (fun j => wtf j.succ))
    with hx
  have hxmem : x ∈ negTensorBelow D _ β.toFinsupp :=
    Submodule.sum_mem _ fun w _ => by
      dsimp only
      rw [negTensor_laurent_smul]; exact Submodule.smul_mem _ _ (hmemw w)
  have hq : negTensorMap D wtf x = ((a.sum (fun w c => LaurentPolynomial.invert c •
      vectorWordAt (C := C) wtf hR β w.prependRed) : integralTensorWeight wtf hR β.toFinsupp) :
        TensorSpace wtf) := by
    rw [hx, map_finsuppSum, Finsupp.sum, Finsupp.sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [negTensorMap_laurent_smul, negTensorMap_negWordVector, Submodule.coe_smul]
    rfl
  have hx' : ((a.sum (fun w c => LaurentPolynomial.invert c • negWordVectorAt C wt β w) :
      negTensorLatticeAt (C := C) wt β) : NegTensor D wt) = x := by
    rw [Finsupp.sum, Submodule.coe_sum, hx, Finsupp.sum]
    rfl
  calc a.sum (fun w c => c • tildeClassAt C hQ Λ β w) = 0
      ↔ rN (a.sum (fun w c => c • tildeClassAt C hQ Λ β w)) = 0 :=
        ⟨fun h => by rw [h, map_zero], fun h => hr.1 (by rw [h, map_zero])⟩
    _ ↔ (a.mapDomain TensorWordAt.prependRed).sum
          (fun w c => c • projectiveWordAt Λf C hQ β w) = 0 := by
        rw [map_finsuppSum, Finsupp.sum_mapDomain_index
          (h := fun w (c : LP) => c • projectiveWordAt Λf C hQ β w) (fun _ => zero_smul _ _)
          (fun _ _ _ => add_smul _ _ _)]
        simp only [map_smul, hrw]
        exact Iff.rfl
    _ ↔ (a.mapDomain TensorWordAt.prependRed).sum
          (fun w c => LaurentPolynomial.invert c • vectorWordAt (C := C) wtf hR β w) = 0 := hrel _
    _ ↔ a.sum (fun w c => LaurentPolynomial.invert c •
          vectorWordAt (C := C) wtf hR β w.prependRed) = 0 := by
        rw [Finsupp.sum_mapDomain_index
          (h := fun w (c : LP) => LaurentPolynomial.invert c • vectorWordAt (C := C) wtf hR β w)
          (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
    _ ↔ negTensorMap D wtf x = 0 := by rw [hq]; exact Submodule.coe_eq_zero.symm
    _ ↔ x = 0 := ⟨fun h => negTensorMap_injective_below hR wtf hdeg hxmem (zero_mem _)
          (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
    _ ↔ _ := by rw [← hx']; exact Submodule.coe_eq_zero


include hR in
/-- **The classes `[P̃_w]` span `K₀(T̃^λ)`** in each black content (Webster,
arXiv:1309.3796v3, proof of Proposition 4.39): `𝔯_N` is bijective, and every word class of
`T^{(λ₀, λ)}` is zero or the class of a word beginning with the red strand `λ₀`. -/
theorem span_tildeClassAt [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i))
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (β : Multiset I) :
    Submodule.span LP (Set.range (tildeClassAt C hQ Λ β)) = ⊤ := by
  classical
  obtain ⟨ω₀, -, rN, hr, hrel, hrw⟩ := exists_firstRedComparison C hQ hR Λ wt hρ hwt β 0
  have hgen (w' : TensorWordAt (ℓ + 1) β) : projectiveWordAt (Fin.cons (weightLabels ω₀) Λ : Fin (ℓ + 1) → I →₀ ℕ) C hQ β w' ∈
      Submodule.map rN (Submodule.span LP (Set.range (tildeClassAt C hQ Λ β))) := by
    rcases tensorWordVector_eq_zero_or w'.1 (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) with h | ⟨h, hc⟩
    · have hv : vectorWordAt (C := C) (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β w' = 0 := Subtype.ext h
      have := (hrel (Finsupp.single w' 1)).mpr (by
        rw [Finsupp.sum_single_index (by simp), map_one, one_smul, hv])
      rw [Finsupp.sum_single_index (by simp), one_smul] at this
      rw [this]
      exact zero_mem _
    · let u : TensorWordAt ℓ β := ⟨w'.1.eraseFirstRed, by rw [hc]; exact w'.2⟩
      have hv : vectorWordAt (C := C) (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β u.prependRed =
          vectorWordAt (C := C) (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β w' := Subtype.ext h.symm
      have := (hrel (Finsupp.single w' 1 + Finsupp.single u.prependRed (-1))).mpr (by
        rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add, add_smul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        rw [hv, map_neg, map_one, one_smul]
        apply Subtype.ext
        rw [Submodule.coe_add, Submodule.coe_smul, tensor_laurent_smul, map_neg, map_one]
        have e (z : TensorSpace (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R)) : z + (-1 : 𝕂) • z = 0 := by
          nth_rewrite 1 [← one_smul 𝕂 z]
          rw [← add_smul, add_neg_cancel, zero_smul]
        exact e _)
      rw [Finsupp.sum_add_index'
          (h := fun w (c : LP) => c • projectiveWordAt (Fin.cons (weightLabels ω₀) Λ : Fin (ℓ + 1) → I →₀ ℕ) C hQ β w) (fun _ => zero_smul _ _)
          (fun _ _ _ => add_smul _ _ _),
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul,
        neg_smul, one_smul, add_neg_eq_zero] at this
      rw [this, ← hrw u]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have htop : Submodule.map rN (Submodule.span LP (Set.range (tildeClassAt C hQ Λ β))) = ⊤ := by
    rw [eq_top_iff, ← span_projectiveWordAt (Fin.cons (weightLabels ω₀) Λ : Fin (ℓ + 1) → I →₀ ℕ) C hQ β, Submodule.span_le]
    rintro _ ⟨w', rfl⟩
    exact hgen w'
  apply Submodule.map_injective_of_injective hr.1
  rw [htop, Submodule.map_top, LinearMap.range_eq_top.mpr hr.2]

end Content

/-! ### Assembling the black contents -/

section Assembly

variable (wt : Fin ℓ → Dom R)

/-- The sum of the lattices of the black contents, mapped into `U⁻ ⊗ V^λ`. -/
def latticeJoin :
    DirectSum (Multiset I) (fun β => negTensorLatticeAt (C := C) wt β) →ₗ[LP] NegTensor D wt :=
  DirectSum.toModule LP _ _ (fun β => (negTensorLatticeAt (C := C) wt β).subtype)

theorem latticeJoin_lof (β : Multiset I) (x : negTensorLatticeAt (C := C) wt β) :
    latticeJoin C wt (DirectSum.lof LP _ _ β x) = x := by
  unfold latticeJoin
  exact DirectSum.toModule_lof LP (M := fun β => negTensorLatticeAt (C := C) wt β) β x

/-- `𝔮_N` maps the lattice of black content `β` into the weight `β` part of
`V^ℤ_{λ₀} ⊗ V^ℤ_λ`. -/
theorem negTensorMap_mem_integralTensorWeight [Finite I] (ω₀ : Dom R) {β : Multiset I}
    {x : NegTensor D wt} (hx : x ∈ negTensorLatticeAt (C := C) wt β) :
    negTensorMapCons C ω₀ wt x ∈
      integralTensorWeight (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β.toFinsupp := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' : w.prependRed.content.toMultiset = β := by rw [w.content_prependRed]; exact hw
    rw [negTensorMapCons_negWordVector]
    exact (vectorWordAt (C := C) (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β
      ⟨w.prependRed, hw'⟩).2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [negTensorMapCons_laurent_smul]
    exact Submodule.smul_mem _ _ hx

/-- `𝔮_N` on the lattice of black content `β`, with values in the weight `β` part. -/
def latticeAtTensorMap [Finite I] (ω₀ : Dom R) (β : Multiset I) :
    negTensorLatticeAt (C := C) wt β →ₗ[LP]
      integralTensorWeight (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR β.toFinsupp where
  toFun x := ⟨negTensorMapCons C ω₀ wt x,
    negTensorMap_mem_integralTensorWeight C hR wt ω₀ x.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (negTensorMapCons_laurent_smul C ω₀ wt c x)

theorem tensorWeightSumEquiv_lmap [Finite I] (ω₀ : Dom R)
    (z : DirectSum (Multiset I) (fun β => negTensorLatticeAt (C := C) wt β)) :
    ((tensorWeightSumEquiv C (Fin.cons ω₀ wt : Fin (ℓ + 1) → Dom R) hR
      (DirectSum.lmap (latticeAtTensorMap C hR wt ω₀) z) : _) : TensorSpace _) =
      negTensorMapCons C ω₀ wt (latticeJoin C wt z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of β x =>
    rw [← DirectSum.lof_eq_of LP, DirectSum.lmap_lof, latticeJoin_lof, DirectSum.lof_eq_of,
      tensorWeightSumEquiv_of]
    rfl
  | add _ _ hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy, map_add, map_add]

include hR in
/-- **The black contents are independent in `U⁻ ⊗ V^λ`** (Webster, arXiv:1309.3796v3, proof
of Proposition 4.39): `𝔮_N` maps them into distinct weight spaces of `V_{λ₀} ⊗ V^λ` and is
injective on finitely many of them for `N` large. -/
theorem latticeJoin_injective [Finite I] (hρ : ∃ ω : Dom R, ∀ i, 1 ≤ ω.1 (R.coroot i)) :
    Function.Injective (latticeJoin C wt) := by
  classical
  intro x y hxy
  obtain ⟨ω, h₁⟩ := hρ
  set S := DFinsupp.support x ∪ DFinsupp.support y
  set B : I →₀ ℕ := ∑ β ∈ S, β.toFinsupp
  set ω₀ := largeWeight ω B.degree
  let wtf : Fin (ℓ + 1) → Dom R := Fin.cons ω₀ wt
  have hq : DirectSum.lmap (latticeAtTensorMap C hR wt ω₀) x =
      DirectSum.lmap (latticeAtTensorMap C hR wt ω₀) y := by
    apply (tensorWeightSumEquiv C wtf hR).injective
    apply Subtype.ext
    rw [tensorWeightSumEquiv_lmap, tensorWeightSumEquiv_lmap, hxy]
  ext1 β
  by_cases hβ : β ∈ S
  · have h0 := congrArg Subtype.val (DFunLike.congr_fun hq β)
    change negTensorMapCons C ω₀ wt (x β : NegTensor D wt) =
      negTensorMapCons C ω₀ wt (y β : NegTensor D wt) at h0
    have hle : β.toFinsupp ≤ B :=
      Finset.single_le_sum (f := Multiset.toFinsupp) (fun _ _ => zero_le) hβ
    exact Subtype.ext (negTensorMap_injective_below hR wtf (largeWeight_coroot h₁ _)
      (negTensorBelow_mono wt hle (mem_negTensorBelow_of_mem_latticeAt C (x β).2))
      (negTensorBelow_mono wt hle (mem_negTensorBelow_of_mem_latticeAt C (y β).2)) h0)
  · rw [Finset.mem_union, not_or] at hβ
    rw [DFinsupp.notMem_support_iff.mp hβ.1, DFinsupp.notMem_support_iff.mp hβ.2]

end Assembly

end Categorification.Stendhal.FirstWeight
