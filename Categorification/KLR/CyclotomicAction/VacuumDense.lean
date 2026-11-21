/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumMorita

/-!
# Density of the images of the vacuum module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Prop. 3.25
and Cor. 3.27. Every finitely generated projective `Ř^λ`-module is a retract of a finite direct
sum of modules `F_s P_∅`, the images of the vacuum module `P_∅` under the 1-morphisms out of its
region (`exists_vacuum_retract`). The proof splits a module into its weight blocks, takes a
finite dual basis of each block, and writes each basis element through the generators
`e(t) ∈ F_{t} P_∅` of the cyclotomic quotient.
-/

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory CategoryTheory.Limits TwoRep KLRAlgebra
open QuantumGroup StringDiagrams Diagrams.BicatInterp KL3.Diagram

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

theorem exists_vacWord_gen {c : X} {ν : Multiset I} (hν : blockWeight RD Λ ν = c)
    (t : KLR.Seq ν) (hc : KL3.Diagram.wt RD (vacWt RD Λ) (ups (KLR.Diagram.word t)) = c) :
    ∃ (x : ((vacWordObj.{u, v, w} hQ RD Λ hΛ hc).obj ⟨ν, hν⟩ : Type _))
      (f : ((vacWordObj.{u, v, w} hQ RD Λ hΛ hc).obj ⟨ν, hν⟩ : Type _) →ₗ[CycKLR
        (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν] CycKLR (UnivCycRing k lam)
        (cycQ k lam Q) (univCycPoly k lam) ν),
      f x = CycKLR.mk _ _ _ ν (e t.rev) := by
  obtain rfl : c = _ := hc.symm.trans (RouqFamily.cond_word (vacWt RD Λ) t).2.2
  let iT := (univFamily (lam := lam) hQ RD Λ hΛ).upIso (vacWt RD Λ) t
    (RouqFamily.cond_word (vacWt RD Λ) t)
  let W := familyObj hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
    (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
    (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ)
  let e : _ ≅ _ := ⟨iT.hom.hom.app W, iT.inv.hom.app W,
    congrArg (fun f => f.hom.app W) iT.hom_inv_id, congrArg (fun f => f.hom.app W) iT.inv_hom_id⟩
  let eν := Pi.isoApp e ⟨ν, hν⟩
  let wg := wgen hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
      (univCycPoly_natDegree_pair RD Λ hΛ)
      (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) _ rfl (univVacGen RD Λ) t
  let wc := wcoord hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
      (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
      (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ) rfl
      (univVacCoord RD Λ) t
  refine ⟨eν.inv wg, wc.comp eν.hom.hom, ?_⟩
  exact (congrArg wc (Iso.inv_hom_id_apply eν wg)).trans
    (wcoord_wgen _ _ _ _ _ _ rfl _ (univVacCoord_univVacGen RD Λ) t)


/-! ### Generic lemmas -/

section Generic

/-- A finitely generated projective module has a finite dual basis. -/
theorem exists_fin_dualBasis (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    ∃ (n : ℕ) (m : Fin n → N) (s : N →ₗ[R] (Fin n → R)), ∀ y, ∑ j, s y j • m j = y := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun j => f fun i => if j = i then 1 else 0, s, fun y => ?_⟩
  rw [← LinearMap.pi_apply_eq_sum_univ f (s y)]
  exact LinearMap.congr_fun hs y

theorem sum_prod_smul_of_sum_eq_one {R N : Type*} [Ring R] [AddCommGroup N] [Module R N] {n : ℕ}
    {T : Type*} [Fintype T] (E : T → R) (hE : ∑ t, E t = 1) (s : Fin n → R) (m : Fin n → N) :
    ∑ i : Fin n × T, (s i.1 * E i.2) • m i.1 = ∑ j, s j • m j := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [← Finset.sum_smul, ← Finset.mul_sum, hE, mul_one]

/-- Composites through `R`-modules `N t` with elements `x t` and functionals `f t`,
`f t (x t) = E t`, `∑ E t = 1`, sum to the identity of a module with a finite dual basis. -/
theorem moduleCat_sum_comp_eq_id {R : Type*} [Ring R] {P : ModuleCat R} {T : Type*}
    [Fintype T] (N : T → ModuleCat R) (x : ∀ t, N t) (f : ∀ t, N t →ₗ[R] R) (E : T → R)
    (hE : ∑ t, E t = 1) (hf : ∀ t, f t (x t) = E t) {n : ℕ} (m : Fin n → P)
    (sd : P →ₗ[R] (Fin n → R)) (hs : ∀ y, ∑ j, sd y j • m j = y) :
    ∑ i : Fin n × T, (ModuleCat.ofHom (LinearMap.toSpanSingleton R (N i.2) (x i.2) ∘ₗ
      LinearMap.proj i.1 ∘ₗ sd) ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R P (m i.1) ∘ₗ
        f i.2)) = 𝟙 P := by
  ext y
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.proj_apply, map_smul, hf, smul_smul,
    ModuleCat.hom_id, LinearMap.id_apply]
  exact (sum_prod_smul_of_sum_eq_one E hE (sd y) m).trans (hs y)

variable {J : Type*} [DecidableEq J] {D : J → Type*} [∀ j, Category (D j)]
  [∀ j, Preadditive (D j)]

/-- The morphism of a product category with component `f` at `j` and zero elsewhere. -/
def piSingleHom {A B : ∀ j, D j} (j : J) (f : A j ⟶ B j) : A ⟶ B := fun j' =>
  if h : j' = j then by subst h; exact f else 0

theorem piSingleHom_self {A B : ∀ j, D j} (j : J) (f : A j ⟶ B j) :
    piSingleHom j f j = f := by
  simp [piSingleHom]

theorem piSingleHom_ne {A B : ∀ j, D j} {j j' : J} (h : j' ≠ j) (f : A j ⟶ B j) :
    piSingleHom j f j' = 0 := by
  simp [piSingleHom, h]

theorem piSingleHom_comp {A B B' : ∀ j, D j} (j : J) (f : A j ⟶ B j) (g : B j ⟶ B' j) :
    piSingleHom j f ≫ piSingleHom j g = piSingleHom j (f ≫ g) := by
  funext j'
  by_cases h : j' = j
  · subst h
    rw [pi_comp_apply, piSingleHom_self, piSingleHom_self, piSingleHom_self]
  · rw [pi_comp_apply, piSingleHom_ne h, piSingleHom_ne h, piSingleHom_ne h, zero_comp]

omit [DecidableEq J] in
theorem pi_sum_apply {A B : ∀ j, D j} {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) (j : J) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, pi_add_apply, ih]

theorem piSingleHom_sum {A B : ∀ j, D j} {ι : Type*} (s : Finset ι) (j : J)
    (f : ι → (A j ⟶ B j)) :
    ∑ i ∈ s, piSingleHom j (f i) = piSingleHom (A := A) (B := B) j (∑ i ∈ s, f i) := by
  funext j'
  rw [pi_sum_apply]
  by_cases h : j' = j
  · subst h
    simp only [piSingleHom_self]
  · simp only [piSingleHom_ne h, Finset.sum_const_zero]

theorem fullSubcategory_hom_sum {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {P : ObjectProperty 𝒞}
    {A B : P.FullSubcategory} {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

end Generic

/-! ### Sums of morphisms factoring through `F_s P_∅` -/

/-- An endomorphism of an object of `Ř^λ-pmod` is a *vacuum sum* if it is a finite sum of
composites through modules `F_s P_∅` obtained by applying upward words `s` out of the region of
`P_∅` to `P_∅`. -/
def IsVacSum {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a} (φ : M ⟶ N) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (g : ι → (vacRegion hQ RD Λ ⟶ a))
    (_ : ∀ i, ∃ t : List I, (LinearCat.revHom (g i)).obj = ob RD (vacWt RD Λ) (ups t))
    (q : ∀ i, M ⟶ ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
      (univVacuum hQ RD Λ hΛ))
    (p : ∀ i, ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
      (univVacuum hQ RD Λ hΛ) ⟶ N), ∑ i, q i ≫ p i = φ

variable {hQ RD Λ hΛ} in
theorem isVacSum_zero {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    (M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a) :
    IsVacSum hQ RD Λ hΛ (0 : M ⟶ N) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim,
    by simp⟩

variable {hQ RD Λ hΛ} in
theorem IsVacSum.add {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a} {φ ψ : M ⟶ N}
    (hφ : IsVacSum hQ RD Λ hΛ φ) (hψ : IsVacSum hQ RD Λ hΛ ψ) :
    IsVacSum hQ RD Λ hΛ (φ + ψ) := by
  obtain ⟨ι, _, g, hg, q, p, rfl⟩ := hφ
  obtain ⟨ι', _, g', hg', q', p', rfl⟩ := hψ
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim g g', fun i => match i with
    | .inl i => hg i | .inr i => hg' i, fun i => match i with
    | .inl i => q i | .inr i => q' i, fun i => match i with
    | .inl i => p i | .inr i => p' i, ?_⟩
  rw [Fintype.sum_sum_type]
  rfl

variable {hQ RD Λ hΛ} in
theorem isVacSum_sum {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) (h : ∀ i ∈ s, IsVacSum hQ RD Λ hΛ (φ i)) :
    IsVacSum hQ RD Λ hΛ (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isVacSum_zero M N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {hQ RD Λ hΛ} in
theorem univ_sum_apply {c : X}
    {A B : (univCyclotomicPresCLk hQ RD Λ hΛ).obj
      (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)}
    {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) (β : WeightBlocks RD Λ c) :
    (∑ i ∈ s, f i) β = ∑ i ∈ s, f i β := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

variable {hQ RD Λ hΛ} in
theorem pmod_piSingle_comp_apply {c : X}
    {A B B' : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj
      (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)}
    (β β' : WeightBlocks RD Λ c) (f : A.obj β ⟶ B.obj β) (g : B.obj β ⟶ B'.obj β) :
    ((ObjectProperty.homMk (piSingleHom β f) : A ⟶ B) ≫
      ObjectProperty.homMk (piSingleHom β g)).hom β' = piSingleHom β (f ≫ g) β' := by
  exact congrFun (piSingleHom_comp β f g) β'

/-- `exists_vacWord_gen` indexed by a block. -/
theorem exists_vacWord_gen' {c : X} (β : WeightBlocks RD Λ c) (t : KLR.Seq β.1)
    (hc : KL3.Diagram.wt RD (vacWt RD Λ) (ups (KLR.Diagram.word t)) = c) :
    ∃ (x : ((vacWordObj.{u, v, w} hQ RD Λ hΛ hc).obj β : Type _))
      (f : ((vacWordObj.{u, v, w} hQ RD Λ hΛ hc).obj β : Type _) →ₗ[CycKLR
        (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) β.1] CycKLR (UnivCycRing k lam)
        (cycQ k lam Q) (univCycPoly k lam) β.1),
      f x = CycKLR.mk _ _ _ β.1 (e t.rev) :=
  exists_vacWord_gen hQ RD Λ hΛ β.2 t hc

variable {hQ RD Λ hΛ} in
/-- The idempotent of `M ∈ Ř^λ-pmod` projecting onto one block `β` is a vacuum sum: it factors
through copies of the modules `F_t P_∅`, one for each element of a dual basis of the block of
`M` and each sequence `t` (Webster, arXiv:1309.3796v2, proof of Prop. 3.25). -/
theorem isVacSum_piSingle {c : X}
    (M : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj
      (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat))
    (β : WeightBlocks RD Λ c) :
    IsVacSum hQ RD Λ hΛ (ObjectProperty.homMk (piSingleHom β (𝟙 (M.obj β))) : M ⟶ M) := by
  have hc : ∀ t : KLR.Seq β.1,
      KL3.Diagram.wt RD (vacWt RD Λ) (ups (KLR.Diagram.word t)) = c := fun t =>
    (RouqFamily.cond_word (vacWt RD Λ) t).2.2.trans
      ((blockWeight_wtop (RD := RD) (Λ := Λ) (μ := vacWt RD Λ) (ν := β.1) rfl).symm.trans β.2)
  choose x f hf using fun t : KLR.Seq β.1 => exists_vacWord_gen' hQ RD Λ hΛ β t.rev (hc t.rev)
  obtain ⟨hfin, hproj⟩ := M.property.1 β
  obtain ⟨n, m, sd, hs⟩ := exists_fin_dualBasis
    (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) β.1) (M.obj β)
  let g' : KLR.Seq β.1 → (vacRegion hQ RD Λ ⟶
      (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)) := fun t =>
    vacHom hQ RD Λ _ (hc t.rev)
  let Nt : KLR.Seq β.1 → ModuleCat (CycKLR (UnivCycRing k lam) (cycQ k lam Q)
      (univCycPoly k lam) β.1) := fun t => (vacWordObj.{u, v, w} hQ RD Λ hΛ (hc t.rev)).obj β
  let Fq : ∀ i : Fin n × KLR.Seq β.1, M.obj β ⟶ Nt i.2 := fun i =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ (Nt i.2) (x i.2) ∘ₗ LinearMap.proj i.1 ∘ₗ sd)
  let Fp : ∀ i : Fin n × KLR.Seq β.1, Nt i.2 ⟶ M.obj β := fun i =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ (M.obj β) (m i.1) ∘ₗ f i.2)
  have hcomp : ∑ i, Fq i ≫ Fp i = 𝟙 (M.obj β) :=
    moduleCat_sum_comp_eq_id Nt x f (fun t => CycKLR.mk _ _ _ β.1 (e t))
      (by rw [← map_sum, KLRAlgebra.sum_e, map_one]) (fun t => (hf t).trans (by rw [Seq.rev_rev]))
      m sd hs
  refine ⟨Fin n × KLR.Seq β.1, inferInstance, fun i => g' i.2, fun _ => ⟨_, rfl⟩,
    fun i => ObjectProperty.homMk (piSingleHom β (Fq i)),
    fun i => ObjectProperty.homMk (piSingleHom β (Fp i)), ?_⟩
  apply ObjectProperty.hom_ext
  refine (fullSubcategory_hom_sum _ _).trans ?_
  funext β'
  refine (univ_sum_apply _ _ _).trans ?_
  refine (Finset.sum_congr rfl fun i _ => pmod_piSingle_comp_apply β β' (Fq i) (Fp i)).trans ?_
  refine (pi_sum_apply Finset.univ (fun i => piSingleHom β (Fq i ≫ Fp i)) β').symm.trans ?_
  refine (congrFun (piSingleHom_sum Finset.univ β fun i => Fq i ≫ Fp i) β').trans ?_
  exact congrFun (congrArg (piSingleHom β) hcomp) β'

/-- A finite sum of morphisms in `Ř^λ-pmod` (used to avoid instance search at explicit
regions). -/
def pmodSum {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) : M ⟶ N :=
  ∑ i ∈ s, φ i

variable {hQ RD Λ hΛ} in
theorem pmodSum_hom {a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {M N : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) : (pmodSum hQ RD Λ hΛ s φ).hom = ∑ i ∈ s, (φ i).hom :=
  fullSubcategory_hom_sum s φ

variable {hQ RD Λ hΛ} in
/-- The identity of `M ∈ Ř^λ-pmod` is a vacuum sum (Webster, arXiv:1309.3796v2, Prop. 3.25):
it is the sum of the block idempotents of the finitely many nonzero blocks of `M`. -/
theorem isVacSum_id {c : (psig RD).Region}
    (M : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj
      (⟨⟨c⟩⟩ : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)) :
    IsVacSum hQ RD Λ hΛ (𝟙 M) := by
  have h : (𝟙 M) = pmodSum hQ RD Λ hΛ M.property.2.toFinset
      fun β => ObjectProperty.homMk (piSingleHom β (𝟙 (M.obj β))) := by
    apply ObjectProperty.hom_ext
    refine Eq.trans ?_ (pmodSum_hom _ _).symm
    funext β'
    refine Eq.trans ?_ (univ_sum_apply _ _ _).symm
    by_cases hβ : β' ∈ M.property.2.toFinset
    · refine Eq.trans ?_ (Finset.sum_eq_single_of_mem β' hβ
        fun b _ hb => piSingleHom_ne (Ne.symm hb) _).symm
      exact (piSingleHom_self _ _).symm
    · have hz : IsZero (M.obj β') :=
        not_not.mp fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
      exact hz.eq_of_src _ _
  exact (congrArg (IsVacSum hQ RD Λ hΛ) h).mpr
    (isVacSum_sum _ _ fun β _ => isVacSum_piSingle M β)

/-- **Every finitely generated projective `Ř^λ`-module is a retract of a sum of modules
`F_s P_∅`, `s` upward** (Webster, arXiv:1309.3796v2, Prop. 3.25, the density statement used in
Cor. 3.27): for every region `a` and every `M ∈ Ř^λ-pmod` at `a` there are finitely many
1-morphisms `g i` out of the region of the vacuum module `P_∅`, each an upward word, and
morphisms `q i : M ⟶ g i (P_∅)`, `p i : g i (P_∅) ⟶ M` with `∑ i, q i ≫ p i = 𝟙 M`. -/
theorem exists_vacuum_up_retract (a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
    (M : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a) :
    ∃ (n : ℕ) (g : Fin n → (vacRegion hQ RD Λ ⟶ a))
      (_ : ∀ i, ∃ t : List I, (LinearCat.revHom (g i)).obj = ob RD (vacWt RD Λ) (ups t))
      (q : ∀ i, M ⟶ ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
        (univVacuum hQ RD Λ hΛ))
      (p : ∀ i, ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
        (univVacuum hQ RD Λ hΛ) ⟶ M), ∑ i, q i ≫ p i = 𝟙 M := by
  have hid : IsVacSum hQ RD Λ hΛ (𝟙 M) := by
    obtain ⟨⟨c⟩⟩ := a
    exact isVacSum_id M
  obtain ⟨ι, _, g, hg, q, p, hs⟩ := hid
  let eι := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => g (eι.symm i), fun i => hg (eι.symm i),
    fun i => q (eι.symm i), fun i => p (eι.symm i), ?_⟩
  rw [← hs]
  exact Equiv.sum_comp eι.symm (fun i => q i ≫ p i)

/-- **Every finitely generated projective `Ř^λ`-module is a retract of a sum of modules
`F_s P_∅`** (Webster, arXiv:1309.3796v2, Prop. 3.25, the density statement used in
Cor. 3.27): for every region `a` and every `M ∈ Ř^λ-pmod` at `a` there are finitely many
1-morphisms `g i` out of the region of the vacuum module `P_∅` and morphisms
`q i : M ⟶ g i (P_∅)`, `p i : g i (P_∅) ⟶ M` with `∑ i, q i ≫ p i = 𝟙 M`. -/
theorem exists_vacuum_retract (a : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)
    (M : (univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).obj a) :
    ∃ (n : ℕ) (g : Fin n → (vacRegion hQ RD Λ ⟶ a))
      (q : ∀ i, M ⟶ ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
        (univVacuum hQ RD Λ hΛ))
      (p : ∀ i, ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (g i)).obj.obj
        (univVacuum hQ RD Λ hΛ) ⟶ M), ∑ i, q i ≫ p i = 𝟙 M := by
  obtain ⟨n, g, -, q, p, h⟩ := exists_vacuum_up_retract hQ RD Λ hΛ a M
  exact ⟨n, g, q, p, h⟩

end
end Categorification.KLR.CyclotomicAction
