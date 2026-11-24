/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedPaletteRelabel
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.Algebra.BalancedTensorTransport

/-!
# Palette transport of the higher-loading inclusion

The root comparison for the retained block boundaries in Webster v2,
§6.1, Lemma 6.8, is unchanged under injective black colour relabelling.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {ℓ : ℕ} {ν : Multiset I}
  (f : I → J) (hf : Function.Injective f)

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight ℓ (ν.map f)
local notation "σ" => paletteLoading f hf
local notation "c" => palette_card (ℓ := ℓ) (ν := ν) f

private theorem count_palette (s : Seq μ) (C : Finset (Fin ℓ)) (i : I) :
    blockBlackCount (σ s) C (f i)=blockBlackCount s C i := by
  unfold blockBlackCount
  symm
  apply Finset.card_bijective (Fin.cast c) (finCongr c).bijective
  intro x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [paletteLoading_lbl]
  have black : Sum.map f (id : Fin ℓ → Fin ℓ) (s.lbl x)=Sum.inl (f i) ↔ s.lbl x=Sum.inl i := by
    cases s.lbl x <;> simp [hf.eq_iff]
  rw [black]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro h y r hr hy
    obtain ⟨a,rfl⟩ := (finCongr c).surjective y
    change (σ s).lbl (Fin.cast c a)=Sum.inr r at hy
    rw [paletteLoading_lbl] at hy
    have hy' : s.lbl a=Sum.inr r := by
      cases hx : s.lbl a with
      | inl i => simp [hx] at hy
      | inr r₀ => simpa [hx] using hy
    exact h a r hr hy'
  · intro h y r hr hy
    have hy' : (σ s).lbl (Fin.cast c y)=Sum.inr r := by
      rw [paletteLoading_lbl,hy]
      rfl
    exact h (Fin.cast c y) r hr hy'

omit [DecidableEq I] in
private theorem count_palette_outside (s : Seq μ) (C : Finset (Fin ℓ))
    (j : J) (hj : j ∉ Set.range f) : blockBlackCount (σ s) C j=0 := by
  unfold blockBlackCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨a,rfl⟩ := (finCongr c).surjective p
  have h := (Finset.mem_filter.mp hp).2.1
  change (σ s).lbl (Fin.cast c a)=Sum.inl j at h
  rw [paletteLoading_lbl] at h
  cases hx : s.lbl a with
  | inr r => simp [hx] at h
  | inl i => exact hj ⟨i,by simpa [hx] using h⟩

/-- Relabelling transports strict comparisons of the two retained roots,
including target colours outside the image of the source palette. -/
theorem paletteLoading_adjacentBlockRoot_lt_iff (a b : Fin ℓ) (s t : Seq μ) :
    adjacentBlockRoot a b (σ s) < adjacentBlockRoot a b (σ t) ↔
      adjacentBlockRoot a b s < adjacentBlockRoot a b t := by
  have le (s t : Seq μ) :
      adjacentBlockRoot a b (σ s) ≤ adjacentBlockRoot a b (σ t) ↔
        adjacentBlockRoot a b s ≤ adjacentBlockRoot a b t := by
    constructor
    · intro h r i
      simpa only [adjacentBlockRoot,count_palette f hf] using h r (f i)
    · intro h r j
      by_cases hj : j ∈ Set.range f
      · obtain ⟨i,rfl⟩ := hj
        simpa only [adjacentBlockRoot,count_palette f hf] using h r i
      · simp only [adjacentBlockRoot,count_palette_outside f hf _ _ j hj,le_refl]
  rw [lt_iff_le_not_ge,lt_iff_le_not_ge,le,le]

namespace BraidedStendhalAlgebra

variable {k : Type*} [CommRing k]
  (Q : J → J → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → J →₀ ℕ)

local notation "Q₀" => fun i j => Q (f i) (f j)
local notation "Λ₀" => pullBlackWeights Λ f hf
local notation "V" => ViolQuotient k Q₀ Λ₀ ν
local notation "V'" => ViolQuotient k Q Λ (ν.map f)
local notation "φ" => violPaletteEquiv Q Λ f hf
local notation "p" => fun s : Seq μ =>
  violMk k Q₀ Λ₀ ν (ofKLR k Q₀ Λ₀ ν (e s))
local notation "p'" => fun s : Seq μ' =>
  violMk k Q Λ (ν.map f) (ofKLR k Q Λ (ν.map f) (e s))

theorem violPaletteEquiv_mem_blockUpperIdeal_iff (t : Seq μ) (a b : Fin ℓ)
    (κ : List (Fin ℓ)) (x : V) :
    φ x ∈ blockUpperIdeal k Q Λ (ν.map f) a b (adjacentBlockRoot a b (σ t)) κ ↔
      x ∈ blockUpperIdeal k Q₀ Λ₀ ν a b (adjacentBlockRoot a b t) κ := by
  let D := blockUpperIdeal k Q₀ Λ₀ ν a b (adjacentBlockRoot a b t) κ
  let D' := blockUpperIdeal k Q Λ (ν.map f) a b (adjacentBlockRoot a b (σ t)) κ
  have forward : D ≤ TwoSidedIdeal.comap φ D' := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨s,hs,lt,rfl⟩
    rw [SetLike.mem_coe,TwoSidedIdeal.mem_comap]
    change φ (p s) ∈ D'
    rw [violPaletteEquiv_e]
    exact TwoSidedIdeal.subset_span ⟨σ s,(paletteLoading_redWord f hf s).trans hs,
      (paletteLoading_adjacentBlockRoot_lt_iff f hf a b t s).mpr lt,rfl⟩
  have backward : D' ≤ TwoSidedIdeal.comap (φ).symm D := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨u,hu,lt,rfl⟩
    obtain ⟨s,rfl⟩ := (σ).surjective u
    rw [SetLike.mem_coe,TwoSidedIdeal.mem_comap]
    have e : (φ).symm (p' (σ s))=p s :=
      ((φ).symm_apply_eq).2 ((violPaletteEquiv_e Q Λ f hf s).symm)
    change (φ).symm (p' (σ s)) ∈ D
    rw [e]
    exact TwoSidedIdeal.subset_span ⟨s,(paletteLoading_redWord f hf s).symm.trans hu,
      (paletteLoading_adjacentBlockRoot_lt_iff f hf a b t s).mp lt,rfl⟩
  constructor
  · intro hx
    have h := backward hx
    rwa [TwoSidedIdeal.mem_comap,AlgEquiv.symm_apply_apply] at h
  · intro hx
    exact (TwoSidedIdeal.mem_comap _).mp (forward hx)

section Tensor

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))
local notation "ord" => isIdempotentElem_violMk_redProj k Q₀ Λ₀ ν (redWord t)
local notation "ord'" => isIdempotentElem_violMk_redProj k Q Λ (ν.map f) (redWord (σ t))
local notation "T" => IsIdempotentElem.Corner ord
local notation "T'" => IsIdempotentElem.Corner ord'
local notation "e₀" => violMk k Q₀ Λ₀ ν (redProj k Q₀ Λ₀ ν (redWord t))
local notation "e₀'" => violMk k Q Λ (ν.map f) (redProj k Q Λ (ν.map f) (redWord (σ t)))
local notation "e₁" => violMk k Q₀ Λ₀ ν (redProj k Q₀ Λ₀ ν κ)
local notation "e₁'" => violMk k Q Λ (ν.map f) (redProj k Q Λ (ν.map f) κ)
local notation "Pr" => rIdeal (orderedLoadingIdem Q₀ Λ₀ t)
local notation "Pr'" => rIdeal (orderedLoadingIdem Q Λ (σ t))
local notation "K" => blockLoadingKernel Q₀ Λ₀ t a b
local notation "K'" => blockLoadingKernel Q Λ (σ t) a b
local notation "B" => RedBlock.crossingSpace (k := k) e₀ e₁
local notation "B'" => RedBlock.crossingSpace (k := k) e₀' e₁'
local notation "D" => blockUpperIdeal k Q₀ Λ₀ ν a b (adjacentBlockRoot a b t) (redWord t)
local notation "D'" => blockUpperIdeal k Q Λ (ν.map f) a b (adjacentBlockRoot a b (σ t)) (redWord (σ t))

private theorem top_projector : φ e₀=e₀' := by
  rw [violPaletteEquiv_redProj,paletteLoading_redWord]

private def orderPaletteEquiv : T ≃+* T' :=
  IsIdempotentElem.cornerRingEquiv ord ord' (φ).toRingEquiv (top_projector f hf Q Λ t)

local notation "ψ" => orderPaletteEquiv f hf Q Λ t

private theorem orderPaletteEquiv_idem :
    ψ (orderedLoadingIdem Q₀ Λ₀ t)=orderedLoadingIdem Q Λ (σ t) :=
  Subtype.ext (violPaletteEquiv_e Q Λ f hf t)

private def projPaletteEquiv : Pr ≃ₗ[k] Pr' where
  toFun x := ⟨ψ x.1, by
    have h := congrArg ψ x.2
    rwa [map_mul,orderPaletteEquiv_idem] at h⟩
  invFun y := ⟨(ψ).symm y.1, by
    apply (ψ).injective
    rw [map_mul,orderPaletteEquiv_idem,RingEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((ψ).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((ψ).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add ψ x.1 y.1)
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    change φ (r • x.1.1)=r • φ x.1.1
    exact map_smul φ r x.1.1

local notation "PE" => projPaletteEquiv f hf Q Λ t

private theorem projPaletteEquiv_smul (r : T) (x : Pr) :
    PE (MulOpposite.op r • x)=MulOpposite.op (ψ r) • PE x :=
  Subtype.ext (map_mul ψ x.1 r)

private theorem palette_mark (x : V) : φ x ∈ D' ↔ x ∈ D := by
  rw [paletteLoading_redWord]
  exact violPaletteEquiv_mem_blockUpperIdeal_iff f hf Q Λ t a b _ x

private def kernelPaletteEquiv : K ≃ₗ[k] K' where
  toFun x := ⟨PE x.1,(palette_mark f hf Q Λ t a b x.1.1.1).mpr x.2⟩
  invFun y := ⟨(PE).symm y.1,by
    have h := (palette_mark f hf Q Λ t a b ((PE).symm y.1).1.1)
    apply h.mp
    have eq := congrArg (fun z : Pr' => z.1.1) ((PE).apply_symm_apply y.1)
    change φ ((PE).symm y.1).1.1=y.1.1.1 at eq
    rw [eq]
    exact y.2⟩
  left_inv x := Subtype.ext ((PE).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((PE).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add PE x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul PE r x.1)

local notation "KE" => kernelPaletteEquiv f hf Q Λ t a b

private theorem kernelPaletteEquiv_smul (r : T) (x : K) :
    KE (MulOpposite.op r • x)=MulOpposite.op (ψ r) • KE x :=
  Subtype.ext (projPaletteEquiv_smul f hf Q Λ t r x.1)

private def crossingCutPaletteEquiv (l : V) (l' : V') (h : φ l=l') :
    RedBlock.crossingSpace (k := k) e₀ l ≃ₗ[k] RedBlock.crossingSpace (k := k) e₀' l' where
  toFun x := ⟨φ x.1,by
    rw [← top_projector f hf Q Λ t,← map_mul,x.2.1],by
    rw [← h,← map_mul,x.2.2]⟩
  invFun y := ⟨(φ).symm y.1,by
    apply (φ).injective
    rw [map_mul,top_projector,(φ).apply_symm_apply,y.2.1],by
    apply (φ).injective
    rw [map_mul,h,(φ).apply_symm_apply,y.2.2]⟩
  left_inv x := Subtype.ext ((φ).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((φ).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add φ x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul φ r x.1)

private theorem crossingCutPaletteEquiv_smul (l : V) (l' : V') (h : φ l=l')
    (r : T) (x : RedBlock.crossingSpace (k := k) e₀ l) :
    crossingCutPaletteEquiv f hf Q Λ t l l' h (r • x)=
      ψ r • crossingCutPaletteEquiv f hf Q Λ t l l' h x :=
  Subtype.ext (map_mul φ r.1 x.1)

local notation "BE" => crossingCutPaletteEquiv f hf Q Λ t e₁ e₁'
  (violPaletteEquiv_redProj Q Λ f hf κ)
local notation "BE_smul" => crossingCutPaletteEquiv_smul f hf Q Λ t e₁ e₁'
  (violPaletteEquiv_redProj Q Λ f hf κ)

private def kernelTensorPaletteEquiv :
    BalancedTensor k k T K B ≃ₗ[k] BalancedTensor k k T' K' B' :=
  BalancedTensor.changeRingEquiv ψ KE BE (kernelPaletteEquiv_smul f hf Q Λ t a b)
    BE_smul

private def projTensorPaletteEquiv :
    BalancedTensor k k T Pr B ≃ₗ[k] BalancedTensor k k T' Pr' B' :=
  BalancedTensor.changeRingEquiv ψ PE BE (projPaletteEquiv_smul f hf Q Λ t)
    BE_smul

local notation "inc" => blockKernelTensorInclusion Q₀ Λ₀ t a b κ
local notation "inc'" => blockKernelTensorInclusion Q Λ (σ t) a b κ
local notation "KT" => kernelTensorPaletteEquiv f hf Q Λ t a b κ
local notation "PT" => projTensorPaletteEquiv f hf Q Λ t κ

private theorem palette_inclusion_square : (inc').comp (KT).toLinearMap =
    (PT).toLinearMap.comp inc := by
  apply BalancedTensor.ext
  intro x y
  rfl

private theorem injective_iff_square {X X' Y Y' : Type*}
    (f : X ≃ X') (g : Y ≃ Y') (i : X → Y) (j : X' → Y')
    (square : ∀ x, j (f x)=g (i x)) : Function.Injective j ↔ Function.Injective i := by
  constructor
  · intro h x y eq
    apply f.injective
    exact h ((square x).trans ((congrArg g eq).trans (square y).symm))
  · intro h x y eq
    obtain ⟨x,rfl⟩ := f.surjective x
    obtain ⟨y,rfl⟩ := f.surjective y
    exact congrArg f (h (g.injective ((square x).symm.trans (eq.trans (square y)))))

/-- The higher-loading balanced tensor inclusion in Webster's (6.21)
preserves injectivity under relabelling the supported black palette. -/
theorem blockKernelTensorInclusion_injective_palette_iff :
    Function.Injective (inc').toFun ↔ Function.Injective (inc).toFun :=
  injective_iff_square (KT).toEquiv (PT).toEquiv (inc).toFun (inc').toFun
    (fun z => LinearMap.congr_fun (palette_inclusion_square f hf Q Λ t a b κ) z)

end Tensor

end BraidedStendhalAlgebra
end Categorification.Stendhal
