/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.KLR.ConcatAssoc

/-!
# Changing the black colour palette

For Webster v2, §6.1, the braided algebra in a fixed black weight only
uses colours occurring in that weight. Injective reindexing of the black
palette fixes every red label and preserves the violated quotient.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {ℓ : ℕ} {ν : Multiset I}
  {k : Type*} [CommRing k]
  (Q : J → J → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → J →₀ ℕ)
  (f : I → J) (hf : Function.Injective f)

local notation "g" => Sum.map f (id : Fin ℓ → Fin ℓ)
local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight ℓ (ν.map f)
local notation "Q₀" => fun i j => Q (f i) (f j)

def pullBlackWeights (r : Fin ℓ) : I →₀ ℕ :=
  (Λ r).comapDomain f hf.injOn

local notation "Λ₀" => pullBlackWeights Λ f hf

omit [DecidableEq I] [DecidableEq J] in
private theorem palette_map_weight : Multiset.map g μ = μ' := by
  simp [stendhalWeight,Multiset.map_map,Function.comp_def]

omit [DecidableEq I] [DecidableEq J] in
theorem palette_card : (Multiset.card μ) = (Multiset.card μ') := by
  rw [← palette_map_weight f,Multiset.card_map]

private def castSeqEquiv {C : Type*} {α β : Multiset C} (h : α=β) :
    Seq α ≃ Seq β := h ▸ Equiv.refl _

private theorem castSeqEquiv_apply {C : Type*} {α β : Multiset C} (h : α=β) (s : Seq α) :
    castSeqEquiv h s = KLR.Seq.cast h s := by cases h; rfl

def paletteLoading : Seq μ ≃ Seq μ' :=
  (KLR.Seq.mapEquiv (Sum.map_injective.mpr ⟨hf,Function.injective_id⟩) μ).trans
    (castSeqEquiv (palette_map_weight f))

omit [DecidableEq I] [DecidableEq J] in
theorem paletteLoading_lbl (s : Seq μ) (p : Fin (Multiset.card μ)) :
    (paletteLoading f hf s).lbl (Fin.cast (palette_card f) p)=g (s.lbl p) := by
  simp only [paletteLoading,Equiv.trans_apply,castSeqEquiv_apply,KLR.Seq.mapEquiv_apply,
    KLR.Seq.cast_apply,KLR.Seq.map_lbl,Fin.cast_cast,Fin.cast_eq_self]

def paletteRelabel :
    SeqRelabel k (stendhalQ Q₀ Λ₀) (stendhalQ Q Λ) μ μ' where
  card_eq := palette_card f
  equiv := paletteLoading f hf
  equiv_smul j s := by
    apply Subtype.ext
    funext p
    obtain ⟨a,rfl⟩ := (finCongr (palette_card f)).surjective p
    change (paletteLoading f hf (sadj (Multiset.card μ) j • s)).lbl (Fin.cast (palette_card f) a) =
      (sadj (Multiset.card μ') j • paletteLoading f hf s).lbl (Fin.cast (palette_card f) a)
    rw [paletteLoading_lbl]
    change g (s.lbl ((sadj (Multiset.card μ) j).symm a)) =
      (paletteLoading f hf s).lbl ((sadj (Multiset.card μ') j).symm (Fin.cast (palette_card f) a))
    rw [← cast_sadj_symm,paletteLoading_lbl]
  lbl_eq_iff s a b := by
    rw [paletteLoading_lbl,paletteLoading_lbl]
    exact (Sum.map_injective.mpr ⟨hf,Function.injective_id⟩).eq_iff
  Q_eq s a b _ := by
    rw [paletteLoading_lbl,paletteLoading_lbl]
    cases s.lbl a <;> cases s.lbl b <;> simp [stendhalQ,pullBlackWeights]

omit [DecidableEq I] [DecidableEq J] in
private theorem paletteLoading_isRight (s : Seq μ) (a : Fin (Multiset.card μ)) :
    ((paletteLoading f hf s).lbl (Fin.cast (palette_card f) a)).isRight = (s.lbl a).isRight := by
  rw [paletteLoading_lbl]
  cases s.lbl a <;> rfl

omit [DecidableEq I] [DecidableEq J] in
private theorem paletteLoading_isViolated (s : Seq μ) :
    IsViolated (paletteLoading f hf s) ↔ IsViolated s := by
  have flags (a : Fin (Multiset.card μ)) :
      ((paletteLoading f hf s).lbl (Fin.cast (palette_card f) a)).isLeft = (s.lbl a).isLeft := by
    rw [paletteLoading_lbl]
    cases s.lbl a <;> rfl
  constructor
  · rintro ⟨h,hv⟩
    have hs : 0 < Multiset.card μ := (palette_card f).symm ▸ h
    refine ⟨hs,?_⟩
    have eq := flags ⟨0,hs⟩
    rw [show (Fin.cast (palette_card f) ⟨0,hs⟩ : Fin (Multiset.card μ'))=⟨0,h⟩ from Fin.ext rfl] at eq
    exact eq.symm.trans hv
  · rintro ⟨h,hv⟩
    refine ⟨palette_card f ▸ h,?_⟩
    exact (flags ⟨0,h⟩).trans hv

private theorem map_finRange_cast {m n : ℕ} (h : m=n) :
    (List.finRange m).map (Fin.cast h)=List.finRange n := by
  subst n
  simp

omit [DecidableEq I] [DecidableEq J] in
/-- Black palette changes leave the red word unchanged. -/
theorem paletteLoading_redWord (s : Seq μ) : redWord (paletteLoading f hf s)=redWord s := by
  unfold redWord
  rw [← map_finRange_cast (palette_card f),List.filterMap_map]
  apply List.filterMap_congr
  intro a _
  change ((paletteLoading f hf s).lbl (Fin.cast (palette_card f) a)).getRight?=(s.lbl a).getRight?
  rw [paletteLoading_lbl]
  cases s.lbl a <;> rfl

namespace BraidedStendhalAlgebra

local notation "B" => BraidedStendhalAlgebra k Q₀ Λ₀ ν
local notation "B'" => BraidedStendhalAlgebra k Q Λ (ν.map f)
local notation "F" => ofKLR k Q₀ Λ₀ ν
local notation "F'" => ofKLR k Q Λ (ν.map f)
local notation "R" => paletteRelabel Q Λ f hf

def paletteAlgEquiv : B ≃ₐ[k] B' :=
  relabelAlgEquiv R (paletteLoading_isRight f hf)

theorem paletteAlgEquiv_e (s : Seq μ) :
    paletteAlgEquiv Q Λ f hf (F (e s))=F' (e (paletteLoading f hf s)) := by
  calc
    _ = F' (KLRAlgebra.relabelHom R (e s)) :=
      relabelAlgEquiv_ofKLR R (paletteLoading_isRight f hf) _
    _ = _ := congrArg F' (KLRAlgebra.relabelHom_e R s)

theorem paletteAlgEquiv_mem_violIdeal_iff (x : B) :
    paletteAlgEquiv Q Λ f hf x ∈ violIdeal k Q Λ (ν.map f) ↔ x ∈ violIdeal k Q₀ Λ₀ ν := by
  let φ : B ≃ₐ[k] B' := paletteAlgEquiv Q Λ f hf
  constructor
  · intro h
    have sub : violIdeal k Q Λ (ν.map f) ≤ TwoSidedIdeal.comap φ.symm (violIdeal k Q₀ Λ₀ ν) := by
      rw [violIdeal,TwoSidedIdeal.span_le]
      rintro _ ⟨s,hs,rfl⟩
      obtain ⟨t,rfl⟩ := (paletteLoading f hf).surjective s
      rw [SetLike.mem_coe,TwoSidedIdeal.mem_comap]
      have e : φ.symm (F' (e (paletteLoading f hf t)))=F (e t) :=
        (φ.symm_apply_eq).2 ((paletteAlgEquiv_e Q Λ f hf t).symm)
      rw [e]
      exact TwoSidedIdeal.subset_span ⟨t,(paletteLoading_isViolated f hf t).mp hs,rfl⟩
    have e := sub h
    rwa [TwoSidedIdeal.mem_comap,φ.symm_apply_apply] at e
  · intro h
    have sub : violIdeal k Q₀ Λ₀ ν ≤ TwoSidedIdeal.comap φ (violIdeal k Q Λ (ν.map f)) := by
      rw [violIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨s,hs,rfl⟩
      rw [SetLike.mem_coe,TwoSidedIdeal.mem_comap]
      change paletteAlgEquiv Q Λ f hf (F (e s)) ∈ _
      rw [paletteAlgEquiv_e]
      exact TwoSidedIdeal.subset_span ⟨_,(paletteLoading_isViolated f hf s).mpr hs,rfl⟩
    exact (TwoSidedIdeal.mem_comap _).mp (sub h)

/-- Injective changes of the black palette preserve the globally violated algebra. -/
def violPaletteEquiv : ViolQuotient k Q₀ Λ₀ ν ≃ₐ[k] ViolQuotient k Q Λ (ν.map f) :=
  RingCon.congrₐ k (paletteAlgEquiv Q Λ f hf) (by
    ext x y
    rw [RingCon.comap_rel,TwoSidedIdeal.rel_iff,TwoSidedIdeal.rel_iff]
    change _ ↔ paletteAlgEquiv Q Λ f hf x-paletteAlgEquiv Q Λ f hf y ∈ _
    rw [← map_sub,paletteAlgEquiv_mem_violIdeal_iff])

theorem violPaletteEquiv_e (s : Seq μ) :
    violPaletteEquiv Q Λ f hf (violMk k Q₀ Λ₀ ν (F (e s))) =
      violMk k Q Λ (ν.map f) (F' (e (paletteLoading f hf s))) := by
  change violMk k Q Λ (ν.map f) (paletteAlgEquiv Q Λ f hf (F (e s)))=_
  rw [paletteAlgEquiv_e]

theorem paletteAlgEquiv_redProj (κ : List (Fin ℓ)) :
    paletteAlgEquiv Q Λ f hf (redProj k Q₀ Λ₀ ν κ)=redProj k Q Λ (ν.map f) κ := by
  rw [redProj,redIdem,map_sum,map_sum,redProj,redIdem,map_sum]
  refine Finset.sum_equiv (paletteLoading f hf) (fun s => ?_) (fun s _ => ?_)
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,paletteLoading_redWord]
  · exact paletteAlgEquiv_e Q Λ f hf s

theorem violPaletteEquiv_redProj (κ : List (Fin ℓ)) :
    violPaletteEquiv Q Λ f hf (violMk k Q₀ Λ₀ ν (redProj k Q₀ Λ₀ ν κ)) =
      violMk k Q Λ (ν.map f) (redProj k Q Λ (ν.map f) κ) := by
  change violMk k Q Λ (ν.map f) (paletteAlgEquiv Q Λ f hf (redProj k Q₀ Λ₀ ν κ))=_
  rw [paletteAlgEquiv_redProj]

end BraidedStendhalAlgebra
end Categorification.Stendhal
