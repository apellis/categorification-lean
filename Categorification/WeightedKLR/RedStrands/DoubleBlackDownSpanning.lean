/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Lemma39
import Categorification.Diagrams.KL3.SymmetryOmega

/-!
# Downward black words with bubbles in the outer region

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28; Khovanov–Lauda III,
arXiv:0807.3250v1, §3, Lemma 3.9 and the symmetry of §3.3.2. The symmetry
reverses orientations and negates region weights. Its sign on equal-colour
crossings multiplies each generator of the spanning submodule by a scalar.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- All the elementary black moves are downward dots or downward crossings. -/
def DownBlackLayers (A : List (LayerData I)) : Prop :=
  ∀ x ∈ A, ∃ q : KLR.Diagram.Gen I, x.2.1 = dnShape q

private theorem downBlackLayers_omega {A : List (LayerData I)} (h : Upward A) :
    DownBlackLayers (Omega.wls A) := by
  rintro x hx
  obtain ⟨⟨u,g,v⟩,hg,rfl⟩ := List.mem_map.mp hx
  have h' := h (u,g,v) hg
  change ∃ q, Omega.shape g = dnShape q
  cases g with
  | dot l => obtain ⟨b,i⟩ := l; cases b <;> first | exact ⟨.dot i, rfl⟩ | contradiction
  | cross b i j => cases b <;> first | exact ⟨.cross i j, rfl⟩ | contradiction
  | cap | cup => contradiction

/-- The all-down part of the KL spanning family and the bubble polynomial
algebra to its right in KL word order. -/
def downwardBlackBubbleSpan (μ : X) (s t : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :=
  Submodule.span k {f | ∃ (A : List (LayerData I)) (γ : End ((pres RD k).obj (ob RD μ []))),
    DownBlackLayers A ∧ SChain s A t ∧ IsBub RD k μ γ ∧ f = dg RD k μ s t A ≫ bubAt RD k μ t γ}

variable [DecidableEq I]

private def reverseSigns (μ : X) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k]
    ((pres RD k).obj (ob RD (-μ) (s.map Letter.dual)) ⟶ (pres RD k).obj (ob RD (-μ) (t.map Letter.dual))) :=
  (TR RD k (Omega.trO μ s).symm (Omega.trO μ t).symm).comp ((omegaU RD k).mapLinearMap k)

private theorem reverseSigns_dg (μ : X) (s t : List (Letter I)) (A : List (LayerData I)) (hA : SChain s A t) :
    reverseSigns RD k μ s t (dg RD k μ s t A) =
      ((Sig.sgnS A : ℤ) : k) • dg RD k (-μ) (s.map Letter.dual) (t.map Letter.dual) (Omega.wls A) := by
  change TR RD k (Omega.trO μ s).symm (Omega.trO μ t).symm ((omegaU RD k).map _) = _
  rw [omegaU_dg μ A hA, map_smul, TR_TR]

private theorem reverseSigns_comp (μ : X) (s t u : List (Letter I))
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))
    (g : (pres RD k).obj (ob RD μ t) ⟶ (pres RD k).obj (ob RD μ u)) :
    reverseSigns RD k μ s u (f ≫ g) = reverseSigns RD k μ s t f ≫ reverseSigns RD k μ t u g := by
  change TR RD k (Omega.trO μ s).symm (Omega.trO μ u).symm ((omegaU RD k).map (f ≫ g)) = _
  rw [Functor.map_comp]
  exact (TR_comp (Omega.trO μ s).symm (Omega.trO μ t).symm (Omega.trO μ u).symm _ _).symm

private theorem reverseSigns_bubAt (μ : X) (s : List (Letter I)) (γ : End ((pres RD k).obj (ob RD μ []))) :
    reverseSigns RD k μ s s (bubAt RD k μ s γ) =
      bubAt RD k (-μ) (s.map Letter.dual) ((omegaU RD k).map γ) := by
  let f := (reverseSigns RD k μ s s).comp (bubAt RD k μ s)
  let g := (bubAt RD k (-μ) (s.map Letter.dual)).comp
    ((omegaU RD k).mapLinearMap k (X := (pres RD k).obj (ob RD μ [])) (Y := (pres RD k).obj (ob RD μ [])))
  have he : f = g := by
    apply hom_ext_dg RD k μ
    intro B hB
    have hw : SChain s (B.map (whL s [])) s := by simpa using hB.whisk s []
    change reverseSigns RD k μ s s (bubAt RD k μ s (dg RD k μ [] [] B)) =
      bubAt RD k (-μ) (s.map Letter.dual) ((omegaU RD k).map (dg RD k μ [] [] B))
    rw [bubAt_dg, reverseSigns_dg _ _ _ _ _ _ hw, omegaU_dg_nil μ B hB, map_smul, bubAt_dg, sgnS_map_whL]
    congr 1
    simp [Omega.wls, Omega.ld, whL, List.map_map, Function.comp_def]
  exact LinearMap.congr_fun he γ

private theorem omegaMap_surjective {a b : Obj (psig RD)} :
    Function.Surjective ((omegaU RD k).map (X := (pres RD k).obj a) (Y := (pres RD k).obj b)) := by
  let ω := omegaU RD k
  intro f
  refine ⟨TR RD k (Omega.obj_obj a).symm (Omega.obj_obj b).symm (ω.map f), ?_⟩
  change (omegaU RD k).map (TR RD k _ _ ((omegaU RD k).map f)) = f
  rw [TR_apply, Functor.map_comp, Functor.map_comp, omegaU_omegaU, TR_apply]
  rw [eqToHom_map, eqToHom_map]
  simp

private theorem reverseSigns_surjective (μ : X) (s t : List (Letter I)) :
    Function.Surjective (reverseSigns RD k μ s t) := by
  intro f
  obtain ⟨g,hg⟩ := omegaMap_surjective RD k (TR RD k (Omega.trO μ s) (Omega.trO μ t) f)
  exact ⟨g, by change TR RD k (Omega.trO μ s).symm (Omega.trO μ t).symm ((omegaU RD k).map g) = f; rw [hg, TR_TR]⟩

private theorem dual_positive_spanning (μ : X) (s t : List (Letter I)) (hs : Positive s) (ht : Positive t)
    (f : (pres RD k).obj (ob RD (-μ) (s.map Letter.dual)) ⟶ (pres RD k).obj (ob RD (-μ) (t.map Letter.dual))) :
    f ∈ downwardBlackBubbleSpan RD k (-μ) (s.map Letter.dual) (t.map Letter.dual) := by
  obtain ⟨g,rfl⟩ := reverseSigns_surjective RD k μ s t f
  have hg : g ∈ upSpan RD k μ s t :=
    (Submodule.span_le.mpr (by rintro _ ⟨ls,h,rfl⟩; exact upSpanDiag (k := k) μ s t ls hs ht h))
      (mem_span_dg RD k μ g)
  induction hg using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A,γ,hA,hch,_,rfl⟩ := hz
    rw [reverseSigns_comp, reverseSigns_dg _ _ _ _ _ _ hch, reverseSigns_bubAt, Linear.smul_comp]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨Omega.wls A,_,downBlackLayers_omega hA, Omega.sChain_wls hch,
      isBub_of_prop36 (RD := RD) (-μ) (prop36 (-μ)) _,rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- KL III, Lemma 3.9, on arbitrary downward black words by the orientation
symmetry of §3.3.2. The spanning terms have bubbles in the rightmost region. -/
theorem downwardBlackBubbleSpan_eq_top (μ : X) (s t : List I) :
    downwardBlackBubbleSpan RD k μ (dns s) (dns t) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨m,rfl⟩ : ∃ m : X, -m = μ := ⟨-μ, neg_neg _⟩
  have h := dual_positive_spanning RD k m (ups s) (ups t) (positive_ups s) (positive_ups t)
  rw [map_dual_ups, map_dual_ups] at h
  exact h f

end Categorification.Stendhal.DoubleDiagram
