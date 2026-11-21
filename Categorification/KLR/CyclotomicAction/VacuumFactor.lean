/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumFakeBubbles
import Categorification.Diagrams.CLQ.SpanningGeneral

/-!
# The ideal `I` at the vacuum as factorizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. Between two words at the region of `P_∅`, the ideal `I` consists of the
morphisms factoring through a word whose strand next to the vacuum is downward
(`mem_vacIdeal_of_mem_vacFactor`, `mem_vacFactor_of_mem_vacIdeal`). Placing an element of `I`
at `1_λ` to the right of any word stays in `I` (`bubAtC_mem_vacIdeal`).
-/

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram
universe u v w u₁
noncomputable section
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- Morphisms `E_s 1_λ ⟶ E_{s'} 1_λ` (`λ` the region of `P_∅`) factoring through a word whose
strand next to the vacuum is downward. -/
def vacFactor (s s' : List (Letter I)) :
    Submodule k ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :=
  Submodule.span k {φ | ∃ (t : List (Letter I)) (i : I)
    (_ : KL3.Diagram.wt RD (vacWt RD Λ) (t ++ [dn i]) = KL3.Diagram.wt RD (vacWt RD Λ) s)
    (α : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (t ++ [dn i])))
    (β : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (t ++ [dn i])) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')), α ≫ β = φ}

/-- Factorizations through a downward strand next to the vacuum lie in `I`. -/
theorem mem_vacIdeal_of_mem_vacFactor {s s' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    {φ} (hφ : φ ∈ vacFactor hQ RD Λ s s') :
    (show vacHom (k := k) hQ RD Λ s hs ⟶ vacHom hQ RD Λ s' hs' from φ) ∈
      vacIdeal hQ RD Λ _ _ := by
  set P := CL.presCL RD k (univScalars hQ RD)
  set μ := vacWt RD Λ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨t, i, hw, α, β, rfl⟩ := h
    have hc : KL3.Diagram.wt RD (KL3.Diagram.wt RD μ [dn i]) t = c := by
      rw [← wt_append]; exact hw.trans hs
    let e : vacRegion hQ RD Λ ⟶ (⟨⟨(KL3.Diagram.wt RD μ [dn i] : X)⟩⟩ : RevBicat P.Bicat) :=
      vacHom hQ RD Λ [dn i] rfl
    let w' : (⟨⟨(KL3.Diagram.wt RD μ [dn i] : X)⟩⟩ : RevBicat P.Bicat) ⟶
        (⟨⟨c⟩⟩ : RevBicat P.Bicat) :=
      (⟨ob RD (KL3.Diagram.wt RD μ [dn i]) t, hc, ob_wf RD _ t, ob_endR RD _ t⟩ :
        StringDiagrams.Presentation.Bicat.Hom _ _)
    have hE : (LinearCat.revHom (e ≫ w')).obj = ob RD μ (t ++ [dn i]) := by
      refine Obj.ext ?_ ?_
      · exact (wt_append RD μ t [dn i]).symm
      · exact (wd_append RD μ t [dn i]).symm
    refine Submodule.subset_span ⟨_, e, w', (α ≫ eqToHom (congrArg P.obj hE.symm) :),
      (eqToHom (congrArg P.obj hE) ≫ β :), ⟨i, μ, rfl⟩, ?_⟩
    change (α ≫ eqToHom (congrArg P.obj hE.symm)) ≫ (eqToHom (congrArg P.obj hE) ≫ β) = α ≫ β
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ r hx

/-- Conversely, every element of `I` between words factors through a downward strand next to
the vacuum. -/
theorem mem_vacFactor_of_mem_vacIdeal {s s' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    {φ : vacHom (k := k) hQ RD Λ s hs ⟶ vacHom hQ RD Λ s' hs'}
    (hφ : φ ∈ vacIdeal hQ RD Λ _ _) :
    (show (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s') from φ) ∈
        vacFactor hQ RD Λ s s' := by
  set P := CL.presCL RD k (univScalars hQ RD)
  set μ := vacWt RD Λ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨b, e, w', α, β, ⟨i, r, hw⟩, rfl⟩ := h
    set Z := (LinearCat.revHom (e ≫ w')).obj
    have hZw : Z.word.map Col.l = (LinearCat.revHom w').obj.word.map Col.l ++ [dn i] := by
      change ((LinearCat.revHom w').obj.word ++ (LinearCat.revHom e).obj.word).map Col.l = _
      rw [hw]; exact (List.map_append (f := Col.l)).trans rfl
    have hZ : Z = ob RD μ ((LinearCat.revHom w').obj.word.map Col.l ++ [dn i]) := by
      rw [← hZw]
      have h1 := wf_eq_ob Z (LinearCat.revHom (e ≫ w')).wf
      have h2 : Z.endR = μ := (LinearCat.revHom (e ≫ w')).endR_eq
      rw [StringDiagrams.Obj.endR] at h2
      exact h1.trans (congrArg (fun m => ob RD m (Z.word.map Col.l)) h2)
    let α' : P.obj (ob RD μ s) ⟶ P.obj Z := α
    let β' : P.obj Z ⟶ P.obj (ob RD μ s') := β
    refine Submodule.subset_span ⟨_, i, ?_, α' ≫ eqToHom (congrArg P.obj hZ),
      eqToHom (congrArg P.obj hZ.symm) ≫ β', ?_⟩
    · have h3 : Z.start = c := (LinearCat.revHom (e ≫ w')).start_eq
      rw [hZ] at h3
      exact h3.trans hs.symm
    · rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rfl
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ r hx

/-- Placing a factorization through a downward strand next to the vacuum to the right of the
strands `s` gives a factorization through a downward strand next to the vacuum. -/
theorem bubAtC_mem_vacFactor (s : List (Letter I)) {f}
    (hf : f ∈ vacFactor hQ RD Λ [] []) :
    CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) s f ∈
      vacFactor hQ RD Λ s s := by
  set P := CL.presCL RD k (univScalars hQ RD)
  set μ := vacWt RD Λ
  induction hf using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨t, i, hw, α, β, rfl⟩ := h
    have hw' : KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) (t ++ [dn i]) =
        KL3.Diagram.wt RD (KL3.Diagram.wt RD μ []) [] := hw
    change CL.dgC P μ s _ [] ≫ CL.plcLC P μ s [] [] [] (α ≫ β) ≫ CL.dgC P μ _ s [] ∈ _
    erw [← CL.plcLC_comp P μ s [] hw' hw'.symm α β]
    have hE : P.obj (ob RD μ (s ++ (t ++ [dn i]) ++ [])) = P.obj (ob RD μ (s ++ t ++ [dn i])) := by
      simp only [List.append_nil, List.append_assoc]
    refine Submodule.subset_span ⟨s ++ t, i, ?_,
      CL.dgC P μ s _ [] ≫ CL.plcLC P μ s [] [] _ α ≫ eqToHom hE,
      eqToHom hE.symm ≫ CL.plcLC P μ s [] _ [] β ≫ CL.dgC P μ _ s [], ?_⟩
    · rw [List.append_assoc, wt_append, hw]; rfl
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **Placing an element of `I` to the right of a word**: for `x ∈ I` at `1_λ`, the endomorphism
`x` placed to the right of the strands `s` lies in `I`. -/
theorem bubAtC_mem_vacIdeal (s : List (Letter I))
    {x : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) []))}
    (hx : x ∈ vacIdealEnd hQ RD Λ) :
    (show vacHom (k := k) hQ RD Λ s rfl ⟶ vacHom hQ RD Λ s rfl from
      CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) s x) ∈
        vacIdeal hQ RD Λ _ _ :=
  mem_vacIdeal_of_mem_vacFactor hQ RD Λ rfl rfl
    (bubAtC_mem_vacFactor hQ RD Λ s (mem_vacFactor_of_mem_vacIdeal hQ RD Λ rfl rfl hx))

end
end Categorification.KLR.CyclotomicAction
