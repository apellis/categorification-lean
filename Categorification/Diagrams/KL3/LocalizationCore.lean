/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationGeneration
import Categorification.Diagrams.KL3.LocalizationDotsDown
import Categorification.Diagrams.KL3.CanonFiltered

/-!
# 2-morphisms of `U′` that become images of `U` after multiplication by dots

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. A 2-morphism `f : 1_μ ⟶ E_s 1_μ` of the localization `U′` is a *core* morphism if
`f` followed by some dots on the strands `s` is the image of a 2-morphism of `U`. The core
morphisms form a submodule (`coreSet`), which contains the image of `U` and is closed under
postcomposition with inverse dots, dots, cups and crossings (the cap is treated separately).

## Main results

* `coreSet`: the core morphisms `1_μ ⟶ E_s 1_μ` of `U′`.
* `coreSet_comp_of_comm`: postcomposition with the image of a 2-morphism of `U` that commutes
  with dots up to extra dots preserves core morphisms.
* `coreSet_comp_invDot`, `coreSet_comp_dot`, `coreSet_comp_cup`, `coreSet_comp_cross`,
  `coreSet_comp_bubAt`: closure under inverse dots, dots, cups, crossings and bubbles.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-! ## Dots on all strands -/

/-- The dots at the positions `is` on the strands `s`, as an endomorphism of `E_s 1_μ` in `U`. -/
abbrev dD (μ : X) (s : List (Letter I)) (is : List ℕ) :
    (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ s) :=
  dg RD k μ s s (dotsL s is)

variable {RD k}

theorem dD_append (μ : X) {s : List (Letter I)} {is js : List ℕ} (hi : ∀ i ∈ is, i < s.length)
    (hj : ∀ j ∈ js, j < s.length) :
    dD RD k μ s (is ++ js) = dD RD k μ s is ≫ dD RD k μ s js := by
  show dg RD k μ s s (dotsL s (is ++ js)) = _
  rw [dotsL_append]
  exact (dg_comp (sChain_dotsL hi) (sChain_dotsL hj)).symm

theorem dD_perm (μ : X) {s : List (Letter I)} {is js : List ℕ} (h : is.Perm js)
    (hi : ∀ i ∈ is, i < s.length) : dD RD k μ s is = dD RD k μ s js := by
  have := dotsL_perm (RD := RD) (k := k) (t := s) h hi [] [] μ s s
  simpa using this

theorem dD_comm (μ : X) {s : List (Letter I)} {is js : List ℕ} (hi : ∀ i ∈ is, i < s.length)
    (hj : ∀ j ∈ js, j < s.length) :
    dD RD k μ s is ≫ dD RD k μ s js = dD RD k μ s js ≫ dD RD k μ s is := by
  rw [← dD_append μ hi hj, ← dD_append μ hj hi]
  exact dD_perm μ List.perm_append_comm (by
    intro i h; rcases List.mem_append.1 h with h | h
    · exact hi i h
    · exact hj i h)

/-! ## Core morphisms -/

variable (RD k) in
/-- **Core morphisms** of `U′` (Webster arXiv:1309.3796v2, proof of Lemma 3.29): the 2-morphisms
`f : 1_μ ⟶ E_s 1_μ` of `U′` such that `f` followed by some dots on the strands `s` is the image of
a 2-morphism of `U`. -/
def coreSet (μ : X) (s : List (Letter I)) :
    Submodule k ((presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s))) where
  carrier := {f | ∃ is : List ℕ, (∀ i ∈ is, i < s.length) ∧
    ∃ g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ s),
      f ≫ (toLoc RD k).map (dD RD k μ s is) = (toLoc RD k).map g}
  zero_mem' := ⟨[], by simp, 0, by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨is₁, h₁, g₁, e₁⟩ ⟨is₂, h₂, g₂, e₂⟩
    have hb : ∀ i ∈ is₁ ++ is₂, i < s.length := by
      intro i h; rcases List.mem_append.1 h with h | h
      · exact h₁ i h
      · exact h₂ i h
    refine ⟨is₁ ++ is₂, hb, g₁ ≫ dD RD k μ s is₂ + g₂ ≫ dD RD k μ s is₁, ?_⟩
    have E₁ := dD_append (RD := RD) (k := k) μ h₁ h₂
    have E₂ : dD RD k μ s (is₁ ++ is₂) = dD RD k μ s is₂ ≫ dD RD k μ s is₁ :=
      (dD_perm μ List.perm_append_comm hb).trans (dD_append μ h₂ h₁)
    calc (f₁ + f₂) ≫ (toLoc RD k).map (dD RD k μ s (is₁ ++ is₂))
        = (f₁ ≫ (toLoc RD k).map (dD RD k μ s is₁)) ≫ (toLoc RD k).map (dD RD k μ s is₂) +
          (f₂ ≫ (toLoc RD k).map (dD RD k μ s is₂)) ≫ (toLoc RD k).map (dD RD k μ s is₁) := by
          rw [Preadditive.add_comp]
          conv_lhs => rw [E₁]
          conv_lhs => arg 2; rw [← E₁, E₂]
          simp only [Functor.map_comp, Category.assoc]
      _ = _ := by rw [e₁, e₂, Functor.map_add, Functor.map_comp, Functor.map_comp]
  smul_mem' := by
    rintro c f ⟨is, h, g, e⟩
    exact ⟨is, h, c • g, by rw [Linear.smul_comp, e, Functor.map_smul]⟩

theorem toLoc_mem_coreSet (μ : X) (s : List (Letter I))
    (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ s)) :
    (toLoc RD k).map g ∈ coreSet RD k μ s :=
  ⟨[], by simp, g, by
    rw [show dD RD k μ s [] = 𝟙 _ from dg_nil μ s]
    exact ((toLoc RD k).map_comp g (𝟙 _)).symm.trans (congrArg _ (Category.comp_id g))⟩

theorem id_mem_coreSet (μ : X) : 𝟙 _ ∈ coreSet RD k μ [] := by
  have := toLoc_mem_coreSet (RD := RD) (k := k) μ [] (𝟙 _)
  rwa [CategoryTheory.Functor.map_id] at this

/-- **Postcomposition with a 2-morphism of `U` commuting with dots** (up to extra dots) preserves
core morphisms. -/
theorem coreSet_comp_of_comm (μ : X) {s t : List (Letter I)}
    (x : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t))
    (hx : ∀ is : List ℕ, (∀ i ∈ is, i < s.length) → ∃ (r js : List ℕ)
      (z : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)),
      (∀ i ∈ r, i < s.length) ∧ (∀ j ∈ js, j < t.length) ∧
        x ≫ dD RD k μ t js = dD RD k μ s (is ++ r) ≫ z)
    {f} (hf : f ∈ coreSet RD k μ s) : f ≫ (toLoc RD k).map x ∈ coreSet RD k μ t := by
  obtain ⟨is, his, g, e⟩ := hf
  obtain ⟨r, js, z, hr, hjs, ex⟩ := hx is his
  refine ⟨js, hjs, g ≫ dD RD k μ s r ≫ z, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, ex, dD_append μ his hr, Functor.map_comp,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, e, Functor.map_comp, Functor.map_comp,
    Category.assoc]

/-- Core morphisms are closed under postcomposition with the inverse dots. -/
theorem coreSet_comp_invDot (μ : X) (u : List (Letter I)) (i : I) (w : List (Letter I)) {f}
    (hf : f ∈ coreSet RD k μ (u ++ [dn i] ++ w)) :
    f ≫ (presLoc RD k).diag (invDot RD μ u i w) ∈ coreSet RD k μ (u ++ [dn i] ++ w) := by
  obtain ⟨is, his, g, e⟩ := hf
  have hu : u.length < (u ++ [dn i] ++ w).length := by simp
  have hb : ∀ j ∈ u.length :: is, j < (u ++ [dn i] ++ w).length := by
    intro j hj; rcases List.mem_cons.1 hj with rfl | hj
    · exact hu
    · exact his j hj
  refine ⟨u.length :: is, hb, g, ?_⟩
  have hd : dD RD k μ (u ++ [dn i] ++ w) [u.length] =
      dg RD k μ (u ++ [dn i] ++ w) (u ++ [dn i] ++ w) [(u, .dot (dn i), w)] := by
    show dg _ _ _ _ _ (dotAt _ u.length ++ []) = _
    rw [List.append_nil, dotAt_eq' (show u ++ [dn i] ++ w = u ++ dn i :: w by simp) rfl]
  rw [show u.length :: is = [u.length] ++ is from rfl,
    dD_append μ (by simp) his, hd, Functor.map_comp, Category.assoc,
    ← Category.assoc ((presLoc RD k).diag _), diag_invDot_eq_inv, IsIso.inv_hom_id,
    Category.id_comp, e]

/-- Core morphisms are closed under postcomposition with the bubbles on the far right. -/
theorem coreSet_comp_bubAt (μ : X) (s : List (Letter I)) (β : End ((pres RD k).obj (ob RD μ [])))
    {f} (hf : f ∈ coreSet RD k μ s) :
    f ≫ (toLoc RD k).map (bubAt RD k μ s β) ∈ coreSet RD k μ s :=
  coreSet_comp_of_comm μ _ (fun is his => ⟨[], is, bubAt RD k μ s β, by simp, his, by
    rw [List.append_nil, bubAt_comm_dg RD k μ β _ (sChain_dotsL his)]⟩) hf

/-- Core morphisms are closed under postcomposition with a dot. -/
theorem coreSet_comp_dot (μ : X) (u : List (Letter I)) (l : Letter I) (w : List (Letter I)) {f}
    (hf : f ∈ coreSet RD k μ (u ++ [l] ++ w)) :
    f ≫ (toLoc RD k).map (dg RD k μ (u ++ [l] ++ w) (u ++ [l] ++ w) [(u, .dot l, w)]) ∈
      coreSet RD k μ (u ++ [l] ++ w) := by
  have hu : u.length < (u ++ [l] ++ w).length := by simp
  have hd : dg RD k μ (u ++ [l] ++ w) (u ++ [l] ++ w) [(u, .dot l, w)] =
      dD RD k μ (u ++ [l] ++ w) [u.length] := by
    show _ = dg _ _ _ _ _ (dotAt _ u.length ++ [])
    rw [List.append_nil, dotAt_eq' (show u ++ [l] ++ w = u ++ l :: w by simp) rfl]
  rw [hd]
  refine coreSet_comp_of_comm μ _ (fun is his => ⟨[], is, dD RD k μ _ [u.length], by simp, his,
    ?_⟩) hf
  rw [List.append_nil]
  exact dD_comm μ (by simp) his

/-! ## Cups -/

theorem lo_zero (ν : X) (s t : List (Letter I)) : Lo RD k ν s t 0 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨L, hL, -⟩
  omega

section Cups

variable [DecidableEq I]

/-- Dots pass a cup exactly. -/
theorem dD_comp_cup (μ : X) (u v : List (Letter I)) (l : Letter I) {is : List ℕ}
    (his : ∀ i ∈ is, i < (u ++ [] ++ v).length) :
    dD RD k μ (u ++ [] ++ v) is ≫
        dg RD k μ (u ++ [] ++ v) (u ++ [l, l.dual] ++ v) [(u, .cup l, v)] =
      dg RD k μ (u ++ [] ++ v) (u ++ [l, l.dual] ++ v) [(u, .cup l, v)] ≫
        dD RD k μ (u ++ [l, l.dual] ++ v) (is.map (mvPos (.cup u.length l))) := by
  have hs : u ++ [] ++ v = u ++ v := by simp
  have ht : u ++ l :: l.dual :: v = u ++ [l, l.dual] ++ v := by simp
  have his' : ∀ i ∈ is, i < (u ++ v).length := by rw [← hs]; exact his
  have hjs : ∀ j ∈ is.map (mvPos (.cup u.length l)), j < (u ++ [l, l.dual] ++ v).length := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    have := his' i hi
    simp only [mvPos]
    split_ifs <;> simp at this ⊢ <;> omega
  have hm : (Chord.Move.cup u.length l : Chord.Move (Letter I)).Ok (u ++ v).length := by
    show u.length ≤ (u ++ v).length
    simp
  have h := dots_move (RD := RD) (k := k) hm his' [] [] μ (u ++ [] ++ v) (u ++ [l, l.dual] ++ v)
  rw [mvL_cup, lst_cup, ht, show ncr [(Chord.Move.cup u.length l : Chord.Move (Letter I))] = 0 from rfl,
    ccnt_nil, add_zero, lo_zero, Submodule.mem_bot, sub_eq_zero] at h
  have hc : SChain (u ++ [] ++ v) [(u, .cup l, v)] (u ++ [l, l.dual] ++ v) := ⟨rfl, rfl⟩
  rw [dg_comp (sChain_dotsL his) hc, dg_comp hc (sChain_dotsL hjs),
    show dotsL (u ++ [] ++ v) is = dotsL (u ++ v) is by rw [hs]]
  simp only [List.nil_append, List.append_nil (α := LayerData I)] at h
  exact h

/-- Core morphisms are closed under postcomposition with a cup. -/
theorem coreSet_comp_cup (μ : X) (u v : List (Letter I)) (l : Letter I) {f}
    (hf : f ∈ coreSet RD k μ (u ++ [] ++ v)) :
    f ≫ (toLoc RD k).map (dg RD k μ (u ++ [] ++ v) (u ++ [l, l.dual] ++ v) [(u, .cup l, v)]) ∈
      coreSet RD k μ (u ++ [l, l.dual] ++ v) := by
  refine coreSet_comp_of_comm μ _ (fun is his => ⟨[], is.map (mvPos (.cup u.length l)), _,
    by simp, ?_, by rw [List.append_nil is]; exact (dD_comp_cup μ u v l his).symm⟩) hf
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
  have := his i hi
  simp only [mvPos]
  split_ifs <;> simp at this ⊢ <;> omega

end Cups

/-! ## Crossings

The product of the dots on the two strands of a crossing commutes with the crossing (from the
dot slides (2.5) of KL III); dots on the other strands commute with it by the interchange law. -/

/-- If `x₀ ψ = ψ y₁ + δ` and `x₁ ψ = ψ y₀ + δ'` with `x₀ δ' + δ y₀ = 0`, and `y₀`, `y₁` commute,
then `x₀ x₁ ψ = ψ y₀ y₁` (composition bottom to top). -/
theorem comp_comp_eq_of_slides {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {A B : 𝒞}
    (x₀ x₁ : A ⟶ A) (y₀ y₁ : B ⟶ B) (ψ δ δ' : A ⟶ B) (h₁ : x₀ ≫ ψ = ψ ≫ y₁ + δ)
    (h₂ : x₁ ≫ ψ = ψ ≫ y₀ + δ') (h₃ : x₀ ≫ δ' + δ ≫ y₀ = 0) (h₄ : y₁ ≫ y₀ = y₀ ≫ y₁) :
    x₀ ≫ x₁ ≫ ψ = ψ ≫ y₀ ≫ y₁ := by
  rw [h₂, Preadditive.comp_add, ← Category.assoc, h₁, Preadditive.add_comp, Category.assoc, h₄,
    add_assoc, add_comm (δ ≫ y₀), h₃, add_zero]

section Crossings

variable [DecidableEq I]

/-- **The product of the dots on the two strands of a crossing commutes with the crossing**:
`x₀ x₁ ψ = ψ x₀ x₁`, for upward and downward crossings of strands of any colours (from KL III
(2.5); Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem dg_dots_cross (ν : X) (ε : Bool) (c d : I) :
    dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)]
        [([], .dot (ε, c), [(ε, d)]), ([(ε, c)], .dot (ε, d), []), ([], .cross ε c d, [])] =
      dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)]
        [([], .cross ε c d, []), ([], .dot (ε, d), [(ε, c)]), ([(ε, d)], .dot (ε, c), [])] := by
  have eL : dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)]
      [([], .dot (ε, c), [(ε, d)]), ([(ε, c)], .dot (ε, d), []), ([], .cross ε c d, [])] =
      dg RD k ν [(ε, c), (ε, d)] [(ε, c), (ε, d)] [([], .dot (ε, c), [(ε, d)])] ≫
        dg RD k ν [(ε, c), (ε, d)] [(ε, c), (ε, d)] [([(ε, c)], .dot (ε, d), [])] ≫
          dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)] [([], .cross ε c d, [])] := by
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]; rfl
  have eR : dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)]
      [([], .cross ε c d, []), ([], .dot (ε, d), [(ε, c)]), ([(ε, d)], .dot (ε, c), [])] =
      dg RD k ν [(ε, c), (ε, d)] [(ε, d), (ε, c)] [([], .cross ε c d, [])] ≫
        dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([], .dot (ε, d), [(ε, c)])] ≫
          dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([(ε, d)], .dot (ε, c), [])] := by
    rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]; rfl
  have h₄ : dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([(ε, d)], .dot (ε, c), [])] ≫
      dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([], .dot (ε, d), [(ε, c)])] =
      dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([], .dot (ε, d), [(ε, c)])] ≫
        dg RD k ν [(ε, d), (ε, c)] [(ε, d), (ε, c)] [([(ε, d)], .dot (ε, c), [])] :=
    dD_comm (RD := RD) (k := k) ν (s := [(ε, d), (ε, c)]) (is := [1]) (js := [0]) (by simp)
      (by simp)
  rw [eL, eR]
  by_cases hcd : c = d
  · subst hcd
    cases ε
    · have h₁ : dg RD k ν [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])] ≫
          dg RD k ν [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] =
          dg RD k ν [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] ≫
            dg RD k ν [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])] +
            -dg RD k ν [dn c, dn c] [dn c, dn c] [] := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
        exact (dg_slideREq_dn RD k ν c).trans (sub_eq_add_neg _ _)
      have h₂ : dg RD k ν [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])] ≫
          dg RD k ν [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] =
          dg RD k ν [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] ≫
            dg RD k ν [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])] +
            dg RD k ν [dn c, dn c] [dn c, dn c] [] := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
        exact (eq_sub_iff_add_eq.mp (dg_slideLEq_dn RD k ν c)).symm
      exact comp_comp_eq_of_slides _ _ _ _ _ _ _ h₁ h₂ (by simp [dg_nil]) h₄
    · have h₁ : dg RD k ν [up c, up c] [up c, up c] [([], .dot (up c), [up c])] ≫
          dg RD k ν [up c, up c] [up c, up c] [([], .cross true c c, [])] =
          dg RD k ν [up c, up c] [up c, up c] [([], .cross true c c, [])] ≫
            dg RD k ν [up c, up c] [up c, up c] [([up c], .dot (up c), [])] +
            dg RD k ν [up c, up c] [up c, up c] [] := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
        exact dg_slideREq (RD := RD) (k := k) ν c
      have h₂ : dg RD k ν [up c, up c] [up c, up c] [([up c], .dot (up c), [])] ≫
          dg RD k ν [up c, up c] [up c, up c] [([], .cross true c c, [])] =
          dg RD k ν [up c, up c] [up c, up c] [([], .cross true c c, [])] ≫
            dg RD k ν [up c, up c] [up c, up c] [([], .dot (up c), [up c])] +
            -dg RD k ν [up c, up c] [up c, up c] [] := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
        exact (eq_add_neg_of_add_eq (dg_slideLEq (RD := RD) (k := k) ν c).symm)
      exact comp_comp_eq_of_slides _ _ _ _ _ _ _ h₁ h₂ (by simp [dg_nil]) h₄
  · cases ε
    · have h₁ : dg RD k ν [dn c, dn d] [dn c, dn d] [([], .dot (dn c), [dn d])] ≫
          dg RD k ν [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])] =
          dg RD k ν [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])] ≫
            dg RD k ν [dn d, dn c] [dn d, dn c] [([dn d], .dot (dn c), [])] + 0 := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), add_zero]
        exact dg_slideRNe_dn RD k ν c d hcd
      have h₂ : dg RD k ν [dn c, dn d] [dn c, dn d] [([dn c], .dot (dn d), [])] ≫
          dg RD k ν [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])] =
          dg RD k ν [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])] ≫
            dg RD k ν [dn d, dn c] [dn d, dn c] [([], .dot (dn d), [dn c])] + 0 := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), add_zero]
        exact (dg_slideLNe_dn RD k ν c d hcd).symm
      exact comp_comp_eq_of_slides _ _ _ _ _ _ _ h₁ h₂ (by simp) h₄
    · have h₁ : dg RD k ν [up c, up d] [up c, up d] [([], .dot (up c), [up d])] ≫
          dg RD k ν [up c, up d] [up d, up c] [([], .cross true c d, [])] =
          dg RD k ν [up c, up d] [up d, up c] [([], .cross true c d, [])] ≫
            dg RD k ν [up d, up c] [up d, up c] [([up d], .dot (up c), [])] + 0 := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), add_zero]
        exact dg_slideRNe (RD := RD) (k := k) ν c d hcd
      have h₂ : dg RD k ν [up c, up d] [up c, up d] [([up c], .dot (up d), [])] ≫
          dg RD k ν [up c, up d] [up d, up c] [([], .cross true c d, [])] =
          dg RD k ν [up c, up d] [up d, up c] [([], .cross true c d, [])] ≫
            dg RD k ν [up d, up c] [up d, up c] [([], .dot (up d), [up c])] + 0 := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain), add_zero]
        exact (dg_slideLNe (RD := RD) (k := k) ν c d hcd).symm
      exact comp_comp_eq_of_slides _ _ _ _ _ _ _ h₁ h₂ (by simp) h₄

/-- The crossing of the strands at positions `|u|`, `|u| + 1`. -/
abbrev crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) :
    (pres RD k).obj (ob RD μ (u ++ [(ε, c), (ε, d)] ++ v)) ⟶
      (pres RD k).obj (ob RD μ (u ++ [(ε, d), (ε, c)] ++ v)) :=
  dg RD k μ (u ++ [(ε, c), (ε, d)] ++ v) (u ++ [(ε, d), (ε, c)] ++ v) [(u, .cross ε c d, v)]

omit [DecidableEq I] in
theorem sChain_crs (u v : List (Letter I)) (ε : Bool) (c d : I) :
    SChain (u ++ [(ε, c), (ε, d)] ++ v) [(u, .cross ε c d, v)] (u ++ [(ε, d), (ε, c)] ++ v) :=
  ⟨rfl, rfl⟩

/-- The dots on both strands of a crossing pass it exactly. -/
theorem dD_pair_comp_crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) :
    dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v) [u.length, u.length + 1] ≫ crs μ u v ε c d =
      crs μ u v ε c d ≫ dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v) [u.length, u.length + 1] := by
  have h := congrArg (plcL RD k μ u v [(ε, c), (ε, d)] [(ε, d), (ε, c)])
    (dg_dots_cross (RD := RD) (k := k) (wt RD μ v) ε c d)
  rw [plcL_dg, plcL_dg] at h
  have hb : ∀ (x y : Letter I), ∀ i ∈ [u.length, u.length + 1], i < (u ++ [x, y] ++ v).length := by
    intro x y i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp
  rw [dg_comp (sChain_dotsL (hb _ _)) (sChain_crs u v ε c d),
    dg_comp (sChain_crs u v ε c d) (sChain_dotsL (hb _ _))]
  have e : ∀ (x y : Letter I), dotsL (u ++ [x, y] ++ v) [u.length, u.length + 1] =
      [(u, .dot x, y :: v), (u ++ [x], .dot y, v)] := by
    intro x y
    rw [dotsL_cons, dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [x, y] ++ v = u ++ x :: (y :: v) by simp) rfl,
      dotAt_eq' (show u ++ [x, y] ++ v = (u ++ [x]) ++ y :: v by simp) (by simp)]
    rfl
  rw [e, e]
  convert h using 2 <;> simp [whL]

omit [DecidableEq I] in
/-- A dot left of a crossing passes it. -/
theorem dD_left_comp_crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) {p : ℕ}
    (hp : p < u.length) :
    dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v) [p] ≫ crs μ u v ε c d =
      crs μ u v ε c d ≫ dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v) [p] := by
  obtain ⟨u₁, l, u₂, rfl, rfl⟩ := exists_split_dot hp
  have hb : ∀ (x y : Letter I), ∀ i ∈ [u₁.length], i < (u₁ ++ l :: u₂ ++ [x, y] ++ v).length := by
    intro x y i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; simp
  rw [dg_comp (sChain_dotsL (hb _ _)) (sChain_crs _ v ε c d),
    dg_comp (sChain_crs _ v ε c d) (sChain_dotsL (hb _ _))]
  have e : ∀ (x y : Letter I), dotsL (u₁ ++ l :: u₂ ++ [x, y] ++ v) [u₁.length] =
      [(u₁, .dot l, u₂ ++ [x, y] ++ v)] := by
    intro x y
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u₁ ++ l :: u₂ ++ [x, y] ++ v = u₁ ++ l :: (u₂ ++ [x, y] ++ v) by simp) rfl]
    rfl
  rw [e, e]
  have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := u₁ ++ l :: u₂ ++ [(ε, c), (ε, d)] ++ v)
    (t₀ := u₁ ++ l :: u₂ ++ [(ε, d), (ε, c)] ++ v) [] [] u₁ v
    (A := [([], .dot l, u₂)]) (B := [([], .cross ε c d, [])])
    (s := l :: u₂) (s' := l :: u₂) (t := [(ε, c), (ε, d)]) (t' := [(ε, d), (ε, c)])
    ⟨by simp, rfl⟩ ⟨rfl, rfl⟩
  convert E using 2 <;> simp [whL]

omit [DecidableEq I] in
/-- A dot right of a crossing passes it. -/
theorem dD_right_comp_crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) {p : ℕ}
    (hp : u.length + 2 ≤ p) (hp' : p < u.length + 2 + v.length) :
    dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v) [p] ≫ crs μ u v ε c d =
      crs μ u v ε c d ≫ dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v) [p] := by
  obtain ⟨v₁, l, v₂, rfl, hv⟩ := exists_split_dot (t := v) (i := p - (u.length + 2)) (by omega)
  have hb : ∀ (x y : Letter I), ∀ i ∈ [p], i < (u ++ [x, y] ++ (v₁ ++ l :: v₂)).length := by
    intro x y i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; simp; omega
  rw [dg_comp (sChain_dotsL (hb _ _)) (sChain_crs u _ ε c d),
    dg_comp (sChain_crs u _ ε c d) (sChain_dotsL (hb _ _))]
  have e : ∀ (x y : Letter I), dotsL (u ++ [x, y] ++ (v₁ ++ l :: v₂)) [p] =
      [(u ++ [x, y] ++ v₁, .dot l, v₂)] := by
    intro x y
    rw [dotsL_cons, dotsL_nil,
      dotAt_eq' (show u ++ [x, y] ++ (v₁ ++ l :: v₂) = (u ++ [x, y] ++ v₁) ++ l :: v₂ by simp)
        (by simp; omega)]
    rfl
  rw [e, e]
  have E := dg_ichg (RD := RD) (k := k) (μ := μ)
    (s₀ := u ++ [(ε, c), (ε, d)] ++ (v₁ ++ l :: v₂))
    (t₀ := u ++ [(ε, d), (ε, c)] ++ (v₁ ++ l :: v₂)) [] [] u v₂
    (A := [([], .cross ε c d, [])]) (B := [(v₁, .dot l, [])])
    (s := [(ε, c), (ε, d)]) (s' := [(ε, d), (ε, c)]) (t := v₁ ++ [l]) (t' := v₁ ++ [l])
    ⟨rfl, rfl⟩ ⟨by simp, by simp⟩
  convert E.symm using 2 <;> simp [whL]

theorem dD_block_comp_crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) {p : ℕ}
    (hp : p < u.length + 2 + v.length) :
    dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v) [p, Equiv.swap u.length (u.length + 1) p] ≫
        crs μ u v ε c d =
      crs μ u v ε c d ≫
        dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v) [p, Equiv.swap u.length (u.length + 1) p] := by
  have hb : ∀ (x y : Letter I) (i : ℕ), i < u.length + 2 + v.length →
      i < (u ++ [x, y] ++ v).length := by
    intro x y i hi; simp; omega
  by_cases h₀ : p = u.length
  · subst h₀; rw [Equiv.swap_apply_left]; exact dD_pair_comp_crs μ u v ε c d
  by_cases h₁ : p = u.length + 1
  · subst h₁
    rw [Equiv.swap_apply_right]
    have hP : ∀ (x y : Letter I), dD RD k μ (u ++ [x, y] ++ v) [u.length + 1, u.length] =
        dD RD k μ (u ++ [x, y] ++ v) [u.length, u.length + 1] := fun x y =>
      dD_perm μ (List.Perm.swap _ _ _) (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp)
    rw [hP, hP]; exact dD_pair_comp_crs μ u v ε c d
  rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]
  have hf : dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v) [p] ≫ crs μ u v ε c d =
      crs μ u v ε c d ≫ dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v) [p] := by
    rcases Nat.lt_or_ge p u.length with h | h
    · exact dD_left_comp_crs μ u v ε c d h
    · exact dD_right_comp_crs μ u v ε c d (by omega) hp
  have hs : ∀ (x y : Letter I), ∀ i ∈ [p], i < (u ++ [x, y] ++ v).length := by
    intro x y i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; exact hb x y _ hp
  rw [show [p, p] = [p] ++ [p] from rfl, dD_append μ (hs _ _) (hs _ _),
    dD_append μ (hs _ _) (hs _ _), Category.assoc, hf, ← Category.assoc, hf, Category.assoc]

theorem dD_flatMap_comp_crs (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) :
    ∀ {is : List ℕ}, (∀ i ∈ is, i < u.length + 2 + v.length) →
    dD RD k μ (u ++ [(ε, c), (ε, d)] ++ v)
        (is.flatMap fun p => [p, Equiv.swap u.length (u.length + 1) p]) ≫ crs μ u v ε c d =
      crs μ u v ε c d ≫ dD RD k μ (u ++ [(ε, d), (ε, c)] ++ v)
        (is.flatMap fun p => [p, Equiv.swap u.length (u.length + 1) p])
  | [], _ => by
    show dg _ _ _ _ _ [] ≫ _ = _ ≫ dg _ _ _ _ _ []
    rw [dg_nil, dg_nil, Category.id_comp, Category.comp_id]
  | p :: is, h => by
    have hb : ∀ (x y : Letter I) (i : ℕ), i < u.length + 2 + v.length →
        i < (u ++ [x, y] ++ v).length := by
      intro x y i hi; simp; omega
    have hsw : ∀ i, i < u.length + 2 + v.length →
        Equiv.swap u.length (u.length + 1) i < u.length + 2 + v.length := by
      intro i hi
      rcases eq_or_ne i u.length with rfl | h₀
      · rw [Equiv.swap_apply_left]; omega
      rcases eq_or_ne i (u.length + 1) with rfl | h₁
      · rw [Equiv.swap_apply_right]; omega
      rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]; exact hi
    have hp : p < u.length + 2 + v.length := h p List.mem_cons_self
    have hpair : ∀ (x y : Letter I), ∀ i ∈ [p, Equiv.swap u.length (u.length + 1) p],
        i < (u ++ [x, y] ++ v).length := by
      intro x y i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hb x y _ hp
      · exact hb x y _ (hsw _ hp)
    have hrest : ∀ (x y : Letter I), ∀ i ∈ is.flatMap (fun p =>
        [p, Equiv.swap u.length (u.length + 1) p]), i < (u ++ [x, y] ++ v).length := by
      intro x y i hi
      obtain ⟨q, hq, hi⟩ := List.mem_flatMap.1 hi
      have hq' := h q (List.mem_cons_of_mem _ hq)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hb x y _ hq'
      · exact hb x y _ (hsw _ hq')
    rw [List.flatMap_cons, dD_append μ (hpair _ _) (hrest _ _),
      dD_append μ (hpair _ _) (hrest _ _), Category.assoc,
      dD_flatMap_comp_crs μ u v ε c d (fun i hi => h i (List.mem_cons_of_mem _ hi)),
      ← Category.assoc, dD_block_comp_crs μ u v ε c d hp, Category.assoc]

theorem perm_flatMap_swap (f : ℕ → ℕ) :
    ∀ is : List ℕ, (is.flatMap fun p => [p, f p]).Perm (is ++ is.map f)
  | [] => List.Perm.refl _
  | p :: is => by
    rw [List.flatMap_cons, List.map_cons, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append]
    refine List.Perm.cons _ ?_
    exact ((perm_flatMap_swap f is).cons _).trans List.perm_middle.symm

/-- **Core morphisms are closed under postcomposition with a crossing**: the dots on the two
strands of the crossing are completed to pairs, which pass the crossing exactly. -/
theorem coreSet_comp_cross (μ : X) (u v : List (Letter I)) (ε : Bool) (c d : I) {f}
    (hf : f ∈ coreSet RD k μ (u ++ [(ε, c), (ε, d)] ++ v)) :
    f ≫ (toLoc RD k).map (crs μ u v ε c d) ∈ coreSet RD k μ (u ++ [(ε, d), (ε, c)] ++ v) := by
  refine coreSet_comp_of_comm μ _ (fun is his => ⟨is.map (Equiv.swap u.length (u.length + 1)),
    is.flatMap (fun p => [p, Equiv.swap u.length (u.length + 1) p]), crs μ u v ε c d,
    ?_, ?_, ?_⟩) hf
  · have : ∀ i ∈ is, i < u.length + 2 + v.length := by
      intro i hi; have := his i hi; simp at this; omega
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    have hi' := this i hi
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases eq_or_ne i u.length with rfl | h₀
    · rw [Equiv.swap_apply_left]; omega
    rcases eq_or_ne i (u.length + 1) with rfl | h₁
    · rw [Equiv.swap_apply_right]; omega
    rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]; omega
  · intro j hj
    obtain ⟨q, hq, hj⟩ := List.mem_flatMap.1 hj
    have hq' := his q hq
    simp only [List.length_append, List.length_cons, List.length_nil] at hq' ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · omega
    rcases eq_or_ne q u.length with rfl | h₀
    · rw [Equiv.swap_apply_left]; omega
    rcases eq_or_ne q (u.length + 1) with rfl | h₁
    · rw [Equiv.swap_apply_right]; omega
    rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]; omega
  · have hb : ∀ i ∈ is, i < u.length + 2 + v.length := by
      intro i hi; have := his i hi; simp at this; omega
    have hb' : ∀ i ∈ is.flatMap (fun p => [p, Equiv.swap u.length (u.length + 1) p]),
        i < (u ++ [(ε, c), (ε, d)] ++ v).length := by
      intro j hj
      obtain ⟨q, hq, hj⟩ := List.mem_flatMap.1 hj
      have hq' := his q hq
      simp only [List.length_append, List.length_cons, List.length_nil] at hq' ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · omega
      rcases eq_or_ne q u.length with rfl | h₀
      · rw [Equiv.swap_apply_left]; omega
      rcases eq_or_ne q (u.length + 1) with rfl | h₁
      · rw [Equiv.swap_apply_right]; omega
      rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]; omega
    rw [← dD_perm μ (perm_flatMap_swap _ is) hb']
    exact (dD_flatMap_comp_crs μ u v ε c d hb).symm

end Crossings

end Categorification.KL3.Diagram
