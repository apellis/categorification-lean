/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigma

/-!
# The signed reflection of KLR diagrams for symmetric KLR polynomials

Khovanov–Lauda, arXiv:0803.4121v2 (KL I), end of §2.1: the involution `σ` reflecting a KLR
diagram across the `y`-axis, with the sign `-1` on every crossing of two strands with the
same label, preserves the KLR relations. `KSig.ksL_relation` proves this for the KL II
polynomials `klQ2`; `KSig.ksL_relation_of_symm` proves it for every family of KLR
polynomials with `Q_{ba}(u, v) = Q_{ab}(v, u)` (`KLR.KLRSymm`), which is the case used for
the downward strands of Webster's double diagrams (arXiv:1309.3796v3, proof of Lemma 4.29).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u

variable {I : Type u} (k : Type w) [CommRing k]

namespace KSig

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}

open KLR.Diagram in
/-- **The KLR relations are symmetric under the signed reflection across the `y`-axis**
for every family of KLR polynomials with `Q_{ba}(u, v) = Q_{ab}(v, u)` (KL I, end of §2.1). -/
theorem ksL_relation_of_symm (hQ : KLR.KLRSymm Q) (r : KLR.Diagram.Rel I) :
    ksL Q (KLR.Diagram.relation k Q r) = 0 := by
  cases r with
  | sqEq c =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (X2 c c ≫ X2 c c)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.sqEq c)
    show ksL _ (LinDiagram.of (X2 c c ≫ X2 c c)) = 0
    rw [ksL_of, show ksD (X2 c c ≫ X2 c c) = X2 c c ≫ X2 c c from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil]
    norm_num
    rw [← Presentation.diag_comp]
    exact H
  | sqNe c d h =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (X2 d c ≫ X2 c d) -
        lpoly k ![D0 d c, D1 d c] (Q d c)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.sqNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, ← KLR.Diagram.linAlg_apply, lpoly,
      AlgHom.map_ncEval] at H
    show ksL _ (LinDiagram.of (X2 c d ≫ X2 d c) - lpoly k ![D0 c d, D1 c d] (Q c d)) = 0
    rw [ksL_sub, ksL_of, ksL_lpoly,
      show ksD (X2 c d ≫ X2 d c) = X2 d c ≫ X2 c d from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, ite_eq_right h,
      ite_eq_right (Ne.symm h), mul_one, Int.cast_one, one_smul]
    rw [sub_eq_zero] at H ⊢
    rw [H]
    have e : (fun a => ksL (Q) (LinDiagram.of ((![D0 c d, D1 c d] : Fin 2 → _) a))) =
        ![(KLR.Diagram.pres k (Q)).diag (D1 d c),
          (KLR.Diagram.pres k (Q)).diag (D0 d c)] := by
      funext a
      fin_cases a
      · show ksL _ (LinDiagram.of (D0 c d)) = (KLR.Diagram.pres k (Q)).diag (D1 d c)
        rw [ksL_of, show ksD (D0 c d) = D1 d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (D1 c d)) = (KLR.Diagram.pres k (Q)).diag (D0 d c)
        rw [ksL_of, show ksD (D1 c d) = D0 d c from Diagram.ext rfl]
        simp [ksgn, ksg]
    rw [e]
    simp only [KLR.Diagram.linAlg_apply, Presentation.lin_of]
    rw [hQ c d h, ← ncEval_rename_of_commute _ (KPsi.commute_diag_dots2 Q d c)]
    congr 1
    funext a
    fin_cases a <;> rfl
  | slideLEq c =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (D0 c c ≫ X2 c c) -
        LinDiagram.of (X2 c c ≫ D1 c c) - LinDiagram.of (𝟙 _)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.slideREq c)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_id] at H
    show ksL _ (LinDiagram.of (X2 c c ≫ D0 c c) - LinDiagram.of (D1 c c ≫ X2 c c) -
      LinDiagram.of (𝟙 _)) = 0
    have h1 : ksL (Q) (LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c]))) =
        𝟙 ((KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c])) := ksL_one _
    have s1 : ksgn (Diagram.layers (X2 c c ≫ D0 c c)) = -1 := by simp [ksgn, ksg]
    have s2 : ksgn (Diagram.layers (D1 c c ≫ X2 c c)) = -1 := by simp [ksgn, ksg]
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, h1, s1, s2,
      show ksD (X2 c c ≫ D0 c c) = X2 c c ≫ D1 c c from Diagram.ext rfl,
      show ksD (D1 c c ≫ X2 c c) = D0 c c ≫ X2 c c from Diagram.ext rfl, ← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    have key : ∀ x y z : (KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c]) ⟶
        (KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c]),
        -x - -y - z = y - x - z := fun x y z => by abel
    exact key _ _ _
  | slideLNe c d h =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (D0 d c ≫ X2 d c) -
        LinDiagram.of (X2 d c ≫ D1 c d)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.slideRNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (X2 c d ≫ D0 d c) - LinDiagram.of (D1 c d ≫ X2 c d)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (X2 c d ≫ D0 d c) = X2 d c ≫ D1 c d from Diagram.ext rfl,
      show ksD (D1 c d ≫ X2 c d) = D0 d c ≫ X2 d c from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, ite_eq_right h, mul_one,
      Int.cast_one, one_smul]
    rw [← neg_eq_zero, neg_sub]
    exact H
  | slideREq c =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (X2 c c ≫ D0 c c) -
        LinDiagram.of (D1 c c ≫ X2 c c) - LinDiagram.of (𝟙 _)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.slideLEq c)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_id] at H
    show ksL _ (LinDiagram.of (D0 c c ≫ X2 c c) - LinDiagram.of (X2 c c ≫ D1 c c) -
      LinDiagram.of (𝟙 _)) = 0
    have h1 : ksL (Q) (LinDiagram.of (𝟙 (KLR.Diagram.ob [c, c]))) =
        𝟙 ((KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c])) := ksL_one _
    have s1 : ksgn (Diagram.layers (D0 c c ≫ X2 c c)) = -1 := by simp [ksgn, ksg]
    have s2 : ksgn (Diagram.layers (X2 c c ≫ D1 c c)) = -1 := by simp [ksgn, ksg]
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, h1, s1, s2,
      show ksD (D0 c c ≫ X2 c c) = D1 c c ≫ X2 c c from Diagram.ext rfl,
      show ksD (X2 c c ≫ D1 c c) = X2 c c ≫ D0 c c from Diagram.ext rfl, ← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    have key : ∀ x y z : (KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c]) ⟶
        (KLR.Diagram.pres k (Q)).obj (KLR.Diagram.ob [c, c]),
        -x - -y - z = y - x - z := fun x y z => by abel
    exact key _ _ _
  | slideRNe c d h =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (X2 d c ≫ D0 c d) -
        LinDiagram.of (D1 d c ≫ X2 d c)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.slideLNe d c (Ne.symm h))
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (D0 c d ≫ X2 c d) - LinDiagram.of (X2 c d ≫ D1 d c)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (D0 c d ≫ X2 c d) = D1 d c ≫ X2 d c from Diagram.ext rfl,
      show ksD (X2 c d ≫ D1 d c) = X2 d c ≫ D0 c d from Diagram.ext rfl]
    simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, ite_eq_right h, mul_one,
      Int.cast_one, one_smul]
    rw [← neg_eq_zero, neg_sub]
    exact H
  | braid c d e h =>
    have h' : ¬ (e = c ∧ e ≠ d) := fun ⟨h₁, h₂⟩ => h ⟨h₁.symm, h₁ ▸ h₂⟩
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (braidL e d c) -
        LinDiagram.of (braidR e d c)) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.braid e d c h')
    rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of] at H
    show ksL _ (LinDiagram.of (braidL c d e) - LinDiagram.of (braidR c d e)) = 0
    rw [ksL_sub, ksL_of, ksL_of,
      show ksD (braidL c d e) = braidR e d c from Diagram.ext rfl,
      show ksD (braidR c d e) = braidL e d c from Diagram.ext rfl]
    have hs : ksgn (Diagram.layers (braidR c d e)) = ksgn (Diagram.layers (braidL c d e)) := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil]
      ring
    rw [hs, ← smul_sub, ← neg_sub, smul_neg, H, smul_zero, neg_zero]
  | braidQ c d h =>
    have H : (KLR.Diagram.pres k (Q)).lin (LinDiagram.of (braidL c d c) -
        LinDiagram.of (braidR c d c) -
        lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (Q c d))) = 0 :=
      (KLR.Diagram.pres k (Q)).lin_rel_self (.braidQ c d h)
    rw [Presentation.lin_sub, Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of,
      ← KLR.Diagram.linAlg_apply, lpoly, AlgHom.map_ncEval] at H
    show ksL _ (LinDiagram.of (braidL c d c) - LinDiagram.of (braidR c d c) -
      lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (Q c d))) = 0
    rw [ksL_sub, ksL_sub, ksL_of, ksL_of, ksL_lpoly,
      show ksD (braidL c d c) = braidR c d c from Diagram.ext rfl,
      show ksD (braidR c d c) = braidL c d c from Diagram.ext rfl]
    have hs₁ : ksgn (Diagram.layers (braidL c d c)) = -1 := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, ite_eq_right h,
        ite_eq_right (Ne.symm h)]
      norm_num
    have hs₂ : ksgn (Diagram.layers (braidR c d c)) = -1 := by
      simp only [ksgn, ksg, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay_gen, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.prod_cons, List.prod_nil, ite_eq_right h,
        ite_eq_right (Ne.symm h)]
      norm_num
    have e : (fun a => ksL (Q)
        (LinDiagram.of ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) a))) =
        fun a => (KLR.Diagram.pres k (Q)).diag
          ((![E0 c d c, E1 c d c, E2 c d c] : Fin 3 → _) (![2, 1, 0] a)) := by
      funext a
      fin_cases a
      · show ksL _ (LinDiagram.of (E0 c d c)) = (KLR.Diagram.pres k (Q)).diag (E2 c d c)
        rw [ksL_of, show ksD (E0 c d c) = E2 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (E1 c d c)) = (KLR.Diagram.pres k (Q)).diag (E1 c d c)
        rw [ksL_of, show ksD (E1 c d c) = E1 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
      · show ksL _ (LinDiagram.of (E2 c d c)) = (KLR.Diagram.pres k (Q)).diag (E0 c d c)
        rw [ksL_of, show ksD (E2 c d c) = E0 c d c from Diagram.ext rfl]
        simp [ksgn, ksg]
    rw [hs₁, hs₂, e, ncEval_rename_of_commute _
      (KPsi.commute_diag_dots3 (Q) c d), KLR.qbar_rename_rev]
    simp only [KLR.Diagram.linAlg_apply, Presentation.lin_of] at H
    rw [← H]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul]
    congr 1
    abel


end KSig

end Categorification.KL3.Diagram
