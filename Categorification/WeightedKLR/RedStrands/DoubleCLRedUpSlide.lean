/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality
import Categorification.Diagrams.CL.NoMix
import Categorification.Diagrams.CL.DownKLR

/-!
# The red/upward slide relations after the cover functor

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, relations (4.4c), (4.4d), and §4.6, proof
of Lemma 4.29. A black dot or crossing on upward strands slides through a red strand. After
reflection the black strands point downward and the red strand passes through them by sideways
crossings, written as mates of upward crossings. The slide then follows from the dot cyclicity
and `Q`-cyclicity of `U_Q(g)`, the zigzag identities and the KLR relations on upward strands.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (S : CLScalars C k)

/-- Dot cyclicity in `U_Q(g)`, rotation with the cup on the right. -/
theorem dgCL_cycDotR (i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [dn i] [dn i]
        [([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]), ([], .cap (up i), [dn i])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presCL RD k S).diag_eq_of_rel (.inr (.cycDotR i μ)) rfl).symm

/-- A downward dot on the left strand of the cap `F_i E_i ⟶ 1` equals an upward dot on its
right strand. -/
theorem dgCL_dot_cap_up (ν : X) (i : I) :
    dgC (presCL RD k S) ν [dn i, up i] [] [([], .dot (dn i), [up i]), ([], .cap (up i), [])] =
      dgC (presCL RD k S) ν [dn i, up i] [] [([dn i], .dot (up i), []), ([], .cap (up i), [])] := by
  datC 0 [] [up i] (dgCL_cycDotR RD k S i _)
  dswapC 2
  dswapC 1
  datC 0 [dn i] [] (dgC_zigL' _ (zigzags RD k S) _ (up i))

/-- A downward dot on the right leg of the cup `1 ⟶ E_i F_i` equals an upward dot on its left
leg. -/
theorem dgCL_dot_cupUp (i : I) (μ : X) :
    dgC (presCL RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([up i], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [] [up i, dn i] [([], .cup (up i), []), ([], .dot (up i), [dn i])] := by
  datC 1 [up i] [] (dgCL_cycDotR RD k S i _)
  dswapC 0; dswapC 1
  datC 2 [] [dn i] (dgC_zigL' _ (zigzags RD k S) _ (up i))

/-- Dot cyclicity in `U_Q(g)`, rotation with the cup on the left. -/
theorem dgCL_cycDotL (i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn i] [dn i] [([], .dot (dn i), [])] =
      dgC (presCL RD k S) μ [dn i] [dn i]
        [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  exact ((presCL RD k S).diag_eq_of_rel (.inr (.cycDotL i μ)) rfl).symm

/-- A downward dot on the right strand of the cap `E_i F_i ⟶ 1` equals an upward dot on its
left strand. -/
theorem dgCL_dot_cap_dn (ν : X) (i : I) :
    dgC (presCL RD k S) ν [up i, dn i] [] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] =
      dgC (presCL RD k S) ν [up i, dn i] [] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] := by
  datC 0 [up i] [] (dgCL_cycDotL RD k S i _)
  dswapC 2
  dswapC 1
  datC 0 [] [dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn i))

/-- An upward dot on the right leg of the cup `1 ⟶ F_i E_i` equals a downward dot on its left
leg. -/
theorem dgCL_dot_cupDn (i : I) (μ : X) :
    dgC (presCL RD k S) μ [] [dn i, up i] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] =
      dgC (presCL RD k S) μ [] [dn i, up i] [([], .cup (dn i), []), ([], .dot (dn i), [up i])] := by
  symm
  datC 1 [] [up i] (dgCL_cycDotL RD k S i _)
  dswapC 0; dswapC 1
  datC 2 [dn i] [] (dgC_zigR' _ (zigzags RD k S) _ (dn i))

/-- The downward crossing is `t_{ij}⁻¹` times the upward crossing rotated by nested cups on the
right and caps on the left (`presCL_rotCrossR`). -/
theorem dgCL_downCross (j i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
      (((S.t i j)⁻¹ : kˣ) : k) • dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j]
        [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
          ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
          ([], .cap (up j), [dn i, dn j])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  change _ = _ • (presCL RD k S).diag (rotCrossR RD j i μ)
  rw [presCL_rotCrossR, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rfl

/-- The downward crossing is `t_{ji}⁻¹` times the upward crossing rotated by nested cups on the
left and caps on the right (`rotCrossL`). -/
theorem dgCL_downCrossL (j i : I) (μ : X) :
    dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])] =
      (((S.t j i)⁻¹ : kˣ) : k) • dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j]
        [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
          ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
          ([dn i, dn j], .cap (dn i), [])] := by
  rw [dgC_of (by schain), dgC_of (by schain)]
  have h := (presCL RD k S).lin_rel_self (.inr (.cycCrossL j i μ))
  change (presCL RD k S).lin ((((S.t j i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0 at h
  rw [lin_sub, lin_smul, lin_of, lin_of, sub_eq_zero] at h
  exact h.symm

variable {Q : I → I → MvPolynomial (Fin 2) k} (hK : KLRHolds (presCL RD k S) Q)
include hK

/-- A downward dot passes through the sideways crossing `F_j E_c ⟶ E_c F_j` for `c ≠ j`. -/
theorem dgCL_dot_crossrL (μ : X) (c j : I) (h : c ≠ j) :
    dgC (presCL RD k S) μ [dn j, up c] [up c, dn j] (([], .dot (dn j), [up c]) :: crossrL c j) =
      dgC (presCL RD k S) μ [dn j, up c] [up c, dn j]
        (crossrL c j ++ [([up c], .dot (dn j), [])]) := by
  simp only [crossrL, List.cons_append, List.nil_append]
  dswapC 0; dswapC 1
  datC 2 [] [up c, dn j] (dgCL_dot_cap_up RD k S _ j)
  datC 1 [dn j] [dn j] (dgC_slideLNe (hK := hK) _ c j h)
  datC 0 [dn j, up c] [] (dgCL_dot_cupUp RD k S j _).symm
  dswapC 1
  dswapC 2

/-- A downward dot passes through the sideways crossing `E_c F_j ⟶ F_j E_c` for `c ≠ j`. -/
theorem dgCL_dot_crosslL (μ : X) (c j : I) (h : c ≠ j) :
    dgC (presCL RD k S) μ [up c, dn j] [dn j, up c] (([up c], .dot (dn j), []) :: crosslL c j) =
      dgC (presCL RD k S) μ [up c, dn j] [dn j, up c]
        (crosslL c j ++ [([], .dot (dn j), [up c])]) := by
  simp only [crosslL, List.cons_append, List.nil_append]
  dswapC 0; dswapC 1
  datC 2 [dn j, up c] [] (dgCL_dot_cap_dn RD k S _ j)
  datC 1 [dn j] [dn j] (dgC_slideRNe (hK := hK) _ j c h.symm).symm
  datC 0 [] [up c, dn j] (dgCL_dot_cupDn RD k S j _)
  dswapC 1
  dswapC 2

/-- An upward strand of colour `c` passes a downward crossing of colours `j`, `i` (`c ≠ i`)
by the sideways crossings `crossrL`. -/
theorem dgCL_downCross_crossrL (μ : X) (c j i : I) (hi : c ≠ i) :
    dgC (presCL RD k S) μ [dn j, dn i, up c] [up c, dn i, dn j]
      ([([], .cross false j i, [up c])] ++ (crossrL c j).map (whL [dn i] []) ++
        (crossrL c i).map (whL [] [dn j])) =
    dgC (presCL RD k S) μ [dn j, dn i, up c] [up c, dn i, dn j]
      ((crossrL c i).map (whL [dn j] []) ++ (crossrL c j).map (whL [] [dn i]) ++
        [([up c], .cross false j i, [])]) := by
  rw [dgC_stepL_at _ 0 [] [up c] (dgCL_downCross RD k S j i _) (by schain) (by schain) rfl,
    map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  conv_rhs => rw [dgC_stepL_at _ 6 [up c] [] (dgCL_downCross RD k S j i _) (by schain)
    (by schain) rfl, map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  datC 2 [dn j, dn i] [up c, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up j))
  dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  dswapC 7; dswapC 6; dswapC 5
  datC 4 [dn j, dn i, up j] [up c, dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up i))
  dswapC 1
  datC 2 [dn j, dn i] [dn i, dn j] (dgC_braid (hK := hK) _ c j i (fun h => hi h.1))
  symm
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 7; dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 8; dswapC 7; dswapC 6; dswapC 5; dswapC 4
  datC 3 [dn j, dn i, up c] [up j, dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up i))
  dswapC 7; dswapC 6
  datC 5 [dn j, up c] [dn i, dn j] (dgC_zigL' _ (zigzags RD k S) _ (up j))
  dswapC 4

/-- An upward strand of colour `c` passes a downward crossing of colours `j`, `i` (`c ≠ j`)
from right to left by the sideways crossings `crosslL`. -/
theorem dgCL_crosslL_downCross (μ : X) (c j i : I) (hj : c ≠ j) :
    dgC (presCL RD k S) μ [up c, dn j, dn i] [dn i, dn j, up c]
      ((crosslL c j).map (whL [] [dn i]) ++ (crosslL c i).map (whL [dn j] []) ++
        [([], .cross false j i, [up c])]) =
    dgC (presCL RD k S) μ [up c, dn j, dn i] [dn i, dn j, up c]
      ([([up c], .cross false j i, [])] ++ (crosslL c i).map (whL [] [dn j]) ++
        (crosslL c j).map (whL [dn i] [])) := by
  rw [dgC_stepL_at _ 6 [] [up c] (dgCL_downCrossL RD k S j i _) (by schain) (by schain) rfl,
    map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  conv_rhs => rw [dgC_stepL_at _ 0 [up c] [] (dgCL_downCrossL RD k S j i _) (by schain)
    (by schain) rfl, map_smul, ctxLC_dg _ _ (by schain) (by schain)]
  congr 1
  dnorm
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 7; dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 8; dswapC 7; dswapC 6; dswapC 5; dswapC 4
  datC 3 [dn i, dn j, up i] [up c, dn j, dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn j))
  dswapC 7; dswapC 6
  datC 5 [dn i, dn j] [up c, dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn i))
  dswapC 4
  datC 2 [dn i, dn j] [dn j, dn i] (dgC_braid (hK := hK) _ j i c (fun h => hj h.1.symm))
  symm
  dswapC 4; dswapC 3; dswapC 2; dswapC 1; dswapC 0
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  datC 2 [dn i, up c] [dn j, dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn i))
  dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 6; dswapC 5; dswapC 4; dswapC 3
  dswapC 7; dswapC 6; dswapC 5
  datC 4 [dn i, dn j, up c] [up i, dn j, dn i] (dgC_zigR' _ (zigzags RD k S) _ (dn j))
  dswapC 1

end Categorification.KL3.Diagram.CL

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram KL3.Diagram.CL StringDiagrams TwoRep

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k]

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W
local notation "κ" => coverColourMap W hC o
local notation "CM" => coverMirror W hC o

/-- The reflected layers of a red strand moving from left to right through upward black
strands of colours `s`: the red strand passes the reflected black strands one at a time by the
sideways crossings `crossrL`. -/
def redThroughL (r : Fin ℓ) : List I → List (LayerData (I ⊕ Fin ℓ))
  | [] => []
  | i :: t => (crossrL (.inr r) (.inl i)).map (whL (coverWord (upBlackWord (ℓ := ℓ) t)) []) ++
      (redThroughL r t).map (whL [] [coverLetter (.inl (true, i))])

/-- The reflected layers of a red strand moving from right to left through upward black
strands of colours `s`, by the sideways crossings `crosslL`. -/
def upThroughL (r : Fin ℓ) : List I → List (LayerData (I ⊕ Fin ℓ))
  | [] => []
  | i :: t => (upThroughL r t).map (whL [] [coverLetter (.inl (true, i))]) ++
      (crosslL (.inr r) (.inl i)).map (whL (coverWord (upBlackWord (ℓ := ℓ) t)) [])

theorem coverWord_upBlackWord_cons (i : I) (t : List I) :
    coverWord (upBlackWord (ℓ := ℓ) (i :: t)) =
      coverWord (upBlackWord (ℓ := ℓ) t) ++ [coverLetter (.inl (true, i))] := by
  simp [upBlackWord, coverWord_cons]

theorem sChain_redThroughL (r : Fin ℓ) (s : List I) :
    SChain (coverWord (upBlackWord (ℓ := ℓ) s) ++ [(true, .inr r)]) (redThroughL r s)
      ([(true, .inr r)] ++ coverWord (upBlackWord (ℓ := ℓ) s)) := by
  induction s with
  | nil => simp [redThroughL, upBlackWord, coverWord]
  | cons i t ih =>
    have h₁ := (show SChain [coverLetter (.inl (true, i)), (true, .inr r)]
      (crossrL (.inr r) (.inl i)) [(true, .inr r), coverLetter (.inl (true, i))] by
        simp [crossrL, SChain, coverLetter, Shape.dom, Shape.cod]).whisk
          (coverWord (upBlackWord (ℓ := ℓ) t)) []
    have h₂ := ih.whisk [] [coverLetter (.inl (true, i))]
    simp only [redThroughL, coverWord_upBlackWord_cons]
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] at h₁ h₂ ⊢
    exact h₁.append h₂

theorem sChain_upThroughL (r : Fin ℓ) (s : List I) :
    SChain ([(true, .inr r)] ++ coverWord (upBlackWord (ℓ := ℓ) s)) (upThroughL r s)
      (coverWord (upBlackWord (ℓ := ℓ) s) ++ [(true, .inr r)]) := by
  induction s with
  | nil => simp [upThroughL, upBlackWord, coverWord]
  | cons i t ih =>
    have h₂ := (show SChain [(true, .inr r), coverLetter (.inl (true, i))]
      (crosslL (.inr r) (.inl i)) [coverLetter (.inl (true, i)), (true, .inr r)] by
        simp [crosslL, SChain, coverLetter, Shape.dom, Shape.cod]).whisk
          (coverWord (upBlackWord (ℓ := ℓ) t)) []
    have h₁ := ih.whisk [] [coverLetter (.inl (true, i))]
    simp only [upThroughL, coverWord_upBlackWord_cons]
    simp only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] at h₁ h₂ ⊢
    exact h₁.append h₂

theorem sChain_redThroughL_ctx (r : Fin ℓ) (s : List I) (u v : List (DoubleStrand I ℓ)) :
    SChain (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))
      ((redThroughL r s).map (whL (coverWord v) (coverWord u)))
      (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v)) := by
  have h := (sChain_redThroughL r s).whisk (coverWord v) (coverWord u)
  simp only [coverWord_append, List.append_assoc] at h ⊢
  simpa [coverWord, coverLetter] using h

theorem sChain_upThroughL_ctx (r : Fin ℓ) (s : List I) (u v : List (DoubleStrand I ℓ)) :
    SChain (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))
      ((upThroughL r s).map (whL (coverWord v) (coverWord u)))
      (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v)) := by
  have h := (sChain_upThroughL r s).whisk (coverWord v) (coverWord u)
  simp only [coverWord_append, List.append_assoc] at h ⊢
  simpa [coverWord, coverLetter] using h

variable (Q : Presentation.{w, max u v} (psig W) k)

theorem dgC_nil_eq {ν : X} {s t : List (Letter (I ⊕ Fin ℓ))} (h : s = t) :
    dgC Q ν s t [] = eqToHom (by rw [h]) := by
  subst h
  exact dgC_nil ν s

theorem coverLin_eqToHom {a b : Obj (signature RD Λ)} (h : a = b) (σ : Move I ℓ → k) :
    coverLin W hC o Q σ (LinDiagram.of (eqToHom h)) = eqToHom (by rw [h]) := by
  subst h
  exact coverLin_id W hC o Q σ a

section CoverForm

variable (σ : Move I ℓ → k)

/-- The cover functor sends `f` to `c` times the normal-form diagram `L` between the words `s`
and `t`, at the right weight `ν`. -/
def HasCoverForm {a b : Obj (signature RD Λ)} (c : k) (f : a ⟶ b) (ν : X)
    (s t : List (Letter (I ⊕ Fin ℓ))) (L : List (LayerData (I ⊕ Fin ℓ))) : Prop :=
  SChain s L t ∧ ∃ (e₁ : Q.obj ((κ).obj ((CM).obj a)) = Q.obj (ob W ν s))
    (e₂ : Q.obj (ob W ν t) = Q.obj ((κ).obj ((CM).obj b))),
    coverLin W hC o Q σ (LinDiagram.of f) = c • (eqToHom e₁ ≫ dgC Q ν s t L ≫ eqToHom e₂)

variable {W hC o Q σ}

theorem HasCoverForm.congr {a b : Obj (signature RD Λ)} {c c' : k} {f : a ⟶ b} {ν : X}
    {s t s' t' : List (Letter (I ⊕ Fin ℓ))} {L : List (LayerData (I ⊕ Fin ℓ))}
    (h : HasCoverForm W hC o Q σ c f ν s t L) (hc : c = c') (hs : s = s') (ht : t = t') :
    HasCoverForm W hC o Q σ c' f ν s' t' L := by
  subst hc hs ht
  exact h

theorem HasCoverForm.comp {a b d : Obj (signature RD Λ)} {c c' : k} {f : a ⟶ b} {g : b ⟶ d}
    {ν : X} {s t t' r : List (Letter (I ⊕ Fin ℓ))} {A B : List (LayerData (I ⊕ Fin ℓ))}
    (hf : HasCoverForm W hC o Q σ c f ν s t A) (hg : HasCoverForm W hC o Q σ c' g ν t' r B)
    (ht : t = t') : HasCoverForm W hC o Q σ (c * c') (f ≫ g) ν s r (A ++ B) := by
  subst ht
  obtain ⟨hA, e₁, e₂, hf⟩ := hf
  obtain ⟨hB, e₃, e₄, hg⟩ := hg
  refine ⟨hA.append hB, e₁, e₄, ?_⟩
  rw [LinDiagram.of_comp, coverLin_comp, hf, hg, Linear.smul_comp, Linear.comp_smul, smul_smul]
  congr 1
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (dgC Q ν s t A), dgC_comp hA hB]

theorem HasCoverForm.cast {a b a' b' : Obj (signature RD Λ)} {c : k} {f : a ⟶ b} {ν : X}
    {s t : List (Letter (I ⊕ Fin ℓ))} {L : List (LayerData (I ⊕ Fin ℓ))}
    (h : HasCoverForm W hC o Q σ c f ν s t L) (ha : a = a') (hb : b = b') :
    HasCoverForm W hC o Q σ c (Diagram.cast f ha hb) ν s t L := by
  subst ha hb
  obtain ⟨hL, e₁, e₂, h⟩ := h
  refine ⟨hL, e₁, e₂, ?_⟩
  rw [coverLin_cast, h]
  simp

theorem HasCoverForm.coverLin_sub_eq_zero {a b : Obj (signature RD Λ)} {c c' : k}
    {f g : a ⟶ b} {ν : X} {s t s' t' : List (Letter (I ⊕ Fin ℓ))}
    {A B : List (LayerData (I ⊕ Fin ℓ))}
    (hf : HasCoverForm W hC o Q σ c f ν s t A) (hg : HasCoverForm W hC o Q σ c' g ν s' t' B)
    (hc : c = c') (hs : s = s') (ht : t = t') (h : dgC Q ν s t A = dgC Q ν s t B) :
    coverLin W hC o Q σ (LinDiagram.of f - LinDiagram.of g) = 0 := by
  subst hc hs ht
  obtain ⟨-, e₁, e₂, hf⟩ := hf
  obtain ⟨-, e₃, e₄, hg⟩ := hg
  rw [show ∀ {a b} (f g : LinDiagram k a b), coverLin W hC o Q σ (f - g) =
      coverLin W hC o Q σ f - coverLin W hC o Q σ g from fun f g => by
    simp only [coverLin, freeLift_map_layerLin, Functor.map_sub], hf, hg, h, sub_self]

variable (W hC o Q σ)

theorem hasCoverForm_moveDiagram (μ : X) (u : List (DoubleStrand I ℓ)) (m : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    HasCoverForm W hC o Q σ (σ m) (moveDiagram RD Λ μ u m v) (o - μ)
      (coverWord v ++ coverWord m.bottom ++ coverWord u)
      (coverWord v ++ coverWord m.top ++ coverWord u)
      ((coverMoveL m).map (whL (coverWord v) (coverWord u))) := by
  obtain ⟨h, e₁, e₂, he⟩ := coverLin_moveDiagram_dgC W hC o Q σ μ u m v
  exact ⟨h, e₁, e₂, he⟩

theorem hasCoverForm_upBlackMoveDiagram (μ : X) (u : List (DoubleStrand I ℓ))
    (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) :
    HasCoverForm W hC o Q σ (σ (.black g.shape)) (upBlackMoveDiagram RD Λ μ u g v) (o - μ)
      (coverWord v ++ coverWord (upBlackWord (ℓ := ℓ) g.bottom) ++ coverWord u)
      (coverWord v ++ coverWord (upBlackWord (ℓ := ℓ) g.top) ++ coverWord u)
      ((coverMoveL (.black g.shape)).map (whL (coverWord v) (coverWord u))) :=
  ((hasCoverForm_moveDiagram W hC o Q σ μ u (.black g.shape) v).cast _ _).congr rfl
    (by cases g <;> rfl) (by cases g <;> rfl)

end CoverForm

variable [DecidableEq I]

/-- The cover functor on a red strand moving from left to right through upward black strands. -/
theorem coverLin_redThroughUpWord (μ : X) (r : Fin ℓ) (s : List I) :
    ∀ (u v : List (DoubleStrand I ℓ))
      (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ
        (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v)))) =
        Q.obj (ob W (o - μ)
          (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))))
      (e₂ : Q.obj (ob W (o - μ)
          (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ
          (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))))),
      coverLin W hC o Q coverSign (LinDiagram.of (redThroughUpWord RD Λ μ r u s v)) =
        eqToHom e₁ ≫ dgC Q (o - μ)
          (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))
          (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))
          ((redThroughL r s).map (whL (coverWord v) (coverWord u))) ≫ eqToHom e₂ := by
  induction s with
  | nil =>
    intro u v e₁ e₂
    rw [redThroughUpWord, coverLin_eqToHom]
    simp only [redThroughL, List.map_nil]
    rw [dgC_nil_eq W Q (by simp [upBlackWord, coverWord])]
    simp
  | cons i t ih =>
    intro u v e₁ e₂
    obtain ⟨h₁, x₁, x₂, he₁⟩ := coverLin_moveDiagram_dgC W hC o Q coverSign μ u
      (.redBlack r (true, i)) (upBlackWord t ++ v)
    simp only [redThroughUpWord]
    rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, ih]
    rotate_left
    · exact congrArg Q.obj (coverObj W hC o μ _)
    · exact (congrArg Q.obj (coverObj W hC o μ _)).symm
    have hs : coverSign (k := k) (ℓ := ℓ) (.redBlack r (true, i)) = 1 := rfl
    rw [hs, one_smul]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ h₁ ?_ ?_ _ _ _ _ _
    · simp [coverWord_append, coverWord_upBlackWord_cons, Move.bottom, coverWord_cons]
    · simp [coverWord_append, Move.top, coverWord_cons]
    · simp [coverWord_append, coverWord_upBlackWord_cons, coverWord_cons]
    · exact sChain_redThroughL_ctx r t _ v
    · have hc : coverMoveL (.redBlack r (true, i) : Move I ℓ) = crossrL (.inr r) (.inl i) := rfl
      simp only [hc, redThroughL, List.map_append, List.map_map, coverWord_append]
      congr 1 <;> refine List.map_congr_left fun x _ => ?_ <;>
        simp [whL, coverWord, coverLetter]

/-- The cover functor on upward black strands moving from left to right through a red
strand. -/
theorem coverLin_upWordThroughRed (μ : X) (r : Fin ℓ) (s : List I) :
    ∀ (u v : List (DoubleStrand I ℓ))
      (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ
        (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v)))) =
        Q.obj (ob W (o - μ)
          (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))))
      (e₂ : Q.obj (ob W (o - μ)
          (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ
          (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))))),
      coverLin W hC o Q coverSign (LinDiagram.of (upWordThroughRed RD Λ μ r u s v)) =
        eqToHom e₁ ≫ dgC Q (o - μ)
          (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))
          (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))
          ((upThroughL r s).map (whL (coverWord v) (coverWord u))) ≫ eqToHom e₂ := by
  induction s with
  | nil =>
    intro u v e₁ e₂
    rw [upWordThroughRed, coverLin_eqToHom]
    simp only [upThroughL, List.map_nil]
    rw [dgC_nil_eq W Q (by simp [upBlackWord, coverWord])]
    simp
  | cons i t ih =>
    intro u v e₁ e₂
    obtain ⟨h₁, x₁, x₂, he₁⟩ := coverLin_moveDiagram_dgC W hC o Q coverSign μ u
      (.blackRed (true, i) r) (upBlackWord t ++ v)
    simp only [upWordThroughRed]
    rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, ih]
    rotate_left
    · exact congrArg Q.obj (coverObj W hC o μ _)
    · exact (congrArg Q.obj (coverObj W hC o μ _)).symm
    have hs : coverSign (k := k) (ℓ := ℓ) (.blackRed (true, i) r) = 1 := rfl
    rw [hs, one_smul]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ ?_ h₁ ?_ _ _ _ _ _
    · simp [coverWord_append, coverWord_upBlackWord_cons, coverWord_cons]
    · simp [coverWord_append, Move.bottom, coverWord_cons]
    · simp [coverWord_append, coverWord_upBlackWord_cons, Move.top, coverWord_cons]
    · exact sChain_upThroughL_ctx r t _ v
    · have hc : coverMoveL (.blackRed (true, i) r : Move I ℓ) = crosslL (.inr r) (.inl i) := rfl
      simp only [hc, upThroughL, List.map_append, List.map_map, coverWord_append]
      congr 1 <;> refine List.map_congr_left fun x _ => ?_ <;>
        simp [whL, coverWord, coverLetter]

theorem hasCoverForm_redThroughUpWord (μ : X) (r : Fin ℓ) (u : List (DoubleStrand I ℓ))
    (s : List I) (v : List (DoubleStrand I ℓ)) :
    HasCoverForm W hC o Q coverSign 1 (redThroughUpWord RD Λ μ r u s v) (o - μ)
      (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))
      (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))
      ((redThroughL r s).map (whL (coverWord v) (coverWord u))) :=
  ⟨sChain_redThroughL_ctx r s u v, congrArg Q.obj (coverObj W hC o μ _),
    (congrArg Q.obj (coverObj W hC o μ _)).symm, by
      rw [one_smul]; exact coverLin_redThroughUpWord W hC o Q μ r s u v _ _⟩

theorem hasCoverForm_upWordThroughRed (μ : X) (r : Fin ℓ) (u : List (DoubleStrand I ℓ))
    (s : List I) (v : List (DoubleStrand I ℓ)) :
    HasCoverForm W hC o Q coverSign 1 (upWordThroughRed RD Λ μ r u s v) (o - μ)
      (coverWord (u ++ upBlackWord (ℓ := ℓ) s ++ [(.inr r : DoubleStrand I ℓ)] ++ v))
      (coverWord (u ++ [(.inr r : DoubleStrand I ℓ)] ++ upBlackWord (ℓ := ℓ) s ++ v))
      ((upThroughL r s).map (whL (coverWord v) (coverWord u))) :=
  ⟨sChain_upThroughL_ctx r s u v, congrArg Q.obj (coverObj W hC o μ _),
    (congrArg Q.obj (coverObj W hC o μ _)).symm, by
      rw [one_smul]; exact coverLin_upWordThroughRed W hC o Q μ r s u v _ _⟩

section Slide

variable (S : CLScalars C' k) {q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k}
  (hK : KLRHolds (presCL W k S) q)
include hK

/-- **Relations (4.4c,d) after the cover functor.** Sliding an upward black dot or crossing
through a red strand from left to right holds after reflection into the Cautis–Lauda
presentation, by the dot and `KLR` slides through the sideways crossings. -/
theorem coverLin_redUpSlideRel (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ)
    (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) :
    coverLin W hC o (presCL W k S) coverSign
      (LinDiagram.of (redUpSlide RD Λ μ u r g v false) -
        LinDiagram.of (redUpSlide RD Λ μ u r g v true)) = 0 := by
  have hu := hasCoverForm_upBlackMoveDiagram W hC o (presCL W k S) coverSign μ
  have hr := hasCoverForm_redThroughUpWord W hC o (presCL W k S) μ r
  simp only [redUpSlide, Bool.false_eq_true, ↓reduceIte]
  cases g with
  | dot i =>
    have hf := (hu (u ++ [(.inr r : DoubleStrand I ℓ)]) (.dot i) v).comp (hr u [i] v) (by
      simp [upBlackWord, coverWord])
    have hg := (hr u [i] v).comp ((hu u (.dot i) ((.inr r : DoubleStrand I ℓ) :: v)).cast
      (show _ = obj RD Λ μ (u ++ upBlackWord [i] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])
      (show _ = obj RD Λ μ (u ++ upBlackWord [i] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])) (by
      simp [upBlackWord, coverWord])
    refine HasCoverForm.coverLin_sub_eq_zero hf hg (by rw [mul_one, one_mul]) ?_ ?_ ?_
    · simp [upBlackWord, coverWord]
    · simp [upBlackWord, coverWord]
    · exact dgC_step (presCL W k S) (o - μ) [] [] (coverWord v) (coverWord u)
        (dgCL_dot_crossrL W k S hK _ (.inr r) (.inl i) Sum.inr_ne_inl)
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [whL, redThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
        (by simp [whL, redThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
  | cross a b =>
    have hf := (hu (u ++ [(.inr r : DoubleStrand I ℓ)]) (.cross a b) v).comp (hr u [b, a] v) (by
      simp [upBlackWord, coverWord])
    have hg := (hr u [a, b] v).comp ((hu u (.cross a b) ((.inr r : DoubleStrand I ℓ) :: v)).cast
      (show _ = obj RD Λ μ (u ++ upBlackWord [a, b] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])
      (show _ = obj RD Λ μ (u ++ upBlackWord [b, a] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])) (by
      simp [upBlackWord, coverWord])
    refine HasCoverForm.coverLin_sub_eq_zero hf hg (by rw [mul_one, one_mul]) ?_ ?_ ?_
    · simp [upBlackWord, coverWord]
    · simp [upBlackWord, coverWord]
    · exact dgC_step (presCL W k S) (o - μ) [] [] (coverWord v) (coverWord u)
        (dgCL_downCross_crossrL W k S hK _ (.inr r) (.inl b) (.inl a) Sum.inr_ne_inl)
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [whL, redThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
        (by simp [whL, redThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])

/-- **The mirrors of relations (4.4c,d) after the cover functor.** Sliding an upward black dot or
crossing through a red strand from right to left holds after reflection into the Cautis–Lauda
presentation. -/
theorem coverLin_redUpSlideMirrorRel (μ : X) (u : List (DoubleStrand I ℓ)) (r : Fin ℓ)
    (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) :
    coverLin W hC o (presCL W k S) coverSign
      (LinDiagram.of (redUpSlideMirror RD Λ μ u r g v false) -
        LinDiagram.of (redUpSlideMirror RD Λ μ u r g v true)) = 0 := by
  have hu := hasCoverForm_upBlackMoveDiagram W hC o (presCL W k S) coverSign μ
  have hr := hasCoverForm_upWordThroughRed W hC o (presCL W k S) μ r
  simp only [redUpSlideMirror, Bool.false_eq_true, ↓reduceIte]
  cases g with
  | dot i =>
    have hf := ((hu u (.dot i) ((.inr r : DoubleStrand I ℓ) :: v)).cast
      (show _ = obj RD Λ μ (u ++ upBlackWord [i] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])
      (show _ = obj RD Λ μ (u ++ upBlackWord [i] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])).comp (hr u [i] v) (by
      simp [upBlackWord, coverWord])
    have hg := (hr u [i] v).comp (hu (u ++ [(.inr r : DoubleStrand I ℓ)]) (.dot i) v) (by
      simp [upBlackWord, coverWord])
    refine HasCoverForm.coverLin_sub_eq_zero hf hg (by rw [mul_one, one_mul]) ?_ ?_ ?_
    · simp [upBlackWord, coverWord]
    · simp [upBlackWord, coverWord]
    · exact dgC_step (presCL W k S) (o - μ) [] [] (coverWord v) (coverWord u)
        (dgCL_dot_crosslL W k S hK _ (.inr r) (.inl i) Sum.inr_ne_inl)
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [whL, upThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
        (by simp [whL, upThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
  | cross a b =>
    have hf := ((hu u (.cross a b) ((.inr r : DoubleStrand I ℓ) :: v)).cast
      (show _ = obj RD Λ μ (u ++ upBlackWord [a, b] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])
      (show _ = obj RD Λ μ (u ++ upBlackWord [b, a] ++ [(.inr r : DoubleStrand I ℓ)] ++ v) by
        simp [List.append_assoc])).comp (hr u [b, a] v) (by
      simp [upBlackWord, coverWord])
    have hg := (hr u [a, b] v).comp (hu (u ++ [(.inr r : DoubleStrand I ℓ)]) (.cross a b) v) (by
      simp [upBlackWord, coverWord])
    refine HasCoverForm.coverLin_sub_eq_zero hf hg (by rw [mul_one, one_mul]) ?_ ?_ ?_
    · simp [upBlackWord, coverWord]
    · simp [upBlackWord, coverWord]
    · exact dgC_step (presCL W k S) (o - μ) [] [] (coverWord v) (coverWord u)
        ((dgCL_crosslL_downCross W k S hK _ (.inr r) (.inl b) (.inl a)
          Sum.inr_ne_inl).symm)
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [SChain, upBlackWord, coverWord, coverLetter])
        (by simp [whL, upThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])
        (by simp [whL, upThroughL, coverMoveL, UpBlackMove.shape, upBlackWord, coverWord,
          coverLetter])

end Slide

end Categorification.Stendhal.DoubleDiagram
