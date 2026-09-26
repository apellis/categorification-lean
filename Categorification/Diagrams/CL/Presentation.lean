/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Scalars
import Categorification.Diagrams.KL3.Presentation

/-!
# The 2-category `U_Q(g)` of Cautis–Lauda

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §1.1 (Definition 1.1, TeX label `defU_cat`, pp. 2–3) and §2 (`sec:cycbiadjoint`,
`sec:KLR`, `sec:mixedrels`, `sec:dotbubbles`, `sec:highersl2`, pp. 6–10). The TeX source
(`xy-pic` pictures) is the authoritative reading of the diagrams; CL read diagrams from right to
left and bottom to top, with the weight `λ` written in the rightmost region unless stated
otherwise.

`U_Q(g)` has the objects, 1-morphisms and generating 2-morphisms of the 2-category `U` of
Khovanov–Lauda III (Definition 1.1, items "objects", "1-morphisms", "2-morphisms": the same
dots, crossings, cups and caps with the same degrees), so we present it on the same signature
`psig RD` and the same pivotal base (cups, caps and the zigzag relations) as `pres RD k`
(`Categorification.Diagrams.KL3.Presentation`). Its relations are those of KL III Definition 3.1
with the scalars of a choice `Q = (t, s, r)` (`CLScalars`) inserted; they are indexed by the same
type `Rel RD` (`Categorification.Diagrams.KL3.Relations`), so that for the KL scalars `presCL` is
literally `pres` (`Categorification.Diagrams.CL.Specialize`). The list, with CL's locators and the
places where the scalars enter:

* **Biadjointness** (Definition 1.1 (1); `eq_biadjoint1`, `eq_biadjoint2`, p. 6): the four
  zigzag relations of the pivotal base (`zigzags`), as in KL III (3.1), (3.2); no scalars.
* **Cyclicity of dots** (`eq_cyclic_dot`, p. 6): `cycDotR`, `cycDotL`, unchanged.
* **`Q`-cyclicity of crossings** (`eq_almost_cyclic`, p. 6): CL's display, with bottom
  `F_a F_b` and top `F_b F_a` (labels `(a, b)` in the picture), reads
  `downCross a b = t_{ab}^{-1} · rotCrossL a b = t_{ba}^{-1} · rotCrossR a b`
  (the middle picture has nested cups on the left and caps on the right, the right picture
  cups on the right and caps on the left; see `Categorification.Diagrams.KL3.Relations` for
  `rotCrossL`, `rotCrossR`, whose pictures are those of KL III `eq_cyclic_cross-gen`). We impose
  the two relations
  `cycCrossR j i μ : t_{ij}^{-1} · rotCrossR j i - downCross j i = 0` and
  `cycCrossL j i μ : t_{ji}^{-1} · rotCrossL j i - downCross j i = 0`,
  which together are exactly CL's chain of two equalities for `(a, b) = (j, i)`. For `t = 1`
  they are KL III's `cycCrossR`, `cycCrossL`. (The weight in CL's picture is the region on the
  left of the crossing; the family of relations over all weights is the same.)
* **Sideways crossings** (`eq_crossl-gen`, `eq_crossr-gen`, p. 6): defined as the first
  composite of each display, exactly `crossl`, `crossr` of KL III; the second equalities are
  consequences of `Q`-cyclicity and are not axioms.
* **KLR relations on upward strands** (`sec:KLR`, pp. 6–8): the relations of the KLR algebra
  `R_Q` (`relationR k (qCL S) r`, see below) placed on upward strands (`upLin`), relation index
  `klr μ r`.
* **KLR relations on downward strands** (Definition 1.1 (2) and the sentence after
  `eq_almost_cyclic`): the `F`'s carry an action of the KLR algebra for the dual scalars `Q'`. CL
  state that this is ensured by `Q`-cyclicity; we therefore do not include these relations in
  `presCL` (whose relation index is `Rel RD`), but record them as `relationDown` and provide the
  presentation `presCLDown` with them added. That they are consequences is proved in
  `Categorification.Diagrams.CL.DownKLR` (`CL.lin_relationDown`, `CL.presCLDownEquiv`).
* **Mixed relations** (`sec:mixedrels`, p. 8, `i ≠ j`): `crossl i j ≫ crossr i j = t_{ji} · 1`
  on `E_i F_j` and `crossr j i ≫ crossl j i = t_{ij} · 1` on `F_i E_j` (indices `downupEF`,
  `downupFE`; KL III's (3.13) with the scalars `t_{ji}`, `t_{ij}`).
* **Dotted bubbles** (`sec:dotbubbles`, `eq_positivity_bubbles`, p. 8): `cwNeg`, `ccwNeg`,
  `cwOne`, `ccwOne`, unchanged.
* **Extended `sl₂` relations** (`sec:highersl2`, pp. 8–10; fake bubbles p. 9, relations pp. 9–10). The fake bubbles are defined by the
  same infinite Grassmannian relation as in KL III (`eq_homo_inf_grass`, `eq_infinite_Grass`;
  `cwL`, `ccwL`), without scalars. The relations, in KL III's uniform form:
  - curls (`eq_reduction-ngeqz`, `eq_reduction-nleqz` and the `n = 0` display): the right curl is
    `r_i` times KL III's right-hand side (`-r_i ∑ …` for `n < 0`, `-r_i · 1` for `n = 0`, `0` for
    `n > 0`), the left curl `r_i` times KL III's (`r_i ∑ …` for `n > 0`, `r_i · 1` for `n = 0`,
    `0` for `n < 0`): `curlR`, `curlL` with the factor `r_i` on `curlRHS`, `curlLHS`;
  - decompositions of `1_{EF}`, `1_{FE}` (`eq_ident_decomp-nleqz` and the displays for `n > 0`,
    `n = 0`): `1 = -r_i^{-2} · (double sideways crossing) + ∑ …`, the sum as in KL III:
    `decompEF`, `decompFE` with the factor `r_i^{-2}` on the double crossing.
  For `r_i = 1` these are KL III's relations.

## The KLR relations with `r_i` (`sec:KLR`)

`relationR k Q r` is the KLR presentation `KLR.Diagram.relation k Q`
(`Categorification.Diagrams.KLR.Basic`) with CL's scalars `r_i`:
* nilHecke dot slides (`eq_nil_dotslide`): `r_i · 1 = x₀ψ - ψx₁ = ψx₀ - x₁ψ` on `E_i E_i`
  (`slideREq`, `slideLEq`; the identity is scaled by `r_i`);
* `ψ² = 0` on `E_i E_i` (`eq_nil_rels`), `ψ² = Q_{ij}(x_i, x_j)` on `E_i E_j` (`eq_r2_ij-gen`,
  `sqNe` with `Q = qCL S`), the dot slides for `i ≠ j` (`eq_dot_slide_ij-gen`, `slideLNe`,
  `slideRNe`) and the braid relation (`eq_r3_easy-gen`, `braid`): unchanged;
* the braid relation on `E_i E_j E_i` for `(α_i, α_j) < 0` (`eq_r3_hard-gen`):
  `r_i^{-1}(ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁) = t_{ij} ∑_{ℓ₁+ℓ₂=d_{ij}-1} x₀^{ℓ₁} x₂^{ℓ₂} + ∑_{p,q} s_{ij}^{pq}
  ∑_{ℓ₁+ℓ₂=p-1} x₀^{ℓ₁} x₁^q x₂^{ℓ₂}`. The right-hand side is the divided difference
  `Q̄_{ij}(x₀, x₁, x₂)` of `Q_{ij}` (`qbar_qCL`), so this is `braidQ` with the correction term
  scaled by `r_i`: `ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = r_i · Q̄_{ij}(x₀, x₁, x₂)`. (CL impose `eq_r3_easy-gen`
  when `i = k` and `(α_i, α_j) = 0`; in our indexing this case is `braidQ i j` with
  `Q̄_{ij} = Q̄(t_{ij}) = 0`, the same relation.)

Every relation of `relationR` agrees with `KLR.Diagram.relation` for `r = 1`
(`relationR_one`). CL's Remark after `eq_r3_hard-gen`, item 1, says that the `ii`-crossing can be
rescaled so that `r_i = 1`; the scaling of the identity in the dot slides and of `Q̄` in the braid
relation, and of `curlRHS`, `curlLHS` and the double sideways crossing in the extended `sl₂`
relations, is consistent with rescaling `ψ_{ii} ↦ r_i^{-1} ψ_{ii}` (each of these diagrams contains
one, one, one and two `ii`-crossings).

## Main definitions

* `relationR k Q r`: the KLR relations with the scalars `r`.
* `dnLin RD k μ`: a linear combination of KLR diagrams placed on downward strands.
* `relationCL RD k S`, `presCL RD k S`, `UCL RD k S`: **CL's `U_Q(g)`** (Definition 1.1) as a
  presentation on `psig RD` and its presented bicategory; `zigzags`: the biadjointness.
* `RelDown RD`, `relationDown RD k S`, `presCLDown RD k S`: the presentation with the KLR
  relations for `Q'` on downward strands added.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

/-! ## The KLR relations with the scalars `r_i` -/

section KLR

variable {I : Type u} (k : Type w) [CommRing k]

open KLR.Diagram LinDiagram in
/-- **The KLR relations of CL §2.3** (arXiv:1111.1431v3, `sec:KLR`, pp. 6–8) for the polynomials
`Q` and the scalars `r`: `KLR.Diagram.relation k Q` with the identity in the nilHecke dot slides
`eq_nil_dotslide` scaled by `r_c`, and the correction term `Q̄_{cd}` of the braid relation
`eq_r3_hard-gen` scaled by `r_c`. -/
def relationR (Q : I → I → MvPolynomial (Fin 2) k) (r : I → k) :
    (x : KLR.Diagram.Rel I) → LinDiagram k x.dom x.cod
  | .slideLEq c => of (X2 c c ≫ D0 c c) - of (D1 c c ≫ X2 c c) - r c • of (𝟙 _)
  | .slideREq c => of (D0 c c ≫ X2 c c) - of (X2 c c ≫ D1 c c) - r c • of (𝟙 _)
  | .braidQ c d _ => of (braidL c d c) - of (braidR c d c) -
      r c • lpoly k ![E0 c d c, E1 c d c, E2 c d c] (KLR.qbar (Q c d))
  | x => KLR.Diagram.relation k Q x

/-- For `r = 1`, `relationR` is the KLR presentation of KL I/II. -/
theorem relationR_one (Q : I → I → MvPolynomial (Fin 2) k) :
    relationR k Q (fun _ => 1) = KLR.Diagram.relation k Q := by
  funext x
  cases x <;> simp [relationR, KLR.Diagram.relation]

/-- The relations only depend on the off-diagonal values of `Q`. -/
theorem relationR_congr {Q Q' : I → I → MvPolynomial (Fin 2) k} {r r' : I → k}
    (hQ : ∀ c d, c ≠ d → Q c d = Q' c d) (hr : r = r') : relationR k Q r = relationR k Q' r' := by
  subst hr
  funext x
  cases x with
  | sqNe c d h => simp [relationR, KLR.Diagram.relation, hQ c d h]
  | braidQ c d h => simp [relationR, hQ c d h]
  | _ => rfl

end KLR

/-! ## KLR diagrams on downward strands -/

section Downward

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y)

/-- Downward strands of the given colours. -/
abbrev dns (l : List I) : List (Letter I) := l.map dn

/-- The shape of a KLR generator, on downward strands. -/
def dnShape : KLR.Diagram.Gen I → Shape I
  | .dot c => .dot (dn c)
  | .cross c d => .cross false c d

theorem dnShape_dom (g : KLR.Diagram.Gen I) : (dnShape g).dom = dns g.dom := by
  cases g <;> rfl

theorem dnShape_cod (g : KLR.Diagram.Gen I) : (dnShape g).cod = dns g.cod := by
  cases g <;> rfl

/-- A KLR layer placed on downward strands with rightmost region `μ`. -/
def dnLay (μ : X) (L : Layer (KLR.Diagram.sig I)) : Layer (psig RD) :=
  lay RD μ (dns L.left) (dnShape L.gen) (dns L.right)

theorem dnLay_dom (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    (dnLay RD μ L).dom = ob RD μ (dns L.dom.word) := by
  rw [dnLay, lay_dom, dnShape_dom]
  simp [List.map_append]

theorem dnLay_cod (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    (dnLay RD μ L).cod = ob RD μ (dns L.cod.word) := by
  rw [dnLay, lay_cod, dnShape_cod]
  simp [List.map_append]

theorem chain_dn (μ : X) {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) :
    Chain (ob RD μ (dns a.word)) (ls.map (dnLay RD μ)) (ob RD μ (dns b.word)) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨lay_valid RD _ _ _ _, dnLay_dom RD μ L, by rw [dnLay_cod]; exact ih hc⟩

/-- A KLR diagram placed on downward strands with rightmost region `μ`. -/
def dnDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    ob RD μ (dns a.word) ⟶ ob RD μ (dns b.word) :=
  Diagram.mk ((Diagram.layers d).map (dnLay RD μ)) (chain_dn RD μ (Diagram.chain d))

@[simp] theorem layers_dnDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    Diagram.layers (dnDiag RD μ d) = (Diagram.layers d).map (dnLay RD μ) := rfl

variable (k : Type w) [CommRing k]

/-- A linear combination of KLR diagrams placed on downward strands with rightmost region `μ`. -/
def dnLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    LinDiagram k (ob RD μ (dns a.word)) (ob RD μ (dns b.word)) :=
  Finsupp.mapDomain (dnDiag RD μ) f

end Downward

/-! ## The presentation -/

section Presentation

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

open LinDiagram in
/-- **The relations of `U_Q(g)`** other than the zigzag relations (see the module docstring for
the locators in arXiv:1111.1431v3), indexed like those of KL III Definition 3.1 (`Rel RD`):

* `curlR i λ`, `curlL i μ`: `curl = r_i · (KL III right-hand side)` (`eq_reduction-*`);
* `decompEF i λ`, `decompFE i λ`: `1 + r_i^{-2} · (double sideways crossing) - ∑ … = 0`
  (`eq_ident_decomp-*`);
* `cycCrossR j i μ`: `t_{ij}^{-1} · rotCrossR j i = downCross j i`, and
  `cycCrossL j i μ`: `t_{ji}^{-1} · rotCrossL j i = downCross j i` (`eq_almost_cyclic` with
  `(a, b) = (j, i)`);
* `downupEF i j μ`: `crossl i j ≫ crossr i j = t_{ji} · 1_{E_i F_j}`, and
  `downupFE i j μ`: `crossr j i ≫ crossl j i = t_{ij} · 1_{F_i E_j}` (`sec:mixedrels`);
* `klr μ r`: the KLR relation `relationR k (qCL S) r` on upward strands (`sec:KLR`);
* all other relations (dot cyclicity, bubbles): those of KL III. -/
def relationCL (S : CLScalars C k) : (r : Rel RD) → LinDiagram k r.dom r.cod
  | .curlR i lam => of (curlR RD i lam) - (S.r i : k) • curlRHS RD k i lam
  | .curlL i μ => of (curlL RD i μ) - (S.r i : k) • curlLHS RD k i μ
  | .decompEF i lam => of (𝟙 _) +
      (((S.r i)⁻¹ : kˣ) : k) ^ 2 • of (crossl RD i i lam ≫ crossr RD i i lam) -
      decompEFSum RD k i lam
  | .decompFE i lam => of (𝟙 _) +
      (((S.r i)⁻¹ : kˣ) : k) ^ 2 • of (crossr RD i i lam ≫ crossl RD i i lam) -
      decompFESum RD k i lam
  | .cycCrossR j i μ => (((S.t i j)⁻¹ : kˣ) : k) • of (rotCrossR RD j i μ) - of (downCross RD j i μ)
  | .cycCrossL j i μ => (((S.t j i)⁻¹ : kˣ) : k) • of (rotCrossL RD j i μ) - of (downCross RD j i μ)
  | .downupEF i j _ μ => of (crossl RD i j μ ≫ crossr RD i j μ) - (S.t j i : k) • of (𝟙 _)
  | .downupFE i j _ μ => of (crossr RD j i μ ≫ crossl RD j i μ) - (S.t i j : k) • of (𝟙 _)
  | .klr μ r => upLin RD k μ (relationR k (qCL S) (fun c => (S.r c : k)) r)
  | r => relation k r

/-- **Cautis–Lauda's 2-category `U_Q(g)`** (arXiv:1111.1431v3, Definition 1.1 with §2), as a
presentation: the pivotal base of `U` (cups, caps and the zigzag relations = biadjointness) with
the relations `relationCL`. Without grading shifts and formal direct sums, as for `pres`. -/
def presCL (S : CLScalars C k) : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels (Rel RD) Rel.dom Rel.cod
    (relationCL RD k S)

/-- The strict bicategory `U_Q(g)`. -/
abbrev UCL (S : CLScalars C k) : Type v := (presCL RD k S).Bicat

/-- **Biadjointness** (CL Definition 1.1 (1), `eq_biadjoint1`, `eq_biadjoint2`): the zigzag
relations hold in `U_Q(g)`. -/
theorem zigzags (S : CLScalars C k) : (presCL RD k S).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) (Rel RD) _ _ _

/-- The biadjunctions `E_i 1_λ ⊣⊢ F_i 1_{λ+i_X}` of all strands in `U_Q(g)`, given by the cups
and caps. -/
abbrev biadjColour (S : CLScalars C k) :
    ColourBiadjunctions (presCL RD k S) (inv RD).toColourDuality.pivotal :=
  Presentation.pivotalBiadj (inv RD) (presCL RD k S) (zigzags RD k S)

/-! ### The KLR relations for `Q'` on downward strands -/

/-- Index type of the KLR relations on downward strands: a rightmost region and a KLR
relation. (The root datum is a parameter so that the index type is attached to `RD`, as
`Rel RD` is.) -/
inductive RelDown (_RD : RootDatum C X Y) : Type (max u v)
  | klr (μ : X) (r : KLR.Diagram.Rel I)

variable {RD}

/-- Bottom boundary. -/
def RelDown.dom : RelDown RD → Obj (psig RD)
  | .klr μ r => ob RD μ (dns (KLR.Diagram.Rel.dom r).word)

/-- Top boundary. -/
def RelDown.cod : RelDown RD → Obj (psig RD)
  | .klr μ r => ob RD μ (dns (KLR.Diagram.Rel.cod r).word)

/-- **The KLR relations for the dual scalars `Q'` on downward strands** (CL Definition 1.1 (2):
"the `F`'s carry an action of the KLR algebra associated to `Q'`"): `relationR k (qCL S.dual)
(-r)` placed on downward strands. CL state (after `eq_almost_cyclic`) that these follow from
`Q`-cyclicity; they are not part of `presCL`. -/
def relationDown (S : CLScalars C k) : (r : RelDown RD) → LinDiagram k r.dom r.cod
  | .klr μ r => dnLin RD k μ (relationR k (qCL S.dual) (fun c => (S.dual.r c : k)) r)

variable (RD)

/-- `presCL` with the KLR relations for `Q'` on downward strands added (CL Definition 1.1 (2),
second half). By CL's claim after `eq_almost_cyclic`, it presents the same 2-category as
`presCL`, which is proved in `Categorification.Diagrams.CL.DownKLR` (`CL.presCLDownEquiv`). -/
def presCLDown (S : CLScalars C k) : Presentation.{w, max u v} (psig RD) k :=
  (presCL RD k S).addRels (RelDown RD) RelDown.dom RelDown.cod (relationDown k S)

end Presentation

end Categorification.KL3.Diagram.CL
